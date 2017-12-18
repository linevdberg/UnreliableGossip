
module UnreliableGossip where

import AgentTypes
import Data.List


type DCUagents  = [AgentInfo]
type DCUnumbers = [(Agent, Agent)]

type DCU = (DCUagents, DCUnumbers)

type Item = (Agent, ([Agent], ([Agent], [Agent], [Agent]), Agenttype,
             Agentproperty))

type Table = [Item]


initialize :: DCU -> Table
initialize ([]                              , _      ) = []
initialize ((a, (aType, aProp), secret):rest, numbers) =
  sort $ (a, (aN, (aX, aY, []), aType, aProp)) : initialize (rest, numbers)
  where
    aN = sort $ check numbers
    check []            = []
    check ((b,c):rest2) = if b == a
                             then c : check rest2
                             else check rest2
    aX = [ a | secret     ]
    aY = [ a | not secret ]


-- merging lists
merge :: [Int] -> [Int] -> [Int]
merge xs     []     = xs
merge []     ys     = ys
merge (x:xs) (y:ys) =
  case compare x y of
    EQ -> x: merge xs     ys
    LT -> x: merge xs     (y:ys)
    GT -> y: merge (x:xs) ys


-- check if call is possible
possible :: Table -> (Agent,Agent) -> Bool
possible table (a, b) = a /= b && b `elem` aN where
  Just (aN, (_aX, _aY, _aZ), _aType, _aProp) = lookup a table


-- update the Table with a call
call :: (Agent, Agent) -> Table -> [Table]
call (a,b) table = let
  Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
  Just (bN, (bX, bY, bZ), bType, bProp) = lookup b table

  -- Leeches do not share numbers
  -- Fact-checkers do not update their numbers
  -- (and therefore do also not share any)
  new_aN | aType == FactChecker = aN
         | bType == Leech       = aN
         | otherwise            = merge aN bN
  new_bN | bType == FactChecker = bN
         | aType == Leech       = bN
         | otherwise            = merge aN bN

  disagreementsX = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aX `intersect` bZ)
                                       `union` (bX `intersect` aZ)

  disagreementsY = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aY `intersect` bZ)
                                       `union` (bY `intersect` aZ)

  -- Fact-checkers do not tell which agents are unreliable
  -- (this could be an option as well)
  new_aX | bType == Leech       = aX
         | bType == FactChecker = aX `union` [b] \\ (aX `intersect` bZ)
         | otherwise            = merge aX bX \\ disagreementsX
  new_bX | aType == Leech       = bX
         | aType == FactChecker = bX `union` [a] \\ (bX `intersect` aZ)
         | otherwise            = merge aX bX \\ disagreementsX

  new_aY | bType == Leech       = aY
         | bType == FactChecker = aY \\ (aY `intersect` bZ)
         | otherwise            = merge aY bY \\ disagreementsY
  new_bY | aType == Leech       = bY
         | aType == FactChecker = bY \\ (bY `intersect` aZ)
         | otherwise            = merge aY bY \\ disagreementsY

  new_aZ | bType == Leech       = aZ
         | bType == FactChecker = aZ `union` (aX `intersect` bZ)
                                     `union` (bX `intersect` aZ)
         | otherwise            = merge aZ bZ `union` (aX `intersect` bY)
                                              `union` (bX `intersect` aY)
  new_bZ | aType == Leech       = bZ
         | bType == FactChecker = bZ `union` (aX `intersect` bY)
                                     `union` (bX `intersect` aY)
         | otherwise            = merge aZ bZ `union` (aX `intersect` bY)
                                              `union` (bX `intersect` aY)

  stripTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp)),
                         (b, (bN, (bX, bY, bZ), bType, bProp))]
  newTable   = sort $ (a, (new_aN, (new_aX, new_aY, new_aZ), aType, aProp)) :
                      (b, (new_bN, (new_bX, new_bY, new_bZ), bType, bProp)) :
                      stripTable
 in
   if possible table (a,b)
      then typeBehavior [(a,aType,aProp),(b,bType,bProp)] newTable (a,b)
      else error "forbidden call!"


-- let's the agents behave according to their types and properties
typeBehavior :: [(Agent, Agenttype, Agentproperty)] -> Table -> (Agent, Agent) -> [Table]
typeBehavior []                     table _ = [table]
typeBehavior ((a,aType,aProp):rest) table (b,c)
  | aType == AlternatingBluffer && aProp == None
      = typeBehavior rest (alternate a table) (b,c)
  | aType == AlternatingBluffer && aProp == TrumpianDel
      = typeBehavior rest (alternate a (censorDelete a table)) (b,c)
  | aType == AlternatingBluffer && aProp == TrumpianBlock
      = typeBehavior rest (alternate a (censorBlock a table)) (b,c)
  | aType == Reliable           && aProp == None
      = typeBehavior rest table (b,c)
  | aType == Reliable           && aProp == TrumpianDel
      = typeBehavior rest (censorDelete a table) (b,c)
  | aType == Reliable           && aProp == TrumpianBlock
      = typeBehavior rest (censorBlock a table) (b,c)
  | aType == Saboteur           && aProp == None
      = concat [ typeBehavior rest (cut unluckyPair table) (b,c) |
                       unluckyPair <- filteredConnections table a (b,c)]
  | otherwise
      = typeBehavior rest table (b,c)


-- a function for Alternating Bluffers
alternate :: Agent -> Table -> Table
alternate a table = sort $ (a, (aN, (newX, newY, aZ), aType, aProp)):newtable where
  Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
  newtable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp))]
  newX | a `elem` aX = aX \\ [a]
       | a `elem` aY = sort $ a:aX
       | otherwise   = aX

  newY | a `elem` aY = aY \\ [a]
       | a `elem` aX = sort $ a:aY
       | otherwise   = aY



-- maps the table to a list of its agents
agents :: Table -> [Agent]
agents = sort . map fst

-- find reliable agents from table
reliable :: Table -> [Agent]
reliable [] = []
reliable ((a, (_aN, (_aX, _aY, _aZ), aType, _aProp)):rest) =
  if aType == Reliable then a : reliable rest
    else reliable rest


-- map table to knowledge of each agent
-- where knowledge of an agent a is X_a union Y_a
knowledge :: Table -> [(Agent,[Agent])]
knowledge [] = []
knowledge ((a, (_aN, (aX, aY, _aZ), _aType, _aProp)):rest) =
  (a, merge aX aY) : knowledge rest


-- table complete if all agents know all secrets of reliable agents
-- note: they may know more secrets
complete :: Table -> Bool
complete table = all (subsetAgs (reliable table)) aXYs where
  aXYs   = map snd (knowledge table)
  -- check if a list is a subset of another list
  subsetAgs :: [Agent] -> [Agent] -> Bool
  subsetAgs [] _ = True
  subsetAgs (a:as) list = a `elem` list && subsetAgs as list

-- table completeR if all reliable agents know all secrets of reliable agents
-- note: they may know more secrets
completeR :: Table -> Bool
completeR table = all (subsetAgs (reliable table)) aXYs where
  rTable = filter (\x -> fst x `elem` reliable table) table
  aXYs   = map snd (knowledge rTable)
  -- check if a list is a subset of another list
  subsetAgs :: [Agent] -> [Agent] -> Bool
  subsetAgs [] _ = True
  subsetAgs (a:as) list = a `elem` list && subsetAgs as list


-- find unreliable agents from table
unreliable :: Table -> [Agent]
unreliable [] = []
unreliable ((a, (_aN, (_aX, _aY, _aZ), aType, _aProp)):rest) =
  if aType /= Reliable then a : unreliable rest
    else unreliable rest

-- map table to list of distrusted agents
distrust :: Table -> [(Agent,[Agent])]
distrust [] = []
distrust ((a, (_aN, (_aX, _aY, aZ), _aType, _aProp)):rest) =
  (a, aZ) :distrust rest

-- table correctly identifies unreliable agents if all agents distrust
-- the unreliable agents
identifyUnreliable :: Table -> Bool
identifyUnreliable table = all (== unreliable table) aZs where
  aZs    = map snd (distrust table)

-- table correctly identifies unreliable agents restricted to reliable agents
-- if all reliable agents distrust the unreliable agents
identifyUnreliableR :: Table -> Bool
identifyUnreliableR table = all (== unreliable table) aZs where
  rTable = filter (\x -> fst x `elem` reliable table) table
  aZs    = map snd (distrust rTable)

-- test for strong completeness
strongComplete :: Table -> Bool
strongComplete table = complete table && identifyUnreliable table

strongCompleteR :: Table -> Bool
strongCompleteR table = completeR table && identifyUnreliableR table




data Protocol = ANY | CMO | LNS | LNSR
  deriving (Eq,Ord,Show)

-- a node is a table with a call history and a protocol
type Node = (Table,Seq,Protocol)

-- a type for calling sequences
type Seq = [(Agent,Agent)]

calls :: Seq -> Table -> [Table]
calls [] table = [table]
calls cs table = concatMap (calls (tail cs)) (call (head cs) table)



-- check whether a call sequence is permitted according to a Protocol
permitted :: Node -> (Agent, Agent) -> Bool
permitted (table, _   , ANY) (a,b) = possible table (a,b)
permitted (table, hist, CMO) (a,b) =
  possible table (a,b) && not ((a,b) `elem` hist || (b,a) `elem` hist)
permitted (table, _   , LNS) (a,b) =
  possible table (a,b) && b `notElem` merge (merge aX aY) aZ
  where
    Just (_aN, (aX, aY, aZ), _aType, _aProp) = lookup a table
permitted (table, hist, LNSR) (a,b) =
  permitted (table, hist, LNS) (a,b) && a `elem` reliable table

-- find all the factcheckers in a table
factcheckers :: Table -> [Agent]
factcheckers [] = []
factcheckers ((c, (_cN, (_cX, _cY, _cZ), cType, _cProp)):rest)
 | cType == FactChecker = c : factcheckers rest
 | otherwise            =     factcheckers rest



-- compute all calls that are permitted in a table
candidates :: Node -> Seq
candidates (table, hist, prot) = let
  ags    = agents table
  pairs  = [(x,y) | x <- ags, y <- ags, x /= y ]
 in
  filter (permitted (table, hist, prot)) pairs



-- a depth first search algorithm that proceeds by building a search tree
search :: (node -> [node])
       -> (node -> Bool) -> [node] -> [node]
search _        _    [] = []
search children goal (x:xs)
  | goal x    = x : search children goal xs
  | otherwise = search children goal (children x ++ xs)

verboseSearch :: Show node => (node -> [node])
       -> (node -> Bool) -> [node] -> IO ()
verboseSearch _        _    [] = return ()
verboseSearch children goal (x:xs)
  | goal x    = do
      putStrLn $ "found one: " ++ show x
      verboseSearch children goal xs
  | otherwise = do
      putStrLn $ "not done:" ++ show x
      putStrLn "children:"
      mapM_  print (children x)
      verboseSearch children goal (children x ++ xs)



-- print which calls have taken place in a Node
showHistOf :: Node -> IO()
showHistOf = print . snd' where
  snd' (_, x, _) = x


-- four ways for solving a node:
-- complete, strong complete, complete restricted to reliable agents and
-- strong complete restricted to reliable agents
solved :: Node -> Bool
solved (table, _, _) = complete table

solvedStrong :: Node -> Bool
solvedStrong (table, _, _) = strongComplete table

solvedR :: Node -> Bool
solvedR (table, _, _) = completeR table

solvedStrongR :: Node -> Bool
solvedStrongR (table, _, _) = strongCompleteR table


extendNode :: Node -> [Node]
extendNode (table, hist, prot) =
  [(newTable, hist ++ [(x,y)], prot) | (x,y) <- candidates (table, hist,
                                                                   prot) ,
                                       newTable <- call (x,y) table]


-- similarly, we have four versions of solveNs, solveAndShow and solveShowHistOf
solveNs :: [Node] -> [Node]
solveNs = search extendNode solved

solveNsStrong :: [Node] -> [Node]
solveNsStrong = search extendNode solvedStrong

solveNsR :: [Node] -> [Node]
solveNsR = search extendNode solvedR

solveNsStrongR :: [Node] -> [Node]
solveNsStrongR = search extendNode solvedStrongR


-- print calling sequences that (strongly) complete (restricted to
-- reliable agents) the network
solveAndShow :: Table -> Protocol -> IO()
solveAndShow t p = solveShowHistOf [(t, [], p)]

solveAndShowStrong :: Table -> Protocol -> IO()
solveAndShowStrong t p = solveShowHistOfStrong [(t, [], p)]

solveAndShowR :: Table -> Protocol -> IO()
solveAndShowR t p = solveShowHistOfR [(t, [], p)]

solveAndShowStrongR :: Table -> Protocol -> IO()
solveAndShowStrongR t p = solveShowHistOfStrongR [(t, [], p)]

-- print hisory
solveShowHistOf :: [Node] -> IO()
solveShowHistOf = sequence_ . fmap showHistOf . solveNs

solveShowHistOfStrong :: [Node] -> IO()
solveShowHistOfStrong = sequence_ . fmap showHistOf . solveNsStrong

solveShowHistOfR :: [Node] -> IO()
solveShowHistOfR = sequence_ . fmap showHistOf . solveNsR

solveShowHistOfStrongR :: [Node] -> IO()
solveShowHistOfStrongR = sequence_ . fmap showHistOf . solveNsStrongR


-- check if a graph is solvable
solvable :: Table -> Protocol -> Bool
solvable t p = solveNs [(t, [], p)] /= []

solvableStrong :: Table -> Protocol -> Bool
solvableStrong t p = solveNsStrong [(t, [], p)] /= []

solvableR :: Table -> Protocol -> Bool
solvableR t p = solveNsR [(t, [], p)] /= []

solvableStrongR :: Table -> Protocol -> Bool
solvableStrongR t p = solveNsStrongR [(t, [], p)] /= []


strip :: Table -> [(Agent, ([Agent], ([Agent], [Agent], [Agent])))]
strip [] = []
strip ((a, (aN, (aX, aY, aZ), _aType, _aProp)):rest) =
  (a, (aN, (aX, aY, aZ))): strip rest



-- censorship action for Trumpian agents
censorDelete :: Agent -> Table -> Table
censorDelete a table = sort $ (a, (newN, (aX, aY, aZ), aType, aProp)):newTable
  where
    Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
    newN = aN \\ aZ
    newTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp))]


-- cencorship action for strong Trumpian agents
censorBlock :: Agent -> Table -> Table
censorBlock a table = sort $ (a, (newN, (aX, aY, aZ), aType, aProp)):newTable
  where
    Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
    newN = aN \\ aZ
    stripTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp))]
    newTable   = adjust a aZ stripTable
    -- function to remove a's number from all agents in aZ
    adjust :: Agent -> [Agent] -> Table -> Table
    adjust _   _    []                                           = []
    adjust ags agsZ ((b, (bN, (bX, bY, bZ), bType, bProp)):rest) =
      if b `elem` agsZ
        then (b, (bN \\ [ags], (bX, bY, bZ), bType, bProp)):
             adjust ags agsZ rest
        else (b, (bN, (bX, bY, bZ), bType, bProp))         :
             adjust ags agsZ rest


numbersTable :: Table -> [(Agent,[Agent])]
numbersTable [] = []
numbersTable ((a,(aN,(_aX,_aY,_aZ),_aType,_aProp)):rest) =
  (a,aN) : numbersTable rest

unreliableIsolated :: Table -> Bool
unreliableIsolated t = all (intersectionEmpty t) aNs where
  rTable = filter (\x -> fst x `elem` reliable t) t
  aNs = map snd (numbersTable rTable)
  intersectionEmpty :: Table -> [Agent] -> Bool
  intersectionEmpty table list
      | null $ unreliable table `intersect` list = True
      | otherwise                                = False


unreliableStrongIsolated :: Table -> Bool
unreliableStrongIsolated t = unreliableIsolated t &&
                             all (intersectionEmpty t) aNs where
  uTable = filter (\x -> fst x `elem` unreliable t) t
  aNs = map snd (numbersTable uTable)
  intersectionEmpty :: Table -> [Agent] -> Bool
  intersectionEmpty table list
      | null $ reliable table `intersect` list = True
      | otherwise                              = False



-- new definitions of completeness
isoComplete :: Table -> Bool
isoComplete table = completeR table && unreliableIsolated table

strongIsoComplete :: Table -> Bool
strongIsoComplete table = completeR table && unreliableStrongIsolated table


-- check whether a node is solved
solvedIso :: Node -> Bool
solvedIso (table, _, _) = isoComplete table

solvedStrongIso :: Node -> Bool
solvedStrongIso (table, _, _) = strongIsoComplete table

-- use the search tree to find solutions
solveNsIso :: [Node] -> [Node]
solveNsIso = search extendNode solvedIso

solveNsStrongIso :: [Node] -> [Node]
solveNsStrongIso = search extendNode solvedStrongIso

-- print calling sequences that complete the network
-- with the definitions of completeness above
solveAndShowIso :: Table -> Protocol -> IO ()
solveAndShowIso t p = solveShowHistOfIso [(t, [], p)]

solveAndShowStrongIso :: Table -> Protocol -> IO ()
solveAndShowStrongIso t p = solveShowHistOfStrongIso [(t, [], p)]

-- print history
solveShowHistOfIso :: [ Node ] -> IO ()
solveShowHistOfIso = sequence_ . fmap showHistOf . solveNsIso

solveShowHistOfStrongIso :: [ Node ] -> IO ()
solveShowHistOfStrongIso = sequence_ . fmap showHistOf . solveNsStrongIso

-- check if a graph is solvable
solvableIso :: Table -> Protocol -> Bool
solvableIso t p = solveNsIso [(t, [], p)] /= []

solvableStrongIso :: Table -> Protocol -> Bool
solvableStrongIso t p = solveNsStrongIso [(t, [], p)] /= []


-- see for yourself attitude
callSFY :: (Agent, Agent) -> Table -> [Table]
callSFY (a,b) table = let
  Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
  Just (bN, (bX, bY, bZ), bType, bProp) = lookup b table
  newN = merge aN bN
  disagreementsX = (aX `intersect` bY) `union` (bX `intersect` aY) `union` (aX `intersect` bZ) `union` (bX `intersect` aZ)
  disagreementsY = (aX `intersect` bY) `union` (bX `intersect` aY) `union` (aY `intersect` bZ) `union` (bY `intersect` aZ)
  newX = merge aX bX \\ disagreementsX
  newY = merge aY bY \\ disagreementsY
  new_aZ = aZ `union` (aX `intersect` bY) `union` (bX `intersect` aY)
  new_bZ = bZ `union` (aX `intersect` bY) `union` (bX `intersect` aY)
  stripTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp)), (b, (bN, (bX, bY, bZ), bType, bProp))]
  addedTable = sort $ (a, (newN, (newX, newY, new_aZ), aType, aProp)):(b, (newN, (newX, newY, new_bZ), bType, bProp)):stripTable
 in
   if possible table (a,b)
      then typeBehavior [(a,aType,aProp),(b,bType,bProp)] addedTable (a,b)
      else error "forbidden call!"


callsSFY :: Seq -> Table -> [Table]
callsSFY [] table = [table]
callsSFY cs table = concatMap (callsSFY (tail cs)) (callSFY (head cs) table)

extendNodeSFY :: Node -> [Node]
extendNodeSFY (table, hist, prot) = [(newTable, hist ++ [(x,y)], prot) | (x,y) <- candidates (table, hist, prot), newTable <- callSFY (x,y) table]

solveNsSFYR :: [Node] -> [Node]
solveNsSFYR = search extendNodeSFY solvedR

solveAndShowSFYR :: Table -> Protocol -> IO()
solveAndShowSFYR t p = solveShowHistOfSFYR [(t, [], p)]

solveShowHistOfSFYR :: [Node] -> IO()
solveShowHistOfSFYR = sequence_ . fmap showHistOf . solveNsSFYR


-- sabotage
-- cut link between two agents
cut :: (Agent, Agent) -> Table -> Table
cut (a,b) table = sort $ (a, (new_aN, (aX, aY, aZ), aType, aProp)):
                         (b, (new_bN, (bX, bY, bZ), bType, bProp)):
                         newTable
  where
    Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
    Just (bN, (bX, bY, bZ), bType, bProp) = lookup b table
    new_aN = aN \\ [b]
    new_bN = bN \\ [a]
    newTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp)),
                         (b, (bN, (bX, bY, bZ), bType, bProp))]

-- finds all the connections in a table
connections :: Table -> [(Agent, Agent)]
connections []                                                = []
connections ((a, (aN, (_aX, _aY, _aZ), _aType, _aProp)):rest) =
  sort $ makelist a aN ++ connections rest
  where
    makelist :: Agent -> [Agent] -> [(Agent, Agent)]
    makelist _ []      = []
    makelist c (b:cNs) = (c,b): makelist c cNs

-- finds all the non-reflexive connections in a table
filteredConnections :: Table -> Agent -> (Agent, Agent) ->
                           [(Agent, Agent)]
-- a is the saboteur and bc is the call taking place
filteredConnections table a (b,c) =
  filter (\x -> fst x /= a && (fst x == b || fst x == c)) newTable
  where
    newTable = filter (uncurry (/=)) (connections table)


type SabTable = (Table, [(Agent, (Agent, Agent))])

-- SabNode keeps track of which agent cut which links
type SabNode = (SabTable,Seq,Protocol)

-- new version of call
callSab :: (Agent, Agent) -> SabTable -> [SabTable]
callSab (a,b) (table, sabhist) = let
  Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
  Just (bN, (bX, bY, bZ), bType, bProp) = lookup b table

  -- Leeches do not share numbers
  -- FactCheckers do not update their numbers
  -- (and therefore do also not share any)
  new_aN | aType == FactChecker = aN
         | bType == Leech       = aN
         | otherwise            = merge aN bN
  new_bN | bType == FactChecker = bN
         | aType == Leech       = bN
         | otherwise            = merge aN bN

  disagreementsX = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aX `intersect` bZ)
                                       `union` (bX `intersect` aZ)

  disagreementsY = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aY `intersect` bZ)
                                       `union` (bY `intersect` aZ)

  -- FactCheckers do not tell which agents are unreliable
  -- (this could be an option as well)
  new_aX | bType == Leech       = aX
         | bType == FactChecker = aX `union` [b] \\ (aX `intersect` bZ)
         | otherwise            = merge aX bX \\ disagreementsX
  new_bX | aType == Leech       = bX
         | aType == FactChecker = bX `union` [a] \\ (bX `intersect` aZ)
         | otherwise            = merge aX bX \\ disagreementsX

  new_aY | bType == Leech       = aY
         | bType == FactChecker = aY \\ (aY `intersect` bZ)
         | otherwise            = merge aY bY \\ disagreementsY
  new_bY | aType == Leech       = bY
         | aType == FactChecker = bY \\ (bY `intersect` aZ)
         | otherwise            = merge aY bY \\ disagreementsY

  new_aZ | bType == Leech       = aZ
         | bType == FactChecker = aZ `union` (aX `intersect` bZ)
                                     `union` (bX `intersect` aZ)
         | otherwise            = merge aZ bZ `union` (aX `intersect` bY)
                                              `union` (bX `intersect` aY)
  new_bZ | aType == Leech       = bZ
         | bType == FactChecker = bZ `union` (aX `intersect` bY)
                                     `union` (bX `intersect` aY)
         | otherwise            = merge aZ bZ `union` (aX `intersect` bY)
                                              `union` (bX `intersect` aY)

  stripTable = table \\ [(a, (aN, (aX, aY, aZ), aType, aProp)),
                         (b, (bN, (bX, bY, bZ), bType, bProp))]
  newTable   = sort $
                (a, (new_aN, (new_aX, new_aY, new_aZ), aType, aProp)) :
                (b, (new_bN, (new_bX, new_bY, new_bZ), bType, bProp)) :
                stripTable
 in
   if possible table (a,b)
      then typeBehaviorSab [(a,aType,aProp),(b,bType,bProp)]
                           (newTable, sabhist) (a,b)
      else error "forbidden call!"


typeBehaviorSab :: [(Agent, Agenttype, Agentproperty)] -> SabTable
                           -> (Agent, Agent) -> [SabTable]
typeBehaviorSab [] (table, sabhist) _ = [(table, sabhist)]
typeBehaviorSab ((a,aType,aProp):rest) (table, sabhist) (b,c)
  | aType == AlternatingBluffer && aProp == None
      = typeBehaviorSab rest (alternate a table,sabhist) (b,c)
  | aType == AlternatingBluffer && aProp == TrumpianDel
      = typeBehaviorSab rest
               (alternate a (censorDelete a table), sabhist) (b,c)
  | aType == AlternatingBluffer && aProp == TrumpianBlock
      = typeBehaviorSab rest
               (alternate a (censorBlock a table), sabhist) (b,c)
  | aType == Reliable           && aProp == None
      = typeBehaviorSab rest (table, sabhist) (b,c)
  | aType == Reliable           && aProp == TrumpianDel
      = typeBehaviorSab rest (censorDelete a table, sabhist) (b,c)
  | aType == Reliable           && aProp == TrumpianBlock
      = typeBehaviorSab rest (censorBlock a table, sabhist) (b,c)
  | aType == Saboteur           && aProp == None
      = concat [ typeBehaviorSab rest (cut unluckyPair table,
                         sabhist ++ [(a, unluckyPair)]) (b,c)   |
                 unluckyPair <- filteredConnections table a (b,c)]
  | otherwise
      = typeBehaviorSab rest (table, sabhist) (b,c)


callsSab :: Seq -> SabTable -> [SabTable]
callsSab [] sabtable = [sabtable]
callsSab cs sabtable = concatMap (callsSab (tail cs))
                                    (callSab (head cs) sabtable)


stuck :: SabNode -> Bool
stuck ((table,_), hist, prot) = not (complete table) &&
                                null (candidates (table, hist, prot))

extendSabNode :: SabNode -> [SabNode]
extendSabNode ((table, sabhist), hist, prot) =
  [(newTable, hist ++ [(x,y)], prot) | (x,y) <- candidates (table, hist, prot),
                                       newTable <- callSab (x,y) (table, sabhist)]

saboteurGame :: [SabNode] -> [SabNode]
saboteurGame = search extendSabNode stuck

saboteurGameShow :: Table -> Protocol -> IO()
saboteurGameShow t p = saboteurGameShowHistOf [((t, []), [], p)]

saboteurGameShowHistOf :: [SabNode] -> IO()
saboteurGameShowHistOf = sequence_ . fmap showSabHistOf . saboteurGame

showSabHistOf :: SabNode -> IO()
showSabHistOf = print . sabHistOf where
  sabHistOf ((_,sabhist),hist,_) = (hist, sabhist)


sabFindHistOf :: SabNode -> (Seq,[(Agent,(Agent,Agent))])
sabFindHistOf ((_,sabhist),hist,_) = (hist,sabhist)

sabGameFind :: SabTable -> Protocol -> [(Seq,[(Agent,(Agent,Agent))])]
sabGameFind t p = solveFindSabHistOf [(t, [], p)]

solveFindSabHistOf :: [SabNode] -> [(Seq,[(Agent,(Agent,Agent))])]
solveFindSabHistOf = fmap sabFindHistOf . saboteurGame

filterHistSabHist :: [(Seq,[(Agent,(Agent,Agent))])] -> [(Seq,[(Agent,(Agent,Agent))])]
filterHistSabHist [] = []
filterHistSabHist ((hist,sabhist):rest)
  | null sabhist = filterHistSabHist rest
  | otherwise    = (hist,sabhist) : filterHistSabHist rest

sabCannotHarm :: Table -> Protocol -> Bool
sabCannotHarm t p = null $ filterHistSabHist $ sabGameFind (t,[]) p


-- broadcast calls
-- update the Table with a broadcast call
broadcastCall :: (Agent, [Agent]) -> Table -> [Table]
broadcastCall (_,[]) table = [table]
broadcastCall (a,(b:brest)) table = let
  Just (aN, (aX, aY, aZ), aType, aProp) = lookup a table
  Just (bN, (bX, bY, bZ), bType, bProp) = lookup b table

  -- Leeches do not share numbers
  -- Fact-checkers do not update their numbers
  -- (and therefore do also not share any)
  new_bN | bType == FactChecker = bN
         | aType == Leech       = bN
         | otherwise            = merge aN bN

  disagreementsX = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aX `intersect` bZ)
                                       `union` (bX `intersect` aZ)

  disagreementsY = (aX `intersect` bY) `union` (bX `intersect` aY)
                                       `union` (aY `intersect` bZ)
                                       `union` (bY `intersect` aZ)

  -- Fact-checkers do not tell which agents are unreliable
  -- (this could be an option as well)
  new_bX | aType == Leech       = bX
         | aType == FactChecker = bX `union` [a] \\ (bX `intersect` aZ)
         | otherwise            = merge aX bX \\ disagreementsX

  new_bY | aType == Leech       = bY
         | aType == FactChecker = bY \\ (bY `intersect` aZ)
         | otherwise            = merge aY bY \\ disagreementsY

  new_bZ | aType == Leech       = bZ
         | bType == FactChecker = bZ `union` (aX `intersect` bY)
                                     `union` (bX `intersect` aY)
         | otherwise            = merge aZ bZ `union` (aX `intersect` bY)
                                              `union` (bX `intersect` aY)

  stripTable = table \\ [(b, (bN, (bX, bY, bZ), bType, bProp))]
  newTable   = broadcastCall (a,brest)
                      (sort $ (b, (new_bN, (new_bX, new_bY, new_bZ), bType, bProp)) :
                      stripTable)
 in
   if possible table (a,b)
      then typeBehavior [(a,aType,aProp),(b,bType,bProp)] (head newTable) (a,b)
      else error "forbidden call!"

-- multiple calls
broadcastCalls :: [(Agent,[Agent])] -> Table -> [Table]
broadcastCalls [] table = [table]
broadcastCalls cs table = concatMap (broadcastCalls (tail cs)) (broadcastCall (head cs) table)
