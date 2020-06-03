module Results where

import AgentTypes
import UnreliableGossip
import Data.List
import Test.QuickCheck

unreliableTerminal :: Table -> Bool
unreliableTerminal [] = True
unreliableTerminal ((a,(aN,(_aX,_aY,_aZ),aType,_aProp)):rest) =
  not (aType /= Reliable && aN /= [a]) && unreliableTerminal rest


-- find isolated agents in a network
isolatedAgents :: Table -> [Agent]
isolatedAgents table = loop table table [] where
  loop :: Table -> Table -> [Agent] -> [Agent]
  loop _ [] listOfAgents = listOfAgents
  loop t ((a,(aN,(aX,aY,aZ),aType,aProp)):rest) listOfAgents =
    if aN == [a] && nobodyLikesMe a othersTable
      then loop t rest (a:listOfAgents)
      else loop t rest listOfAgents where
        othersTable = t \\ [(a,(aN,(aX,aY,aZ),aType,aProp))]
        nobodyLikesMe :: Agent -> Table -> Bool
        nobodyLikesMe _ [] = True
        nobodyLikesMe c ((_,(bN,(_,_,_),_,_)):trest) =
          c `notElem` bN && nobodyLikesMe c trest

-- delete isolated agents from network
deleteIsolated :: Table -> Table
deleteIsolated t = dI t t where
  dI _ [] = []
  dI table ((a,(aN,(aX,aY,aZ),aType,aProp)):rest) =
    if a `elem` isolatedAgents table
      then dI table rest
      else (a,(aN,(aX,aY,aZ),aType,aProp)) : dI table rest

-- turn a graph into a reliable counter-graph
reliableCounterGraph :: Table -> Table
reliableCounterGraph [] = []
reliableCounterGraph ((a, (aN, (aX, aY, _aZ), _aType, _aProp)):rest) =
  (a, (aN, (aX, aY, []), Reliable, None)) : reliableCounterGraph rest

-- turn a graph into a reliable subgraph
reliableSubGraph :: Table -> Table
reliableSubGraph table = rSG table where
  rSG [] = []
  rSG ((a, (aN, (aX, aY, _aZ), aType, aProp)):rest) =
    if aType == Reliable && aProp == None
      then (a, (new aN, (new aX, new aY, []), aType, aProp)) : rSG rest
      else rSG rest
      where
        new :: [Agent] -> [Agent]
        new = filter (\x -> x `elem` reliable table)


newtype ArbAgs = ArbAgs [Agent] deriving (Show,Eq,Ord)

instance Arbitrary ArbAgs where
  arbitrary = do
    -- change amount of agents in graphs
    n <- choose (3,5)
    return (ArbAgs [1..(n::Agent)])

getrandomLength :: IO Int
getrandomLength = do
  (ArbAgs as) <- generate arbitrary
  return (length as)

powerset :: [a] -> [[a]]
powerset []     = [[]]
powerset (x:xs) = map (x:) pxs ++ pxs where pxs = powerset xs

-- generate arbitrary table
newtype ArbTable = ArbT Table deriving (Show,Eq,Ord)

instance Arbitrary ArbTable where
  arbitrary = do
    ArbAgs ags <- arbitrary
    t <- mapM (\i -> do
      iType <- elements [Reliable, AlternatingBluffer]
      n' <- sublistOf (ags \\ [i])
      let n = sort $ i : n'
      -- generate initial graphs, uncomment next line:
      return (i,(n,([i],[],[]),iType,None))) ags
      -- generate random graphs, uncomment next three lines:
      -- s' <- sublistOf (n \\ [i])
      -- let s = sort $ i : s'
      -- return (i,(n, (s,[],[]), iType, None))) ags
    -- to have also isolated agents, uncomment next line:
    --return $ ArbT t
    -- only graphs without isolated agents (note: [] is now valid):
    return $ ArbT (deleteIsolated t)

unpack :: ArbTable -> Table
unpack (ArbT t) = t

-- generate arbitrary table in which unreliable agents are terminal
newtype ArbTableUT = ArbTUT Table deriving (Show,Eq,Ord)

instance Arbitrary ArbTableUT where
  arbitrary = do
    ArbAgs ags <- arbitrary
    t <- mapM (\i -> do
      iType <- elements [Reliable, AlternatingBluffer]
      n' <- sublistOf (ags \\ [i])
      let n | iType == Reliable = sort $ i : n'
            | otherwise         = [i]
      -- generate initial graphs, uncomment next line:
      return (i,(n,([i],[],[]),iType,None))) ags
      -- generate random graphs, uncomment next four lines:
      -- s' <- sublistOf (n \\ [i])
      -- let s | iType == Reliable = sort $ i : s'
      ---      | otherwise         = [i]
      --return (i,(n,(s,[],[]),iType,None))) ags
    -- to have also isolated agents, uncomment next line:
    -- return $ arBTUT t
    -- only graphs without isolated agents (note: [] is now valid):
    return $ ArbTUT (deleteIsolated t)
