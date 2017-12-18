module AgentTypes where

type Agent = Int

data Agenttype = Reliable | AlternatingBluffer | Bluffer | Liar |
                 NoisyAgent | Saboteur | StrongSaboteur | Leech |
                 FactChecker
  deriving (Eq,Ord,Show)

data Agentproperty = None | Consistent | TrumpianDel | TrumpianBlock
  deriving (Eq,Ord,Show)

type Secret = Bool

type AgentInfo = (Agent, (Agenttype, Agentproperty), Secret)
