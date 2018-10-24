{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Consensus2 where

import Control.Monad
import Data.Foldable (find, toList)
import Data.Maybe (mapMaybe, listToMaybe, isJust, fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Debug.Trace

import qualified Test.QuickCheck as QC
import           Test.QuickCheck (Arbitrary(..), (==>), (===))
import qualified Test.QuickCheck.Arbitrary as QC

newtype ReplicaId = ReplicaId { unReplicaId :: Int } deriving newtype (Eq, Ord)

instance Show ReplicaId where
  show (ReplicaId n) = "S" <> show n

newtype Timestamp = Timestamp (ReplicaId, Int) deriving (Eq, Ord)

instance Show Timestamp where
  show (Timestamp (r, n)) = show r <> "." <> show n

replica :: Timestamp -> ReplicaId
replica (Timestamp (r, _)) = r

-- | Local partial order on timestamps. Only timestamps from the same replica
-- are comparable, and are compared by local timestamp.
localLE :: Timestamp -> Timestamp -> Bool
localLE (Timestamp (r1, t1)) (Timestamp (r2, t2)) = r1 == r2 && t1 <= t2

newtype CausalityDiagram = CausalityDiagram
  { unCausalityDiagram :: Set (Timestamp, Timestamp)
  } deriving (Eq, Show)
  -- Invariant: pairs must be incomparable by `localLE`

-- | Check whether a given timestamp is `globalLE` some timestamp in the diagram.
inCD :: Timestamp -> CausalityDiagram -> Bool
inCD ts (CausalityDiagram events) = any (\(from, to) -> ts `localLE` from || ts `localLE` to) events

-- A CausalityDiagram induces a partial ordering on timestamps `globalLE`
-- that is the transitive closure of the set of pairs and `localLE`

-- | Keep only events that are `globalLE` the given timestamp
restrictLE :: Timestamp -> CausalityDiagram -> CausalityDiagram
restrictLE top = undefined

type Proposal = Timestamp -- We ignore the proposal payload for now

data History = History
  { replicas :: Set ReplicaId
  , causality :: CausalityDiagram
  , proposals :: Set Proposal
  } deriving (Eq, Show)

-- | Keep only events that are `globalLE` the given timestamp
restrictLE_History :: Timestamp -> History -> History
restrictLE_History top (History r cd proposals) =
  let cd' = restrictLE top cd in
  History r cd' (Set.filter (`inCD` cd') proposals)

-- | For each replica, return the proposals it has seen, in order.
proposalHistories :: History -> Map ReplicaId [Proposal]
proposalHistories history = error "magic!"

-- Invariant: timestamps sorted by causal order (with respect to some history)
type Path = [Timestamp]

-- Invariant: all paths have the same start and end
type MultiPath = Set Path

-- | Subsets of of size N of the given set.
subsetsOfN :: Int -> Set a -> [Set a]
subsetsOfN n = error "magic"

potentialAcceptingRounds :: History -> [(Proposal, Set ReplicaId)]
potentialAcceptingRounds history = do
  let proposalHistories' = proposalHistories history
  let majority = majorityOf (Set.size (replicas history))
  p <- Set.toList $ proposals history
  otherReplicas <- subsetsOfN (majority - 1) (replicas history)
  guard $ all
    (\r -> let seenProposals = fromMaybe [] (Map.lookup r proposalHistories') in
           seenProposals == [] || [p] `List.isPrefixOf` seenProposals)
    otherReplicas
  pure (p, Set.insert (replica p) otherReplicas)

majorityOf :: Int -> Int
majorityOf n = (n `div` 2) + 1

------------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------------

mkHistory :: [Int] -> [(Int, Int)] -> [((Int, Int), (Int, Int))] -> History
mkHistory replicas proposals cd =
  History
    (Set.fromList (map ReplicaId replicas))
    (CausalityDiagram (Set.fromList (map (\(x, y) -> (mkTS x, mkTS y)) cd)))
    (Set.fromList (map mkTS proposals))

mkTS (x, y) = Timestamp (ReplicaId x, y)

(-->) = (,)

pattern S1 = 1
pattern S2 = 2
pattern S3 = 3
pattern S4 = 4
pattern S5 = 5

-- | Single proposal, clean run with no conflicts and no failures.
example1 :: History
example1 = mkHistory
  [S1,S2,S3]
  [(S1,0)]
  [                  (S2,2) --> (S1,3),  (S3,2) --> (S1,4)
  , (S1,0) --> (S2,1)
  , (S1,0) --> (S3,1)
  ]
