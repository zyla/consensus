{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

module Consensus where

import Control.Monad
import Data.Foldable (find, toList)
import Data.Maybe (mapMaybe, listToMaybe, isJust)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (nub, intercalate)
import Debug.Trace

import qualified Test.QuickCheck as QC
import           Test.QuickCheck (Arbitrary(..), (==>), (===))
import qualified Test.QuickCheck.Arbitrary as QC

newtype ReplicaId = ReplicaId { unReplicaId :: Text } deriving newtype (Eq, Show, Ord)

instance Arbitrary ReplicaId where
  arbitrary = (\n -> ReplicaId (Text.pack ("S" <> show (abs n :: Int)))) <$> arbitrary

newtype OpId = OpId (ReplicaId, Int) deriving (Eq, Ord)

instance Arbitrary OpId where
  arbitrary = OpId . fmap abs <$> arbitrary

instance Show OpId where
  show (OpId (ReplicaId r, n)) | Text.null r = show n -- special case for test data
  show (OpId (ReplicaId r, n)) = Text.unpack r <> "/" <> show n

data Op a = Op
  { opId :: OpId
  , payload :: a
  } deriving (Eq, Show, Ord)

-- | List with the additional invariant that there are no duplicates.
--
-- TODO: use https://hackage.haskell.org/package/ordered-containers instead
newtype UniqueList a = UniqueList { getUniqueList :: [a] } deriving newtype (Eq, Ord, Show)

mkUniqueList :: Eq a => [a] -> UniqueList a
mkUniqueList = UniqueList . nub

fromSetUL :: Set a -> UniqueList a
fromSetUL = UniqueList . Set.toList

instance Eq a => Semigroup (UniqueList a) where
  UniqueList a <> UniqueList b = mkUniqueList (a <> b)

instance Eq a => Monoid (UniqueList a) where
  mempty = UniqueList mempty

instance (Eq a, Arbitrary a) => Arbitrary (UniqueList a) where
  arbitrary = mkUniqueList <$> arbitrary
  shrink = map mkUniqueList . shrink . getUniqueList

takeUL :: Int -> UniqueList a -> UniqueList a
takeUL n (UniqueList xs) = UniqueList (take n xs)

lengthUL :: UniqueList a -> Int
lengthUL (UniqueList xs) = length xs

elemUL :: Eq a => a -> UniqueList a -> Bool
elemUL x (UniqueList xs) = x `elem` xs

-- | History. Mapping from replicas to the sequence of operations seen by that replica.
newtype History = History { unHistory :: Map ReplicaId (UniqueList OpId) }
  deriving (Eq)

instance Arbitrary History where
  arbitrary = QC.sized $ \size -> do
    nreplicas <- QC.choose (1, size)
    let replicas = map (\n -> ReplicaId $ Text.pack $ "S" <> show (n :: Int)) [1..nreplicas]
    nops <- QC.choose (1, size)
    let ops = map (\n -> OpId (ReplicaId "", n)) [1..nops]
    fmap (History . Map.fromList) $ forM replicas $ \replica ->
      (,) replica <$> mkUniqueList <$> QC.listOf (QC.oneof (map pure ops))

  shrink = map History . shrink . unHistory

instance Show History where
  show (History h) | Map.null h = "(empty history)"
  show (History h) = unlines $
    map (\(replica, ops) ->
      Text.unpack (unReplicaId replica) <> ": " <>
        intercalate " " (map show (getUniqueList ops))) $
    Map.toList h

emptyH :: History -> Bool
emptyH (History h) = Map.null h || all (null . getUniqueList) h

-- | Find committed operation sets for a given history.
--
-- A committed operation set is the smallest set of operations `ops` such that:
-- * there's a majority of replicas where `ops` is a prefix of their operation sequence
-- * (some magic property)
--
-- There should be only one such set. This function returns all of them for validation purposes.
--
-- Returns the set of operations and the set of replicas having these operations as prefix.
committedOps' :: History -> Set (Set OpId, Set ReplicaId)
committedOps' (History history) | Map.null history = Set.empty
committedOps' (History history) =
  let
    majority = majorityOf (Map.size history)
    maxSize = maximum (fmap lengthUL history)

    prefixesOfLength :: Int -> Set (Set OpId, Set ReplicaId)
    prefixesOfLength n =
      let
        -- History, truncated to the prefix length (n)
        historyPrefix = Map.filter (\xs -> lengthUL xs == n) $ fmap (takeUL n) history

        -- Map from sets of operations to replicas with these ops as prefix.
        replicasWithOpsAsPrefix :: Map (Set OpId) (Set ReplicaId)
        replicasWithOpsAsPrefix =
          Map.fromListWith (<>) $
          map (\(replica, ops) -> (Set.fromList (getUniqueList ops), Set.singleton replica)) $
          Map.toList historyPrefix

      in
        -- Find majorities
        Set.fromList $ 
        filter (\(ops, replicas) -> length replicas >= majority) $
        Map.toList replicasWithOpsAsPrefix
  in
    mconcat $ take 1 $ filter (not . Set.null) $ map prefixesOfLength [1..maxSize]

committedOps :: History -> Maybe (Set OpId, Set ReplicaId)
committedOps = listToMaybe . Set.toList . committedOps'

majorityOf :: Int -> Int
majorityOf n = (n `div` 2) + 1

------------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------------

-- | If a committed op set exists, it is unique.
prop_onlyOneCommittedOpSet :: History -> QC.Property
prop_onlyOneCommittedOpSet h =
  let ops = committedOps' h in
  QC.counterexample ("ops: " <> show ops) $
  QC.classify (Set.null ops) "none" $
  QC.classify (not (Set.null ops)) "some" $
  Set.size ops <= 1

-- | Send all ops to all nodes, in arbitrary order.
propagateAll :: History -> History
propagateAll (History history) =
  let
    allOps :: UniqueList OpId
    allOps = fromSetUL $ Set.unions $ map (Set.fromList . getUniqueList) $ toList history
  in
    History $ fmap (<>allOps) history

-- | If we propagate all ops to all nodes, we should get a committed op set.
prop_committedAfterPropagate :: History -> QC.Property
prop_committedAfterPropagate h =
  let propagated = propagateAll h in
  QC.counterexample ("propagated: \n" <> show propagated) $
  not (emptyH h) ==>
  Set.size (committedOps' propagated) == 1

-- | What ops can we exchange between replicas?
possiblePropagations :: History -> [(ReplicaId, OpId)]
possiblePropagations (History history) = do
  op <- Set.toList $ Set.unions $ map (Set.fromList . getUniqueList) $ toList history
  (replica, knownOps) <- Map.toList history
  guard $ not $ op `elemUL` knownOps
  pure (replica, op)

propagate :: ReplicaId -> OpId -> History -> History
propagate replica op (History h) = History $ Map.alter (fmap (<>mkUniqueList [op])) replica h

-- | If a committed op set exists, then propagating information between replicas
-- won't change it.
prop_propagationDoesNotChangeCommittedOpSet :: History -> QC.Property
prop_propagationDoesNotChangeCommittedOpSet h =
  let propagations = possiblePropagations h in
  (not (null propagations) ==>) $

  QC.forAll (QC.oneof (map pure propagations)) $ \(replica, op) ->
  let
    propagated = propagate replica op h
    opsBefore = fmap fst (committedOps h)
    opsAfter = fmap fst (committedOps propagated)

  in

  QC.counterexample ("propagated: \n" <> show propagated) $
  QC.counterexample ("ops before: " <> show (Set.toList <$> opsBefore)) $
  QC.counterexample ("ops after: " <> show (Set.toList <$> opsAfter)) $

  isJust opsBefore ==>
  opsAfter === opsBefore

op n = OpId (ReplicaId "", n)

h0 :: History
h0 = History $ Map.fromList
  [ (ReplicaId "S1", mkUniqueList [op 1, op 2])
  , (ReplicaId "S2", mkUniqueList [op 2, op 1])
  , (ReplicaId "S3", mkUniqueList [op 3, op 2])
  ]

h1 :: History
h1 = History $ Map.fromList
  [ (ReplicaId "S1", mkUniqueList [op 1, op 2])
  , (ReplicaId "S2", mkUniqueList [])
  , (ReplicaId "S3", mkUniqueList [op 2, op 1])
  ]
