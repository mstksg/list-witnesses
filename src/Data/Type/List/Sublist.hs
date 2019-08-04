{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.List.Sublist
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Witnesses regarding sublists of lists.
module Data.Type.List.Sublist (
  -- * Prefix and Suffix
  -- ** Prefix
    Prefix(..)
  , takeRec, prefixLens, takeIndex, weakenIndex
  -- ** Suffix
  , Suffix(..)
  , dropRec, suffixLens, dropIndex, shiftIndex
  -- * Append
  , Append(..)
  , prefixToAppend, suffixToAppend
  , appendToPrefix, appendToSuffix, splitAppend
  -- ** Application
  , splitRec, appendRec, splitRecIso
  , splitIndex
  -- * Interleave
  , Interleave(..)
  , interleaveRec, unweaveRec, interleaveRecIso
  , injectIndexL, injectIndexR, unweaveIndex
  ) where

import           Data.Bifunctor
import           Data.Kind
import           Data.Profunctor
import           Data.Type.Universe
import           Data.Vinyl.Core
import           Lens.Micro
import           Lens.Micro.Extras

-- | A @'Prefix' as bs@ witnesses that @as@ is a prefix of @bs@.
--
-- Some examples:
--
-- @
-- PreZ                    :: Prefix '[]      '[1,2,3]
-- PreS PreZ               :: Prefix '[1]     '[1,2,3]
-- PreS (PreS PreZ)        :: Prefix '[1,2]   '[1,2,3]
-- PreS (PreS (PreS PreZ)) :: Prefix '[1,2,3] '[1,2,3]
-- @
--
-- Rule of thumb for construction: the number of 'PreS' is the number of
-- items in the prefix.
--
-- This is essentially the first half of an 'Append', but is conceptually
-- easier to work with.
data Prefix :: [k] -> [k] -> Type where
    PreZ :: Prefix '[] as
    PreS :: Prefix  as bs -> Prefix  (a ': as) (a ': bs)

deriving instance Show (Prefix as bs)

-- | A lens into the prefix of a 'Rec'.
prefixLens :: Prefix as bs -> Lens' (Rec f bs) (Rec f as)
prefixLens p = prefixToAppend p $ \a -> splitRecIso a . _1

-- | Take items from a 'Rec' corresponding to a given 'Prefix'.
takeRec :: Prefix as bs -> Rec f bs -> Rec f as
takeRec p = view (prefixLens p)

-- | A @'Suffix' as bs@ witnesses that @as@ is a suffix of @bs@.
--
-- Some examples:
--
-- @
-- SufZ                    :: Suffix '[1,2,3] '[1,2,3]
-- SufS SufZ               :: Suffix   '[2,3] '[1,2,3]
-- SufS (SufS SufZ)        :: Suffix     '[3] '[1,2,3]
-- SufS (SufS (SufS SufZ)) :: Suffix      '[] '[1,2,3]
-- @
--
-- Rule of thumb for construction: the number of 'SufS' is the number of
-- items to "drop" before getting the suffix.
--
-- This is essentially the second half of an 'Append', but is conceptually
-- easier to work with.
data Suffix :: [k] -> [k] -> Type where
    SufZ :: Suffix as as
    SufS :: Suffix as bs -> Suffix as (b ': bs)

deriving instance Show (Suffix as bs)

-- | A lens into the suffix of a 'Rec'.
suffixLens :: Suffix as bs -> Lens' (Rec f bs) (Rec f as)
suffixLens p = suffixToAppend p $ \a -> splitRecIso a . _2

-- | Drop items from a 'Rec' corresponding to a given 'Suffix'.
dropRec :: Suffix as bs -> Rec f bs -> Rec f as
dropRec p = view (suffixLens p)

-- | An @'Append' as bs cs@ witnesses that @cs@ is the result of appending
-- @as@ and @bs@.
--
-- Some examples:
--
-- @
-- AppZ                     :: Append '[]  '[1,2]   '[1,2]
-- AppZ                     :: Append '[]  '[1,2,3] '[1,2,3]
-- AppS AppZ                :: Append '[0] '[1,2]   '[0,1,2]
-- @
--
-- Rule of thumb for construction: the number of 'AppS' is the number of
-- items in the /first/ list.
--
-- This basically combines 'Prefix' and 'Suffix'.
data Append :: [k] -> [k] -> [k] -> Type where
    AppZ :: Append '[] as as
    AppS :: Append as bs cs -> Append (a ': as) bs (a ': cs)

deriving instance Show (Append as bs cs)

-- | Witness an isomorphism between 'Rec' and two parts that compose it.
--
-- Read this type signature as:
--
-- @
-- 'splitRecIso'
--     :: Append as  bs  cs
--     -> Iso' (Rec f cs) (Rec f as, Rec f bs)
-- @
--
-- This can be used with the combinators from the lens library.
--
-- The 'Append' tells the point to split the 'Rec' at.
splitRecIso
    :: (Profunctor p, Functor f)
    => Append as bs cs
    -> p (Rec g as, Rec g bs) (f (Rec g as, Rec g bs))
    -> p (Rec g cs)           (f (Rec g cs))
splitRecIso a = dimap (splitRec a) ((fmap . uncurry) (appendRec a))

-- | Split a 'Rec' into a prefix and suffix.  Basically 'takeRec'
-- and 'dropRec' combined.
splitRec
    :: Append as bs cs
    -> Rec f cs
    -> (Rec f as, Rec f bs)
splitRec = \case
    AppZ   -> (RNil,)
    AppS a -> \case
      x :& xs -> first (x :&) . splitRec a $ xs

-- | Append two 'Rec's together according to an 'Append'.
appendRec
    :: Append as bs cs
    -> Rec f as
    -> Rec f bs
    -> Rec f cs
appendRec = \case
    AppZ   -> \_ -> id
    AppS a -> \case
      x :& xs -> (x :&) . appendRec a xs

-- | Convert a 'Prefix' to an 'Append', with an existential @bs@.
prefixToAppend
    :: Prefix as cs
    -> (forall bs. Append as bs cs -> r)
    -> r
prefixToAppend = \case
    PreZ   -> ($ AppZ)
    PreS p -> \f -> prefixToAppend p (f . AppS)

-- | Convert a 'Suffix' to an 'Append', with an existential @as@.
suffixToAppend
    :: Suffix bs cs
    -> (forall as. Append as bs cs -> r)
    -> r
suffixToAppend = \case
    SufZ   -> ($ AppZ)
    SufS s -> \f -> suffixToAppend s (f . AppS)

-- | Split an 'Append' into a 'Prefix' and 'Suffix'.  Basically
-- 'appendToPrefix' and 'appendToSuffix' at the same time.
splitAppend
    :: Append as bs cs
    -> (Prefix as cs, Suffix bs cs)
splitAppend = \case
    AppZ   -> (PreZ, SufZ)
    AppS a -> bimap PreS SufS . splitAppend $ a

-- | Convert an 'Append' to a 'Prefix', forgetting the suffix.
appendToPrefix :: Append as bs cs -> Prefix as cs
appendToPrefix = \case
    AppZ   -> PreZ
    AppS a -> PreS . appendToPrefix $ a

-- | Convert an 'Append' to a 'Suffix', forgetting the prefix
appendToSuffix :: Append as bs cs -> Suffix bs cs
appendToSuffix = \case
    AppZ   -> SufZ
    AppS a -> SufS . appendToSuffix $ a

-- | Split an 'Index' by an 'Append'.  If the 'Index' was in the first part
-- of the list, it'll return 'Left'.  If it was in the second part, it'll
-- return 'Right'.
--
-- This is essentially 'takeIndex' and 'dropIndex' at the same time.
splitIndex
    :: Append as bs cs
    -> Index cs x
    -> Either (Index as x) (Index bs x)
splitIndex = \case
    AppZ   -> Right
    AppS a -> \case
      IZ   -> Left IZ
      IS i -> first IS . splitIndex a $ i

-- | Shave off the final inhabitants of an 'Index', keeping only indices
-- a part of a given prefix.  If the index is out of range, 'Nothing' will
-- be returned.
--
-- This is essentially 'splitIndex', but taking only 'Left' results.
takeIndex
    :: Prefix as bs
    -> Index bs x
    -> Maybe (Index as x)
takeIndex p i = prefixToAppend p $ either Just (const Nothing)
                                 . (`splitIndex` i)

-- | Shave off the initial inhabitants of an 'Index', keeping only indices
-- a part of a given suffix  If the index is out of range, 'Nothing' will
-- be returned.
--
-- This is essentially 'splitIndex', but taking only 'Right' results.
dropIndex
    :: Suffix as bs
    -> Index bs x
    -> Maybe (Index as x)
dropIndex s i = suffixToAppend s $ either (const Nothing) Just
                                 . (`splitIndex` i)

-- | An index pointing to a given item in a prefix is also an index
-- pointing to the same item in the full list.  This "weakens" the bounds
-- of an index, widening the list at the end but preserving the original
-- index.  This is the inverse of 'takeIndex'.
weakenIndex
    :: Prefix as bs
    -> Index as x
    -> Index bs x
weakenIndex = \case
    PreZ   -> \case {}
    PreS p -> \case
      IZ   -> IZ
      IS i -> IS (weakenIndex p i)

-- | An index pointing to a given item in a suffix can be transformed into
-- an index pointing to the same item in the full list.  This is the
-- inverse of 'dropIndex'.
shiftIndex
    :: Suffix as bs
    -> Index as x
    -> Index bs x
shiftIndex = \case
    SufZ   -> id
    SufS s -> IS . shiftIndex s

-- | A @'Interleave' as bs cs@ witnesses that @cs@ is @as@ interleaved with
-- @bs. It is constructed by selectively zipping items from @as@ and @bs@
-- together, like mergesort or riffle shuffle.
--
-- You construct a 'Interleave' from @as@ and @bs@ by picking "which item" from
-- @as@ and @bs@ to add to @cs@.
--
-- Some examples:
--
-- @
-- IntL (IntL (IntR (IntR IntZ))) :: Interleave '[1,2] '[3,4] '[1,2,3,4]
-- IntR (IntR (IntL (IntL IntZ))) :: Interleave '[1,2] '[3,4] '[3,4,1,2]
-- IntL (IntR (IntL (IntR IntZ))) :: Interleave '[1,2] '[3,4] '[1,3,2,4]
-- IntR (IntL (IntR (IntL IntZ))) :: Interleave '[1,2] '[3,4] '[3,1,4,2]
-- @
--
-- @since 0.1.1.0
data Interleave :: [k] -> [k] -> [k] -> Type where
    IntZ :: Interleave '[] '[] '[]
    IntL :: Interleave as bs cs -> Interleave (a ': as) bs        (a ': cs)
    IntR :: Interleave as bs cs -> Interleave as        (b ': bs) (b ': cs)

deriving instance Show (Interleave as bs cs)

-- | Given two 'Rec's, interleave the two to create a combined 'Rec'.
--
-- @since 0.1.1.0
interleaveRec :: Interleave as bs cs -> Rec f as -> Rec f bs -> Rec f cs
interleaveRec = \case
    IntZ -> \case
      RNil -> \case
        RNil -> RNil
    IntL m -> \case
      x :& xs -> \ys -> x :& interleaveRec m xs ys
    IntR m -> \xs -> \case
      y :& ys -> y :& interleaveRec m xs ys

-- | Given a 'Rec', disinterleave it into two 'Rec's corresponding to an
-- 'Interleave'.
--
-- @since 0.1.1.0
unweaveRec :: Interleave as bs cs -> Rec f cs -> (Rec f as, Rec f bs)
unweaveRec = \case
    IntZ -> \case
      RNil -> (RNil, RNil)
    IntL m -> \case
      x :& xs -> first  (x :&) . unweaveRec m $ xs
    IntR m -> \case
      x :& xs -> second (x :&) . unweaveRec m $ xs

-- | Interleave an 'Index' on @as@ into a full index on @cs@, which is @as@
-- interleaved with @bs@.
--
-- @since 0.1.1.0
injectIndexL :: Interleave as bs cs -> Index as a -> Index cs a
injectIndexL = \case
    IntZ -> \case {}
    IntL m -> \case
      IZ -> IZ
      IS i -> IS (injectIndexL m i)
    IntR m -> IS . injectIndexL m

-- | Interleave an 'Index' on @bs@ into a full index on @cs@, which is @as@
-- interleaved with @bs@.
--
-- @since 0.1.1.0
injectIndexR :: Interleave as bs cs -> Index bs b -> Index cs b
injectIndexR = \case
    IntZ -> \case {}
    IntL m -> IS . injectIndexR m
    IntR m -> \case
      IZ -> IZ
      IS i -> IS (injectIndexR m i)

-- | Given an index on @cs@, disinterleave it into either an index on @as@
-- or on @bs@.
--
-- @since 0.1.1.0
unweaveIndex :: Interleave as bs cs -> Index cs c -> Either (Index as c) (Index bs c)
unweaveIndex = \case
    IntZ -> \case {}
    IntL m -> \case
      IZ   -> Left IZ
      IS i -> first IS $ unweaveIndex m i
    IntR m -> \case
      IZ   -> Right IZ
      IS i -> second IS $ unweaveIndex m i

-- | Witness an isomorphism between 'Rec' and two parts that interleave it.
--
-- Read this type signature as:
--
-- @
-- 'interleaveRecIso'
--     :: Interleave as  bs  cs
--     -> Iso' (Rec f cs) (Rec f as, Rec f bs)
-- @
--
-- This can be used with the combinators from the lens library.
--
-- The 'Interleave' tells how to unweave the 'Rec'.
--
-- @since 0.1.1.0
interleaveRecIso
    :: (Profunctor p, Functor f)
    => Interleave as bs cs
    -> p (Rec g as, Rec g bs) (f (Rec g as, Rec g bs))
    -> p (Rec g cs)           (f (Rec g cs))
interleaveRecIso m = dimap (unweaveRec m) ((fmap . uncurry) (interleaveRec m))
