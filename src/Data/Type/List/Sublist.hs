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
  , takeProd, prefixLens, takeIndex
  -- ** Suffix
  , Suffix(..)
  , dropProd, suffixLens, dropIndex
  -- * Append
  , Append(..)
  , prefixToAppend, suffixToAppend
  , appendToPrefix, appendToSuffix, splitAppend
  -- ** Product
  , splitProd, appendProd, splitProdIso
  -- ** Index
  , splitIndex
  ) where

import           Control.Applicative
import           Data.Bifunctor
import           Data.Kind
import           Data.Profunctor
import           Data.Type.List.Prod
import           Data.Type.Universe

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

-- | A lens into the prefix of a 'Prod'.
--
-- Read this type signature as:
--
-- @
-- 'prefixLens'
--     :: Prefix as bs
--     -> Lens' (Prod f bs) (Prod f as)
-- @
prefixLens
    :: forall as bs g f. Functor f
    => Prefix as bs
    -> (Prod g as -> f (Prod g as))
    -> Prod g bs
    -> f (Prod g bs)
prefixLens p = prefixToAppend p $ \a -> splitProdIso a . _1
  where
    _1 :: (a -> f b) -> (a, c) -> f (b, c)
    _1 f (x, y) = (, y) <$> f x

-- | Take items from a 'Prod' corresponding to a given 'Prefix'.
takeProd :: Prefix as bs -> Prod f bs -> Prod f as
takeProd p = getConst . prefixLens p Const

-- | A @'Suffix' as bs@ witnesses that @as@ is a suffix of @bs@.
--
-- Some examples:
--
-- @
-- SufZ                      :: Suffix '[1,2,3] '[1,2,3]
-- SufS SufZ                 :: Suffix   '[2,3] '[1,2,3]
-- SufS (SufS SufZ)          :: Suffix     '[3] '[1,2,3]
-- SufS (SufS (SufS (SufZ))) :: Suffix      '[] '[1,2,3]
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

-- | A lens into the suffix of a 'Prod'.
--
-- Read this type signature as:
--
-- @
-- 'suffixLens'
--     :: Suffix as bs
--     -> Lens' (Prod f bs) (Prod f as)
-- @
suffixLens
    :: forall as bs g f. Functor f
    => Suffix as bs
    -> (Prod g as -> f (Prod g as))
    -> Prod g bs
    -> f (Prod g bs)
suffixLens p = suffixToAppend p $ \a -> splitProdIso a . _2
  where
    _2 :: (a -> f b) -> (c, a) -> f (c, b)
    _2 f (x, y) = (x ,) <$> f y

-- | Drop items from a 'Prod' corresponding to a given 'Suffix'.
dropProd :: Suffix as bs -> Prod f bs -> Prod f as
dropProd p = getConst . suffixLens p Const

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

-- | Witness an isomorphism between 'Prod' and two parts that compose it.
--
-- Read this type signature as:
--
-- @
-- 'splitProdIso'
--     :: Append as  bs  cs
--     -> Iso (Prod f cs)            (Prod f cs)
--            (Prod f as, Prod f bs) (Prod f as, Prod f bs)
-- @
--
-- This can be used with the combinators from the lens library.
--
-- The 'Append' tells the point to split the 'Prod' at.
splitProdIso
    :: (Profunctor p, Functor f)
    => Append as bs cs
    -> p (Prod g as, Prod g bs) (f (Prod g as, Prod g bs))
    -> p (Prod g cs)            (f (Prod g cs))
splitProdIso a = dimap (splitProd a) ((fmap . uncurry) (appendProd a))

-- | Split a 'Prod' into a prefix and suffix.  Basically 'takeProd'
-- and 'dropProd' combined.
splitProd
    :: Append as bs cs
    -> Prod f cs
    -> (Prod f as, Prod f bs)
splitProd = \case
    AppZ   -> (Ø,)
    AppS a -> \case
      x :< xs -> first (x :<) . splitProd a $ xs

-- | Append two 'Prod's together according to an 'Append'.
appendProd
    :: Append as bs cs
    -> Prod f as
    -> Prod f bs
    -> Prod f cs
appendProd = \case
    AppZ   -> \_ -> id
    AppS a -> \case
      x :< xs -> (x :<) . appendProd a xs

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
-- of the list, it'll return 'Left'.  If it was int he second part, it'll
-- return 'Right'.
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
takeIndex
    :: Prefix as bs
    -> Index bs x
    -> Maybe (Index as x)
takeIndex p i = prefixToAppend p $ either Just (const Nothing)
                                 . (`splitIndex` i)

-- | Shave off the initial inhabitants of an 'Index', keeping only indices
-- a part of a given suffix  If the index is out of range, 'Nothing' will
-- be returned.
dropIndex
    :: Suffix as bs
    -> Index bs x
    -> Maybe (Index as x)
dropIndex s i = suffixToAppend s $ either (const Nothing) Just
                                 . (`splitIndex` i)
