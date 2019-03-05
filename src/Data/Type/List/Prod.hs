{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.List.Prod
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Parameterized heterogeneous list.
module Data.Type.List.Prod (
    Prod(..), pNil
  , headProd
  , tailProd
  , lensProd'
  , indexProd
  -- * Traversals
  , mapProd, traverseProd, foldMapProd, zipProd
  -- * Conversion
  -- ** With Singletons
  , prodSing, singProd
  -- ** Quantification
  , allProd
  , prodAll
  ) where

import           Control.Applicative
import           Data.Functor.Identity
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Type.Universe
import           GHC.Generics                 ((:*:)(..))

-- | This shows up in many places in the Haskell ecosystem: it's vinyl, or
-- a heterogeneous list parameterized by a functor.
--
-- A value of type
--
-- @
-- 'Prod' f '[a,b,c]
-- @
--
-- contains an @f a@, and @f b@, and an @f c@.
--
-- While this exists in my places, it's reproduced here to to provide
-- a canonical implementation.
data Prod :: (k -> Type) -> [k] -> Type where
    Ø    :: Prod f '[]
    (:<) :: f a -> Prod f as -> Prod f (a ': as)

infixr 5 :<

-- | Alias for 'Ø'
pNil :: Prod f '[]
pNil = Ø

-- | (Total) head of a 'Prod'.
headProd :: Prod f (a ': as) -> f a
headProd = \case
    x :< _ -> x

-- | (total) tail of a 'Prod'.
tailProd :: Prod f (a ': as) -> Prod f as
tailProd = \case
    _ :< xs -> xs

-- | Retrieve an element in a 'Prod' at a given index.
indexProd :: Index as x -> Prod f as -> f x
indexProd i = getConst . lensProd' i Const

-- | A type-preserving lens into a value in a 'Prod', given a 'Index'
-- indicating which value.  This lens cannot change the type of the value,
-- unlike "Data.Type.List.Edit.lensProd'.
--
-- Read this type signature as:
--
-- @
-- 'lensProd'
--     :: 'Index' as x
--     -> Lens' ('Prod' g as) (g x)
-- @
lensProd'
    :: forall as x g f. Functor f
    => Index as x
    -> (g x -> f (g x))
    -> Prod g as
    -> f (Prod g as)
lensProd' s0 f = go s0
  where
    go  :: Index bs x
        -> Prod g bs
        -> f (Prod g bs)
    go = \case
      IZ -> \case
        x :< xs -> (:< xs) <$> f x
      IS i -> \case
        x :< xs -> (x :<) <$> go i xs

-- | Convert a 'Prod' of 'Sing' elements into a 'Sing' of the list of
-- elements.
prodSing
    :: Prod Sing as
    -> Sing as
prodSing = \case
    Ø       -> SNil
    x :< xs -> x `SCons` prodSing xs

-- | Convert a 'Sing' of a list of elements into a 'Prod' of 'Sing'
-- elements.
singProd
    :: Sing as
    -> Prod Sing as
singProd = \case
    SNil         -> Ø
    x `SCons` xs -> x :< singProd xs

-- | A RankN traversal over items in a 'Prod'.
traverseProd
    :: forall f g h as. Applicative h
    => (forall x. f x -> h (g x))
    -> Prod f as
    -> h (Prod g as)
traverseProd f = go
  where
    go  :: Prod f bs -> h (Prod g bs)
    go = \case
      Ø -> pure Ø
      x :< xs -> (:<) <$> f x <*> go xs

-- | A RankN map over items in a 'Prod'.
mapProd
    :: forall f g as. ()
    => (forall x. f x -> g x)
    -> Prod f as
    -> Prod g as
mapProd f = runIdentity . traverseProd (Identity . f)

-- | RankN fold over items in a 'Prod'.
foldMapProd
    :: forall f as m. Monoid m
    => (forall x. f x -> m)
    -> Prod f as
    -> m
foldMapProd f = getConst . traverseProd (Const . f)

-- | Zip together two 'Prod'.
zipProd
    :: Prod f as
    -> Prod g as
    -> Prod (f :*: g) as
zipProd = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> (x :*: y) :< zipProd xs ys

-- | Convert a 'WitAll' into a 'Prod'.  This requires providing a singleton
-- witnessing the structure of the list.
allProd :: Sing as -> WitAll [] (TyCon1 f) as -> Prod f as
allProd = \case
    SNil         -> \_ -> Ø
    _ `SCons` xs -> \a -> runWitAll a IZ :< allProd xs (WitAll (runWitAll a . IS))

-- | Convert a 'Prod' into a 'WitAll'.
prodAll :: Prod f as -> WitAll [] (TyCon1 f) as
prodAll = \case
    Ø       -> WitAll $ \case
    x :< xs -> WitAll $ \case
      IZ   -> x
      IS i -> runWitAll (prodAll xs) i
