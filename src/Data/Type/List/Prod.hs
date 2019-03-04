{-# LANGUAGE EmptyCase      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Type.List.Prod (
    Prod(..), pNil
  , indexProd
  ) where

import           Data.Type.Universe
import           Data.Kind

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
data Prod :: (k -> Type) -> [k] -> Type where
    Ø    :: Prod f '[]
    (:<) :: f a -> Prod f as -> Prod f (a ': as)

infixr 5 :<

-- | Alias for 'Ø'
pNil :: Prod f '[]
pNil = Ø

-- | Retrieve an element in a 'Prod' at a given index.
indexProd :: Index as x -> Prod f as -> f x
indexProd = \case
    IZ -> \case
      x :< _ -> x
    IS i -> \case
      _ :< xs -> indexProd i xs

