{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.List.Prod (
    Prod(..), pNil
  , indexProd
  , lensProd'
  ) where

import           Control.Applicative
import           Data.Kind
import           Data.Type.Universe

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
