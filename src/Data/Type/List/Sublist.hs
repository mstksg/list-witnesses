{-# LANGUAGE EmptyCase          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Type.List.Sublist (
    Prefix(..)
  , Suffix(..)
  , takeProd
  , dropProd
  ) where

import           Data.Kind
import           Data.Type.List.Prod

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
data Prefix :: [k] -> [k] -> Type where
    PreZ :: Prefix '[] as
    PreS :: Prefix  as bs -> Prefix  (a ': as) (a ': bs)

deriving instance Show (Prefix as bs)

-- | Take items from a 'Prod' corresponding to a given 'Prefix'.
takeProd :: Prefix as bs -> Prod f bs -> Prod f as
takeProd = \case
    PreZ   -> \_ -> Ø
    PreS p -> \case
      x :< xs -> x :< takeProd p xs

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
data Suffix :: [k] -> [k] -> Type where
    SufZ :: Suffix as as
    SufS :: Suffix as bs -> Suffix as (b ': bs)

deriving instance Show (Suffix as bs)

-- | Drop items from a 'Prod' corresponding to a given 'Suffix'.
dropProd :: Suffix as bs -> Prod f bs -> Prod f as
dropProd = \case
    SufZ   -> id
    SufS s -> \case
      _ :< xs -> dropProd s xs
