{-# LANGUAGE EmptyCase      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Type.List.Edit (
  -- * Simple edits
    Insert(..)
  , Delete(..)
  , insToDel
  , delToIns
  , Substitute(..)
  , flipSub
  -- * Compound edits
  , Edit(..)
  , flipEdit
  -- * Product
  , insertProd, deleteProd, deleteGetProd
  -- * Index
  , shiftIndex, Unshifted(..), unshiftIndex, unshiftIndex_
  ) where

import           Data.Kind
import           Data.Type.List.Prod
import           Data.Type.Universe
import qualified Control.Category       as C

-- | An @'Insert' as bs x@ is a witness that you can insert @x@ into some
-- position in list @as@ to produce list @bs@.
--
-- Some examples:
--
-- @
-- InsZ                   :: Insert '[1,2,3] '[4,1,2,3] 4
-- InsS InsZ              :: Insert '[1,2,3] '[1,4,2,3] 4
-- InsS (InsS InsZ)       :: Insert '[1,2,3] '[1,2,4,3] 4
-- InsS (InsS (InsS InsZ) :: Insert '[1,2,3] '[1,2,3,4] 4
-- @
data Insert :: [k] -> [k] -> k -> Type where
    InsZ :: Insert as (x ': as) x
    InsS :: Insert as bs x -> Insert (a ': as) (a ': bs) x

insToDel :: Insert as bs x -> Delete bs as x
insToDel = \case
    InsZ   -> DelZ
    InsS i -> DelS (insToDel i)

-- | A @'Delete' as bs x@ is a witness that you can delete item @x@ from
-- @as@ to produce the list @bs@.  It is essentially 'Insert' flipped.
--
-- Some examples:
--
-- @
-- DelZ             :: Delete '[1,2,3] '[2,3] 1
-- DelS DelZ        :: Delete '[1,2,3] '[2,3] 2
-- DelS (DelS DelZ) :: Delete '[1,2,3] '[1,2] 3
-- @
data Delete :: [k] -> [k] -> k -> Type where
    DelZ :: Delete (x ': as) as x
    DelS :: Delete as bs x -> Delete (a ': as) (a ': bs) x

-- | Flip a deletion
delToIns :: Delete as bs x -> Insert bs as x
delToIns = \case
    DelZ   -> InsZ
    DelS d -> InsS (delToIns d)

-- | A @'Substitute' as bs x y@ is a witness that you can replace item @x@ in
-- @as@ with item @y@ to produce @bs@.
--
-- Some examples:
--
-- @
-- SubZ             :: Subsitute '[1,2,3] '[4,2,3] 1 4
-- SubS SubZ        :: Subsitute '[1,2,3] '[1,4,3] 2 4
-- SubS (SubS SubZ) :: Substitute '[1,2,3] '[1,2,4] 3 4
-- @
--
data Substitute :: [k] -> [k] -> k -> k -> Type where
    SubZ :: Substitute (x ': as) (y ': as) x y
    SubS :: Substitute as bs x y -> Substitute (c ': as) (c ': bs) x y

-- | Flip a substitution
flipSub :: Substitute as bs x y -> Substitute bs as y x
flipSub = \case
    SubZ   -> SubZ
    SubS s -> SubS (flipSub s)

-- | An @'Edit' as bs@ is an edit script transforming @as@ into @bs@
-- through successive insertions, deletions, and substitutions.
data Edit :: [k] -> [k] -> Type where
    ENil :: Edit as as
    EIns :: Insert bs cs x -> Edit as bs -> Edit as cs
    EDel :: Delete bs cs x -> Edit as bs -> Edit as cs
    ESub :: Substitute bs cs x y -> Edit as bs -> Edit as cs

-- | Compose two 'Edit's
compEdit :: Edit as bs -> Edit bs cs -> Edit as cs
compEdit xs = \case
    ENil -> xs
    EIns i ys -> EIns i (compEdit xs ys)
    EDel d ys -> EDel d (compEdit xs ys)
    ESub s ys -> ESub s (compEdit xs ys)

-- | 'Edit' composition
instance C.Category Edit where
    id = ENil
    xs . ys = compEdit ys xs

-- | Reverse an 'Edit' script.  O(n^2).
flipEdit :: Edit as bs -> Edit bs as
flipEdit = \case
    ENil      -> ENil
    EIns i ys -> EDel (insToDel i) ENil `compEdit` flipEdit ys
    EDel d ys -> EIns (delToIns d) ENil `compEdit` flipEdit ys
    ESub s ys -> ESub (flipSub  s) ENil `compEdit` flipEdit ys

-- | Insert a value into a 'Prod', at a position indicated by the 'Insert'.
insertProd :: Insert as bs x -> f x -> Prod f as -> Prod f bs
insertProd = \case
    InsZ   -> (:<)
    InsS i -> \x -> \case
      y :< ys -> y :< insertProd i x ys

-- | Retrieve and delete a value in a 'Prod', at a position indicated by the 'Delete'.
deleteGetProd :: Delete as bs x -> Prod f as -> (f x, Prod f bs)
deleteGetProd = \case
    DelZ -> \case
      x :< xs -> (x, xs)
    DelS d -> \case
      x :< xs -> let (y, ys) = deleteGetProd d xs
                 in  (y, x :< ys)

-- | Delete a value in a 'Prod', at a position indicated by the 'Delete'.
deleteProd :: Delete as bs x -> Prod f as -> Prod f bs
deleteProd = \case
    DelZ -> \case
      _ :< xs -> xs
    DelS d -> \case
      x :< xs -> x :< deleteProd d xs

-- | If you add an item to @as@ to create @bs@, you also need to shift an
-- @'Index' as y@ to @Index bs y@.  This shifts the 'Index' in @as@ to
-- become an 'Index' in @bs@, but makes sure that the index points to the
-- same original value.
shiftIndex :: Insert as bs x -> Index as y -> Index bs y
shiftIndex = \case
    InsZ   -> IS
    InsS ins -> \case
      IZ   -> IZ
      IS i -> IS (shiftIndex ins i)

data Unshifted :: [k] -> [k] -> k -> k -> Type where
    GotDeleted :: Unshifted as bs x x
    NotDeleted :: Index bs y -> Unshifted as bs x y

-- | If you delete an item in @as@ to create @bs@, you also need to move
-- @'Index' as y@ into @Index bs y@.  This transforms the 'Index' in @as@
-- to become an 'Index' in @bs@, making sure the index points to the same
-- original value.
--
-- However, there is a possibility that the deleted item is the item that
-- the index was originally pointing to.  If this is the case, this
-- function returns 'GotDeleted', a witness that @x ~ y@.  Otherwise, it
-- returns 'NotDeleted' with the unshifted index.
unshiftIndex :: Delete as bs x -> Index as y -> Unshifted as bs x y
unshiftIndex = \case
    DelZ -> \case
      IZ   -> GotDeleted
      IS i -> NotDeleted i
    DelS del -> \case
      IZ   -> NotDeleted IZ
      IS i -> case unshiftIndex del i of
        GotDeleted   -> GotDeleted
        NotDeleted j -> NotDeleted (IS j)

-- | A version of 'unshiftIndex' returning a simple 'Maybe'.  This can be
-- used if you don't care about witnessing that @x ~ y@ in the case that
-- the index is the item that is deleted.
unshiftIndex_ :: Delete as bs x -> Index as y -> Maybe (Index bs y)
unshiftIndex_ del i = case unshiftIndex del i of
    GotDeleted   -> Nothing
    NotDeleted j -> Just j
