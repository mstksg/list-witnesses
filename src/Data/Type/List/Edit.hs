{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Type.List.Edit
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Witnesses regarding single-item edits of lists.
module Data.Type.List.Edit (
  -- * Simple edits
    Insert(..)
  , Delete(..)
  , insToDel
  , delToIns
  , Substitute(..)
  , flipSub
  , subToDelIns
  -- * Compound edits
  , Edit(..)
  , compEdit
  , flipEdit
  -- * Rec
  , insertRec, deleteRec, deleteGetRec
  , recLens, substituteRec
  -- * Index
  -- ** Manipulating indices
  , insertIndex
  , DeletedIx(..), deleteIndex, deleteIndex_
  , SubstitutedIx(..), substituteIndex, substituteIndex_
  -- ** Converting from indices
  , withDelete, withInsert, withInsertAfter
  ) where

import           Data.Functor.Identity
import           Data.Kind
import           Data.Type.Universe
import           Data.Vinyl.Core
import qualified Control.Category      as C

-- | An @'Insert' as bs x@ is a witness that you can insert @x@ into some
-- position in list @as@ to produce list @bs@.  It is essentially 'Delete'
-- flipped.
--
-- Some examples:
--
-- @
-- InsZ                   :: Insert '[1,2,3] '[4,1,2,3] 4
-- InsS InsZ              :: Insert '[1,2,3] '[1,4,2,3] 4
-- InsS (InsS InsZ)       :: Insert '[1,2,3] '[1,2,4,3] 4
-- InsS (InsS (InsS InsZ) :: Insert '[1,2,3] '[1,2,3,4] 4
-- @
--
-- @bs@ will always be exactly one item longer than @as@.
data Insert :: [k] -> [k] -> k -> Type where
    InsZ :: Insert as (x ': as) x
    InsS :: Insert as bs x -> Insert (a ': as) (a ': bs) x

deriving instance Show (Insert as bs x)

-- | Flip an insertion.
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
--
-- @bs@ will always be exactly one item shorter than @as@.
data Delete :: [k] -> [k] -> k -> Type where
    DelZ :: Delete (x ': as) as x
    DelS :: Delete as bs x -> Delete (a ': as) (a ': bs) x

deriving instance Show (Delete as bs x)

-- | Flip a deletion.
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
-- SubZ             :: Substitute '[1,2,3] '[4,2,3] 1 4
-- SubS SubZ        :: Substitute '[1,2,3] '[1,4,3] 2 4
-- SubS (SubS SubZ) :: Substitute '[1,2,3] '[1,2,4] 3 4
-- @
--
data Substitute :: [k] -> [k] -> k -> k -> Type where
    SubZ :: Substitute (x ': as) (y ': as) x y
    SubS :: Substitute as bs x y -> Substitute (c ': as) (c ': bs) x y

deriving instance Show (Substitute as bs x y)

-- | Flip a substitution
flipSub :: Substitute as bs x y -> Substitute bs as y x
flipSub = \case
    SubZ   -> SubZ
    SubS s -> SubS (flipSub s)

-- | Decompose a 'Substitute' into a 'Delete' followed by an 'Insert'.
subToDelIns
    :: Substitute as bs x y
    -> (forall cs. Delete as cs x -> Insert cs bs y -> r)
    -> r
subToDelIns = \case
    SubZ   -> \f -> f DelZ InsZ
    SubS s -> \f -> subToDelIns s $ \d i -> f (DelS d) (InsS i)

-- | An @'Edit' as bs@ is a reversible edit script transforming @as@ into
-- @bs@ through successive insertions, deletions, and substitutions.
data Edit :: [k] -> [k] -> Type where
    ENil :: Edit as as
    EIns :: Insert bs cs x -> Edit as bs -> Edit as cs
    EDel :: Delete bs cs x -> Edit as bs -> Edit as cs
    ESub :: Substitute bs cs x y -> Edit as bs -> Edit as cs

deriving instance Show (Edit as bs)

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

-- | Reverse an 'Edit' script.  O(n^2).  Please do not use.
--
-- TODO: Make O(n) using diff lists.
flipEdit :: Edit as bs -> Edit bs as
flipEdit = \case
    ENil      -> ENil
    EIns i ys -> EDel (insToDel i) ENil `compEdit` flipEdit ys
    EDel d ys -> EIns (delToIns d) ENil `compEdit` flipEdit ys
    ESub s ys -> ESub (flipSub  s) ENil `compEdit` flipEdit ys

-- | Insert a value into a 'Rec', at a position indicated by the 'Insert'.
insertRec :: Insert as bs x -> f x -> Rec f as -> Rec f bs
insertRec = \case
    InsZ   -> (:&)
    InsS i -> \x -> \case
      y :& ys -> y :& insertRec i x ys

-- | Retrieve and delete a value in a 'Rec', at a position indicated by the 'Delete'.
deleteGetRec :: Delete as bs x -> Rec f as -> (f x, Rec f bs)
deleteGetRec = \case
    DelZ -> \case
      x :& xs -> (x, xs)
    DelS d -> \case
      x :& xs -> let (y, ys) = deleteGetRec d xs
                 in  (y, x :& ys)

-- | Delete a value in a 'Rec', at a position indicated by the 'Delete'.
deleteRec :: Delete as bs x -> Rec f as -> Rec f bs
deleteRec = \case
    DelZ -> \case
      _ :& xs -> xs
    DelS d -> \case
      x :& xs -> x :& deleteRec d xs

-- | A type-changing lens into a value in a 'Rec', given a 'Substitute'
-- indicating which value.
--
-- Read this type signature as:
--
-- @
-- 'recLens'
--     :: 'Substitute' as bs x y
--     -> Lens ('Rec' g as) (Rec g bs) (g x) (g y)
-- @
--
-- This is simular to 'rlensC' from /vinyl/, but is built explicitly and
-- inductively, instead of using typeclass magic.
recLens
    :: forall as bs x y g f. Functor f
    => Substitute as bs x y
    -> (g x -> f (g y))
    -> Rec g as
    -> f (Rec g bs)
recLens s0 f = go s0
  where
    go  :: Substitute cs ds x y
        -> Rec g cs
        -> f (Rec g ds)
    go = \case
      SubZ -> \case
        x :& xs -> (:& xs) <$> f x
      SubS s -> \case
        x :& xs -> (x :&) <$> go s xs

-- | Substitute a value in a 'Rec' at a given position, indicated by the
-- 'Substitute'.  This is essentially a specialized version of 'recLens'.
substituteRec
    :: Substitute as bs x y
    -> (f x -> f y)
    -> Rec f as
    -> Rec f bs
substituteRec s f = runIdentity . recLens s (Identity . f)

-- | If you add an item to @as@ to create @bs@, you also need to shift an
-- @'Index' as y@ to @Index bs y@.  This shifts the 'Index' in @as@ to
-- become an 'Index' in @bs@, but makes sure that the index points to the
-- same original value.
insertIndex :: Insert as bs x -> Index as y -> Index bs y
insertIndex = \case
    InsZ   -> IS
    InsS ins -> \case
      IZ   -> IZ
      IS i -> IS (insertIndex ins i)

-- | Used as the return type of 'deleteIndex'.  An @'DeletedIx' bs x y@ is
-- like a @'Maybe' ('Index' bs y)@, except the 'Nothing' case witnesses
-- that @x ~ y@.
data DeletedIx :: [k] -> k -> k -> Type where
    GotDeleted :: DeletedIx bs x x
    NotDeleted :: Index bs y -> DeletedIx bs x y

deriving instance Show (DeletedIx bs x y)

-- | If you delete an item in @as@ to create @bs@, you also need to move
-- @'Index' as y@ into @Index bs y@.  This transforms the 'Index' in @as@
-- to become an 'Index' in @bs@, making sure the index points to the same
-- original value.
--
-- However, there is a possibility that the deleted item is the item that
-- the index was originally pointing to.  If this is the case, this
-- function returns 'GotDeleted', a witness that @x ~ y@.  Otherwise, it
-- returns 'NotDeleted' with the unshifted index.
deleteIndex :: Delete as bs x -> Index as y -> DeletedIx bs x y
deleteIndex = \case
    DelZ -> \case
      IZ   -> GotDeleted
      IS i -> NotDeleted i
    DelS del -> \case
      IZ   -> NotDeleted IZ
      IS i -> case deleteIndex del i of
        GotDeleted   -> GotDeleted
        NotDeleted j -> NotDeleted (IS j)

-- | A version of 'deleteIndex' returning a simple 'Maybe'.  This can be
-- used if you don't care about witnessing that @x ~ y@ in the case that
-- the index is the item that is deleted.
deleteIndex_ :: Delete as bs x -> Index as y -> Maybe (Index bs y)
deleteIndex_ del i = case deleteIndex del i of
    GotDeleted   -> Nothing
    NotDeleted j -> Just j

-- | Used as the return type of 'substituteIndex'.  An @'SubstitutedIx' bs x y z@ is
-- like an @'Either' ('Index' bs y) ('Index' bs z)@, except the 'Left' case
-- witnesses that @x ~ z@.
data SubstitutedIx :: [k] -> k -> k -> k -> Type where
    GotSubbed :: Index bs y -> SubstitutedIx bs z y z
    NotSubbed :: Index bs z -> SubstitutedIx bs x y z

-- | If you substitute an item in @as@ to create @bs@, you also need to
-- reshift @'Index' as z@ into @'Index' bs z@.  This reshifts the 'Index'
-- in @as@ to become an 'Index' in @bs@, making sure the index points to
-- the same original value.
--
-- However, there is a possibility that the substituted item is the item
-- that the index was originally pointing to.  If this is the case, this
-- function returns 'GotSubbed', a witness that @x ~ z@.  Otherwise, it
-- returns 'NotSubbed'.  Both contain the updated index.
substituteIndex
    :: Substitute as bs x y
    -> Index as z
    -> SubstitutedIx bs x y z
substituteIndex = \case
    SubZ -> \case
      IZ   -> GotSubbed IZ
      IS i -> NotSubbed (IS i)
    SubS s -> \case
      IZ   -> NotSubbed IZ
      IS i -> case substituteIndex s i of
        GotSubbed j -> GotSubbed (IS j)
        NotSubbed j -> NotSubbed (IS j)

-- | A version of 'substituteIndex' returning a simple 'Either'.  This can be
-- the case if you don't care about witnessing @x ~ z@ in the case that the
-- index is the item that was substituted.
substituteIndex_
    :: Substitute as bs x y
    -> Index as z
    -> Either (Index bs y) (Index bs z)
substituteIndex_ sub i = case substituteIndex sub i of
    GotSubbed j -> Left  j
    NotSubbed j -> Right j

-- | Given an 'Index' pointing to an element, create a 'Delete'
-- corresponding to the given item.  The type of the resulting list is
-- existentially quantified, is guaranteed to be just exactly the original
-- list minus the specified element.
withDelete
    :: Index as x
    -> (forall bs. Delete as bs x -> r)
    -> r
withDelete = \case
    IZ   -> \f -> f DelZ
    IS i -> \f -> withDelete i (f . DelS)

-- | Given an 'Index' pointing to an element, create an 'Insert' placing an
-- item /directly before/ the given element.  The type is existentailly
-- quantified.
withInsert
    :: Index as x
    -> (forall bs. Insert as bs y -> r)
    -> r
withInsert = \case
    IZ   -> \f -> f InsZ
    IS i -> \f -> withInsert i (f . InsS)

-- | Given an 'Index' pointing to an element, create an 'Insert' placing an
-- item /directly after/ the given element.  The type is existentailly
-- quantified.
withInsertAfter
    :: Index as x
    -> (forall bs. Insert as bs y -> r)
    -> r
withInsertAfter = \case
    IZ   -> \f -> f (InsS InsZ)
    IS i -> \f -> withInsertAfter i (f . InsS)
