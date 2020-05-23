{- This file is part of DLπ.                                         -}
{-                                                                   -}
{- DLπ is free software: you can redistribute it and/or modify it    -}
{- under the terms of the GNU General Public License as published by -}
{- the Free Software Foundation, either version 3 of the License, or -}
{- (at your option) any later version.                               -}
{-                                                                   -}
{- DLπ is distributed in the hope that it will be useful, but        -}
{- WITHOUT ANY WARRANTY; without even the implied warranty of        -}
{- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU -}
{- General Public License for more details.                          -}
{-                                                                   -}
{- You should have received a copy of the GNU General Public License -}
{- along with DLπ.  If not, see <https://www.gnu.org/licenses/>.     -}
{-                                                                   -}
{- Copyright 2020 Luca Ciccone, Luca Padovani                        -}

open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≢_; refl)
open import Relation.Nullary using (¬_)
open import Codata.Thunk

open import Common
open import Multiplicity
open import Type
open import Context
open import Language
open import Weakening
open import Scaling

has-type-split :
  ∀{Γ Γ1 Γ2 k t v}
  -> Lookup k Γ t v
  -> CSplit Γ Γ1 Γ2
  -> ∃[ t1 ] ∃[ t2 ] ∃[ v1 ] ∃[ v2 ] (TSplit t t1 t2 v v1 v2 × Lookup k Γ1 t1 v1 × Lookup k Γ2 t2 v2)
has-type-split ht-here (ts :: _) =
  _ , _ , _ , _ , ts , ht-here , ht-here
has-type-split (ht-next ht) (_ :: sp) =
  let _ , _ , _ , _ , ts , ht1 , ht2 = has-type-split ht sp in
  _ , _ , _ , _ , ts , ht-next ht1 , ht-next ht2

has-type-null : ∀{Γ k t v} -> Lookup k Γ t v -> CNull Γ -> TNull t
has-type-null ht-here (tnull :: _) = tnull
has-type-null (ht-next ht) (_ :: null) = has-type-null ht null

has-type-scale :
  ∀{Γ Δ k t v} ->
  Lookup k Δ t v ->
  CScale Γ Δ ->
  ∃[ s ] ∃[ w ] (TScale s t w v × Lookup k Γ s w)
has-type-scale ht-here (tsc :: sc) = _ , _ , tsc , ht-here
has-type-scale (ht-next ht) (tsc :: sc) =
  let _ , _ , ssc , ht' = has-type-scale ht sc in
  _ , _ , ssc , ht-next ht'

not-in-name-null :
  ∀{k l Γ t s v w}
  -> Name k Γ s w
  -> l ≢ k
  -> Lookup l Γ t v
  -> TNull t
not-in-name-null (here _) nx ht-here = ⊥-elim (nx refl)
not-in-name-null (here cz) _ (ht-next ht) = has-type-null ht cz
not-in-name-null (next tnull _) _ ht-here = tnull
not-in-name-null (next _ x) nx (ht-next ht) = not-in-name-null x (suc-≢ nx) ht

not-in-term-null :
  ∀{k Γ t s v w}
  -> {V : Term Γ s w}
  -> NotInTerm k V
  -> Lookup k Γ t v
  -> TNull t
not-in-term-null (nin-v {x = x} nx) ht = not-in-name-null x nx ht
not-in-term-null (nin-n cnull _) ht = has-type-null ht cnull
not-in-term-null (nin-p sp nie1 nie2) ht =
  let _ , _ , _ , _ , ts , ht1 , ht2 = has-type-split ht sp in
  t-null-null-split-null (not-in-term-null nie1 ht1) (not-in-term-null nie2 ht2) ts

witness : (t : Type) -> ⟦ t ⟧
witness (Pure A) = x
  where postulate x : A -- We assume that all pure types are inhabited
witness (Chan _ _ _) = tt
witness (Pair t f) = let v = witness t in v , witness (f v)

not-in-process-null :
  ∀{k Γ t v}
  -> {P : Process Γ}
  -> NotInProcess k P
  -> Lookup k Γ t v
  -> TNull t
not-in-process-null {P = Idle cnull} _ ht = has-type-null ht cnull
not-in-process-null (nin-send sp ne1 ne2) ht =
  let _ , _ , _ , _ , ts , ht1 , ht2 = has-type-split ht sp in
  t-null-null-split-null (not-in-term-null ne1 ht1) (not-in-term-null ne2 ht2) ts
not-in-process-null (nin-recv {t = t} sp niE nig) ht =
  let _ , _ , _ , _ , ts , htE , htP = has-type-split ht sp in
  t-null-null-split-null (not-in-term-null niE htE)
                         (not-in-process-null (nig (witness (t .force))) (ht-next htP)) ts
  -- Applying f to a single witness suffices because the type
  -- which we want to prove unrestricted is always the same and
  -- does not depend on the witness
not-in-process-null (nin-par sp niP niQ) ht =
  let _ , _ , _ , _ , ts , htP , htQ = has-type-split ht sp in
  t-null-null-split-null (not-in-process-null niP htP) (not-in-process-null niQ htQ) ts
not-in-process-null (nin-new niP) ht = not-in-process-null niP (ht-next ht)
not-in-process-null (nin-rep sc niP) ht =
  let _ , _ , tsc , ht' = has-type-scale ht sc in
  t-null-scale-null-l (not-in-process-null niP ht') tsc
not-in-process-null (nin-let {t = t} {f = f} sp niE niP) ht =
  let _ , _ , _ , _ , ts , ht1 , ht2 = has-type-split ht sp in
  t-null-null-split-null (not-in-term-null niE ht1)
                   (not-in-process-null niP (ht-next (ht-next ht2))) ts
