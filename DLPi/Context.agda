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

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym)

open import Type

infixr 5 _::_

data Context : Set₁ where
  []   : Context
  _#_::_ : (t : Type) → ⟦ t ⟧ -> Context → Context

data CNull : Context -> Set₁ where
  []   : CNull []
  _::_ : ∀{t v Γ} -> TNull t -> CNull Γ -> CNull (t # v :: Γ)

data CSplit : Context → Context → Context → Set₁ where
  []   : CSplit [] [] []
  _::_ : ∀{t t1 t2 Γ Γ1 Γ2 v v1 v2} → TSplit t t1 t2 v v1 v2 → CSplit Γ Γ1 Γ2 → CSplit (t # v :: Γ) (t1 # v1 :: Γ1) (t2 # v2 :: Γ2)

_≍_ : Context -> Context -> Set₁
_≍_ Γ1 Γ2 = ∃[ Γ ] CSplit Γ Γ1 Γ2

join : ∀{Γ Δ} -> Γ ≍ Δ -> Context
join (Γ , _) = Γ

data CScale : Context -> Context -> Set₁ where
  []   : CScale [] []
  _::_ : ∀{Γ Δ t s v w} -> TScale t s v w -> CScale Γ Δ -> CScale (t # v :: Γ) (s # w :: Δ)

data Lookup : ℕ -> Context -> (t : Type) -> ⟦ t ⟧ -> Set₁ where
  ht-here : ∀{Γ t v} -> Lookup zero (t # v :: Γ) t v
  ht-next : ∀{Γ t s v w k} -> Lookup k Γ t v -> Lookup (suc k) (s # w :: Γ) t v

c-null-null-split-null : ∀{Γ Γ1 Γ2} -> CNull Γ1 -> CNull Γ2 -> CSplit Γ Γ1 Γ2 -> CNull Γ
c-null-null-split-null [] [] [] = []
c-null-null-split-null (tz1 :: cnull1) (tz2 :: cnull2) (ts :: sp) =
  t-null-null-split-null tz1 tz2 ts :: c-null-null-split-null cnull1 cnull2 sp

csplit-comm : ∀{Γ Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> CSplit Γ Γ2 Γ1
csplit-comm [] = []
csplit-comm (ts :: sp) = tsplit-comm ts :: csplit-comm sp

csplit-comm-inv : ∀{Γ Γ1 Γ2} -> (sp : CSplit Γ Γ1 Γ2) -> csplit-comm (csplit-comm sp) ≡ sp
csplit-comm-inv [] = refl
csplit-comm-inv (ts :: sp) = cong₂ _::_ (tsplit-comm-inv ts) (csplit-comm-inv sp)

csplit-assoc-rl :
  ∀{Γ Γ1 Γ23 Γ2 Γ3}
  -> CSplit Γ Γ1 Γ23
  -> CSplit Γ23 Γ2 Γ3
  -> ∃ λ Δ -> CSplit Γ Δ Γ3 × CSplit Δ Γ1 Γ2
csplit-assoc-rl [] [] = [] , [] , []
csplit-assoc-rl (ts1 :: sp1) (ts2 :: sp2) =
  let _ , _ , ts1 , ts2 = tsplit-assoc-rl ts1 ts2 in
  let _ , sp1 , sp2 = csplit-assoc-rl sp1 sp2 in
  _ , ts1 :: sp1 , ts2 :: sp2

csplit-assoc-lr :
  ∀{Γ Γ12 Γ1 Γ2 Γ3}
  -> CSplit Γ Γ12 Γ3
  -> CSplit Γ12 Γ1 Γ2
  -> ∃ λ Δ -> CSplit Γ Γ1 Δ × CSplit Δ Γ2 Γ3
csplit-assoc-lr sp1 sp2 =
  let sp1 = csplit-comm sp1 in
  let sp2 = csplit-comm sp2 in
  let _ , sp1 , sp2 = csplit-assoc-rl sp1 sp2 in
  let sp1 = csplit-comm sp1 in
  let sp2 = csplit-comm sp2 in
  _ , sp1 , sp2

csplit-l : ∀(Γ : Context) -> ∃[ Δ ] (CNull Δ × CSplit Γ Γ Δ)
csplit-l [] = _ , [] , []
csplit-l (t # _ :: Γ) =
  let _ , _ , tnull , ts = tsplit-l t in
  let _ , cnull , sp = csplit-l Γ in
  _ , tnull :: cnull , ts :: sp

csplit-r : ∀(Γ : Context) -> ∃[ Δ ] (CNull Δ × CSplit Γ Δ Γ)
csplit-r Γ =
  let _ , cnull , sp = csplit-l Γ in
  _ , cnull , csplit-comm sp

c-null-split : ∀{Γ} -> CNull Γ -> CSplit Γ Γ Γ
c-null-split [] = []
c-null-split (tnull :: Γ) = t-null-split tnull :: c-null-split Γ

c-split-split-split :
  ∀{Δ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22}
  -> CSplit Δ Γ1 Γ2
  -> CSplit Γ1 Γ11 Γ12
  -> CSplit Γ2 Γ21 Γ22
  -> ∃ λ Δ1 -> ∃ λ Δ2
  -> CSplit Δ Δ1 Δ2 × CSplit Δ1 Γ11 Γ21 × CSplit Δ2 Γ12 Γ22
c-split-split-split sp sp1 sp2 =
  let _ , sp1 , sp = csplit-assoc-lr sp sp1 in
  let _ , sp2 , sp = csplit-assoc-rl sp sp2 in
  let sp = csplit-comm sp in
  let _ , sp , sp2 = csplit-assoc-lr sp2 sp in
  let _ , sp , sp1 = csplit-assoc-rl sp1 sp in
  _ , _ , sp , sp1 , sp2

c-split-scale : ∀{Γ Δ} -> CSplit Δ Γ Γ -> CSplit Δ Γ Δ
c-split-scale [] = []
c-split-scale (ts :: sp) = {!!} :: (c-split-scale sp)
