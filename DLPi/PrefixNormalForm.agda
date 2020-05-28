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
open import Data.Nat
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Codata.Thunk

open import Common
open import Language
open import Congruence
open import PrefixedBy
open import Split
open import Scale
open import Weaken

data PrefixNormalForm : ∀{Γ} -> ℕ -> Multiplicity -> Multiplicity -> Process Γ -> Set where
  pnf-send :
    ∀{k Γ Γ1 Γ2 t v}
     {x : Name k Γ1 (Chan #0 #1 t) _}
     {V : Term Γ2 (t .force) v}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixNormalForm k #0 #1 (Send sp (name x) V)
  pnf-recv :
    ∀{k Γ Γ1 Γ2 t}
     {x : Name k Γ1 (Chan #1 #0 t) _}
     {g : (v : ⟦ t .force ⟧) -> Process (t .force # v :: Γ2)}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixNormalForm k #1 #0 (Recv sp (name x) g)
  pnf-par :
    ∀{Γ Γ1 Γ2 k m n}{P : Process Γ1}{Q : Process Γ2}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixNormalForm k m n P
    -> PrefixNormalForm k m n (Par sp P Q)
  pnf-new :
    ∀{Γ m n m' n' t k}
     {P : Process (Chan m' n' t # _ :: Γ)}
    -> PrefixNormalForm (suc k) m n P
    -> PrefixNormalForm k m n (New P)

prefix-normal-form :
  ∀{Γ k m n}
  -> (P : Process Γ)
  -> PrefixedBy k m n P
  -> ∃ λ Q -> P <= Q × PrefixNormalForm k m n Q
prefix-normal-form (Send _ (name _) _) (prefixed-send sp) =
  _ , cong-refl , pnf-send sp
prefix-normal-form (Recv _ (name _) _) (prefixed-recv sp) =
  _ , cong-refl , pnf-recv sp
prefix-normal-form (Par _ P _) (prefixed-par-l sp pb) =
  let _ , pc , pnf = prefix-normal-form P pb in
  _ , cong-par-cong sp pc , pnf-par sp pnf
prefix-normal-form (Par _ _ Q) (prefixed-par-r sp pb) =
  let _ , pc , pnf = prefix-normal-form Q pb in
  let sp' = csplit-comm sp in
  _ , cong-trans (cong-par-comm sp) (cong-par-cong sp' pc) , pnf-par sp' pnf
prefix-normal-form (New P) (prefixed-new pb) =
  let _ , pc , pnf = prefix-normal-form P pb in
  _ , cong-new-cong pc , pnf-new pnf
prefix-normal-form (Rep sc P) (prefixed-rep pb) =
  let _ , pc , pnf = prefix-normal-form P pb in
  let sp = c-scale-split sc in
  _ , cong-trans (cong-rep-par sc) (cong-par-cong sp pc) , pnf-par sp pnf

weaken-pnf :
  ∀{Γ Δ k l m n}
  -> (P : Process Γ)
  -> (we : Weaken l Γ Δ)
  -> PrefixNormalForm k m n P
  -> PrefixNormalForm (weaken-name-index l k) m n (weaken-process we P)
weaken-pnf (Send sp (name x) E) we (pnf-send _) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  pnf-send sp'
weaken-pnf (Recv sp (name x) P) we (pnf-recv _) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  pnf-recv sp'
weaken-pnf (Par sp P _) we (pnf-par _ pnf) =
  let _ , _ , sp' , we' , _ = weaken-split we sp in
  pnf-par sp' (weaken-pnf P we' pnf)
weaken-pnf (New P) we (pnf-new pnf) = pnf-new (weaken-pnf P (next we) pnf)
