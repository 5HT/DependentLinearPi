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

open import Relation.Binary.PropositionalEquality
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat

open import Language
open import Weaken
open import Lookup
open import Congruence
open import Reduction

{- Structural Congruence preserves typing -}

Theorem42 : {Γ : Context} -> Process Γ -> Process Γ -> Set₁
Theorem42 P Q = P <= Q

{- Subject Reduction -}

Theorem43 : ∀{α Γ Δ} -> Process Γ -> (Γ == α => Δ) -> Process Δ -> Set₁
Theorem43 P c-red Q = P ~~ c-red ~> Q

{- Type Safety -}
-- Exchanged messages have the expected type
-- Γ11 contains the channel with capabilities #0 #1
-- In Γ12 the term being sent is well types
-- Γ21 contains the channel with capabilities #1 #0
-- In Γ22 the continuation of the receive is well typed
Proposition44 :
  ∀{k Γ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22 m1 n1 m2 n2 t s} ->
  CSplit Γ Γ1 Γ2 ->
  CSplit Γ1 Γ11 Γ12 ->
  CSplit Γ2 Γ21 Γ22 ->
  Name k Γ11 (Chan m1 n1 t) _ ->
  Name k Γ21 (Chan m2 n2 s) _ ->
  t ≡ s
Proposition44 = csplit-type-eq

{- Names that are not free are unrestricted -}

Proposition45 : ∀{k Γ t v} ->
                {P : Process Γ} ->
                NotInProcess k P ->
                Lookup k Γ t v ->
                TNull t
Proposition45 = not-in-process-null

{- Channels with #0 multiplicities are not used for communication -}

Proposition46 :
  ∀{Γ Γ' m t α k} ->
  Name k Γ (Chan m #0 t) _ ->
  Γ == α => Γ' ->
  α ≢ L# k
Proposition46 _          tau          = λ ()
Proposition46 _          (?-here _)   = λ ()
Proposition46 _          (!-here _)   = λ ()
Proposition46 (next _ _) (#-here _ _) = λ ()
Proposition46 _          (?-next _)   = λ ()
Proposition46 _          (!-next _)   = λ ()
Proposition46 (here _)   (#-next _)   = λ ()
Proposition46 (next x ch) (#-next red) = λ q → p (cong pred-l q)
  where
    p = Proposition46 ch red

    pred-l : Label -> Label
    pred-l Lτ = Lτ
    pred-l (L? zero) = L? zero
    pred-l (L? (suc x)) = L? x
    pred-l (L! zero) = L! zero
    pred-l (L! (suc x)) = L! x
    pred-l (L# zero) = L# zero
    pred-l (L# (suc x)) = L# x
