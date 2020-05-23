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
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂; sym)

open import Multiplicity
open import Type
open import Context
open import Syntax

data Swap : ℕ -> Context -> Context -> Set where
  here : ∀{Γ t s v w} -> Swap zero (t # v :: (s # w :: Γ)) (s # w :: (t # v :: Γ))
  next : ∀{n Γ Δ t v} -> Swap n Γ Δ -> Swap (suc n) (t # v :: Γ) (t # v :: Δ)

swap-inv : ∀{n Γ Δ} -> Swap n Γ Δ -> Swap n Δ Γ
swap-inv here = here
swap-inv (next sw) = next (swap-inv sw)

swap-null : ∀{n Γ Δ} -> Swap n Γ Δ -> CNull Γ -> CNull Δ
swap-null here (tz :: sz :: cz) = sz :: tz :: cz
swap-null (next sw) (tz :: cz) = tz :: swap-null sw cz

swap-name-index : ℕ -> ℕ -> ℕ
swap-name-index zero zero = suc zero
swap-name-index zero (suc zero) = zero
swap-name-index zero (suc (suc k)) = suc (suc k)
swap-name-index (suc n) zero = zero
swap-name-index (suc n) (suc k) = suc (swap-name-index n k)

swap-name : ∀{k n Γ Δ t v} -> Swap n Γ Δ -> Name k Γ t v -> Name (swap-name-index n k) Δ t v
swap-name here (here (sz :: cz)) = next sz (here cz)
swap-name here (next tz (here cz)) = here (tz :: cz)
swap-name here (next tz (next sz x)) = next sz (next tz x)
swap-name (next sw) (here cz) = here (swap-null sw cz)
swap-name (next sw) (next tu x) = next tu (swap-name sw x)

swap-split :
  ∀{n Γ Γ1 Γ2 Δ}
  -> Swap n Γ Δ
  -> CSplit Γ Γ1 Γ2
  -> ∃[ Δ1 ] ∃[ Δ2 ] (CSplit Δ Δ1 Δ2 × Swap n Γ1 Δ1 × Swap n Γ2 Δ2)
swap-split here (ts :: ss :: sp) =
  _ , _ , ss :: ts :: sp , here , here
swap-split (next sw) (ts :: sp) =
  let _ , _ , sp , sw1 , sw2 = swap-split sw sp in
  _ , _ , ts :: sp , next sw1 , next sw2

swap-term : ∀{n Γ Δ t v} -> Swap n Γ Δ -> Term Γ t v -> Term Δ t v
swap-term sw (name x) = name (swap-name sw x)
swap-term sw (pure cnull c) = pure (swap-null sw cnull) c
swap-term sw (pair sp E1 E2) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  pair sp' (swap-term sw1 E1) (swap-term sw2 E2)

swap-scale : ∀{n Γ Γ' Δ'} -> Swap n Γ' Δ' -> CScale Γ Γ' -> ∃[ Δ ] (Swap n Γ Δ × CScale Δ Δ')
swap-scale here (tsc :: ssc :: sc) =
  _ , here , ssc :: tsc :: sc
swap-scale (next sw) (tsc :: sc) =
  let _ , sw , sc = swap-scale sw sc in
  _ , next sw , tsc :: sc

swap-process : ∀{n Γ Δ} -> Swap n Γ Δ -> Process Γ -> Process Δ
swap-process sw (Idle cz) = Idle (swap-null sw cz)
swap-process sw (Send sp ec em) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  Send sp' (swap-term sw1 ec) (swap-term sw2 em)
swap-process sw (Recv sp e g) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  Recv sp' (swap-term sw1 e) (λ v -> swap-process (next sw2) (g v))
swap-process sw (Par sp p q) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  Par sp' (swap-process sw1 p) (swap-process sw2 q)
swap-process sw (New p) = New (swap-process (next sw) p)
swap-process sw (Rep sc P) =
  let _ , sw' , sc' = swap-scale sw sc in
  Rep sc' (swap-process sw' P)
swap-process sw (Let sp E P) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  Let sp' (swap-term sw1 E) (swap-process (next (next sw2)) P)
