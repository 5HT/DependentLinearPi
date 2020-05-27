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

open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Codata.Thunk

open import Multiplicity
open import Type
open import Context

module Syntax where

data Name : ℕ -> Context -> (t : Type) -> ⟦ t ⟧ -> Set₁ where
  here : ∀{Γ t p} -> CNull Γ -> Name zero (t # p :: Γ) t p
  next : ∀{k Γ t s p q} -> TNull s -> Name k Γ t p ->
         Name (suc k) (s # q :: Γ) t p

data Term : Context -> (t : Type) -> ⟦ t ⟧ -> Set₁ where
  name : ∀{k Γ t p} -> Name k Γ t p -> Term Γ t p
  pure : ∀{Γ A} -> CNull Γ -> (p : A) -> Term Γ (Pure A) p
  pair : ∀{Γ Γ1 Γ2 t f p q} -> CSplit Γ Γ1 Γ2 -> Term Γ1 t p ->
         Term Γ2 (f p) q -> Term Γ (Pair t f) (p , q)

data Process : Context -> Set₁ where
  Idle : ∀{Γ} -> CNull Γ -> Process Γ
  Send : ∀{Γ Γ1 Γ2 t p} -> CSplit Γ Γ1 Γ2 -> Term Γ1 (Chan #0 #1 t) _ ->
         Term Γ2 (t .force) p -> Process Γ
  Recv : ∀{Γ Γ1 Γ2 t} -> CSplit Γ Γ1 Γ2 -> Term Γ1 (Chan #1 #0 t) _ ->
         ((x : ⟦ t .force ⟧) -> Process (t .force # x :: Γ2)) ->
         Process Γ
  Par  : ∀{Γ Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> Process Γ1 -> Process Γ2 ->
         Process Γ
  New  : ∀{Γ σ ρ t} -> Process (Chan σ ρ t # _ :: Γ) -> Process Γ
  Rep  : ∀{Γ Δ} -> CScale Γ Δ -> Process Γ -> Process Δ
  Let  : ∀{Γ Γ1 Γ2 t f p q} -> CSplit Γ Γ1 Γ2 ->
         Term Γ1 (Pair t f) (p , q) ->
         Process (t # p :: (f p # q :: Γ2)) -> Process Γ
