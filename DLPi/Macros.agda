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

open import Data.Unit
open import Data.Bool
open import Data.Product

open import Language
open import Weakening

SplitIn :
  ∀{Γ Γ1 Γ2 t s} ->
  CSplit Γ Γ1 Γ2 ->
  Expression Γ1 (Pair t (λ _ -> s)) ->
  Process (t :: s :: Γ2) ->
  Process Γ
SplitIn sp E P = Let sp E (λ _ -> P)

IfThenElse :
  ∀{Γ Γ1 Γ2 v} ->
  CSplit Γ Γ1 Γ2 ->
  Value Γ1 (Pure Bool) v ->
  Process Γ2 ->
  Process Γ2 ->
  Process Γ
IfThenElse sp B P Q =
  let _ , null , sp' = csplit-l _ in
  Let sp (val (pair sp' B (pure null tt))) aux
  where
    aux : Bool -> Process _
    aux true = weaken-process (weaken-here null-p) (weaken-process (weaken-here null-p) P)
    aux false = weaken-process (weaken-here null-p) (weaken-process (weaken-here null-p) Q)

Drop : ∀{t Γ} -> TNull t -> Process Γ -> Process (t :: Γ)
Drop null = weaken-process (weaken-here null)

