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
open import Data.Bool
open import Data.Unit

open import SessionTypes.LinearLogic.Types
open import SessionTypes.LinearLogic.Encoding

module SessionTypes.LinearLogic.Decode where

⌈_,_⌉ : ∀{t} → Encoding t → Bool → SessionType
⌈ unit , _ ⌉ = End
⌈ input unit x , false ⌉ = ⌈ unit , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input unit x , true ⌉ = ⌈ unit , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (input E x₁) x , false ⌉ = ⌈ input E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input (input E x₁) x , true ⌉ = ⌈ input E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (output E x₁) x , false ⌉ = ⌈ output E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input (output E x₁) x , true ⌉ = ⌈ output E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (pure t) x , false ⌉ = All t # λ x₁ → ⌈ x x₁ , false ⌉
⌈ input (pure t) x , true ⌉ = Ex t # λ x₁ → ⌈ x x₁ , true ⌉
⌈ output unit x , false ⌉ = ⌈ unit , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output unit x , true ⌉ = ⌈ unit , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (input E x₁) x , false ⌉ = ⌈ input E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output (input E x₁) x , true ⌉ = ⌈ input E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (output E x₁) x , false ⌉ = ⌈ output E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output (output E x₁) x , true ⌉ = ⌈ output E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (pure t) x , false ⌉ = Ex t # λ x₁ → ⌈ x x₁ , true ⌉
⌈ output (pure t) x , true ⌉ = All t # λ x₁ → ⌈ x x₁ , false ⌉
⌈ pure τ , _ ⌉ = $ τ
