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
open import Data.List
open import Data.Bool
open import Data.Product

open import SessionTypes.Common
open import SessionTypes.LinearLogic.Types
open import SessionTypes.LinearLogic.Encoding

module SessionTypes.LinearLogic.Encode where

mutual
  ⌊_,_⌋ : SessionType → Bool → Type
  ⌊ End , _ ⌋ = Chan #0 #0 (Pure ⊤)
  ⌊ $ x , _ ⌋ = Pure x
  ⌊ A ⊸ B , false ⌋ = Chan #1 #0 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , false ⌋)
  ⌊ A ⊸ B , true ⌋ =  Chan #0 #1 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , false ⌋)
  ⌊ A ⊗ B , false ⌋ = Chan #0 #1 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , true ⌋)
  ⌊ A ⊗ B , true ⌋ = Chan #1 #0 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , true ⌋)
  ⌊ A & B , false ⌋ = Chan #1 #0 (Pair (Pure Bool) λ x → if x then ⌊ A , false ⌋ else ⌊ B , false ⌋)
  ⌊ A & B , true ⌋ = Chan #0 #1 (Pair (Pure Bool) λ x → if x then ⌊ A , false ⌋ else ⌊ B , false ⌋)
  ⌊ A ⊕ B , false ⌋ = Chan #0 #1 (Pair (Pure Bool) λ x → if x then ⌊ A , true ⌋ else ⌊ B , true ⌋)
  ⌊ A ⊕ B , true ⌋ = Chan #1 #0 (Pair (Pure Bool) λ x → if x then ⌊ A , true ⌋ else ⌊ B , true ⌋)
  ⌊ Ex τ # f , false ⌋ = Chan #0 #1 (Pair (Pure τ) λ x → ⌊ f x , true ⌋)
  ⌊ Ex τ # f , true ⌋ = Chan #1 #0 (Pair (Pure τ) λ x → ⌊ f x , true ⌋)
  ⌊ All τ # f , false ⌋ = Chan #1 #0 (Pair (Pure τ) λ x → ⌊ f x , false ⌋)
  ⌊ All τ # f , true ⌋ = Chan #0 #1 (Pair (Pure τ) λ x → ⌊ f x , false ⌋)

enc-Enc : ∀ A b → Encoding ⌊ A , b ⌋
enc-Enc End _ = unit
enc-Enc ($ x) _ = pure x
enc-Enc (A ⊸ B) false = input (enc-Enc A false) λ _ → enc-Enc B false
enc-Enc (A ⊸ B) true = output (enc-Enc A false) λ _ → enc-Enc B false
enc-Enc (A ⊗ B) false = output (enc-Enc A false) λ _ → enc-Enc B true
enc-Enc (A ⊗ B) true = input (enc-Enc A false) λ _ → enc-Enc B true
enc-Enc (A & B) false = input (pure Bool) λ { true → enc-Enc A false ; false → enc-Enc B false }
enc-Enc (A & B) true = output (pure Bool) λ { true → enc-Enc A false ; false → enc-Enc B false } 
enc-Enc (A ⊕ B) false = output (pure Bool) λ { true → enc-Enc A true ; false → enc-Enc B true}
enc-Enc (A ⊕ B) true = input (pure Bool) λ { true → enc-Enc A true ; false → enc-Enc B true}
enc-Enc (Ex τ # x) false = output (pure τ) λ x₁ → enc-Enc (x x₁) true
enc-Enc (Ex τ # x) true = input (pure τ) λ x₁ → enc-Enc (x x₁) true
enc-Enc (All τ # x) false = input (pure τ) λ x₁ → enc-Enc (x x₁) false
enc-Enc (All τ # x) true = output (pure τ) λ x₁ → enc-Enc (x x₁) false
