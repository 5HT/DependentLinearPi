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

open import Data.Bool

module SessionTypes.LinearLogic.Types where

BaseType : Set₁
BaseType = Set

data SessionType : Set₁ where
  End : SessionType
  $_ : BaseType → SessionType
  _⊸_ _⊗_ _&_ _⊕_ : SessionType → SessionType → SessionType
  All_#_ Ex_#_ : (τ : BaseType) → (τ → SessionType) → SessionType

data _≋_ : SessionType → SessionType → Set₁ where
  refl     : ∀ A → A ≋ A
  sym      : ∀{A B} → A ≋ B → B ≋ A
  in-in    : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⊸ B) ≋ (A' ⊸ B')
  out-out  : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⊗ B) ≋ (A' ⊗ B')
  all-all  : ∀{τ f f'} → ((x : τ) → (f x) ≋ (f' x)) → (All τ # f) ≋ (All τ # f')
  ex-ex    : ∀{τ f f'} → ((x : τ) → (f x) ≋ (f' x)) → (Ex τ # f) ≋ (Ex τ # f')
  plus-ex  : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⊕ B) ≋ (Ex Bool # λ {false → A' ; true → B'})
  with-all : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A & B) ≋ (All Bool # λ {false → A' ; true → B'})
  impl-all : ∀{τ A A'} → A ≋ A' → (($ τ) ⊸ A) ≋ (All τ # λ _ → A')
  tens-ex  : ∀{τ A A'} → A ≋ A' → (($ τ) ⊗ A) ≋ (Ex τ # λ _ → A')
