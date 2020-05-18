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

open import Data.Fin

module SessionTypes.Labeled.Types where

{- TYPE -}
mutual
  data BaseType : Set₁ where
    Pure    : Set → BaseType
    Session : SessionType → BaseType

  data SessionType : Set₁ where
    End : SessionType
    In Out : BaseType → SessionType → SessionType
    Branch Choice : ∀{n} → (f : Fin n → SessionType) → SessionType

{- ##### Duality ##### -}

-- data _∥ₛ_ : SessionType → SessionType → Set₁ where
--   ∅∥ₛ∅ : ∅ ∥ₛ ∅
--   ¿∥ₛ! : ∀{T S S'} → S ∥ₛ S' → (¿ T , S) ∥ₛ (! T , S')
--   !∥ₛ¿ : ∀{T S S'} → S ∥ₛ S' → (! T , S) ∥ₛ (¿ T , S')
--   &∥ₛ⊕ : ∀{n}{f f' : Fin n → SessionType} → (∀{i} → f i ∥ₛ f' i) → & f ∥ₛ ⊕ f'
--   ⊕∥ₛ& : ∀{n}{f f' : Fin n → SessionType} → (∀{i} → f i ∥ₛ f' i) → ⊕ f ∥ₛ & f'


-- ⊥ₛ : SessionType → SessionType
-- ⊥ₛ ∅ = ∅
-- ⊥ₛ (¿ x , s) = ! x , ⊥ₛ s
-- ⊥ₛ (! x , s) = ¿ x , ⊥ₛ s
-- ⊥ₛ (& x) = ⊕ λ x₁ → ⊥ₛ (x x₁)
-- ⊥ₛ (⊕ x) = & λ x₁ → ⊥ₛ (x x₁)
