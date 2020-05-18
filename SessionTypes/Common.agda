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

import Level
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Unit using (⊤)
open import Data.Product using (Σ)

module SessionTypes.Common where

postulate
  extensionality : Extensionality Level.zero (Level.suc Level.zero)

{- MULTIPLICITY -}

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

{- TYPE -}

mutual
  data Type : Set₁ where
    Pure : (A : Set) → Type
    Chan : Multiplicity → Multiplicity → Type → Type
    Pair : ∀(t : Type) → (f : ⟦ t ⟧ → Type) → Type

  ⟦_⟧ : Type → Set
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = ⊤
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x -> ⟦ f x ⟧

flip-chan : Type → Type
flip-chan (Chan σ ρ t) = Chan ρ σ t
flip-chan t            = t
