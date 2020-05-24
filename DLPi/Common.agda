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

open import Data.Nat using (suc)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl)

suc-≢ : ∀{m n} -> suc m ≢ suc n -> m ≢ n
suc-≢ = contraposition (cong suc)

cong₃ :
  ∀{ℓ1 ℓ2 ℓ3 ℓ4}{A : Set ℓ1}{B : Set ℓ2}{C : Set ℓ3}{D : Set ℓ4}{x x' : A}{y y' : B}{z z' : C} ->
  (f : A -> B -> C -> D) -> x ≡ x' -> y ≡ y' -> z ≡ z' -> f x y z ≡ f x' y' z'
cong₃ _ refl refl refl = refl

postulate
  extensionality :
    ∀{A B : Set} {f g : A -> B} -> (∀(x : A) -> f x ≡ g x) -> f ≡ g
  ∀-extensionality :
    ∀{ℓ ℓ'}{A : Set ℓ} {B : A -> Set ℓ'} {f g : (x : A) -> B x} ->
    (∀(x : A) -> f x ≡ g x) -> f ≡ g
