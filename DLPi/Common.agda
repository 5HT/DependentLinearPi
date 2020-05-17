-- This file is part of DLπ.

-- DLπ is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- DLπ is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
-- General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with DLπ.  If not, see <https://www.gnu.org/licenses/>.

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym)

_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)

zero-not-suc : ∀{m} -> zero ≢ suc m
zero-not-suc ()

suc-not-zero : ∀{m} -> suc m ≢ zero
suc-not-zero ()

suc-≢ : ∀{m n} -> suc m ≢ suc n -> m ≢ n
suc-≢ neq p rewrite p = neq refl

suc-≡ : ∀{m n} -> suc m ≡ suc n -> m ≡ n
suc-≡ refl = refl

≢-suc : ∀{m n} -> m ≢ n -> suc m ≢ suc n
≢-suc neq p rewrite suc-≡ p = neq refl

cong₃ : ∀{ℓ1 ℓ2 ℓ3 ℓ4}{A : Set ℓ1}{B : Set ℓ2}{C : Set ℓ3}{D : Set ℓ4}{x x' : A}{y y' : B}{z z' : C}
  -> (f : A -> B -> C -> D)
  -> x ≡ x'
  -> y ≡ y'
  -> z ≡ z'
  -> f x y z ≡ f x' y' z'
cong₃ f p q r rewrite p | q | r = refl

postulate
  extensionality :
    ∀{A B : Set} {f g : A -> B} ->
    (∀(x : A) -> f x ≡ g x) ->
    f ≡ g
  ∀-extensionality :
    ∀{ℓ ℓ'}{A : Set ℓ} {B : A -> Set ℓ'} {f g : (x : A) -> B x} ->
    (∀(x : A) -> f x ≡ g x) ->
    f ≡ g
