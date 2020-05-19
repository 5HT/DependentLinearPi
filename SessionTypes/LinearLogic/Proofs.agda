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

open import Data.Product
open import Data.Bool
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common
open import SessionTypes.LinearLogic.Types
open import SessionTypes.LinearLogic.Encoding
open import SessionTypes.LinearLogic.Encode
open import SessionTypes.LinearLogic.Decode

module SessionTypes.LinearLogic.Proofs where

enc-dec : ∀ S b → S ≋ ⌈ enc-Enc S b , b ⌉
enc-dec End _ = refl End
enc-dec ($ x) _ = refl ($ x)
enc-dec (End ⊸ S₁) false = in-in (refl End) (enc-dec S₁ false)
enc-dec (($ x) ⊸ S₁) false = impl-all (enc-dec S₁ false)
enc-dec ((S ⊸ S₂) ⊸ S₁) false = in-in (enc-dec (S ⊸ S₂) false) (enc-dec S₁ false)
enc-dec ((S ⊗ S₂) ⊸ S₁) false = in-in (enc-dec (S ⊗ S₂) false) (enc-dec S₁ false)
enc-dec ((S & S₂) ⊸ S₁) false = in-in (enc-dec (S & S₂) false) (enc-dec S₁ false)
enc-dec ((S ⊕ S₂) ⊸ S₁) false = in-in (enc-dec (S ⊕ S₂) false) (enc-dec S₁ false)
enc-dec ((Ex τ # x) ⊸ S₁) false = in-in (enc-dec (Ex τ # x) false) (enc-dec S₁ false)
enc-dec ((All τ # x) ⊸ S₁) false = in-in (enc-dec (All τ # x) false) (enc-dec S₁ false)
enc-dec (End ⊸ S₁) true = in-in (refl End) (enc-dec S₁ false)
enc-dec (($ x) ⊸ S₁) true = impl-all (enc-dec S₁ false)
enc-dec ((S ⊸ S₂) ⊸ S₁) true = in-in (enc-dec (S ⊸ S₂) false) (enc-dec S₁ false)
enc-dec ((S ⊗ S₂) ⊸ S₁) true = in-in (enc-dec (S ⊗ S₂) false) (enc-dec S₁ false)
enc-dec ((S & S₂) ⊸ S₁) true = in-in (enc-dec (S & S₂) false) (enc-dec S₁ false)
enc-dec ((S ⊕ S₂) ⊸ S₁) true = in-in (enc-dec (S ⊕ S₂) false) (enc-dec S₁ false)
enc-dec ((Ex τ # x) ⊸ S₁) true = in-in (enc-dec (Ex τ # x) false) (enc-dec S₁ false)
enc-dec ((All τ # x) ⊸ S₁) true = in-in (enc-dec (All τ # x) false) (enc-dec S₁ false)
enc-dec (End ⊗ S₁) false = out-out (refl End) (enc-dec S₁ true)
enc-dec (($ x) ⊗ S₁) false = tens-ex (enc-dec S₁ true)
enc-dec ((S ⊸ S₂) ⊗ S₁) false = out-out (enc-dec (S ⊸ S₂) false) (enc-dec S₁ true)
enc-dec ((S ⊗ S₂) ⊗ S₁) false = out-out (enc-dec (S ⊗ S₂) false) (enc-dec S₁ true)
enc-dec ((S & S₂) ⊗ S₁) false = out-out (enc-dec (S & S₂) false) (enc-dec S₁ true)
enc-dec ((S ⊕ S₂) ⊗ S₁) false = out-out (enc-dec (S ⊕ S₂) false) (enc-dec S₁ true)
enc-dec ((Ex τ # x) ⊗ S₁) false = out-out (enc-dec (Ex τ # x) false) (enc-dec S₁ true)
enc-dec ((All τ # x) ⊗ S₁) false = out-out (enc-dec (All τ # x) false) (enc-dec S₁ true)
enc-dec (End ⊗ S₁) true = out-out (refl End) (enc-dec S₁ true)
enc-dec (($ x) ⊗ S₁) true = tens-ex (enc-dec S₁ true)
enc-dec ((S ⊸ S₂) ⊗ S₁) true = out-out (enc-dec (S ⊸ S₂) false) (enc-dec S₁ true)
enc-dec ((S ⊗ S₂) ⊗ S₁) true = out-out (enc-dec (S ⊗ S₂) false) (enc-dec S₁ true)
enc-dec ((S & S₂) ⊗ S₁) true = out-out (enc-dec (S & S₂) false) (enc-dec S₁ true)
enc-dec ((S ⊕ S₂) ⊗ S₁) true = out-out (enc-dec (S ⊕ S₂) false) (enc-dec S₁ true)
enc-dec ((Ex τ # x) ⊗ S₁) true = out-out (enc-dec (Ex τ # x) false) (enc-dec S₁ true)
enc-dec ((All τ # x) ⊗ S₁) true = out-out (enc-dec (All τ # x) false) (enc-dec S₁ true)
enc-dec (S & S₁) false =
  let aux = with-all (enc-dec S false) (enc-dec S₁ false) in
  subst (λ x → (S & S₁) ≋ (All Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S & S₁) true =
  let aux = with-all (enc-dec S false) (enc-dec S₁ false) in
  subst (λ x → (S & S₁) ≋ (All Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S ⊕ S₁) false =
  let aux = plus-ex (enc-dec S true) (enc-dec S₁ true) in
  subst (λ x → (S ⊕ S₁) ≋ (Ex Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S ⊕ S₁) true =
  let aux = plus-ex (enc-dec S true) (enc-dec S₁ true) in
  subst (λ x → (S ⊕ S₁) ≋ (Ex Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (Ex τ # x) false = ex-ex λ x₁ → enc-dec (x x₁) true
enc-dec (Ex τ # x) true = ex-ex λ x₁ → enc-dec (x x₁) true
enc-dec (All τ # x) false = all-all λ x₁ → enc-dec (x x₁) false
enc-dec (All τ # x) true = all-all λ x₁ → enc-dec (x x₁) false

dec-enc : ∀{t} → (enc : Encoding t) → (b : Bool) → t ≡ ⌊ ⌈ enc , b ⌉ , b ⌋
dec-enc unit _ = refl
dec-enc (input unit x) false =
  cong
    (λ x₁ → Chan #1 #0 (Pair (Chan #0 #0 (Pure ⊤)) x₁))
    (extensionality λ x₁ → dec-enc (x x₁) false)
dec-enc (input unit x) true =
  cong
    (λ x₁ → Chan #1 #0 (Pair (Chan #0 #0 (Pure ⊤)) x₁))
    (extensionality λ x₁ → dec-enc (x x₁) true)
dec-enc (input (input e x₁) x) false =
  cong₂ (λ x₂ x₃ → Chan #1 #0 (Pair x₂ λ _ → x₃)) (dec-enc (input e x₁) false) (dec-enc (x tt) false)
dec-enc (input (input e x₁) x) true =
  cong₂ (λ x₂ x₃ → Chan #1 #0 (Pair x₂ λ _ → x₃)) (dec-enc (input e x₁) false) (dec-enc (x tt) true)
dec-enc (input (output e x₁) x) false =
  cong₂ (λ x₂ x₃ → Chan #1 #0 (Pair x₂ λ _ → x₃)) (dec-enc (output e x₁) false) (dec-enc (x tt) false)
dec-enc (input (output e x₁) x) true =
  cong₂ (λ x₂ x₃ → Chan #1 #0 (Pair x₂ λ _ → x₃)) (dec-enc (output e x₁) false) (dec-enc (x tt) true)
dec-enc (input (pure t) x) false =
  cong (λ x₁ → Chan #1 #0 (Pair (Pure t) x₁)) (extensionality λ x₁ → dec-enc (x x₁) false)
dec-enc (input (pure t) x) true =
  cong (λ x₁ → Chan #1 #0 (Pair (Pure t) x₁)) (extensionality λ x₁ → dec-enc (x x₁) true)
dec-enc (output unit x) false =
  cong
    (λ x₁ → Chan #0 #1 (Pair (Chan #0 #0 (Pure ⊤)) x₁))
    (extensionality λ x₁ → dec-enc (x x₁) true)
dec-enc (output unit x) true =
  cong
    (λ x₁ → Chan #0 #1 (Pair (Chan #0 #0 (Pure ⊤)) x₁))
    (extensionality λ x₁ → dec-enc (x x₁) false)
dec-enc (output (input e x₁) x) false =
  cong₂ (λ x₂ x₃ → Chan #0 #1 (Pair x₂ λ _ → x₃)) (dec-enc (input e x₁) false) (dec-enc (x tt) true)
dec-enc (output (input e x₁) x) true =
  cong₂ (λ x₂ x₃ → Chan #0 #1 (Pair x₂ λ _ → x₃)) (dec-enc (input e x₁) false) (dec-enc (x tt) false)
dec-enc (output (output e x₁) x) false =
  cong₂ (λ x₂ x₃ → Chan #0 #1 (Pair x₂ λ _ → x₃)) (dec-enc (output e x₁) false) (dec-enc (x tt) true)
dec-enc (output (output e x₁) x) true =
  cong₂ (λ x₂ x₃ → Chan #0 #1 (Pair x₂ λ _ → x₃)) (dec-enc (output e x₁) false) (dec-enc (x tt) false)
dec-enc (output (pure t) x) false =
  cong (λ x₁ → Chan #0 #1 (Pair (Pure t) x₁)) (extensionality λ x₁ → dec-enc (x x₁) true)
dec-enc (output (pure t) x) true =
  cong (λ x₁ → Chan #0 #1 (Pair (Pure t) x₁)) (extensionality λ x₁ → dec-enc (x x₁) false)
dec-enc (pure _) _ = refl
