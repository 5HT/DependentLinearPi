open import LTTypes
open import Pi_Types
open import Encode
open import Decode
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Common
open import Relation.Binary.PropositionalEquality

module Proofs where

enc-dec : ∀ S b → S ≋ ⌈ enc-Enc S b , b ⌉
enc-dec End _ = refl End
enc-dec ($ x) _ = refl ($ x)
enc-dec (End ⊸ S₁) false = in-in (refl End) (enc-dec S₁ false)
enc-dec (($ x) ⊸ S₁) false = impl-ex (enc-dec S₁ false)
enc-dec ((S ⊸ S₂) ⊸ S₁) false = in-in (enc-dec (S ⊸ S₂) false) (enc-dec S₁ false)
enc-dec ((S ⨂ S₂) ⊸ S₁) false = in-in (enc-dec (S ⨂ S₂) false) (enc-dec S₁ false)
enc-dec ((S & S₂) ⊸ S₁) false = in-in (enc-dec (S & S₂) false) (enc-dec S₁ false)
enc-dec ((S ⨁ S₂) ⊸ S₁) false = in-in (enc-dec (S ⨁ S₂) false) (enc-dec S₁ false)
enc-dec ((All τ # x) ⊸ S₁) false = in-in (enc-dec (All τ # x) false) (enc-dec S₁ false)
enc-dec ((Ex τ # x) ⊸ S₁) false = in-in (enc-dec (Ex τ # x) false) (enc-dec S₁ false)
enc-dec (End ⊸ S₁) true = in-in (refl End) (enc-dec S₁ false)
enc-dec (($ x) ⊸ S₁) true = impl-ex (enc-dec S₁ false)
enc-dec ((S ⊸ S₂) ⊸ S₁) true = in-in (enc-dec (S ⊸ S₂) false) (enc-dec S₁ false)
enc-dec ((S ⨂ S₂) ⊸ S₁) true = in-in (enc-dec (S ⨂ S₂) false) (enc-dec S₁ false)
enc-dec ((S & S₂) ⊸ S₁) true = in-in (enc-dec (S & S₂) false) (enc-dec S₁ false)
enc-dec ((S ⨁ S₂) ⊸ S₁) true = in-in (enc-dec (S ⨁ S₂) false) (enc-dec S₁ false)
enc-dec ((All τ # x) ⊸ S₁) true = in-in (enc-dec (All τ # x) false) (enc-dec S₁ false)
enc-dec ((Ex τ # x) ⊸ S₁) true = in-in (enc-dec (Ex τ # x) false) (enc-dec S₁ false)
enc-dec (End ⨂ S₁) false = out-out (refl End) (enc-dec S₁ true)
enc-dec (($ x) ⨂ S₁) false = tens-all (enc-dec S₁ true)
enc-dec ((S ⊸ S₂) ⨂ S₁) false = out-out (enc-dec (S ⊸ S₂) false) (enc-dec S₁ true)
enc-dec ((S ⨂ S₂) ⨂ S₁) false = out-out (enc-dec (S ⨂ S₂) false) (enc-dec S₁ true)
enc-dec ((S & S₂) ⨂ S₁) false = out-out (enc-dec (S & S₂) false) (enc-dec S₁ true)
enc-dec ((S ⨁ S₂) ⨂ S₁) false = out-out (enc-dec (S ⨁ S₂) false) (enc-dec S₁ true)
enc-dec ((All τ # x) ⨂ S₁) false = out-out (enc-dec (All τ # x) false) (enc-dec S₁ true)
enc-dec ((Ex τ # x) ⨂ S₁) false = out-out (enc-dec (Ex τ # x) false) (enc-dec S₁ true)
enc-dec (End ⨂ S₁) true = out-out (refl End) (enc-dec S₁ true)
enc-dec (($ x) ⨂ S₁) true = tens-all (enc-dec S₁ true)
enc-dec ((S ⊸ S₂) ⨂ S₁) true = out-out (enc-dec (S ⊸ S₂) false) (enc-dec S₁ true)
enc-dec ((S ⨂ S₂) ⨂ S₁) true = out-out (enc-dec (S ⨂ S₂) false) (enc-dec S₁ true)
enc-dec ((S & S₂) ⨂ S₁) true = out-out (enc-dec (S & S₂) false) (enc-dec S₁ true)
enc-dec ((S ⨁ S₂) ⨂ S₁) true = out-out (enc-dec (S ⨁ S₂) false) (enc-dec S₁ true)
enc-dec ((All τ # x) ⨂ S₁) true = out-out (enc-dec (All τ # x) false) (enc-dec S₁ true)
enc-dec ((Ex τ # x) ⨂ S₁) true = out-out (enc-dec (Ex τ # x) false) (enc-dec S₁ true)
enc-dec (S & S₁) false =
  let aux = with-ex (enc-dec S false) (enc-dec S₁ false) in
  subst (λ x → (S & S₁) ≋ (Ex Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S & S₁) true =
  let aux = with-ex (enc-dec S false) (enc-dec S₁ false) in
  subst (λ x → (S & S₁) ≋ (Ex Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S ⨁ S₁) false =
  let aux = plus-all (enc-dec S true) (enc-dec S₁ true) in
  subst (λ x → (S ⨁ S₁) ≋ (All Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (S ⨁ S₁) true =
  let aux = plus-all (enc-dec S true) (enc-dec S₁ true) in
  subst (λ x → (S ⨁ S₁) ≋ (All Bool # x)) (extensionality λ {false → refl ; true → refl}) aux
enc-dec (All τ # x) false = all-all λ x₁ → enc-dec (x x₁) true
enc-dec (All τ # x) true = all-all λ x₁ → enc-dec (x x₁) true
enc-dec (Ex τ # x) false = ex-ex λ x₁ → enc-dec (x x₁) false
enc-dec (Ex τ # x) true = ex-ex λ x₁ → enc-dec (x x₁) false

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
