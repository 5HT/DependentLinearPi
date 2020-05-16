open import LDSTypes
open import Pi_Encoding
open import Encode
open import Decode
open import Data.Product
open import Data.Bool
open import Common
open import Relation.Binary.PropositionalEquality

module Proofs where

enc-dec : ∀{Γ S} b → (E : Env Γ) → (W : WFS Γ S) -> Bisimilar E W (dec-WFS-Γ b (enc-Enc E W b))
enc-dec _ _ wf-end = sim-end
enc-dec false E (wf-case x W W₁) with env-lookup E x
enc-dec false E (wf-case x W W₁) | false , p = sim-case-lf p (enc-dec false E W)
enc-dec false E (wf-case x W W₁) | true , p = sim-case-lt p (enc-dec false E W₁)
enc-dec true E (wf-case x W W₁) with env-lookup E x
enc-dec true E (wf-case x W W₁) | false , p = sim-case-lf p (enc-dec true E W)
enc-dec true E (wf-case x W W₁) | true , p = sim-case-lt p (enc-dec true E W₁)
enc-dec false E (wf-in-s W W₁) = sim-in-s (enc-dec false E W) (enc-dec false E W₁)
enc-dec true E (wf-in-s W W₁) = sim-in-s (enc-dec false E W) (enc-dec false E W₁)
enc-dec false E (wf-out-s W W₁) = sim-out-s (enc-dec false E W) (enc-dec true E W₁)
enc-dec true E (wf-out-s W W₁) = sim-out-s (enc-dec false E W) (enc-dec true E W₁)
enc-dec false E (wf-in-b W) =
  sim-in-b (sim-case-rf here (enc-dec false (false :: E) W)) (sim-case-rt here (enc-dec false (true :: E) W))
enc-dec true E (wf-in-b W) =
  sim-in-b (sim-case-rf here (enc-dec false (false :: E) W)) (sim-case-rt here (enc-dec false (true :: E) W))
enc-dec false E (wf-out-b W) = sim-out-b ((sim-case-rf here (enc-dec true (false :: E) W))) ((sim-case-rt here (enc-dec true (true :: E) W)))
enc-dec true E (wf-out-b W) = sim-out-b ((sim-case-rf here (enc-dec true (false :: E) W))) ((sim-case-rt here (enc-dec true (true :: E) W)))

dec-enc : ∀{Γ t} b → (E : Env Γ) → (enc : Encoding t) → t ≡ ⌊ E , dec-WFS-Γ b enc , b ⌋ 
dec-enc _ E unit = refl
dec-enc false E (in-b x) =
  cong (Chan #1 #0)
  (cong (Pair (Pure Bool))
    (extensionality λ {true → dec-enc false (true :: E) (x true) ; false → dec-enc false (false :: E) (x false)}))
dec-enc true E (in-b x) =
  cong (Chan #1 #0)
  (cong (Pair (Pure Bool))
    (extensionality λ {true → dec-enc true (true :: E) (x true) ; false → dec-enc true (false :: E) (x false)}))
dec-enc false E (out-b x) =
  cong (Chan #0 #1)
  (cong (Pair (Pure Bool))
    (extensionality λ {true → dec-enc true (true :: E) (x true) ; false → dec-enc true (false :: E) (x false)}))
dec-enc true E (out-b x) =
  cong (Chan #0 #1)
  (cong (Pair (Pure Bool))
    (extensionality λ {true → dec-enc false (true :: E) (x true) ; false → dec-enc false (false :: E) (x false)}))
dec-enc false E (in-s enc enc₁) =
  cong₂ (λ x x₁ → Chan #1 #0 (Pair x λ _ → x₁)) (dec-enc false E enc) (dec-enc false E enc₁)
dec-enc true E (in-s enc enc₁) =
   cong₂ (λ x x₁ → Chan #1 #0 (Pair x λ _ → x₁)) (dec-enc false E enc) (dec-enc true E enc₁)
dec-enc false E (out-s enc enc₁) =
  cong₂ (λ x x₁ → Chan #0 #1 (Pair x λ _ → x₁)) (dec-enc false E enc) (dec-enc true E enc₁)
dec-enc true E (out-s enc enc₁) =
  cong₂ (λ x x₁ → Chan #0 #1 (Pair x λ _ → x₁)) (dec-enc false E enc) (dec-enc false E enc₁)
