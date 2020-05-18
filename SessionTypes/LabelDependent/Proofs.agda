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
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common
open import SessionTypes.LabelDependent.Encode
open import SessionTypes.LabelDependent.Decode
open import SessionTypes.LabelDependent.Types
open import SessionTypes.LabelDependent.Encoding

module SessionTypes.LabelDependent.Proofs where

mutual
  xenc-dec : ∀{Γ T} → (E : Env Γ) → (W : WFS Γ T) → Bisimilar E W (dec-WFS-Γ false (image E W))
  xenc-dec E wf-end = sim-end
  xenc-dec E (wf-case x W1 W2) with env-lookup E x
  ... | false , p = sim-case-lf p (xenc-dec E W1)
  ... | true  , p = sim-case-lt p (xenc-dec E W2)
  xenc-dec E (wf-in-s W1 W2) = sim-in-s (xenc-dec E W1) (xenc-dec E W2)
  xenc-dec E (wf-out-s W1 W2) = sim-out-s (xenc-dec E W1) (xenc-dec-dual E W2)
  xenc-dec E (wf-in-b W) = sim-in-b (sim-case-rf here (xenc-dec (false :: E) W))
                                    (sim-case-rt here (xenc-dec (true :: E) W))
  xenc-dec E (wf-out-b W) = sim-out-b (sim-case-rf here (xenc-dec-dual (false :: E) W))
                                      (sim-case-rt here (xenc-dec-dual (true :: E) W))

  xenc-dec-dual : ∀{Γ T} → (E : Env Γ) → (W : WFS Γ T) → Bisimilar E W (dec-WFS-Γ true (dual-enc (image E W)))
  xenc-dec-dual E wf-end = sim-end
  xenc-dec-dual E (wf-case x W1 W2) with env-lookup E x
  ... | false , p = sim-case-lf p (xenc-dec-dual E W1)
  ... | true  , p = sim-case-lt p (xenc-dec-dual E W2)
  xenc-dec-dual E (wf-in-s W1 W2) = sim-in-s (xenc-dec E W1) (xenc-dec E W2)
  xenc-dec-dual E (wf-out-s W1 W2) = sim-out-s (xenc-dec E W1) (xenc-dec-dual E W2)
  xenc-dec-dual E (wf-in-b W) = sim-in-b (sim-case-rf here (xenc-dec (false :: E) W))
                                         (sim-case-rt here (xenc-dec (true :: E) W))
  xenc-dec-dual E (wf-out-b W) = sim-out-b (sim-case-rf here (xenc-dec-dual (false :: E) W))
                                           (sim-case-rt here (xenc-dec-dual (true :: E) W))

mutual
  xdec-enc : ∀{Γ t} → (E : Env Γ) → (enc : Encoding t) → t ≡ x⌊ E , dec-WFS-Γ false enc ⌋
  xdec-enc E unit = refl
  xdec-enc E (in-b f) =
    cong (Chan #1 #0)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → xdec-enc (true :: E) (f true)
                            ; false → xdec-enc (false :: E) (f false) }))
  xdec-enc E (out-b f) =
    cong (Chan #0 #1)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → xdec-enc-dual (true :: E) (f true)
                            ; false → xdec-enc-dual (false :: E) (f false) }))
  xdec-enc E (in-s enc1 enc2) =
    cong (Chan #1 #0) (cong₂ (λ x y → Pair x (λ _ → y)) (xdec-enc E enc1) (xdec-enc E enc2))
  xdec-enc E (out-s enc1 enc2) =
    cong (Chan #0 #1) (cong₂ (λ x y → Pair x (λ _ → y)) (xdec-enc E enc1) (xdec-enc-dual E enc2))

  xdec-enc-dual : ∀{Γ t} → (E : Env Γ) → (enc : Encoding t) → t ≡ flip-chan x⌊ E , dec-WFS-Γ true enc ⌋
  xdec-enc-dual E unit = refl
  xdec-enc-dual E (in-b f) =
    cong (Chan #1 #0)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → xdec-enc-dual (true :: E) (f true) ;
                              false → xdec-enc-dual (false :: E) (f false) }))
  xdec-enc-dual E (out-b f) =
    cong (Chan #0 #1)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → xdec-enc (true :: E) (f true)
                            ; false → xdec-enc (false :: E) (f false) }))
  xdec-enc-dual E (in-s enc1 enc2) =
    cong (Chan #1 #0) (cong₂ (λ x y → Pair x (λ _ → y)) (xdec-enc E enc1) (xdec-enc-dual E enc2))
  xdec-enc-dual E (out-s enc1 enc2) =
    cong (Chan #0 #1) (cong₂ (λ x y → Pair x (λ _ → y)) (xdec-enc E enc1) (xdec-enc E enc2))

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
