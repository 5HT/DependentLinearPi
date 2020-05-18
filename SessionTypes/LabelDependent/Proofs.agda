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
  enc-dec : ∀{Γ T} → (E : Env Γ) → (W : WFS Γ T) → Bisimilar E W (dec-WFS (image E W))
  enc-dec E wf-end = sim-end
  enc-dec E (wf-case x W1 W2) with env-lookup E x
  ... | false , p = sim-case-lf p (enc-dec E W1)
  ... | true  , p = sim-case-lt p (enc-dec E W2)
  enc-dec E (wf-in-s W1 W2) = sim-in-s (enc-dec E W1) (enc-dec E W2)
  enc-dec E (wf-out-s W1 W2) = sim-out-s (enc-dec E W1) (enc-dec-dual E W2)
  enc-dec E (wf-in-b W) = sim-in-b (sim-case-rf here (enc-dec (false :: E) W))
                                    (sim-case-rt here (enc-dec (true :: E) W))
  enc-dec E (wf-out-b W) = sim-out-b (sim-case-rf here (enc-dec-dual (false :: E) W))
                                      (sim-case-rt here (enc-dec-dual (true :: E) W))

  enc-dec-dual : ∀{Γ T} → (E : Env Γ) → (W : WFS Γ T) → Bisimilar E W (dec-WFS-dual (dual-enc (image E W)))
  enc-dec-dual E wf-end = sim-end
  enc-dec-dual E (wf-case x W1 W2) with env-lookup E x
  ... | false , p = sim-case-lf p (enc-dec-dual E W1)
  ... | true  , p = sim-case-lt p (enc-dec-dual E W2)
  enc-dec-dual E (wf-in-s W1 W2) = sim-in-s (enc-dec E W1) (enc-dec E W2)
  enc-dec-dual E (wf-out-s W1 W2) = sim-out-s (enc-dec E W1) (enc-dec-dual E W2)
  enc-dec-dual E (wf-in-b W) = sim-in-b (sim-case-rf here (enc-dec (false :: E) W))
                                         (sim-case-rt here (enc-dec (true :: E) W))
  enc-dec-dual E (wf-out-b W) = sim-out-b (sim-case-rf here (enc-dec-dual (false :: E) W))
                                           (sim-case-rt here (enc-dec-dual (true :: E) W))

mutual
  dec-enc : ∀{Γ t} → (E : Env Γ) → (enc : Encoding t) → t ≡ ⌊ E , dec-WFS enc ⌋
  dec-enc E unit = refl
  dec-enc E (in-b f) =
    cong (Chan #1 #0)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → dec-enc (true :: E) (f true)
                            ; false → dec-enc (false :: E) (f false) }))
  dec-enc E (out-b f) =
    cong (Chan #0 #1)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → dec-enc-dual (true :: E) (f true)
                            ; false → dec-enc-dual (false :: E) (f false) }))
  dec-enc E (in-s enc1 enc2) =
    cong (Chan #1 #0) (cong₂ (λ x y → Pair x (λ _ → y)) (dec-enc E enc1) (dec-enc E enc2))
  dec-enc E (out-s enc1 enc2) =
    cong (Chan #0 #1) (cong₂ (λ x y → Pair x (λ _ → y)) (dec-enc E enc1) (dec-enc-dual E enc2))

  dec-enc-dual : ∀{Γ t} → (E : Env Γ) → (enc : Encoding t) → t ≡ flip-chan ⌊ E , dec-WFS-dual enc ⌋
  dec-enc-dual E unit = refl
  dec-enc-dual E (in-b f) =
    cong (Chan #1 #0)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → dec-enc-dual (true :: E) (f true) ;
                              false → dec-enc-dual (false :: E) (f false) }))
  dec-enc-dual E (out-b f) =
    cong (Chan #0 #1)
    (cong (Pair (Pure Bool))
          (extensionality λ { true  → dec-enc (true :: E) (f true)
                            ; false → dec-enc (false :: E) (f false) }))
  dec-enc-dual E (in-s enc1 enc2) =
    cong (Chan #1 #0) (cong₂ (λ x y → Pair x (λ _ → y)) (dec-enc E enc1) (dec-enc-dual E enc2))
  dec-enc-dual E (out-s enc1 enc2) =
    cong (Chan #0 #1) (cong₂ (λ x y → Pair x (λ _ → y)) (dec-enc E enc1) (dec-enc E enc2))
