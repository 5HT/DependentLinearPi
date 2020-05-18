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

open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Bool
open import Data.Unit

open import SessionTypes.Common
open import SessionTypes.Labeled.Types
open import SessionTypes.Labeled.Encode
open import SessionTypes.Labeled.Decode
open import SessionTypes.Labeled.Encoding

module Sessiontypes.Labeled.Proofs where

mutual
  dec-enc-base : (τ : BaseType) → τ ≡ ⌈ base-image τ ⌉-base
  dec-enc-base (Pure _) = refl
  dec-enc-base (Session T) = cong Session (dec-enc T)

  dec-enc : (T : SessionType) → T ≡ ⌈ image T ⌉
  dec-enc End = refl
  dec-enc (In τ T) = cong₂ In (dec-enc-base τ) (dec-enc T)
  dec-enc (Out τ T) = cong₂ Out (dec-enc-base τ) (dec-enc-dual T)
  dec-enc (Branch f) = cong Branch (extensionality λ i → dec-enc (f i))
  dec-enc (Choice f) = cong Choice (extensionality λ i → dec-enc-dual (f i))

  dec-enc-dual : (T : SessionType) → T ≡ ⌈ dual-enc (image T) ⌉-dual
  dec-enc-dual End = refl
  dec-enc-dual (In τ T) = cong₂ In (dec-enc-base τ) (dec-enc T)
  dec-enc-dual (Out τ T) = cong₂ Out (dec-enc-base τ) (dec-enc-dual T)
  dec-enc-dual (Branch f) = cong Branch (extensionality λ i → dec-enc (f i))
  dec-enc-dual (Choice f) = cong Choice (extensionality λ i → dec-enc-dual (f i))

mutual
  enc-dec-base : ∀{t} → (benc : BaseEncoding t) → t ≡ ⌊ ⌈ benc ⌉-base ⌋-base
  enc-dec-base Pure = refl
  enc-dec-base (Chan enc) = enc-dec enc

  enc-dec : ∀{t} → (enc : Encoding t) → t ≡ ⌊ ⌈ enc ⌉ ⌋
  enc-dec End = refl
  enc-dec (In benc enc) = cong₂ (λ x y → Chan #1 #0 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec enc)
  enc-dec (Out benc enc) = cong₂ (λ x y → Chan #0 #1 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec-dual enc)
  enc-dec (Branch fenc) = cong (λ x → Chan #1 #0 (Pair _ x)) (extensionality λ i → enc-dec (fenc i))
  enc-dec (Choice fenc) = cong (λ x → Chan #0 #1 (Pair _ x)) (extensionality λ i → enc-dec-dual (fenc i))

  enc-dec-dual : ∀{t} → (enc : Encoding t) → t ≡ dual-of ⌊ ⌈ enc ⌉-dual ⌋
  enc-dec-dual End = refl
  enc-dec-dual (In benc enc) = cong₂ (λ x y → Chan #1 #0 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec-dual enc)
  enc-dec-dual (Out benc enc) = cong₂ (λ x y → Chan #0 #1 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec enc)
  enc-dec-dual (Branch fenc) = cong (λ x → Chan #1 #0 (Pair _ x)) (extensionality λ i → enc-dec-dual (fenc i))
  enc-dec-dual (Choice fenc) = cong (λ x → Chan #0 #1 (Pair _ x)) (extensionality λ i → enc-dec (fenc i))

-- {- ##### Duality Correctness ##### -}

-- dec-∥ₛ-eq : ∀{T}(E : πEncoding T) → (∀ b → ⌈ E , b ⌉ ∥ₛ ⌈ E , not b ⌉)
-- dec-∥ₛ-eq unit _ = ∅∥ₛ∅
-- dec-∥ₛ-eq (¿ch _ E) false = ¿∥ₛ! (dec-∥ₛ-eq E false) 
-- dec-∥ₛ-eq (!ch _ E) false = !∥ₛ¿ (dec-∥ₛ-eq E true)
-- dec-∥ₛ-eq (&ch f) false = &∥ₛ⊕ λ {i} → dec-∥ₛ-eq (f i) false
-- dec-∥ₛ-eq (⊕ch f) false = ⊕∥ₛ& λ {i} → dec-∥ₛ-eq (f i) true
-- dec-∥ₛ-eq (¿ch x E) true = !∥ₛ¿ (dec-∥ₛ-eq E true)
-- dec-∥ₛ-eq (!ch x E) true = ¿∥ₛ! (dec-∥ₛ-eq E false)
-- dec-∥ₛ-eq (&ch f) true = ⊕∥ₛ& λ {i} → dec-∥ₛ-eq (f i) true
-- dec-∥ₛ-eq (⊕ch f) true = &∥ₛ⊕ λ {i} → dec-∥ₛ-eq (f i) false

-- enc-∥π-eq : ∀ S → (∀ b → ⌊ S , b ⌋ ∥π ⌊ S , not b ⌋)
-- enc-∥π-eq ∅ _ = flip
-- enc-∥π-eq (¿ _ , _) false = flip
-- enc-∥π-eq (! _ , _) false = flip
-- enc-∥π-eq (& _) false = flip
-- enc-∥π-eq (⊕ _) false = flip
-- enc-∥π-eq (¿ _ , _) true = flip
-- enc-∥π-eq (! _ , _) true = flip
-- enc-∥π-eq (& _) true = flip
-- enc-∥π-eq (⊕ _) true = flip

-- ∥ₛ-enc-eq : ∀{S S'} → S ∥ₛ S' → ∀ b → ⌊ S , b ⌋ ≡ ⌊ S' , not b ⌋
-- ∥ₛ-enc-eq ∅∥ₛ∅ _ = refl
-- ∥ₛ-enc-eq (¿∥ₛ! d) false = cong (λ x → Chan #1 #0 (Pair _ λ _ → x)) (∥ₛ-enc-eq d false)
-- ∥ₛ-enc-eq (!∥ₛ¿ d) false = cong (λ x → Chan #0 #1 (Pair _ λ _ → x)) (∥ₛ-enc-eq d true)
-- ∥ₛ-enc-eq (&∥ₛ⊕ {n} x) false = cong (λ x₁ → Chan #1 #0 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) false)
-- ∥ₛ-enc-eq (⊕∥ₛ& {n} x) false = cong (λ x₁ → Chan #0 #1 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) true)
-- ∥ₛ-enc-eq (¿∥ₛ! d) true = cong (λ x → Chan #0 #1 (Pair _ λ _ → x)) (∥ₛ-enc-eq d false)
-- ∥ₛ-enc-eq (!∥ₛ¿ d) true = cong (λ x → Chan #1 #0 (Pair _ λ _ → x)) (∥ₛ-enc-eq d true)
-- ∥ₛ-enc-eq (&∥ₛ⊕ {n} x) true = cong (λ x₁ → Chan #0 #1 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) false)
-- ∥ₛ-enc-eq (⊕∥ₛ& {n} x) true = cong (λ x₁ → Chan #1 #0 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) true)


-- dec-flip-eq : ∀{T}(E : πEncoding T) b → ⌈ E , b ⌉ ≡ ⌈ flip-π-enc E , not b ⌉
-- dec-flip-eq unit _ = refl
-- dec-flip-eq (¿ch x E) false = refl
-- dec-flip-eq (!ch x E) false = refl
-- dec-flip-eq (&ch e) false = refl
-- dec-flip-eq (⊕ch e) false = refl
-- dec-flip-eq (¿ch x E) true = refl
-- dec-flip-eq (!ch x E) true = refl
-- dec-flip-eq (&ch e) true = refl
-- dec-flip-eq (⊕ch e) true = refl


-- {- ##### Commuting Duality ##### -}

-- comm-dual-dec : ∀{T} (E : πEncoding T) b → ⌈ flip-π-enc E , b ⌉ ≡ ⊥ₛ ⌈ E , b ⌉
-- comm-dual-dec unit _ = refl
-- comm-dual-dec (¿ch x E) false =
--   let rec = comm-dual-dec E false in
--   cong₂ (λ x₁ x₂ → ! x₁ , x₂) refl (trans (dec-flip-eq E true) rec)
-- comm-dual-dec (!ch x E) false =
--   let rec = comm-dual-dec E true in
--   cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) refl (trans (dec-flip-eq E false) rec)
-- comm-dual-dec (&ch e) false =
--   cong (λ x → ⊕ x) (extensionality λ x → trans (dec-flip-eq (e x) true) (comm-dual-dec (e x) false))
-- comm-dual-dec (⊕ch e) false =
--   cong (λ x → & x) (extensionality λ x → trans (dec-flip-eq (e x) false) (comm-dual-dec (e x) true))
-- comm-dual-dec (¿ch x E) true =
--   let rec = comm-dual-dec E true in
--   cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) refl (trans (dec-flip-eq E false) rec)
-- comm-dual-dec (!ch x E) true =
--   let rec = comm-dual-dec E false in
--   cong₂ (λ x₁ x₂ → ! x₁ , x₂) refl (trans (dec-flip-eq E true) rec)
-- comm-dual-dec (&ch e) true =
--   cong (λ x → & x) (extensionality λ x → trans (dec-flip-eq (e x) false) (comm-dual-dec (e x) true))
-- comm-dual-dec (⊕ch e) true =
--   cong (λ x → ⊕ x) (extensionality λ x → trans (dec-flip-eq (e x) true) (comm-dual-dec (e x) false))
