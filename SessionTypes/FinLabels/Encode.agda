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

open import Data.Fin as Fin
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common
open import SessionTypes.FinLabels.Types
open import SessionTypes.FinLabels.Encoding

module SessionTypes.FinLabels.Encode where

mutual
  ⌊_⌋-base : BaseType → Type
  ⌊ Pure A ⌋-base = Pure A
  ⌊ Session T ⌋-base = ⌊ T ⌋

  ⌊_⌋ : SessionType → Type
  ⌊ End ⌋ = Chan #0 #0 (Pure ⊤)
  ⌊ In τ T ⌋ = Chan #1 #0 (Pair ⌊ τ ⌋-base λ _ → ⌊ T ⌋)
  ⌊ Out τ T ⌋ = Chan #0 #1 (Pair ⌊ τ ⌋-base λ _ → flip-chan ⌊ T ⌋)
  ⌊ Branch {n} f ⌋ = Chan #1 #0 (Pair (Pure (Fin n)) λ n → ⌊ f n ⌋)
  ⌊ Choice {n} f ⌋ = Chan #0 #1 (Pair (Pure (Fin n)) λ n → flip-chan ⌊ f n ⌋)

mutual
  base-image : ∀ B → BaseEncoding ⌊ B ⌋-base
  base-image (Pure _) = Pure
  base-image (Session T) = Chan (image T)

  image : (S : SessionType) → Encoding ⌊ S ⌋
  image End = End
  image (In τ T) = In (base-image τ) (image T)
  image (Out τ T) = Out (base-image τ) (dual-enc (image T))
  image (Branch f) = Branch λ i → image (f i)
  image (Choice f) = Choice λ i → dual-enc (image (f i))

-- ∥ₛ-to-flip : ∀ b S S' → S ∥ₛ S' → ⌊ S , b ⌋ ≡ ⌊ S' , not b ⌋
-- ∥ₛ-to-flip _ ∅ ∅ ∅∥ₛ∅ = refl
-- ∥ₛ-to-flip false (¿ T , S) (! T , S') (¿∥ₛ! d) =
--            let rec = ∥ₛ-to-flip false S S' d in
--            let t = Pair ⌊ T ⌋-base in
--            cong (λ x → Chan #1 #0 (t λ _ → x)) rec
-- ∥ₛ-to-flip true (¿ T , S) (! T , S') (¿∥ₛ! d) =
--            let rec = ∥ₛ-to-flip false S S' d in
--            let t = Pair ⌊ T ⌋-base in
--            cong (λ x → Chan #0 #1 (t λ _ → x)) rec
-- ∥ₛ-to-flip false (! T , S) (¿ T , S') (!∥ₛ¿ d) =
--            let rec = ∥ₛ-to-flip true S S' d in
--            let t = Pair ⌊ T ⌋-base in
--            cong (λ x → Chan #0 #1 (t λ _ → x)) rec
-- ∥ₛ-to-flip true (! T , S) (¿ T , S') (!∥ₛ¿ d) =
--            let rec = ∥ₛ-to-flip true S S' d in
--            let t = Pair ⌊ T ⌋-base in
--            cong (λ x → Chan #1 #0 (t λ _ → x)) rec
-- ∥ₛ-to-flip false (& f) (⊕ f') (&∥ₛ⊕ x) =
--   let aux = λ i → ∥ₛ-to-flip false (f i) (f' i) (x {i}) in
--   cong
--     (λ x₁ → Chan #1 #0 (Pair (Pure _) x₁))
--     (extensionality aux)
-- ∥ₛ-to-flip true (& f) (⊕ f') (&∥ₛ⊕ x) =
--   let aux = λ i → ∥ₛ-to-flip false (f i) (f' i) (x {i}) in
--   cong
--     (λ x₁ → Chan #0 #1 (Pair (Pure _) x₁))
--     (extensionality aux)
-- ∥ₛ-to-flip false (⊕ f) (& f') (⊕∥ₛ& x) =
--   let aux = λ i → ∥ₛ-to-flip true (f i) (f' i) (x {i}) in
--   cong
--     (λ x₁ → Chan #0 #1 (Pair (Pure _) x₁))
--     (extensionality aux)
-- ∥ₛ-to-flip true (⊕ f) (& f') (⊕∥ₛ& x) =
--   let aux = λ i → ∥ₛ-to-flip true (f i) (f' i) (x {i}) in
--   cong
--     (λ x₁ → Chan #1 #0 (Pair (Pure _) x₁))
--     (extensionality aux)
