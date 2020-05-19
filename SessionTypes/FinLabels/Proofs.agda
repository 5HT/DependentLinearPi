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
open import SessionTypes.FinLabels.Types
open import SessionTypes.FinLabels.Encode
open import SessionTypes.FinLabels.Decode
open import SessionTypes.FinLabels.Encoding

module Sessiontypes.FinLabels.Proofs where

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

  enc-dec-dual : ∀{t} → (enc : Encoding t) → t ≡ flip-chan ⌊ ⌈ enc ⌉-dual ⌋
  enc-dec-dual End = refl
  enc-dec-dual (In benc enc) = cong₂ (λ x y → Chan #1 #0 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec-dual enc)
  enc-dec-dual (Out benc enc) = cong₂ (λ x y → Chan #0 #1 (Pair x (λ _ → y))) (enc-dec-base benc) (enc-dec enc)
  enc-dec-dual (Branch fenc) = cong (λ x → Chan #1 #0 (Pair _ x)) (extensionality λ i → enc-dec-dual (fenc i))
  enc-dec-dual (Choice fenc) = cong (λ x → Chan #0 #1 (Pair _ x)) (extensionality λ i → enc-dec (fenc i))

flip-chan-inv : (t : Type) → flip-chan (flip-chan t) ≡ t
flip-chan-inv (Pure _) = refl
flip-chan-inv (Chan _ _ _) = refl
flip-chan-inv (Pair _ _) = refl

flip-chan-swap : ∀{t s : Type} → t ≡ flip-chan s → flip-chan t ≡ s
flip-chan-swap eq rewrite eq = flip-chan-inv _

duality : (T : SessionType) → ⌊ dual T ⌋ ≡ flip-chan ⌊ T ⌋
duality End = refl
duality (In τ T) = cong (λ x → Chan #0 #1 (Pair _ (λ _ → x))) (flip-chan-swap (duality T))
duality (Out τ T) = cong (λ x → Chan #1 #0 (Pair _ (λ _ → x))) (duality T)
duality (Branch f) = cong (Chan #0 #1) (cong (Pair _) (extensionality λ i → flip-chan-swap (duality (f i))))
duality (Choice f) = cong (Chan #1 #0) (cong (Pair _) (extensionality λ i → duality (f i)))
