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

open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Product

open import SessionTypes.Common
open import SessionTypes.LabelDependent.Encoding
open import SessionTypes.LabelDependent.Types

module SessionTypes.LabelDependent.Encode where

⌊_,_⌋ : ∀{Γ T} → Env Γ → WFS Γ T → Type
⌊ _ , wf-end ⌋ = Chan #0 #0 (Pure ⊤)
⌊ E , wf-case x T S ⌋ with env-lookup E x
... | false , _ = ⌊ E , T ⌋
... | true , _  = ⌊ E , S ⌋
⌊ E , wf-in-s S T ⌋ = Chan #1 #0 (Pair ⌊ E , S ⌋ λ _ → ⌊ E , T ⌋)
⌊ E , wf-out-s S T ⌋ = Chan #0 #1 (Pair ⌊ E , S ⌋ λ _ → flip-chan ⌊ E , T ⌋)
⌊ E , wf-in-b T ⌋ = Chan #1 #0 (Pair (Pure Bool) λ x → ⌊ x :: E , T ⌋)
⌊ E , wf-out-b T ⌋ = Chan #0 #1 (Pair (Pure Bool) λ x → flip-chan ⌊ x :: E , T ⌋)

image : ∀{Γ T} → (E : Env Γ) → (W : WFS Γ T) → Encoding ⌊ E , W ⌋
image E wf-end = unit
image E (wf-case x W1 W2) with env-lookup E x
... | false , _ = image E W1
... | true , _  = image E W2
image E (wf-in-s W1 W2) = in-s (image E W1) (image E W2)
image E (wf-out-s W1 W2) = out-s (image E W1) (dual-enc (image E W2))
image E (wf-in-b W) = in-b λ x → image (x :: E) W
image E (wf-out-b W) = out-b λ x → dual-enc (image (x :: E) W)
