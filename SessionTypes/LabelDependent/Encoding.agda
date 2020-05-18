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
open import Data.Bool
open import Data.Unit

open import SessionTypes.Common

module SessionTypes.LabelDependent.Encoding where

{- ##### πEncoding ##### -}

data Encoding : Type → Set₁ where
  unit  : Encoding (Chan #0 #0 (Pure ⊤))
  in-b  : {f : Bool → Type} → ((b : Bool) → Encoding (f b)) → Encoding (Chan #1 #0 (Pair (Pure Bool) f))
  out-b : {f : Bool → Type} → ((b : Bool) → Encoding (f b)) → Encoding (Chan #0 #1 (Pair (Pure Bool) f))
  in-s  : {t t' : Type} → Encoding t → Encoding t' → Encoding (Chan #1 #0 (Pair t λ _ → t'))
  out-s : {t t' : Type} → Encoding t → Encoding t' → Encoding (Chan #0 #1 (Pair t λ _ → t'))

dual-enc : ∀{t : Type} → Encoding t → Encoding (flip-chan t)
dual-enc unit = unit
dual-enc (in-b enc) = out-b enc
dual-enc (out-b enc) = in-b enc
dual-enc (in-s enc1 enc2) = out-s enc1 enc2
dual-enc (out-s enc1 enc2) = in-s enc1 enc2
