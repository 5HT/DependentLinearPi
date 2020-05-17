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
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common

module SessionTypes.LinearLogic.Encoding where

{- ##### πEncoding ##### -}

data Encoding : Type → Set₁ where
  unit   : Encoding (Chan #0 #0 (Pure ⊤))
  input  : {t : Type}{f : ⟦ t ⟧ → Type} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x)) → Encoding (Chan #1 #0 (Pair t f))
  output : {t : Type}{f : ⟦ t ⟧ → Type} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x)) → Encoding (Chan #0 #1 (Pair t f))
  pure   : ∀ t → Encoding (Pure t)
