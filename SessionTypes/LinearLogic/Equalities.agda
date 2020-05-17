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

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common
open import SessionTypes.LinearLogic.Types
open import SessionTypes.LinearLogic.Encoding
open import SessionTypes.LinearLogic.Encode

module SessionTypes.LinearLogic.Equalities where

test1 : ∀{T : SessionType} -> ⌊ (($ Bool) ⊸ T) , false ⌋ ≡ ⌊ T & T , false ⌋
test1 = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))

test2 : ∀{T : SessionType} -> ⌊ T & T , false ⌋ ≡ ⌊ All Bool # (λ _ -> T) , false ⌋
test2 = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))
