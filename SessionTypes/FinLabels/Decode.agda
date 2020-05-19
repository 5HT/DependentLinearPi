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

open import Data.Fin

open import SessionTypes.Common
open import SessionTypes.FinLabels.Encoding
open import SessionTypes.FinLabels.Types

module SessionTypes.FinLabels.Decode where

mutual
  ⌈_⌉-base : {t : Type} → BaseEncoding t → BaseType
  ⌈ Pure {A} ⌉-base = Pure A
  ⌈ Chan t ⌉-base = Session ⌈ t ⌉

  ⌈_⌉ : {t : Type} → Encoding t → SessionType
  ⌈ End ⌉ = End
  ⌈ In benc enc ⌉ = In ⌈ benc ⌉-base ⌈ enc ⌉
  ⌈ Out benc enc ⌉ = Out ⌈ benc ⌉-base ⌈ enc ⌉-dual
  ⌈ Branch f ⌉ = Branch λ i → ⌈ f i ⌉
  ⌈ Choice f ⌉ = Choice λ i → ⌈ f i ⌉-dual

  ⌈_⌉-dual : {t : Type} → Encoding t → SessionType
  ⌈ End ⌉-dual = End
  ⌈ In benc enc ⌉-dual = Out ⌈ benc ⌉-base ⌈ enc ⌉-dual
  ⌈ Out benc enc ⌉-dual = In ⌈ benc ⌉-base ⌈ enc ⌉
  ⌈ Branch f ⌉-dual = Choice λ i → ⌈ f i ⌉-dual
  ⌈ Choice f ⌉-dual = Branch λ i → ⌈ f i ⌉
