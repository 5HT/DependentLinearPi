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

module SessionTypes.Labeled.Types where

mutual
  data BaseType : Set₁ where
    Pure    : Set → BaseType
    Session : SessionType → BaseType

  data SessionType : Set₁ where
    End : SessionType
    In Out : BaseType → SessionType → SessionType
    Branch Choice : ∀{n} → (f : Fin n → SessionType) → SessionType

{- ##### Duality ##### -}

dual : SessionType → SessionType
dual End = End
dual (In τ T) = Out τ (dual T)
dual (Out τ T) = In τ (dual T)
dual (Branch f) = Choice λ i → dual (f i)
dual (Choice f) = Branch λ i → dual (f i)
