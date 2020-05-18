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

open import Data.Nat
open import Data.Product
open import Data.List
open import Data.Bool

open import SessionTypes.LabelDependent.Types
open import SessionTypes.LabelDependent.Encoding

module SessionTypes.LabelDependent.Decode where

mutual
  ⌈_⌉ : ∀{t} → Encoding t → SessionType
  ⌈ unit ⌉ = End
  ⌈ in-b f ⌉ = ¿ Boolean , case zero of ⌈ f false ⌉ , ⌈ f true ⌉
  ⌈ out-b f ⌉ = ! Boolean , case zero of ⌈ f false ⌉-dual , ⌈ f true ⌉-dual
  ⌈ in-s enc1 enc2 ⌉ = ¿ Session ⌈ enc1 ⌉ , ⌈ enc2 ⌉
  ⌈ out-s enc1 enc2 ⌉ = ! Session ⌈ enc1 ⌉ , ⌈ enc2 ⌉-dual

  ⌈_⌉-dual : ∀{t} → Encoding t → SessionType
  ⌈ unit ⌉-dual = End
  ⌈ in-b f ⌉-dual = ! Boolean , case zero of ⌈ f false ⌉-dual , ⌈ f true ⌉-dual
  ⌈ out-b f ⌉-dual = ¿ Boolean , case zero of ⌈ f false ⌉ , ⌈ f true ⌉
  ⌈ in-s enc1 enc2 ⌉-dual = ! Session ⌈ enc1 ⌉ , ⌈ enc2 ⌉-dual
  ⌈ out-s enc1 enc2 ⌉-dual = ¿ Session ⌈ enc1 ⌉ , ⌈ enc2 ⌉

mutual
  dec-WFS : ∀{t Γ} -> (enc : Encoding t) -> WFS Γ ⌈ enc ⌉
  dec-WFS unit = wf-end
  dec-WFS (in-b x) = wf-in-b (wf-case here (dec-WFS (x false)) (dec-WFS (x true)))
  dec-WFS (out-b x) = wf-out-b (wf-case here (dec-WFS-dual (x false)) (dec-WFS-dual (x true)))
  dec-WFS (in-s T₁ T₂) = wf-in-s (dec-WFS T₁) (dec-WFS T₂)
  dec-WFS (out-s T₁ T₂) = wf-out-s (dec-WFS T₁) (dec-WFS-dual T₂)

  dec-WFS-dual : ∀{t Γ} -> (enc : Encoding t) -> WFS Γ ⌈ enc ⌉-dual
  dec-WFS-dual unit = wf-end
  dec-WFS-dual (in-b x) = wf-out-b (wf-case here  (dec-WFS-dual (x false)) (dec-WFS-dual (x true)))
  dec-WFS-dual (out-b x) = wf-in-b (wf-case here  (dec-WFS (x false)) (dec-WFS (x true)))
  dec-WFS-dual (in-s T₁ T₂) = wf-out-s (dec-WFS T₁) (dec-WFS-dual T₂)
  dec-WFS-dual (out-s T₁ T₂) = wf-in-s (dec-WFS T₁) (dec-WFS T₂)
