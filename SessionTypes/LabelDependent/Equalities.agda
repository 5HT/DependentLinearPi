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
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common
open import SessionTypes.LabelDependent.Types
open import SessionTypes.LabelDependent.Encode
open import SessionTypes.LabelDependent.Encoding

module SessionTypes.LabelDependent.Equalities where

example1 : SessionType -> SessionType -> SessionType
example1 S T = ¿ Boolean , (case 0 of (¿ (Session S) , T ) , (¿ (Session S) , T))

example2 : SessionType -> SessionType -> SessionType
example2 S T = ¿ Boolean , (¿ (Session S) , (case 0 of T , T))

mutual
  shift-t : MessageType -> MessageType
  shift-t (Session T) = Session (shift-st T)
  shift-t Boolean = Boolean

  shift-st : SessionType -> SessionType
  shift-st End = End
  shift-st (case x of T , S) = case (suc x) of shift-st T , shift-st S
  shift-st (! t , T) = ! shift-t t , shift-st T
  shift-st (¿ t , T) = ¿ shift-t t , shift-st T

weaken-var : ∀{s Γ n} -> WFV n Γ Boolean -> WFV (suc n) (s ∷ Γ) Boolean
weaken-var here = next here
weaken-var (next x) = next (weaken-var x)

weaken : ∀{Γ T} -> WFS Γ T -> WFS (Boolean ∷ Γ) (shift-st T)
weaken wf-end = wf-end
weaken (wf-case x T S) = wf-case (weaken-var x) (weaken T) (weaken S)
weaken (wf-in-s S T) = wf-in-s (weaken S) (weaken T)
weaken (wf-out-s S T) = wf-out-s (weaken S) (weaken T)
weaken (wf-in-b T) = wf-in-b (weaken T)
weaken (wf-out-b T) = wf-out-b (weaken T)

example1-wf : ∀{S T} -> WFS [] S -> WFS [] T -> WFS [] (example1 (shift-st S) (shift-st T))
example1-wf S T = wf-in-b (wf-case here (wf-in-s (weaken S) (weaken T)) (wf-in-s (weaken S) (weaken T)))

example2-wf : ∀{S T} -> WFS [] S -> WFS [] T -> WFS [] (example2 (shift-st S) (shift-st T))
example2-wf S T = wf-in-b (wf-in-s (weaken S) (wf-case here (weaken T) (weaken T)))

test-eq : ∀{S T} -> (WS : WFS [] S) -> (WT : WFS [] T) -> (⌊ [] , example1-wf WS WT , false ⌋) ≡ (⌊ [] , example2-wf WS WT , false ⌋)
test-eq S T = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))
