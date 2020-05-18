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
open import Data.Fin
open import Relation.Binary.PropositionalEquality

open import SessionTypes.Common

module SessionTypes.Labeled.Encoding where

{- ##### πEncoding ##### -}

mutual
  data BaseEncoding : Type → Set₁ where
    Pure : ∀{A} → BaseEncoding (Pure A)
    Chan : ∀{t} → Encoding t → BaseEncoding t

  data Encoding : Type → Set₁ where
    End : Encoding (Chan #0 #0 (Pure ⊤))
    In  : {t s : Type} → BaseEncoding t → Encoding s → Encoding (Chan #1 #0 (Pair t λ _ → s))
    Out : {t s : Type} → BaseEncoding t → Encoding s → Encoding (Chan #0 #1 (Pair t λ _ → s))
    Branch : ∀{n} → {f : Fin n → Type} → ((i : Fin n) → Encoding (f i)) →
             Encoding (Chan #1 #0 (Pair (Pure (Fin n)) f))
    Choice : ∀{n} → {f : Fin n → Type} → ((i : Fin n) → Encoding (f i)) →
             Encoding (Chan #0 #1 (Pair (Pure (Fin n)) f))

dual-enc : ∀{t} → Encoding t → Encoding (flip-chan t)
dual-enc End = End
dual-enc (In x e) = Out x e
dual-enc (Out x e) = In x e
dual-enc (Branch x) = Choice x
dual-enc (Choice x) = Branch x

-- {- ##### πType Duality as Predicate ##### -}

-- data _∥π_ : Type → πType → Set where
--   flip : ∀{m n t} → Chan m n t ∥π Chan n m t

-- -- Symmetric
-- ∥π-sym : ∀{T T'} → T ∥π T' → T' ∥π T
-- ∥π-sym flip = flip

-- -- Involutory
-- ∥π-inv : ∀{T T' T''} → T ∥π T' → T' ∥π T'' → T ≡ T''
-- ∥π-inv flip flip = refl


-- flip-mul : πType → πType
-- flip-mul (Pure A) = Pure A
-- flip-mul (Chan x x₁ p) = Chan x₁ x p
-- flip-mul (Pair p f) = Pair p f

-- -- Involutory
-- flip-inv : ∀ T → T ≡ flip-mul (flip-mul T)
-- flip-inv (Pure A) = refl
-- flip-inv (Chan x x₁ T) = refl
-- flip-inv (Pair T f) = refl

-- -- Symmetric
-- flip-sym : ∀ T T' → T ≡ flip-mul T' → flip-mul T ≡ T'
-- flip-sym .(Pure A) (Pure A) refl = refl
-- flip-sym .(Chan x₁ x T') (Chan x x₁ T') refl = sym (flip-inv (Chan x x₁ T'))
-- flip-sym .(Pair T' f) (Pair T' f) refl = refl

-- -- πEncoding holds after multiplicity flip

-- flip-π-enc : ∀ {t} → πEncoding t → πEncoding (flip-mul t)
-- flip-π-enc unit = unit
-- flip-π-enc (¿ch b e) = !ch b e
-- flip-π-enc (!ch b e) = ¿ch b e
-- flip-π-enc (&ch l) = ⊕ch l
-- flip-π-enc (⊕ch l) = &ch l
