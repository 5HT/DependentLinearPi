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

open import Size using (Size; ∞)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_)
open import Codata.Thunk

module Language where

{- Multiplicity -}

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

{- Type -}

mutual
  data PreType : Size → Set₁ where
    Pure : ∀{i} → Set → PreType i
    Chan : ∀{i} → Multiplicity → Multiplicity → Thunk PreType i → PreType i
    Pair : ∀{i} → (t : PreType i) → (f : ⟦ t ⟧ → PreType i) → PreType i

  {- Interpretation : datatype → type -}
  ⟦_⟧ : ∀{i} → PreType i → Set
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = ⊤
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x → ⟦ f x ⟧

UnfoldedType : Set₁
UnfoldedType = ∀{i} → PreType i

FoldedType : Set₁
FoldedType = ∀{i} → Thunk PreType i

fold : UnfoldedType → FoldedType
fold t = λ where .force → t

unfold : FoldedType → UnfoldedType
unfold t = t .force

Type : Set₁
Type = PreType ∞

{- Context -}

infixr 5 _::_
infixr 5 _#_::_

data Context : Set₁ where
  []   : Context
  _#_::_ : (t : Type) → ⟦ t ⟧ → Context → Context

{- Linear -}

data Linear : Type → Set where
  pair : ∀{t s} → Linear (Pair t s)

{- Null -}

data TNull : Type → Set₁ where
  pure : ∀{A} → TNull (Pure A)
  chan : ∀{t} → TNull (Chan #0 #0 t)

data CNull : Context → Set₁ where
  []   : CNull []
  _::_ : ∀{t p Γ} → TNull t → CNull Γ → CNull (t # p :: Γ)

{- Scale -}

data MScale : Multiplicity → Multiplicity → Set where
  0·0 : MScale #0 #0
  1·ω : MScale #1 #ω
  ω·ω : MScale #ω #ω

data TScale : (t s : Type) → ⟦ t ⟧ → ⟦ s ⟧ → Set₁ where
  pure : ∀{A p} → TScale (Pure A) (Pure A) p p
  chan : ∀{σ σ' ρ ρ' t} → MScale σ σ' → MScale ρ ρ' → TScale (Chan σ ρ t) (Chan σ' ρ' t) _ _

data CScale : Context → Context → Set₁ where
  []   : CScale [] []
  _::_ : ∀{Γ Δ t s p q} → TScale t s p q → CScale Γ Δ → CScale (t # p :: Γ) (s # q :: Δ)

{- Split -}

data MSplit : Multiplicity → Multiplicity → Multiplicity → Set where
  0+0 : MSplit #0 #0 #0
  0+1 : MSplit #1 #0 #1
  0+ω : MSplit #ω #0 #ω
  1+0 : MSplit #1 #1 #0
  1+1 : MSplit #ω #1 #1
  1+ω : MSplit #ω #1 #ω
  ω+0 : MSplit #ω #ω #0
  ω+1 : MSplit #ω #ω #1
  ω+ω : MSplit #ω #ω #ω

data TSplit : (t t1 t2 : Type) → ⟦ t ⟧ → ⟦ t1 ⟧ → ⟦ t2 ⟧ → Set₁ where
  pure  : ∀{A p} → TSplit (Pure A) (Pure A) (Pure A) p p p
  left  : ∀{t p} → Linear t → TSplit t t (Pure ⊤) p p tt
  right : ∀{t p} → Linear t → TSplit t (Pure ⊤) t p tt p
  chan  : ∀{σ σ1 σ2 ρ ρ1 ρ2 t} → MSplit σ σ1 σ2 → MSplit ρ ρ1 ρ2 → TSplit (Chan σ ρ t) (Chan σ1 ρ1 t) (Chan σ2 ρ2 t) tt tt tt

data CSplit : Context → Context → Context → Set₁ where
  []   : CSplit [] [] []
  _::_ : ∀{t t1 t2 Γ Γ1 Γ2 p p1 p2} → TSplit t t1 t2 p p1 p2 → CSplit Γ Γ1 Γ2 → CSplit (t # p :: Γ) (t1 # p1 :: Γ1) (t2 # p2 :: Γ2)

{- Term -}

data Name : ℕ → Context → (t : Type) → ⟦ t ⟧ → Set₁ where
  here : ∀{Γ t p} → CNull Γ → Name zero (t # p :: Γ) t p
  next : ∀{k Γ t s p q} → TNull s → Name k Γ t p →
         Name (suc k) (s # q :: Γ) t p

data Term : Context → (t : Type) → ⟦ t ⟧ → Set₁ where
  name : ∀{k Γ t p} → Name k Γ t p → Term Γ t p
  pure : ∀{Γ A} → CNull Γ → (p : A) → Term Γ (Pure A) p
  pair : ∀{Γ Γ1 Γ2 t f p q} → CSplit Γ Γ1 Γ2 → Term Γ1 t p →
         Term Γ2 (f p) q → Term Γ (Pair t f) (p , q)

{- Process -}

data Process : Context → Set₁ where
  Idle : ∀{Γ} → CNull Γ → Process Γ
  Send : ∀{Γ Γ1 Γ2 t p} → CSplit Γ Γ1 Γ2 → Term Γ1 (Chan #0 #1 t) _ →
         Term Γ2 (t .force) p → Process Γ
  Recv : ∀{Γ Γ1 Γ2 t} → CSplit Γ Γ1 Γ2 → Term Γ1 (Chan #1 #0 t) _ →
         ((x : ⟦ t .force ⟧) → Process (t .force # x :: Γ2)) →
         Process Γ
  Par  : ∀{Γ Γ1 Γ2} → CSplit Γ Γ1 Γ2 → Process Γ1 → Process Γ2 →
         Process Γ
  New  : ∀{Γ σ ρ t} → Process (Chan σ ρ t # _ :: Γ) → Process Γ
  Rep  : ∀{Γ Δ} → CScale Γ Δ → Process Γ → Process Δ
  Let  : ∀{Γ Γ1 Γ2 t f p q} → CSplit Γ Γ1 Γ2 →
         Term Γ1 (Pair t f) (p , q) →
         Process (t # p :: f p # q :: Γ2) → Process Γ
