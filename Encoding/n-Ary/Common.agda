open import Axiom.Extensionality.Propositional as Axiom
open import Level as Lv
open import Data.Unit
open import Data.Product

module Common where

postulate
  extensionality : Axiom.Extensionality Lv.zero (Lv.suc Lv.zero)

{- MULTIPLICITY -}

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

{- TYPE -}

mutual
  data PreType : Set₁ where
    Pure : (A : Set) -> PreType
    Chan : Multiplicity → Multiplicity → PreType → PreType
    Pair : ∀(t : PreType) -> (f : ⟦ t ⟧ → PreType) → PreType

  {- Interpretation : datatype → type -}
  ⟦_⟧ : PreType → Set
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = ⊤
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x -> ⟦ f x ⟧

πType : Set₁
πType = PreType
