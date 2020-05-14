open import Size
open import Codata.Thunk
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Data.Fin
open import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Bool

module Pi_Types where

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

{- ##### πEncoding ##### -}

data Encoding : PreType → Set₁ where
  unit  : Encoding (Chan #0 #0 (Pure ⊤))
  input : {t : πType}{f : ⟦ t ⟧ → πType} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x))→ Encoding (Chan #1 #0 (Pair t f))
  output : {t : πType}{f : ⟦ t ⟧ → πType} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x))→ Encoding (Chan #0 #1 (Pair t f))
  pure : ∀ t → Encoding (Pure t)
