open import Size
open import Codata.Thunk
open import Data.Unit
open import Data.Product
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
open import Data.Fin

open import Pi_Types

module Session_Types where


{- TYPE -}
mutual
  data BaseType : Set₁ where
    Pi : Set → BaseType
    Session : SessionType → BaseType

  data SessionType : Set₁ where
    ∅ : SessionType
    ¿_,_ !_,_ : BaseType → SessionType → SessionType
    & ⊕ : ∀{n} → (f : Fin n → SessionType) → SessionType


{- ##### Duality ##### -}

data _∥ₛ_ : SessionType → SessionType → Set₁ where
  ∅∥ₛ∅ : ∅ ∥ₛ ∅
  ¿∥ₛ! : ∀{T S S'} → S ∥ₛ S' → (¿ T , S) ∥ₛ (! T , S')
  !∥ₛ¿ : ∀{T S S'} → S ∥ₛ S' → (! T , S) ∥ₛ (¿ T , S')
  &∥ₛ⊕ : ∀{n}{f f' : Fin n → SessionType} → (∀{i} → f i ∥ₛ f' i) → & f ∥ₛ ⊕ f'
  ⊕∥ₛ& : ∀{n}{f f' : Fin n → SessionType} → (∀{i} → f i ∥ₛ f' i) → ⊕ f ∥ₛ & f'


⊥ₛ : SessionType → SessionType
⊥ₛ ∅ = ∅
⊥ₛ (¿ x , s) = ! x , ⊥ₛ s
⊥ₛ (! x , s) = ¿ x , ⊥ₛ s
⊥ₛ (& x) = ⊕ λ x₁ → ⊥ₛ (x x₁)
⊥ₛ (⊕ x) = & λ x₁ → ⊥ₛ (x x₁)
