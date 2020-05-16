open import Pi_Encoding
open import LTTypes
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.Unit

module Decode where

⌈_,_⌉ : ∀{t} → Encoding t → Bool → SessionType
⌈ unit , _ ⌉ = End
⌈ input unit x , false ⌉ = ⌈ unit , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input unit x , true ⌉ = ⌈ unit , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (input E x₁) x , false ⌉ = ⌈ input E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input (input E x₁) x , true ⌉ = ⌈ input E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (output E x₁) x , false ⌉ = ⌈ output E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ input (output E x₁) x , true ⌉ = ⌈ output E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ input (pure t) x , false ⌉ = All t # λ x₁ → ⌈ x x₁ , false ⌉
⌈ input (pure t) x , true ⌉ = Ex t # λ x₁ → ⌈ x x₁ , true ⌉
⌈ output unit x , false ⌉ = ⌈ unit , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output unit x , true ⌉ = ⌈ unit , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (input E x₁) x , false ⌉ = ⌈ input E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output (input E x₁) x , true ⌉ = ⌈ input E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (output E x₁) x , false ⌉ = ⌈ output E x₁ , false ⌉ ⨂ ⌈ x tt , true ⌉
⌈ output (output E x₁) x , true ⌉ = ⌈ output E x₁ , false ⌉ ⊸ ⌈ x tt , false ⌉
⌈ output (pure t) x , false ⌉ = Ex t # λ x₁ → ⌈ x x₁ , true ⌉
⌈ output (pure t) x , true ⌉ = All t # λ x₁ → ⌈ x x₁ , false ⌉
⌈ pure τ , _ ⌉ = $ τ
