open import Pi_Types as PI
open import Data.Unit
open import Data.List
open import Data.Bool
open import LTTypes
open import Data.Product

module Encode where

mutual
  ⌊_,_⌋ : SessionType → Bool → πType
  ⌊ End , _ ⌋ = Chan #0 #0 (Pure ⊤)
  ⌊ $ x , _ ⌋ = Pure x
  ⌊ A ⊸ B , false ⌋ = Chan #1 #0 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , false ⌋)
  ⌊ A ⊸ B , true ⌋ =  Chan #0 #1 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , false ⌋)
  ⌊ A ⨂ B , false ⌋ = Chan #0 #1 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , true ⌋)
  ⌊ A ⨂ B , true ⌋ = Chan #1 #0 (Pair ⌊ A , false ⌋ λ _ → ⌊ B , true ⌋)
  ⌊ A & B , false ⌋ = Chan #1 #0 (Pair (Pure Bool) λ {true → ⌊ B , false ⌋ ; false → ⌊ A , false ⌋})
  ⌊ A & B , true ⌋ = Chan #0 #1 (Pair (Pure Bool) λ {true → ⌊ B , false ⌋ ; false → ⌊ A , false ⌋})
  ⌊ A ⨁ B , false ⌋ = Chan #0 #1 (Pair (Pure Bool) λ {true → ⌊ B , true ⌋ ; false → ⌊ A , true ⌋})
  ⌊ A ⨁ B , true ⌋ = Chan #1 #0 (Pair (Pure Bool) λ {true → ⌊ B , true ⌋ ; false → ⌊ A , true ⌋})
  ⌊ All τ # f , false ⌋ = Chan #0 #1 (Pair (Pure τ) λ x → ⌊ f x , true ⌋)
  ⌊ All τ # f , true ⌋ = Chan #1 #0 (Pair (Pure τ) λ x → ⌊ f x , true ⌋)
  ⌊ Ex τ # f , false ⌋ = Chan #1 #0 (Pair (Pure τ) λ x → ⌊ f x , false ⌋)
  ⌊ Ex τ # f , true ⌋ = Chan #0 #1 (Pair (Pure τ) λ x → ⌊ f x , false ⌋)



enc-Enc : ∀ S b → Encoding ⌊ S , b ⌋ 
enc-Enc End _ = unit
enc-Enc ($ x) _ = pure x
enc-Enc (S ⊸ S₁) false = input (enc-Enc S false) λ _ → enc-Enc S₁ false
enc-Enc (S ⊸ S₁) true = output (enc-Enc S false) λ _ → enc-Enc S₁ false
enc-Enc (S ⨂ S₁) false = output (enc-Enc S false) λ _ → enc-Enc S₁ true
enc-Enc (S ⨂ S₁) true = input (enc-Enc S false) λ _ → enc-Enc S₁ true
enc-Enc (S & S₁) false = input (pure Bool) λ {false → enc-Enc S false ; true → enc-Enc S₁ false}
enc-Enc (S & S₁) true = output (pure Bool) λ {false → enc-Enc S false ; true → enc-Enc S₁ false}
enc-Enc (S ⨁ S₁) false = output (pure Bool) λ {false → enc-Enc S true ; true → enc-Enc S₁ true}
enc-Enc (S ⨁ S₁) true = input (pure Bool) λ {false → enc-Enc S true ; true → enc-Enc S₁ true}
enc-Enc (All τ # x) false = output (pure τ) λ x₁ → enc-Enc (x x₁) true
enc-Enc (All τ # x) true = input (pure τ) λ x₁ → enc-Enc (x x₁) true
enc-Enc (Ex τ # x) false = input (pure τ) λ x₁ → enc-Enc (x x₁) false
enc-Enc (Ex τ # x) true = output (pure τ) λ x₁ → enc-Enc (x x₁) false
