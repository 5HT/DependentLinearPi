open import Data.Bool
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Unit

module LTTypes where

{- ##### Types ##### -}

mutual
  SCtx : Set₁
  SCtx = List SessionType

  Type : Set₁
  Type = Set
  
  data SessionType : Set₁ where
    End : SessionType
    $_ : Type → SessionType
    _⊸_ _⨂_ _&_ _⨁_ : SessionType → SessionType → SessionType
    All_#_ Ex_#_ : (τ : Type) → (τ → SessionType) → SessionType

UpInterface : SessionType
UpInterface = All ℕ # λ n → All n > 0 # λ _ → Ex ℕ # λ y → Ex y > 0 # λ _ → End

TCtx : Set₁
TCtx = List Type

data _≋_ : SessionType → SessionType → Set₁ where
  refl : ∀ A → A ≋ A
  sym : ∀ {A B} → A ≋ B → B ≋ A
  in-in : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⊸ B) ≋ (A' ⊸ B')
  out-out : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⨂ B) ≋ (A' ⨂ B')
  all-all : ∀{τ f f'} → ((x : τ) → (f x) ≋ (f' x)) → (All τ # f) ≋ (All τ # f')
  ex-ex : ∀{τ f f'} → ((x : τ) → (f x) ≋ (f' x)) → (Ex τ # f) ≋ (Ex τ # f')
  plus-ex : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⨁ B) ≋ (Ex Bool # λ {false → A' ; true → B'})
  with-all : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A & B) ≋ (All Bool # λ {false → A' ; true → B'})
  impl-all : ∀{τ A A'} → A ≋ A' → (($ τ) ⊸ A) ≋ (All τ # λ _ → A')
  tens-ex : ∀{τ A A'} → A ≋ A' → (($ τ) ⨂ A) ≋ (Ex τ # λ _ → A')
