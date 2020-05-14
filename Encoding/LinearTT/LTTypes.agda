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
  with-ex : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A & B) ≋ (Ex Bool # λ {false → A' ; true → B'})
  plus-all : ∀{A A' B B'} → A ≋ A' → B ≋ B' → (A ⨁ B) ≋ (All Bool # λ {false → A' ; true → B'})
  impl-ex : ∀{τ A A'} → A ≋ A' → (($ τ) ⊸ A) ≋ (Ex τ # λ _ → A')
  tens-all : ∀{τ A A'} → A ≋ A' → (($ τ) ⨂ A) ≋ (All τ # λ _ → A')

{-
{-
data TCtx : Set₁ where
  [] : TCtx
  _∷_ : ∀{τ : Type} → (x : ⟦ τ ⟧) → TCtx → TCtx
-}

mutual
  data _,_⊢_ : TCtx → SCtx → SessionType → Set₁ where
    ⊸R : ∀{Ψ Γ A B} →
         Ψ , (A ∷ Γ) ⊢ B →
         ----------------------
         Ψ , Γ ⊢ (A ⊸ B)
    ⊸L : ∀{Ψ Ψ' Γ Γ' A B C} →
         Ψ , Γ ⊢ A → Ψ' , (B ∷ Γ') ⊢ C →
         ----------------------
         {!!} , (A ∷ Γ ++ Γ') ⊢ C
    1R : [] , [] ⊢ End
    1L : ∀{Ψ Γ C} →
         Ψ , Γ ⊢ C →
         --------------
         Ψ , (End ∷ Γ) ⊢ C
    ⨂R : ∀{Ψ Ψ' Γ Γ' A B} →
         Ψ , Γ ⊢ A → Ψ' , Γ' ⊢ B →
         -------------------------
         {!!} , (Γ ++ Γ') ⊢ (A ⨂ B)
    ⨂L : ∀{Ψ Γ A B C} →
         Ψ , (A ∷ B ∷ Γ) ⊢ C →
         ------------------
         Ψ , (A ⨂ B ∷ Γ) ⊢ C
    $R : ∀{Ψ τ} → Ψ , [] ⊢ ($ τ)
    $L : ∀{Ψ Γ C τ} →
         (τ ∷ Ψ) , Γ ⊢ C →
         -------------------
         Ψ , $ τ ∷ Γ ⊢ C
    &R : ∀{Ψ Γ A B} →
         Ψ , Γ ⊢ A → Ψ , Γ ⊢ B →
         --------------------------
         Ψ , Γ ⊢ (A & B)
    &L₁ : ∀{Ψ Γ A B C} →
          Ψ , A ∷ Γ ⊢ C →
          ----------------------
          Ψ , A & B ∷ Γ ⊢ C
    &L₂ : ∀{Ψ Γ A B C} →
          Ψ , B ∷ Γ ⊢ C →
          ----------------------
          Ψ , A & B ∷ Γ ⊢ C
    ⨁R₁ : ∀{Ψ Γ A B} →
          Ψ , Γ ⊢ A →
          ----------------------
          Ψ , Γ ⊢ (A ⨁ B)
    ⨁R₂ : ∀{Ψ Γ A B} →
          Ψ , Γ ⊢ B →
          ----------------------
          Ψ , Γ ⊢ (A ⨁ B)
    ⨁L₂ : ∀{Ψ Γ A B C} →
          Ψ , A ∷ Γ ⊢ C → Ψ , B ∷ Γ ⊢ C →
          ----------------------
          Ψ , A ⨁ B ∷ Γ ⊢ C
-}
