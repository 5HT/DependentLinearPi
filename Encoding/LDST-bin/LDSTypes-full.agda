open import Data.Bool
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Fin

module LDSTypes where

data Kind : Set where
  lin un : Kind

mutual

{-
  data Ctx_HasKind_ : Ctx → Kind → Set where
    unrC : ∀{Γ} → {!!} → {!!}

  data Type {Γ : Ctx} : Kind → Set where
    Unit : ⊢ Γ ፤ un → Type un

  data SessionType : Ctx → Kind → Set where
    End : ∀{Γ} → ⊢ Γ ፤ un → SessionType Γ un
-}

  Ctx : Set₁
  Ctx = List Type
  
  data Value : Set where
    β : Bool → Value
    ₍₎ : Value
    lam_,_↠_ : Kind → {!!} → {!!} → Value
    ⟨_==_⟩ : {!!} → (Σ[ V ∈ Value ] Value) → Value
    send : Value → Value

  data Type : Set₁ where
    Session : SessionType → Type
    Unit : Type
    Ł : Set → Type --Label Set
    _==_ : Value → Value → Type -- Subst with ≡?
    case_of_,_ : Value → Type → Type → Type
    Π_,_,_ : Kind → Type → Type → Type
    Ε_,_ : Type → Type → Type 

  data SessionType : Set₁ where
    End : SessionType
    case_of_,_ : Value → SessionType → SessionType → SessionType
    !_,_ ¿_,_ : Type → SessionType → SessionType 

  {- ##### Unrestricted Projection, Conditional Extension ##### -}

  data _UnrProjOf_ : Ctx → Ctx → Set₁ where
    empty : [] UnrProjOf []
    cons : ∀{Γ Γ' t} → Γ' Ext Γ ◁ t → Γ' UnrProjOf (t ∷ Γ)

  data _Ext_◁_ : Ctx → Ctx → Type → Set₁ where
    lin-ext : ∀{Γ Γᵤ t} → Γᵤ UnrProjOf Γ → Γᵤ ⊢ₜ t ፤ lin → Γ Ext Γ ◁ t  
    unr-ext : ∀{Γ Γᵤ t} → Γᵤ UnrProjOf Γ → Γᵤ ⊢ₜ t ፤ un → (t ∷ Γ) Ext Γ ◁ t  

  {- ##### Formation Rules ##### -}

  -- Context Formation
  data ⊢_፤_ : Ctx → Kind → Set₁ where
   empty : ∀{m} → ⊢ [] ፤ m
   cons : ∀{Γ A m} → ⊢ Γ ፤ m → Γ ⊢ₜ A ፤ m → ⊢ A ∷ Γ ፤ m 

  -- Type Formation
  data _⊢ₜ_፤_ : Ctx → Type → Kind → Set₁ where
    --Session : ∀{Γ S m} → Γ ⊢ₛ S ፤ m → Γ ⊢ₜ Session S ፤ m
    Unit-F : ∀{Γ} → ⊢ Γ ፤ un → Γ ⊢ₜ Unit ፤ un
    Lab-F : ∀{Γ} → ⊢ Γ ፤ un → Γ ⊢ₜ Ł Bool ፤ un
    Lab-F' : ∀{Γ Γ' Γ'' V A B m} → Γ' Ext Γ ◁ (V == β true) → Γ'' Ext Γ ◁ (V == β false)
      → Γ' ⊢ₜ A ፤ m → Γ'' ⊢ₜ B ፤ m → {!!} → Γ ⊢ₜ case V of A , B ፤ m
    Pi-F : ∀{Γ Γ' A B m n} → Γ' Ext Γ ◁ A → Γ' ⊢ₜ B ፤ n → Γ ⊢ₜ Π m , A , B ፤ m
    Sigma-F : ∀{Γ Γ' A B m} → Γ' Ext Γ ◁ A → Γ' ⊢ₜ B ፤ m → Γ ⊢ₜ A ፤ m → Γ ⊢ₜ Ε A , B ፤ m
   
    
  -- SessionType Formation
  data _⊢ₛ_፤_ : Ctx → SessionType → Kind → Set₁ where
    End-F : ∀{Γ} → ⊢ Γ ፤ un → Γ ⊢ₛ End ፤ un
    Ssn-Out-F Ssn-In-F : ∀{Γ Γ' A S} → Γ' Ext Γ ◁ A → Γ' ⊢ₛ S ፤ lin → Γ ⊢ₛ ! A , S ፤ lin
    Ssn-Lab : ∀{Γ Γ' Γ'' V S' S'' m} → Γ' Ext Γ ◁ (V == β true) → Γ'' Ext Γ ◁ (V == β false)
      → Γ' ⊢ₛ S' ፤ m → Γ'' ⊢ₛ S'' ፤ m → {!!} → Γ ⊢ₛ case V of S' , S'' ፤ m
