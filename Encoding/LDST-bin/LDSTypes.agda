open import Data.Bool
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Unit

module LDSTypes where

{- ##### Types ##### -}

mutual
  Ctx : Set
  Ctx = List Type

  data Type : Set where
    Session : SessionType → Type
    Boolean : Type

  data SessionType : Set where
    End : SessionType
    case_of_,_ : ℕ → SessionType → SessionType → SessionType
    !_,_ ¿_,_ : Type → SessionType → SessionType

-- Interpretation
⟦_⟧ : Type → Set
⟦ Session _ ⟧ = ⊤
⟦ Boolean ⟧ = Bool

{- ##### Formation Rules ##### -}

mutual
  data WFV : ℕ → Ctx → Type → Set where
    here : ∀{Γ t} → WFV zero (t ∷ Γ) t
    next : ∀{Γ s t n} → WFV n Γ t → WFV (suc n) (s ∷ Γ) t

  data WFC : Ctx → Set where
    empty : WFC []
    cons : ∀{Γ t} → WFT Γ t → WFC (t ∷ Γ)

  data WFT : Ctx → Type → Set where
    wf-s : ∀{Γ S} → WFS Γ S → WFT Γ (Session S)
    wf-b : ∀{Γ} → WFT Γ Boolean

  data WFS : Ctx → SessionType → Set where
    wf-end   : ∀{Γ} → WFS Γ End
    wf-case  : ∀{Γ n S T} → WFV n Γ Boolean → WFS Γ S → WFS Γ T → WFS Γ (case n of S , T)
    wf-in-s  : ∀{Γ S T} -> WFS Γ S -> WFS Γ T -> WFS Γ (¿ Session S , T)
    wf-out-s : ∀{Γ S T} -> WFS Γ S -> WFS Γ T -> WFS Γ (! Session S , T)
    wf-in-b  : ∀{Γ T} -> WFS (Boolean ∷ Γ) T -> WFS Γ (¿ Boolean , T)
    wf-out-b : ∀{Γ T} -> WFS (Boolean ∷ Γ) T -> WFS Γ (! Boolean , T)

{- ##### Environment for Encoding ##### -}

data Env : Ctx → Set where
  []   : Env []
  _::_ : ∀{Γ} → Bool → Env Γ → Env (Boolean ∷ Γ)

env-get : ∀{Γ n} → (E : Env Γ) → WFV n Γ Boolean → Bool
env-get (x :: E) here = x
env-get (_ :: E) (next V) = env-get E V

data VarIs : ∀{Γ n} -> Env Γ -> WFV n Γ Boolean -> Bool -> Set where
  here : ∀{Γ}{E : Env Γ}{b} -> VarIs (b :: E) here b
  next :
    ∀{Γ n}{E : Env Γ}{b b' : Bool}{V : WFV n Γ Boolean} ->
    VarIs E V b ->
    VarIs (b' :: E) (next V) b

env-lookup : ∀{Γ n} → (E : Env Γ) → (x : WFV n Γ Boolean) → Σ[ b ∈ Bool ] VarIs E x b
env-lookup (_ :: E) here = _ , here
env-lookup (_ :: E) (next x) =
  let rec = (proj₂ (env-lookup E x)) in
  _ , next rec 

data Bisimilar : ∀{Γ T S} -> Env Γ -> WFS Γ T -> WFS Γ S -> Set where
  sim-end    : ∀{Γ}{E : Env Γ} -> Bisimilar E wf-end wf-end
  sim-case-lf :
    ∀{Γ T1 T2 T n}{E : Env Γ}{W1 : WFS Γ T1}{W2 : WFS Γ T2}{W : WFS Γ T}{V : WFV n Γ Boolean} ->
    VarIs E V false ->
    Bisimilar E W1 W ->
    Bisimilar E (wf-case V W1 W2) W
  sim-case-lt :
    ∀{Γ T1 T2 T n}{E : Env Γ}{W1 : WFS Γ T1}{W2 : WFS Γ T2}{W : WFS Γ T}{V : WFV n Γ Boolean} ->
    VarIs E V true ->
    Bisimilar E W2 W ->
    Bisimilar E (wf-case V W1 W2) W
  sim-case-rf :
    ∀{Γ T1 T2 T n}{E : Env Γ}{W1 : WFS Γ T1}{W2 : WFS Γ T2}{W : WFS Γ T}{V : WFV n Γ Boolean} ->
    VarIs E V false ->
    Bisimilar E W W1 ->
    Bisimilar E W (wf-case V W1 W2)
  sim-case-rt :
    ∀{Γ T1 T2 T n}{E : Env Γ}{W1 : WFS Γ T1}{W2 : WFS Γ T2}{W : WFS Γ T}{V : WFV n Γ Boolean} ->
    VarIs E V true ->
    Bisimilar E W W2 ->
    Bisimilar E W (wf-case V W1 W2)
  sim-in-s :
    ∀{Γ T1 T2 S1 S2}{E : Env Γ}{W1 : WFS Γ T1}{W1' : WFS Γ S1}{W2 : WFS Γ T2}{W2' : WFS Γ S2} ->
    Bisimilar E W1 W2 →
    Bisimilar E W1' W2' →
    Bisimilar E (wf-in-s W1 W1') (wf-in-s W2 W2')
  sim-out-s :
    ∀{Γ T1 T2 S1 S2}{E : Env Γ}{W1 : WFS Γ T1}{W1' : WFS Γ S1}{W2 : WFS Γ T2}{W2' : WFS Γ S2} ->
    Bisimilar E W1 W2 →
    Bisimilar E W1' W2' →
    Bisimilar E (wf-out-s W1 W1') (wf-out-s W2 W2')
  sim-in-b :
    ∀{Γ T1 T2}{E : Env Γ}{W1 : WFS (Boolean ∷ Γ) T1}{W2 : WFS (Boolean ∷ Γ) T2} ->
    Bisimilar (false :: E) W1 W2 ->
    Bisimilar (true :: E) W1 W2 ->
    Bisimilar E (wf-in-b W1) (wf-in-b W2)
  sim-out-b :
    ∀{Γ T1 T2}{E : Env Γ}{W1 : WFS (Boolean ∷ Γ) T1}{W2 : WFS (Boolean ∷ Γ) T2} ->
    Bisimilar (false :: E) W1 W2 ->
    Bisimilar (true :: E) W1 W2 ->
    Bisimilar E (wf-out-b W1) (wf-out-b W2)
