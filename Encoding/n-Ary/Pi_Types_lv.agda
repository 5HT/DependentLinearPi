open import Size
open import Codata.Thunk
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Level

module Pi_Types_lv where

{- MULTIPLICITY -}

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

{- TYPE -}
{-
mutual
  data PreType {l} : Size → Set₁ where
    Pure : ∀{i} → (A : Set) -> PreType i
    Chan : ∀{i} → Multiplicity → Multiplicity → Thunk PreType i → PreType i
    Pair : ∀{i} → (t : PreType i) -> (f : ⟦ t ⟧ → PreType i) → PreType i

  {- Interpretation : datatype → type -}
  ⟦_⟧ : ∀{i} → PreType i → Set
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = ⊤
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x -> ⟦ f x ⟧

UnfoldedType : Set₁
UnfoldedType = ∀{i} -> PreType i

FoldedType : Set₁
FoldedType = ∀{i} -> Thunk PreType i

fold : UnfoldedType -> FoldedType
fold t = λ where .force -> t

unfold : FoldedType -> UnfoldedType
unfold t = t .force

PiType : Set₁
PiType = PreType ∞
-}

data OK {l} : Set l where
  tt : OK
  
mutual
  data πType {l} : Set (suc l) where
    Pure : (A : Set l) -> πType
    Chan : Multiplicity → Multiplicity → πType {l} → πType
    Pair : ∀(t : πType {l}) -> (f : ⟦ t ⟧ → πType {l}) → πType

  {- Interpretation : datatype → type -}
  ⟦_⟧ : {l : Level} → πType {l} → Set l
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = OK
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x -> ⟦ f x ⟧


data πEncoding {l} : πType {l} → Set where
  unit : πEncoding (Chan #0 #0 (Pure OK))
  ¿ch : {t : πType} → πEncoding (Chan #1 #0 t)
  !ch : {t : πType} → πEncoding (Chan #0 #1 t)


⊥ₜ : ∀{l} → Σ[ t ∈ πType {l} ] πEncoding t → Σ[ t' ∈ πType {l} ] πEncoding t'
⊥ₜ (.(Chan #0 #0 (Pure OK)) , unit) = Chan #0 #0 (Pure OK) , unit
⊥ₜ ((Chan #1 #0 t) , ¿ch) = Chan #0 #1 t , !ch
⊥ₜ ((Chan #0 #1 t) , !ch) = Chan #1 #0 t , ¿ch


data _∥π_ {l} : πType {l} → πType {l} → Set₁ where
  ch : ∀{m n t} → Chan m n t ∥π Chan n m t


ex : πType
ex = Chan #0 #1 (Pair (Pure πType) λ x → Pair (Pure πType) λ x₁ → Pure (x ∥π x₁))

ex2 : πType
ex2 = Pair (Pure Set) λ A → Chan #1 #0 {!Pure A!}

data _∥π-enc_ {l} : (Σ[ t ∈ πType {l} ] πEncoding t) → (Σ[ t ∈ πType {l} ] πEncoding t) → Set where
  unit∥unit : (Chan #0 #0 (Pure OK) , unit) ∥π-enc (Chan #0 #0 (Pure OK) , unit)
  in∥out : ∀{t} → (Chan #1 #0 t , ¿ch) ∥π-enc (Chan #0 #1 t , !ch)
  out∥in : ∀{t} → (Chan #0 #1 t , !ch) ∥π-enc (Chan #1 #0 t , ¿ch)

⊥-to-∥ : ∀{l} (c : Σ[ t ∈ πType {l} ] πEncoding t)  → c ∥π-enc (⊥ₜ c)
⊥-to-∥ (.(Chan #0 #0 (Pure OK)) , unit) = unit∥unit
⊥-to-∥ (.(Chan #1 #0 _) , ¿ch) = in∥out
⊥-to-∥ (.(Chan #0 #1 _) , !ch) = out∥in



 {-
∥-to-⊥ : ∀ t t' → t ∥π-enc t' → t' ≡ ⊥ₜ t
∥-to-⊥ .(Chan #0 #0 (Pure OK) , unit) .(Chan #0 #0 (Pure OK) , unit) unit∥unit = refl
∥-to-⊥ .(Chan #1 #0 _ , ¿ch) .(Chan #0 #1 _ , !ch) in∥out = refl
∥-to-⊥ .(Chan #0 #1 _ , !ch) .(Chan #1 #0 _ , ¿ch) out∥in = refl
-}
