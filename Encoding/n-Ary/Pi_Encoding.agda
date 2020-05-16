open import Common
open import Data.Unit
open import Data.Fin
open import Relation.Binary.PropositionalEquality

module Pi_Encoding where

{- ##### πEncoding ##### -}

mutual
  data 𝕓Encoding : PreType → Set₁ where
    πB : ∀{A} → 𝕓Encoding (Pure A)
    encB : ∀{t} → πEncoding t → 𝕓Encoding t
  
  data πEncoding : PreType → Set₁ where
    unit : πEncoding (Chan #0 #0 (Pure ⊤))
    ¿ch : {t t' : πType} → 𝕓Encoding t → πEncoding t' → πEncoding (Chan #1 #0 (Pair t λ _ → t'))
    !ch : {t t' : πType} → 𝕓Encoding t → πEncoding t' → πEncoding (Chan #0 #1 (Pair t λ _ → t'))
    &ch : ∀{n} → {f : Fin n → πType} → (e : (i : Fin n) → πEncoding (f i)) →
          πEncoding (Chan #1 #0 (Pair (Pure (Fin n)) f))
    ⊕ch : ∀{n} → {f : Fin n → πType} → (e : (i : Fin n) → πEncoding (f i)) →
          πEncoding (Chan #0 #1 (Pair (Pure (Fin n)) f))

{- ##### πType Duality as Predicate ##### -}

data _∥π_ : πType → πType → Set where
  flip : ∀{m n t} → Chan m n t ∥π Chan n m t

-- Symmetric
∥π-sym : ∀{T T'} → T ∥π T' → T' ∥π T
∥π-sym flip = flip

-- Involutory
∥π-inv : ∀{T T' T''} → T ∥π T' → T' ∥π T'' → T ≡ T''
∥π-inv flip flip = refl


flip-mul : πType → πType
flip-mul (Pure A) = Pure A
flip-mul (Chan x x₁ p) = Chan x₁ x p
flip-mul (Pair p f) = Pair p f

-- Involutory
flip-inv : ∀ T → T ≡ flip-mul (flip-mul T)
flip-inv (Pure A) = refl
flip-inv (Chan x x₁ T) = refl
flip-inv (Pair T f) = refl

-- Symmetric
flip-sym : ∀ T T' → T ≡ flip-mul T' → flip-mul T ≡ T'
flip-sym .(Pure A) (Pure A) refl = refl
flip-sym .(Chan x₁ x T') (Chan x x₁ T') refl = sym (flip-inv (Chan x x₁ T'))
flip-sym .(Pair T' f) (Pair T' f) refl = refl

-- πEncoding holds after multiplicity flip

flip-π-enc : ∀ {t} → πEncoding t → πEncoding (flip-mul t)
flip-π-enc unit = unit
flip-π-enc (¿ch b e) = !ch b e
flip-π-enc (!ch b e) = ¿ch b e
flip-π-enc (&ch l) = ⊕ch l
flip-π-enc (⊕ch l) = &ch l
