open import Data.Unit
open import Common
open import Relation.Binary.PropositionalEquality

module Pi_Encoding where

{- ##### πEncoding ##### -}

data Encoding : PreType → Set₁ where
  unit  : Encoding (Chan #0 #0 (Pure ⊤))
  input : {t : πType}{f : ⟦ t ⟧ → πType} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x))→ Encoding (Chan #1 #0 (Pair t f))
  output : {t : πType}{f : ⟦ t ⟧ → πType} → Encoding t → ((x : ⟦ t ⟧) → Encoding (f x))→ Encoding (Chan #0 #1 (Pair t f))
  pure : ∀ t → Encoding (Pure t)
