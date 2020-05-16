open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Unit
open import Common

module Pi_Encoding where

{- ##### πEncoding ##### -}

data Encoding : PreType → Set₁ where
  unit  : Encoding (Chan #0 #0 (Pure ⊤))
  in-b  : {f : Bool → πType} → ((b : Bool) → Encoding (f b)) → Encoding (Chan #1 #0 (Pair (Pure Bool) f))
  out-b : {f : Bool → πType} → ((b : Bool) → Encoding (f b)) → Encoding (Chan #0 #1 (Pair (Pure Bool) f))
  in-s  : {t t' : πType} → Encoding t → Encoding t' → Encoding (Chan #1 #0 (Pair t λ _ → t'))
  out-s : {t t' : πType} → Encoding t → Encoding t' → Encoding (Chan #0 #1 (Pair t λ _ → t'))
