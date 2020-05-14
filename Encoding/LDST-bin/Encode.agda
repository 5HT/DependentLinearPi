open import Pi_Types as PI
open import LDSTypes as LDST
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Product

module Encode where

mutual
  ⌊_,_⌋-base : ∀{Γ t} → Env Γ → WFT Γ t → πType
  ⌊ E , wf-s W ⌋-base = ⌊ E , W , false ⌋
  ⌊ _ , wf-b ⌋-base = Pure Bool

  ⌊_,_,_⌋ : ∀{Γ S} → Env Γ → WFS Γ S → Bool → πType
  ⌊ _ , wf-end , _ ⌋ = Chan #0 #0 (Pure ⊤)
  ⌊ E , wf-case x T S , b ⌋ with env-lookup E x
  ...| false , _  = ⌊ E , T , b ⌋
  ...| true , _ = ⌊ E , S , b ⌋
  ⌊ E , wf-in-s T S , false ⌋ = Chan #1 #0 (Pair ⌊ E , T , false ⌋ λ _ -> ⌊ E , S , false ⌋)
  ⌊ E , wf-in-b T   , false ⌋ = Chan #1 #0 (Pair (Pure Bool) λ x -> ⌊ x :: E , T , false ⌋)
  ⌊ E , wf-in-s T S , true ⌋  = Chan #0 #1 (Pair ⌊ E , T , false ⌋ λ _ -> ⌊ E , S , false ⌋)
  ⌊ E , wf-in-b T   , true ⌋  = Chan #0 #1 (Pair (Pure Bool) λ x -> ⌊ x :: E , T , false ⌋)
  ⌊ E , wf-out-s T S , false ⌋ = Chan #0 #1 (Pair ⌊ E , T , false ⌋ λ _ -> ⌊ E , S , true ⌋)
  ⌊ E , wf-out-b T   , false ⌋ = Chan #0 #1 (Pair (Pure Bool) λ x -> ⌊ x :: E , T , true ⌋)
  ⌊ E , wf-out-s T S , true ⌋  = Chan #1 #0 (Pair ⌊ E , T , false ⌋ λ _ -> ⌊ E , S , true ⌋)
  ⌊ E , wf-out-b T   , true ⌋  = Chan #1 #0 (Pair (Pure Bool) λ x -> ⌊ x :: E , T , true ⌋)


enc-Enc : ∀{Γ T} -> (E : Env Γ) -> (W : WFS Γ T) -> (b : Bool) -> Encoding ⌊ E , W , b ⌋
enc-Enc E wf-end b = unit
enc-Enc E (wf-case x W1 W2) b with env-lookup E x
... | false , _ = enc-Enc E W1 b
... | true , _ = enc-Enc E W2 b
enc-Enc E (wf-in-s W1 W2) false = in-s (enc-Enc E W1 false) (enc-Enc E W2 false)
enc-Enc E (wf-in-s W1 W2) true = out-s (enc-Enc E W1 false) (enc-Enc E W2 false)
enc-Enc E (wf-out-s W1 W2) false = out-s (enc-Enc E W1 false) (enc-Enc E W2 true)
enc-Enc E (wf-out-s W1 W2) true = in-s (enc-Enc E W1 false) (enc-Enc E W2 true)
enc-Enc E (wf-in-b W) false = in-b λ x -> enc-Enc (x :: E) W false
enc-Enc E (wf-in-b W) true = out-b λ x -> enc-Enc (x :: E) W false
enc-Enc E (wf-out-b W) false = out-b λ x -> enc-Enc (x :: E) W true
enc-Enc E (wf-out-b W) true = in-b λ x -> enc-Enc (x :: E) W true
