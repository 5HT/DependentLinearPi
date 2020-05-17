open import Session_Types
open import Pi_Encoding
open import Data.Fin as Fin
open import Data.Nat as Nat
open import Data.Bool
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Axiom
open import Level as Lv
open import Common

module Encoding where

mutual
  ⌊_⌋-base : BaseType → πType
  ⌊ Pi x ⌋-base = Pure x
  ⌊ Session x ⌋-base = ⌊ x , false ⌋

  ⌊_,_⌋ : SessionType → Bool → πType
  ⌊ ∅ , _ ⌋ = Chan #0 #0 (Pure ⊤)
  ⌊ (¿ x , s) , false ⌋ = Chan #1 #0 (Pair ⌊ x ⌋-base λ _ → ⌊ s , false ⌋)
  ⌊ (¿ x , s) , true ⌋ = Chan #0 #1 (Pair ⌊ x ⌋-base λ _ → ⌊ s , false ⌋)
  ⌊ (! x , s) , false ⌋ =  Chan #0 #1 (Pair ⌊ x ⌋-base λ _ → ⌊ s , true ⌋)
  ⌊ (! x , s) , true ⌋ =  Chan #1 #0 (Pair ⌊ x ⌋-base λ _ → ⌊ s , true ⌋)
  ⌊ & {n} f , false ⌋ = Chan #1 #0 (Pair (Pure (Fin n)) λ x₂ → ⌊ f x₂ , false ⌋)
  ⌊ & {n} f , true ⌋ = Chan #0 #1 (Pair (Pure (Fin n)) λ x₂ → ⌊ f x₂ , false ⌋)
  ⌊ ⊕ {n} f , false ⌋ = Chan #0 #1 (Pair (Pure (Fin n)) λ x₂ → ⌊ f x₂ , true ⌋)
  ⌊ ⊕ {n} f , true ⌋ = Chan #1 #0 (Pair (Pure (Fin n)) λ x₂ → ⌊ f x₂ , true ⌋)

{- Encoded Session is a πEncoding -}
mutual
  𝕓-enc : ∀ B → 𝕓Encoding ⌊ B ⌋-base
  𝕓-enc (Pi x) = πB
  𝕓-enc (Session x) = encB (π-enc false x)
  
  π-enc : ∀(b S) → πEncoding ⌊ S , b ⌋
  π-enc _ ∅ = unit
  π-enc false (¿ x , S) = ¿ch (𝕓-enc x) (π-enc false S)
  π-enc true (¿ x , S) = !ch (𝕓-enc x) (π-enc false S)
  π-enc false (! x , S) = !ch (𝕓-enc x) (π-enc true S)
  π-enc true (! x , S) = ¿ch (𝕓-enc x) (π-enc true S)
  π-enc false (& f) = &ch λ i → π-enc false (f i)
  π-enc true (& f) = ⊕ch λ i → π-enc false (f i)
  π-enc false (⊕ f) = ⊕ch λ i → π-enc true (f i)
  π-enc true (⊕ f) = &ch λ i → π-enc true (f i)


∥ₛ-to-flip : ∀ b S S' → S ∥ₛ S' → ⌊ S , b ⌋ ≡ ⌊ S' , not b ⌋
∥ₛ-to-flip _ ∅ ∅ ∅∥ₛ∅ = refl
∥ₛ-to-flip false (¿ T , S) (! T , S') (¿∥ₛ! d) =
           let rec = ∥ₛ-to-flip false S S' d in
           let t = Pair ⌊ T ⌋-base in
           cong (λ x → Chan #1 #0 (t λ _ → x)) rec
∥ₛ-to-flip true (¿ T , S) (! T , S') (¿∥ₛ! d) =
           let rec = ∥ₛ-to-flip false S S' d in
           let t = Pair ⌊ T ⌋-base in
           cong (λ x → Chan #0 #1 (t λ _ → x)) rec
∥ₛ-to-flip false (! T , S) (¿ T , S') (!∥ₛ¿ d) =
           let rec = ∥ₛ-to-flip true S S' d in
           let t = Pair ⌊ T ⌋-base in
           cong (λ x → Chan #0 #1 (t λ _ → x)) rec
∥ₛ-to-flip true (! T , S) (¿ T , S') (!∥ₛ¿ d) =
           let rec = ∥ₛ-to-flip true S S' d in
           let t = Pair ⌊ T ⌋-base in
           cong (λ x → Chan #1 #0 (t λ _ → x)) rec
∥ₛ-to-flip false (& f) (⊕ f') (&∥ₛ⊕ x) =
  let aux = λ i → ∥ₛ-to-flip false (f i) (f' i) (x {i}) in
  cong
    (λ x₁ → Chan #1 #0 (Pair (Pure _) x₁))
    (extensionality aux)
∥ₛ-to-flip true (& f) (⊕ f') (&∥ₛ⊕ x) =
  let aux = λ i → ∥ₛ-to-flip false (f i) (f' i) (x {i}) in
  cong
    (λ x₁ → Chan #0 #1 (Pair (Pure _) x₁))
    (extensionality aux)
∥ₛ-to-flip false (⊕ f) (& f') (⊕∥ₛ& x) =
  let aux = λ i → ∥ₛ-to-flip true (f i) (f' i) (x {i}) in
  cong
    (λ x₁ → Chan #0 #1 (Pair (Pure _) x₁))
    (extensionality aux)
∥ₛ-to-flip true (⊕ f) (& f') (⊕∥ₛ& x) =
  let aux = λ i → ∥ₛ-to-flip true (f i) (f' i) (x {i}) in
  cong
    (λ x₁ → Chan #1 #0 (Pair (Pure _) x₁))
    (extensionality aux)
