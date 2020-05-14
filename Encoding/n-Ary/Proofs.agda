open import Encoding
open import Decoding
open import Pi_Types
open import Session_Types
open import Common
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Vec
open import Data.Bool
open import Data.Unit

module Proofs where


mutual
  dec-enc-𝕓 : ∀ B → B ≡ ⌈ 𝕓-enc B ⌉-base
  dec-enc-𝕓 (Pi x) = refl
  dec-enc-𝕓 (Session x) = cong Session (dec-enc false x)

  dec-enc : ∀ b S → S ≡ ⌈ π-enc b S , b ⌉
  dec-enc _ ∅ = refl
  dec-enc false (¿ x , S) = cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) (dec-enc-𝕓 x) (dec-enc false S)
  dec-enc true (¿ x , S) = cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) (dec-enc-𝕓 x) (dec-enc false S)
  dec-enc false (! x , S) = cong₂ (λ x₁ x₂ → ! x₁ , x₂) (dec-enc-𝕓 x) (dec-enc true S)
  dec-enc true (! x , S) = cong₂ (λ x₁ x₂ → ! x₁ , x₂) (dec-enc-𝕓 x) (dec-enc true S)
  dec-enc false (& f) =
    let aux = λ i → dec-enc false (f i) in
    cong & (extensionality aux)
  dec-enc true (& f) =
    let aux = λ i → dec-enc false (f i) in
    cong & (extensionality aux)
  dec-enc false (⊕ f) =
    let aux = λ i → dec-enc true (f i) in
    cong ⊕ (extensionality aux)
  dec-enc true (⊕ f) =
    let aux = λ i → dec-enc true (f i) in
    cong ⊕ (extensionality aux)


mutual
  enc-dec-𝕓 : ∀{B} → (Enc : 𝕓Encoding B) → B ≡ ⌊ ⌈ Enc ⌉-base ⌋-base
  enc-dec-𝕓 {.(Pure _)} πB = refl
  enc-dec-𝕓 {B} (encB x) = enc-dec false x

  enc-dec : ∀{T} b → (Enc : πEncoding T) → T ≡ ⌊ ⌈ Enc , b ⌉ , b ⌋
  enc-dec b unit = refl
  enc-dec false (¿ch x enc) = cong₂ (λ x₁ x₂ → Chan #1 #0 (Pair x₁ λ _ → x₂)) (enc-dec-𝕓 x) (enc-dec false enc)
  enc-dec true (¿ch x enc) = cong₂ (λ x₁ x₂ → Chan #1 #0 (Pair x₁ λ _ → x₂)) (enc-dec-𝕓 x) (enc-dec true enc)
  enc-dec false (!ch x enc) = cong₂ (λ x₁ x₂ → Chan #0 #1 (Pair x₁ λ _ → x₂)) (enc-dec-𝕓 x) (enc-dec true enc)
  enc-dec true (!ch x enc) = cong₂ (λ x₁ x₂ → Chan #0 #1 (Pair x₁ λ _ → x₂)) (enc-dec-𝕓 x) (enc-dec false enc)
  enc-dec false (&ch {n} e) =
    cong
      (λ x → Chan #1 #0 (Pair (Pure (Fin n)) x))
      (extensionality λ x → enc-dec false (e x))
  enc-dec true (&ch {n} e) =
    cong
      (λ x → Chan #1 #0 (Pair (Pure (Fin n)) x))
      (extensionality λ x → enc-dec true (e x))
  enc-dec false (⊕ch {n} e) =
    cong
      (λ x → Chan #0 #1 (Pair (Pure (Fin n)) x))
      (extensionality λ x → enc-dec true (e x))
  enc-dec true (⊕ch {n} e) =
    cong
      (λ x → Chan #0 #1 (Pair (Pure (Fin n)) x))
      (extensionality λ x → enc-dec false (e x))

{- ##### Duality Correctness ##### -}

dec-∥ₛ-eq : ∀{T}(E : πEncoding T) → (∀ b → ⌈ E , b ⌉ ∥ₛ ⌈ E , not b ⌉)
dec-∥ₛ-eq unit _ = ∅∥ₛ∅
dec-∥ₛ-eq (¿ch _ E) false = ¿∥ₛ! (dec-∥ₛ-eq E false) 
dec-∥ₛ-eq (!ch _ E) false = !∥ₛ¿ (dec-∥ₛ-eq E true)
dec-∥ₛ-eq (&ch f) false = &∥ₛ⊕ λ {i} → dec-∥ₛ-eq (f i) false
dec-∥ₛ-eq (⊕ch f) false = ⊕∥ₛ& λ {i} → dec-∥ₛ-eq (f i) true
dec-∥ₛ-eq (¿ch x E) true = !∥ₛ¿ (dec-∥ₛ-eq E true)
dec-∥ₛ-eq (!ch x E) true = ¿∥ₛ! (dec-∥ₛ-eq E false)
dec-∥ₛ-eq (&ch f) true = ⊕∥ₛ& λ {i} → dec-∥ₛ-eq (f i) true
dec-∥ₛ-eq (⊕ch f) true = &∥ₛ⊕ λ {i} → dec-∥ₛ-eq (f i) false

enc-∥π-eq : ∀ S → (∀ b → ⌊ S , b ⌋ ∥π ⌊ S , not b ⌋)
enc-∥π-eq ∅ _ = flip
enc-∥π-eq (¿ _ , _) false = flip
enc-∥π-eq (! _ , _) false = flip
enc-∥π-eq (& _) false = flip
enc-∥π-eq (⊕ _) false = flip
enc-∥π-eq (¿ _ , _) true = flip
enc-∥π-eq (! _ , _) true = flip
enc-∥π-eq (& _) true = flip
enc-∥π-eq (⊕ _) true = flip

∥ₛ-enc-eq : ∀{S S'} → S ∥ₛ S' → ∀ b → ⌊ S , b ⌋ ≡ ⌊ S' , not b ⌋
∥ₛ-enc-eq ∅∥ₛ∅ _ = refl
∥ₛ-enc-eq (¿∥ₛ! d) false = cong (λ x → Chan #1 #0 (Pair _ λ _ → x)) (∥ₛ-enc-eq d false)
∥ₛ-enc-eq (!∥ₛ¿ d) false = cong (λ x → Chan #0 #1 (Pair _ λ _ → x)) (∥ₛ-enc-eq d true)
∥ₛ-enc-eq (&∥ₛ⊕ {n} x) false = cong (λ x₁ → Chan #1 #0 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) false)
∥ₛ-enc-eq (⊕∥ₛ& {n} x) false = cong (λ x₁ → Chan #0 #1 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) true)
∥ₛ-enc-eq (¿∥ₛ! d) true = cong (λ x → Chan #0 #1 (Pair _ λ _ → x)) (∥ₛ-enc-eq d false)
∥ₛ-enc-eq (!∥ₛ¿ d) true = cong (λ x → Chan #1 #0 (Pair _ λ _ → x)) (∥ₛ-enc-eq d true)
∥ₛ-enc-eq (&∥ₛ⊕ {n} x) true = cong (λ x₁ → Chan #0 #1 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) false)
∥ₛ-enc-eq (⊕∥ₛ& {n} x) true = cong (λ x₁ → Chan #1 #0 (Pair (Pure (Fin n)) x₁)) (extensionality λ x₁ → ∥ₛ-enc-eq (x {x₁}) true)


dec-flip-eq : ∀{T}(E : πEncoding T) b → ⌈ E , b ⌉ ≡ ⌈ flip-π-enc E , not b ⌉
dec-flip-eq unit _ = refl
dec-flip-eq (¿ch x E) false = refl
dec-flip-eq (!ch x E) false = refl
dec-flip-eq (&ch e) false = refl
dec-flip-eq (⊕ch e) false = refl
dec-flip-eq (¿ch x E) true = refl
dec-flip-eq (!ch x E) true = refl
dec-flip-eq (&ch e) true = refl
dec-flip-eq (⊕ch e) true = refl


{- ##### Commuting Duality ##### -}

comm-dual-dec : ∀{T} (E : πEncoding T) b → ⌈ flip-π-enc E , b ⌉ ≡ ⊥ₛ ⌈ E , b ⌉
comm-dual-dec unit _ = refl
comm-dual-dec (¿ch x E) false =
  let rec = comm-dual-dec E false in
  cong₂ (λ x₁ x₂ → ! x₁ , x₂) refl (trans (dec-flip-eq E true) rec)
comm-dual-dec (!ch x E) false =
  let rec = comm-dual-dec E true in
  cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) refl (trans (dec-flip-eq E false) rec)
comm-dual-dec (&ch e) false =
  cong (λ x → ⊕ x) (extensionality λ x → trans (dec-flip-eq (e x) true) (comm-dual-dec (e x) false))
comm-dual-dec (⊕ch e) false =
  cong (λ x → & x) (extensionality λ x → trans (dec-flip-eq (e x) false) (comm-dual-dec (e x) true))
comm-dual-dec (¿ch x E) true =
  let rec = comm-dual-dec E true in
  cong₂ (λ x₁ x₂ → ¿ x₁ , x₂) refl (trans (dec-flip-eq E false) rec)
comm-dual-dec (!ch x E) true =
  let rec = comm-dual-dec E false in
  cong₂ (λ x₁ x₂ → ! x₁ , x₂) refl (trans (dec-flip-eq E true) rec)
comm-dual-dec (&ch e) true =
  cong (λ x → & x) (extensionality λ x → trans (dec-flip-eq (e x) false) (comm-dual-dec (e x) true))
comm-dual-dec (⊕ch e) true =
  cong (λ x → ⊕ x) (extensionality λ x → trans (dec-flip-eq (e x) true) (comm-dual-dec (e x) false))
