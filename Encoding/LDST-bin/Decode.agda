open import Pi_Encoding
open import LDSTypes
open import Data.Nat
open import Data.Product
open import Data.List
open import Data.Bool

module Decode where

⌈_,_⌉ : ∀{t} -> Encoding t → Bool -> SessionType
⌈ unit , _ ⌉ = End
⌈ in-b f , false ⌉ = ¿ Boolean , case zero of ⌈ (f false) , false ⌉ , ⌈ (f true) , false ⌉
⌈ in-b f , true ⌉ = ! Boolean , case zero of ⌈ (f false) , true ⌉ , ⌈ (f true) , true ⌉
⌈ out-b f , false ⌉ = ! Boolean , case zero of ⌈ (f false) , true ⌉ , ⌈ (f true) , true ⌉
⌈ out-b f , true ⌉ = ¿ Boolean , case zero of ⌈ (f false) , false ⌉ , ⌈ (f true) , false ⌉
⌈ in-s enc1 enc2 , false ⌉ = ¿ Session ⌈ enc1 , false ⌉ , ⌈ enc2 , false ⌉
⌈ in-s enc1 enc2 , true ⌉ = ! Session ⌈ enc1 , false ⌉ , ⌈ enc2 , true ⌉
⌈ out-s enc1 enc2 , false ⌉ = ! Session ⌈ enc1 , false ⌉ , ⌈ enc2 , true ⌉
⌈ out-s enc1 enc2 , true ⌉ = ¿ Session ⌈ enc1 , false ⌉ , ⌈ enc2 , false ⌉

dec-WFS-Γ : ∀{t Γ} b -> (enc : Encoding t) -> WFS Γ ⌈ enc , b ⌉
dec-WFS-Γ _ unit = wf-end
dec-WFS-Γ false (in-b x) = wf-in-b (wf-case here  (dec-WFS-Γ false (x false)) (dec-WFS-Γ false (x true)))
dec-WFS-Γ true (in-b x) = wf-out-b (wf-case here  (dec-WFS-Γ true (x false)) (dec-WFS-Γ true (x true)))
dec-WFS-Γ false (out-b x) = wf-out-b (wf-case here  (dec-WFS-Γ true (x false)) (dec-WFS-Γ true (x true)))
dec-WFS-Γ true (out-b x) = wf-in-b (wf-case here  (dec-WFS-Γ false (x false)) (dec-WFS-Γ false (x true)))
dec-WFS-Γ false (in-s T₁ T₂) = wf-in-s (dec-WFS-Γ false T₁) (dec-WFS-Γ false T₂)
dec-WFS-Γ true (in-s T₁ T₂) = wf-out-s (dec-WFS-Γ false T₁) (dec-WFS-Γ true T₂) 
dec-WFS-Γ false (out-s T₁ T₂) = wf-out-s (dec-WFS-Γ false T₁) (dec-WFS-Γ true T₂) 
dec-WFS-Γ true (out-s T₁ T₂) = wf-in-s (dec-WFS-Γ false T₁) (dec-WFS-Γ false T₂) 

dec-WFS-[] : ∀{t} b -> (enc : Encoding t) -> WFS [] ⌈ enc , b ⌉
dec-WFS-[] b enc = dec-WFS-Γ {Γ = []} b enc
