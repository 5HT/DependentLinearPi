open import Pi_Encoding
open import Session_Types
open import Data.Product
open import Common
open import Data.Unit
open import Data.Fin
open import Data.Vec as Vec
open import Level
open import Data.Bool
open import Data.Empty
open import Relation.Binary.PropositionalEquality

module Decoding where

mutual
  ⌈_⌉-base : {t : πType} → 𝕓Encoding t → BaseType
  ⌈ πB {A} ⌉-base = Pi A
  ⌈ encB x ⌉-base = Session ⌈ x , false ⌉ 
  
  ⌈_,_⌉ : {t : πType} → πEncoding t → Bool → SessionType
  ⌈ unit , _ ⌉ = ∅
  ⌈ ¿ch b e , false ⌉ = ¿ ⌈ b ⌉-base , ⌈ e , false ⌉
  ⌈ ¿ch b e , true ⌉ = ! ⌈ b ⌉-base , ⌈ e , true ⌉
  ⌈ !ch b e , false ⌉ = ! ⌈ b ⌉-base , ⌈ e , true ⌉
  ⌈ !ch b e , true ⌉ = ¿ ⌈ b ⌉-base , ⌈ e , false ⌉
  ⌈ &ch f , false ⌉ = & λ x → ⌈ f x , false ⌉
  ⌈ &ch f , true ⌉ = ⊕ λ x → ⌈ f x , true ⌉
  ⌈ ⊕ch f , false ⌉ = ⊕ λ x → ⌈ f x , true ⌉
  ⌈ ⊕ch f , true ⌉ = & λ x → ⌈ f x , false ⌉

