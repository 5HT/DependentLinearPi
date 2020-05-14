
open import Data.Bool
open import LTTypes
open import Pi_Types
open import Encode
open import Relation.Binary.PropositionalEquality
open import Common

test1 : ∀{T : SessionType} -> ⌊ (($ Bool) ⊸ T) , false ⌋ ≡ ⌊ T & T , false ⌋
test1 = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))

test2 : ∀{T : SessionType} -> ⌊ T & T , false ⌋ ≡ ⌊ Ex Bool # (λ _ -> T) , false ⌋
test2 = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))
