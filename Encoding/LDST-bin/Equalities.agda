open import Data.Nat
open import Data.Bool
open import LDSTypes
open import Pi_Encoding
open import Encode
open import Relation.Binary.PropositionalEquality
open import Common
open import Data.List

example1 : SessionType -> SessionType -> SessionType
example1 S T = ¿ Boolean , (case 0 of (¿ (Session S) , T ) , (¿ (Session S) , T))

example2 : SessionType -> SessionType -> SessionType
example2 S T = ¿ Boolean , (¿ (Session S) , (case 0 of T , T))

mutual
  shift-t : Type -> Type
  shift-t (Session T) = Session (shift-st T)
  shift-t Boolean = Boolean

  shift-st : SessionType -> SessionType
  shift-st End = End
  shift-st (case x of T , S) = case (suc x) of shift-st T , shift-st S
  shift-st (! t , T) = ! shift-t t , shift-st T
  shift-st (¿ t , T) = ¿ shift-t t , shift-st T

weaken-var : ∀{s Γ n} -> WFV n Γ Boolean -> WFV (suc n) (s ∷ Γ) Boolean
weaken-var here = next here
weaken-var (next x) = next (weaken-var x)

weaken : ∀{Γ T} -> WFS Γ T -> WFS (Boolean ∷ Γ) (shift-st T)
weaken wf-end = wf-end
weaken (wf-case x T S) = wf-case (weaken-var x) (weaken T) (weaken S)
weaken (wf-in-s S T) = wf-in-s (weaken S) (weaken T)
weaken (wf-out-s S T) = wf-out-s (weaken S) (weaken T)
weaken (wf-in-b T) = wf-in-b (weaken T)
weaken (wf-out-b T) = wf-out-b (weaken T)

example1-wf : ∀{S T} -> WFS [] S -> WFS [] T -> WFS [] (example1 (shift-st S) (shift-st T))
example1-wf S T = wf-in-b (wf-case here (wf-in-s (weaken S) (weaken T)) (wf-in-s (weaken S) (weaken T)))

example2-wf : ∀{S T} -> WFS [] S -> WFS [] T -> WFS [] (example2 (shift-st S) (shift-st T))
example2-wf S T = wf-in-b (wf-in-s (weaken S) (wf-case here (weaken T) (weaken T)))

test-eq : ∀{S T} -> (WS : WFS [] S) -> (WT : WFS [] T) -> (⌊ [] , example1-wf WS WT , false ⌋) ≡ (⌊ [] , example2-wf WS WT , false ⌋)
test-eq S T = cong (Chan #1 #0) (cong (Pair (Pure Bool)) (extensionality λ { true -> refl ; false -> refl }))
