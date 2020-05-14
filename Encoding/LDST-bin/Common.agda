open import Axiom.Extensionality.Propositional as Axiom
open import Level as Lv

module Common where

postulate
  extensionality : Axiom.Extensionality Lv.zero (Lv.suc Lv.zero)


