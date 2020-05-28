{- This file is part of DLπ.                                         -}
{-                                                                   -}
{- DLπ is free software: you can redistribute it and/or modify it    -}
{- under the terms of the GNU General Public License as published by -}
{- the Free Software Foundation, either version 3 of the License, or -}
{- (at your option) any later version.                               -}
{-                                                                   -}
{- DLπ is distributed in the hope that it will be useful, but        -}
{- WITHOUT ANY WARRANTY; without even the implied warranty of        -}
{- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU -}
{- General Public License for more details.                          -}
{-                                                                   -}
{- You should have received a copy of the GNU General Public License -}
{- along with DLπ.  If not, see <https://www.gnu.org/licenses/>.     -}
{-                                                                   -}
{- Copyright 2020 Luca Ciccone, Luca Padovani                        -}

open import Data.Maybe
open import Data.Empty
open import Data.Nat
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Codata.Thunk

open import Language
open import Congruence
open import Reduction
open import PrefixedBy
open import PrefixNormalForm
open import Split
open import Weaken
open import Substitution

data ReducibleNormalForm : ∀{Γ} -> ℕ -> Process Γ -> Set where
  rnf-com :
    ∀{k Γ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22 t s v}
    -> (sp  : CSplit Γ Γ1 Γ2)
    -> (sp1 : CSplit Γ1 Γ11 Γ12)
    -> (sp2 : CSplit Γ2 Γ21 Γ22)
    -> (x   : Name k Γ11 (Chan #0 #1 t) _)
    -> (y   : Name k Γ21 (Chan #1 #0 s) _)
    -> (V   : Term Γ12 (t .force) v)
    -> (g   : (v : ⟦ s .force ⟧) -> Process (s .force # v :: Γ22))
    -> ReducibleNormalForm k (Par sp (Send sp1 (name x) V) (Recv sp2 (name y) g))
  rnf-par :
    ∀{Γ Γ1 Γ2 k}{P : Process Γ1}{Q : Process Γ2}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> ReducibleNormalForm k P
    -> ReducibleNormalForm k (Par sp P Q)
  rnf-new :
    ∀{Γ m n t k}
     {P : Process (Chan m n t # _ :: Γ)}
    -> ReducibleNormalForm (suc k) P
    -> ReducibleNormalForm k (New P)

cong-par-assoc-swap-assoc :
  ∀{Γ Γ1 Γ2 Γ11 Γ12}
  -> (sp1 : CSplit Γ Γ1 Γ2)
  -> (sp2 : CSplit Γ1 Γ11 Γ12)
  -> (P : Process Γ11)
  -> (Q : Process Γ12)
  -> (R : Process Γ2)
  -> let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
     let _ , sp1'' , sp2'' = csplit-assoc-rl sp1' (csplit-comm sp2') in
     Par sp1 (Par sp2 P Q) R <= Par sp1'' (Par sp2'' P R) Q
     -- Par sp1 (Par sp2 P Q) R <= Par sp1' P (Par sp2' Q R)
     --                         <= Par sp1' P (Par (csplit-comm sp2') R Q)
     --                         <= Par sp1'' (Par sp2'' P R) Q
cong-par-assoc-swap-assoc sp1 sp2 P Q R =
  let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
  cong-trans (cong-par-assoc-lr sp1 sp2)
  (cong-trans (cong-par-cong-r sp1' P (Par sp2' Q R)
                                       (Par (csplit-comm sp2') R Q)
                                       (cong-par-comm sp2'))
              (cong-par-assoc-rl sp1' (csplit-comm sp2')))

{-# TERMINATING #-}
pnf-pnf-rnf :
  ∀{Γ Γ1 Γ2 k}
  -> (sp : CSplit Γ Γ1 Γ2)
  -> (P : Process Γ1)
  -> (Q : Process Γ2)
  -> PrefixNormalForm k #0 #1 P
  -> PrefixNormalForm k #1 #0 Q
  -> ∃ λ R -> Par sp P Q <= R × ReducibleNormalForm k R
pnf-pnf-rnf sp (Send sp1 (name x) V) (Recv sp2 (name y) R) (pnf-send _) (pnf-recv _) =
  _ , cong-refl , rnf-com sp sp1 sp2 x y V R
pnf-pnf-rnf sp1 P (Par sp2 Q1 Q2) pnfP@(pnf-send _) (pnf-par _ pnfQ1) =
  let _ , sp1' , sp2' = csplit-assoc-rl sp1 sp2 in
  let R , P|Q1<=R , rnf = pnf-pnf-rnf sp2' P Q1 pnfP pnfQ1 in
  Par sp1' R Q2 ,
  cong-trans (cong-par-assoc-rl sp1 sp2) (cong-par-cong sp1' P|Q1<=R) ,
  rnf-par sp1' rnf
pnf-pnf-rnf sp P (New {_} {m} {n} Q) pnfP@(pnf-send _) (pnf-new pnfQ) =
  let we = here chan in
  let P' = weaken-process we P in
  let sp' = chan (msplit-r m) (msplit-r n) :: sp in
  let R , P'|Q<=R , rnf = pnf-pnf-rnf sp' P' Q (weaken-pnf P we pnfP) pnfQ in
  New R ,
  cong-trans (cong-par-new-r sp P Q) (cong-new-cong P'|Q<=R) ,
  rnf-new rnf
pnf-pnf-rnf sp1 (Par sp2 P1 P2) Q (pnf-par _ pnfP) pnfQ =
  let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
  let _ , sp1'' , sp2'' = csplit-assoc-rl sp1' (csplit-comm sp2') in
  let R , P1|Q<=R , rnf = pnf-pnf-rnf sp2'' P1 Q pnfP pnfQ in
  Par sp1'' R P2 ,
  cong-trans (cong-par-assoc-swap-assoc sp1 sp2 P1 P2 Q)
             (cong-par-cong sp1'' P1|Q<=R) ,
  rnf-par sp1'' rnf
pnf-pnf-rnf sp (New {_} {m} {n} P) Q (pnf-new pnfP) pnfQ =
  let we = here chan in
  let sp' = chan (msplit-l m) (msplit-l n) :: sp in
  let Q' = weaken-process we Q in
  let R , P|Q<=R , rnf = pnf-pnf-rnf sp' P Q' pnfP (weaken-pnf Q we pnfQ) in
  New R ,
  cong-trans (cong-par-new sp) (cong-new-cong P|Q<=R) ,
  rnf-new rnf

pnf-pb-rnf :
  ∀{Γ k}
  -> (P : Process Γ)
  -> PrefixNormalForm k #0 #1 P
  -> PrefixedBy k #1 #0 P
  -> ∃ λ Q -> P <= Q × ReducibleNormalForm k Q
pnf-pb-rnf (Par sp P Q) (pnf-par _ pnf) (prefixed-par-l _ pb) =
  let R , P<=R , Rnf = pnf-pb-rnf P pnf pb in
  Par sp R Q , cong-par-cong sp P<=R , rnf-par sp Rnf
pnf-pb-rnf (Par sp P Q) (pnf-par _ pnfP) (prefixed-par-r _ pb) =
  let Q' , Q<=Q' , pnfQ' = prefix-normal-form Q pb in
  let R , P|Q'<=R , rnf = pnf-pnf-rnf sp P Q' pnfP pnfQ' in
  R , cong-trans (cong-par-cong-r sp P Q Q' Q<=Q') P|Q'<=R , rnf
pnf-pb-rnf (New P) (pnf-new pnf) (prefixed-new pb) =
  let Q , P<=Q , Rnf = pnf-pb-rnf P pnf pb in
  New Q , cong-new-cong P<=Q , rnf-new Rnf

reducible-normal-form :
  ∀{Γ k}
  -> (P : Process Γ)
  -> PrefixedBy k #0 #1 P
  -> PrefixedBy k #1 #0 P
  -> ∃ λ Q -> P <= Q × ReducibleNormalForm k Q
reducible-normal-form P pbo pbi =
  let P' , P<=P' , Pnf = prefix-normal-form P pbo in
  let Q' , P'<=Q' , Rnf = pnf-pb-rnf P' Pnf (prefixed-cong pbi P<=P') in
  Q' , cong-trans P<=P' P'<=Q' , Rnf

rnf-reduces :
  ∀{k Γ}
  -> (P : Process Γ)
  -> ReducibleNormalForm k P
  -> ∃ λ l
  -> ∃ λ Δ
  -> ∃ λ (cr : Γ == l => Δ)
  -> ∃ λ (Q : Process Δ)
  -> SyncLabel l × P ~~ cr ~> Q
rnf-reduces (Par sp (Send sp1 (name x) V) (Recv sp2 (name y) P))
            (rnf-com _ _ _ _ _ _ _) =
  _ , _ , _ , _ , sync# , r-com sp sp1 sp2 x y V P
rnf-reduces (Par sp P R) (rnf-par _ pnf) =
  let _ , _ , cr' , _ , sl , red = rnf-reduces P pnf in
  _ , _ , _ , _ , sl , r-par sp cr' red
rnf-reduces (New P) (rnf-new pnf) with rnf-reduces P pnf
... | _ , _ , tau          , _ , sl , red = _ , _ , _ , _ , sl , r-new-tau red
... | _ , _ , #-here m0 n0 , _ , _  , red = _ , _ , _ , _ , syncτ , r-new-here (#-here m0 n0) red
... | _ , _ , #-next cr    , _ , _  , red = _ , _ , _ , _ , sync# , r-new-next cr red
