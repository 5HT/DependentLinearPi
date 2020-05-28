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

open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; cong₂)

open import Language
open import Split
open import Scale
open import Swap
open import Weaken

module Congruence where

data _<=_ : ∀{Γ} -> Process Γ -> Process Γ -> Set₁ where
  cong-refl : ∀{Γ}{P : Process Γ} -> P <= P
  cong-trans : ∀{Γ}{P Q R : Process Γ} -> P <= Q -> Q <= R -> P <= R
  cong-par-idle-lr :
    ∀{Γ Δ P} {sp : CSplit Γ Δ Γ} {cz : CNull Δ} -> Par sp (Idle cz) P <= P
  cong-par-idle-rl :
    ∀{Γ Δ P} {sp : CSplit Γ Δ Γ} {cz : CNull Δ} -> P <= Par sp (Idle cz) P
  cong-par-cong :
    ∀{Γ Γ1 Γ2 P P' Q} (sp : CSplit Γ Γ1 Γ2) -> P <= P' -> Par sp P Q <= Par sp P' Q
  cong-par-comm :
    ∀{Γ Γ1 Γ2 P Q} (sp : CSplit Γ Γ1 Γ2) -> Par sp P Q <= Par (csplit-comm sp) Q P
  cong-par-assoc-rl :
    ∀{Γ ΓP ΓQR ΓQ ΓR}
    {P   : Process ΓP}
    {Q   : Process ΓQ}
    {R   : Process ΓR}
    (sp1 : CSplit Γ ΓP ΓQR)
    (sp2 : CSplit ΓQR ΓQ ΓR) ->
    let _ , sp1' , sp2' = csplit-assoc-rl sp1 sp2 in
    Par sp1 P (Par sp2 Q R) <= Par sp1' (Par sp2' P Q) R
  cong-par-assoc-lr :
    ∀{Γ ΓPQ ΓP ΓQ ΓR}
    {P   : Process ΓP}
    {Q   : Process ΓQ}
    {R   : Process ΓR}
    (sp1 : CSplit Γ ΓPQ ΓR)
    (sp2 : CSplit ΓPQ ΓP ΓQ) ->
    let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
    Par sp1 (Par sp2 P Q) R <= Par sp1' P (Par sp2' Q R)
  cong-new-cong :
    ∀{Γ σ ρ t}
    {P Q : Process (Chan σ ρ t # _ :: Γ)} ->
    P <= Q -> New P <= New Q
  cong-new-new :
    ∀{Γ σ1 ρ1 σ2 ρ2 t1 t2}
    {P : Process (Chan σ1 ρ1 t1 # _ :: (Chan σ2 ρ2 t2 # _ :: Γ))}->
    New (New P) <= New (New (swap-process here P))
  cong-par-new :
    ∀{Γ ΓP ΓQ σ ρ t}
    {P  : Process (Chan σ ρ t # _ :: ΓP)}
    {Q  : Process ΓQ}
    (sp : CSplit Γ ΓP ΓQ) ->
    let sp' = chan (msplit-l σ) (msplit-l ρ) :: sp in
    let we = here chan in
    Par sp (New P) Q <= New (Par sp' P (weaken-process we Q))
  cong-new-par :
    ∀{Γ Γ1 Γ2 σ ρ t P Q}
    (sp : CSplit Γ Γ1 Γ2)
    (niQ : NotInProcess zero Q) ->
    let sp' = chan (msplit-l σ) (msplit-l ρ) :: sp in
    let we = here chan in
    New {_} {σ} {ρ} {t} (Par sp' P Q) <= Par sp (New P) (strengthen-process we Q niQ)
  cong-new-idle :
    ∀{Γ t}
    (cz : CNull (Chan #0 #0 t # _ :: Γ)) ->
    New (Idle cz) <= Idle (strengthen-null (here chan) cz)
  cong-idle-new :
    ∀{Γ t}
    (cz : CNull Γ) ->
    Idle cz <= New {_} {#0} {#0} {t} (Idle (chan :: cz))
  cong-rep-par :
    ∀{Γ Δ P}
    (sc : CScale Γ Δ) ->
    Rep sc P <= Par (c-scale-split sc) P (Rep sc P)
  cong-par-rep :
    ∀{Γ Δ P}
    (sp : CSplit Δ Γ Δ)
    (sc : CScale Γ Δ) ->
    Par sp P (Rep sc P) <= Rep sc P

cong-par-cong-r :
  ∀{Γ Γ1 Γ2}
  (sp : CSplit Γ Γ1 Γ2)
  (P : Process Γ1)
  (Q : Process Γ2)
  (Q' : Process Γ2) ->
  Q <= Q' ->
  Par sp P Q <= Par sp P Q'
cong-par-cong-r sp P Q Q' Q<=Q' =
  let sp' = csplit-comm sp in
  let pc = cong-trans (cong-par-comm sp)
           (cong-trans (cong-par-cong sp' Q<=Q')
           (cong-par-comm sp')) in
  subst (λ x -> Par sp P Q <= Par x P Q') (csplit-comm-inv sp) pc

cong-par-new-r :
  ∀{Γ Γ1 Γ2 m n t}
  (sp : CSplit Γ Γ1 Γ2)
  (P : Process Γ1)
  (Q : Process (Chan m n t # _ :: Γ2)) ->
  let sp' = chan (msplit-r m) (msplit-r n) :: sp in
  let we = here chan in
  Par sp P (New Q) <= New (Par sp' (weaken-process we P) Q)
cong-par-new-r {Γ} {Γ1} {Γ2} {m} {n} {t} sp P Q =
  let we = here chan in
  let sp' = chan {m} {m} {#0} {n} {n} {#0} {t} (msplit-l m) (msplit-l n) :: (csplit-comm sp) in
  let spe = chan {m} {#0} {m} {n} {#0} {n} {t} (msplit-r m) (msplit-r n) :: sp in
  let pc1 : Par sp P (New Q) <= Par (csplit-comm sp) (New Q) P
      pc1 = cong-par-comm sp
      pc2 : Par (csplit-comm sp) (New Q) P <= New (Par sp' Q (weaken-process we P))
      pc2 = cong-par-new (csplit-comm sp)
      pc3 : New (Par sp' Q (weaken-process we P)) <= New (Par (csplit-comm sp') (weaken-process we P) Q)
      pc3 = cong-new-cong (cong-par-comm sp')
      pce : New (Par sp' Q (weaken-process we P)) <= New (Par spe (weaken-process we P) Q)
      pce = subst (λ x -> New (Par sp' Q (weaken-process we P)) <= New (Par x (weaken-process we P) Q))
                  (cong₂ _::_
                         (cong₂ chan (msplit-comm-lr m) (msplit-comm-lr n))
                         (csplit-comm-inv sp))
                  pc3
  in
  cong-trans pc1 (cong-trans pc2 pce)

