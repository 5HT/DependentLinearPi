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

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Codata.Thunk
open import Data.Maybe

open import Common
open import Multiplicity
open import Type
open import Context
open import Language
open import Swapping
open import Weakening
open import Substitution
open import Scaling

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst; subst₂)

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
    New (New P) <= New (New (swap-process swap-here P))
  cong-par-new :
    ∀{Γ ΓP ΓQ σ ρ t}
    {P  : Process (Chan σ ρ t # _ :: ΓP)}
    {Q  : Process ΓQ}
    (sp : CSplit Γ ΓP ΓQ) ->
    let sp' = split-c (msplit-l σ) (msplit-l ρ) :: sp in
    let we = weaken-here null-c in
    Par sp (New P) Q <= New (Par sp' P (weaken-process we Q))
  cong-new-par :
    ∀{Γ Γ1 Γ2 σ ρ t P Q}
    (sp : CSplit Γ Γ1 Γ2)
    (niQ : NotInProcess zero Q) ->
    let sp' = split-c (msplit-l σ) (msplit-l ρ) :: sp in
    let we = weaken-here null-c in
    New {_} {σ} {ρ} {t} (Par sp' P Q) <= Par sp (New P) (strengthen-process we Q niQ)
  cong-new-idle :
    ∀{Γ t}
    (cz : CNull (Chan #0 #0 t # _ :: Γ)) ->
    New (Idle cz) <= Idle (strengthen-null (weaken-here null-c) cz)
  cong-idle-new :
    ∀{Γ t}
    (cz : CNull Γ) ->
    Idle cz <= New {_} {#0} {#0} {t} (Idle (null-c :: cz))
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
  let sp' = split-c (msplit-r m) (msplit-r n) :: sp in
  let we = weaken-here null-c in
  Par sp P (New Q) <= New (Par sp' (weaken-process we P) Q)
cong-par-new-r {Γ} {Γ1} {Γ2} {m} {n} {t} sp P Q =
  let we = weaken-here null-c in
  let sp' = split-c {m} {m} {#0} {n} {n} {#0} {t} (msplit-l m) (msplit-l n) :: (csplit-comm sp) in
  let spe = split-c {m} {#0} {m} {n} {#0} {n} {t} (msplit-r m) (msplit-r n) :: sp in
  let pc1 : Par sp P (New Q) <= Par (csplit-comm sp) (New Q) P
      pc1 = cong-par-comm sp
      pc2 : Par (csplit-comm sp) (New Q) P <= New (Par sp' Q (weaken-process we P))
      pc2 = cong-par-new (csplit-comm sp)
      pc3 : New (Par sp' Q (weaken-process we P)) <= New (Par (csplit-comm sp') (weaken-process we P) Q)
      pc3 = cong-new-cong (cong-par-comm sp')
      pce : New (Par sp' Q (weaken-process we P)) <= New (Par spe (weaken-process we P) Q)
      pce = subst (λ x -> New (Par sp' Q (weaken-process we P)) <= New (Par x (weaken-process we P) Q))
                  (cong₂ _::_
                         (cong₂ split-c (msplit-comm-lr m) (msplit-comm-lr n))
                         (csplit-comm-inv sp))
                  pc3
  in
  cong-trans pc1 (cong-trans pc2 pce)

data Label : Set where
  Lτ : Label
  L? L! L# : ℕ -> Label

data SyncLabel : Label -> Set where
  sync# : ∀{k} -> SyncLabel (L# k)
  syncτ : SyncLabel Lτ

data _==_=>_ : Context -> Label -> Context -> Set₁ where
  tau : ∀{Γ} -> Γ == Lτ => Γ
  ?-here :
    ∀{t m m' n Γ} ->
    MSplit m #1 m' ->
    (Chan m n t # _ :: Γ) == L? zero => (Chan m' n t # _ :: Γ)
  !-here :
    ∀{t m n n' Γ} ->
    MSplit n #1 n' ->
    (Chan m n t # _ :: Γ) == L! zero => (Chan m n' t # _ :: Γ)
  #-here :
    ∀{t m m' n n' Γ} ->
    MSplit m #1 m' ->
    MSplit n #1 n' ->
    (Chan m n t # _ :: Γ) == L# zero => (Chan m' n' t # _ :: Γ)
  ?-next :
    ∀{k t v Γ Δ} ->
    Γ == L? k => Δ ->
    (t # v :: Γ) == L? (suc k) => (t # v :: Δ)
  !-next :
    ∀{k t v Γ Δ} ->
    Γ == L! k => Δ ->
    (t # v :: Γ) == L! (suc k) => (t # v :: Δ)
  #-next :
    ∀{k t v Γ Δ} ->
    Γ == L# k => Δ ->
    (t # v :: Γ) == L# (suc k) => (t # v :: Δ)

m-split-split-l :
  ∀{m m' n n'} ->
  MSplit m n m' ->
  MSplit n #1 n' ->
  ∃[ r ] (MSplit r n' m' × MSplit m #1 r)
m-split-split-l sp1 sp2 =
  let _ , sp1 , sp2 = msplit-assoc-lr sp1 sp2 in
  _ , sp2 , sp1

m-split-split-r :
  ∀{m m' n n'} ->
  MSplit m m' n ->
  MSplit n #1 n' ->
  ∃[ r ] (MSplit r m' n' × MSplit m #1 r)
m-split-split-r sp1 sp2 =
  let _ , sp2 , sp1 = msplit-assoc-rl sp1 sp2 in
  let sp1 = msplit-comm sp1 in
  let _ , sp1 , sp2 = msplit-assoc-lr sp2 sp1 in
  _ , sp2 , sp1

!-reduction :
  ∀{k Γ t}
  -> Var k Γ (Chan #0 #1 t) _
  -> ∃[ Δ ] ((Γ == L! k => Δ) × CNull Δ)
!-reduction {_} {_ # _ :: Γ} {t} (var-here cz) =
  (Chan #0 #0 t # _ :: Γ) , !-here split10 , null-c :: cz
!-reduction {_} {s # _ :: _} (var-next sz x) =
  let Δ , cout , cz = !-reduction x in
  (s # _ :: Δ) , !-next cout , sz :: cz

?-reduction :
  ∀{k Γ t}
  -> Var k Γ (Chan #1 #0 t) _
  -> ∃[ Δ ] ((Γ == L? k => Δ) × CNull Δ)
?-reduction {_} {_ # _ :: Γ} {t} (var-here cz) =
  (Chan #0 #0 t # _ :: Γ) , ?-here split10 , null-c :: cz
?-reduction {_} {s # _ :: _} (var-next sz x) =
  let Δ , cinp , cz = ?-reduction x in
  (s # _ :: Δ) , ?-next cinp , sz :: cz

#-reduction :
  ∀{Γ Γ1 Γ2 Δ1 Δ2 k}
  -> CSplit Γ Γ1 Γ2
  -> Γ1 == L! k => Δ1
  -> Γ2 == L? k => Δ2
  -> ∃[ Δ ] ((Γ == L# k => Δ) × CSplit Δ Δ1 Δ2)
#-reduction (split-c ms ns :: sp) (!-here rs) (?-here ss) =
  let _ , ns' , rs' = m-split-split-l ns rs in
  let _ , ms' , ss' = m-split-split-r ms ss in
  _ , #-here ss' rs' , split-c ms' ns' :: sp
#-reduction (ts :: sp) (!-next cr1) (?-next cr2) =
  let _ , cr , sp' = #-reduction sp cr1 cr2 in
  _ , #-next cr , ts :: sp'

split-reduction :
  ∀{Γ Γ1 Γ2 Δ1 l}
  -> CSplit Γ Γ1 Γ2
  -> Γ1 == l => Δ1
  -> ∃[ Δ ] ((Γ == l => Δ) × CSplit Δ Δ1 Γ2)
split-reduction {Γ} sp tau = Γ , tau , sp
split-reduction (split-c ms ns :: sp) (?-here rs) =
  let _ , ms' , rs' = m-split-split-l ms rs in
  _ , ?-here rs' , split-c ms' ns :: sp
split-reduction (split-c ms ns :: sp) (!-here rs) =
  let _ , ns' , rs' = m-split-split-l ns rs in
  _ , !-here rs' , split-c ms ns' :: sp
split-reduction (split-c ms ns :: sp) (#-here rs ss) =
  let _ , ms' , rs' = m-split-split-l ms rs in
  let _ , ns' , ss' = m-split-split-l ns ss in
  _ , #-here rs' ss' , split-c ms' ns' :: sp
split-reduction (ts :: sp) (?-next cr) =
  let _ , tr' , sp' = split-reduction sp cr in
  _ , ?-next tr' , ts :: sp'
split-reduction (ts :: sp) (!-next cr) =
  let Δ , tr' , sp' = split-reduction sp cr in
  _ , !-next tr' , ts :: sp'
split-reduction (ts :: sp) (#-next cr) =
  let Δ , tr' , sp' = split-reduction sp cr in
  _ , #-next tr' , ts :: sp'

tsplit-type-eq :
  ∀{t t1 t2 t11 t12 t21 t22 m1 n1 m2 n2 v v1 v2 v12 v22}
  -> TSplit t t1 t2 v v1 v2
  -> TSplit t1 (Chan m1 n1 t11) t12 v1 _ v12
  -> TSplit t2 (Chan m2 n2 t21) t22 v2 _ v22
  -> t11 ≡ t21
tsplit-type-eq (split-c _ _) (split-c _ _) (split-c _ _) = refl

csplit-type-eq :
  ∀{k Γ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22 m1 n1 m2 n2 t s}
  -> CSplit Γ Γ1 Γ2
  -> CSplit Γ1 Γ11 Γ12
  -> CSplit Γ2 Γ21 Γ22
  -> Var k Γ11 (Chan m1 n1 t) _
  -> Var k Γ21 (Chan m2 n2 s) _
  -> t ≡ s
csplit-type-eq (ts :: _)
               (ts1 :: _)
               (ts2 :: _)
               (var-here _)
               (var-here _) = tsplit-type-eq ts ts1 ts2
csplit-type-eq (_ :: sp)
               (_ :: sp1)
               (_ :: sp2)
               (var-next _ x)
               (var-next _ y) = csplit-type-eq sp sp1 sp2 x y

sync :
  ∀{k Γ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22 t s} ->
  CSplit Γ Γ1 Γ2 ->
  CSplit Γ1 Γ11 Γ12 ->
  CSplit Γ2 Γ21 Γ22 ->
  Var k Γ11 (Chan #0 #1 t) _ ->
  Var k Γ21 (Chan #1 #0 s) _ ->
  ∃[ Δ ] ((Γ == L# k => Δ) × CSplit Δ Γ12 Γ22)
sync {_} {_} {Γ1} {Γ2} {_} {Γ12} {_} {Γ22} sp sp1 sp2 x y =
  let Δ11 , ocr , cz1 = !-reduction x in
  let Δ21 , icr , cz2 = ?-reduction y in
  let Δ1 , otr' , sp1' = split-reduction sp1 ocr in
  let Δ2 , itr' , sp2' = split-reduction sp2 icr in
  -- ocr  : CReduction k O Γ11 Δ11
  -- otr' : CReduction k O Γ1 Δ1
  -- icr  : CReduction k I Γ21 Δ21
  -- itr' : CReduction k I Γ2 Δ2
  -- sp1' : CSplit Δ1 Δ11 Γ12
  -- sp2' : CSplit Δ2 Δ21 Γ22
  let eq1 = c-split-null-eq-r sp1' cz1 -- eq1 : Δ1 ≡ Γ12
      eq2 = c-split-null-eq-r sp2' cz2 -- eq2 : Δ2 ≡ Γ22
  in
  let Δ , cr , sp' = #-reduction sp otr' itr' in
  let sp'' : CSplit Δ Γ12 Γ22
      sp'' = subst₂ (CSplit Δ) eq1 eq2 sp' in
  Δ , cr , sp''

cast-pure : ∀{t s} -> t ≡ s -> ⟦ t ⟧ -> ⟦ s ⟧
cast-pure refl v = v

cast-term : ∀{Γ t s v} -> (eq : t ≡ s) -> Term Γ t v -> Term Γ s (cast-pure eq v)
cast-term refl E = E

data _~~_~>_ : ∀{l Γ Δ} -> Process Γ -> (Γ == l => Δ) -> Process Δ -> Set₁ where
  r-com :
    ∀{k Γ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22 t s v}
    (sp  : CSplit Γ Γ1 Γ2)
    (sp1 : CSplit Γ1 Γ11 Γ12)
    (sp2 : CSplit Γ2 Γ21 Γ22)
    (x   : Var k Γ11 (Chan #0 #1 t) _)
    (y   : Var k Γ21 (Chan #1 #0 s) _)
    (M   : Term Γ12 (t .force) v)
    (F   : (w : ⟦ s .force ⟧) -> Process (s .force # w :: Γ22)) ->
    let _ , α , sp' = sync sp sp1 sp2 x y in
    let teq = csplit-type-eq sp sp1 sp2 x y in
    let N = cast-term (cong (λ p -> p .force) teq) M in
    Par sp (Send sp1 (var x) M) (Recv sp2 (var y) F)
    ~~ α ~>
    subst-process sp' N insert-here (F (cast-pure (cong (λ p -> p .force) teq) v))
  r-let :
    ∀{Γ Γ1 Γ2 Γ11 Γ12 t}
    (f   : ⟦ t ⟧ -> Type)
    (sp1 : CSplit Γ Γ1 Γ2)
    (sp2 : CSplit Γ1 Γ11 Γ12)
    {p   : ⟦ t ⟧}
    {q   : ⟦ f p ⟧}
    {M   : Term Γ11 t p}
    {N   : Term Γ12 (f p) q}
    (P   : Process (t # p :: (f p # q :: Γ2))) ->
    let _ , sp1' , sp2' = csplit-assoc-lr sp1 (csplit-comm sp2) in
    let _ , _ , dnull , ds = tsplit-r (f p) in
    let M' = weaken-term (weaken-here dnull) M in
    let P1 = subst-process (ds :: sp2') M' insert-here P in
    Let sp1 (pair {f = f} sp2 M N) P ~~ tau ~> subst-process sp1' N insert-here P1
  r-par :
    ∀{Γ Γ1 Δ1 Γ2 l}
    {P  : Process Γ1}
    {Q  : Process Δ1}
    {R  : Process Γ2}
    (sp : CSplit Γ Γ1 Γ2)
    (α  : Γ1 == l => Δ1) ->
    P ~~ α ~> Q ->
    let _ , β , sp' = split-reduction sp α in
    Par sp P R ~~ β ~> Par sp' Q R
  r-new-tau :
    ∀{Γ σ ρ t}
    {P : Process (Chan σ ρ t # _ :: Γ)}
    {Q : Process (Chan σ ρ t # _ :: Γ)} ->
    P ~~ tau ~> Q ->
    New P ~~ tau ~> New Q
  r-new-here :
    ∀{Γ σ1 ρ1 σ2 ρ2 t}
    {P : Process (Chan σ1 ρ1 t # _ :: Γ)}
    {Q : Process (Chan σ2 ρ2 t # _ :: Γ)}
    (α : (Chan σ1 ρ1 t # _ :: Γ) == L# zero => (Chan σ2 ρ2 t # _ :: Γ)) ->
    P ~~ α ~> Q ->
    New P ~~ tau ~> New Q
  r-new-next :
    ∀{Γ Δ σ ρ t k}
    {P : Process (Chan σ ρ t # _ :: Γ)}
    {Q : Process (Chan σ ρ t # _ :: Δ)}
    (α : Γ == L# k => Δ) ->
    P ~~ #-next α ~> Q ->
    New P ~~ α ~> New Q
  r-struct :
    ∀{Γ Δ l}
    {P P' : Process Γ}
    {Q' Q : Process Δ}
    (α : Γ == l => Δ) ->
    P <= P' ->
    P' ~~ α ~> Q' ->
    Q' <= Q ->
    P ~~ α ~> Q
