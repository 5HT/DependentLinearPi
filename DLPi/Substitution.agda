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

open import Data.Unit
open import Data.Nat
open import Data.Product
open import Codata.Thunk
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst)

open import Relation.Binary.HeterogeneousEquality using (_≅_)

open import Common
open import Language
open import Split
open import Scale
open import Weaken

data Insert : ℕ -> (t : Type) -> ⟦ t ⟧ -> Context -> Context -> Set where
  here : ∀{Γ t v} -> Insert zero t v Γ (t # v :: Γ)
  next : ∀{Γ Δ t s v w k} -> Insert k t v Γ Δ -> Insert (suc k) t v (s # w :: Γ) (s # w :: Δ)

split-insert :
  ∀{Γ Δ Δ1 Δ2 k t v} ->
  CSplit Δ Δ1 Δ2 ->
  Insert k t v Γ Δ ->
  ∃[ t1 ] ∃[ t2 ] ∃[ Γ1 ] ∃[ Γ2 ] ∃[ v1 ] ∃[ v2 ]
    (TSplit t t1 t2 v v1 v2 × CSplit Γ Γ1 Γ2 × Insert k t1 v1 Γ1 Δ1 × Insert k t2 v2 Γ2 Δ2)
split-insert (ts :: sp) here =
  _ , _ , _ , _ , _ , _ , ts , sp , here , here
split-insert (ss :: sp) (next ins) =
  let _ , _ , _ , _ , _ , _ , ts , sp' , ins1 , ins2 = split-insert sp ins in
  _ , _ , _ , _ , _ , _ , ts , ss :: sp' , next ins1 , next ins2

insert-null-null-null :
  ∀{k t Γ Δ v} ->
  Insert k t v Γ Δ ->
  CNull Δ ->
  TNull t × CNull Γ
insert-null-null-null here (tz :: cnull) = tz , cnull
insert-null-null-null (next ins) (sz :: cnull) =
  let tz , cnull' = insert-null-null-null ins cnull in
  tz , sz :: cnull'

name-null-null : ∀{k Γ t v} -> Name k Γ t v -> TNull t -> CNull Γ
name-null-null (here cnull) tz = tz :: cnull
name-null-null (next sz x) tz = sz :: name-null-null x tz

term-null-null : ∀{Γ t v} -> Term Γ t v -> TNull t -> CNull Γ
term-null-null (name x) tnull = name-null-null x tnull
term-null-null (pure null _) pure = null

split-name : ∀{k Γ t t1 t2 v v1 v2}
  -> TSplit t t1 t2 v v1 v2
  -> Name k Γ t v
  -> ∃[ Γ1 ] ∃[ Γ2 ] (CSplit Γ Γ1 Γ2 × Name k Γ1 t1 v1 × Name k Γ2 t2 v2)
split-name tsp (here null) = _ , _ , tsp :: (c-null-split null) , here null , here null
split-name tsp (next snull x) =
  let _ , _ , sp , x1 , x2 = split-name tsp x in
  _ , _ , t-null-split snull :: sp , next snull x1 , next snull x2

split-term :
  ∀{Γ t t1 t2 v v1 v2} ->
  TSplit t t1 t2 v v1 v2 ->
  Term Γ t v ->
  ∃[ Γ1 ] ∃[ Γ2 ] (CSplit Γ Γ1 Γ2 × Term Γ1 t1 v1 × Term Γ2 t2 v2)
split-term sp (name x) with split-name sp x
... | _ , _ , csp , x1 , x2 = _ , _ , csp , name x1 , name x2
split-term pure E@(pure null c) =
  _ , _ , c-null-split null , E , E
split-term {Γ} (left lin) E =
  let _ , null , sp = csplit-l Γ in
  _ , _ , sp , E , pure null tt
split-term {Γ} (right lin) E =
  let _ , null , sp = csplit-r Γ in
  _ , _ , sp , pure null tt , E

m-split-zero-eq-l : ∀{m n} -> MSplit m n #0 -> m ≡ n
m-split-zero-eq-l 0+0 = refl
m-split-zero-eq-l 1+0 = refl
m-split-zero-eq-l ω+0 = refl

m-split-zero-eq-r : ∀{m n} -> MSplit m #0 n -> m ≡ n
m-split-zero-eq-r 0+0 = refl
m-split-zero-eq-r 0+1 = refl
m-split-zero-eq-r 0+ω = refl

t-split-null-eq-r : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t1 -> t ≡ t2
t-split-null-eq-r pure pure = refl
t-split-null-eq-r (left ()) pure
t-split-null-eq-r (left ()) chan
t-split-null-eq-r (right lin-p) pure = refl
t-split-null-eq-r (chan σs ρs) chan =
  cong₂ (λ σ ρ -> Chan σ ρ _) (m-split-zero-eq-r σs) (m-split-zero-eq-r ρs)

t-split-null-eq-rr : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t1 -> t ≡ t2 × v ≅ v2
t-split-null-eq-rr pure pure = refl , _≅_.refl
t-split-null-eq-rr (left ()) pure
t-split-null-eq-rr (left ()) chan
t-split-null-eq-rr (right lin-p) pure = refl , _≅_.refl
t-split-null-eq-rr (chan σs ρs) chan =
  cong₂ (λ σ ρ -> Chan σ ρ _) (m-split-zero-eq-r σs) (m-split-zero-eq-r ρs) , _≅_.refl

t-split-eq-rv :
  ∀{t t1 v v1 v2} ->
  TSplit t t1 t v v1 v2 ->
  v ≡ v2
t-split-eq-rv pure = refl
t-split-eq-rv (right _) = refl
t-split-eq-rv (chan _ _) = refl

t-split-eq-lv :
  ∀{t t2 v v1 v2} ->
  TSplit t t t2 v v1 v2 ->
  v ≡ v1
t-split-eq-lv pure = refl
t-split-eq-lv (left _ ) = refl
t-split-eq-lv (chan _ _) = refl

t-split-null-eq-l : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t2 -> t ≡ t1
t-split-null-eq-l sp = t-split-null-eq-r (tsplit-comm sp)

t-split-null-eq-ll : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t2 -> t ≡ t1 × v ≅ v1
t-split-null-eq-ll sp = t-split-null-eq-rr (tsplit-comm sp)

c-split-null-eq-l : ∀{Γ Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> CNull Γ2 -> Γ ≡ Γ1
c-split-null-eq-l [] [] = refl
c-split-null-eq-l (ts :: cs) (tz :: cnull) =
  let teq , veq = t-split-null-eq-ll ts tz in
  let ceq = c-split-null-eq-l cs cnull in
  aux teq veq ceq
  where
    aux : ∀{t s}{v : ⟦ t ⟧}{w : ⟦ s ⟧}{Γ Δ} -> t ≡ s -> v ≅ w -> Γ ≡ Δ -> (t # v :: Γ) ≡ (s # w :: Δ)
    aux refl _≅_.refl refl = refl

c-split-null-eq-r : ∀{Γ Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> CNull Γ1 -> Γ ≡ Γ2
c-split-null-eq-r sp cnull = c-split-null-eq-l (csplit-comm sp) cnull

data SubstitutionResult : (t : Type) -> ⟦ t ⟧ -> Context -> Context -> (s : Type) -> ⟦ s ⟧ -> Set₁ where
  found : ∀{t v Γ Δ} -> CNull Γ -> SubstitutionResult t v Γ Δ t v
  not-found : ∀{k t v Γ Δ s w} -> TNull t -> Name k Γ s w -> SubstitutionResult t v Γ Δ s w

subst-result :
  ∀{Γ Δ k l t s v w}
  -> Insert l t v Γ Δ
  -> Name k Δ s w
  -> SubstitutionResult t v Γ Δ s w
subst-result here (here cnull) = found cnull
subst-result here (next tz x) = not-found tz x
subst-result (next ins) (here cnull) =
  let tz , cnull = insert-null-null-null ins cnull in
  not-found tz (here cnull)
subst-result (next ins) (next sz x) with subst-result ins x
... | found cnull = found (sz :: cnull)
... | not-found tu y = not-found tu (next sz y)

insert-null-weaken : ∀{k Γ Δ t v} -> TNull t -> Insert k t v Γ Δ -> Weaken k Γ Δ
insert-null-weaken tz here = here tz
insert-null-weaken tz (next ins) = next (insert-null-weaken tz ins)

scale-name :
  ∀{k Δ t s v w} ->
  TScale t s v w ->
  Name k Δ s w ->
  ∃[ Γ ] (CScale Γ Δ × Name k Γ t v)
scale-name sc (here null) = _ , sc :: c-null-scale null , here null
scale-name sc (next tnull x) =
  let _ , sc' , y = scale-name sc x in
  _ , t-null-scale tnull :: sc' , next tnull y

scale-term :
  ∀{Δ s t v w} ->
  TScale t s v w ->
  Term Δ s w ->
  ∃[ Γ ] (CScale Γ Δ × Term Γ t v)
scale-term sc (name x) =
  let _ , sc , x = scale-name sc x in
  _ , sc , name x
scale-term pure (pure null c) = _ , c-null-scale null , pure null c

insert-scale :
  ∀{k t Γ' Δ Δ' v} ->
  Insert k t v Γ' Δ' ->
  CScale Δ Δ' ->
  ∃[ s ] ∃[ w ] ∃[ Γ ] (Insert k s w Γ Δ × TScale s t w v × CScale Γ Γ')
insert-scale here (tsc :: sc) = _ , _ , _ , here , tsc , sc
insert-scale (next ins) (ssc :: sc) =
  let _ , _ , _ , ins' , tsc , sc' = insert-scale ins sc in
  _ , _ , _ , next ins' , tsc , ssc :: sc'

subst-name :
  ∀{Γ Δ Γ1 Γ2 k l t s v w}
  -> CSplit Γ Γ1 Γ2
  -> Term Γ1 t v
  -> Insert l t v Γ2 Δ
  -> Name k Δ s w
  -> Term Γ s w
subst-name sp V ins x with subst-result ins x
... | found cnull rewrite c-split-null-eq-l sp cnull = V
... | not-found tz y =
  let we = insert-null-weaken tz ins in
  let cnull = term-null-null V tz in
  subst (λ Γ' -> Term Γ' _ _) (sym (c-split-null-eq-r sp cnull)) (name y)

subst-term :
  ∀{Γ Δ Γ1 Γ2 k t s v w} ->
  CSplit Γ Γ1 Γ2 ->
  Term Γ1 t v ->
  Insert k t v Γ2 Δ ->
  Term Δ s w ->
  Term Γ s w
subst-term sp E ins (name x) = subst-name sp E ins x
subst-term sp V ins (pure cnull c) =
  let tnull , cnull' = insert-null-null-null ins cnull in
  pure (c-null-null-split-null (term-null-null V tnull) cnull' sp) c
subst-term sp V ins (pair sp1 F1 F2) with split-insert sp1 ins
... | _ , _ , _ , _ , _ , _ , tsp , sp1' , ins1 , ins2 with split-term tsp V
... | _ , _ , esp' , V1 , V2 =
  let _ , _ , sp' , sp1 , sp2 = c-split-split-split sp esp' sp1' in
  pair sp' (subst-term sp1 V1 ins1 F1) (subst-term sp2 V2 ins2 F2)

subst-process :
  ∀{Γ Δ Γ1 Γ2 t k v} ->
  CSplit Γ Γ1 Γ2 ->
  Term Γ1 t v ->
  Insert k t v Γ2 Δ ->
  Process Δ ->
  Process Γ
subst-process sp V ins (Idle cnull) =
  let tz , cnull' = insert-null-null-null ins cnull in
  Idle (c-null-null-split-null (term-null-null V tz) cnull' sp)
subst-process sp V ins (Send sp1 F1 F2) with split-insert sp1 ins
... | _ , _ , _ , _ , _ , _ , tsp , sp1' , ins1 , ins2 with split-term tsp V
... | _ , _ , esp' , V1 , V2 =
  let _ , _ , sp' , sp1 , sp2 = c-split-split-split sp esp' sp1' in
  let F1 = subst-term sp1 V1 ins1 F1 in
  let F2 = subst-term sp2 V2 ins2 F2 in
  Send sp' F1 F2
subst-process sp V ins (Recv {t = t} sp1 E f) with split-insert sp1 ins
... | _ , _ , _ , _ , _ , _ , tsp , sp1' , inse , insP with split-term tsp V
... | _ , _ , esp' , V1 , V2 =
  let _ , _ , sp' , spE , spP = c-split-split-split sp esp' sp1' in
  let E = subst-term spE V1 inse E in
  Recv sp' E
           λ v -> let _ , _ , snull , ts = tsplit-r (t .force) in
                  (subst-process (ts :: spP)
                                 (weaken-term (here snull) V2) (next insP) (f v))
subst-process sp V ins (Par psp P Q) with split-insert psp ins
... | _ , _ , _ , _ , _ , _ , tsp , psp' , insP , insQ with split-term tsp V
... | _ , _ , esp' , V1 , V2 =
  let _ , _ , sp' , spP , spQ = c-split-split-split sp esp' psp' in
  Par sp' (subst-process spP V1 insP P) (subst-process spQ V2 insQ Q)
subst-process sp e ins (New {_} {m} {n} P) =
  New (subst-process (chan (msplit-r m) (msplit-r n) :: sp)
                     (weaken-term (here chan) e)
                     (next ins) P)
subst-process sp e ins (Rep sc P) with insert-scale ins sc
... | _ , _ , _ , ins' , pure , sc2 =
  let _ , sc1 , F = scale-term pure e in
  let _ , sc' , sp' = c-split-scale-scale sp sc1 sc2 in
  Rep sc' (subst-process sp' F ins' P)
... | _ , _ , _ , ins' , tsc@(chan _ _) , sc2 =
  let _ , sc1 , F = scale-term tsc e in
  let _ , sc' , sp' = c-split-scale-scale sp sc1 sc2 in
  Rep sc' (subst-process sp' F ins' P)
subst-process sp E ins (Let {t = t} {ft} sp1 F P) with split-insert sp1 ins
... | _ , _ , _ , _ , _ , _ , tsp , sp1' , ins1 , ins2 with split-term tsp E
... | _ , _ , esp' , E1 , E2 =
  let _ , _ , sp' , sp1 , sp2 = c-split-split-split sp esp' sp1' in
  let _ , _ , tnull , ts = tsplit-r t in
  let _ , _ , dnull , ds = tsplit-r (ft _) in
  Let sp' (subst-term sp1 E1 ins1 F)
          (subst-process (ts :: ds :: sp2)
            (weaken-term (here tnull) (weaken-term (here dnull) E2))
            (next (next ins2))
            P)
