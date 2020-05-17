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
open import Multiplicity
open import Type
open import Context
open import Language
open import Weakening
open import Scaling

data Insert : ℕ -> (t : Type) -> ⟦ t ⟧ -> Context -> Context -> Set where
  insert-here : ∀{Γ t v} -> Insert zero t v Γ (t # v :: Γ)
  insert-next : ∀{Γ Δ t s v w k} -> Insert k t v Γ Δ -> Insert (suc k) t v (s # w :: Γ) (s # w :: Δ)

split-insert : ∀{Γ Δ Δ1 Δ2 k t v}
  -> CSplit Δ Δ1 Δ2
  -> Insert k t v Γ Δ
  -> ∃[ t1 ] ∃[ t2 ] ∃[ Γ1 ] ∃[ Γ2 ] ∃[ v1 ] ∃[ v2 ]
     (TSplit t t1 t2 v v1 v2 × CSplit Γ Γ1 Γ2 × Insert k t1 v1 Γ1 Δ1 × Insert k t2 v2 Γ2 Δ2)
split-insert (ts :: sp) insert-here =
  _ , _ , _ , _ , _ , _ , ts , sp , insert-here , insert-here
split-insert (ss :: sp) (insert-next ins) =
  let _ , _ , _ , _ , _ , _ , ts , sp' , ins1 , ins2 = split-insert sp ins in
  _ , _ , _ , _ , _ , _ , ts , ss :: sp' , insert-next ins1 , insert-next ins2

insert-null-null-null :
  ∀{k t Γ Δ v} ->
  Insert k t v Γ Δ ->
  CNull Δ ->
  TNull t × CNull Γ
insert-null-null-null insert-here (tz :: cnull) = tz , cnull
insert-null-null-null (insert-next ins) (sz :: cnull) =
  let tz , cnull' = insert-null-null-null ins cnull in
  tz , sz :: cnull'

var-null-null : ∀{k Γ t v} -> Var k Γ t v -> TNull t -> CNull Γ
var-null-null (var-here cnull) tz = tz :: cnull
var-null-null (var-next sz x) tz = sz :: var-null-null x tz

term-null-null : ∀{Γ t v} -> Term Γ t v -> TNull t -> CNull Γ
term-null-null (var x) tnull = var-null-null x tnull
term-null-null (pure null _) null-p = null

split-var : ∀{k Γ t t1 t2 v v1 v2}
  -> TSplit t t1 t2 v v1 v2
  -> Var k Γ t v
  -> ∃[ Γ1 ] ∃[ Γ2 ] (CSplit Γ Γ1 Γ2 × Var k Γ1 t1 v1 × Var k Γ2 t2 v2)
split-var tsp (var-here null) = _ , _ , tsp :: (c-null-split null) , var-here null , var-here null
split-var tsp (var-next snull x) =
  let _ , _ , sp , x1 , x2 = split-var tsp x in
  _ , _ , t-null-split snull :: sp , var-next snull x1 , var-next snull x2

split-term :
  ∀{Γ t t1 t2 v v1 v2} ->
  TSplit t t1 t2 v v1 v2 ->
  Term Γ t v ->
  ∃[ Γ1 ] ∃[ Γ2 ] (CSplit Γ Γ1 Γ2 × Term Γ1 t1 v1 × Term Γ2 t2 v2)
split-term sp (var x) with split-var sp x
... | _ , _ , csp , x1 , x2 = _ , _ , csp , var x1 , var x2
split-term split-p E@(pure null c) =
  _ , _ , c-null-split null , E , E
split-term {Γ} (split-l lin) E =
  let _ , null , sp = csplit-l Γ in
  _ , _ , sp , E , pure null tt
split-term {Γ} (split-r lin) E =
  let _ , null , sp = csplit-r Γ in
  _ , _ , sp , pure null tt , E

m-split-zero-eq-l : ∀{m n} -> MSplit m n #0 -> m ≡ n
m-split-zero-eq-l split00 = refl
m-split-zero-eq-l split10 = refl
m-split-zero-eq-l splitω0 = refl

m-split-zero-eq-r : ∀{m n} -> MSplit m #0 n -> m ≡ n
m-split-zero-eq-r split00 = refl
m-split-zero-eq-r split01 = refl
m-split-zero-eq-r split0ω = refl

t-split-null-eq-r : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t1 -> t ≡ t2
t-split-null-eq-r split-p null-p = refl
t-split-null-eq-r (split-l ()) null-p
t-split-null-eq-r (split-l ()) null-c
t-split-null-eq-r (split-r lin-p) null-p = refl
t-split-null-eq-r (split-c σs ρs) null-c =
  cong₂ (λ σ ρ -> Chan σ ρ _) (m-split-zero-eq-r σs) (m-split-zero-eq-r ρs)

t-split-null-eq-rr : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TNull t1 -> t ≡ t2 × v ≅ v2
t-split-null-eq-rr split-p null-p = refl , _≅_.refl
t-split-null-eq-rr (split-l ()) null-p
t-split-null-eq-rr (split-l ()) null-c
t-split-null-eq-rr (split-r lin-p) null-p = refl , _≅_.refl
t-split-null-eq-rr (split-c σs ρs) null-c =
  cong₂ (λ σ ρ -> Chan σ ρ _) (m-split-zero-eq-r σs) (m-split-zero-eq-r ρs) , _≅_.refl

t-split-eq-rv :
  ∀{t t1 v v1 v2} ->
  TSplit t t1 t v v1 v2 ->
  v ≡ v2
t-split-eq-rv split-p = refl
t-split-eq-rv (split-r _) = refl
t-split-eq-rv (split-c _ _) = refl

t-split-eq-lv :
  ∀{t t2 v v1 v2} ->
  TSplit t t t2 v v1 v2 ->
  v ≡ v1
t-split-eq-lv split-p = refl
t-split-eq-lv (split-l _ ) = refl
t-split-eq-lv (split-c _ _) = refl

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
  not-found : ∀{k t v Γ Δ s w} -> TNull t -> Var k Γ s w -> SubstitutionResult t v Γ Δ s w

subst-result :
  ∀{Γ Δ k l t s v w}
  -> Insert l t v Γ Δ
  -> Var k Δ s w
  -> SubstitutionResult t v Γ Δ s w
subst-result insert-here (var-here cnull) = found cnull
subst-result insert-here (var-next tz x) = not-found tz x
subst-result (insert-next ins) (var-here cnull) =
  let tz , cnull = insert-null-null-null ins cnull in
  not-found tz (var-here cnull)
subst-result (insert-next ins) (var-next sz x) with subst-result ins x
... | found cnull = found (sz :: cnull)
... | not-found tu y = not-found tu (var-next sz y)

insert-null-weaken : ∀{k Γ Δ t v} -> TNull t -> Insert k t v Γ Δ -> Weaken k Γ Δ
insert-null-weaken tz insert-here = weaken-here tz
insert-null-weaken tz (insert-next ins) = weaken-next (insert-null-weaken tz ins)

insert-scale :
  ∀{k t Γ' Δ Δ' v} ->
  Insert k t v Γ' Δ' ->
  CScale Δ Δ' ->
  ∃[ s ] ∃[ w ] ∃[ Γ ] (Insert k s w Γ Δ × TScale s t w v × CScale Γ Γ')
insert-scale insert-here (tsc :: sc) = _ , _ , _ , insert-here , tsc , sc
insert-scale (insert-next ins) (ssc :: sc) =
  let _ , _ , _ , ins' , tsc , sc' = insert-scale ins sc in
  _ , _ , _ , insert-next ins' , tsc , ssc :: sc'

subst-var :
  ∀{Γ Δ Γ1 Γ2 k l t s v w}
  -> CSplit Γ Γ1 Γ2
  -> Term Γ1 t v
  -> Insert l t v Γ2 Δ
  -> Var k Δ s w
  -> Term Γ s w
subst-var sp V ins x with subst-result ins x
... | found cnull rewrite c-split-null-eq-l sp cnull = V
... | not-found tz y =
  let we = insert-null-weaken tz ins in
  let cnull = term-null-null V tz in
  subst (λ Γ' -> Term Γ' _ _) (sym (c-split-null-eq-r sp cnull)) (var y)

subst-term :
  ∀{Γ Δ Γ1 Γ2 k t s v w} ->
  CSplit Γ Γ1 Γ2 ->
  Term Γ1 t v ->
  Insert k t v Γ2 Δ ->
  Term Δ s w ->
  Term Γ s w
subst-term sp E ins (var x) = subst-var sp E ins x
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
                                 (weaken-term (weaken-here snull) V2) (insert-next insP) (f v))
subst-process sp V ins (Par psp P Q) with split-insert psp ins
... | _ , _ , _ , _ , _ , _ , tsp , psp' , insP , insQ with split-term tsp V
... | _ , _ , esp' , V1 , V2 =
  let _ , _ , sp' , spP , spQ = c-split-split-split sp esp' psp' in
  Par sp' (subst-process spP V1 insP P) (subst-process spQ V2 insQ Q)
subst-process sp e ins (New {_} {m} {n} P) =
  New (subst-process (split-c (msplit-r m) (msplit-r n) :: sp)
                     (weaken-term (weaken-here null-c) e)
                     (insert-next ins) P)
subst-process sp e ins (Rep sc P) with insert-scale ins sc
... | _ , _ , _ , ins' , scale-p , sc2 =
  let _ , sc1 , F = scale-term scale-p e in
  let _ , sc' , sp' = c-split-scale-scale sp sc1 sc2 in
  Rep sc' (subst-process sp' F ins' P)
... | _ , _ , _ , ins' , tsc@(scale-c _ _) , sc2 =
  let _ , sc1 , F = scale-term tsc e in
  let _ , sc' , sp' = c-split-scale-scale sp sc1 sc2 in
  Rep sc' (subst-process sp' F ins' P)
subst-process sp E ins (Let {t = t} {ft} sp1 F g) with split-insert sp1 ins
... | _ , _ , _ , _ , _ , _ , tsp , sp1' , ins1 , ins2 with split-term tsp E
... | _ , _ , esp' , E1 , E2 =
  let _ , _ , sp' , sp1 , sp2 = c-split-split-split sp esp' sp1' in
  let F = subst-term sp1 E1 ins1 F in
  Let sp' F
          λ v w -> let _ , _ , tnull , ts = tsplit-r t in
                   let _ , _ , dnull , ds = tsplit-r (ft _) in
                   subst-process (ts :: ds :: sp2)
                                 (weaken-term (weaken-here tnull) (weaken-term (weaken-here dnull) E2))
                                 (insert-next (insert-next ins2))
                                 (g v w)