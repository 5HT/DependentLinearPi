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
open import Relation.Nullary.Negation using (contraposition)
open import Data.Nat.Properties using (0≢1+n; 1+n≢0; suc-injective)
open import Data.Empty using (⊥-elim)
open import Data.Product
open import Codata.Thunk
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common
open import Language
open import Split
open import Scale

module Weaken where

{- Context weakening -}

data Weaken : ℕ -> Context -> Context -> Set₁ where
  here : ∀{Γ t v} -> TNull t -> Weaken zero Γ (t # v :: Γ)
  next : ∀{n Γ Δ mt v} -> Weaken n Γ Δ -> Weaken (suc n) (mt # v :: Γ) (mt # v :: Δ)

{- Does not occur -}

data NotInTerm : ∀{Γ t v} -> ℕ -> Term Γ t v -> Set₁ where
  nin-v : ∀{Γ t v k n}{x : Name k Γ t v} -> n ≢ k -> NotInTerm n (name x)
  nin-n : ∀{Γ A n} -> (cnull : CNull Γ) -> (c : A) -> NotInTerm n (pure cnull c)
  nin-p :
    ∀{Γ Γ1 Γ2 n}{t : Type}{f : ⟦ t ⟧ -> Type}{v w}
     {V1 : Term Γ1 t v}
     {V2 : Term Γ2 (f v) w} ->
     (sp : CSplit Γ Γ1 Γ2) ->
     NotInTerm n V1 ->
     NotInTerm n V2 ->
     NotInTerm n (pair {f = f} sp V1 V2)

data NotInProcess : ∀{Γ} -> ℕ -> Process Γ -> Set₁ where
  nin-idle :
    ∀{Γ n}
    {cnull : CNull Γ} ->
    NotInProcess n (Idle cnull)
  nin-send :
    ∀{Γ Γ1 Γ2 k t v}{M : Term Γ1 (Chan #0 #1 t) _}{N : Term Γ2 (t .force) v} ->
    (sp : CSplit Γ Γ1 Γ2) ->
    NotInTerm k M ->
    NotInTerm k N ->
    NotInProcess k (Send sp M N)
  nin-recv :
    ∀{Γ Γ1 Γ2 t k F}{e : Term Γ1 (Chan #1 #0 t) _} ->
    (sp : CSplit Γ Γ1 Γ2) ->
    NotInTerm k e ->
    ((x : ⟦ t .force ⟧) -> NotInProcess (suc k) (F x)) ->
    NotInProcess k (Recv sp e F)
  nin-par :
    ∀{Γ Γ1 Γ2 k P Q} ->
    (sp : CSplit Γ Γ1 Γ2) ->
    NotInProcess k P ->
    NotInProcess k Q ->
    NotInProcess k (Par sp P Q)
  nin-new :
    ∀{Γ m n t k P} ->
    NotInProcess (suc k) P ->
    NotInProcess k (New {Γ} {m} {n} {t} P)
  nin-rep :
    ∀{Γ Δ k}{P : Process Γ} ->
    (sc : CScale Γ Δ) ->
    NotInProcess k P ->
    NotInProcess k (Rep sc P)
  nin-let :
    ∀{k Γ Γ1 Γ2 t}{f : ⟦ t ⟧ -> Type}{v w}{E : Term Γ1 (Pair t f) (v , w)}
    {P : Process (t # v :: f v # w :: Γ2)} →
    (sp : CSplit Γ Γ1 Γ2) →
    NotInTerm k E →
    NotInProcess (suc (suc k)) P →
    NotInProcess k (Let sp E P)

{- Weakening -}

weaken-null : ∀{n Γ Δ} -> Weaken n Γ Δ -> CNull Γ -> CNull Δ
weaken-null (here tnull) null = tnull :: null
weaken-null (next we) (tnull :: null) = tnull :: weaken-null we null

weaken-scale :
  ∀{n Γ Γ' Δ'} ->
  Weaken n Γ' Δ' ->
  CScale Γ Γ' ->
  ∃[ Δ ] (Weaken n Γ Δ × CScale Δ Δ')
weaken-scale (here tnull) cscale =
  _ , here tnull , t-null-scale tnull :: cscale
weaken-scale (next we) (tscale :: cscale) =
  let _ , we' , cscale' = weaken-scale we cscale in
  _ , next we' , tscale :: cscale'

weaken-split :
  ∀{n Γ Γ1 Γ2 Δ} ->
  Weaken n Γ Δ ->
  CSplit Γ Γ1 Γ2 ->
  ∃[ Δ1 ] ∃[ Δ2 ] (CSplit Δ Δ1 Δ2 × Weaken n Γ1 Δ1 × Weaken n Γ2 Δ2)
weaken-split (here tz) sp =
  _ , _ , t-null-split tz :: sp , here tz , here tz
weaken-split (next we) (ts :: sp) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  _ , _ , ts :: sp' , next we1 , next we2

weaken-name-index : ℕ -> ℕ -> ℕ
weaken-name-index zero k = suc k
weaken-name-index (suc n) zero = zero
weaken-name-index (suc n) (suc k) = suc (weaken-name-index n k)

weaken-name : ∀{n k Γ Δ t v} -> Weaken n Γ Δ -> Name k Γ t v -> Name (weaken-name-index n k) Δ t v
weaken-name (here tnull) x = next tnull x
weaken-name (next we) (here null) = here (weaken-null we null)
weaken-name (next we) (next tnull x) = next tnull (weaken-name we x)

weaken-term : ∀{n Γ Δ t v} -> Weaken n Γ Δ -> Term Γ t v -> Term Δ t v
weaken-term we (name x) = name (weaken-name we x)
weaken-term we (pure cnull c) = pure (weaken-null we cnull) c
weaken-term we (pair sp E1 E2) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  pair sp' (weaken-term we1 E1) (weaken-term we2 E2)

weaken-process : ∀{n Γ Δ} -> Weaken n Γ Δ -> Process Γ -> Process Δ
weaken-process we (Idle cnull) = Idle (weaken-null we cnull)
weaken-process we (Send sp ec em) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  Send sp' (weaken-term we1 ec) (weaken-term we2 em)
weaken-process we (Recv sp e f) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  Recv sp' (weaken-term we1 e) (λ x -> weaken-process (next we2) (f x))
weaken-process we (Par sp P Q) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  Par sp' (weaken-process we1 P) (weaken-process we2 Q)
weaken-process we (New P) = New (weaken-process (next we) P)
weaken-process we (Rep sc P) =
  let _ , we' , sc' = weaken-scale we sc in
  Rep sc' (weaken-process we' P)
weaken-process we (Let sp E P) =
   let _ , _ , sp' , we1 , we2 = weaken-split we sp in
   Let sp' (weaken-term we1 E)
           (weaken-process (next (next we2)) P)

{- Strengthening -}

strengthen-null : ∀{n Γ Δ} -> Weaken n Γ Δ -> CNull Δ -> CNull Γ
strengthen-null (here _) (_ :: cnull) = cnull
strengthen-null (next we) (tz :: cnull) = tz :: strengthen-null we cnull

strengthen-scale :
  ∀{n Γ' Δ Δ'} ->
  Weaken n Γ' Δ' ->
  CScale Δ Δ' ->
  ∃[ Γ ] (Weaken n Γ Δ × CScale Γ Γ')
strengthen-scale (here tnull) (tsc :: sc) =
  _ , here (t-null-scale-null tnull tsc) , sc
strengthen-scale (next we) (tsc :: sc) =
  let _ , we' , sc' = strengthen-scale we sc in
  _ , next we' , tsc :: sc'

strengthen-split :
  ∀{n Γ Δ Δ1 Δ2}
  -> Weaken n Γ Δ
  -> CSplit Δ Δ1 Δ2
  -> ∃[ Γ1 ] ∃[ Γ2 ] (CSplit Γ Γ1 Γ2 × Weaken n Γ1 Δ1 × Weaken n Γ2 Δ2)
strengthen-split (here tnull) (ts :: sp) =
  let tnull1 , tnull2 = t-null-split-null-null tnull ts in
  _ , _ , sp , here tnull1 , here tnull2
strengthen-split (next we) (ts :: sp) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  _ , _ , ts :: sp' , next we1 , next we2

strengthen-split-eq :
  ∀{n Γ Δ Δ'}
  -> Weaken n Γ Δ
  -> CSplit Δ Δ' Δ'
  -> ∃[ Γ' ] (CSplit Γ Γ' Γ' × Weaken n Γ' Δ')
strengthen-split-eq (here tnull) (ts :: sp) =
  let tnull1 , tnull2 = t-null-split-null-null tnull ts in
  _ , sp , here tnull1
strengthen-split-eq (next we) (ts :: sp) =
  let _ , sp' , we' = strengthen-split-eq we sp in
  _ , ts :: sp' , next we'

strengthen-name-index : (l : ℕ) -> (k : ℕ) -> l ≢ k -> ℕ
strengthen-name-index zero zero neq = ⊥-elim (neq refl)
strengthen-name-index zero (suc k) _ = k
strengthen-name-index (suc l) zero _ = zero
strengthen-name-index (suc l) (suc k) neq = suc (strengthen-name-index l k (suc-≢ neq))

strengthen-name : ∀{k n Γ Δ t v} -> Weaken n Γ Δ -> Name k Δ t v -> (neq : n ≢ k) -> Name (strengthen-name-index n k neq) Γ t v
strengthen-name (here _) (here _) neq = ⊥-elim (neq refl)
strengthen-name (here _) (next _ x) _ = x
strengthen-name (next we) (here cnull) _ = here (strengthen-null we cnull)
strengthen-name (next we) (next tu x) neq = next tu (strengthen-name we x (suc-≢ neq))

strengthen-term : ∀{n Γ Δ t v} -> Weaken n Γ Δ -> (V : Term Δ t v) -> NotInTerm n V -> Term Γ t v
strengthen-term we (name x) (nin-v neq) = name (strengthen-name we x neq)
strengthen-term we (pure cnull c) ni = pure (strengthen-null we cnull) c
strengthen-term we (pair sp E1 E2) (nin-p _ nie1 nie2) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  pair sp' (strengthen-term we1 E1 nie1) (strengthen-term we2 E2 nie2)

strengthen-process :
  ∀{k Γ Δ} ->
  Weaken k Γ Δ ->
  (P : Process Δ) ->
  NotInProcess k P ->
  Process Γ
strengthen-process we (Idle cnull) _ = Idle (strengthen-null we cnull)
strengthen-process we (Send sp ec em) (nin-send _ nic nim) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  Send sp' (strengthen-term we1 ec nic) (strengthen-term we2 em nim)
strengthen-process we (Recv sp e f) (nin-recv _ nie niP) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  Recv sp' (strengthen-term we1 e nie) (λ x -> strengthen-process (next we2) (f x) (niP x))
strengthen-process we (Par sp P Q) (nin-par _ niP niQ) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  Par sp' (strengthen-process we1 P niP) (strengthen-process we2 Q niQ)
strengthen-process we (New P) (nin-new ni) =
  New (strengthen-process (next we) P ni)
strengthen-process we (Rep sc P) (nin-rep _ niP) =
  let _ , we' , sc' = strengthen-scale we sc in
  Rep sc' (strengthen-process we' P niP)
strengthen-process we (Let sp E P) (nin-let _ niE niP) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  Let sp' (strengthen-term we1 E niE)
          (strengthen-process (next (next we2)) P niP)

{- Weakened name does not occur -}

not-in-weakened-name : ∀{k n Γ Δ t v} -> Weaken n Γ Δ -> Name k Γ t v -> n ≢ weaken-name-index n k
not-in-weakened-name (here _) _ = 0≢1+n
not-in-weakened-name (next _) (here _) = 1+n≢0
not-in-weakened-name (next we) (next _ x) = contraposition suc-injective (not-in-weakened-name we x)

not-in-weakened-term :
  ∀{n Γ Δ t p} ->
  (we : Weaken n Γ Δ) ->
  (M : Term Γ t p) ->
  NotInTerm n (weaken-term we M)
not-in-weakened-term we (name x) = nin-v (not-in-weakened-name we x)
not-in-weakened-term we (pure cnull c) = nin-n (weaken-null we cnull) c
not-in-weakened-term we (pair sp E1 E2) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  nin-p sp' (not-in-weakened-term we1 E1) (not-in-weakened-term we2 E2)

not-in-weakened-process :
  ∀{n Γ Δ} ->
  (we : Weaken n Γ Δ) ->
  (P : Process Γ) ->
  NotInProcess n (weaken-process we P)
not-in-weakened-process we (Idle _) = nin-idle
not-in-weakened-process we (Send sp ec em) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  nin-send sp' (not-in-weakened-term we1 ec) (not-in-weakened-term we2 em)
not-in-weakened-process we (Recv sp e f) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  nin-recv sp' (not-in-weakened-term we1 e) (λ x -> not-in-weakened-process (next we2) (f x))
not-in-weakened-process we (Par sp P Q) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  nin-par sp' (not-in-weakened-process we1 P) (not-in-weakened-process we2 Q)
not-in-weakened-process we (New P) = nin-new (not-in-weakened-process (next we) P)
not-in-weakened-process we (Rep sc P) =
  let _ , we' , sc' = weaken-scale we sc in
  nin-rep sc' (not-in-weakened-process we' P)
not-in-weakened-process we (Let sp E P) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  nin-let sp' (not-in-weakened-term we1 E)
              (not-in-weakened-process (next (next we2)) P)
