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

open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Language

module Split where

{- Splitting is commutative -}

msplit-comm : {σ σ1 σ2 : Multiplicity} -> MSplit σ σ1 σ2 -> MSplit σ σ2 σ1
msplit-comm 0+0 = 0+0
msplit-comm 0+1 = 1+0
msplit-comm 0+ω = ω+0
msplit-comm 1+0 = 0+1
msplit-comm 1+1 = 1+1
msplit-comm 1+ω = ω+1
msplit-comm ω+0 = 0+ω
msplit-comm ω+1 = 1+ω
msplit-comm ω+ω = ω+ω

tsplit-comm : ∀{t t1 t2 p p1 p2} -> TSplit t t1 t2 p p1 p2 -> TSplit t t2 t1 p p2 p1
tsplit-comm pure         = pure
tsplit-comm (left lin)   = right lin
tsplit-comm (right lin)  = left lin
tsplit-comm (chan σs ρs) = chan (msplit-comm σs) (msplit-comm ρs)

csplit-comm : ∀{Γ Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> CSplit Γ Γ2 Γ1
csplit-comm [] = []
csplit-comm (ts :: sp) = tsplit-comm ts :: csplit-comm sp

{- commutativity is involutive -}

msplit-comm-inv :
  ∀{σ σ1 σ2} -> (sp : MSplit σ σ1 σ2) -> msplit-comm (msplit-comm sp) ≡ sp
msplit-comm-inv 0+0 = refl
msplit-comm-inv 0+1 = refl
msplit-comm-inv 0+ω = refl
msplit-comm-inv 1+0 = refl
msplit-comm-inv 1+1 = refl
msplit-comm-inv 1+ω = refl
msplit-comm-inv ω+0 = refl
msplit-comm-inv ω+1 = refl
msplit-comm-inv ω+ω = refl

tsplit-comm-inv : ∀{t t1 t2 v v1 v2} -> (ts : TSplit t t1 t2 v v1 v2) -> tsplit-comm (tsplit-comm ts) ≡ ts
tsplit-comm-inv pure         = refl
tsplit-comm-inv (left _)     = refl
tsplit-comm-inv (right _)    = refl
tsplit-comm-inv (chan σs ρs) = cong₂ chan (msplit-comm-inv σs) (msplit-comm-inv ρs)

csplit-comm-inv : ∀{Γ Γ1 Γ2} (sp : CSplit Γ Γ1 Γ2) -> csplit-comm (csplit-comm sp) ≡ sp
csplit-comm-inv [] = refl
csplit-comm-inv (ts :: sp) = cong₂ _::_ (tsplit-comm-inv ts) (csplit-comm-inv sp)

{- Associativity -}

msplit-assoc-rl :
  ∀{σ σ1 σ23 σ2 σ3} ->
  MSplit σ σ1 σ23 ->
  MSplit σ23 σ2 σ3 ->
  ∃[ ρ ] (MSplit σ ρ σ3 × MSplit ρ σ1 σ2)
msplit-assoc-rl 0+0 0+0 = #0 , 0+0 , 0+0
msplit-assoc-rl 0+1 0+1 = #0 , 0+1 , 0+0
msplit-assoc-rl 0+1 1+0 = #1 , 1+0 , 0+1
msplit-assoc-rl 0+ω 0+ω = #0 , 0+ω , 0+0
msplit-assoc-rl 0+ω 1+1 = #1 , 1+1 , 0+1
msplit-assoc-rl 0+ω 1+ω = #1 , 1+ω , 0+1
msplit-assoc-rl 0+ω ω+0 = #ω , ω+0 , 0+ω
msplit-assoc-rl 0+ω ω+1 = #ω , ω+1 , 0+ω
msplit-assoc-rl 0+ω ω+ω = #ω , ω+ω , 0+ω
msplit-assoc-rl 1+0 0+0 = #1 , 1+0 , 1+0
msplit-assoc-rl 1+1 0+1 = #1 , 1+1 , 1+0
msplit-assoc-rl 1+1 1+0 = #ω , ω+0 , 1+1
msplit-assoc-rl 1+ω 0+ω = #1 , 1+ω , 1+0
msplit-assoc-rl 1+ω 1+1 = #ω , ω+1 , 1+1
msplit-assoc-rl 1+ω 1+ω = #ω , ω+ω , 1+1
msplit-assoc-rl 1+ω ω+0 = #ω , ω+0 , 1+ω
msplit-assoc-rl 1+ω ω+1 = #ω , ω+1 , 1+ω
msplit-assoc-rl 1+ω ω+ω = #ω , ω+ω , 1+ω
msplit-assoc-rl ω+0 0+0 = #ω , ω+0 , ω+0
msplit-assoc-rl ω+1 0+1 = #ω , ω+1 , ω+0
msplit-assoc-rl ω+1 1+0 = #ω , ω+0 , ω+1
msplit-assoc-rl ω+ω 0+ω = #ω , ω+ω , ω+0
msplit-assoc-rl ω+ω 1+1 = #ω , ω+1 , ω+1
msplit-assoc-rl ω+ω 1+ω = #ω , ω+ω , ω+1
msplit-assoc-rl ω+ω ω+0 = #ω , ω+0 , ω+ω
msplit-assoc-rl ω+ω ω+1 = #ω , ω+1 , ω+ω
msplit-assoc-rl ω+ω ω+ω = #ω , ω+ω , ω+ω

msplit-assoc-lr :
  ∀{σ σ12 σ1 σ2 σ3} ->
  MSplit σ σ12 σ3 ->
  MSplit σ12 σ1 σ2 ->
  ∃[ ρ ] (MSplit σ σ1 ρ × MSplit ρ σ2 σ3)
msplit-assoc-lr ms1 ms2 =
  let _ , ms1' , ms2' = msplit-assoc-rl (msplit-comm ms1) (msplit-comm ms2) in
  _ , msplit-comm ms1' , msplit-comm ms2'

tsplit-assoc-rl :
  ∀{t t1 t23 t2 t3 p p1 p23 p2 p3}
  -> TSplit t t1 t23 p p1 p23
  -> TSplit t23 t2 t3 p23 p2 p3
  -> ∃[ s ] ∃[ q ] (TSplit t s t3 p q p3 × TSplit s t1 t2 q p1 p2)
tsplit-assoc-rl pure pure = _ , _ , pure , pure
tsplit-assoc-rl (left lin) pure = _ , _ , left lin , left lin
tsplit-assoc-rl (right lin) (left _) = _ , _ , left lin , right lin
tsplit-assoc-rl (right lin) (right _) = _ , _ , right lin , pure
tsplit-assoc-rl (chan σs1 ρs1) (chan σs2 ρs2) =
  let _ , σs1 , σs2 = msplit-assoc-rl σs1 σs2 in
  let _ , ρs1 , ρs2 = msplit-assoc-rl ρs1 ρs2 in
  _ , _ , chan σs1 ρs1 , chan σs2 ρs2

tsplit-assoc-lr :
  ∀{t t12 t1 t2 t3 p p12 p1 p2 p3} ->
  TSplit t t12 t3 p p12 p3 ->
  TSplit t12 t1 t2 p12 p1 p2 ->
  ∃[ s ] ∃[ q ] (TSplit t t1 s p p1 q × TSplit s t2 t3 q p2 p3)
tsplit-assoc-lr sp1 sp2 =
  let _ , _ , sp1' , sp2' = tsplit-assoc-rl (tsplit-comm sp1) (tsplit-comm sp2) in
  _ , _ , tsplit-comm sp1' , tsplit-comm sp2'

csplit-assoc-rl :
  ∀{Γ Γ1 Γ23 Γ2 Γ3} ->
  CSplit Γ Γ1 Γ23 ->
  CSplit Γ23 Γ2 Γ3 ->
  ∃[ Δ ] (CSplit Γ Δ Γ3 × CSplit Δ Γ1 Γ2)
csplit-assoc-rl [] [] = [] , [] , []
csplit-assoc-rl (ts1 :: sp1) (ts2 :: sp2) =
  let _ , _ , ts1 , ts2 = tsplit-assoc-rl ts1 ts2 in
  let _ , sp1 , sp2 = csplit-assoc-rl sp1 sp2 in
  _ , ts1 :: sp1 , ts2 :: sp2

csplit-assoc-lr :
  ∀{Γ Γ12 Γ1 Γ2 Γ3} ->
  CSplit Γ Γ12 Γ3 ->
  CSplit Γ12 Γ1 Γ2 ->
  ∃[ Δ ] (CSplit Γ Γ1 Δ × CSplit Δ Γ2 Γ3)
csplit-assoc-lr sp1 sp2 =
  let sp1 = csplit-comm sp1 in
  let sp2 = csplit-comm sp2 in
  let _ , sp1 , sp2 = csplit-assoc-rl sp1 sp2 in
  let sp1 = csplit-comm sp1 in
  let sp2 = csplit-comm sp2 in
  _ , sp1 , sp2

{- Special case of associativity -}

m-split-split-split :
  ∀{ρ σ1 σ2 σ11 σ12 σ21 σ22} ->
  MSplit ρ σ1 σ2 ->
  MSplit σ1 σ11 σ12 ->
  MSplit σ2 σ21 σ22 ->
  ∃[ ρ1 ] ∃[ ρ2 ] (MSplit ρ ρ1 ρ2 × MSplit ρ1 σ11 σ21 × MSplit ρ2 σ12 σ22)
m-split-split-split sp sp1 sp2 =
  let _ , sp1 , sp = msplit-assoc-lr sp sp1 in
  let _ , sp2 , sp = msplit-assoc-rl sp sp2 in
  let sp = msplit-comm sp in
  let _ , sp , sp2 = msplit-assoc-lr sp2 sp in
  let _ , sp , sp1 = msplit-assoc-rl sp1 sp in
  _ , _ , sp , sp1 , sp2

t-split-split-split :
  ∀{s t1 t2 t11 t12 t21 t22 q p1 p2 p11 p12 p21 p22} ->
  TSplit s t1 t2 q p1 p2 ->
  TSplit t1 t11 t12 p1 p11 p12 ->
  TSplit t2 t21 t22 p2 p21 p22 ->
  ∃[ s1 ] ∃[ s2 ] ∃[ q1 ] ∃[ q2 ] (TSplit s s1 s2 q q1 q2 × TSplit s1 t11 t21 q1 p11 p21 × TSplit s2 t12 t22 q2 p12 p22)
t-split-split-split sp sp1 sp2 =
  let _ , _ , sp1 , sp = tsplit-assoc-lr sp sp1 in
  let _ , _ , sp2 , sp = tsplit-assoc-rl sp sp2 in
  let sp = tsplit-comm sp in
  let _ , _ , sp , sp2 = tsplit-assoc-lr sp2 sp in
  let _ , _ , sp , sp1 = tsplit-assoc-rl sp1 sp in
  _ , _ , _ , _ , sp , sp1 , sp2

c-split-split-split :
  ∀{Δ Γ1 Γ2 Γ11 Γ12 Γ21 Γ22} ->
  CSplit Δ Γ1 Γ2 ->
  CSplit Γ1 Γ11 Γ12 ->
  CSplit Γ2 Γ21 Γ22 ->
  ∃[ Δ1 ] ∃[ Δ2 ] (CSplit Δ Δ1 Δ2 × CSplit Δ1 Γ11 Γ21 × CSplit Δ2 Γ12 Γ22)
c-split-split-split sp sp1 sp2 =
  let _ , sp1 , sp = csplit-assoc-lr sp sp1 in
  let _ , sp2 , sp = csplit-assoc-rl sp sp2 in
  let sp = csplit-comm sp in
  let _ , sp , sp2 = csplit-assoc-lr sp2 sp in
  let _ , sp , sp1 = csplit-assoc-rl sp1 sp in
  _ , _ , sp , sp1 , sp2

{- Split Left -}

msplit-l : (σ : Multiplicity) -> MSplit σ σ #0
msplit-l #0 = 0+0
msplit-l #1 = 1+0
msplit-l #ω = ω+0

tsplit-l : ∀(t : Type){p} -> ∃[ s ] ∃[ q ] (TNull s × TSplit t t s p p q)
tsplit-l (Pure _)     = _ , _ , pure , pure
tsplit-l (Chan σ ρ t) = _ , _ , chan , chan (msplit-l σ) (msplit-l ρ)
tsplit-l (Pair _ _)   = _ , _ , pure , left pair

csplit-l : (Γ : Context) -> ∃[ Δ ] (CNull Δ × CSplit Γ Γ Δ)
csplit-l [] = _ , [] , []
csplit-l (t # _ :: Γ) =
  let _ , _ , tnull , ts = tsplit-l t in
  let _ , cnull , sp = csplit-l Γ in
  _ , tnull :: cnull , ts :: sp

{- Split Right -}

msplit-r : (σ : Multiplicity) -> MSplit σ #0 σ
msplit-r #0 = 0+0
msplit-r #1 = 0+1
msplit-r #ω = 0+ω

tsplit-r : ∀(t : Type){v} -> ∃[ s ] ∃[ w ] (TNull s × TSplit t s t v w v)
tsplit-r t =
  let _ , _ , tnull , ts = tsplit-l t in
  _ , _ , tnull , tsplit-comm ts

csplit-r : (Γ : Context) -> ∃[ Δ ] (CNull Δ × CSplit Γ Δ Γ)
csplit-r Γ =
  let _ , cnull , sp = csplit-l Γ in
  _ , cnull , csplit-comm sp

{- Split Left Right -}

msplit-comm-lr : (σ : Multiplicity) -> msplit-comm (msplit-l σ) ≡ msplit-r σ
msplit-comm-lr #0 = refl
msplit-comm-lr #1 = refl
msplit-comm-lr #ω = refl

{- Null Split => Null Null -}

t-null-split-null-null : ∀{t t1 t2 p p1 p2} -> TNull t -> TSplit t t1 t2 p p1 p2 -> TNull t1 × TNull t2
t-null-split-null-null pure pure = pure , pure
t-null-split-null-null chan (chan 0+0 0+0) = chan , chan

{- Null => Split -}

t-null-split : ∀{t p} -> TNull t -> TSplit t t t p p p
t-null-split pure = pure
t-null-split chan = chan 0+0 0+0

c-null-split : ∀{Γ} -> CNull Γ -> CSplit Γ Γ Γ
c-null-split [] = []
c-null-split (tnull :: Γ) = t-null-split tnull :: c-null-split Γ

{- Null Null Split => Null -}

t-null-null-split-null : ∀{t t1 t2 p p1 p2} -> TNull t1 -> TNull t2 -> TSplit t t1 t2 p p1 p2 -> TNull t
t-null-null-split-null pure pure pure           = pure
t-null-null-split-null pure pure (left _)       = pure
t-null-null-split-null chan pure (left _)       = chan
t-null-null-split-null pure pure (right _)      = pure
t-null-null-split-null pure chan (right _)      = chan
t-null-null-split-null chan chan (chan 0+0 0+0) = chan

c-null-null-split-null : ∀{Γ Γ1 Γ2} -> CNull Γ1 -> CNull Γ2 -> CSplit Γ Γ1 Γ2 -> CNull Γ
c-null-null-split-null [] [] [] = []
c-null-null-split-null (tz1 :: cnull1) (tz2 :: cnull2) (ts :: sp) =
  t-null-null-split-null tz1 tz2 ts :: c-null-null-split-null cnull1 cnull2 sp

