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

open import Language

module Scale where

{- Scale => Split -}

m-scale-split : ∀{σ ρ} -> MScale σ ρ -> MSplit ρ σ ρ
m-scale-split 0·0 = 0+0
m-scale-split 1·ω = 1+ω
m-scale-split ω·ω = ω+ω

t-scale-split : ∀{t s p q} -> TScale t s p q -> TSplit s t s q p q
t-scale-split pure = pure
t-scale-split (chan σsc ρsc) = chan (m-scale-split σsc) (m-scale-split ρsc)

c-scale-split : ∀{Γ Δ} -> CScale Γ Δ -> CSplit Δ Γ Δ
c-scale-split [] = []
c-scale-split (tsc :: sc) = t-scale-split tsc :: c-scale-split sc

{- Null => Scale -}

t-null-scale : ∀{t p} -> TNull t -> TScale t t p p
t-null-scale pure = pure
t-null-scale chan = chan 0·0 0·0

c-null-scale : ∀{Γ} -> CNull Γ -> CScale Γ Γ
c-null-scale [] = []
c-null-scale (tnull :: null) = t-null-scale tnull :: c-null-scale null

{- Split Scale Scale => Scale Split -}

m-split-scale-scale :
  ∀{σ1 σ2 ρ ρ1 ρ2} ->
  MSplit ρ ρ1 ρ2 ->
  MScale σ1 ρ1 ->
  MScale σ2 ρ2 ->
  ∃[ σ ] (MScale σ ρ × MSplit σ σ1 σ2)
m-split-scale-scale 0+0 0·0 0·0 = _ , 0·0 , 0+0
m-split-scale-scale 0+ω 0·0 1·ω = _ , 1·ω , 0+1
m-split-scale-scale 0+ω 0·0 ω·ω = _ , ω·ω , 0+ω
m-split-scale-scale ω+0 1·ω 0·0 = _ , 1·ω , 1+0
m-split-scale-scale ω+0 ω·ω 0·0 = _ , ω·ω , ω+0
m-split-scale-scale ω+ω 1·ω 1·ω = _ , ω·ω , 1+1
m-split-scale-scale ω+ω 1·ω ω·ω = _ , ω·ω , 1+ω
m-split-scale-scale ω+ω ω·ω 1·ω = _ , ω·ω , ω+1
m-split-scale-scale ω+ω ω·ω ω·ω = _ , ω·ω , ω+ω

t-split-scale-scale :
  ∀{s t1 t2 s1 s2 q p1 p2 q1 q2} ->
  TSplit s s1 s2 q q1 q2 ->
  TScale t1 s1 p1 q1 ->
  TScale t2 s2 p2 q2 ->
  ∃[ t ] ∃[ p ] (TScale t s p q × TSplit t t1 t2 p p1 p2)
t-split-scale-scale (left lin) pure pure = _ , _ , pure , left lin
t-split-scale-scale (left ()) (chan _ _) _
t-split-scale-scale (right lin) pure pure = _ , _ , pure , right lin
t-split-scale-scale (right ()) pure (chan _ _)
t-split-scale-scale pure pure pure = _ , _ , pure , pure
t-split-scale-scale (chan σs ρs) (chan σsc1 ρsc1) (chan σsc2 ρsc2) =
  let _ , σsc , σs' = m-split-scale-scale σs σsc1 σsc2 in
  let _ , ρsc , ρs' = m-split-scale-scale ρs ρsc1 ρsc2 in
  _ , _ , chan σsc ρsc , chan σs' ρs'

c-split-scale-scale :
  ∀{Γ1 Γ2 Δ Δ1 Δ2} ->
  CSplit Δ Δ1 Δ2 ->
  CScale Γ1 Δ1 ->
  CScale Γ2 Δ2 ->
  ∃[ Γ ] (CScale Γ Δ × CSplit Γ Γ1 Γ2)
c-split-scale-scale [] [] [] = _ , [] , []
c-split-scale-scale (ts :: sp) (tsc1 :: sc1) (tsc2 :: sc2) =
  let _ , _ , tsc , ts' = t-split-scale-scale ts tsc1 tsc2 in
  let _ , sc , sp' = c-split-scale-scale sp sc1 sc2 in
  _ , tsc :: sc , ts' :: sp'

{- Null Scale => Null -}

t-null-scale-null-l : ∀{t s p q} -> TNull t -> TScale t s p q -> TNull s
t-null-scale-null-l pure pure = pure
t-null-scale-null-l chan (chan 0·0 0·0) = chan

t-null-scale-null : ∀{t s p q} -> TNull s -> TScale t s p q -> TNull t
t-null-scale-null pure pure = pure
t-null-scale-null chan (chan 0·0 0·0) = chan
