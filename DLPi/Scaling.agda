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
open import Data.Product

open import Multiplicity
open import Type
open import Context
open import Language

m-scale-split : ∀{m n} -> MScale m n -> MSplit n m n
m-scale-split scale00 = split00
m-scale-split scale1ω = split1ω
m-scale-split scaleωω = splitωω

t-null-scale : ∀{t v} -> TNull t -> TScale t t v v
t-null-scale null-p = scale-p
t-null-scale null-c = scale-c scale00 scale00

t-null-scale-null-l : ∀{t s v w} -> TNull t -> TScale t s v w -> TNull s
t-null-scale-null-l null-p scale-p = null-p
t-null-scale-null-l null-c (scale-c scale00 scale00) = null-c

t-null-scale-null : ∀{t s v w} -> TNull s -> TScale t s v w -> TNull t
t-null-scale-null null-p scale-p = null-p
t-null-scale-null null-c (scale-c scale00 scale00) = null-c

c-null-scale : ∀{Γ} -> CNull Γ -> CScale Γ Γ
c-null-scale [] = []
c-null-scale (tnull :: null) = t-null-scale tnull :: c-null-scale null

t-scale-split : ∀{t s v w} -> TScale t s v w -> TSplit s t s w v w
t-scale-split scale-p = split-p
t-scale-split (scale-c σsc ρsc) = split-c (m-scale-split σsc) (m-scale-split ρsc)

c-scale-split : ∀{Γ Δ} -> CScale Γ Δ -> CSplit Δ Γ Δ
c-scale-split [] = []
c-scale-split (tsc :: sc) = t-scale-split tsc :: c-scale-split sc

m-split-scale-scale :
  ∀{σ1 σ2 ρ ρ1 ρ2} ->
  MSplit ρ ρ1 ρ2 ->
  MScale σ1 ρ1 ->
  MScale σ2 ρ2 ->
  ∃[ σ ] (MScale σ ρ × MSplit σ σ1 σ2)
m-split-scale-scale split00 scale00 scale00 = _ , scale00 , split00
m-split-scale-scale split0ω scale00 scale1ω = _ , scale1ω , split01
m-split-scale-scale split0ω scale00 scaleωω = _ , scaleωω , split0ω
m-split-scale-scale splitω0 scale1ω scale00 = _ , scale1ω , split10
m-split-scale-scale splitω0 scaleωω scale00 = _ , scaleωω , splitω0
m-split-scale-scale splitωω scale1ω scale1ω = _ , scaleωω , split11
m-split-scale-scale splitωω scale1ω scaleωω = _ , scaleωω , split1ω
m-split-scale-scale splitωω scaleωω scale1ω = _ , scaleωω , splitω1
m-split-scale-scale splitωω scaleωω scaleωω = _ , scaleωω , splitωω

t-split-scale-scale :
  ∀{s t1 t2 s1 s2 w v1 v2 w1 w2} ->
  TSplit s s1 s2 w w1 w2 ->
  TScale t1 s1 v1 w1 ->
  TScale t2 s2 v2 w2 ->
  ∃[ t ] ∃[ v ] (TScale t s v w × TSplit t t1 t2 v v1 v2)
t-split-scale-scale (split-l lin) scale-p scale-p = _ , _ , scale-p , split-l lin
t-split-scale-scale (split-l ()) (scale-c _ _) _
t-split-scale-scale (split-r lin) scale-p scale-p = _ , _ , scale-p , split-r lin
t-split-scale-scale (split-r ()) scale-p (scale-c _ _)
t-split-scale-scale split-p scale-p scale-p = _ , _ , scale-p , split-p
t-split-scale-scale (split-c σs ρs) (scale-c σsc1 ρsc1) (scale-c σsc2 ρsc2) =
  let _ , σsc , σs' = m-split-scale-scale σs σsc1 σsc2 in
  let _ , ρsc , ρs' = m-split-scale-scale ρs ρsc1 ρsc2 in
  _ , _ , scale-c σsc ρsc , split-c σs' ρs'

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

scale-name :
  ∀{k Δ t s v w} ->
  TScale t s v w ->
  Name k Δ s w ->
  ∃[ Γ ] (CScale Γ Δ × Name k Γ t v)
scale-name sc (name-here null) = _ , sc :: c-null-scale null , name-here null
scale-name sc (name-next tnull x) =
  let _ , sc' , y = scale-name sc x in
  _ , t-null-scale tnull :: sc' , name-next tnull y

scale-term :
  ∀{Δ s t v w} ->
  TScale t s v w ->
  Term Δ s w ->
  ∃[ Γ ] (CScale Γ Δ × Term Γ t v)
scale-term sc (name x) =
  let _ , sc , x = scale-name sc x in
  _ , sc , name x
scale-term scale-p (pure null c) = _ , c-null-scale null , pure null c
