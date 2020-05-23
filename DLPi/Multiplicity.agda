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

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym)

module Multiplicity where

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

data MScale : Multiplicity -> Multiplicity -> Set where
  0·0 : MScale #0 #0
  1·ω : MScale #1 #ω
  ω·ω : MScale #ω #ω

data MSplit : Multiplicity → Multiplicity → Multiplicity → Set where
  0+0 : MSplit #0 #0 #0
  0+1 : MSplit #1 #0 #1
  0+ω : MSplit #ω #0 #ω
  1+0 : MSplit #1 #1 #0
  1+1 : MSplit #ω #1 #1
  1+ω : MSplit #ω #1 #ω
  ω+0 : MSplit #ω #ω #0
  ω+1 : MSplit #ω #ω #1
  ω+ω : MSplit #ω #ω #ω

msplit-l : (σ : Multiplicity) -> MSplit σ σ #0
msplit-l #0 = 0+0
msplit-l #1 = 1+0
msplit-l #ω = ω+0

msplit-r : (σ : Multiplicity) -> MSplit σ #0 σ
msplit-r #0 = 0+0
msplit-r #1 = 0+1
msplit-r #ω = 0+ω

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

msplit-comm-inv :
  {σ σ1 σ2 : Multiplicity} -> (sp : MSplit σ σ1 σ2) -> msplit-comm (msplit-comm sp) ≡ sp
msplit-comm-inv 0+0 = refl
msplit-comm-inv 0+1 = refl
msplit-comm-inv 0+ω = refl
msplit-comm-inv 1+0 = refl
msplit-comm-inv 1+1 = refl
msplit-comm-inv 1+ω = refl
msplit-comm-inv ω+0 = refl
msplit-comm-inv ω+1 = refl
msplit-comm-inv ω+ω = refl

msplit-comm-lr : (σ : Multiplicity) -> msplit-comm (msplit-l σ) ≡ msplit-r σ
msplit-comm-lr #0 = refl
msplit-comm-lr #1 = refl
msplit-comm-lr #ω = refl

msplit-assoc-rl :
  ∀{σ σ1 σ23 σ2 m3}
  -> MSplit σ σ1 σ23
  -> MSplit σ23 σ2 m3
  -> ∃[ ρ ] (MSplit σ ρ m3 × MSplit ρ σ1 σ2)
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
  ∀{σ σ12 σ1 σ2 m3}
  -> MSplit σ σ12 m3
  -> MSplit σ12 σ1 σ2
  -> ∃[ ρ ] (MSplit σ σ1 ρ × MSplit ρ σ2 m3)
msplit-assoc-lr ms1 ms2 =
  let _ , ms1' , ms2' = msplit-assoc-rl (msplit-comm ms1) (msplit-comm ms2) in
  _ , msplit-comm ms1' , msplit-comm ms2'

m-split-split-split :
  ∀{ρ σ1 σ2 σ11 σ12 σ21 σ22}
  -> MSplit ρ σ1 σ2
  -> MSplit σ1 σ11 σ12
  -> MSplit σ2 σ21 σ22
  -> ∃[ ρ1 ] ∃[ ρ2 ] (MSplit ρ ρ1 ρ2 × MSplit ρ1 σ11 σ21 × MSplit ρ2 σ12 σ22)
m-split-split-split sp sp1 sp2 =
  let _ , sp1 , sp = msplit-assoc-lr sp sp1 in
  let _ , sp2 , sp = msplit-assoc-rl sp sp2 in
  let sp = msplit-comm sp in
  let _ , sp , sp2 = msplit-assoc-lr sp2 sp in
  let _ , sp , sp1 = msplit-assoc-rl sp1 sp in
  _ , _ , sp , sp1 , sp2

m-scale-split : ∀{σ ρ} -> MScale σ ρ -> MSplit ρ σ ρ
m-scale-split 0·0 = 0+0
m-scale-split 1·ω = 1+ω
m-scale-split ω·ω = ω+ω

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
