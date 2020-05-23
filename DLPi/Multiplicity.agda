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

msplit-l : (m : Multiplicity) -> MSplit m m #0
msplit-l #0 = 0+0
msplit-l #1 = 1+0
msplit-l #ω = ω+0

msplit-r : (m : Multiplicity) -> MSplit m #0 m
msplit-r #0 = 0+0
msplit-r #1 = 0+1
msplit-r #ω = 0+ω

msplit-comm : {m m1 m2 : Multiplicity} -> MSplit m m1 m2 -> MSplit m m2 m1
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
  {m m1 m2 : Multiplicity} -> (sp : MSplit m m1 m2) -> msplit-comm (msplit-comm sp) ≡ sp
msplit-comm-inv 0+0 = refl
msplit-comm-inv 0+1 = refl
msplit-comm-inv 0+ω = refl
msplit-comm-inv 1+0 = refl
msplit-comm-inv 1+1 = refl
msplit-comm-inv 1+ω = refl
msplit-comm-inv ω+0 = refl
msplit-comm-inv ω+1 = refl
msplit-comm-inv ω+ω = refl

msplit-comm-lr : (m : Multiplicity) -> msplit-comm (msplit-l m) ≡ msplit-r m
msplit-comm-lr #0 = refl
msplit-comm-lr #1 = refl
msplit-comm-lr #ω = refl

msplit-assoc-rl :
  ∀{m m1 m23 m2 m3}
  -> MSplit m m1 m23
  -> MSplit m23 m2 m3
  -> ∃[ n ] (MSplit m n m3 × MSplit n m1 m2)
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
  ∀{m m12 m1 m2 m3}
  -> MSplit m m12 m3
  -> MSplit m12 m1 m2
  -> ∃[ n ] (MSplit m m1 n × MSplit n m2 m3)
msplit-assoc-lr ms1 ms2 =
  let _ , ms1' , ms2' = msplit-assoc-rl (msplit-comm ms1) (msplit-comm ms2) in
  _ , msplit-comm ms1' , msplit-comm ms2'

m-split-split-split :
  ∀{n m1 m2 m11 m12 m21 m22}
  -> MSplit n m1 m2
  -> MSplit m1 m11 m12
  -> MSplit m2 m21 m22
  -> ∃[ n1 ] ∃[ n2 ] (MSplit n n1 n2 × MSplit n1 m11 m21 × MSplit n2 m12 m22)
m-split-split-split sp sp1 sp2 =
  let _ , sp1 , sp = msplit-assoc-lr sp sp1 in
  let _ , sp2 , sp = msplit-assoc-rl sp sp2 in
  let sp = msplit-comm sp in
  let _ , sp , sp2 = msplit-assoc-lr sp2 sp in
  let _ , sp , sp1 = msplit-assoc-rl sp1 sp in
  _ , _ , sp , sp1 , sp2

