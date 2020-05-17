-- This file is part of DLπ.

-- DLπ is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.

-- DLπ is distributed in the hope that it will be useful, but
-- WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
-- General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with DLπ.  If not, see <https://www.gnu.org/licenses/>.

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym)

module Multiplicity where

data Multiplicity : Set where
  #0 #1 #ω : Multiplicity

data MScale : Multiplicity -> Multiplicity -> Set where
  scale00 : MScale #0 #0
  scale1ω : MScale #1 #ω
  scaleωω : MScale #ω #ω

data MSplit : Multiplicity → Multiplicity → Multiplicity → Set where
  split00 : MSplit #0 #0 #0
  split01 : MSplit #1 #0 #1
  split0ω : MSplit #ω #0 #ω
  split10 : MSplit #1 #1 #0
  split11 : MSplit #ω #1 #1
  split1ω : MSplit #ω #1 #ω
  splitω0 : MSplit #ω #ω #0
  splitω1 : MSplit #ω #ω #1
  splitωω : MSplit #ω #ω #ω

msplit-l : (m : Multiplicity) -> MSplit m m #0
msplit-l #0 = split00
msplit-l #1 = split10
msplit-l #ω = splitω0

msplit-r : (m : Multiplicity) -> MSplit m #0 m
msplit-r #0 = split00
msplit-r #1 = split01
msplit-r #ω = split0ω

msplit-comm : {m m1 m2 : Multiplicity} -> MSplit m m1 m2 -> MSplit m m2 m1
msplit-comm split00 = split00
msplit-comm split01 = split10
msplit-comm split0ω = splitω0
msplit-comm split10 = split01
msplit-comm split11 = split11
msplit-comm split1ω = splitω1
msplit-comm splitω0 = split0ω
msplit-comm splitω1 = split1ω
msplit-comm splitωω = splitωω

msplit-comm-inv :
  {m m1 m2 : Multiplicity} -> (sp : MSplit m m1 m2) -> msplit-comm (msplit-comm sp) ≡ sp
msplit-comm-inv split00 = refl
msplit-comm-inv split01 = refl
msplit-comm-inv split0ω = refl
msplit-comm-inv split10 = refl
msplit-comm-inv split11 = refl
msplit-comm-inv split1ω = refl
msplit-comm-inv splitω0 = refl
msplit-comm-inv splitω1 = refl
msplit-comm-inv splitωω = refl

msplit-comm-lr : (m : Multiplicity) -> msplit-comm (msplit-l m) ≡ msplit-r m
msplit-comm-lr #0 = refl
msplit-comm-lr #1 = refl
msplit-comm-lr #ω = refl

msplit-assoc-rl :
  ∀{m m1 m23 m2 m3}
  -> MSplit m m1 m23
  -> MSplit m23 m2 m3
  -> ∃[ n ] (MSplit m n m3 × MSplit n m1 m2)
msplit-assoc-rl split00 split00 = #0 , split00 , split00
msplit-assoc-rl split01 split01 = #0 , split01 , split00
msplit-assoc-rl split01 split10 = #1 , split10 , split01
msplit-assoc-rl split0ω split0ω = #0 , split0ω , split00
msplit-assoc-rl split0ω split11 = #1 , split11 , split01
msplit-assoc-rl split0ω split1ω = #1 , split1ω , split01
msplit-assoc-rl split0ω splitω0 = #ω , splitω0 , split0ω
msplit-assoc-rl split0ω splitω1 = #ω , splitω1 , split0ω
msplit-assoc-rl split0ω splitωω = #ω , splitωω , split0ω
msplit-assoc-rl split10 split00 = #1 , split10 , split10
msplit-assoc-rl split11 split01 = #1 , split11 , split10
msplit-assoc-rl split11 split10 = #ω , splitω0 , split11
msplit-assoc-rl split1ω split0ω = #1 , split1ω , split10
msplit-assoc-rl split1ω split11 = #ω , splitω1 , split11
msplit-assoc-rl split1ω split1ω = #ω , splitωω , split11
msplit-assoc-rl split1ω splitω0 = #ω , splitω0 , split1ω
msplit-assoc-rl split1ω splitω1 = #ω , splitω1 , split1ω
msplit-assoc-rl split1ω splitωω = #ω , splitωω , split1ω
msplit-assoc-rl splitω0 split00 = #ω , splitω0 , splitω0
msplit-assoc-rl splitω1 split01 = #ω , splitω1 , splitω0
msplit-assoc-rl splitω1 split10 = #ω , splitω0 , splitω1
msplit-assoc-rl splitωω split0ω = #ω , splitωω , splitω0
msplit-assoc-rl splitωω split11 = #ω , splitω1 , splitω1
msplit-assoc-rl splitωω split1ω = #ω , splitωω , splitω1
msplit-assoc-rl splitωω splitω0 = #ω , splitω0 , splitωω
msplit-assoc-rl splitωω splitω1 = #ω , splitω1 , splitωω
msplit-assoc-rl splitωω splitωω = #ω , splitωω , splitωω

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

