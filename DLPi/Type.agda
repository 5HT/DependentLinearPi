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
open import Size
open import Codata.Thunk
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym)

open import Multiplicity

mutual
  data PreType : Size → Set₁ where
    Pure : ∀{i} → Set -> PreType i
    Chan : ∀{i} → Multiplicity → Multiplicity → Thunk PreType i → PreType i
    Pair : ∀{i} → (t : PreType i) -> (f : ⟦ t ⟧ → PreType i) → PreType i

  {- Interpretation : datatype → type -}
  ⟦_⟧ : ∀{i} → PreType i → Set
  ⟦ Pure A ⟧     = A
  ⟦ Chan _ _ _ ⟧ = ⊤
  ⟦ Pair t f ⟧   = Σ ⟦ t ⟧ λ x -> ⟦ f x ⟧

UnfoldedType : Set₁
UnfoldedType = ∀{i} -> PreType i

FoldedType : Set₁
FoldedType = ∀{i} -> Thunk PreType i

fold : UnfoldedType -> FoldedType
fold t = λ where .force -> t

unfold : FoldedType -> UnfoldedType
unfold t = t .force

Type : Set₁
Type = PreType ∞

data Linear : Type -> Set where
  pair : ∀{t s} -> Linear (Pair t s)

data TNull : Type -> Set₁ where
  pure : ∀{A} -> TNull (Pure A)
  chan : ∀{t} -> TNull (Chan #0 #0 t)

data TSplit : (t t1 t2 : Type) → ⟦ t ⟧ -> ⟦ t1 ⟧ -> ⟦ t2 ⟧ -> Set₁ where
  pure  : ∀{A v} -> TSplit (Pure A) (Pure A) (Pure A) v v v
  left  : ∀{t v} -> Linear t -> TSplit t t (Pure ⊤) v v tt
  right : ∀{t v} -> Linear t -> TSplit t (Pure ⊤) t v tt v
  chan  : ∀{m m1 m2 n n1 n2 t} → MSplit m m1 m2 → MSplit n n1 n2 → TSplit (Chan m n t) (Chan m1 n1 t) (Chan m2 n2 t) tt tt tt

data TScale : (t s : Type) -> ⟦ t ⟧ -> ⟦ s ⟧ -> Set₁ where
  pure : ∀{A v} -> TScale (Pure A) (Pure A) v v
  chan : ∀{σ σ' ρ ρ' t} -> MScale σ σ' -> MScale ρ ρ' -> TScale (Chan σ ρ t) (Chan σ' ρ' t) _ _

t-null-split-null-null : ∀{t t1 t2 v v1 v2} -> TNull t -> TSplit t t1 t2 v v1 v2 -> TNull t1 × TNull t2
t-null-split-null-null pure pure = pure , pure
t-null-split-null-null chan (chan 0+0 0+0) = chan , chan

t-null-split : ∀{t v} -> TNull t -> TSplit t t t v v v
t-null-split pure = pure
t-null-split chan = chan 0+0 0+0

tsplit-comm : ∀{t t1 t2 v v1 v2} -> TSplit t t1 t2 v v1 v2 -> TSplit t t2 t1 v v2 v1
tsplit-comm pure = pure
tsplit-comm (left lin) = right lin
tsplit-comm (right lin) = left lin
tsplit-comm (chan σs ρs) = chan (msplit-comm σs) (msplit-comm ρs)

tsplit-comm-inv : ∀{t t1 t2 v v1 v2} -> (ts : TSplit t t1 t2 v v1 v2) -> tsplit-comm (tsplit-comm ts) ≡ ts
tsplit-comm-inv pure = refl
tsplit-comm-inv (left _) = refl
tsplit-comm-inv (right _) = refl
tsplit-comm-inv (chan σs ρs) = cong₂ chan (msplit-comm-inv σs) (msplit-comm-inv ρs)

tsplit-l : ∀(t : Type){v} -> ∃[ s ] ∃[ w ] (TNull s × TSplit t t s v v w)
tsplit-l (Pure _) = _ , _ , pure , pure
tsplit-l (Chan σ ρ t) = _ , _ , chan , chan (msplit-l σ) (msplit-l ρ)
tsplit-l (Pair _ _) = _ , _ , pure , left pair

tsplit-r : ∀(t : Type){v} -> ∃[ s ] ∃[ w ] (TNull s × TSplit t s t v w v)
tsplit-r t =
  let _ , _ , tnull , ts = tsplit-l t in
  _ , _ , tnull , tsplit-comm ts

tsplit-assoc-rl :
  ∀{t t1 t23 t2 t3 v v1 v23 v2 v3}
  -> TSplit t t1 t23 v v1 v23
  -> TSplit t23 t2 t3 v23 v2 v3
  -> ∃[ s ] ∃[ w ] (TSplit t s t3 v w v3 × TSplit s t1 t2 w v1 v2)
tsplit-assoc-rl pure pure = _ , _ , pure , pure
tsplit-assoc-rl (left lin) pure = _ , _ , left lin , left lin
tsplit-assoc-rl (right lin) (left _) = _ , _ , left lin , right lin
tsplit-assoc-rl (right lin) (right _) = _ , _ , right lin , pure
tsplit-assoc-rl (chan σs1 ρs1) (chan σs2 ρs2) =
  let _ , σs1 , σs2 = msplit-assoc-rl σs1 σs2 in
  let _ , ρs1 , ρs2 = msplit-assoc-rl ρs1 ρs2 in
  _ , _ , chan σs1 ρs1 , chan σs2 ρs2

tsplit-assoc-lr :
  ∀{t t12 t1 t2 t3 v v12 v1 v2 v3} ->
  TSplit t t12 t3 v v12 v3 ->
  TSplit t12 t1 t2 v12 v1 v2 ->
  ∃[ s ] ∃[ w ] (TSplit t t1 s v v1 w × TSplit s t2 t3 w v2 v3)
tsplit-assoc-lr sp1 sp2 =
  let _ , _ , sp1' , sp2' = tsplit-assoc-rl (tsplit-comm sp1) (tsplit-comm sp2) in
  _ , _ , tsplit-comm sp1' , tsplit-comm sp2'

t-null-null-split-null : ∀{t t1 t2 v v1 v2} -> TNull t1 -> TNull t2 -> TSplit t t1 t2 v v1 v2 -> TNull t
t-null-null-split-null pure pure pure = pure
t-null-null-split-null pure pure (left _) = pure
t-null-null-split-null chan pure (left _) = chan
t-null-null-split-null pure pure (right _) = pure
t-null-null-split-null pure chan (right _) = chan
t-null-null-split-null chan chan (chan 0+0 0+0) = chan

t-split-split-split :
  ∀{s t1 t2 t11 t12 t21 t22 w v1 v2 v11 v12 v21 v22} ->
  TSplit s t1 t2 w v1 v2 ->
  TSplit t1 t11 t12 v1 v11 v12 ->
  TSplit t2 t21 t22 v2 v21 v22 ->
  ∃[ s1 ] ∃[ s2 ] ∃[ w1 ] ∃[ w2 ] (TSplit s s1 s2 w w1 w2 × TSplit s1 t11 t21 w1 v11 v21 × TSplit s2 t12 t22 w2 v12 v22)
t-split-split-split sp sp1 sp2 =
  let _ , _ , sp1 , sp = tsplit-assoc-lr sp sp1 in
  let _ , _ , sp2 , sp = tsplit-assoc-rl sp sp2 in
  let sp = tsplit-comm sp in
  let _ , _ , sp , sp2 = tsplit-assoc-lr sp2 sp in
  let _ , _ , sp , sp1 = tsplit-assoc-rl sp1 sp in
  _ , _ , _ , _ , sp , sp1 , sp2

t-null-scale : ∀{t v} -> TNull t -> TScale t t v v
t-null-scale pure = pure
t-null-scale chan = chan 0·0 0·0

t-null-scale-null-l : ∀{t s v w} -> TNull t -> TScale t s v w -> TNull s
t-null-scale-null-l pure pure = pure
t-null-scale-null-l chan (chan 0·0 0·0) = chan

t-null-scale-null : ∀{t s v w} -> TNull s -> TScale t s v w -> TNull t
t-null-scale-null pure pure = pure
t-null-scale-null chan (chan 0·0 0·0) = chan

t-scale-split : ∀{t s v w} -> TScale t s v w -> TSplit s t s w v w
t-scale-split pure = pure
t-scale-split (chan σsc ρsc) = chan (m-scale-split σsc) (m-scale-split ρsc)

t-split-scale-scale :
  ∀{s t1 t2 s1 s2 w v1 v2 w1 w2} ->
  TSplit s s1 s2 w w1 w2 ->
  TScale t1 s1 v1 w1 ->
  TScale t2 s2 v2 w2 ->
  ∃[ t ] ∃[ v ] (TScale t s v w × TSplit t t1 t2 v v1 v2)
t-split-scale-scale (left lin) pure pure = _ , _ , pure , left lin
t-split-scale-scale (left ()) (chan _ _) _
t-split-scale-scale (right lin) pure pure = _ , _ , pure , right lin
t-split-scale-scale (right ()) pure (chan _ _)
t-split-scale-scale pure pure pure = _ , _ , pure , pure
t-split-scale-scale (chan σs ρs) (chan σsc1 ρsc1) (chan σsc2 ρsc2) =
  let _ , σsc , σs' = m-split-scale-scale σs σsc1 σsc2 in
  let _ , ρsc , ρs' = m-split-scale-scale ρs ρsc1 ρsc2 in
  _ , _ , chan σsc ρsc , chan σs' ρs'
