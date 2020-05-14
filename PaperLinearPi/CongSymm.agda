
open import Data.Nat
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.HeterogeneousEquality as Heq
open Heq using (_≅_; refl; cong; cong₂; cong-app; trans; subst; ≡-to-≅)
open Eq using (_≡_)

open import Language
open import Swapping
open import Semantics

swap-null-inv :
  ∀{n Γ Δ} ->
  (sw : Swap n Γ Δ) ->
  (null : CNull Γ) ->
  swap-null (swap-inv sw) (swap-null sw null) ≅ null
swap-null-inv swap-here (_ :: _ :: _) = refl
swap-null-inv (swap-next sw) (x :: null) = cong (x ::_) (swap-null-inv sw null)

≅1-cong :
  ∀{ℓ ℓ'}{A : Set ℓ}
  {i j : A}
  (T S : A -> Set ℓ') ->
  {g : A -> A}
  (f : ∀{i} -> T i -> S (g i)) ->
  i ≅ j ->
  {x : T i}{y : T j} ->
  x ≅ y ->
  f x ≅ f y
≅1-cong _ _ _ refl refl = refl

≅1-cong₂ :
  ∀{ℓ ℓ'}{A : Set ℓ}
  {i j : A}
  (T S : A -> Set ℓ') ->
  {g : A -> A}
  (f : ∀{i} -> T i -> S (g i)) ->
  i ≅ j ->
  {x : T i}{y : T j} ->
  x ≅ y ->
  f x ≅ f y
≅1-cong₂ _ _ _ refl refl = refl

≅2-cong :
  ∀{ℓ ℓ'}{A : Set ℓ}
  {i1 j1 i2 j2 : A}
  (T S : A -> A -> Set ℓ') ->
  {f1 : A -> A}
  {f2 : A -> A}
  (f : ∀{i j} -> T i j -> S (f1 i) (f2 j)) ->
  i1 ≅ j1 ->
  i2 ≅ j2 ->
  {x : T i1 i2}{y : T j1 j2} ->
  x ≅ y ->
  f x ≅ f y
≅2-cong _ _ _ refl refl refl = refl

swap-split-inv :
  ∀{n Γ Γ1 Γ2 Δ} ->
  (sw : Swap n Γ Δ) ->
  (sp : CSplit Γ Γ1 Γ2) ->
  let _ , _ , sp' , _ , _ = swap-split sw sp in
  let Γ1' , Γ2' , sp'' , _ , _ = swap-split (swap-inv sw) sp' in
  Γ1' ≅ Γ1 × Γ2' ≅ Γ2 × sp'' ≅ sp
swap-split-inv swap-here (x :: x₁ :: sp) = refl , refl , refl
swap-split-inv {_} {_ :: Γ} (swap-next sw) (ts :: sp) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  let _ , _ , sp'' , sw1' , sw2' = swap-split (swap-inv sw) sp' in
  let eq1 , eq2 , eq = swap-split-inv sw sp in
  cong (_ ::_) eq1 ,
  cong (_ ::_) eq2 ,
  ≅2-cong (CSplit _) (CSplit _) (_ ::_) eq1 eq2 eq

var-next-cong :
  ∀{m n Γ s t}{snull : TNull s} ->
  {x : Var m Γ t} ->
  {y : Var n Γ t} ->
  m ≡ n ->
  x ≅ y ->
  var-next snull x ≅ var-next snull y
var-next-cong Eq.refl refl = refl

pair-cong :
  ∀{Γ Γ1 Γ2 Δ Δ1 Δ2 t1 t2 v1 v2} ->
  Γ ≅ Δ ->
  Γ1 ≅ Δ1 ->
  Γ2 ≅ Δ2 ->
  {V1 : Value Γ1 t1 v1}
  {V2 : Value Γ2 t2 v2}
  {W1 : Value Δ1 t1 v1}
  {W2 : Value Δ2 t2 v2} ->
  V1 ≅ W1 ->
  V2 ≅ W2 ->
  {sp : CSplit Γ Γ1 Γ2}
  {sp' : CSplit Δ Δ1 Δ2} ->
  sp ≅ sp' ->
  pair sp V1 V2 ≅ pair sp' W1 W2
pair-cong refl refl refl refl refl refl = refl

swap-var-inv :
  ∀{n Γ Δ k t} ->
  (sw : Swap n Γ Δ) ->
  (x : Var k Γ t) ->
  swap-var-index n (swap-var-index n k) ≡ k × swap-var (swap-inv sw) (swap-var sw x) ≅ x
swap-var-inv swap-here (var-here (_ :: _)) = Eq.refl , refl
swap-var-inv swap-here (var-next _ (var-here _)) = Eq.refl , refl
swap-var-inv swap-here (var-next _ (var-next _ _)) = Eq.refl , refl
swap-var-inv (swap-next sw) (var-here _) = Eq.refl , cong var-here (swap-null-inv sw _)
swap-var-inv (swap-next sw) (var-next _ x) =
  let eq1 , eq2 = swap-var-inv sw x in
  Eq.cong suc eq1 ,
  var-next-cong eq1 eq2

swap-value-inv :
  ∀{n Γ Δ t v} ->
  (sw : Swap n Γ Δ) ->
  (V : Value Γ t v) ->
  swap-value (swap-inv sw) (swap-value sw V) ≅ V
swap-value-inv sw (pure null _) = cong (λ p -> pure p _) (swap-null-inv sw null)
swap-value-inv {n} sw (chan x) =
  let eq1 , eq2 = swap-var-inv sw x in
  ≅1-cong (λ x -> Var x _ _) _ {λ x -> swap-var-index n (swap-var-index n x)} chan (≡-to-≅ eq1) eq2
swap-value-inv {v = v1 , v2} sw (pair {f = f} {v = _} {w = _} sp V1 V2)
  with swap-split sw sp
...| _ , _ , sp' , sw1 , sw2 with swap-split-inv sw sp
...| eq1 , eq2 , eq3 = {!!}
  -- let eq4 = swap-value-inv sw1 V1 in
  -- let eq5 = swap-value-inv sw2 V2 in
  -- let ack = pair-cong {!!} {!!} {!!} {!!} {!!} eq3 in
  -- {!!}

swap-expression-inv :
  ∀{n Γ Δ t} ->
  (sw : Swap n Γ Δ) ->
  (E : Expression Γ t) ->
  swap-expr (swap-inv sw) (swap-expr sw E) ≅ E
swap-expression-inv sw (val V) = {!!}
swap-expression-inv {n} {Γ} {_} {t} sw (var x) =
  let eq1 , eq2 = swap-var-inv sw x in
  ≅1-cong (λ x -> Var x _ _) _ {λ x -> swap-var-index n (swap-var-index n x)} var (≡-to-≅ eq1) eq2

swap-process-inv :
  ∀{n Γ Δ} ->
  (sw : Swap n Γ Δ) ->
  (P : Process Γ) ->
  swap-process (swap-inv sw) (swap-process sw P) ≅ P
swap-process-inv sw (Idle null) = cong Idle (swap-null-inv sw null)
swap-process-inv sw (Send sp E1 E2) = {!!}
swap-process-inv sw (Recv sp E P) = {!!}
swap-process-inv sw (Par sp P1 P2) = {!!}
swap-process-inv sw (New P) = {!!}
swap-process-inv sw (Rep sc P) = {!!}
swap-process-inv sw (Let sp E P) = {!!}

cong-symm : ∀{Γ}{P Q : Process Γ} -> P <= Q -> ∃[ R ] (R ≅ P × Q <= R)
cong-symm cong-refl = _ , refl , cong-refl
cong-symm (cong-trans pc1 pc2) =
  let _ , eq1 , pc1' = cong-symm pc1 in
  let _ , eq2 , pc2' = cong-symm pc2 in
  _ , eq1 , cong-trans (subst (_ <=_) eq2 pc2') pc1'
cong-symm (cong-par-idle-lr sp null) =
  _ , refl , cong-par-idle-rl sp null
cong-symm (cong-par-idle-rl sp null) =
  _ , refl , cong-par-idle-lr sp null
cong-symm (cong-par-cong sp pc) = {!!}
cong-symm (cong-par-comm sp) =
  _ , cong (λ sp -> Par sp _ _) (≡-to-≅ (csplit-comm-inv sp)) , cong-par-comm (csplit-comm sp)
cong-symm (cong-par-assoc-rl sp1 sp2) = {!!}
cong-symm (cong-par-assoc-lr sp1 sp2) = {!!}
cong-symm (cong-new-cong pc) = {!!}
cong-symm cong-new-new =
  _ , cong (λ P -> New (New P)) (swap-process-inv _ _) , cong-new-new
cong-symm (cong-par-new sp) = {!!}
cong-symm (cong-new-par sp niQ) = {!!}
cong-symm (cong-new-idle cz) = {!!}
cong-symm (cong-idle-new cz) = {!!}
cong-symm (cong-rep-par sc) = {!!}
cong-symm (cong-par-rep sp sc) = {!!}
