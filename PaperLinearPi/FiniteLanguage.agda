{-# OPTIONS --allow-unsolved-metas #-}

{- PURPPOSE: INFERRING MULTIPLICITIES -}

open import Size
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Language
open import Codata.Thunk
open import Data.Maybe
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂; sym)

{- FINITE TYPE -}

mutual
  data FiniteType : Set₁ where
    Pure : Set -> FiniteType
    [_]  : FiniteType -> FiniteType
    Pair : FiniteType -> FiniteType -> FiniteType
    Dep  : (t : FiniteType) -> (S⟦ t ⟧ -> FiniteType) -> FiniteType

  S⟦_⟧ : FiniteType -> Set
  S⟦ Pure A ⟧ = A
  S⟦ [ _ ] ⟧ = ⊤
  S⟦ Pair t s ⟧ = S⟦ t ⟧ × S⟦ s ⟧
  S⟦ Dep t f ⟧ = Σ S⟦ t ⟧ λ x -> S⟦ f x ⟧

{- SIMPLE CONTEXT -}

data SimpleContext : Set₁ where
  []   : SimpleContext
  _::_ : FiniteType -> SimpleContext -> SimpleContext

{- SIMPLY-TYPED EXPRESSIONS -}

data SimpleVar : SimpleContext -> FiniteType -> Set where
  var-here : ∀{Δ t} -> SimpleVar (t :: Δ) t
  var-next : ∀{Δ t s} -> SimpleVar Δ t -> SimpleVar (s :: Δ) t

data SimpleExpression : SimpleContext -> FiniteType -> Set where
  pure : ∀{Δ A} -> A -> SimpleExpression Δ (Pure A)
  var  : ∀{Δ t} -> SimpleVar Δ t -> SimpleExpression Δ t
  pair : ∀{Δ t s} -> SimpleExpression Δ t -> SimpleExpression Δ s -> SimpleExpression Δ (Pair t s)

data SimpleProcess : SimpleContext -> Set₁ where
  Idle : ∀{Δ} -> SimpleProcess Δ
  Send : ∀{Δ t} -> SimpleExpression Δ [ t ] -> SimpleExpression Δ t -> SimpleProcess Δ
  Recv : ∀{Δ t} -> SimpleExpression Δ [ t ] -> SimpleProcess (t :: Δ) -> SimpleProcess Δ
  Par  : ∀{Δ} -> SimpleProcess Δ -> SimpleProcess Δ -> SimpleProcess Δ
  New  : ∀{Δ} -> (t : FiniteType) -> SimpleProcess ([ t ] :: Δ) -> SimpleProcess Δ
  Rep  : ∀{Δ} -> SimpleProcess Δ -> SimpleProcess Δ
  Let  :
    ∀{Δ} ->
    (t : FiniteType) ->
    (s : FiniteType) ->
    SimpleExpression Δ (Pair t s) ->
    SimpleProcess (t :: s :: Δ) -> SimpleProcess Δ

-- m-scale : ∀(σ) -> ∃[ ρ ] (MScale σ ρ)
-- m-scale #0 = #0 , scale00
-- m-scale #1 = #ω , scale1ω
-- m-scale #ω = #ω , scaleωω

-- t-scale : ∀(t) -> ∃[ s ] (TScale t s)
-- t-scale (Pure A) = Pure A , scale-n
-- t-scale (Ch σ ρ t) =
--   let _ , σsc = m-scale σ in
--   let _ , ρsc = m-scale ρ in
--   _ , scale-c σsc ρsc
-- t-scale (Pair t s) =
--   let _ , tsc = t-scale t in
--   let _ , ssc = t-scale s in
--   _ , scale-p tsc ssc
-- t-scale (Dep t f) =
--   _ , scale-d λ x -> let _ , sc = t-scale (f x) in sc

-- mutual
--   t-zero-ann : FiniteType -> Type
--   t-zero-ann (Pure A) = Pure A
--   t-zero-ann [ t ] = Ch #0 #0 t
--   t-zero-ann (Pair t s) = Pair (t-zero-ann t) (t-zero-ann s)
--   t-zero-ann (Dep t f) =
--     let t' = t-zero-ann t in
--     Dep t' λ x -> t-zero-ann (f (t-zero-ann-eq t x))

--   t-zero-ann-eq : (t : FiniteType) -> ⟦ t-zero-ann t ⟧ -> S⟦ t ⟧
--   t-zero-ann-eq (Pure _) x = x
--   t-zero-ann-eq [ _ ] x = x
--   t-zero-ann-eq (Pair t s) (x , y) = t-zero-ann-eq t x , t-zero-ann-eq s y
--   t-zero-ann-eq (Dep t f) (x , y) =
--     t-zero-ann-eq t x , t-zero-ann-eq (f (t-zero-ann-eq t x)) y

-- t-zero-ann-null : ∀(t) -> TNull (t-zero-ann t)
-- t-zero-ann-null (Pure _) = null-n
-- t-zero-ann-null [ _ ] = null-c
-- t-zero-ann-null (Pair t s) = null-p (t-zero-ann-null t) (t-zero-ann-null s)
-- t-zero-ann-null (Dep t f) = null-d (λ x -> t-zero-ann-null (f (t-zero-ann-eq t x)))

-- t-zero-ann-strip : ∀(t : FiniteType) -> TStrip (t-zero-ann t) t
-- t-zero-ann-strip (Pure _) = strip-n
-- t-zero-ann-strip [ _ ] = strip-c
-- t-zero-ann-strip (Pair t s) = strip-p (t-zero-ann-strip t) (t-zero-ann-strip s)
-- t-zero-ann-strip (Dep t f) = {!!}

-- t-strip-correct : ∀(t : Type) -> TStrip t (t-strip t)
-- t-strip-correct (Pure _) = strip-n
-- t-strip-correct (Ch _ _ _) = strip-c
-- t-strip-correct (Pair t s) = strip-p (t-strip-correct t) (t-strip-correct s)
-- t-strip-correct (Dep t f) = ⊥-elim impossible
--   where postulate impossible : ⊥

-- c-strip : Context -> SimpleContext
-- c-strip [] = []
-- c-strip (t :: Γ) = t-strip t :: c-strip Γ

-- data CStrip : Context -> SimpleContext -> Set₁ where
--   strip-[] : CStrip [] []
--   strip-:: : ∀{t s Γ Δ} -> TStrip t s -> CStrip Γ Δ -> CStrip (t :: Γ) (s :: Δ)

-- c-zero-ann : SimpleContext -> Context
-- c-zero-ann [] = []
-- c-zero-ann (t :: Γ) = t-zero-ann t :: c-zero-ann Γ

-- c-zero-ann-null : (Γ : SimpleContext) -> CNull (c-zero-ann Γ)
-- c-zero-ann-null [] = null-[]
-- c-zero-ann-null (_ :: Γ) = null-:: (t-zero-ann-null _) (c-zero-ann-null Γ)

-- c-zero-ann-strip : (Γ : SimpleContext) -> CStrip (c-zero-ann Γ) Γ
-- c-zero-ann-strip [] = strip-[]
-- c-zero-ann-strip (t :: Γ) = strip-:: (t-zero-ann-strip t) (c-zero-ann-strip Γ)

-- {- TYPE INFERENCE FOR EXPRESSIONS -}

-- m-join : (σ1 σ2 : Multiplicity) -> ∃[ σ ] MSplit σ σ1 σ2
-- m-join #0 #0 = #0 , split00
-- m-join #0 #1 = #1 , split01
-- m-join #0 #ω = #ω , split0ω
-- m-join #1 #0 = #1 , split10
-- m-join #1 #1 = #ω , split11
-- m-join #1 #ω = #ω , split1ω
-- m-join #ω #0 = #ω , splitω0
-- m-join #ω #1 = #ω , splitω1
-- m-join #ω #ω = #ω , splitωω

-- t-strip-strip-join : ∀{t1 t2 s} -> TStrip t1 s -> TStrip t2 s -> ∃[ t ] (TSplit t t1 t2 × TStrip t s)
-- t-strip-strip-join strip-n strip-n = _ , split-n , strip-n
-- t-strip-strip-join strip-c strip-c =
--   let _ , σs = m-join _ _ in
--   let _ , ρs = m-join _ _ in
--   _ , split-c σs ρs , strip-c
-- t-strip-strip-join (strip-p st1 st3) (strip-p st2 st4) =
--   let _ , ts , tst = t-strip-strip-join st1 st2 in
--   let _ , ss , sst = t-strip-strip-join st3 st4 in
--   _ , split-p ts ss , strip-p tst sst

-- c-strip-strip-join : ∀{Γ1 Γ2 Δ} -> CStrip Γ1 Δ -> CStrip Γ2 Δ -> ∃[ Γ ] (CSplit Γ Γ1 Γ2 × CStrip Γ Δ)
-- c-strip-strip-join strip-[] strip-[] = [] , split-[] , strip-[]
-- c-strip-strip-join (strip-:: ts1 st1) (strip-:: ts2 st2) =
--   let _ , ts , tst = t-strip-strip-join ts1 ts2 in
--   let _ , sp , cst = c-strip-strip-join st1 st2 in
--   _ , split-:: ts sp , strip-:: tst cst

-- t-strip-strip-split-strip :
--   ∀{t t1 t2 s} ->
--   TStrip t1 s ->
--   TStrip t2 s ->
--   TSplit t t1 t2 ->
--   TStrip t s
-- t-strip-strip-split-strip strip-n strip-n split-n = strip-n
-- t-strip-strip-split-strip strip-c strip-c (split-c _ _) = strip-c
-- t-strip-strip-split-strip (strip-p ts1 ss1) (strip-p ts2 ss2) (split-p ts ss) =
--   strip-p (t-strip-strip-split-strip ts1 ts2 ts) (t-strip-strip-split-strip ss1 ss2 ss)

-- c-strip-strip-split-strip :
--   ∀{Γ Γ1 Γ2 Δ} ->
--   CStrip Γ1 Δ ->
--   CStrip Γ2 Δ ->
--   CSplit Γ Γ1 Γ2 ->
--   CStrip Γ Δ
-- c-strip-strip-split-strip strip-[] strip-[] split-[] = strip-[]
-- c-strip-strip-split-strip (strip-:: ts1 st1) (strip-:: ts2 st2) (split-:: ts sp) =
--   strip-:: (t-strip-strip-split-strip ts1 ts2 ts) (c-strip-strip-split-strip st1 st2 sp)

-- match-multiplicity : ∀(σ ρ : Multiplicity) -> Maybe (σ ≡ ρ)
-- match-multiplicity #0 #0 = just refl
-- match-multiplicity #0 #1 = nothing
-- match-multiplicity #0 #ω = nothing
-- match-multiplicity #1 #0 = nothing
-- match-multiplicity #1 #1 = just refl
-- match-multiplicity #1 #ω = nothing
-- match-multiplicity #ω #0 = nothing
-- match-multiplicity #ω #1 = nothing
-- match-multiplicity #ω #ω = just refl

-- check-type : ∀(t s : Type) -> TStrip t (t-strip s) -> Maybe (t ≡ s)
-- check-type _ (Pure _) strip-n = just refl
-- check-type (Ch σ1 ρ1 _) (Ch σ2 ρ2 _) strip-c = do
--   refl <- match-multiplicity σ1 σ2
--   refl <- match-multiplicity ρ1 ρ2
--   just refl
-- check-type (Pair t1 t2) (Pair s1 s2) (strip-p st1 st2) = do
--   refl <- check-type t1 s1 st1
--   refl <- check-type t2 s2 st2
--   just refl
-- check-type t (Dep s f) st = nothing

-- check-var : ∀{Δ t s} -> TStrip t s -> SimpleVar Δ s -> ∃[ Γ ] ∃[ k ] (CStrip Γ Δ × Var k Γ t)
-- check-var {_ :: Δ} st var-here =
--   _ :: c-zero-ann Δ ,
--   zero , strip-:: st (c-zero-ann-strip Δ) ,
--   var-here (c-zero-ann-null Δ)
-- check-var {u :: Δ} st (var-next x) =
--   let _ , k , st , y = check-var st x in
--   _ , suc k , strip-:: (t-zero-ann-strip u) st , var-next (t-zero-ann-null u) y

-- check-expression' : ∀{Δ t} -> SimpleExpression Δ (t-strip t) -> ∃[ Γ ] (c-strip Γ ≡ Δ × Expression Γ t)
-- check-expression' {Δ} {Pure A} (pure x) = c-zero-ann Δ , {!!} , pure (c-zero-ann-null Δ) x
-- check-expression' {_} {Pure A} (var x) = {!!}
-- check-expression' {_} {Ch x x₁ x₂} (var x₃) = {!!}
-- check-expression' {_} {Pair t t₁} (var x) = {!!}
-- check-expression' {_} {Pair t t₁} (pair E E₁) = {!!}
-- check-expression' {_} {Dep t f} E = {!!}

-- check-expression : ∀{Δ t s} -> TStrip t s -> SimpleExpression Δ s -> ∃[ Γ ] (CStrip Γ Δ × Expression Γ t)
-- check-expression {Δ} strip-n (pure c) = c-zero-ann Δ , c-zero-ann-strip Δ , pure (c-zero-ann-null Δ) c
-- check-expression st (var x) =
--   let _ , _ , st , y = check-var st x in
--   _ , st , var y
-- check-expression (strip-p st1 st2) (pair E1 E2) =
--   let Γ1 , cst1 , F1 = check-expression st1 E1 in
--   let Γ2 , cst2 , F2 = check-expression st2 E2 in
--   let Γ , sp , st = c-strip-strip-join cst1 cst2 in
--   Γ , st , pair sp F1 F2

-- c-scale : (Γ : Context) -> ∃[ Δ ] CScale Γ Δ
-- c-scale [] = [] , scale-[]
-- c-scale (t :: Γ) =
--   let _ , tsc = t-scale t in
--   let _ , sc = c-scale Γ in
--   _ , scale-:: tsc sc

-- c-tail : Context -> Maybe Context
-- c-tail [] = nothing
-- c-tail (_ :: Γ) = just Γ

-- t-strip-scale-strip :
--   ∀{t t' s} ->
--   TStrip t s ->
--   TScale t t' ->
--   TStrip t' s
-- t-strip-scale-strip strip-n scale-n = strip-n
-- t-strip-scale-strip strip-c (scale-c _ _) = strip-c
-- t-strip-scale-strip (strip-p st1 st2) (scale-p sc1 sc2) =
--   strip-p (t-strip-scale-strip st1 sc1) (t-strip-scale-strip st2 sc2)

-- c-strip-scale-strip :
--   ∀{Γ Γ' Δ} ->
--   CStrip Γ Δ ->
--   CScale Γ Γ' ->
--   CStrip Γ' Δ
-- c-strip-scale-strip strip-[] scale-[] = strip-[]
-- c-strip-scale-strip (strip-:: tst cst) (scale-:: tsc csc) =
--   strip-:: (t-strip-scale-strip tst tsc) (c-strip-scale-strip cst csc)

-- as-channel : Type -> Maybe (Multiplicity × Multiplicity × (∀{i} -> Thunk PreType i))
-- as-channel (Pure _) = nothing
-- as-channel (Ch σ ρ t) = just (σ , ρ , t)
-- as-channel (Pair _ _) = nothing
-- as-channel (Dep _ _) = nothing

-- check-process : ∀{Δ} -> SimpleProcess Δ -> Maybe (∃[ Γ ] (CStrip Γ Δ × Process Γ))
-- check-process {Δ} Idle =
--   just (c-zero-ann Δ ,
--        c-zero-ann-strip Δ ,
--        Idle (c-zero-ann-null Δ))
-- check-process (Send {_} {t} E1 E2) = do
--   let Γ1 , st1 , F1 = check-expression (strip-c {#0} {#1}) E1
--   let Γ2 , st2 , F2 = check-expression (t-strip-correct (t .force)) E2
--   let Γ , sp , st = c-strip-strip-join st1 st2
--   just (Γ , st , Send sp F1 F2)
-- check-process (Recv {_} {t} E P) = do
--   let Γ1 , st1 , F = check-expression (strip-c {#1} {#0}) E
--   (s :: Γ2 , strip-:: st21 st22 , Q) <- check-process P
--   refl <- check-type s (t .force) st21
--   let Γ , sp , st = c-strip-strip-join st1 st22
--   just (Γ , st , Recv sp F Q)
-- check-process (Par P1 P2) = do
--   (Γ1 , st1 , Q1) <- check-process P1
--   (Γ2 , st2 , Q2) <- check-process P2
--   let Γ , sp , st = c-strip-strip-join st1 st2
--   just (Γ , st , Par sp Q1 Q2)
-- check-process (New t P) = do
--   (s :: Γ , strip-:: strip-c st2 , Q) <- check-process P
--   just (Γ , st2 , New Q)
-- check-process (Rep P) = do
--   (Γ , st , Q) <- check-process P
--   let Γ' , sc = c-scale Γ
--   just (Γ' , c-strip-scale-strip st sc , Rep sc Q)
-- check-process (Let t s E P) = do
--   let Γ1 , st1 , F = check-expression (strip-p (t-strip-correct t) (t-strip-correct s)) E
--   (t' :: s' :: Γ2 , strip-:: tst (strip-:: sst st2) , Q) <- check-process P
--   refl <- check-type t' t tst
--   refl <- check-type s' s sst
--   let Γ , sp , st = c-strip-strip-join st1 st2
--   just (Γ , st , {!!})
