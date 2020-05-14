
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Codata.Thunk
open import Data.Maybe
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂; sym)

open import Multiplicity
open import Type
open import Context
open import Language
open import Weakening

{- SIMPLE TYPES -}

mutual
  data SimpleType : Set₁ where
    Pure : Set -> SimpleType
    Chan : Multiplicity -> Multiplicity -> SimpleType -> SimpleType
    Pair : SimpleType -> SimpleType -> SimpleType
    DepN : (ℕ -> SimpleType) -> SimpleType
    DepB : (Bool -> SimpleType) -> SimpleType

  S⟦_⟧ : SimpleType -> Set
  S⟦ Pure A ⟧     = A
  S⟦ Chan _ _ _ ⟧ = ⊤
  S⟦ Pair t s ⟧   = Σ S⟦ t ⟧ λ _ -> S⟦ s ⟧
  S⟦ DepN f ⟧     = Σ ℕ λ x -> S⟦ f x ⟧
  S⟦ DepB f ⟧     = Σ Bool λ x -> S⟦ f x ⟧

t-make : ∀{i} -> SimpleType -> PreType i
t-make (Pure A)     = Pure A
t-make (Chan σ ρ t) = Chan σ ρ (fold (t-make t))
t-make (Pair t s)   = Pair (t-make t) λ _ -> t-make s
t-make (DepN f)     = Pair (Pure ℕ) λ x -> t-make (f x)
t-make (DepB f)     = Pair (Pure Bool) λ x -> t-make (f x)

-- IDEA: TStrip t s if t is "more precise than" s, that it t
-- describes more faithfully than s how a value of that type is used
-- in a process.
data TStrip : SimpleType -> SimpleType -> Set₁ where
  strip-n  : ∀{A : Set} -> TStrip (Pure A) (Pure A)
  strip-c  : ∀{σ ρ σ' ρ' t} -> TStrip (Chan σ ρ t) (Chan σ' ρ' t)
  strip-p  : ∀{t s} -> TStrip (Pair t s) (Pair t s)
  strip-np : ∀{f} -> TStrip (DepN f) (DepN f)
  strip-bp : ∀{f} -> TStrip (DepB f) (DepB f)
  strip-l  : ∀{t f} -> TStrip (Pure ⊤) (Pair t f)
  strip-nl : ∀{f} -> TStrip (Pure ⊤) (DepN f)
  strip-bl : ∀{f} -> TStrip (Pure ⊤) (DepB f)

t-strip-refl : (t : SimpleType) -> TStrip t t
t-strip-refl (Pure _) = strip-n
t-strip-refl (Chan _ _ t) = strip-c
t-strip-refl (Pair t s) = strip-p
t-strip-refl (DepN f) = strip-np
t-strip-refl (DepB f) = strip-bp

t-strip-null : ∀(s : SimpleType) -> ∃[ t ] (TNull (t-make t) × TStrip t s)
t-strip-null (Pure _) = _ , null-p , strip-n
t-strip-null (Chan _ _ _) = _ , null-c , strip-c
t-strip-null (Pair _ _) = _ , null-p , strip-l
t-strip-null (DepN _) = _ , null-p , strip-nl
t-strip-null (DepB _) = _ , null-p , strip-bl

t-make-cast : (t : SimpleType) -> S⟦ t ⟧ -> ⟦ t-make t ⟧
t-make-cast (Pure _) x = x
t-make-cast (Chan _ _ _) _ = tt
t-make-cast (Pair t s) (x , y) = t-make-cast t x , t-make-cast s y
t-make-cast (DepN f) (x , y) = x , t-make-cast (f x) y
t-make-cast (DepB f) (x , y) = x , t-make-cast (f x) y

t-strip-cast : ∀{t s} -> TStrip t s -> S⟦ s ⟧ -> S⟦ t ⟧
t-strip-cast strip-n x = x
t-strip-cast strip-c _ = tt
t-strip-cast strip-p x = x
t-strip-cast strip-np x = x
t-strip-cast strip-bp x = x
t-strip-cast strip-l _ = tt
t-strip-cast strip-nl _ = tt
t-strip-cast strip-bl _ = tt

t-strip-make-cast : ∀{t s} -> TStrip t s -> S⟦ s ⟧ -> ⟦ t-make t ⟧
t-strip-make-cast {t} ts x = t-make-cast t (t-strip-cast ts x)

cast-boh : (t : SimpleType) -> (x : S⟦ t ⟧) -> t-strip-make-cast (t-strip-refl t) x ≡ t-make-cast t x
cast-boh (Pure _) _ = refl
cast-boh (Chan _ _ _) _ = refl
cast-boh (Pair _ _) _ = refl
cast-boh (DepN _) _ = refl
cast-boh (DepB _) _ = refl

m-scale : ∀(σ) -> ∃[ ρ ] (MScale σ ρ)
m-scale #0 = #0 , scale00
m-scale #1 = #ω , scale1ω
m-scale #ω = #ω , scaleωω

t-scale : ∀(t){v} -> Maybe (∃[ s ] ∃[ w ] TScale (t-make t) (t-make s) v w)
t-scale (Pure A) = just (Pure A , _ , scale-p)
t-scale (Chan σ ρ t) =
  let _ , σsc = m-scale σ in
  let _ , ρsc = m-scale ρ in
  just (_ , _ , scale-c σsc ρsc)
t-scale (Pair _ _) = nothing
t-scale (DepN _) = nothing
t-scale (DepB _) = nothing

{- SIMPLE CONTEXT -}

data SimpleContext : Set₁ where
  []   : SimpleContext
  _::_ : SimpleType -> SimpleContext -> SimpleContext

c-make : SimpleContext -> Context
c-make [] = []
c-make (t :: Γ) = t-make t :: c-make Γ

data CStrip : SimpleContext -> SimpleContext -> Set₁ where
  []   : CStrip [] []
  _::_ : ∀{t s Γ Δ} -> TStrip t s -> CStrip Γ Δ -> CStrip (t :: Γ) (s :: Δ)

c-strip-null : ∀(Δ) -> ∃[ Γ ] (CNull (c-make Γ) × CStrip Γ Δ)
c-strip-null [] = [] , [] , []
c-strip-null (t :: Γ) =
  let _ , tnull , ts = t-strip-null t in
  let _ , cnull , cs = c-strip-null Γ in
  _ , tnull :: cnull , ts :: cs

{- SIMPLY-TYPED EXPRESSIONS -}

data SimpleVar : SimpleContext -> SimpleType -> Set where
  var-here : ∀{Δ t} -> SimpleVar (t :: Δ) t
  var-next : ∀{Δ t s} -> SimpleVar Δ t -> SimpleVar (s :: Δ) t

data SimpleValue : SimpleContext -> (t : SimpleType) -> S⟦ t ⟧ -> Set₁ where
  pure : ∀{Δ A} -> (c : A) -> SimpleValue Δ (Pure A) c
  chan : ∀{Δ σ ρ t} -> SimpleVar Δ (Chan σ ρ t) -> SimpleValue Δ (Chan σ ρ t) tt
  pair :
    ∀{Δ t s v w} ->
    SimpleValue Δ t v ->
    SimpleValue Δ s w ->
    SimpleValue Δ (Pair t s) (v , w)
  depn :
    ∀{Δ}{f : ℕ -> SimpleType} ->
    (n : ℕ) ->
    ∀{v} -> SimpleValue Δ (f n) v ->
    SimpleValue Δ (DepN f) (n , v)
  depb :
    ∀{Δ}{f : Bool -> SimpleType} ->
    (b : Bool) ->
    ∀{v} -> SimpleValue Δ (f b) v ->
    SimpleValue Δ (DepB f) (b , v)

data SimpleExpression : SimpleContext -> SimpleType -> Set₁ where
  val : ∀{Δ t c} -> SimpleValue Δ t c -> SimpleExpression Δ t
  var : ∀{Δ t} -> SimpleVar Δ t -> SimpleExpression Δ t

data SimpleProcess : SimpleContext -> Set₁ where
  Idle : ∀{Δ} -> SimpleProcess Δ
  Send : ∀{Δ σ ρ t} -> SimpleVar Δ (Chan σ ρ t) -> SimpleExpression Δ t -> SimpleProcess Δ
  Recv : ∀{Δ σ ρ t} -> SimpleVar Δ (Chan σ ρ t) -> SimpleProcess (t :: Δ) -> SimpleProcess Δ
  Par  : ∀{Δ} -> SimpleProcess Δ -> SimpleProcess Δ -> SimpleProcess Δ
  New  : ∀{Δ} -> (σ ρ : Multiplicity) (t : SimpleType) -> SimpleProcess (Chan σ ρ t :: Δ) -> SimpleProcess Δ
  Rep  : ∀{Δ} -> SimpleProcess Δ -> SimpleProcess Δ
  Let  :
    ∀{Δ t s} ->
    SimpleExpression Δ (Pair t s) ->
    SimpleProcess (t :: s :: Δ) ->
    SimpleProcess Δ
  LetN :
    ∀{Δ} {f : ℕ -> SimpleType} ->
    SimpleExpression Δ (DepN f) ->
    (F : (n : ℕ) -> SimpleProcess (Pure ℕ :: f n :: [])) ->
    SimpleProcess Δ
  LetB :
    ∀{Δ f} ->
    SimpleExpression Δ (DepB f) ->
    SimpleProcess (f true :: Δ) ->
    SimpleProcess (f false :: Δ) ->
    SimpleProcess Δ

{- TYPE INFERENCE FOR EXPRESSIONS -}

m-join : (σ1 σ2 : Multiplicity) -> ∃[ σ ] MSplit σ σ1 σ2
m-join #0 #0 = #0 , split00
m-join #0 #1 = #1 , split01
m-join #0 #ω = #ω , split0ω
m-join #1 #0 = #1 , split10
m-join #1 #1 = #ω , split11
m-join #1 #ω = #ω , split1ω
m-join #ω #0 = #ω , splitω0
m-join #ω #1 = #ω , splitω1
m-join #ω #ω = #ω , splitωω

t-strip-strip-join :
  ∀{t1 t2 s} ->
  TStrip t1 s ->
  TStrip t2 s ->
  Maybe (∃[ t ] (TSplit (t-make t) (t-make t1) (t-make t2) × TStrip t s))
t-strip-strip-join strip-n strip-n = just (_ , split-p , strip-n)
t-strip-strip-join strip-c strip-c = do
  let _ , σs = m-join _ _
  let _ , ρs = m-join _ _
  just (_ , split-c σs ρs , strip-c)
t-strip-strip-join strip-p strip-p = nothing
t-strip-strip-join strip-p strip-l = just (_ , split-l lin-p , strip-p)
t-strip-strip-join strip-l strip-p = just (_ , split-r lin-p , strip-p)
t-strip-strip-join strip-l strip-l = just (_ , split-p , strip-l)
t-strip-strip-join strip-np strip-np = nothing
t-strip-strip-join strip-np strip-nl = just (_ , split-l lin-p , strip-np)
t-strip-strip-join strip-nl strip-np = just (_ , split-r lin-p , strip-np)
t-strip-strip-join strip-nl strip-nl = just (_ , split-p , strip-nl)
t-strip-strip-join strip-bp strip-bp = nothing
t-strip-strip-join strip-bp strip-bl = just (_ , split-l lin-p , strip-bp)
t-strip-strip-join strip-bl strip-bp = just (_ , split-r lin-p , strip-bp)
t-strip-strip-join strip-bl strip-bl = just (_ , split-p , strip-bl)

c-strip-strip-join :
  ∀{Γ1 Γ2 Δ} ->
  CStrip Γ1 Δ ->
  CStrip Γ2 Δ ->
  Maybe (∃[ Γ ] (CSplit (c-make Γ) (c-make Γ1) (c-make Γ2) × CStrip Γ Δ))
c-strip-strip-join [] [] = just (_ , [] , [])
c-strip-strip-join (ts1 :: cs1) (ts2 :: cs2) = do
  (_ , tst , tsp) <- t-strip-strip-join ts1 ts2
  (_ , cst , csp) <- c-strip-strip-join cs1 cs2
  just (_ , tst :: cst , tsp :: csp)

check-var : ∀{Δ t s} -> TStrip t s -> SimpleVar Δ s -> ∃[ Γ ] ∃[ k ] (CStrip Γ Δ × Var k (c-make Γ) (t-make t))
check-var {s :: Δ} ts var-here =
  let _ , cnull , cs = c-strip-null Δ in
  _ , _ , ts :: cs , var-here cnull
check-var {s :: _} st (var-next x) =
  let _ , snull , ss = t-strip-null s in
  let _ , _ , cs , x = check-var st x in
  _ , _ , ss :: cs , var-next snull x

check-value :
  ∀{Δ t s v} ->
  (ts : TStrip t s) ->
  SimpleValue Δ s v ->
  Maybe (∃[ Γ ] (CStrip Γ Δ × Value (c-make Γ) (t-make t) (t-strip-make-cast ts v)))
check-value {Δ} strip-n (pure c) = do
  let _ , cnull , cs = c-strip-null Δ
  just (_ , cs , pure cnull c)
check-value ts@strip-c (chan x) = do
  let _ , _ , cs , x = check-var ts x
  just (_ , cs , chan x)
check-value strip-p (pair {_} {t} {s} {x} {y} V1 V2) = do
  (_ , cs1 , W1) <- check-value (t-strip-refl _) V1
  (_ , cs2 , W2) <- check-value (t-strip-refl _) V2
  (_ , sp , st) <- c-strip-strip-join cs1 cs2
  just (_ , st , pair sp (subst (Value _ _) (cast-boh t x) W1)
                         (subst (Value _ _) (cast-boh s y) W2))
check-value {Δ} strip-l (pair _ _) = do
  let _ , cnull , cs = c-strip-null Δ
  just (_ , cs , pure cnull tt)
check-value {Δ} strip-np (depn {_} {f} n {v} V) = do
  let _ , cnull , cs1 = c-strip-null Δ
  (_ , cs2 , W) <- check-value (t-strip-refl (f n)) V
  (_ , sp , st) <- c-strip-strip-join cs1 cs2
  just (_ , st , pair sp (pure cnull n) (subst (Value _ _) (cast-boh (f n) v) W))
check-value {Δ} strip-bp (depb {_} {f} b {v} V) = do
  let _ , cnull , cs1 = c-strip-null Δ
  (_ , cs2 , W) <- check-value (t-strip-refl (f b)) V
  (_ , sp , st) <- c-strip-strip-join cs1 cs2
  just (_ , st , pair sp (pure cnull b) (subst (Value _ _) (cast-boh (f b) v) W))
check-value {Δ} strip-nl (depn _ _) = do
  let _ , cnull , cs = c-strip-null Δ
  just (_ , cs , pure cnull tt)
check-value {Δ} strip-bl (depb _ _) = do
  let _ , cnull , cs = c-strip-null Δ
  just (_ , cs , pure cnull tt)

check-expression :
  ∀{Δ t s} ->
  TStrip t s ->
  SimpleExpression Δ s ->
  Maybe (∃[ Γ ] (CStrip Γ Δ × Expression (c-make Γ) (t-make t)))
check-expression st (val V) = do
  (_ , sp , W) <- check-value st V
  just (_ , sp , val W)
check-expression st (var x) = do
  let _ , _ , st , x = check-var st x
  just (_ , st , var x)

c-scale : (Γ : SimpleContext) -> Maybe (∃[ Δ ] CScale (c-make Γ) (c-make Δ))
c-scale [] = just ([] , [])
c-scale (t :: Γ) = do
  (_ , tsc) <- t-scale t
  (_ , sc) <- c-scale Γ
  just (_ , tsc :: sc)

t-scale-strip : ∀{t s} -> TStrip t s -> Maybe (∃[ t' ] (TStrip t' s × TScale (t-make t) (t-make t')))
t-scale-strip strip-n = just (_ , strip-n , scale-p)
t-scale-strip (strip-c {σ} {ρ}) = do
  let σ' , σsc = m-scale σ
  let ρ' , ρsc = m-scale ρ
  just (_ , strip-c {σ'} {ρ'} , scale-c σsc ρsc)
t-scale-strip strip-p = nothing
t-scale-strip strip-np = nothing
t-scale-strip strip-bp = nothing
t-scale-strip strip-l = just (_ , strip-l , scale-p)
t-scale-strip strip-nl = just (_ , strip-nl , scale-p)
t-scale-strip strip-bl = just (_ , strip-bl , scale-p)

c-scale-strip : ∀{Γ Δ} -> CStrip Γ Δ -> Maybe (∃[ Γ' ] (CStrip Γ' Δ × CScale (c-make Γ) (c-make Γ')))
c-scale-strip [] = just (_ , [] , [])
c-scale-strip (tst :: st) = do
  (_ , tst , tsc) <- t-scale-strip tst
  (_ , st , sc) <- c-scale-strip st
  just (_ , tst :: st , tsc :: sc)

check-multiplicity : (σ ρ : Multiplicity) -> Maybe (σ ≡ ρ)
check-multiplicity #0 #0 = just refl
check-multiplicity #0 #1 = nothing
check-multiplicity #0 #ω = nothing
check-multiplicity #1 #0 = nothing
check-multiplicity #1 #1 = just refl
check-multiplicity #1 #ω = nothing
check-multiplicity #ω #0 = nothing
check-multiplicity #ω #1 = nothing
check-multiplicity #ω #ω = just refl

t-strip-strip-almost-eq : ∀{t1 t2 s} -> TStrip t1 s -> TStrip t2 s -> Maybe (t1 ≡ t2)
t-strip-strip-almost-eq strip-n strip-n = just refl
t-strip-strip-almost-eq (strip-c {σ1} {ρ1}) (strip-c {σ2} {ρ2}) = do
  refl <- check-multiplicity σ1 σ2
  refl <- check-multiplicity ρ1 ρ2
  just refl
t-strip-strip-almost-eq strip-p strip-p = just refl
t-strip-strip-almost-eq strip-p strip-l = nothing
t-strip-strip-almost-eq strip-l strip-p = nothing
t-strip-strip-almost-eq strip-l strip-l = just refl
t-strip-strip-almost-eq strip-np strip-np = just refl
t-strip-strip-almost-eq strip-nl strip-np = nothing
t-strip-strip-almost-eq strip-np strip-nl = nothing
t-strip-strip-almost-eq strip-nl strip-nl = just refl
t-strip-strip-almost-eq strip-bp strip-bp = just refl
t-strip-strip-almost-eq strip-bl strip-bp = nothing
t-strip-strip-almost-eq strip-bp strip-bl = nothing
t-strip-strip-almost-eq strip-bl strip-bl = just refl

check-type : ∀{t s} -> TStrip t s -> Maybe (t ≡ s)
check-type strip-n = just refl
check-type strip-l = nothing
check-type strip-nl = nothing
check-type strip-bl = nothing
check-type {Chan σ1 ρ1 _} {Chan σ2 ρ2 _} strip-c = do
  refl <- check-multiplicity σ1 σ2
  refl <- check-multiplicity ρ1 ρ2
  just refl
check-type strip-p = just refl
check-type strip-np = just refl
check-type strip-bp = just refl

c-strip-strip-almost-eq :
  ∀{Γ1 Γ2 Δ} ->
  CStrip Γ1 Δ ->
  CStrip Γ2 Δ ->
  Maybe (Γ1 ≡ Γ2)
c-strip-strip-almost-eq [] [] = just refl
c-strip-strip-almost-eq (ts1 :: cs1) (ts2 :: cs2) = do
  refl <- t-strip-strip-almost-eq ts1 ts2
  refl <- c-strip-strip-almost-eq cs1 cs2
  just refl

check-process : ∀{Δ} -> SimpleProcess Δ -> Maybe (∃[ Γ ] (CStrip Γ Δ × Process (c-make Γ)))
check-process-n :
  ∀{f : ℕ -> SimpleType} ->
  ((n : ℕ) -> SimpleProcess (Pure ℕ :: f n :: [])) ->
  ∀{Δ} -> ∃[ Γ ] (CStrip Γ Δ × CNull (c-make Γ) × ((n : ℕ) -> Process (Pure ℕ :: t-make (f n) :: c-make Γ)))

check-process-n {f} F {Δ} =
  let _ , cnull , st = c-strip-null Δ in
  _ , st , cnull , cast-maybe (aux cnull)
  where
    _C++_ : Context -> Context -> Context
    [] C++ Γ2 = Γ2
    (t :: Γ1) C++ Γ2 = t :: (Γ1 C++ Γ2)

    C++-identity-r : ∀{Γ} -> Γ C++ [] ≡ Γ
    C++-identity-r {[]} = refl
    C++-identity-r {t :: Γ} = cong (t ::_) (C++-identity-r {Γ})

    weaken-there-there : ∀{Γ1 Γ2 t1 t2} -> CNull Γ1 -> Process (t1 :: t2 :: Γ2) -> Process (t1 :: t2 :: (Γ1 C++ Γ2))
    weaken-there-there [] P = P
    weaken-there-there (tnull :: cnull) P =
      weaken-process (weaken-next (weaken-next (weaken-here tnull))) (weaken-there-there cnull P)

    aux : ∀{Γ} -> CNull Γ -> (n : ℕ) -> Maybe (Process (Pure ℕ :: t-make (f n) :: Γ))
    aux {Γ} cnull n = do
      (_ , strip-n :: ts2 :: [] , P) <- check-process (F n)
      refl <- check-type ts2
      just (subst (λ x -> Process (_ :: _ :: x)) (C++-identity-r {Γ}) (weaken-there-there cnull P))

    postulate runtime-error : ⊥

    cast-maybe : ∀{A : ℕ -> Set₁} -> ((n : ℕ) -> Maybe (A n)) -> (n : ℕ) -> A n
    cast-maybe f n with f n
    ... | nothing = ⊥-elim runtime-error
    ... | just x = x

check-process {Δ} Idle = do
  let _ , null , st = c-strip-null Δ
  just (_ , st , Idle null)
check-process (Send x E) = do
  let _ , _ , st1 , x = check-var (strip-c {#0} {#1}) x
  (_ , st2 , F) <- check-expression (t-strip-refl _) E
  (_ , sp , st) <- c-strip-strip-join st1 st2
  just (_ , st , Send sp (var x) F)
check-process (Recv x P) = do
  let _ , _ , st1 , x = check-var (strip-c {#1} {#0}) x
  (_ , ts' :: st2 , Q) <- check-process P
  (_ , sp , st) <- c-strip-strip-join st1 st2
  refl <- t-strip-strip-almost-eq (t-strip-refl _) ts'
  just (_ , st , Recv sp (var x) Q)
check-process (Par P1 P2) = do
  (_ , st1 , Q1) <- check-process P1
  (_ , st2 , Q2) <- check-process P2
  (_ , sp , st) <- c-strip-strip-join st1 st2
  just (_ , st , Par sp Q1 Q2)
check-process (New σ ρ s P) = do
  (_ , strip-c :: cst , Q) <- check-process P
  -- TODO: check that the inferred multiplicies match with σ and ρ
  just (_ , cst , New Q)
check-process (Rep P) = do
  (_ , st , Q) <- check-process P
  (_ , st , sc) <- c-scale-strip st
  just (_ , st , Rep sc Q)
check-process (Let E P) = do
  (_ , ts :: ss :: st2 , Q) <- check-process P
  (_ , st1 , F) <- check-expression strip-p E
  refl <- t-strip-strip-almost-eq (t-strip-refl _) ts
  refl <- t-strip-strip-almost-eq (t-strip-refl _) ss
  (_ , sp , st) <- c-strip-strip-join st1 st2
  just (_ , st , Let sp F λ _ -> Q)
check-process (LetN E F) = do
  let _ , st2 , cnull , F = check-process-n F
  (_ , st1 , E') <- check-expression strip-np E
  (_ , sp , st) <- c-strip-strip-join st1 st2
  just (_ , st , Let sp E' F)
check-process (LetB E P1 P2) = do
  (_ , ts :: st1 , Q1) <- check-process P1
  (_ , fs :: st2 , Q2) <- check-process P2
  refl <- t-strip-strip-almost-eq (t-strip-refl _) ts
  refl <- t-strip-strip-almost-eq (t-strip-refl _) fs
  (_ , st0 , E') <- check-expression strip-bp E
  refl <- c-strip-strip-almost-eq st1 st2
  (_ , sp , st) <- c-strip-strip-join st0 st1
  let Q1 = weaken-process (weaken-here null-p) Q1 -- make room for the witness
  let Q2 = weaken-process (weaken-here null-p) Q2 -- make room for the witness
  just (_ , st , Let sp E' λ { true -> Q1 ; false -> Q2 })

module EchoServer where
  server : SimpleProcess (Chan #ω #0 (DepN λ x -> Chan #0 #1 (DepN λ y -> Pure (x ≡ y))) :: [])
  server = Rep (Recv var-here
                     (LetN (var var-here)
                           λ x -> Send (var-next var-here) (val (depn x (pure refl)))))

module DependentPairN where
  data-type : ℕ -> SimpleType
  data-type zero = Pure ℕ
  data-type (suc n) = Pair (Pure ℕ) (Chan #1 #0 (data-type n))

  send-type : SimpleType
  send-type = Chan #0 #1 (DepN λ n -> Chan #1 #0 (data-type n))

  recv-type : SimpleType
  recv-type = Chan #1 #0 (DepN λ n -> Chan #1 #0 (data-type n))

  recv-data : ∀{σ ρ Δ} -> (n : ℕ) -> SimpleProcess (Pure ℕ :: Chan σ ρ (data-type n) :: Δ)
  recv-data zero = Recv (var-next var-here) Idle
  recv-data (suc n) = Recv (var-next var-here) (Let (var var-here) (recv-data n))

  send-data : ∀{σ ρ Δ} -> (n : ℕ) -> SimpleProcess (Chan σ ρ (data-type n) :: Δ)
  send-data zero = Send var-here (val (pure zero))
  send-data (suc n) =
    New _ _ _
        (Par (Send (var-next var-here) (val (pair (pure (suc n)) (chan var-here))))
             (send-data n))

  sender : (n : ℕ) -> SimpleProcess (send-type :: [])
  sender n = New _ _ (data-type n)
                 (Par (Send (var-next var-here) (val (depn n (chan var-here))))
                      (send-data n))

  receiver : SimpleProcess (recv-type :: [])
  receiver = Recv var-here (LetN (var var-here) recv-data)

  test : (n : ℕ) -> Process (Pure ℕ :: Chan #1 #0 (fold (t-make (data-type n))) :: [])
  test n = let _ , st , null , f = check-process-n {λ n -> Chan #1 #0 (data-type n)} recv-data {[]} in
           let P = f n in
           P

module Rename where
  Renaming : SimpleContext -> SimpleContext -> Set₁
  Renaming Γ Δ = ∀{t} -> SimpleVar Γ t -> SimpleVar Δ t

  extend : ∀{Γ Δ t} -> Renaming Γ Δ -> Renaming (t :: Γ) (t :: Δ)
  extend ren var-here = var-here
  extend ren (var-next x) = var-next (ren x)

  value : ∀{Γ Δ t v} -> Renaming Γ Δ -> SimpleValue Γ t v -> SimpleValue Δ t v
  value ren (pure x) = pure x
  value ren (chan x) = chan (ren x)
  value ren (pair V W) = pair (value ren V) (value ren W)
  value ren (depn n V) = depn n (value ren V)
  value ren (depb b V) = depb b (value ren V)

  expression : ∀{Γ Δ t} -> Renaming Γ Δ -> SimpleExpression Γ t -> SimpleExpression Δ t
  expression ren (val V) = val (value ren V)
  expression ren (var x) = var (ren x)

  process : ∀{Γ Δ} -> Renaming Γ Δ -> SimpleProcess Γ -> SimpleProcess Δ
  process ren Idle = Idle
  process ren (Send x E) = Send (ren x) (expression ren E)
  process ren (Recv x P) = Recv (ren x) (process (extend ren) P)
  process ren (Par P Q) = Par (process ren P) (process ren Q)
  process ren (New σ ρ t P) = New σ ρ t (process (extend ren) P)
  process ren (Rep P) = Rep (process ren P)
  process ren (Let E P) = Let (expression ren E) (process (extend (extend ren)) P)
  process ren (LetN E F) = LetN (expression ren E) F
  process ren (LetB E P Q) = LetB (expression ren E) (process (extend ren) P) (process (extend ren) Q)

module Session where
  send :
    ∀{Δ σ ρ σ' ρ' t s v} ->
    SimpleVar Δ (Chan σ ρ (Pair t (Chan σ' ρ' s))) ->
    SimpleValue Δ t v ->
    SimpleProcess (Chan σ' ρ' s :: Δ) ->
    SimpleProcess Δ
  send x V P =
    New _ _ _ (Par (Send (var-next x) (val (pair (Rename.value var-next V) (chan var-here)))) P)

  receive :
    ∀{Δ σ ρ σ' ρ' t s} ->
    SimpleVar Δ (Chan σ ρ (Pair t (Chan σ' ρ' s))) ->
    SimpleProcess (t :: Chan σ' ρ' s :: Δ) ->
    SimpleProcess Δ
  receive x P = Recv x (Let (var var-here) (Rename.process (Rename.extend (Rename.extend var-next)) P))

  left :
    ∀{Δ σ ρ σ' ρ' t f} ->
    SimpleVar Δ (Chan σ ρ (DepB λ { true -> Chan σ' ρ' t ; false -> Chan σ' ρ' f })) ->
    SimpleProcess (Chan σ' ρ' t :: Δ) ->
    SimpleProcess Δ
  left x P = New _ _ _ (Par (Send (var-next x) (val (depb true (chan var-here)))) P)

  right :
    ∀{Δ σ ρ σ' ρ' t f} ->
    SimpleVar Δ (Chan σ ρ (DepB λ { true -> Chan σ' ρ' t ; false -> Chan σ' ρ' f })) ->
    SimpleProcess (Chan σ' ρ' f :: Δ) ->
    SimpleProcess Δ
  right x P = New _ _ _ (Par (Send (var-next x) (val (depb false (chan var-here)))) P)

  branch :
    ∀{Δ σ ρ σ1 ρ1 σ2 ρ2 t f} ->
    SimpleVar Δ (Chan σ ρ (DepB λ { true -> Chan σ1 ρ1 t ; false -> Chan σ2 ρ2 f })) ->
    SimpleProcess (Chan σ1 ρ1 t :: Δ) ->
    SimpleProcess (Chan σ2 ρ2 f :: Δ) ->
    SimpleProcess Δ
  branch x P Q =
    let P = Rename.process (Rename.extend var-next) P in
    let Q = Rename.process (Rename.extend var-next) Q in
    Recv x (LetB (var var-here) P Q)
