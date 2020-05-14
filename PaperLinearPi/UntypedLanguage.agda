
open import Language
open import SimpleLanguage
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst)

open import Data.Bool
open import Data.Nat
open import Data.String using (String; _==_)
open import Codata.Thunk
open import Data.Maybe
open import Data.Product

{- NAMED CONTEXT -}

data NamedContext : Set₁ where
  []     : NamedContext
  _∈_::_ : String -> SimpleType -> NamedContext -> NamedContext

{- SIMPLE EXPRESSION -}

data Index : NamedContext -> SimpleContext -> Set where
  index-[] : Index [] []
  index-:: : ∀{Γ Δ x t} -> Index Γ Δ -> Index (x ∈ t :: Γ) (t :: Δ)

index : (Γ : NamedContext) -> ∃[ Δ ] Index Γ Δ
index [] = [] , index-[]
index (_ ∈ t :: Γ) =
  let Δ , idx = index Γ in
  t :: Δ , index-:: idx

index-injective : {Γ : NamedContext} {Δ1 Δ2 : SimpleContext} -> Index Γ Δ1 -> Index Γ Δ2 -> Δ1 ≡ Δ2
index-injective index-[] index-[] = refl
index-injective (index-:: idx1) (index-:: idx2) = cong (_ ::_) (index-injective idx1 idx2)

data UntypedExpression : Set₁ where
  #     : ∀{A : Set} -> A -> UntypedExpression
  $     : String -> UntypedExpression
  ⟨_,_⟩ : UntypedExpression -> UntypedExpression -> UntypedExpression

{- UNTYPED PROCESS -}

data UntypedProcess : Set₁ where
  DONE       : UntypedProcess
  _!⟨_⟩      : UntypedExpression -> UntypedExpression -> UntypedProcess
  _?⟨_⟩_     : UntypedExpression -> String -> UntypedProcess -> UntypedProcess
  _||_       : UntypedProcess -> UntypedProcess -> UntypedProcess
  NEW_∈_IN_  : String -> SimpleType -> UntypedProcess -> UntypedProcess
  REP        : UntypedProcess -> UntypedProcess
  SPLIT_AS_,_∈_,_IN_ :
    UntypedExpression -> String -> String -> Type -> Type -> UntypedProcess -> UntypedProcess

infer-var : (Γ : NamedContext) -> String -> Maybe (∃[ Δ ] ∃[ t ] (Index Γ Δ × SimpleVar Δ t) )
infer-var [] x = nothing
infer-var (x ∈ s :: Γ) y with x == y
... | false = do
  (Δ , t , idx , z) <- infer-var Γ y
  just (s :: Δ , t , index-:: idx , var-next z)
... | true = do
  let Δ , idx = index Γ
  just (s :: Δ , s , index-:: idx , var-here)

infer-expression : (Γ : NamedContext) -> UntypedExpression -> Maybe (∃[ Δ ] ∃[ t ] (Index Γ Δ × SimpleExpression Δ t))
infer-expression Γ (# c) =
  let Δ , idx = index Γ in
  just (Δ , _ , idx , pure c)
infer-expression Γ ($ x) = do
  (Δ , t , idx , y) <- infer-var Γ x
  just (Δ , t , idx , var y)
infer-expression Γ ⟨ E1 , E2 ⟩ = do
  (Δ , t , idx1 , F1) <- infer-expression Γ E1
  (_ , s , idx2 , F2) <- infer-expression Γ E2
  refl <- just (index-injective idx1 idx2)
  just (Δ , Pair t s , idx1 , pair F1 F2)

postulate match-type : (t s : SimpleType) -> Maybe (t ≡ s)

as-simple-channel : (s : SimpleType) -> Maybe (∃ λ (t : ∀{i} -> Thunk PreType i) -> s ≡ [ t ])
as-simple-channel [ t ] = just (t , refl)
as-simple-channel _ = nothing

as-simple-pair : (s : SimpleType) -> Maybe (∃[ t1 ] ∃[ t2 ] (s ≡ Pair t1 t2))
as-simple-pair (Pair t s) = just (t , s , refl)
as-simple-pair _ = nothing

infer-process : (Γ : NamedContext) -> UntypedProcess -> Maybe (∃[ Δ ] (Index Γ Δ × SimpleProcess Δ))
infer-process Γ DONE =
  let Δ , idx = index Γ in
  just (Δ , idx , Idle)
infer-process Γ (E1 !⟨ E2 ⟩) = do
  (Δ , t , idx1 , F1) <- infer-expression Γ E1
  (_ , s , idx2 , F2) <- infer-expression Γ E2
  (t , refl) <- as-simple-channel t
  refl <- match-type (t-strip (t .force)) s
  refl <- just (index-injective idx1 idx2)
  just (Δ , idx1 , Send F1 F2)
infer-process Γ (E ?⟨ x ⟩ P) = do
  (Δ , t , idx1 , F) <- infer-expression Γ E
  (t , refl) <- as-simple-channel t
  (_ , idx2 , Q) <- infer-process (x ∈ t-strip (t .force) :: Γ) P
  refl <- just (index-injective (index-:: idx1) idx2)
  just (Δ , idx1 , Recv F Q)
infer-process Γ (P1 || P2) = do
  (Δ , idx1 , Q1) <- infer-process Γ P1
  (_ , idx2 , Q2) <- infer-process Γ P2
  refl <- just (index-injective idx1 idx2)
  just (Δ , idx1 , Par Q1 Q2)
infer-process Γ (NEW x ∈ t IN P) = do
  (t :: Δ , index-:: idx , Q) <- infer-process (x ∈ t :: Γ) P
  (s , refl) <- as-simple-channel t
  just (Δ , idx , New s Q)
infer-process Γ (REP P) = do
  (Δ , idx , Q) <- infer-process Γ P
  just (Δ , idx , Rep Q)
infer-process Γ (SPLIT E AS x , y ∈ t1 , t2 IN P) = do
  (Δ , t , idx1 , F) <- infer-expression Γ E
  (s1 , s2 , refl) <- as-simple-pair t
  (_ , index-:: (index-:: idx2) , Q) <- infer-process (x ∈ s1 :: (y ∈ s2 :: Γ)) P
  refl <- just (index-injective idx1 idx2)
  refl <- match-type (t-strip t1) s1
  refl <- match-type (t-strip t2) s2
  just (Δ , idx1 , Let t1 t2 F Q)

_ : UntypedProcess
_ = DONE

a = REP ( $ "id" ?⟨ "p" ⟩
          ( SPLIT $ "p" AS "x" , "y" ∈ {!!} , {!!} IN
            ( $ "y" !⟨ $ "x" ⟩ )
          )
        )
