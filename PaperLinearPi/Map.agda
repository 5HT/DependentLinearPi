
open import Data.Nat
open import Data.Maybe
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst)

open import Common
open import Language
open import Substitution
open import Weakening

record ExpressionMap (Γ Δ : Context) : Set₁ where
  inductive
  field
    mnull  : CNull Γ -> CNull Δ
    mvar   : ∀{k t} -> Var k Γ t -> ∃[ l ] Var l Δ t

record ProcessMap (Γ Δ : Context) : Set₁ where
  inductive
  field
    mexpr  : ExpressionMap Γ Δ
    split  : ∀{Γ1 Γ2} -> CSplit Γ Γ1 Γ2 -> ∃[ Δ1 ] ∃[ Δ2 ] (CSplit Δ Δ1 Δ2 × ProcessMap Γ1 Δ1 × ProcessMap Γ2 Δ2)
    scale  : ∀{Γ'} -> CScale Γ' Γ -> ∃[ Δ' ] (CScale Δ' Δ × ProcessMap Γ' Δ')
    extend : ∀{t} -> ProcessMap (t :: Γ) (t :: Δ)

NullMap : ∀{Γ Δ} -> CNull Γ -> CNull Δ
VarMap  : ∀{k Γ t} -> Var k Γ t -> ∃[ l ] Var l Δ t

map-expression :
  ∀{Γ Δ t} ->
  NullMap ->
  VarMap ->

map-expression : ∀{Γ Δ t} -> ExpressionMap Γ Δ -> Expression Γ t -> Expression Δ t
map-expression map (pure null c) = pure (ExpressionMap.mnull map null ) c
map-expression map (var x) =
  let _ , x = ExpressionMap.mvar map x in
  var x
map-expression map (pair sp E1 E2) =
  let _ , _ , sp' , map1 , map2 = ExpressionMap.msplit map sp in
  pair sp' (map-expression map1 E1) (map-expression map2 E2)
map-expression map (dep x E) = dep x (map-expression map E)

map-process : ∀{Γ Δ} -> ProcessMap Γ Δ -> Process Γ -> Process Δ
map-process map (Idle null) = Idle (ExpressionMap.mnull (ProcessMap.mexpr map) null)
map-process map (Send sp E1 E2) =
  let _ , _ , sp' , map1 , map2 = ProcessMap.split map sp in
  Send sp' (map-expression (ProcessMap.mexpr map1) E1)
           (map-expression (ProcessMap.mexpr map2) E2)
map-process map (Recv sp E P) =
  let _ , _ , sp' , map1 , map2 = ProcessMap.split map sp in
  Recv sp' (map-expression (ProcessMap.mexpr map1) E)
           (map-process (ProcessMap.extend map2) P)
map-process map (Par sp P1 P2) =
  let _ , _ , sp' , map1 , map2 = ProcessMap.split map sp in
  Par sp' (map-process map1 P1) (map-process map2 P2)
map-process map (New P) = New (map-process (ProcessMap.extend map) P)
map-process map (Rep sc P) =
  let _ , sc' , map' = ProcessMap.scale map sc in
  Rep sc' (map-process map' P)
map-process map (Let sp E f) =
  let _ , _ , sp' , map1 , map2 = ProcessMap.split map sp in
  Let sp' (map-expression (ProcessMap.mexpr map1) E)
          λ x -> map-process (ProcessMap.extend map2) (f x)

module StrengthenNothing where
  mnull : ∀{Γ Δ k} -> Insert k nothing Γ Δ -> CNull Δ -> CNull Γ
  mnull insert-here (null-:: _ null) = null
  mnull (insert-next ins) (null-:: tnull null) = null-:: tnull (mnull ins null)

  mvar : ∀{Γ Δ k n t} -> Insert n nothing Γ Δ -> Var k Δ t -> ∃[ l ] Var l Γ t
  mvar (insert-next ins) (var-here null) = _ , var-here (mnull ins null)
  mvar insert-here (var-next null-n x) = _ , x
  mvar (insert-next ins) (var-next snull x) =
    let _ , x = mvar ins x in
    _ , var-next snull x

  msplit : ∀{k Γ Γ1 Γ2 Δ} -> Insert k nothing Δ Γ -> CSplit Γ Γ1 Γ2 -> ∃[ Δ1 ] ∃[ Δ2 ] (CSplit Δ Δ1 Δ2 × ExpressionMap Γ1 Δ1 × ExpressionMap Γ2 Δ2)
  strengthen-nothing-expr : ∀{Γ Δ k} -> Insert k nothing Δ Γ -> ExpressionMap Γ Δ

  msplit ins sp with split-insert sp ins
  ... | _ , _ , _ , _ , split-n , sp' , ins1 , ins2 =
    _ , _ , sp' , strengthen-nothing-expr ins1 , strengthen-nothing-expr ins2

  strengthen-nothing-expr ins =
    record {
      mnull  = mnull ins ;
      mvar   = mvar ins
    }
