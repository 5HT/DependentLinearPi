
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Codata.Thunk

open import Multiplicity
open import Type
open import Context

module Language where

data Var : ℕ -> Context -> (t : Type) -> ⟦ t ⟧ -> Set₁ where
  var-here : ∀{Γ t v} -> CNull Γ -> Var zero (t # v :: Γ) t v
  var-next : ∀{k Γ t v s w} -> TNull s -> Var k Γ t v -> Var (suc k) (s # w :: Γ) t v

data Term : Context -> (t : Type) -> ⟦ t ⟧ -> Set₁ where
  var  : ∀{k Γ t v} -> Var k Γ t v -> Term Γ t v
  pure : ∀{Γ A} -> CNull Γ -> (v : A) -> Term Γ (Pure A) v
  pair : ∀{Γ Γ1 Γ2 t f v w} -> CSplit Γ Γ1 Γ2 -> Term Γ1 t v -> Term Γ2 (f v) w -> Term Γ (Pair t f) (v , w)

data Process : Context -> Set₁ where
  Idle : ∀{Γ} -> CNull Γ -> Process Γ
  Send :
    ∀{Γ Γ1 Γ2 t v} ->
    CSplit Γ Γ1 Γ2 ->
    Term Γ1 (Chan #0 #1 t) _ ->
    Term Γ2 (t .force) v ->
    Process Γ
  Recv :
    ∀{Γ Γ1 Γ2 t} ->
    CSplit Γ Γ1 Γ2 ->
    Term Γ1 (Chan #1 #0 t) _ ->
    ((x : ⟦ t .force ⟧) -> Process (t .force # x :: Γ2)) ->
    Process Γ
  Par :
    ∀{Γ Γ1 Γ2} ->
    CSplit Γ Γ1 Γ2 ->
    Process Γ1 ->
    Process Γ2 ->
    Process Γ
  New :
    ∀{Γ σ ρ t} ->
    Process (Chan σ ρ t # _ :: Γ) ->
    Process Γ
  Rep : ∀{Γ Δ} -> CScale Γ Δ -> Process Γ -> Process Δ
  Let :
    ∀{Γ Γ1 Γ2 t f v w} ->
    CSplit Γ Γ1 Γ2 ->
    Term Γ1 (Pair t f) (v , w) ->
    ((x : ⟦ t ⟧) (y : ⟦ f x ⟧) -> Process (t # x :: (f x # y :: Γ2))) ->
    Process Γ
