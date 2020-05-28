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

open import Data.Nat
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; subst₂; cong; cong₂; sym)
open import Codata.Thunk

open import Common
open import Language
open import Congruence
open import Swap
open import Split
open import Scale
open import Weaken

module PrefixedBy where

data PrefixedBy : ∀{Γ} -> ℕ -> Multiplicity -> Multiplicity -> Process Γ -> Set where
  prefixed-send :
    ∀{k Γ Γ1 Γ2 t v}{x : Name k Γ1 (Chan #0 #1 t) _}{V : Term Γ2 (t .force) v}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixedBy k #0 #1 (Send sp (name x) V)
  prefixed-recv :
    ∀{k Γ Γ1 Γ2 t g}{x : Name k Γ1 (Chan #1 #0 t) _}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixedBy k #1 #0 (Recv sp (name x) g)
  prefixed-par-l :
    ∀{Γ Γ1 Γ2 m n k P Q}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixedBy k m n P
    -> PrefixedBy k m n (Par sp P Q)
  prefixed-par-r :
    ∀{Γ Γ1 Γ2 m n k P Q}
    -> (sp : CSplit Γ Γ1 Γ2)
    -> PrefixedBy k m n Q
    -> PrefixedBy k m n (Par sp P Q)
  prefixed-new :
    ∀{Γ m n m' n' t k P}
    -> PrefixedBy (suc k) m n P
    -> PrefixedBy k m n (New {Γ} {m'} {n'} {t} P)
  prefixed-rep :
    ∀{Γ Δ k m n P}{sc : CScale Γ Δ}
    -> PrefixedBy k m n P
    -> PrefixedBy k m n (Rep sc P)

swap-prefixed :
  ∀{k l m n Γ Δ}
  -> (sw : Swap l Γ Δ)
  -> (P : Process Γ)
  -> PrefixedBy k m n P
  -> PrefixedBy (swap-name-index l k) m n (swap-process sw P)
swap-prefixed {_} {_} {m} {n} {_} {Δ} sw (Send sp (name x) E) (prefixed-send _) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  let x' = swap-name sw1 x in
  let E' = swap-term sw2 E in
  prefixed-send sp'
swap-prefixed {_} {_} {m} {n} sw (Recv sp (name x) P) (prefixed-recv _) =
  let _ , _ , sp' , sw1 , sw2 = swap-split sw sp in
  let x' = swap-name sw1 x in
  -- let P' = swap-process (next sw2) P in -- TODO: WHAT IS THIS FOR?
  prefixed-recv sp'
swap-prefixed sw (Par sp P Q) (prefixed-par-l _ pb) =
  let _ , _ , sp' , sw' , _ = swap-split sw sp in
  let pb' = swap-prefixed sw' P pb in
  prefixed-par-l sp' pb'
swap-prefixed sw (Par sp P Q) (prefixed-par-r _ pb) =
  let _ , _ , sp' , _ , sw' = swap-split sw sp in
  let pb' = swap-prefixed sw' Q pb in
  prefixed-par-r sp' pb'
swap-prefixed sw (New P) (prefixed-new pb) =
  let pb' = swap-prefixed (next sw) P pb in
  prefixed-new pb'
swap-prefixed sw (Rep sc P) (prefixed-rep pb) =
  let _ , sw' , sc' = swap-scale sw sc in
  prefixed-rep (swap-prefixed sw' P pb)

weaken-prefixed :
  ∀{k l m n Γ Δ}
  -> (we : Weaken l Γ Δ)
  -> (P : Process Γ)
  -> PrefixedBy k m n P
  -> PrefixedBy (weaken-name-index l k) m n (weaken-process we P)
weaken-prefixed {_} {_} {m} {n} we (Send sp (name x) V) (prefixed-send _) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  let x' = weaken-name we1 x in
  let V' = weaken-term we2 V in
  prefixed-send {x = x'} {V = V'} sp'
weaken-prefixed {_} {_} {m} {n} we (Recv sp (name x) P) (prefixed-recv _) =
  let _ , _ , sp' , we1 , we2 = weaken-split we sp in
  let x' = weaken-name we1 x in
  -- let P' = weaken-process (next we2) P in -- TODO: WHAT IS THIS FOR?
  prefixed-recv sp'
weaken-prefixed we (Par sp P Q) (prefixed-par-l _ pb) =
  let _ , _ , sp' , we' , _ = weaken-split we sp in
  prefixed-par-l sp' (weaken-prefixed we' P pb)
weaken-prefixed we (Par sp P Q) (prefixed-par-r _ pb) =
  let _ , _ , sp' , _ , we' = weaken-split we sp in
  prefixed-par-r sp' (weaken-prefixed we' Q pb)
weaken-prefixed we (New P) (prefixed-new pb) =
  prefixed-new (weaken-prefixed (next we) P pb)
weaken-prefixed we (Rep sc P) (prefixed-rep pb) =
  let _ , we' , sc' = weaken-scale we sc in
  prefixed-rep (weaken-prefixed we' P pb)

weaken-not-in-term-neq :
  ∀{k l Γ σ ρ t}
  -> (x : Name k Γ (Chan σ ρ t) _)
  -> NotInTerm l (name x)
  -> l ≢ k
weaken-not-in-term-neq _ (nin-v nx) = nx

weaken-not-in-process-neq :
  ∀{k l m n Γ}
  -> (P : Process Γ)
  -> NotInProcess l P
  -> PrefixedBy k m n P
  -> l ≢ k
weaken-not-in-process-neq (Send _ (name x) _) (nin-send _ nie _) (prefixed-send _) =
  weaken-not-in-term-neq x nie
weaken-not-in-process-neq (Recv _ (name x) _) (nin-recv _ nie _) (prefixed-recv _) =
  weaken-not-in-term-neq x nie
weaken-not-in-process-neq (Par sp P _) (nin-par _ nip _) (prefixed-par-l _ pb) =
  weaken-not-in-process-neq P nip pb
weaken-not-in-process-neq (Par sp _ Q) (nin-par _ _ niq) (prefixed-par-r _ pb) =
  weaken-not-in-process-neq Q niq pb
weaken-not-in-process-neq (New P) (nin-new nip) (prefixed-new pb) =
  suc-≢ (weaken-not-in-process-neq P nip pb)
weaken-not-in-process-neq (Rep _ P) (nin-rep _ nip) (prefixed-rep pb) =
  weaken-not-in-process-neq P nip pb

strengthen-prefixed :
  ∀{k l m n Γ Δ}
  -> (we : Weaken l Γ Δ)
  -> (P : Process Δ)
  -> (nip : NotInProcess l P)
  -> (pb : PrefixedBy k m n P)
  -> let neq = weaken-not-in-process-neq P nip pb in
     PrefixedBy (strengthen-name-index l k neq) m n (strengthen-process we P nip)
strengthen-prefixed we (Send sp (name x) V) (nin-send _ (nin-v neq) niv) (prefixed-send _) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  let x' = strengthen-name we1 x neq in
  let V' = strengthen-term we2 V niv in
  prefixed-send {x = x'} {V = V'} sp'
strengthen-prefixed we (Recv sp (name x) P) (nin-recv _ (nin-v neq) nip) (prefixed-recv _) =
  let _ , _ , sp' , we1 , we2 = strengthen-split we sp in
  let x' = strengthen-name we1 x neq in
  -- let P' = strengthen-process (next we2) P nip in -- TODO: WHAT IS THIS FOR?
  prefixed-recv sp'
strengthen-prefixed we (Par sp P _) (nin-par _ nip _) (prefixed-par-l _ pb) =
  let _ , _ , sp' , we' , _ = strengthen-split we sp in
  prefixed-par-l sp' (strengthen-prefixed we' P nip pb)
strengthen-prefixed we (Par sp _ Q) (nin-par _ _ niq) (prefixed-par-r _ pb) =
  let _ , _ , sp' , _ , we' = strengthen-split we sp in
  prefixed-par-r sp' (strengthen-prefixed we' Q niq pb)
strengthen-prefixed we (New P) (nin-new nip) (prefixed-new pb) =
  prefixed-new (strengthen-prefixed (next we) P nip pb)
strengthen-prefixed we (Rep sc P) (nin-rep _ nip) (prefixed-rep pb) =
  let _ , we' , _ = strengthen-scale we sc in
  prefixed-rep (strengthen-prefixed we' P nip pb)

prefixed-cong :
  ∀{Γ k m n}{P Q : Process Γ}
  -> PrefixedBy k m n P
  -> P <= Q
  -> PrefixedBy k m n Q
prefixed-cong pb cong-refl = pb
prefixed-cong pb (cong-trans cong1 cong2) = prefixed-cong (prefixed-cong pb cong1) cong2
prefixed-cong (prefixed-par-r _ pb) cong-par-idle-lr = pb
prefixed-cong pb cong-par-idle-rl = prefixed-par-r _ pb
prefixed-cong (prefixed-par-l _ pb) (cong-par-comm sp) = prefixed-par-r (csplit-comm sp) pb
prefixed-cong (prefixed-par-r _ pb) (cong-par-comm sp) = prefixed-par-l (csplit-comm sp) pb
prefixed-cong (prefixed-par-l _ pb) (cong-par-assoc-rl sp1 sp2) =
  let _ , sp1' , sp2' = csplit-assoc-rl sp1 sp2 in
  prefixed-par-l sp1' (prefixed-par-l sp2' pb)
prefixed-cong (prefixed-par-r sp1 (prefixed-par-l sp2 pb)) (cong-par-assoc-rl _ _) =
  let _ , sp1' , sp2' = csplit-assoc-rl sp1 sp2 in
  prefixed-par-l sp1' (prefixed-par-r sp2' pb)
prefixed-cong (prefixed-par-r sp1 (prefixed-par-r sp2 pb)) (cong-par-assoc-rl _ _) =
  let _ , sp1' , _ = csplit-assoc-rl sp1 sp2 in
  prefixed-par-r sp1' pb
prefixed-cong (prefixed-par-l _ (prefixed-par-l _ pb)) (cong-par-assoc-lr sp1 sp2) =
  let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
  prefixed-par-l sp1' pb
prefixed-cong (prefixed-par-l _ (prefixed-par-r _ pb)) (cong-par-assoc-lr sp1 sp2) =
  let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
  prefixed-par-r sp1' (prefixed-par-l sp2' pb)
prefixed-cong (prefixed-par-r _ pb) (cong-par-assoc-lr sp1 sp2) =
  let _ , sp1' , sp2' = csplit-assoc-lr sp1 sp2 in
  prefixed-par-r sp1' (prefixed-par-r sp2' pb)
prefixed-cong (prefixed-new (prefixed-new {P = P} pb)) cong-new-new =
  prefixed-new (prefixed-new (swap-prefixed here P pb))
prefixed-cong (prefixed-par-l _ (prefixed-new pb)) (cong-par-new {σ = m} {ρ = n} sp) =
  let sp' = chan (msplit-l m) (msplit-l n) :: sp in
  prefixed-new (prefixed-par-l sp' pb)
prefixed-cong (prefixed-par-r {Q = Q} _ pb) (cong-par-new {σ = m} {ρ = n} sp) =
  let sp' = chan (msplit-l m) (msplit-l n) :: sp in
  let we = here chan in
  prefixed-new (prefixed-par-r sp' (weaken-prefixed we Q pb))
prefixed-cong (prefixed-new (prefixed-par-l _ pb)) (cong-new-par sp _) =
  prefixed-par-l sp (prefixed-new pb)
prefixed-cong (prefixed-new {m' = m} {n' = n} (prefixed-par-r {Q = Q} _ pb)) (cong-new-par sp niQ) =
  prefixed-par-r sp (strengthen-prefixed (here chan) Q niQ pb)
prefixed-cong (prefixed-new ()) (cong-new-idle _)
prefixed-cong (prefixed-rep pb) (cong-rep-par sc) = prefixed-par-l (c-scale-split sc) pb
prefixed-cong (prefixed-par-l _ pb) (cong-par-rep _ _) = prefixed-rep pb
prefixed-cong (prefixed-par-r _ pb) (cong-par-rep _ _) = pb
prefixed-cong (prefixed-par-l _ pb) (cong-par-cong sp pc) =
  prefixed-par-l sp (prefixed-cong pb pc)
prefixed-cong (prefixed-par-r _ pb) (cong-par-cong sp _) = prefixed-par-r sp pb
prefixed-cong (prefixed-new pb) (cong-new-cong pc) = prefixed-new (prefixed-cong pb pc)
