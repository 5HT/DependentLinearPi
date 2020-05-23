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

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym; subst; subst₂)
open import Function using (_$_)

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Size
open import Data.Bool
open import Data.Nat

open import Multiplicity
open import Type
open import Context
open import Language
open import Weakening
open import HasType
open import Substitution

open import Codata.Thunk
open import ReducibleNormalForm
open import Data.Product

{- SERVER THAT COMPUTES THE SUCCESSOR OF A NATURAL NUMBER -}
successor : Process (Chan #ω #0 (λ where .force -> Pair (Pure ℕ) (λ _ -> Chan #0 #1 (λ where .force -> Pure ℕ))) # _ :: [])
successor =
  Rep (scale-c scale1ω scale00 :: []) $
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (x , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (null-c :: []))) $
  Send (split-p :: split-c split00 split10 :: split-p :: split-c split00 split00 :: [])
       (name (next null-p (here (null-p :: null-c :: []))))
       (pure (null-p :: null-c :: null-p :: null-c :: []) (suc x))


{- SERVER THAT COMPUTES THE PREDECESSOR OF A NON-NULL NATURAL NUMBER -}
predecessor : Process (Chan #ω #0 (λ where .force -> Pair (Pure ℕ) (λ n -> Pair (Pure (n ≢ 0)) (λ _ -> Chan #0 #1 (λ where .force -> Pure ℕ)))) # _ :: [])
predecessor =
  Rep (scale-c scale1ω scale00 :: []) $
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (x , p , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (null-c :: []))) $
  Let (split-p :: split-l pair :: split-p :: split-c split00 split00 :: [])
      (name (next null-p (here (null-p :: null-c :: [])))) $
  Send (split-p :: split-c split00 split10 :: split-p :: split-p :: split-p :: split-c split00 split00 :: [])
       (name (next null-p (here (null-p :: null-p :: null-p :: null-c :: []))))
       (pure (null-p :: null-c :: null-p :: null-p :: null-p :: null-c :: []) (checked-pred x p))
  where
    checked-pred : (x : ℕ) -> x ≢ 0 -> ℕ
    checked-pred zero p = ⊥-elim (p refl)
    checked-pred (suc x) _ = x

data-type : (n : ℕ) -> ∀{i} -> Thunk PreType i
data-type zero = λ where .force -> Pure ℕ
data-type (suc n) = λ where .force -> Pair (Pure ℕ) (λ _ -> Chan #1 #0 (data-type n))

send-type : ∀{i} -> PreType i
send-type = Chan #0 #1 (λ where .force -> Pair (Pure ℕ) (λ n -> Chan #1 #0 (data-type n)))

recv-type : ∀{i} -> PreType i
recv-type = Chan #1 #0 (λ where .force -> Pair (Pure ℕ) (λ n -> Chan #1 #0 (data-type n)))

{- PROCESSO THAT SENDS N FOLLOWED BY N MESSAGES -}

send-data : ∀{Γ}(n : ℕ) -> CNull Γ -> Process (Chan #0 #1 (data-type n) # _ :: Γ)
send-data zero null =
  Send (split-c split00 split10 :: c-null-split null)
       (name (here null))
       (pure (null-c :: null) zero)
send-data (suc n) null =
  New (Par (split-c split10 split01 :: split-c split00 split10 :: c-null-split null)
           (Send (split-c split01 split00 :: split-c split00 split10 :: c-null-split null)
                 (name (next null-c (here null)))
                 (pair (split-c split01 split00 :: split-c split00 split00 :: c-null-split null)
                       (pure (null-c :: null-c :: null) (suc n))
                       (name (here (null-c :: null)))))
           (send-data n (null-c :: null)))

send : (n : ℕ) -> Process (send-type # _ :: [])
send n =
  New (Par (split-c split10 split01 :: split-c split00 split10 :: [])
           (Send (split-c split01 split00 :: split-c split00 split10 :: [])
                 (name (next null-c (here [])))
                 (pair (split-c split01 split00 :: split-c split00 split00 :: [])
                       (pure (null-c :: null-c :: []) n)
                       (name (here (null-c :: [])))))
           (send-data n (null-c :: [])))

{- PROCESS THAT RECEIVES N FOLLOWED BY N MESSAGES -}

recv-data : ∀{Γ} -> CNull Γ -> (n : ℕ) -> Process (Chan #1 #0 (data-type n) # _ :: Γ)
recv-data null zero =
  Recv (split-c split10 split00 :: c-null-split null)
       (name (here null))
       (λ _ -> Idle (null-p :: null-c :: null))
recv-data null (suc n) =
  Recv (split-c split10 split00 :: c-null-split null)
       (name (here null))
       λ _ ->
  Let (split-l pair :: split-c split00 split00 :: c-null-split null)
      (name (here (null-c :: null))) $
  weaken-process (here null-p) (recv-data (null-p :: null-c :: null) n)

recv : Process (recv-type # _ :: [])
recv =
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (n , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (null-c :: []))) $
  weaken-process (here null-p) (recv-data (null-p :: null-c :: []) n)

{- CERTIFIED ECHO SERVER -}

echo : Process (Chan #ω #0 (fold (Pair (Pure ℕ) (λ x -> Chan #0 #1 (fold (Pair (Pure ℕ) λ y -> Pure (x ≡ y)))))) # _ :: [])
echo = Rep ((scale-c scale1ω scale00) :: []) $
       Recv (split-c split10 split00 :: [])
            (name (here []))
            λ (x , _) ->
       Let (split-l pair :: split-c split00 split00 :: [])
           (name (here (null-c :: []))) $
       Send (split-p :: split-c split00 split10 :: split-p :: split-c split00 split00 :: [])
            (name (next null-p (here (null-p :: (null-c :: [])))))
            (pair (split-p :: split-c split00 split00 :: split-p :: split-c split00 split00 :: [])
                  (pure (null-p :: null-c :: null-p :: null-c :: []) x)
                  (pure (null-p :: null-c :: null-p :: null-c :: []) refl))
