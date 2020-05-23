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
  Rep (chan scale1ω scale00 :: []) $
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (x , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (chan :: []))) $
  Send (split-p :: split-c split00 split10 :: split-p :: split-c split00 split00 :: [])
       (name (next pure (here (pure :: chan :: []))))
       (pure (pure :: chan :: pure :: chan :: []) (suc x))


{- SERVER THAT COMPUTES THE PREDECESSOR OF A NON-NULL NATURAL NUMBER -}
predecessor : Process (Chan #ω #0 (λ where .force -> Pair (Pure ℕ) (λ n -> Pair (Pure (n ≢ 0)) (λ _ -> Chan #0 #1 (λ where .force -> Pure ℕ)))) # _ :: [])
predecessor =
  Rep (chan scale1ω scale00 :: []) $
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (x , p , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (chan :: []))) $
  Let (split-p :: split-l pair :: split-p :: split-c split00 split00 :: [])
      (name (next pure (here (pure :: chan :: [])))) $
  Send (split-p :: split-c split00 split10 :: split-p :: split-p :: split-p :: split-c split00 split00 :: [])
       (name (next pure (here (pure :: pure :: pure :: chan :: []))))
       (pure (pure :: chan :: pure :: pure :: pure :: chan :: []) (checked-pred x p))
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
       (pure (chan :: null) zero)
send-data (suc n) null =
  New (Par (split-c split10 split01 :: split-c split00 split10 :: c-null-split null)
           (Send (split-c split01 split00 :: split-c split00 split10 :: c-null-split null)
                 (name (next chan (here null)))
                 (pair (split-c split01 split00 :: split-c split00 split00 :: c-null-split null)
                       (pure (chan :: chan :: null) (suc n))
                       (name (here (chan :: null)))))
           (send-data n (chan :: null)))

send : (n : ℕ) -> Process (send-type # _ :: [])
send n =
  New (Par (split-c split10 split01 :: split-c split00 split10 :: [])
           (Send (split-c split01 split00 :: split-c split00 split10 :: [])
                 (name (next chan (here [])))
                 (pair (split-c split01 split00 :: split-c split00 split00 :: [])
                       (pure (chan :: chan :: []) n)
                       (name (here (chan :: [])))))
           (send-data n (chan :: [])))

{- PROCESS THAT RECEIVES N FOLLOWED BY N MESSAGES -}

recv-data : ∀{Γ} -> CNull Γ -> (n : ℕ) -> Process (Chan #1 #0 (data-type n) # _ :: Γ)
recv-data null zero =
  Recv (split-c split10 split00 :: c-null-split null)
       (name (here null))
       (λ _ -> Idle (pure :: chan :: null))
recv-data null (suc n) =
  Recv (split-c split10 split00 :: c-null-split null)
       (name (here null))
       λ _ ->
  Let (split-l pair :: split-c split00 split00 :: c-null-split null)
      (name (here (chan :: null))) $
  weaken-process (here pure) (recv-data (pure :: chan :: null) n)

recv : Process (recv-type # _ :: [])
recv =
  Recv (split-c split10 split00 :: [])
       (name (here []))
       λ (n , _) ->
  Let (split-l pair :: split-c split00 split00 :: [])
      (name (here (chan :: []))) $
  weaken-process (here pure) (recv-data (pure :: chan :: []) n)

{- CERTIFIED ECHO SERVER -}

echo : Process (Chan #ω #0 (fold (Pair (Pure ℕ) (λ x -> Chan #0 #1 (fold (Pair (Pure ℕ) λ y -> Pure (x ≡ y)))))) # _ :: [])
echo = Rep ((chan scale1ω scale00) :: []) $
       Recv (split-c split10 split00 :: [])
            (name (here []))
            λ (x , _) ->
       Let (split-l pair :: split-c split00 split00 :: [])
           (name (here (chan :: []))) $
       Send (split-p :: split-c split00 split10 :: split-p :: split-c split00 split00 :: [])
            (name (next pure (here (pure :: (chan :: [])))))
            (pair (split-p :: split-c split00 split00 :: split-p :: split-c split00 split00 :: [])
                  (pure (pure :: chan :: pure :: chan :: []) x)
                  (pure (pure :: chan :: pure :: chan :: []) refl))
