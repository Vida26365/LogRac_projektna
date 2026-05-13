-- https://ucilnica.fmf.uni-lj.si/pluginfile.php/183756/mod_resource/content/3/project.pdf

module projekt where

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Relation.Binary using (Decidable; DecidableEquality)
-- open import Data.List.Relation.Unary.Any using (Any; any?)
-- open import Data.List.Relation.Unary.All using (All; all?)
open import Relation.Nullary using (Dec; yes; no; ¬_; ¬?)
open import Data.Maybe using (Maybe; nothing; just)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; _≢_)
-- open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; head; _++_; map)
-- open import Data.Empty using (⊥)
---------------
-- Problem 1 --
---------------

data Formula : Set where
  Var : ℕ → Formula
  ¬A_  : Formula → Formula
  _∧A_ : Formula → Formula → Formula
  _∨A_ : Formula → Formula → Formula


---------------
-- Problem 2 --
---------------

data Literal : Set where
  Pos : ℕ → Literal
  Neg : ℕ → Literal

infixr 6 _∧An_
infixr 5 _∨An_

data NNF : Set where
  lit  : Literal → NNF
  _∧An_ : NNF → NNF → NNF
  _∨An_ : NNF → NNF → NNF


---------------
-- Problem 3 --
---------------

to-nnf : Formula → NNF
to-nnf (Var x) = lit ( Pos x )
to-nnf (¬A Var x) = lit ( Neg x)
to-nnf (¬A (¬A f)) = to-nnf f
to-nnf (¬A (f ∧A g)) = to-nnf (¬A f) ∨An to-nnf ( ¬A g)
to-nnf (¬A (f ∨A g)) = to-nnf (¬A f) ∧An to-nnf ( ¬A g)
to-nnf (f ∧A g) = to-nnf f ∧An to-nnf g
to-nnf (f ∨A g) = to-nnf f ∨An to-nnf g


---------------
-- Problem 4 --
---------------

-- data Dec (A : Set) : Set where
--   yes :    A  → Dec A
--   no  : (¬ A) → Dec A


record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType

module Assoc (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)

  data _∈_ : carr K → Assoc → Set where
    ∈-here  : {k : carr K } → {v : V} → {xs : Assoc} → k ∈ ((k , v) ∷ xs)
    ∈-there : {k : carr K} → {y : carr K × V} → {xs : Assoc} → k ∈ xs → k ∈ (y ∷ xs)

  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup {_} {x ∷ kvs} ∈-here = proj₂ x
  lookup {_} {x ∷ kvs} (∈-there ∈-here) = x .proj₂
  lookup {_} {x ∷ kvs} (∈-there (∈-there p)) = x .proj₂

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no λ ()
  
  k ∈? (x ∷ kvs) with K. test-≡ k (proj₁ x)
  ... | yes refl = yes ∈-here
  ... | no n with k ∈? kvs
  ... | yes p = yes (∈-there p) 
  ... | no p = no λ { ∈-here → n refl
                    ; (∈-there q) → p q} 

  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  [] ‼ k = nothing
  (x ∷ kvs) ‼ k  with K .test-≡ k (proj₁ x)
  ... | yes p = just (proj₂ x)
  ... | no p = kvs ‼ k

  _[_]≔_ : Assoc → carr K → V → Assoc
  kvs [ k ]≔ v = {!!}


