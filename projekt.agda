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
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
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
  [] [ k ]≔ v = (( k , v)) ∷ []
  ( x ∷ kvs) [ k ]≔ v with k ∈? (x ∷ kvs)
  ... | yes ∈-here = (k , v) ∷ kvs
  ... | yes (∈-there p) = x ∷ ( kvs [ k ]≔ v )
  ... | no p = ((k , v)) ∷ kvs 


---------------
-- Problem 5 --
---------------

_eqn_ : (m n : ℕ) → Dec (m ≡ n)
zero eqn zero = yes refl
zero eqn suc n = no (λ ())
suc m eqn zero = no (λ ())
suc m eqn suc n with m eqn n
... | yes p = yes (cong suc p)
... | no ¬p = no (λ h → ¬p (cong pred h))

open Assoc record { carr = ℕ ; test-≡ = _eqn_ } Bool

Assignment : Set 
Assignment = Assoc


eval : Assignment → Formula → Maybe Bool
eval asg (Var x) = asg ‼ x
eval asg (¬A fmn) with (eval asg fmn)
... | just false = just true
... | just true = just false
... | nothing = nothing
eval asg (fmn ∧A fml) with (eval asg fmn)
... | nothing = nothing
... | just x with (eval asg fmn)
...   | just y = just (x ∧ y)
...   | nothing = nothing
eval asg (fmn ∨A fml) with (eval asg fmn)
... | nothing = nothing
... | just x with (eval asg fml)
...   | just y = just (x ∨ y)
...   | nothing = nothing


---------------
-- Problem 6 --
---------------
eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf asg (lit (Pos x)) = asg ‼ x
eval-nnf asg (lit (Neg x)) = eval asg (¬A ( Var x ))
eval-nnf asg (nft ∧An nfn) with (eval-nnf asg nft)
... | nothing = nothing
... | just x with (eval-nnf asg nfn)
... | just y = just ( x ∧ y)
... | nothing = nothing
eval-nnf asg (nft ∨An nfn) with ( (eval-nnf asg nft) , (eval-nnf asg nfn) )
... | just x , just y = just (x ∨ y)
... | just x₁ , nothing = nothing
... | nothing , just x₁ = nothing
... | nothing , nothing = nothing

---------------
-- Problem 7 --
---------------

data Disjunct : Set where
  litd : Literal → Disjunct
  _∨d_ : Literal → Disjunct → Disjunct

data CNF : Set where
  _∨c_ : Disjunct → CNF → CNF


---------------
-- Problem 8 --
---------------

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf asg (litd x ∨c cnf) with (eval-nnf asg (lit x) , eval-cnf asg cnf )
... | just x₁ , just x₂ = just (x₁ ∨ x₂)
... | just x₁ , nothing = nothing
... | nothing , just x₁ = nothing
... | nothing , nothing = nothing
eval-cnf asg ((x ∨d d) ∨c cnf) with ( eval-nnf asg (lit x),  eval-cnf asg ( d ∨c cnf))
... | just z , just w = just (w ∨ z)
... | just x₁ , nothing = nothing
... | nothing , just x₁ = nothing
... | nothing , nothing = nothing

