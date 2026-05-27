-- https://ucilnica.fmf.uni-lj.si/pluginfile.php/183756/mod_resource/content/3/project.pdf

module projekt where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _⊔_)
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

-- * Problem 1 --
-----------------
-- Define a type of formulas called Formula, with the following grammar:
--   Formula → Var n
--           | ¬ Formula
--           | Formula ∧ Formula
--           | Formula ∨ Formula

data Formula : Set where
  Var : ℕ → Formula
  ¬A_  : Formula → Formula
  _∧A_ : Formula → Formula → Formula
  _∨A_ : Formula → Formula → Formula

infixr 6 _∧A_
infixr 5 _∨A_


-- * Problem 2 --
-----------------
-- Define a type of negation normal form formulas called NNF, with the following grammar:
--   Literal → Var n
--           | ¬ Var n
--   NNF → Literal
--       | NNF ∧ NNF
--       | NNF ∨ NNF

data Literal : Set where
  Pos : ℕ → Literal
  Neg : ℕ → Literal

neg-lit : Literal → Literal
neg-lit (Pos n) = Neg n
neg-lit (Neg n) = Pos n

infixr 6 _∧An_
infixr 5 _∨An_

data NNF : Set where
  lit  : Literal → NNF
  _∧An_ : NNF → NNF → NNF
  _∨An_ : NNF → NNF → NNF


-- * Problem 3 --
-----------------
-- Construct a function to-nnf of type Formula → NNF that converts a formula
-- to an equivalent formula in negation normal form.

to-nnf : Formula → NNF
to-nnf (Var x) = lit ( Pos x )
to-nnf (¬A Var x) = lit ( Neg x)
to-nnf (¬A (¬A f)) = to-nnf f
to-nnf (¬A (f ∧A g)) = to-nnf (¬A f) ∨An to-nnf ( ¬A g)
to-nnf (¬A (f ∨A g)) = to-nnf (¬A f) ∧An to-nnf ( ¬A g)
to-nnf (f ∧A g) = to-nnf f ∧An to-nnf g
to-nnf (f ∨A g) = to-nnf f ∨An to-nnf g

-- * Problem 4 --
-----------------
-- Copy the Assoc module from week 9 exercises and complete it to a fully
-- working implementation of an associative structure (associative list, dictionary, etc.).
-- Then use:
--   open Assoc ℕ test-≡ Bool
--   Assignment : Set
--   Assignment = Assoc

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
  lookup {_} {x ∷ kvs} (∈-there p) = lookup p
 
  
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


-- * Problem 5 --
-----------------
-- Define an evaluation function eval : Assignment → Formula → Maybe Bool
-- assigning to each assignment of variables and formula its truth value.

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
eval asg (¬A ϕ) with (eval asg ϕ)
... | just x = just (not x)
... | nothing = nothing
eval asg (ϕ ∧A ψ) with (eval asg ϕ) , (eval asg ψ)
... | (just x , just y) = just (x ∧ y)
... | _ = nothing

eval asg (ϕ ∨A ψ) with ((eval asg ϕ) , (eval asg ψ))
... | (just x , just y) = just (x ∨ y)
... | _ = nothing

-- * Problem 6 --
-----------------
-- Define an evaluation function eval-nnf : Assignment → NNF → Maybe Bool
-- assigning to each assignment of variables and NNF formula its truth value.

eval-literal : Assignment → Literal → Maybe Bool
eval-literal asg (Pos x) = asg ‼ x
eval-literal asg (Neg x) with asg ‼ x
... | just b = just (not b)
... | nothing = nothing

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf asg (lit (Pos x)) = asg ‼ x
eval-nnf asg (lit (Neg x)) = eval asg (¬A ( Var x ))
eval-nnf asg (ϕ ∧An ψ) with ((eval-nnf asg ϕ) , (eval-nnf asg ψ))
... | just x , just y = just (x ∧ y)
... | _ , _ = nothing
eval-nnf asg (ϕ ∨An ψ) with ( (eval-nnf asg ϕ) , (eval-nnf asg ψ) )
... | just x , just y = just (x ∨ y)
... | _ , _ = nothing

-- * Problem 7 --
-----------------
-- Define a type of conjunction normal form formulas called CNF, with the following grammar:
--   Literal  → Var n
--            | ¬ Var n
--   Disjunct → Literal
--            | Literal ∨ Disjunct
--   CNF      → Disjunct ∨ CNF


Disjunct = List Literal
CNF = List Disjunct

litd : Literal → Disjunct
litd x = x ∷ []

-- Problem 8 --
---------------
-- Define an evaluation function eval-cnf : Assignment → CNF → Maybe Bool
-- assigning to each assignment of variables and CNF formula its truth value.

eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct asg []      = just false
eval-disjunct asg (x ∷ p) with eval-literal asg x | eval-disjunct asg p
... | just a  | just b  = just (a ∨ b)
... | _       | _       = nothing

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf asg []      = just true
eval-cnf asg (d ∷ p) with eval-disjunct asg d | eval-cnf asg p
... | just a  | just b  = just (a ∧ b)
... | _       | _       = nothing

-- * Problem 9 --
-----------------
-- Write a SAT solver for CNF formulas.
-- Output: either an assignment such that eval-cnf asg cnf ≡ just true,
--         or a proof that no such assignment exists.
-- Note: a more complex implementation (e.g. DPLL) will be graded higher.

Units = List Literal -- list unitov
Literals = List Literal -- list literalov

data SatResult (cnf : CNF) : Set where
  sat   : (asg : Assignment) → eval-cnf asg cnf ≡ just true → SatResult cnf
  unsat : (∀ (asg : Assignment) → eval-cnf asg cnf ≢ just true) → SatResult cnf

sat-solver : (cnf : CNF) → SatResult cnf
sat-solver ϕ = {!  !}

all-literals : (cnf : CNF) → Literals
all-literals [] = []
all-literals ([] ∷ cnf) = all-literals cnf
all-literals ((x ∷ xs) ∷ cnf) = {!   !}

contradiction : (cnf : CNF) → (asg : Assignment) → Bool
contradiction [] asg = true
contradiction (x ∷ cnf) asg with (eval-disjunct asg x)
... | just b = not b ∨ contradiction cnf asg
... | nothing = contradiction cnf asg

find-units : (cnf : CNF) → Units -- list unitov
find-units [] = []
find-units ([] ∷ cnf) = find-units cnf
find-units ((x ∷ []) ∷ cnf) = x ∷ (find-units cnf)
find-units ((x ∷ _ ∷ xs) ∷ cnf) = find-units cnf

-- find-unit-clause : (cnf : CNF) → Maybe Formula
-- find-unit-clause ϕ = {!   !}

-- choose nekej
-- preveri unit clause (while)

-- * Problem 10 --
------------------
-- Show that the SAT solver is correct, if that is not obvious from the output type.
-- i.e. if the solver returns an assignment, prove eval-cnf asg cnf ≡ just true.

-- * Problem 11 --
------------------
-- Write a function that converts an NNF formula to an equisatisfiable CNF formula.
-- Note: Tseytin transformation intended; simpler implementation accepted for partial credit.

-- First see the largest variable index used so we keep same var indices

max-var-lit : Literal → ℕ
max-var-lit (Pos n) = n
max-var-lit (Neg n) = n
    
max-var-nnf : NNF → ℕ
max-var-nnf (lit x)   = max-var-lit x
max-var-nnf (ϕ ∧An ψ) = max-var-nnf ϕ ⊔ max-var-nnf ψ
max-var-nnf (ϕ ∨An ψ) = max-var-nnf ϕ ⊔ max-var-nnf ψ
  
tseytin : NNF → ℕ → (Literal × CNF × ℕ)
tseytin (lit x) n = (x , [] , n)
tseytin (ϕ ∧An ψ) n =
  let (a , csl , nl) = tseytin ϕ n
      (b , csr , nr) = tseytin ψ nl
      x  = Pos nr
      ¬x = Neg nr
      c1 = ¬x ∷ a ∷ []
      c2 = ¬x ∷ b ∷ []
      c3 = neg-lit a ∷ (neg-lit b ∷ x ∷ [])
  in (x , csl ++ csr ++ (c1 ∷ c2 ∷ c3 ∷ []) , suc nr)
tseytin (ϕ ∨An ψ) n =
  let (a , csl , nl) = tseytin ϕ n
      (b , csr , nr) = tseytin ψ nl
      x  = Pos nr
      ¬x = Neg nr
      c1 = neg-lit a ∷ x ∷ []
      c2 = neg-lit b ∷ x ∷ []
      c3 = ¬x ∷ a ∷ b ∷ []
  in (x , csl ++ csr ++ (c1 ∷ c2 ∷ c3 ∷ []) , suc nr)
  
to-cnf : NNF → CNF
to-cnf ϕ with tseytin ϕ (suc (max-var-nnf ϕ))
... | root , cs , _ = (litd root) ∷ cs
  
-- * Problem 12 --
------------------
-- Use the above to construct a SAT solver for any Formula.
-- i.e. compose to-nnf, NNF-to-CNF, and the CNF SAT solver.
