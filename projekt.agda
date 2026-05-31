-- https://ucilnica.fmf.uni-lj.si/pluginfile.php/183756/mod_resource/content/3/project.pdf

module projekt where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _⊔_; _≤?_)
open import Relation.Binary using (Decidable; DecidableEquality)
-- open import Data.List.Relation.Unary.Any using (Any; any?)
-- open import Data.List.Relation.Unary.All using (All; all?)
open import Relation.Nullary using (Dec; yes; no; ¬_; ¬?)
open import Data.Maybe using (Maybe; nothing; just; _>>=_; _<∣>_)
  renaming (map to mapM)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; head; _++_; map; length; mapMaybe)
open import Level using (0ℓ)
open import Effect.Functor using (RawFunctor)   -- or Effect.Functor on ≥2.0
open import Data.Maybe.Effectful using (functor) -- or Data.Maybe.Effectful
open RawFunctor (functor {0ℓ}) using (_<$>_)
open import Data.Sum using (_⊎_; inj₁; inj₂)


-- open import Data.Empty using (⊥)

-- * Problem 1  - Formula type
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

-- * Problem 2  - NNF type
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

-- * Problem 3  - to-nnf
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

-- * Problem 4  - assoc
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

-- * Problem 5  - eval formulas
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

literal-eq : (a b : Literal) → Dec (a ≡ b)
literal-eq (Pos m) (Pos n) with m eqn n
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
literal-eq (Neg m) (Neg n) with m eqn n
... | yes refl = yes refl
... | no ¬p    = no (λ { refl → ¬p refl })
literal-eq (Pos _) (Neg _) = no (λ ())
literal-eq (Neg _) (Pos _) = no (λ ())

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

-- * Problem 6  - eval-nnf
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

-- * Problem 7  - CNF type
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

-- Originally: Partial assignments are always nothing
-- eval-disjunct : Assignment → Disjunct → Maybe Bool
-- eval-disjunct asg []      = just false
-- eval-disjunct asg (x ∷ p) with eval-literal asg x | eval-disjunct asg p
-- ... | just a  | just b  = just (a ∨ b)
-- ... | _       | _       = nothing

-- eval-cnf : Assignment → CNF → Maybe Bool
-- eval-cnf asg []      = just true
-- eval-cnf asg (d ∷ p) with eval-disjunct asg d | eval-cnf asg p
-- ... | just a  | just b  = just (a ∧ b)
-- ... | _       | _       = nothing

-- For easier DPLL verification, we consider an incomplete assignment with extraneous variables as true, e.g.
-- assigning (x₀ = true) means that (x₀ ∨ x₁) evaluates to true

or-maybe : Maybe Bool → Maybe Bool → Maybe Bool
or-maybe (just true)  _           = just true
or-maybe _            (just true) = just true
or-maybe (just false) y           = y
or-maybe nothing      _           = nothing

and-maybe : Maybe Bool → Maybe Bool → Maybe Bool
and-maybe (just false) _            = just false
and-maybe _            (just false) = just false
and-maybe (just true)  y            = y
and-maybe nothing      _            = nothing

eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct asg []      = just false
eval-disjunct asg (x ∷ p) = or-maybe (eval-literal asg x) (eval-disjunct asg p)

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf asg []      = just true
eval-cnf asg (d ∷ p) = and-maybe (eval-disjunct asg d) (eval-cnf asg p)

-- * Problem 9  - DPLL
-----------------
-- Write a SAT solver for CNF formulas.
-- Output: either an assignment such that eval-cnf asg ϕ ≡ just true,
--         or a proof that no such assignment exists.
-- Note: a more complex implementation (e.g. DPLL) will be graded higher.

-- We adapted some core functions from https://github.com/joshuaguerin/DPLL/blob/main/DPLL.hs

Units = List Literal -- list unitov
Literals = List Literal -- list literalov

----------------  Vse to je za filterDuplicates, da lahko dobimo literals
PosLiterals = List Literal
NegLiterals = List Literal

SortPosLiterals = List Literal
SortNegLiterals = List Literal

pos-sorted-insert : (x : ℕ) → (ltrs : SortPosLiterals) → SortPosLiterals -- sortirani pozitivni literali
pos-sorted-insert x [] = Pos x ∷ []
pos-sorted-insert x (Neg y ∷ litrs) = pos-sorted-insert x litrs 
pos-sorted-insert x (Pos y ∷ litrs) with x ≤? y
... | yes _ = Pos x ∷ Pos y ∷ litrs
... | no _ = Pos y ∷ pos-sorted-insert x litrs

neg-sorted-insert : (x : ℕ) → (ltrs : SortNegLiterals) → SortNegLiterals -- sortirani negativni literali
neg-sorted-insert x [] = Neg x ∷ []
neg-sorted-insert x (Pos y ∷ litrs) = neg-sorted-insert x litrs 
neg-sorted-insert x (Neg y ∷ litrs) with x ≤? y
... | yes _ = Neg x ∷ Neg y ∷ litrs
... | no _ = Neg y ∷ neg-sorted-insert x litrs

pos-sort : (litrs : Literals) → SortPosLiterals
pos-sort [] = []
pos-sort (Pos x ∷ litrs) = pos-sorted-insert x (pos-sort litrs)
pos-sort (Neg x ∷ litrs) = pos-sort litrs

neg-sort : (litrs : Literals) → SortNegLiterals
neg-sort [] = []
neg-sort (Neg x ∷ litrs) = neg-sorted-insert x (neg-sort litrs)
neg-sort (Pos x ∷ litrs) = neg-sort litrs

sort-literals : (litr : Literals) → PosLiterals × NegLiterals
sort-literals litr = (pos-sort litr) , (neg-sort litr)

all-literals' : (ϕ : CNF) → Literals -- nefiltrirani
all-literals' [] = []
all-literals' ([] ∷ ϕ) = all-literals' ϕ
all-literals' ((x ∷ xs) ∷ ϕ) = x ∷ all-literals' (xs ∷ ϕ)

reduce-disjunct : Assignment → Disjunct → Maybe Disjunct
reduce-disjunct asg [] = just []
reduce-disjunct asg (x ∷ dis) with eval-literal asg x
... | just true  = nothing
... | just false = reduce-disjunct asg dis
... | nothing with reduce-disjunct asg dis
...   | nothing  = nothing
...   | just dis' = just (x ∷ dis') -- skip unassigned terms

reduce-cnf : Assignment → CNF → CNF
reduce-cnf asg = mapMaybe (reduce-disjunct asg)

units-to-assign : Units → Assignment
units-to-assign [] = []
units-to-assign (Pos x ∷ unt) = (x , true ) ∷ units-to-assign unt
units-to-assign (Neg x ∷ unt) = (x , false) ∷ units-to-assign unt

lit→pair : Literal → ℕ × Bool
lit→pair (Pos x) = x , true
lit→pair (Neg x) = x , false

-- Single unit at a time
find-unit : (ϕ : CNF) → Maybe Literal
find-unit [] = nothing
find-unit ([] ∷ ϕ) = find-unit ϕ
find-unit ((x ∷ []) ∷ ϕ) = just x
find-unit ((x ∷ _ ∷ xs) ∷ ϕ) = find-unit ϕ

unit-propagate : (ϕ : CNF) → CNF × Maybe Literal
unit-propagate ϕ with find-unit ϕ
... | nothing = ϕ , nothing
... | just l  = reduce-cnf ((lit→pair l) ∷ []) ϕ , just l

has-empty-clause : CNF → Bool
has-empty-clause [] = false
has-empty-clause ([] ∷ _)      = true -- empty disjunct found → conflict
has-empty-clause ((_ ∷ _) ∷ ϕ) = has-empty-clause ϕ

choose-lit : (ϕ : CNF) → Maybe Literal
choose-lit [] = nothing
choose-lit ([] ∷ ϕ) = choose-lit ϕ
choose-lit ((x ∷ _) ∷ _) = just x

-- DPLL implementation itself
-- Left out pure literal elimination since we mentioned in class it doesn't actually speed things up in practice

Sat : CNF → Set
Sat ϕ = ∃ λ asg → eval-cnf asg ϕ ≡ just true

dpll-helper-v : ℕ → (asg : Assignment) → (ϕ : CNF) → Maybe (Sat ϕ)
dpll-helper-v _ asg [] = just (asg , refl)
dpll-helper-v zero asg ϕ = nothing
dpll-helper-v (suc n) asg ϕ with has-empty-clause ϕ , unit-propagate ϕ
... | true , _ = nothing
... | false , ϕ' , just l with dpll-helper-v n (lit→pair l ∷ asg) ϕ'
...   | nothing = nothing
...   | just (a , p) = just (a , {!!})
dpll-helper-v (suc n) asg ϕ | false , ϕ' , nothing with choose-lit ϕ'
...   | nothing = nothing
...   | just l = let l' = neg-lit l in
       mapM (λ { (a , p) → a , {!!} })
                 (dpll-helper-v n (lit→pair l ∷ asg) (reduce-cnf (units-to-assign (l ∷ [])) ϕ'))
       <∣>
       mapM (λ { (a , p) → a , {!!} })
                 (dpll-helper-v n (lit→pair l' ∷ asg) (reduce-cnf (units-to-assign (l' ∷ [])) ϕ'))

dpll-helper : ℕ → (asg : Assignment) → (ϕ : CNF) → Maybe Assignment
dpll-helper _ asg [] = just asg -- Empty conjunction is true
dpll-helper zero asg ϕ = nothing -- Out of fuel
dpll-helper (suc n) asg ϕ with has-empty-clause ϕ , unit-propagate ϕ
... | true , _ = nothing -- Empty clause, unsat
... | false , ϕ' , just l = dpll-helper n (lit→pair l ∷ asg) ϕ' -- Unit found, recurse
... | false , ϕ' , nothing with choose-lit ϕ' -- No unit, choose literal and branch
...   | nothing = nothing
...   | just l = let
  l' = neg-lit l
  pos = dpll-helper n (lit→pair l  ∷ asg) (reduce-cnf (units-to-assign (l  ∷ [])) ϕ')
  neg = dpll-helper n (lit→pair l' ∷ asg) (reduce-cnf (units-to-assign (l' ∷ [])) ϕ')
  in pos <∣> neg

-- The unverified version used complete-assignment with the previous eval to pick arbitrary variables
dpll : CNF → Maybe Assignment
dpll ϕ = dpll-helper (length (all-literals' ϕ)) [] ϕ

-- dpll : (ϕ : CNF) → Maybe (Sat ϕ)
-- dpll ϕ = dpll-helper (length (all-literals' ϕ)) [] ϕ

-- We previously used complete-assignment with the stricter eval
max-var-lit : Literal → ℕ
max-var-lit (Pos n) = n
max-var-lit (Neg n) = n

max-var-disjunct : Disjunct → ℕ
max-var-disjunct [] = 0
max-var-disjunct (Pos x ∷ d) = x ⊔ max-var-disjunct d
max-var-disjunct (Neg x ∷ d) = x ⊔ max-var-disjunct d

max-var-cnf : CNF → ℕ
max-var-cnf [] = 0
max-var-cnf (x ∷ ϕ) = max-var-disjunct x ⊔ max-var-cnf ϕ

-- Add missing variables that don't matter for the assignment dpll finds
complete-assignment : ℕ → Assignment → Assignment
complete-assignment zero asg with zero ∈? asg
... | yes _ = asg
... | no  _ = (zero , false) ∷ asg
complete-assignment (suc n) asg with (suc n) ∈? asg
... | yes _ = complete-assignment n asg
... | no  _ = complete-assignment n ((suc n , false) ∷ asg)


-- * Problem 10 - SAT correctness
------------------
-- Show that the SAT solver is correct, if that is not obvious from the output type.


-- * Problem 11 - Tseytin
------------------
-- Write a function that converts an NNF formula to an equisatisfiable CNF formula.
-- Note: Tseytin transformation intended; simpler implementation accepted for partial credit.

-- First see the largest variable index used so we keep same var indices
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
  
nnf-to-cnf : NNF → CNF
nnf-to-cnf ϕ with tseytin ϕ (suc (max-var-nnf ϕ))
... | root , cs , _ = (litd root) ∷ cs
  
-- * Problem 12 - SAT for any formula
------------------
-- Use the above to construct a SAT solver for any Formula.
-- i.e. compose to-nnf, NNF-to-CNF, and the CNF SAT solver.

sat : Formula → Maybe Assignment
sat ϕ = dpll (nnf-to-cnf (to-nnf ϕ))

-- sat : Formula → Maybe Assignment
-- sat ϕ = mapM proj₁ (dpll (nnf-to-cnf (to-nnf ϕ)))

