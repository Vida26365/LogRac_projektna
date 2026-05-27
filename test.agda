module test where

open import projekt
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


test-formula = (Var 0 ∧A Var 1) ∨A (¬A Var 2) -- (x ∧ y) ∨ (¬ z)
-- to-neg test-formula ->> lit (Pos 0) ∧An lit (Pos 1) ∨An lit (Neg 2)

-- should be just false, not just true (AND bug)
test-and : Maybe Bool
test-and = eval ((0 , true) ∷ (1 , false) ∷ []) (Var 0 ∧A Var 1)

test-eval-neg : Maybe Bool
test-eval-neg = eval ((0 , true) ∷ []) (¬A Var 0)
-- C-c C-n test-eval-neg  →  just false

test-nnf : NNF
test-nnf = to-nnf (¬A (Var 0 ∧A Var 1))
-- C-c C-n test-nnf  →  lit (Neg 0) ∨An lit (Neg 1)

-- to-cnf on a leaf: just the unit clause
test-cnf-leaf : CNF
test-cnf-leaf = to-cnf (lit (Pos 0))
-- C-c C-n  →  (Pos 0 ∷ []) ∷ []

-- to-cnf on a conjunction: unit clause + 3 Tseytin clauses for the ∧ gate
test-cnf-and : CNF
test-cnf-and = to-cnf (lit (Pos 0) ∧An lit (Pos 1))
-- C-c C-n shows the fresh var (Pos 2) and the encoded clauses

-- End-to-end: to-nnf then to-cnf, then eval under a satisfying assignment
-- (x ∧ y) ∨ ¬z  with  x=true, y=true, z=false, gate vars also true
test-end-to-end : Maybe Bool
test-end-to-end =
  eval-cnf ((0 , true) ∷ (1 , true) ∷ (2 , false)
         ∷ (3 , true) ∷ (4 , true) ∷ (5 , true) ∷ [])
           (to-cnf (to-nnf test-formula))
-- C-c C-n  →  hopefully just true
