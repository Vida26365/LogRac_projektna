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
open import Data.List using (List; []; _∷_; head; _++_; map; length)
-- open import Data.Empty using (⊥)


test-formula = (Var 0 ∧A Var 1) ∨A (¬A Var 2) -- (x ∧ y) ∨ (¬ z)
-- to-neg test-formula ->> lit (Pos 0) ∧An lit (Pos 1) ∨An lit (Neg 2)

test-cnf = nnf-to-cnf (to-nnf test-formula)

-- should be just false, not just true (AND bug)
test-and : Maybe Bool
test-and = eval ((0 , true) ∷ (1 , false) ∷ []) (Var 0 ∧A Var 1)

test-eval-neg : Maybe Bool
test-eval-neg = eval ((0 , true) ∷ []) (¬A Var 0)
-- C-c C-n test-eval-neg  →  just false

test-nnf : NNF
test-nnf = to-nnf (¬A (Var 0 ∧A Var 1))
-- C-c C-n test-nnf  →  lit (Neg 0) ∨An lit (Neg 1)


cnf-contra = (Pos 0 ∷ []) ∷ (Neg 0 ∷ []) ∷ []
cnf-unit = (Pos 0 ∷ []) ∷ []
cnf-or = (Pos 0 ∷ Pos 1 ∷ []) ∷ []
cnf-chain = (Pos 0 ∷ Pos 1 ∷ [])
          ∷ (Neg 0 ∷ [])
          ∷ (Neg 1 ∷ Pos 2 ∷ [])
          ∷ []
cnf-unsat2 = (Pos 0 ∷ Pos 1 ∷ [])
           ∷ (Pos 0 ∷ Neg 1 ∷ [])
           ∷ (Neg 0 ∷ Pos 1 ∷ [])
           ∷ (Neg 0 ∷ Neg 1 ∷ [])
           ∷ []

sat-eval-check : Maybe Bool
sat-eval-check with sat test-formula
... | just asg = eval asg test-formula
... | nothing  = nothing
