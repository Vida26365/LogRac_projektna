module projekt where

open import Data.Nat using (ℕ)

---------------
-- Problem 1 --
---------------

data Formula : Set where
  Var : ℕ → Formula
  ¬_  : Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula


---------------
-- Problem 2 --
---------------
