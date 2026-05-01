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

data Literal : Set where
  Pos : ℕ → Literal
  Neg : ℕ → Literal

infixr 6 _∧n_
infixr 5 _∨n_

data NNF : Set where
  lit  : Literal → NNF
  _∧n_ : NNF → NNF → NNF
  _∨n_ : NNF → NNF → NNF


---------------
-- Problem 3 --
---------------

to-nnf : Formula → NNF
to-nnf (Var x) = lit ( Pos x )
to-nnf (¬ Var x) = lit ( Neg x)
to-nnf (¬ (¬ f)) = to-nnf f
to-nnf (¬ (f ∧ g)) = to-nnf (¬ f) ∨n to-nnf ( ¬ g)
to-nnf (¬ (f ∨ g)) = to-nnf (¬ f) ∧n to-nnf ( ¬ g)
to-nnf (f ∧ g) = to-nnf f ∧n to-nnf g
to-nnf (f ∨ g) = to-nnf f ∨n to-nnf g


---------------
-- Problem 4 --
---------------

