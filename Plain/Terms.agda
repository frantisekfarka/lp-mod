module Terms where

open import Data.Nat
open import Data.Fin

record Signature (n : ℕ) : Set where
  field
    -- symbols are encoded as numbers in Fin n
    -- arity
    ar : Fin n → ℕ

open Signature public

-- | Countable set of Variables
Var : Set
Var = ℕ

open import Data.Vec as V
open import Size
-- | Term in with a signature Σ with variables var
data Term {i : Size} {j : Size< i} {n : ℕ}
  (Σ : Signature n) (var : Set) : Set where
   FNode : {k : Size< j}
     → (f : Fin n) → Vec (Term {j} {k} {n} Σ var) (ar Σ f)
     → Term {i} {j} {n} Σ var
   VNode :  (v : var) → Term {i} {j} {n} Σ var

open import Data.Empty

-- | Ground Terms
GTerm : {n : ℕ} → (Σ : Signature n) → Set
GTerm Σ =  Term Σ ⊥

open import Data.List as L

-- | Horn clause
--
data Clause {n : ℕ} (Σ : Signature n) : Set where
  _:-_ : (Term Σ Var) → List (Term Σ Var)  → Clause Σ

cHead : {n : ℕ} → {Σ : Signature n} → Clause Σ → Term Σ Var
cHead (a :- _) = a

cBody : {n : ℕ} → {Σ : Signature n} → Clause Σ → List (Term Σ Var)
cBody (_ :- bs) = bs

record Program {n : ℕ} (Σ : Signature n) : Set where
  field
    prg : List (Clause Σ) -- → Program Σ

--unPrg : {n : ℕ} → {Σ : Signature n} → Program Σ → List (Clause Σ)
--unPrg (prg cls) = cls


record GSubst {n : ℕ} (Σ : Signature n) : Set₁ where
  field
    subst : (Var → GTerm Σ)

open GSubst

-- | substitution application
app : {i : Size} → {j : Size< i} →
  {n : ℕ} → {Σ : Signature n}
  → GSubst Σ → Term {i} {j} Σ Var → GTerm Σ
app σ (FNode f fs) = FNode f (V.map (app σ) fs)
app σ (VNode v) = subst σ v


