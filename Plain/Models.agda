module Plain.Models where

open import Data.Nat
open import Plain.Terms

-- The (complete) Herbrand universe for Σ
U' : {n : ℕ} → (Signature n) → Set
U' Σ = GTerm Σ

open import Relation.Unary as U
open import Level

-- a (complete) Herbrand interpretation
record Interp {n : ℕ} (Σ : Signature n) : Set₁ where
  field
    Carrier : Pred (U' Σ) Level.zero
open Interp

_∩ᵢ_ : {n : ℕ} → {Σ : Signature n} → Interp Σ → Interp Σ
  → Interp Σ
i₁ ∩ᵢ i₂ = record { Carrier = (Carrier i₁) U.∩ Carrier i₂ }

_∪ᵢ_ : {n : ℕ} → {Σ : Signature n} → Interp Σ → Interp Σ
  → Interp Σ
i₁ ∪ᵢ i₂ = record { Carrier = (Carrier i₁) U.∪ Carrier i₂ }

open import Data.List as L
open import Data.List.All as LAl
open import Data.List.Any as LAn
open import Relation.Binary.Core

open Program

-- | Inductive model property
record IsIndModel {n : ℕ}
  {Σ : Signature n} (i : Interp Σ) (P : Program Σ) : Set₂ where
  field
    forwClosed :
      (bs' : List (GTerm Σ))
      → All (λ b → b ∈ Carrier i) bs'
      → (σ : GSubst Σ)
      → (a : Term Σ Var)
      → (bs : List (Term Σ Var))
      → Any (λ cl → cl ≡ (a :- bs)) (prg P)
      → (L.map (app σ) bs) ≡ bs'
      → (app σ a ∈ Carrier i)
open IsIndModel

-- | Ind Model
record IndModel {n : ℕ}
  {Σ : Signature n} (P : Program Σ) : Set₂ where
  field
    iInterp : Interp Σ
    isIndModel : IsIndModel iInterp P

open IndModel

open import Data.Product
open import Data.List.All.Properties -- using (All-map)


{-
-- | Model intersection
_∩m_ : {n : ℕ} → {Σ : Signature n} → {P : Program Σ}
  → (m₁ : IndModel P) → (m₂ : IndModel P)
  → IndModel P
_∩m_ {n} {Σ} {P} m₁ m₂ = record
  { interp = interp m₁ ∩ᵢ interp m₂
  ; isIndModel = prop-model-intersection-pair P m₁ m₂ }
-}

⋂ᵢ : {n : ℕ} → {Σ : Signature n} →
  (I : Set) → (I → Interp Σ)
  → Interp Σ
⋂ᵢ I f = record { Carrier = ⋂ I (λ i t → t ∈ Carrier (f i)) }

open import Function

prop-model-intersection : {n : ℕ} → {Σ : Signature n} →
  (P : Program Σ)
  → (I : Set) -- ^ is non-empty by what argument?
  → (mps : I → IndModel P)
  → IsIndModel ( ⋂ᵢ I (iInterp ∘ mps)) P
prop-model-intersection P I mps =
  record { forwClosed = λ bs' pbs' σ a bs pcl pbs i →
    forwClosed (isIndModel (mps i)) bs'
      (LAl.map (λ k → k i) pbs')
      σ a bs pcl pbs
    }

-- | Coinductive model
record IsCoiModel {n : ℕ}
  {Σ : Signature n} (i : Interp Σ) (P : Program Σ) : Set₂ where
  field
    backClosed :
      {a : Term Σ Var} → {bs : List (Term Σ Var)}
      → (a' : GTerm Σ)
      → a' ∈ Carrier i
      → ∃ (λ (σclsp : GSubst Σ ×
        Any (λ c → a :- bs ≡ c) (prg P))
      → app (proj₁ σclsp) a ≡ a'
      → All (λ c → c ∈ Carrier i) (L.map (app (proj₁ σclsp)) bs))
open IsCoiModel

-- | Coi Model
record CoiModel {n : ℕ}
  {Σ : Signature n} (P : Program Σ) : Set₂ where
  field
    cInterp : Interp Σ
    isCoiModel : IsCoiModel cInterp P

open CoiModel


⋃ᵢ : {n : ℕ} → {Σ : Signature n} →
  (I : Set) → (I → Interp Σ)
  → Interp Σ
⋃ᵢ I f = record { Carrier = λ x → ⋃ I (λ i t → t ∈ Carrier (f i)) x }

open import Data.Product as DP

-- | model union property 
prop-model-union : {n : ℕ} → {Σ : Signature n} →
  (P : Program Σ)
  → (I : Set) -- ^ is non-empty by what argument?
  → (mps : I → CoiModel P)
  → IsCoiModel ( ⋃ᵢ I (cInterp ∘ mps)) P
prop-model-union P I mps =
  record { backClosed = λ a' x →
    DP.map (λ id → id)
           (λ x₂ x₃ → LAl.map (λ x₄ → proj₁ x , x₄) (x₂ x₃))
           (backClosed (isCoiModel (mps (proj₁ x))) a' (proj₂ x)) }


