module Models where

open import Data.Nat
open import Terms

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

-- | Inductive model
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
open import Data.Product
open import Data.List.All.Properties -- using (All-map)

-- | model intersection property for a pair of models
prop_model_intersection_pair : {n : ℕ} → {Σ : Signature n} →
  (P : Program Σ)
  → (m₁ : Interp Σ)
  → (m₂ : Interp Σ)
  → (mp₁ : IsIndModel m₁ P)
  → (mp₂ : IsIndModel m₂ P)
  → IsIndModel (m₁ ∩ᵢ m₂) P
prop_model_intersection_pair P m₁ m₂ mp₁ mp₂ =
--  record { forwClosed = λ bs' x σ a₁ bs pcls pbody
--    → ( forwClosed mp₁ bs' (lemACar₁ x) σ a₁ bs pcls pbody
--      , forwClosed mp₂ bs' (lemACar₂ x) σ a₁ bs pcls pbody ) }
    record { forwClosed = λ bs' x σ a₁ bs pcls pbody →
         ( forwClosed mp₁ bs' (LAl.map proj₁ x) σ a₁ bs pcls pbody
         , forwClosed mp₂ bs' (LAl.map proj₂ x) σ a₁ bs pcls pbody
         )
      
    }