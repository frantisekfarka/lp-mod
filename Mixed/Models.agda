module Models where

open import Data.Nat
open import Terms


-- The (complete) Herbrand universe for Σ
U' : {n m : ℕ} → (Signature n m) → Set
U' Σ = GTerm Σ

-- The (complete) μ-Herbrand base for Σ

B'μ : {n m : ℕ} → (Signature n m) → Set
B'μ Σ = GAtom Σ μ

B'ν : {n m : ℕ} → (Signature n m) → Set
B'ν Σ = GAtom Σ ν


open import Relation.Unary as U
open import Level

-- a (complete) Herbrand interpretation
record Interp {n m : ℕ} (Σ : Signature n m) : Set₁ where
  field
    Carrier-μ : Pred (B'μ Σ) Level.zero
    Carrier-ν : Pred (B'ν Σ) Level.zero
open Interp


_∩ᵢ_ : {n m : ℕ} → {Σ : Signature n m} → Interp Σ → Interp Σ
  → Interp Σ
i₁ ∩ᵢ i₂ = record
  { Carrier-μ = Carrier-μ i₁ ∩ Carrier-μ i₂
  ; Carrier-ν = Carrier-ν i₁ ∩ Carrier-ν i₂
  }

_∪ᵢ_ : {n m : ℕ} → {Σ : Signature n m} → Interp Σ → Interp Σ
  → Interp Σ
i₁ ∪ᵢ i₂ = record
  { Carrier-μ = Carrier-μ i₁ ∪ Carrier-μ i₂
  ; Carrier-ν = Carrier-ν i₁ ∪ Carrier-ν i₂
  }

open import Data.List as L
open import Data.List.All as LAl
open import Data.List.Any as LAn
open import Relation.Binary.Core

open Program

-- | Inductive model
record IsIModel {n m : ℕ} {Σ : Signature n m} {var : Set}
       (i : Interp Σ) (P : Program Σ var) : Set₂ where
  field
    forwClosed :
      (bs'μ : List (GAtom Σ μ))
      → All (λ b → b ∈ Carrier-μ i) bs'μ
      → (bs'ν : List (GAtom Σ ν))
      → All (λ b → b ∈ Carrier-ν i) bs'ν
      → (σ : GSubst Σ var)
      → (a : Atom Σ var μ)
      → (bsμ : List (Atom Σ var μ))
      → (bsν : List (Atom Σ var ν))
      → Any (λ cl → cl ≡ (a :- bsμ , bsν)) (prg-μ P)
      → (L.map (appA σ) bsμ) ≡ bs'μ
      → (L.map (appA σ) bsν) ≡ bs'ν
      → (appA σ a ∈ Carrier-μ i)
open IsIModel
open import Data.Product

hA : {A : Set} {B : Set₁}  → A × B → A
hA = proj₁

hBsμ : {A B : Set} {C : Set₁} → A × B × C → B
hBsμ (_ , a , _) = a

hBsν : {A B C : Set} {D : Set₁} → A × B × C × D → C
hBsν (_ , _ , a , _) = a

hσ : {A B C : Set} {D : Set₁} → A × B × C × D → D
hσ (_ , _ , _ , a) = a
open import Data.List.All.Properties -- using (All-map)

-- | model intersection property for a pair of models
prop_model_intersection_pair : {n m : ℕ} → {Σ : Signature n m} {var : Set} →
  (P : Program Σ var)
  → (m₁ : Interp Σ)
  → (m₂ : Interp Σ)
  → Carrier-ν m₁ ≡ Carrier-ν m₂
  → (mp₁ : IsIModel m₁ P)
  → (mp₂ : IsIModel m₂ P)
  → IsIModel (m₁ ∩ᵢ m₂) P
prop_model_intersection_pair P m₁ m₂ eq mp₁ mp₂ =
  record { forwClosed = λ bs'μ x bs'ν y σ a bsμ bsν pcls pμ pν →
    ( forwClosed mp₁ bs'μ (LAl.map proj₁ x) bs'ν
                 (LAl.map proj₁ y) σ a bsμ bsν pcls pμ pν
    , forwClosed mp₂ bs'μ (LAl.map proj₂ x) bs'ν
                 (LAl.map proj₂ y) σ a bsμ bsν pcls pμ pν
    )}


-- | Coinductive model
record IsCModel {n m : ℕ} {Σ : Signature n m} {var : Set}
       (i : Interp Σ) (P : Program Σ var) : Set₁ where
  field
    backClosed :
      --→
      (a' : GAtom Σ ν)
      → a' ∈ Carrier-ν i
      → ∃ (λ ( w : (Atom Σ var ν) -- a
          × (List (Atom Σ var μ)) -- bs-μ
          × (List (Atom Σ var ν)) -- bs-ν
          × GSubst Σ var) →            -- σ

          (Any (λ c → (hA w) :- (hBsμ w) , (hBsν w) ≡ c) (prg-ν P))
          × appA (hσ w) (hA w) ≡ a'
          × All (λ c → c ∈ Carrier-μ i) (L.map (appA (hσ w)) (hBsμ w))
          × All (λ c → c ∈ Carrier-ν i) (L.map (appA (hσ w)) (hBsν w))
     )
open IsCModel


open import Data.Sum
open import Data.Product as DP
open Interp

open import Relation.Binary.PropositionalEquality

-- | model union property for a pair of models
prop_model_union_pair : {n m : ℕ} → {Σ : Signature n m} → {var : Set}
  (P : Program Σ var)
  → (m₁ : Interp Σ)
  → (m₂ : Interp Σ)
  → Carrier-μ m₁ ≡ Carrier-μ m₂
  → (mp₁ : IsCModel m₁ P)
  → (mp₂ : IsCModel m₂ P)
  → IsCModel (m₁ ∪ᵢ m₂) P
prop_model_union_pair P m₁ m₂ eq mp₁ mp₂ {-with (sym eq) -- | (Carrier-μ m₁)
... | eq' {-| dm₁-}-} = record { backClosed = λ
  { a' (inj₁ x) → DP.map
       (λ atm → atm)
       (DP.map
         (λ any → any)
         (λ w → DP.map (λ eq₁ → eq₁) (λ x₃
           → LAl.map inj₁ (proj₁ (proj₂ w))
           , LAl.map inj₁ (proj₂ (proj₂ w))) w))
       (backClosed mp₁ a' x)
  ; a' (inj₂ y) → DP.map
       (λ atm → atm)
       (DP.map
         (λ any → any)
         (λ w → DP.map (λ eq → eq) (λ x₁
           → LAl.map inj₂ (proj₁ (proj₂ w))
           , LAl.map inj₂ (proj₂ (proj₂ w))) w))
       (backClosed mp₂ a' y)
  } }

