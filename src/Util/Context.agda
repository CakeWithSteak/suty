open import Relation.Binary.Definitions
open import Level

module Util.Context {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (⌊_⌋; _×-dec_; yes; no; does; _because_; of; ¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL; IsDecEquivalence)
open import Data.Bool using (true; false; if_then_else_)
open import Function.Base using (case_of_)
open import Data.Product
open import Data.Sum
open import Data.Empty

private
  variable
    V : Set

-- Represents a generic context (scope, typing context, store, etc) indexed by name
data Context (V : Set) : Set where
  ∅ : Context V
  _,_↦_ : Context V → name → V → Context V

infix 4  _,_↦_
infixl 4 _⸴_
infix 4 _↦_∈_

-- NB this is a raised comma (\, number 4) so as not to conflict with pairs
pattern _⸴_ Γ x = (Γ , x ↦ _)

data _↦_∈_  (x : name) (v : V) : Context V → Set  where
  here : {Γ : Context V} → x ↦ v ∈ (Γ , x ↦ v)
  there : ∀ {y w} {Γ : Context V} (_ : x ↦ v ∈ Γ) → x ↦ v ∈ (Γ , y ↦ w)

_∈_ :  name → Context ⊤ → Set
_∈_ x Γ = x ↦ tt ∈ Γ

data All (R : REL name V 0ℓ) : Pred (Context V) 0ℓ where
  ∅ : All R ∅
  _,_ : ∀ {x v Γ} (rest : All R Γ) (this : R x v) → All R (Γ , x ↦ v)

-- Type witnessing a deleteBinding
infix 3  _-_↦_≡_
data _-_↦_≡_  {V : Set} :  Context V → name →  V → Context V → Set where
  deleteHere : (Γ : Context V) (x : name) (v : V)  → ((Γ , x ↦ v) - x ↦ v ≡ Γ)
  deleteThere : ∀ {y u} (Γ : Context V) (x : name) (v : V) (Γ' : Context V) → ¬ (y ≡ x  × v ≡ u) → Γ - x ↦ v ≡ Γ' → (Γ , y ↦ u) - x ↦ v ≡ (Γ' , y ↦ u)

deleteBinding :  {V : Set} {_≟ᵥ_ : DecidableEquality V} (Γ : Context V) (x : name) (v : V) → x ↦ v ∈ Γ → Σ[ Γ' ∈ Context V ] (Γ - x ↦ v ≡ Γ')
deleteBinding {V} {_≟ᵥ_} (Γ , y ↦ u) x v elem with y ≟ₙ x ×-dec u ≟ᵥ v
... | no ¬eq = let (Γ' , d') = deleteBinding {V} {_≟ᵥ_} Γ x v (case elem of λ { here → ⊥-elim (¬eq (refl , refl)) ; (there x) → x}) in (Γ' , y ↦ u) , deleteThere Γ x v Γ' (λ { (refl , refl) → ¬eq (refl , refl)}) d'
... | yes (refl , refl) = Γ , deleteHere Γ y u
  
Scope : Set
Scope = Context ⊤
