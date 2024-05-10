open import Relation.Binary.Definitions using (DecidableEquality)
open import Level

module Scoping.Context {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (⌊_⌋; _×-dec_; yes; no; does; _because_; of; ¬_; Dec; contradiction)
open import Relation.Unary using (Pred) renaming (Decidable to Decidable₁)
open import Relation.Binary using (REL; IsDecEquivalence; _⇒_) renaming (Decidable to Decidable₂)
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

_∉_ : name → Context ⊤ → Set
_∉_ x Γ = ¬ (x ↦ tt ∈ Γ)

_↦_∈?_ : (x : name) (v : V) (Γ : Context V) {_≟ᵥ_ : DecidableEquality V} → Dec (x ↦ v ∈ Γ)
x ↦ v ∈? ∅ = no (λ ())
(x ↦ v ∈? (Γ , y ↦ u)) {_≟ᵥ_} with x ≟ₙ y ×-dec v ≟ᵥ u | (x ↦ v ∈? Γ) {_≟ᵥ_}
... | yes (refl , refl)  | _ = yes here
... | no ¬eq | no ¬elem = no λ { here → ¬eq (refl , refl) ; (there actually-elem) → ¬elem actually-elem}
... | no ¬eq | yes elem  = yes (there elem)

lookup : (Γ : Context V) (x : name) → Dec (Σ[ v ∈ V ] x ↦ v ∈ Γ)
lookup ∅ x = no (λ { ()})
lookup (Γ , y ↦ u) x with x ≟ₙ y
... | yes refl = yes (u , here)
... | no x≢y with lookup Γ x
...   | no nosub = no (λ { (v , here) → contradiction refl x≢y ; (v , there p) → contradiction (v , p) nosub})
... | yes (v , p) = yes (v , (there p))


data All (R : REL name V 0ℓ) : Pred (Context V) 0ℓ where
  ∅ : All R ∅
  _,_ : ∀ {x v Γ} (rest : All R Γ) (this : R x v) → All R (Γ , x ↦ v)

mapAll : {A : REL name V 0ℓ} {B : REL name V 0ℓ} {Γ : Context V} → A ⇒ B → All A Γ → All B Γ
mapAll impl ∅ = ∅
mapAll impl (a , this) = mapAll impl a , impl this

all? : {R : REL name V 0ℓ} → Decidable₂ R  → Decidable₁ (All R)
all? r ∅ = yes ∅
all? r (Γ , x ↦ v) with all? r Γ
... | no ¬a = no λ { (prev , this) → ¬a prev}
... | yes prev = case r x v of λ { (no ¬a) → no (λ {(prev , this) → ¬a this}) ; (yes this) → yes (prev , this)}

¬all⇒∉ : {R : REL name V 0ℓ} {Γ : Context V} {x : name} {v : V} → All R Γ → ¬ R x v → ¬ (x ↦ v ∈ Γ)
¬all⇒∉ (all , this) not-R here = contradiction this not-R
¬all⇒∉ (all , this) not-R (there yes-elem) = ¬all⇒∉ all not-R yes-elem

-- Type witnessing a deleteBinding
infix 3  _-_↦_≡_
data _-_↦_≡_  {V : Set} :  Context V → name →  V → Context V → Set where
  deleteHere : (Γ : Context V) (x : name) (v : V)  → ((Γ , x ↦ v) - x ↦ v ≡ Γ)
  deleteThere : ∀ {y u} (Γ : Context V) (x : name) (v : V) (Γ' : Context V) → ¬ (y ≡ x  × v ≡ u) → Γ - x ↦ v ≡ Γ' → (Γ , y ↦ u) - x ↦ v ≡ (Γ' , y ↦ u)

deleteBinding-unique : ∀ {x V Γ Γ₁ Γ₂} {v : V} → Γ - x ↦ v ≡ Γ₁ → Γ - x ↦ v ≡ Γ₂ → Γ₁ ≡ Γ₂
deleteBinding-unique (deleteHere _ _ _) (deleteHere _ _ _) = refl
deleteBinding-unique (deleteHere _ _ _) (deleteThere _ _ _ _ noteq _) = contradiction (refl , refl) noteq
deleteBinding-unique (deleteThere _ _ _ _ noteq _) (deleteHere _ _ _) = contradiction (refl , refl) noteq
deleteBinding-unique (deleteThere _ _ _ _ _ sub₁) (deleteThere _ _ _ _ _ sub₂) = case deleteBinding-unique sub₁ sub₂ of λ {refl → refl}

deleteBinding :  {V : Set} {_≟ᵥ_ : DecidableEquality V} (Γ : Context V) (x : name) (v : V) → x ↦ v ∈ Γ → Σ[ Γ' ∈ Context V ] (Γ - x ↦ v ≡ Γ')
deleteBinding {V} {_≟ᵥ_} (Γ , y ↦ u) x v elem with y ≟ₙ x ×-dec u ≟ᵥ v
... | no ¬eq = let (Γ' , d') = deleteBinding {V} {_≟ᵥ_} Γ x v (case elem of λ { here → ⊥-elim (¬eq (refl , refl)) ; (there x) → x}) in (Γ' , y ↦ u) , deleteThere Γ x v Γ' (λ { (refl , refl) → ¬eq (refl , refl)}) d'
... | yes (refl , refl) = Γ , deleteHere Γ y u

_≟Γ_ : {V : Set} {_≟ᵥ_ : DecidableEquality V} → DecidableEquality (Context V)
∅  ≟Γ ∅ = yes refl
∅ ≟Γ (Ω , x ↦ x₁) = no (λ ())
(Γ , x ↦ x₁) ≟Γ ∅ = no (λ ())
_≟Γ_ {V} {_≟ᵥ_} (Γ , x ↦ v) (Ω , y ↦ u) with x ≟ₙ y ×-dec v ≟ᵥ u ×-dec _≟Γ_ {_≟ᵥ_ = _≟ᵥ_} Γ Ω
... | no neq = no (λ {refl → neq (refl , (refl , refl))})
... | yes (refl , (refl , refl)) = yes refl

Scope : Set
Scope = Context ⊤

