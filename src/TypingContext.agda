open import Relation.Binary.Definitions

module TypingContext {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Type
open import Qualifier
open import Util.Context {name} {_≟ₙ_}
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Binary using (REL)
open import Data.Bool
open import Function.Base using (case_of_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Pred)
open import Function.Bundles using (_⇔_)
open import Data.Product
open import Level

TypingContext : Set
TypingContext = Context Type

-- Ordered inclusion in the typing context: same as normal inclusion for non-ordered types, but requires that the type be at the head of the context for ordered types
data _↦_∈*_ (x : name) (t : Type) : TypingContext → Set where
  here : {Γ : TypingContext} → x ↦ t ∈* (Γ , x ↦ t)
  thereUnordered : ∀ {y u} {Γ : TypingContext} {_ : False (ordQualified? t)} → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)
  thereOrdered : ∀ {y u} {Γ : TypingContext} {_ : True (ordQualified? t)} → False (ordQualified? u) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)

_↦_∉*_ : name → Type → TypingContext → Set
x ↦ t ∉* Γ  = ¬ ( x ↦ t ∈* Γ )

-- "Weakens" ∈* into ∈
∈*⇒∈ : ∀ {x t Γ} → x ↦ t ∈* Γ → x ↦ t ∈ Γ
∈*⇒∈ here = here
∈*⇒∈ (thereUnordered p) = there (∈*⇒∈ p)
∈*⇒∈ (thereOrdered _ p) = there (∈*⇒∈ p)

data _÷_≡_ : TypingContext → TypingContext → TypingContext → Set where
  divEmpty : (Γ : TypingContext) → Γ ÷ ∅ ≡ Γ
  
  -- When dividing by an unrestricted var, we assume that the returned context (Γ₁) still contains it (otherwise code removed it in error), but we want to remove it to uphold scoping rules, while also keeping all other bindings intact
  divUn : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄} →                                  Γ₁ ÷ Γ₂ ≡ Γ₃ → -- Recurse, using Γ₃ as an intermediate value
                                                                           qualifierOf t ≡ un → -- Rule applies only for unrestricted vars
                                                                                      x ↦ t ∈* Γ₃ → -- Binding should not have disappeared
                                                                             Γ₃ - x ↦ t ≡ Γ₄  → -- Result context Γ₄ must be Γ₃ but with the x ↦ t binding deleted
                                                                             Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  -- For lin/ord qualified types, we enforce usage by requiring that the returned context does not contain them
  divMustuse : ∀ {x t Γ₁ Γ₂ Γ₃} → Γ₁ ÷ Γ₂ ≡ Γ₃ → qualifierOf t ≢ un →  x ↦ t ∉* Γ₃ → Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₃

_⟨⟨_⟩⟩ : Qualifier → TypingContext → Set
q ⟨⟨ Γ ⟩⟩ = All (λ _ ty → q ⟨ ty ⟩) Γ
