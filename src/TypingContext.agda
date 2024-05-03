open import Relation.Binary.Definitions

module TypingContext {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Type
open import Qualifier
open import Util.Context {name} {_≟ₙ_}
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary using (REL)
open import Data.Bool
open import Function.Base using (case_of_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred)
open import Function.Bundles using (_⇔_)
open import Data.Product
open import Level

TypingContext : Set
TypingContext = Context Type

-- Ordered inclusion in the typing context: same as normal inclusion for non-ordered types, but requires that the type be at the head of the context for ordered types
data _↦_∈*_ (x : name) (t : Type) : TypingContext → Set where
  here : {Γ : TypingContext} → x ↦ t ∈* (Γ , x ↦ t)
  thereUnordered : ∀ {y u} {Γ : TypingContext} → False (ordQualified? t) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)
  thereOrdered : ∀ {y u} {Γ : TypingContext} → True (ordQualified? t) → False (ordQualified? u) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)

_↦_∉*_ : name → Type → TypingContext → Set
x ↦ t ∉* Γ  = ¬ ( x ↦ t ∈* Γ )

_↦_∈*?_ : (x : name) (ty : Type) (Γ : TypingContext) → Dec (x ↦ ty ∈* Γ)
x ↦ ty ∈*? ∅ = no (λ ())
x ↦ ty ∈*? (Γ , y ↦ u) with x ≟ₙ y ×-dec ty ≟ₜ u | x ↦ ty ∈*? Γ | ordQualified? ty | ordQualified? u 
... | yes (refl , refl) | _ | _ | _ = yes here
... | no neq | no not-elem | _ | _  = no λ { here → contradiction (refl , refl) neq ; (thereUnordered _ elem) → contradiction elem not-elem; (thereOrdered _ _ elem) → contradiction elem not-elem}
... | no neq | yes elem | no ty-not-ord | _ = yes (thereUnordered (fromWitnessFalse ty-not-ord) elem)
... | no neq | yes elem | yes ty-ord | no u-not-ord = yes (thereOrdered (fromWitness ty-ord) (fromWitnessFalse u-not-ord) elem)
... | no neq | yes elem | yes ty-ord | yes u-ord = no λ { here → contradiction (refl , refl) neq ; (thereUnordered ty-not-ord _) → contradiction ty-ord (toWitnessFalse ty-not-ord) ; (thereOrdered _ u-not-ord _) → contradiction u-ord (toWitnessFalse u-not-ord)}

-- "Weakens" ∈* into ∈
∈*⇒∈ : ∀ {x t Γ} → x ↦ t ∈* Γ → x ↦ t ∈ Γ
∈*⇒∈ here = here
∈*⇒∈ (thereUnordered _ p) = there (∈*⇒∈ p)
∈*⇒∈ (thereOrdered _ _ p) = there (∈*⇒∈ p)

data _÷_≡_ : TypingContext → TypingContext → TypingContext → Set where
  divEmpty : (Γ : TypingContext) → Γ ÷ ∅ ≡ Γ
  
  -- When dividing by an unrestricted var, we assume that the returned context (Γ₁) still contains it (otherwise code removed it in error), but we want to remove it to uphold scoping rules, while also keeping all other bindings intact
  divUn : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄} →                                  Γ₁ ÷ (Γ₂ , x ↦ t)  ≡ Γ₃ → -- Recurse, using Γ₃ as an intermediate value
                                                                           qualifierOf t ≡ un → -- Rule applies only for unrestricted vars
                                                                                      x ↦ t ∈* Γ₃ → -- Binding should not have disappeared
                                                                             Γ₃ - x ↦ t ≡ Γ₄  → -- Result context Γ₄ must be Γ₃ but with the x ↦ t binding deleted
                                                                             Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  -- For lin/ord qualified types, we enforce usage by requiring that the returned context does not contain them
  divMustuse : ∀ {x t Γ₁ Γ₂ Γ₃} → Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₃ → qualifierOf t ≢ un →  x ↦ t ∉* Γ₃ → Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₃

÷-unique : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → Γ₁ ÷ Γ₂ ≡ Γ₃ → Γ₁ ÷ Γ₂ ≡ Γ₄ → Γ₃ ≡ Γ₄
÷-unique (divEmpty _) (divEmpty _) = refl
÷-unique (divUn {x} {t} {Γ₃ = Γ-sub₁} sub₁ t-un₁ x-in-sub₁ sub-gives-res₁) (divUn {x} {t} {Γ₃ = Γ-sub₂} sub₂ t-un₂ x-in-sub₂ sub-gives-res₂) = case ÷-unique sub₁ sub₂ of λ { refl → deleteBinding-unique sub-gives-res₁ sub-gives-res₂ }
÷-unique (divUn _ t-un _ _) (divMustuse _ t-not-un _) = contradiction t-un t-not-un
÷-unique (divMustuse _ t-not-un _) (divUn _ t-un _ _) = contradiction t-un t-not-un
÷-unique (divMustuse sub₁ _ _) (divMustuse sub₂ _ _) = ÷-unique sub₁ sub₂

--divideContext : (Γ₁ : TypingContext) (Γ₂ : TypingContext) → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ÷ Γ₂ ≡ Γ₃)
--divideContext Γ₁ ∅ = yes (Γ₁ , divEmpty Γ₁)
--divideContext Γ₁ (Γ₂ , x ↦ T) with divideContext Γ₁ Γ₂ | qualifierOf T ≟q un
--... | no nosub | _ = no λ { (Γ₄ , divUn {Γ₃ = Γ₃} sub _ _ _) → nosub (Γ₃ , sub) ; (Γ₃ , divMustuse sub _ _) → nosub (Γ₃ , sub)}
--... | yes (Γ₃ , sub) | yes T-is-un  = case x ↦ T ∈*? Γ₃ of λ {
 -- (no not-elem) → no λ { (Γ₄ , divUn  sub _ elem _) → {!!} ; (Γ₄ , divMustuse snd x x₁) → {!!}} ;
  --(yes a) → {!!}
 -- }
--... | yes sub | no T-is-not-un = {!!}

_⟨⟨_⟩⟩ : REL Qualifier TypingContext 0ℓ
q ⟨⟨ Γ ⟩⟩ = All (λ _ ty → q ⟨ ty ⟩) Γ

canContainCtx? : Decidable _⟨⟨_⟩⟩
canContainCtx? q Γ = all? (λ _ ty → canContain? q ty) Γ
