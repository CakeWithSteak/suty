open import Relation.Binary.Definitions

module Lang.TypingContext {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Lang.Type
open import Lang.Qualifier
open import Scoping.Context {name} {_≟ₙ_}
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
  thereUnordered : ∀ {y u} {Γ : TypingContext} → x ≢ y → False (ordQualified? t) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)
  thereOrdered : ∀ {y u} {Γ : TypingContext} → x ≢ y → True (ordQualified? t) → False (ordQualified? u) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)

_↦_∉*_ : name → Type → TypingContext → Set
x ↦ t ∉* Γ  = ¬ ( x ↦ t ∈* Γ )

_↦_∈*?_ : (x : name) (ty : Type) (Γ : TypingContext) → Dec (x ↦ ty ∈* Γ)
x ↦ ty ∈*? ∅ = no (λ ())
x ↦ ty ∈*? (Γ , y ↦ u) with x ≟ₙ y | ty ≟ₜ u | x ↦ ty ∈*? Γ | ordQualified? ty | ordQualified? u 
... | yes refl | yes refl | _ | _ | _ = yes here
... | yes refl | no ty≢u | _ | _ | _ = no λ { here → contradiction refl ty≢u ; (thereUnordered x≢y _ _) → contradiction refl x≢y ; (thereOrdered x≢y _ _ _) → contradiction refl x≢y}
... | no x≢y  | _ | no not-elem | _ | _  = no λ { here → contradiction refl x≢y ; (thereUnordered _ _ elem) → contradiction elem not-elem; (thereOrdered _ _ _ elem) → contradiction elem not-elem}
... | no x≢y | _  | yes elem | no ty-not-ord | _ = yes (thereUnordered x≢y (fromWitnessFalse ty-not-ord) elem)
... | no x≢y | _  | yes elem | yes ty-ord | no u-not-ord = yes (thereOrdered x≢y (fromWitness ty-ord) (fromWitnessFalse u-not-ord) elem)
... | no x≢y | _  | yes elem | yes ty-ord | yes u-ord = no λ { here → contradiction refl x≢y ; (thereUnordered _ ty-not-ord _) → contradiction ty-ord (toWitnessFalse ty-not-ord) ; (thereOrdered _ _ u-not-ord _) → contradiction u-ord (toWitnessFalse u-not-ord)}

∈*-unique : ∀ {x Γ T U} → x ↦ T ∈* Γ → x ↦ U ∈* Γ → T ≡ U
∈*-unique here here = refl
∈*-unique here (thereUnordered x≢x _ _) = contradiction refl x≢x
∈*-unique here (thereOrdered x≢x _ _ _) = contradiction refl x≢x
∈*-unique (thereUnordered x≢x _ _) here = contradiction refl x≢x
∈*-unique (thereUnordered x x₁ a) (thereUnordered x₂ x₃ b) = ∈*-unique a b
∈*-unique (thereUnordered x x₁ a) (thereOrdered x₂ x₃ x₄ b) = ∈*-unique a b
∈*-unique (thereOrdered x≢x _ _ _) here = contradiction refl x≢x
∈*-unique (thereOrdered x x₁ x₂ a) (thereUnordered x₃ x₄ b) = ∈*-unique a b
∈*-unique (thereOrdered x x₁ x₂ a) (thereOrdered x₃ x₄ x₅ b) = ∈*-unique a b

typeLookup : (Γ : TypingContext) (x : name) → Dec (Σ[ ty ∈ Type ] x ↦ ty ∈* Γ)
typeLookup ∅ x = no λ { (ty , ())}
typeLookup (Γ , y ↦ u) x with x ≟ₙ y
... | yes refl  = yes (u , here)
... | no x≢y with typeLookup Γ x
...   | no nosub = no (λ { (ty , here) → contradiction refl x≢y ; (ty , thereUnordered _ _ sub) → contradiction (ty , sub) nosub ; (ty , thereOrdered _ _ _ sub) → contradiction (ty , sub) nosub})
...   | yes (ty , sub) with ordQualified? ty | ordQualified? u
...     | yes ty-ord | no u-not-ord = yes (ty , (thereOrdered x≢y (fromWitness ty-ord) (fromWitnessFalse u-not-ord) sub))
...     | yes ty-ord | yes u-ord = no λ {
          (ty' , here) → contradiction refl x≢y ;
          (ty' , thereUnordered _ ty'-not-ord sub') → case ∈*-unique sub sub' of λ {refl → contradiction ty-ord (toWitnessFalse ty'-not-ord)} ;
          (ty' , thereOrdered _ _  u-not-ord _) → contradiction u-ord (toWitnessFalse u-not-ord)}
...    | no ty-not-ord | _ = yes (ty , (thereUnordered x≢y (fromWitnessFalse ty-not-ord) sub))

-- "Weakens" ∈* into ∈
∈*⇒∈ : ∀ {x t Γ} → x ↦ t ∈* Γ → x ↦ t ∈ Γ
∈*⇒∈ here = here
∈*⇒∈ (thereUnordered _ _ p) = there (∈*⇒∈ p)
∈*⇒∈ (thereOrdered _ _ _ p) = there (∈*⇒∈ p)

data _÷_≡_ : TypingContext → TypingContext → TypingContext → Set where
  divEmpty : (Γ : TypingContext) → Γ ÷ ∅ ≡ Γ
  
  -- When dividing by an unrestricted var, we assume that the returned context (Γ₁) still contains it (otherwise code removed it in error), but we want to remove it to uphold scoping rules, while also keeping all other bindings intact
  divUn : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄} →                                  Γ₁ ÷ Γ₂  ≡ Γ₃ → -- Recurse, using Γ₃ as an intermediate value
                                                                           qualifierOf t ≡ un → -- Rule applies only for unrestricted vars
                                                                                      x ↦ t ∈* Γ₃ → -- Binding should not have disappeared
                                                                             Γ₃ - x ↦ t ≡ Γ₄  → -- Result context Γ₄ must be Γ₃ but with the x ↦ t binding deleted
                                                                             Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  -- For lin/ord qualified types, we enforce usage by requiring that the returned context does not contain them
  divMustuse : ∀ {x t Γ₁ Γ₂ Γ₃} → Γ₁ ÷ Γ₂ ≡ Γ₃ → qualifierOf t ≢ un →  x ↦ t ∉* Γ₃ → Γ₁ ÷ (Γ₂ , x ↦ t) ≡ Γ₃

÷-unique : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → Γ₁ ÷ Γ₂ ≡ Γ₃ → Γ₁ ÷ Γ₂ ≡ Γ₄ → Γ₃ ≡ Γ₄
÷-unique (divEmpty _) (divEmpty _) = refl
÷-unique (divUn sub₁ _ _ sub-gives-res₁) (divUn  sub₂ _ _ sub-gives-res₂) = case ÷-unique sub₁ sub₂ of λ { refl → deleteBinding-unique sub-gives-res₁ sub-gives-res₂ }
÷-unique (divUn _ t-un _ _) (divMustuse _ t-not-un _) = contradiction t-un t-not-un
÷-unique (divMustuse _ t-not-un _) (divUn _ t-un _ _) = contradiction t-un t-not-un
÷-unique (divMustuse sub₁ _ _) (divMustuse sub₂ _ _) = ÷-unique sub₁ sub₂

divideContext : (Γ₁ : TypingContext) (Γ₂ : TypingContext) → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ÷ Γ₂ ≡ Γ₃)
divideContext Γ₁ ∅ = yes (Γ₁ , divEmpty Γ₁)
divideContext Γ₁ (Γ₂ , x ↦ T) with divideContext Γ₁ Γ₂ | qualifierOf T ≟q un
... | no nosub | _ = no λ { (Γ₄ , divUn {Γ₃ = Γ₃} sub _ _ _) → nosub (Γ₃ , sub) ; (Γ₃ , divMustuse sub _ _) → nosub (Γ₃ , sub)}
... | yes (Γ₃ , sub) | yes T-is-un  = case x ↦ T ∈*? Γ₃ of λ {
  (no not-elem) → no λ {
    (Γ₄ , divUn  sub' _ elem _) → case ÷-unique sub sub' of λ {refl → contradiction elem not-elem} ;
    (Γ₄ , divMustuse _ T-not-un _) → contradiction T-is-un T-not-un
    } ;
  (yes elem) → case deleteBinding {Type} {_≟ₜ_} Γ₃ x T (∈*⇒∈ elem) of λ { (Γ₄ , pdiff) → yes (Γ₄ , divUn sub T-is-un elem pdiff)}
  }
... | yes (Γ₃ , sub) | no T-not-un = case x ↦ T ∈*? Γ₃  of λ {
  (no not-elem) → yes (Γ₃ , (divMustuse sub T-not-un not-elem));
  (yes elem) → no λ {
    (Γ₄ , divUn _ T-un _ _) → contradiction T-un T-not-un;
    (Γ₄ , divMustuse sub' _ not-elem) → case ÷-unique sub sub' of λ {refl → contradiction elem not-elem}
    }
  }
  
_⟨⟨_⟩⟩ : REL Qualifier TypingContext 0ℓ
q ⟨⟨ Γ ⟩⟩ = All (λ _ ty → q ⟨ ty ⟩) Γ

canContainCtx? : Decidable _⟨⟨_⟩⟩
canContainCtx? q Γ = all? (λ _ ty → canContain? q ty) Γ
