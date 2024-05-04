module Type where

open import Qualifier hiding (refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using  (Dec; yes; no; False)
open import Relation.Binary using (DecidableEquality; Decidable; REL)
open import Relation.Unary using (Pred) renaming (Decidable to Decidable₁)
open import Level
open import Data.Sum renaming (inj₁ to yes'; inj₂ to no') public
open import Data.Product

-- Qualifier is folded into Type because having ord functions is forbidden. If that can be relaxed, this definition can be made more elegant
data Type : Set where
  `_`Bool : Qualifier → Type
  `_`Unit : Qualifier → Type
  `_`_`×_ : Qualifier → Type → Type → Type
  `_`_⇒_ : (q : Qualifier) → Type → Type → {q ≢ ord}  → Type

data IsBool : Pred Type 0ℓ where
  isBool : {q : Qualifier} → IsBool ` q `Bool

data IsUnit : Pred Type 0ℓ where
  isUnit : {q : Qualifier} → IsUnit ` q `Unit

data IsProduct : Pred Type 0ℓ where
  isProduct : ∀ {q T U} → IsProduct (` q ` T `× U)

data IsArrow : Pred Type 0ℓ where
  isArrow : ∀ {q T U} {p : q ≢ ord} → IsArrow ((` q ` T ⇒ U) {p})

bool? :  (ty : Type) → Σ Qualifier (λ q → ` q `Bool ≡ ty) ⊎ (∀ {q : Qualifier} → ` q `Bool ≢ ty)
bool? ` x `Bool = yes' (x , refl)
bool? ` x `Unit = no' (λ ())
bool? (` x ` x₁ `× x₂) = no' (λ ())
bool? (` q ` x ⇒ x₁) = no' (λ ())

unit? : (ty : Type) → Σ Qualifier (λ q → ` q `Unit ≡ ty) ⊎ (∀ {q : Qualifier} → ty ≢ ` q `Unit)
unit? ` x `Bool = no' (λ ())
unit? ` x `Unit = yes' (x , refl)
unit? (` x ` ty `× ty₁) = no' (λ ())
unit? (` q ` ty ⇒ ty₁) = no' (λ ())

product? :  (ty : Type) → Σ (Qualifier × Type × Type) (λ { (q , T , U) → ` q ` T `× U ≡ ty})  ⊎ (∀ {q T U} → ty ≢ ` q ` T `× U)
product? ` x `Bool = no' (λ ())
product? ` x `Unit = no' (λ ())
product? (` q ` x₁ `× x₂) = yes' ((q , (x₁ , x₂)) , refl)
product? (` q ` x ⇒ x₁) = no' (λ ())

-- arrow? : (ty : Type) → Σ (Qualifier × Type × Type) (λ { (q , T , U) → ` q ` T ⇒ U ≡ ty})  ⊎ (∀ {q T U} → ty ≢ ` q ` T ⇒ U)

qualifierOf : Type → Qualifier
qualifierOf ` q `Bool = q
qualifierOf ` q `Unit = q
qualifierOf (` q ` _ `× _) = q
qualifierOf (` q ` _ ⇒ _) = q

ordQualified? : (t : Type) → Dec (qualifierOf t ≡ ord)
ordQualified? t = qualifierOf t ≟q ord

-- todo somewhat hacky to avoid "I'm not sure" compiler errors
qualifierCases : {A : Set} (ty : Type) → (qualifierOf ty ≡ un → A) → (qualifierOf ty ≡ lin → A) → (qualifierOf ty ≡ ord → A) → A
qualifierCases ty@(` un `Bool) u l o = u refl
qualifierCases ty@(` lin `Bool) u l o = l refl
qualifierCases ty@(` ord `Bool) u l o = o refl
qualifierCases ty@(` un `Unit) u l o = u refl
qualifierCases ty@(` lin `Unit) u l o = l refl
qualifierCases ty@(` ord `Unit) u l o = o refl
qualifierCases ty@(` un ` _ `× _) u l o = u refl
qualifierCases ty@(` lin ` _ `× _) u l o = l refl
qualifierCases ty@(` ord ` _ `× _) u l o = o refl
qualifierCases ty@(` un ` _ ⇒ _) u l o = u refl
qualifierCases ty@(` lin ` _ ⇒ _) u l o = l refl
qualifierCases ty@(` ord ` _ ⇒ _) u l o = o refl

_≟ₜ_ : DecidableEquality Type
` q `Bool ≟ₜ ` w `Bool with q ≟q w
... | no q≢w = no (λ {refl → q≢w refl})
... | yes refl = yes refl

` q `Unit ≟ₜ ` w `Unit with q ≟q w
... | no q≢w = no (λ {refl → q≢w refl})
... | yes refl = yes refl

(` q ` T₁ `× T₂) ≟ₜ (` w ` U₁ `× U₂) with q ≟q w | T₁ ≟ₜ U₁ | T₂ ≟ₜ U₂
... | no q≢w | _ | _ = no (λ {refl → q≢w refl})
... | yes q≡w  | no T₁≢U₁ | _ = no λ {refl → T₁≢U₁ refl }
... | yes q≡w  | yes T₁≡U₁  | no T₂≢U₂ = no λ {refl → T₂≢U₂ refl}
... | yes refl  | yes refl  | yes refl = yes refl

(` q ` T₁ ⇒ T₂) ≟ₜ (` w ` U₁ ⇒ U₂) with q ≟q w | T₁ ≟ₜ U₁ | T₂ ≟ₜ U₂
... | no q≢w | _ | _ = no (λ {refl → q≢w refl})
... | yes q≡w  | no T₁≢U₁ | _ = no λ {refl → T₁≢U₁ refl }
... | yes q≡w  | yes T₁≡U₁  | no T₂≢U₂ = no λ {refl → T₂≢U₂ refl}
... | yes refl  | yes refl  | yes refl = yes refl

` x `Bool ≟ₜ ` x₁ `Unit = no (λ ())
` x `Bool ≟ₜ (` x₁ ` y `× y₁) = no (λ ())
` x `Bool ≟ₜ (` q ` y ⇒ y₁) = no (λ ())
` x `Unit ≟ₜ ` x₁ `Bool = no (λ ())
` x `Unit ≟ₜ (` x₁ ` y `× y₁) = no (λ ())
` x `Unit ≟ₜ (` q ` y ⇒ y₁) = no (λ ())
(` x ` x₁ `× x₂) ≟ₜ ` x₃ `Bool = no (λ ())
(` x ` x₁ `× x₂) ≟ₜ ` x₃ `Unit = no (λ ())
(` x ` x₁ `× x₂) ≟ₜ (` q ` y ⇒ y₁) = no (λ ())
(` q ` x ⇒ x₁) ≟ₜ ` x₂ `Bool = no (λ ())
(` q ` x ⇒ x₁) ≟ₜ ` x₂ `Unit = no (λ ())
(` q ` x ⇒ x₁) ≟ₜ (` x₂ ` y `× y₁) = no (λ ())

_⟨_⟩ : REL Qualifier Type 0ℓ
q ⟨ ty ⟩ = (q ⊑ qualifierOf ty)

canContain? : Decidable _⟨_⟩
canContain? q ty = (q ⊑? qualifierOf ty)

--data _⟨_⟩ (q : Qualifier) (ty : Type) : Set where
--  qualifies : q ⊑ qualifierOf ty → q ⟨ ty ⟩

--canContain? : Decidable _⟨_⟩
--canContain? q ty with q ⊑? qualifierOf ty
--... | no q⋢ = no λ { (qualifies q⊑) → contradiction q⊑ q⋢}
--... | yes p = yes (qualifies p)
