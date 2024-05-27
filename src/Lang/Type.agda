module Lang.Type where

open import Lang.Qualifier
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

arrow? : (ty : Type) → (Σ Qualifier λ q → Σ (q ≢ ord × Type × Type) (λ { (q≢ord , T , U) → (` q ` T ⇒ U) {q≢ord} ≡ ty}))  ⊎ (∀ {q T U q≢ord} → ty ≢ (` q ` T ⇒ U) {q≢ord})
arrow? ` x `Bool = no' (λ ())
arrow? ` x `Unit = no' (λ ())
arrow? (` x ` x₁ `× x₂) = no' (λ ())
arrow? ((` q ` T₁ ⇒ T₂) {q≢ord}) = yes' (q , ((q≢ord , T₁ , T₂) , refl))

qualifierOf : Type → Qualifier
qualifierOf ` q `Bool = q
qualifierOf ` q `Unit = q
qualifierOf (` q ` _ `× _) = q
qualifierOf (` q ` _ ⇒ _) = q

ordQualified? : (t : Type) → Dec (qualifierOf t ≡ ord)
ordQualified? t = qualifierOf t ≟q ord

--  somewhat hacky to avoid "I'm not sure" compiler errors
qualifierCases : {A : Set} (ty : Type) → (qualifierOf ty ≡ un → A) → (qualifierOf ty ≡ lin → A) → (qualifierOf ty ≡ ord → A) → (qualifierOf ty ≡ aff → A) → (qualifierOf ty ≡ rel → A) → A
qualifierCases ` un `Bool u l o a r = u refl
qualifierCases ` aff `Bool u l o a r = a refl
qualifierCases ` lin `Bool u l o a r = l refl
qualifierCases ` ord `Bool u l o a r = o refl
qualifierCases ` rel `Bool u l o a r = r refl
qualifierCases ` un `Unit u l o a r = u refl
qualifierCases ` aff `Unit u l o a r = a refl
qualifierCases ` lin `Unit u l o a r = l refl
qualifierCases ` ord `Unit u l o a r = o refl
qualifierCases ` rel `Unit u l o a r = r refl
qualifierCases (` un ` _ `× _) u l o a r = u refl
qualifierCases (` aff ` _ `× _) u l o a r = a refl
qualifierCases (` lin ` _ `× _) u l o a r = l refl
qualifierCases (` ord ` _ `× _) u l o a r = o refl
qualifierCases (` rel ` _ `× _) u l o a r = r refl
qualifierCases (` un ` _ ⇒ _) u l o a r = u refl
qualifierCases (` aff ` _ ⇒ _) u l o a r = a refl
qualifierCases (` lin ` _ ⇒ _) u l o a r = l refl
qualifierCases (` ord ` _ ⇒ _) u l o a r = o refl
qualifierCases (` rel ` _ ⇒ _) u l o a r = r refl

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
