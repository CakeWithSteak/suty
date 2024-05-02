module Type where

open import Qualifier
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable using  (Dec)

-- Qualifier is folded into Type because having ord functions is forbidden. If that can be relaxed, this definition can be made more elegant
data Type : Set where
  `_`Bool : Qualifier → Type
  `_`Unit : Qualifier → Type
  `_`_`×_ : Qualifier → Type → Type → Type
  `_`_⇒_ : (q : Qualifier) → Type → Type → {q ≢ ord}  → Type

qualifierOf : Type → Qualifier
qualifierOf ` q `Bool = q
qualifierOf ` q `Unit = q
qualifierOf (` q ` _ `× _) = q
qualifierOf (` q ` _ ⇒ _) = q

ordQualified? : (t : Type) → Dec (qualifierOf t ≡ ord)
ordQualified? t = qualifierOf t ≟ ord

data _⟨_⟩ (q : Qualifier) (ty : Type) : Set where
  qualifies : q ⊑ qualifierOf ty → q ⟨ ty ⟩ 
