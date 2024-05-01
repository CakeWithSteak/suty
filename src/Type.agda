module Type where

open import Qualifier
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- Qualifier is folded into Type because having ord functions is forbidden. If that can be relaxed, this definition can be made more elegant
data Type : Set where
  `_`Bool : Qualifier → Type
  `_`Unit : Qualifier → Type
  `_`_`×_ : Qualifier → Type → Type → Type
  `_`_⇒_ : (q : Qualifier) → {q ≢ ord} → Type → Type → Type

qualifierOf : Type → Qualifier
qualifierOf ` q `Bool = q
qualifierOf ` q `Unit = q
qualifierOf (` q ` _ `× _) = q
qualifierOf (` q ` _ ⇒ _) = q
