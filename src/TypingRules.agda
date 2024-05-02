open import Relation.Binary.Definitions
module TypingRules {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Util.Context {name} {_≟ₙ_}
open import Type
open import Term {name} {_≟ₙ_}
open import TypingContext {name} {_≟ₙ_}
open import Qualifier
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable

private
  variable
    α : Scope
    x : name

infix 2 _⊢_::_,_
data _⊢_::_,_ (Γᵢ : TypingContext) : (t : Term α) (ty : Type) (Γₒ : TypingContext) → Set where
  TUVar : {ty : Type} → (p : x ∈ α) → (elem : x ↦  ty ∈* Γᵢ) →  (qualifierOf ty ≡ un) → Γᵢ ⊢ (` x # p) :: ty , Γᵢ
  --TLVar
