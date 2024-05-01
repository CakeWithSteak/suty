open import Relation.Binary.Bundles
open import Level

module TypingContext {Key : DecSetoid 0ℓ 0ℓ} where

open import Type
open import Qualifier
open import Util.Context {Key = Key}
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Binary using (REL)
open import Data.Bool
open import Function.Base using (case_of_)

TypingContext : Set
TypingContext = Context Type

-- Ordered inclusion in the typing context: same as normal inclusion for non-ordered types, but requires that the type be at the head of the context for ordered types
data _↦_∈*_ (x : name) (t : Type) : TypingContext → Set where
  here : {Γ : TypingContext} → x ↦ t ∈* (Γ , x ↦ t)
  thereUnordered : ∀ {y u} {Γ : TypingContext} {_ : False (ordQualified? t)} → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)
  thereOrdered : ∀ {y u} {Γ : TypingContext} {_ : True (ordQualified? t)} → False (ordQualified? u) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)

data _÷_≡_ : TypingContext → TypingContext → TypingContext → Set where
  divEmpty : (Γ : TypingContext) → Γ ÷ ∅ ≡ Γ
 -- divUn : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ÷ Γ₂ ≡ Γ₃ → 
