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

ValidInUnorderedContext : REL name Type 0ℓ
ValidInUnorderedContext = λ _ t → False (ordQualified? t)

ValidInOrderedContext : REL name Type 0ℓ
ValidInOrderedContext = λ _ t → True (ordQualified? t)

data TypingContext : Set where
  ⟨_,_⟩ : (Γ Ω : Context Type) → {All ValidInUnorderedContext Γ} → {All ValidInOrderedContext Ω} → TypingContext

-- Adds a normal context of types to the merged typing context
_++_ : TypingContext → Context Type → TypingContext
⟨ Γ , Ω ⟩ {p₁} {p₂} ++ ∅ = ⟨ Γ , Ω ⟩ {p₁} {p₂}
⟨ Γ , Ω ⟩ {p₁} {p₂} ++ (Φ , x ↦ t) with ordQualified? t
... | no isnotord = ⟨ Γ , x ↦ t , Ω ⟩ {p₁ , fromWitnessFalse isnotord} {p₂}
... | yes isord = ⟨ Γ , Ω , x ↦ t ⟩ {p₁} {p₂ , fromWitness isord}

-- Ordered inclusion in the typing context: same as normal inclusion for non-ordered types, but requires that the type be at the head of the ordered context for ordered types
data _↦_∈*_ (x : name) (t : Type) : TypingContext → Set where
  here :  {Γ Ω : Context Type} {p₁ : All ValidInUnorderedContext Γ} {p₂ : All ValidInOrderedContext Ω} {p' : False (ordQualified? t)} → x ↦ t ∈* ⟨ Γ , x ↦ t , Ω ⟩ {p₁ , p'} {p₂}
  hereOrdered :  {Γ Ω : Context Type} {p₁ : All ValidInUnorderedContext Γ} {p₂ : All ValidInOrderedContext Ω} {p' : True (ordQualified? t)} → x ↦ t ∈* ⟨ Γ , Ω , x ↦ t ⟩ {p₁} {p₂ , p'}
  there : ∀ {y u} {Γ Ω : Context Type} {p₁ : All ValidInUnorderedContext Γ} {p₂ : All ValidInOrderedContext Ω}  {_ : False (ordQualified? t)}  {p' : True (ordQualified?)} →  x ↦ t ∈* ⟨ Γ , Ω ⟩ {p₁} {p₂} → x ↦ t ∈* ⟨ Γ , Ω , y ↦ u ⟩ {p₁} {p₂ , 

ord-binding-implies-nonempty-context : ∀ {x t} {Γ Ω : Context Type}  {p₁ : All ValidInUnorderedContext Γ} {p₂ : All ValidInOrderedContext Ω}  {_ : True (ordQualified? t)} → x ↦ t ∈* ⟨ Γ , Ω ⟩ {p₁} {p₂} → Ω ≢ ∅
ord-binding-implies-nonempty-context {x} {t} {Γ} {Ω} {p₁} {p₂} {t-ord} hereOrdered = {!!}
ord-binding-implies-nonempty-context {x} {t} {Γ} {Ω} {p₁} {p₂} {t-ord} there = {!!}

-- Deletes the last matching binding from the appropriate subcontext
_-_↦_ : (Δ : TypingContext) → (x : name) → (t : Type) → {elem : x ↦ t ∈* Δ}  → TypingContext
(⟨ Γ , Ω ⟩ {p₁} {p₂} - x ↦ t) {elem} with ordQualified? t
...  | no isnotord = ⟨ deleteBinding Γ x , Ω ⟩ {deleteBinding-preserves-all p₁} {p₂}
...  | yes isord = ⟨ Γ , case Ω of (λ { ∅ → {!!} ; (Ω' , x ↦ t) → Ω' }) ⟩ {{!!}} {{!!}}
