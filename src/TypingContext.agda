open import Relation.Binary.Bundles
open import Level

module TypingContext {Key : DecSetoid 0ℓ 0ℓ} where

open import Type
open import Qualifier
open import Util.Context {Key = Key}
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Bool

data TypingContext : Set where
  ⟨_,_⟩ : (Γ Ω : Context Type) → {All (λ _ t → qualifierOf t ≢ ord) Γ} → {All (λ _ t → qualifierOf t ≡ ord) Ω} → TypingContext

_++_ : TypingContext → Context Type → TypingContext
⟨ Γ , Ω ⟩ {p₁} {p₂} ++ ∅ = ⟨ Γ , Ω ⟩ {p₁} {p₂}
⟨ Γ , Ω ⟩ {p₁} {p₂} ++ (Φ , x ↦ t) with qualifierOf t Qualifier.≟ ord
... | no isnotord = ⟨ Γ , x ↦ t , Ω ⟩ {p₁ , isnotord} {p₂}
... | yes isord = ⟨ Γ , Ω , x ↦ t ⟩ {p₁} {p₂ , isord}
