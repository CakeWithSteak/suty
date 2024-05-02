open import Relation.Binary.Definitions
module TypingRules {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Util.Context {name} {_≟ₙ_}
open import Type
open import Term {name} {_≟ₙ_}
open import TypingContext {name} {_≟ₙ_}
open import Qualifier
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Bool using (Bool)
open import Function using (_∋_)

private
  variable
    α : Scope
    x y : name
    q : Qualifier
    t t₁ t₂ t₃ : Term α
    T T₁ T₂ : Type
    Γ₂ Γ₃ Γ₄ : TypingContext

infix 2 _⊢_::_,_
data _⊢_::_,_ (Γᵢ : TypingContext) : (t : Term α) (ty : Type) (Γₒ : TypingContext) → Set where
  TUVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) →  (qualifierOf T ≡ un) → Γᵢ ⊢ (` x # p) :: T , Γᵢ
  TLVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ lin) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ
  TOVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ ord) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ

  TBool :  {b : Bool} → Γᵢ ⊢ (Term α ∋ ` q ` b ) :: ` q `Bool , Γᵢ
  TUnit : Γᵢ ⊢ (Term α ∋ ` q `unit) :: ` q `Unit , Γᵢ
  TIf :                 Γᵢ ⊢ t₁ :: ` q `Bool , Γ₂
                       → Γ₂ ⊢ t₂ :: T , Γ₃
                       → Γ₂ ⊢ t₃ :: T , Γ₃
                       ------------------------------------------------------------------------
                       → Γᵢ ⊢ `if t₁ then t₂ else t₃  :: T , Γ₃

  TEat : Γᵢ ⊢ t :: ` q `Unit , Γ₂
              ------------------------------------------------------------------------
           → Γᵢ ⊢ `eat t :: ` un `Unit , Γ₃

  TPair : (p₁ : x ∈ α) → (p₂ : y ∈ α)
            → Γᵢ ⊢ ` y # p₂ :: T₂ , Γ₂ -- the context is first passed into t₂ because pairs of ordered variables must conserve the order of the stack. For other variables the order of evaluation (in pairs) doesn't matter, so this is safe.
            → Γ₂ ⊢ ` x # p₁ :: T₁ , Γ₃
            → q ⟨ T₁ ⟩
            → q ⟨ T₂ ⟩
            ------------------------------------------------------------------------
            → Γᵢ ⊢ ` q < x , y > {p₁} {p₂} :: ` q ` T₁ `× T₂ , Γ₃

  TSplit : Γᵢ ⊢ t₁ :: ` q ` T₁ `× T₂ , Γ₂
              → ((Γ₂ , x ↦ T₁) , y ↦ T₂) ⊢ t₂ :: T , Γ₃
              → Γ₃ ÷ (∅ , x ↦ T₁) , y ↦ T₂ ≡ Γ₄
              ------------------------------------------------------------------------
              → Γᵢ ⊢ `split t₁ as x , y ⇒ t₂ :: T , Γ₄

  TLet : Γᵢ ⊢ t₁ :: T₁ , Γ₂
           → Γ₂ , x ↦ T₁ ⊢ t₂ :: T₂ , Γ₃
           → Γ₃ ÷ ∅ , x ↦ T₁ ≡ Γ₄
           ------------------------------------------------------------------------
           → Γᵢ ⊢ `let x := t₁ ⇒ t₂ :: T₂ , Γ₄

  TAbs : (p : q ≢ ord)
            → q ⟨⟨ Γᵢ ⟩⟩
            → Γᵢ , x ↦ T₁ ⊢ t :: T₂ , Γ₂
            → Γ₂ ÷ (∅ , x ↦ T₁) ≡ Γ₃
            ------------------------------------------------------------------------
            → Γᵢ ⊢ (` q ƛ x :: T₁ ⇒ t) {p} :: (` q ` T₁ ⇒ T₂) {p} , Γ₃

  TApp : (p₁ : x ∈ α) (p₂ : y ∈ α) (pq : q ≢ ord)
             → Γᵢ ⊢ ` x # p₁ :: (` q ` T₁ ⇒ T₂) {pq} , Γ₂
             → Γ₂ ⊢ ` y # p₂ :: T₁ , Γ₃
             ------------------------------------------------------------------------
             → Γᵢ ⊢ (x · y) {p₁} {p₂} :: T₂ , Γ₃
