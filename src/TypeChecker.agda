module TypeChecker where

open import Data.String renaming (_≟_ to _≟ₛ_)
name = String

open import Type
open import TypingRules {name} {_≟ₛ_}
open import TypingContext {name} {_≟ₛ_}
open import Term {name} {_≟ₛ_}
open import Util.Context {name} {_≟ₛ_}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Function using (case_of_)

private
  variable
    α : Scope

typeOf : (Γ : TypingContext) → (t : Term α) → Dec (Σ (Type × TypingContext) λ { (T , Γ') → Γ ⊢ t :: T , Γ' } )
typeOf Γ (` q # x) = {!!}
typeOf Γ (` x ` x₁) = {!!}
typeOf Γ (` x `unit) = {!!}
typeOf Γ (`if t then t₁ else t₂) = {!!}
typeOf Γ (` x < x₁ , y >) = {!!}
typeOf Γ (`split t as x , y ⇒ t₁) = {!!}
typeOf Γ (` q ƛ x :: x₁ ⇒ t) = {!!}
typeOf Γ (x · y) = {!!}
typeOf Γ (`let x := t ⇒ t₁) = {!!}
typeOf Γ (`eat t) = {!!}
