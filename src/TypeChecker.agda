module TypeChecker where

open import Data.String renaming (_≟_ to _≟ₛ_)
name = String

open import Type
open import Qualifier
open import TypingRules {name} {_≟ₛ_}
open import TypingContext {name} {_≟ₛ_}
open import Term {name} {_≟ₛ_}
open import Util.Context {name} {_≟ₛ_}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Function using (case_of_; _$_)

private
  variable
    α : Scope

typeOf : (Γ : TypingContext) → (t : Term α) → Dec (Σ (Type × TypingContext) λ { (T , Γ') → Γ ⊢ t :: T , Γ' } )
checkType : (Γ : TypingContext) → (t : Term α) → (T : Type) → Dec (Σ (TypingContext) λ Γ' → Γ ⊢ t :: T , Γ' )

typeOf Γ (` x # well-scoped) with typeLookup Γ x
...  | no not-elem = no (λ { ((ty , _) , TUVar .well-scoped elem _) → contradiction (ty , elem) not-elem ; ((ty , _) , TLVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ; ((ty , _) , TOVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem})
...  | yes (ty , elem) = yes $ qualifierCases ty
           (λ is-un → (ty , Γ) , (TUVar well-scoped elem is-un))
           (λ is-lin → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TLVar well-scoped elem is-lin Γ' Γ'-proof)
           (λ is-ord → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TOVar well-scoped elem is-ord Γ' Γ'-proof)
typeOf Γ (` q ` b) = yes ((` q `Bool , Γ) , TBool)
typeOf Γ (` q `unit) = yes ((` q `Unit , Γ) , TUnit)
typeOf Γ (`if t₁ then t₂ else t₃) with typeOf Γ t₁
... | no cond-not-bool = no (λ { (_ , TIf {q = q} cond-bool _ _) → {!contradiction!}})
... | yes cond-bool = {!!}
typeOf Γ (` x < x₁ , y >) = {!!}
typeOf Γ (`split t as x , y ⇒ t₁) = {!!}
typeOf Γ (` q ƛ x :: x₁ ⇒ t) = {!!}
typeOf Γ (x · y) = {!!}
typeOf Γ (`let x := t ⇒ t₁) = {!!}
typeOf Γ (`eat t) = {!!}

checkType Γ t T with typeOf Γ t
... | no untypable = {!!}
... | yes (T' , T'-proof)= {!!}
