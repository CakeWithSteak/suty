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
open import Data.Sum using (inj₁; inj₂)

private
  variable
    α : Scope

private if-untypable-if-either-arm-untypable : ∀ {Γ Γ' T} {t t₁ t₂ : Term α} → Γ ⊢ t :: T , Γ' → (Γ' ⊢ t₁ ::⊥) ⊎ (Γ' ⊢ t₂ ::⊥) → Γ ⊢(`if t then t₁ else t₂) ::⊥
if-untypable-if-either-arm-untypable cond (inj₁ t₁-untypable) = λ { ((T , Γ') , TIf cond' t₁-typable _) → case typing-unique cond cond' of λ {(refl , refl) → contradiction ((T , Γ') , t₁-typable) t₁-untypable}}
if-untypable-if-either-arm-untypable cond (inj₂ t₂-untypable) = λ { ((T , Γ') , TIf cond' _ t₂-typable) → case typing-unique cond cond' of λ {(refl , refl) → contradiction ((T , Γ') , t₂-typable) t₂-untypable}}

typeOf : (Γ : TypingContext) → (t : Term α) → Dec (Σ (Type × TypingContext) λ { (T , Γ') → Γ ⊢ t :: T , Γ' } )
checkType : (Γ : TypingContext) → (t : Term α) → (T : Type) → Dec (Σ (TypingContext) λ Γ' → Γ ⊢ t :: T , Γ' ) -- todo useless?

typeOf Γ (` x # well-scoped) with typeLookup Γ x
...  | no not-elem = no (λ { ((ty , _) , TUVar .well-scoped elem _) → contradiction (ty , elem) not-elem ; ((ty , _) , TLVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ; ((ty , _) , TOVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem})
...  | yes (ty , elem) = yes $ qualifierCases ty
           (λ is-un → (ty , Γ) , (TUVar well-scoped elem is-un))
           (λ is-lin → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TLVar well-scoped elem is-lin Γ' Γ'-proof)
           (λ is-ord → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TOVar well-scoped elem is-ord Γ' Γ'-proof)
typeOf Γ (` q ` b) = yes ((` q `Bool , Γ) , TBool)
typeOf Γ (` q `unit) = yes ((` q `Unit , Γ) , TUnit)
typeOf Γ (`if t₁ then t₂ else t₃) with typeOf Γ t₁
... | no cond-untypable = no (λ { (_ , TIf  {q = q} {Γ₂ = Γ₂} cond-bool _ _) → contradiction ((` q `Bool , Γ₂) , cond-bool) cond-untypable})
... | yes ((T-cond , Γ₂) , cond-proof) with bool? T-cond
... | no' cond-not-bool = no (λ { (_ , TIf  cond-bool _ _) → typing-contradiction cond-not-bool cond-bool cond-proof})
... | yes' cond-bool with typeOf Γ₂ t₂ | typeOf Γ₂ t₃
... | no a  | _ = no (if-untypable-if-either-arm-untypable cond-proof (inj₁ a))
... | _        | no b =  no (if-untypable-if-either-arm-untypable cond-proof (inj₂ b))
typeOf Γ (` x < x₁ , y >) = {!!}
typeOf Γ (`split t as x , y ⇒ t₁) = {!!}
typeOf Γ (` q ƛ x :: x₁ ⇒ t) = {!!}
typeOf Γ (x · y) = {!!}
typeOf Γ (`let x := t ⇒ t₁) = {!!}
typeOf Γ (`eat t) = {!!}

checkType Γ t T with typeOf Γ t
... | no untypable = no λ { (Γ' , proof) → contradiction ((T , Γ') , proof) untypable}
... | yes ((T' , Γ') , T'-proof) with T ≟ₜ T'
...   | no T≢T' = no λ {(Γ'' , Γ''-proof) → contradiction (proj₁ (typing-unique Γ''-proof T'-proof)) T≢T'}
...   | yes refl = yes (Γ' , T'-proof)
