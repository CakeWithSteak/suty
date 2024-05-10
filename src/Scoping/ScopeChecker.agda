module Scoping.ScopeChecker where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; n≮n; m<n⇒m<n⊔o; m≤m⊔n; ⊔-comm; ≤-trans; ≤-reflexive; <-irrefl)
open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (refl; _≡_;_≢_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product
open import Data.Sum
open import Function using (_$_; _∋_)
open import Lang.Qualifier

record AbstractName : Set where
  constructor _aka_
  field
    id : ℕ 
    humanReadable : String

_≟ₙ_ : DecidableEquality AbstractName
(id aka humanReadable) ≟ₙ (id₁ aka humanReadable₁) with id ≟ℕ id₁ | humanReadable ≟String humanReadable₁
... | yes refl | yes refl = yes refl
... | no id-not-eq | _ = no (λ { refl → contradiction refl id-not-eq})
... | _ | no human-not-eq = no (λ { refl → contradiction refl human-not-eq})

eraseAbstractName : AbstractName → String
eraseAbstractName n = AbstractName.humanReadable n

open import Lang.Type
open import Lang.Term {name = AbstractName} {_≟ₙ_}
import Scoping.Context {name = AbstractName} {_≟ₙ_} as Ctx
import Scoping.Context {name = String} {_≟String_} as RawCtx
open RawCtx using (_∈_; _↦_∈_; _,_↦_)
open Ctx renaming (_∈_ to _∈'_; _↦_∈_ to _↦_∈'_; _,_↦_ to _,_↦'_)
open import Raw
open import Raw.Erasure {abstractName = AbstractName} {_≟ₙ_} (eraseAbstractName)

private
  Substitution = RawCtx.Context AbstractName
  
  AllIdsBelow : ℕ → Ctx.Scope → Set
  AllIdsBelow max α = Ctx.All (λ n tt → AbstractName.id n < max) α

  SubsConsistent : Substitution → Ctx.Scope → Set
  SubsConsistent Γ α = {x x' : String} {id : ℕ} → x ↦ (id aka x') ∈ Γ → x ≡ x' × (id aka x) ∈' α

  extendSubsConsistency : {subs : Substitution} {x : String} {id : ℕ} {α : Ctx.Scope} → SubsConsistent subs α → SubsConsistent (subs , x ↦ (id aka x)) (α ⸴ (id aka x))
  extendSubsConsistency  cons RawCtx.here = refl , Ctx.here
  extendSubsConsistency cons (RawCtx.there p) with cons p
  ... | eq , elem = eq , there elem


scopeCheck : (t : RawTerm) → Dec (Σ[ t' ∈ Term Ctx.∅ ] EraseTerm t' t)
scopeCheck t = {!f t RawCtx.∅ zero RawCtx.All.∅!}
  where
    f : (t : RawTerm) → (subs : Substitution) → (α : Ctx.Scope) → (max : ℕ) →  AllIdsBelow max α → SubsConsistent subs α → Dec ((Σ[ t' ∈ Term α ] EraseTerm t' t))
    
    f (RVar x) subs α max α-lt-max subs-cons  with RawCtx.lookup subs x
    ... | yes (x' , proof-x') with subs-cons proof-x'
    ... | refl , in-α = yes (` x' # in-α , EVar)
    f (RBool x x₁) subs α max α-lt-max subs-cons = {!!}
    f (RUnit x) subs α max α-lt-max subs-cons = {!!}
    f (RIf t t₁ t₂) subs α max α-lt-max subs-cons = {!!}
    f (RPair x x₁ x₂) subs α max α-lt-max subs-cons = {!!}
    f (RSplit t x x₁ t₁) subs α max α-lt-max subs-cons = {!!}
    f (RAbs x x₁ x₂ t) subs α max α-lt-max subs-cons = {!!}
    f (RApp x x₁) subs α max α-lt-max subs-cons = {!!}
    f (RLet x t tinner) subs α max α-lt-max subs-cons with f t subs α max α-lt-max subs-cons | f tinner (subs , x ↦ (max aka x)) (α ⸴ (max aka x)) (suc max) (mapAll m<n⇒m<1+n α-lt-max , n<1+n max) (extendSubsConsistency subs-cons)
    ... | yes (t' , t-erasure) | yes (tinner' , tinner-erasure) = yes ((`let max aka x := t' ⇒ tinner') {¬all⇒∉ α-lt-max (n≮n max)}, (ELet t-erasure tinner-erasure))
    ... | no t-bad | _ = no λ { ((`let _ := t' ⇒ _)  , ELet t-good _) → contradiction (t' , t-good) t-bad}
    ... | _ | no tinner-bad = no λ { ((`let (id aka .x) := t' ⇒ tinner') , ELet _ tinner-good) → contradiction ({!`let (max aka x) := t' ⇒ tinner'!} , {!!}) tinner-bad}
    f (REat t) subs α max α-lt-max subs-cons = {!!}
