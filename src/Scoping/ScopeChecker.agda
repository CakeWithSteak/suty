-- Turns raw terms into enriched terms, if possible. Most of the work is renaming varaibles from String identifiers to AbstractNames, which
-- contain a unique numeric ID for each variable (along with its original name)
module Scoping.ScopeChecker where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; n≮n; m<n⇒m<n⊔o; m≤m⊔n; ⊔-comm; ≤-trans; ≤-reflexive; <-irrefl; <-asym)
open import Data.String using (String; _++_) renaming (_≟_ to _≟String_)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (refl; _≡_;_≢_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product
open import Data.Sum
open import Function using (_$_; _∋_)
open import Lang.Qualifier
open import Lang using (AbstractName; _aka_;  _≟ₙ_; eraseAbstractName)
open import Lang.Type
open import Lang.Term {name = AbstractName} {_≟ₙ_}
import Scoping.Context {name = AbstractName} {_≟ₙ_} as Ctx
import Scoping.Context {name = String} {_≟String_} as RawCtx
open RawCtx using (_∈_; _↦_∈_; _,_↦_)
open Ctx renaming (_∈_ to _∈'_; _↦_∈_ to _↦_∈'_; _,_↦_ to _,_↦'_)
open import Raw
open import Raw.Erasure {abstractName = AbstractName} {_≟ₙ_} (eraseAbstractName)

-- Helper types for the scope checker
private
  -- Maps Strings to AbstractNames
  Substitution = RawCtx.Context AbstractName

  -- All IDs in the scope are below some number
  AllIdsBelow : ℕ → Ctx.Scope → Set
  AllIdsBelow max α = Ctx.All (λ n tt → AbstractName.id n < max) α

  -- The substitution from the raw context to the enriched context is consistent with the enriched context: human readable names are stored corretly and the appropriate bindigns are in the enriched context
  SubsConsistent : Substitution → Ctx.Scope → Set
  SubsConsistent Γ α = {x x' : String} {id : ℕ} → x ↦ (id aka x') ∈ Γ → x ≡ x' × (id aka x) ∈' α

  -- Extends the proof of consistency with a new substitution
  extendSubsConsistency : {subs : Substitution} {x : String} {id : ℕ} {α : Ctx.Scope} → SubsConsistent subs α → SubsConsistent (subs , x ↦ (id aka x)) (α ⸴ (id aka x))
  extendSubsConsistency  cons RawCtx.here = refl , Ctx.here
  extendSubsConsistency cons (RawCtx.there p) with cons p
  ... | eq , elem = eq , there elem

data ScopeCheckResult {α : Scope} (t : RawTerm) : Set where
  good : Σ[ t' ∈ Term α ] EraseTerm t' t → ScopeCheckResult t
  bad : String → ScopeCheckResult t

-- Checks if a raw type is valid
checkType : (R : RawType) → Dec (Σ[ T ∈ Type ] EraseType T R)
checkType (RTyBool q) = yes (` q `Bool , ETyBool)
checkType (RTyUnit q) = yes (` q `Unit , ETyUnit)
checkType (RTyProduct q T U) with checkType T | checkType U
... | yes (T' , T-erasure) | yes (U' , U-erasure) = yes ((` q ` T' `× U') , ETyProduct T-erasure U-erasure)
... | no T-bad | _ = no λ { (` _ ` T' `× _ , ETyProduct T-good _) → contradiction (T' , T-good) T-bad }
... | _ | no U-bad = no λ { (` _ ` _ `× U' , ETyProduct _ U-good) → contradiction (U' , U-good) U-bad }
checkType (RTyArrow q T U)  with checkType T | checkType U | q ≟q ord
... | yes (T' , T-erasure) | yes (U' , U-erasure) | no q-not-ord = yes ((` q ` T' ⇒ U') {q-not-ord} , (ETyArrow T-erasure U-erasure))
... | no T-bad | _ | _ = no λ { (` _ ` T' ⇒ _ , ETyArrow T-good _)  → contradiction (T' , T-good) T-bad }
... | _ | no U-bad | _  = no λ { (` _ ` _ ⇒ U' , ETyArrow _ U-good) → contradiction (U' , U-good) U-bad }
... | _ | _ | yes refl = no λ { ((` .ord ` _ ⇒ _) {q-not-ord} , ETyArrow _ _) → contradiction refl q-not-ord}

scopeCheck : (t : RawTerm) → ScopeCheckResult {Ctx.∅} t
scopeCheck t = f t RawCtx.∅ ∅ zero ∅ (λ ())
  where
    -- The scope checker maintains a number of values and correctness proofs throughout its run:
    f : (t : RawTerm) -- The term
        → (subs : Substitution) -- The current substitutions
        → (α : Ctx.Scope) -- The current scope
        → (max : ℕ) -- The largest ID currently in use
        →  AllIdsBelow max α -- Proof that max is indeed the largest ID
        → SubsConsistent subs α -- Proof that subs and α match
        → ScopeCheckResult {α} t
    
    f (RVar x) subs α max α-lt-max subs-cons  with RawCtx.lookup subs x -- look at what abstract name this variable has
    ... | no _ = bad ("Unbound variable " ++ x) -- none: unbound, fail
    ... | yes (x' , proof-x') with subs-cons proof-x' -- obtain a proof of well-scopedness and succeed
    ... | refl , in-α = good (` x' # in-α , EVar)
    f (RBool q b) subs α max α-lt-max subs-cons = good ((` q ` b) , EBool)
    f (RUnit q) subs α max α-lt-max subs-cons = good ((` q `unit) , EUnit)
    f (RIf t t₁ t₂) subs α max α-lt-max subs-cons with f t subs α max α-lt-max subs-cons | f t₁ subs α max α-lt-max subs-cons  | f t₂ subs α max α-lt-max subs-cons -- scope check all subterms
    ... | good (t' , t-erasure) | good (t₁' , t₁-erasure) | good (t₂' , t₂-erasure) = good ((`if t' then t₁' else t₂') , EIf t-erasure t₁-erasure t₂-erasure) -- all good: succeed
    ... | bad t-bad | _ | _ = bad ("If condition bad: " ++ t-bad)
    ... | _ | bad t₁-bad | _ = bad ("If then branch bad: " ++ t₁-bad)
    ... | _ | _ | bad t₂-bad = bad ("If else bad: " ++ t₂-bad)
    f (RPair q x y) subs α max α-lt-max subs-cons with RawCtx.lookup subs x | RawCtx.lookup subs y -- lookup pair components
    ... | no _ | _ = bad ("Unbound variable: " ++ x)
    ... | _ | no _ = bad ("Unbound variable: " ++ y)
    ... | yes (x' , proof-x') | yes (y' , proof-y') with subs-cons proof-x' | subs-cons proof-y' -- obtain well-scopedness proofs
    ... | refl , x∈α | refl , y∈α = good (` q < x' , y' > {x∈α} {y∈α} , EPair)
    f (RSplit t x y t₁) subs α max α-lt-max subs-cons  with f t subs α max α-lt-max subs-cons | f t₁ subs' α' (suc $ suc max) α'-lt-max subs-cons' -- scope check t and t₁, increasing max by two for t₁
      where
        x' = (max aka x) -- abstract name for x
        y' = (suc max aka y) -- abstract name for y
        subs' = (subs , x ↦ x') ,  y ↦ y' -- new substitution
        α' = α ⸴ x' ⸴ y' -- new scope
        α'-lt-max = mapAll m<n⇒m<1+n (mapAll m<n⇒m<1+n α-lt-max , n<1+n max) , (n<1+n $ suc max) -- proof that the new max is still the max of the new scope
        subs-cons' = extendSubsConsistency $ extendSubsConsistency subs-cons -- extend the consistency proof
    ... | good (t' , t-erasure) | good (t₁' , t₁-erasure) = good ((`split t' as (max aka x) , (suc max aka y) ⇒ t₁')
                                                                                                                 {¬all⇒∉ α-lt-max (n≮n max)} -- x is unique because it is bellow the max
                                                                                                                 {¬all⇒∉ α-lt-max (<-asym $ n<1+n max)} -- y is unique because it is below the max
                                                                                                                 {λ ()} -- x ≢ y because max ≢ suc max
                                                                                                                 , ESplit t-erasure t₁-erasure)
    ... | bad err | _ = bad ("Split argument bad: " ++ err)
    ... | _ | bad err = bad ("Split body bad: " ++ err)
    f (RAbs q x T t) subs α max α-lt-max subs-cons with q ≟q ord | checkType T  | f t (subs , x ↦ (max aka x)) (α ⸴ (max aka x)) (suc max) (mapAll m<n⇒m<1+n α-lt-max , n<1+n max) (extendSubsConsistency subs-cons) -- check qualifier, type, scope check body with new binding
    ... | no q-not-ord | yes (T' , T-erasure) | good (t' , t-erasure) = good ((` q ƛ (max aka x) :: T' ⇒ t') {q-not-ord} {¬all⇒∉ α-lt-max (n≮n max)} , EAbs T-erasure t-erasure)
    ... | yes q-ord | _ | _ = bad "Ordered functions are not allowed"
    ... | _ | no T-bad | _ = bad "Invalid function argument type"
    ... | _ | _ | bad t-bad = bad ("Function body bad: " ++ t-bad)
    f (RApp x y) subs α max α-lt-max subs-cons with RawCtx.lookup subs x | RawCtx.lookup subs y -- look up funciton and argument
    ... | no _ | _ = bad ("Unbound variable: " ++ x)
    ... | _ | no _ = bad ("Unbound variable: " ++ y)
    ... | yes (x' , x∈subs) | yes (y' , y∈subs) with subs-cons x∈subs | subs-cons y∈subs -- obtain well-scopedness proofs
    ... | refl , x∈α  | refl , y∈α = good ((x' · y') {x∈α} {y∈α} , EApp)
    f (RLet x t tinner) subs α max α-lt-max subs-cons with f t subs α max α-lt-max subs-cons | f tinner (subs , x ↦ (max aka x)) (α ⸴ (max aka x)) (suc max) (mapAll m<n⇒m<1+n α-lt-max , n<1+n max) (extendSubsConsistency subs-cons) -- scope check t and tinner extending tinner with the new binding 
    ... | good (t' , t-erasure) | good (tinner' , tinner-erasure) = good ((`let max aka x := t' ⇒ tinner') {¬all⇒∉ α-lt-max (n≮n max)}, (ELet t-erasure tinner-erasure))
    ... | bad t-bad | _ = bad ("Let binding term bad: " ++  t-bad)
    ... | _ | bad tinner-bad = bad ("Let inner term bad: " ++ tinner-bad)
    f (REat t) subs α max α-lt-max subs-cons with f t subs α max α-lt-max subs-cons -- scope check argument
    ... | good (t' , t-erasure) = good (`eat t' , EEat t-erasure)
    ... | bad t-bad = bad ("Eat argument bad: " ++ t-bad)
