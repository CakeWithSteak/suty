module Scoping.ScopeChecker where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; n≮n; m<n⇒m<n⊔o; m≤m⊔n; ⊔-comm; ≤-trans; ≤-reflexive; <-irrefl)
open import Data.String using (String) renaming (_≟_ to _≟String_)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (refl; _≡_;_≢_)
open import Relation.Nullary.Negation using (contradiction; contraposition)
open import Data.Product
open import Data.Sum
open import Function using (_$_; _∋_)
open import Lang.Qualifier
open import Function using (case_of_)

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

-- Order of variables in a Scope does not matter, but doing things at the end is easier -- this helper swaps the last two varaibles
--exchangeLastTwoBinds : {α : Ctx.Scope} {x y : AbstractName} → Term (α ⸴ x ⸴ y) → Term (α ⸴ y ⸴ x)
--exchangeLastTwoBinds (` x # here) = ` x # there here
--exchangeLastTwoBinds (` x # there here) = ` x # here
--exchangeLastTwoBinds (` x # there (there well-scoped-x)) = ` x # there (there well-scoped-x)
--exchangeLastTwoBinds (` q ` b) = ` q ` b
--exchangeLastTwoBinds ` q `unit = ` q `unit
--exchangeLastTwoBinds (`if t then t₁ else t₂) = `if --exchangeLastTwoBinds t then --exchangeLastTwoBinds t₁ else --exchangeLastTwoBinds t₂
--exchangeLastTwoBinds ((` q < x , y >) {here} {here}) = ` q < x , y > {there here} {there here}
--exchangeLastTwoBinds ((` q < x , y >) {there here} {here}) = ` q < x , y > {here} {there here}
--exchangeLastTwoBinds ((` q < x , y >) {here} {there here}) = ` q < x , y > {there here} {here}
--exchangeLastTwoBinds ((` q < x , y >) {there here} {there here}) = ` q < x , y > {here} {here}
--exchangeLastTwoBinds ((` q < x , y >) {there (there well-scoped-x)} {here}) = ` q < x , y > {there (there well-scoped-x)} {there here}
--exchangeLastTwoBinds ((` q < x , y >) {there (there well-scoped-x)} {there here}) = ` q < x , y > {there (there well-scoped-x)} {here}
--exchangeLastTwoBinds ((` q < x , y >) {here} {there (there well-scoped-y)}) = ` q < x , y > {there here} {there (there well-scoped-y)}
--exchangeLastTwoBinds ((` q < x , y >) {there here} {there (there well-scoped-y)}) = ` q < x , y > {here} {there (there well-scoped-y)}
--exchangeLastTwoBinds ((` q < x , y >) {there (there well-scoped-x)} {there (there well-scoped-y)}) = ` q < x , y > {there (there well-scoped-x)} {there (there well-scoped-y)}
--exchangeLastTwoBinds (`split t as x , y ⇒ t₁) = `split (--exchangeLastTwoBinds t) as {!!} , {!!} ⇒ {!!}
--exchangeLastTwoBinds (` q ƛ x :: x₁ ⇒ t) = {!!}
--exchangeLastTwoBinds (x · y) = {!!}
--exchangeLastTwoBinds (`let x := t ⇒ t₁) = {!!}
--exchangeLastTwoBinds (`eat t) = {!!}

--α-convert : {α : Ctx.Scope} →  (x : AbstractName) → (y : AbstractName) → Term (α ⸴ x) → Term (α ⸴ y)
--α-convert x y (` .x # here) = ` y # here
--α-convert x y (` z # there well-scoped-z) = ` z # there well-scoped-z
--α-convert x y (` q ` b) = ` q ` b
--α-convert x y ` q `unit = ` q `unit
--α-convert x y (`if t then t₁ else t₂) = `if (--α-convert x y t) then (--α-convert x y t₁) else (--α-convert x y t₂)
--α-convert x y (` q < .x , .x > {here} {here}) = ` q < y , y > {here} {here}
--α-convert x y (` q < .x , w > {here} {there well-scoped-w}) = ` q < y , w > {here} {there well-scoped-w}
--α-convert x y (` q < z , .x > {there well-scoped-z} {here}) = ` q < z , y > {there well-scoped-z} {here}
--α-convert x y (` q < z , w > {there well-scoped-z} {there well-scoped-w}) = ` q < z , w > {there well-scoped-z} {there well-scoped-w} 
--α-convert x y ((`split t as z , w ⇒ t₁) {z-uniq} {w-uniq} {z-not-w}) with z ≟ₙ x | w ≟ₙ x
--... | yes refl | yes refl = contradiction refl z-not-w
--... | yes refl | no _ = `split (--α-convert x y t) as y , w ⇒ ({!!})
--... | no _ | yes refl = {!!}
--... | no _ | no _ = {!!}
--α-convert x y (` q ƛ x₁ :: x₂ ⇒ t) = {!!}
--α-convert x y (x₁ · y₁) = {!!}
--α-convert x y (`let x₁ := t ⇒ t₁) = {!!}
--α-convert x y (`eat t) = {!!}

-- Can't find this in Data.Nat.Properties
n≤m⇒n<1+m : {n m : ℕ} → n ≤ m → n < 1 + m
n≤m⇒n<1+m z≤n = z<s
n≤m⇒n<1+m (s≤s n-1≤m-1) = s≤s (s≤s n-1≤m-1)

freshUniqueVar : (α : Ctx.Scope) → Σ[ a ∈ AbstractName ] a ∉ α
freshUniqueVar α = let (id , proof) = strictUpperBoundId α in (id aka "#fresh") , ¬all⇒∉ proof (<-irrefl refl)
  where
    strictUpperBoundId : (α : Ctx.Scope) → Σ[ max ∈ ℕ ] (All (λ {(id aka _) tt → id < max}) α)
    strictUpperBoundId ∅ = zero , ∅
    strictUpperBoundId (α ⸴ (id aka _)) = let (max , all) = strictUpperBoundId α in (suc (max ⊔ id)) , ( mapAll (λ { {x = id' aka _} id'<max → m<n⇒m<1+n $ m<n⇒m<n⊔o id id'<max }) all , (n≤m⇒n<1+m $ ≤-trans (m≤m⊔n id max) (≤-reflexive (⊔-comm id max))))


rescopeTerm : {α β : Scope} → ScopeEquivalent α β → Term α → Term β
rescopeTerm record { equiv = equiv } (` x # well-scoped-x) = ` x # _⇔_.to (equiv x) well-scoped-x
rescopeTerm record { equiv = equiv } (` q ` b) = ` q ` b
rescopeTerm record { equiv = equiv } ` q `unit = ` q `unit
rescopeTerm se@record { equiv = equiv } (`if t then t₁ else t₂) = `if (rescopeTerm se t) then (rescopeTerm se t₁) else (rescopeTerm se t₂)
rescopeTerm record { equiv = equiv } ((` q < a , b >) {well-scoped-a} {well-scoped-b}) = ` q < a , b > {_⇔_.to (equiv a) well-scoped-a} {_⇔_.to (equiv b) well-scoped-b}
rescopeTerm se@record { equiv = equiv } ((`split t as x , y ⇒ t₁) {x-uniq} {y-uniq} {x≢y}) = (`split rescopeTerm se t as x , y ⇒ rescopeTerm extendedEquivalence t₁) {x-uniq-b} {y-uniq-b} {x≢y}
  where
    extendedEquivalence = extendEquivalence y $ extendEquivalence x se
    x-uniq-b = contraposition (_⇔_.from (equiv x)) x-uniq
    y-uniq-b = contraposition (_⇔_.from (equiv y)) y-uniq
rescopeTerm se@record { equiv = equiv } ((` q ƛ x :: T ⇒ t) {q-not-ord} {x-uniq}) = (` q ƛ x :: T ⇒ rescopeTerm (extendEquivalence x se) t) {q-not-ord} {contraposition (_⇔_.from (equiv x)) x-uniq}
rescopeTerm record { equiv = equiv } ((x · y) {well-scoped-x} {well-scoped-y}) = (x · y) {(_⇔_.to (equiv x) well-scoped-x)} {_⇔_.to (equiv y) well-scoped-y}
rescopeTerm se@record { equiv = equiv } ((`let x := t ⇒ t₁) {x-uniq}) = (`let x := (rescopeTerm se t) ⇒ (rescopeTerm (extendEquivalence x se) t₁)) {contraposition (_⇔_.from (equiv x)) x-uniq}
rescopeTerm se@record { equiv = equiv } (`eat t) = `eat (rescopeTerm se t)

α-convert : {α : Scope} (x : AbstractName) (y : AbstractName) → Term α → Σ[ β ∈ Scope ] (Term β × ScopeRenamed α β x y)
α-convert {α} x y (` a # well-scoped-a) with a ≟ₙ x
... | yes refl = ? , ?
... | no a≢x = {!!}
α-convert {α} x y (` q ` b) = {!!}
α-convert {α} x y ` q `unit = {!!}
α-convert {α} x y (`if t then t₁ else t₂) = {!!}
α-convert {α} x y ` q < a , b > = {!!}
α-convert {α} x y (`split t as a , b ⇒ t₁) = {!!}
α-convert {α} x y (` q ƛ a :: T ⇒ t) = {!!}
α-convert {α} x y (a · b) = {!!}
α-convert {α} x y (`let a := t ⇒ t₁) = {!!}
α-convert {α} x y (`eat t) = {!!}

--freshUniqueVar ∅ = (zero aka "?fresh") , (λ ())
--freshUniqueVar (α ⸴ (id aka _)) = ((suc {!id ⊔ !}) aka {!!}) , {!!}

--α-convert-split₁ : {α : Scope} (x y b : AbstractName) {x-uniq : x ∉ α} {b-uniq : b ∉ α} {y-uniq : y ∉ α}  {x≢y : x ≢ y} {x≢b : x ≢ b} {y≢b : y ≢ b} {t₁ : Term α} {t₂ : Term (α ⸴ x ⸴ b)}  → (t : Term α)  → {is-split : t ≡ (`split t₁ as x , b ⇒ t₂) {x-uniq} {b-uniq} {x≢b}} → Term α
--α-convert-split₂ : {α : Scope} (a x y : AbstractName) {x-uniq : x ∉ α} {a-uniq : a ∉ α} {y-uniq : y ∉ α}  {x≢y : x ≢ y} {a≢x : a ≢ x} {y≢a : y ≢ a} {t₁ : Term α} {t₂ : Term (α ⸴ a ⸴ x)} → (t : Term α) →  {is-split : t ≡ (`split t₁ as a , x ⇒ t₂) {a-uniq} {x-uniq} {a≢x}}  → Term α
--α-convert-single-binder : {α : Scope} (x y : AbstractName) {q : Qualifier} {T : Type} {q-not-ord : q ≢ ord} {x-uniq : x ∉ α} {t₁ : Term α} {t₂ : Term (α ⸴ x)} → (t : Term α) → {is-single-binder : t ≡ ((` q ƛ x :: T ⇒ t₂) {q-not-ord} {x-uniq}) ⊎ t ≡ (`let x := t₁ ⇒ t₂) {x-uniq}} → Term α
--α-convert : {α : Scope} (x y : AbstractName) → Term α → Term α

--α-convert-split₁ x y b (`split t₁ as .x , .b ⇒ t₂) {is-split = refl} = `split t₁ as b , y ⇒ {!α-convert x y t₂!}

-- green slime? hope not!
--α-convert : {α : Scope} (x y : AbstractName) (x∈α : x ∈' α) → Term α → Term (proj₁ $ replaceInScope x y α x∈α)
--α-convert' : {α : Scope} (x y : AbstractName) (x∈α : x ∈' α) → Term α → Σ[ β ∈ Scope ] (β ≡ (proj₁ $ replaceInScope x y α x∈α) × Term β)

--α-convert' {α} x y x∈α t = (proj₁ $ replaceInScope x y α x∈α) , (refl , α-convert x y x∈α t)

--α-convert {α} x y x∈α (` a # well-scoped-a) with a ≟ₙ x
--... | yes refl = let (β , y∈β , rest-preserved) = replaceInScope x y α x∈α in  ` y # y∈β
--... | no x≢a =  let (β , y∈β , rest-preserved) = replaceInScope x y α x∈α in ` a # rest-preserved a x≢a well-scoped-a
--α-convert x y x∈α (` x₁ ` x₂) = {!!}
--α-convert x y x∈α ` x₁ `unit = {!!}
--α-convert x y x∈α (`if t then t₁ else t₂) = {!!}
--α-convert x y x∈α ` x₁ < x₂ , y₁ > = {!!}
--α-convert {α} x y x∈α ((`split t as a , b ⇒ t₁) {a-uniq} {b-uniq} {a≢b}) with a ≟ₙ x | b ≟ₙ x
--... | yes refl | yes refl = contradiction refl a≢b
--... | yes refl | no _ = let
 --   t'  = α-convert x y x∈α t
  --  β = scopeOf t'
   -- (fresh , fresh-uniq) = freshUniqueVar β
   -- (γ , (γ-id , t₁')) = α-convert' x fresh (there here) t₁
    --(β' , fresh∈β' , rest-preserved) = replaceInScope x fresh ({!!} ⸴ x ⸴ b) (there here)
    --(γ , t₁') = ?
  --in case  (γ-id) of λ { (refl) → (`split t' as fresh , b ⇒ {!t₁'!})}
--... | no _ | yes refl = {!!}
--... | no _ | no _ = {!!}
--α-convert x y x∈α (` q ƛ x₁ :: x₂ ⇒ t) = {!!}
--α-convert x y x∈α (x₁ · y₁) = {!!}
--α-convert x y x∈α (`let x₁ := t ⇒ t₁) = {!!}
--α-convert x y x∈α (`eat t) = {!!}

--α-convert-split₁

--α-convert : {α β : Scope} (x y : AbstractName) →  y ∈' β → Term α → Term β
--α-convert x y well-scoped-y (` a # well-scoped-x) = ` y # well-scoped-y
--α-convert x y well-scoped-y (` x₁ ` x₂) = {!!}
--α-convert x y well-scoped-y ` x₁ `unit = {!!}
--α-convert x y well-scoped-y (`if t then t₁ else t₂) = {!!}
--α-convert x y well-scoped-y ` x₁ < x₂ , y₁ > = {!!}
--α-convert {β = β} x y well-scoped-y ((`split t as a , b ⇒ t₁) {well-scoped-a} {well-scoped-b} {a≢b} ) with a ≟ₙ x | a ≟ₙ b
--...| yes refl | _ = let (fresh , proof-fresh) = freshUniqueVar β in (`split (α-convert x y well-scoped-y t) as fresh , b ⇒ α-convert x fresh (there here) t₁) {proof-fresh} {{!well-scoped-b!}} {{!!}}
--... | _ | yes refl = {!!}
--... | no _ | no _ = {!!}
--α-convert x y well-scoped-y (` q ƛ x₁ :: x₂ ⇒ t) = {!!}
--α-convert x y well-scoped-y (x₁ · y₁) = {!!}
--α-convert x y well-scoped-y (`let x₁ := t ⇒ t₁) = {!!}
--α-convert x y well-scoped-y (`eat t) = {!!}

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
