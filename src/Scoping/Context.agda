open import Relation.Binary.Definitions using (DecidableEquality)
open import Level

module Scoping.Context {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (⌊_⌋; _×-dec_; yes; no; does; _because_; of; ¬_; Dec; contradiction)
open import Relation.Unary using (Pred) renaming (Decidable to Decidable₁)
open import Relation.Binary using (REL; IsDecEquivalence; _⇒_) renaming (Decidable to Decidable₂)
open import Data.Bool using (true; false; if_then_else_)
open import Function.Base using (case_of_; _$_)
open import Data.Product
open import Data.Sum
open import Data.Empty

private
  variable
    V : Set

-- Represents a generic context (scope, typing context, store, etc) indexed by name
data Context (V : Set) : Set where
  ∅ : Context V
  _,_↦_ : Context V → name → V → Context V

infix 4  _,_↦_
infixl 4 _⸴_
infix 4 _↦_∈_

-- NB this is a raised comma (\, number 4) so as not to conflict with pairs
pattern _⸴_ Γ x = (Γ , x ↦ _)

data _↦_∈_  (x : name) (v : V) : Context V → Set  where
  here : {Γ : Context V} → x ↦ v ∈ (Γ , x ↦ v)
  there : ∀ {y w} {Γ : Context V} (_ : x ↦ v ∈ Γ) → x ↦ v ∈ (Γ , y ↦ w)

_∈_ :  name → Context ⊤ → Set
_∈_ x Γ = x ↦ tt ∈ Γ

_∉_ : name → Context ⊤ → Set
_∉_ x Γ = ¬ (x ↦ tt ∈ Γ)

_↦_∈?_ : (x : name) (v : V) (Γ : Context V) {_≟ᵥ_ : DecidableEquality V} → Dec (x ↦ v ∈ Γ)
x ↦ v ∈? ∅ = no (λ ())
(x ↦ v ∈? (Γ , y ↦ u)) {_≟ᵥ_} with x ≟ₙ y ×-dec v ≟ᵥ u | (x ↦ v ∈? Γ) {_≟ᵥ_}
... | yes (refl , refl)  | _ = yes here
... | no ¬eq | no ¬elem = no λ { here → ¬eq (refl , refl) ; (there actually-elem) → ¬elem actually-elem}
... | no ¬eq | yes elem  = yes (there elem)

lookup : (Γ : Context V) (x : name) → Dec (Σ[ v ∈ V ] x ↦ v ∈ Γ)
lookup ∅ x = no (λ { ()})
lookup (Γ , y ↦ u) x with x ≟ₙ y
... | yes refl = yes (u , here)
... | no x≢y with lookup Γ x
...   | no nosub = no (λ { (v , here) → contradiction refl x≢y ; (v , there p) → contradiction (v , p) nosub})
... | yes (v , p) = yes (v , (there p))


data All (R : REL name V 0ℓ) : Pred (Context V) 0ℓ where
  ∅ : All R ∅
  _,_ : ∀ {x v Γ} (rest : All R Γ) (this : R x v) → All R (Γ , x ↦ v)

mapAll : {A : REL name V 0ℓ} {B : REL name V 0ℓ} {Γ : Context V} → A ⇒ B → All A Γ → All B Γ
mapAll impl ∅ = ∅
mapAll impl (a , this) = mapAll impl a , impl this

all? : {R : REL name V 0ℓ} → Decidable₂ R  → Decidable₁ (All R)
all? r ∅ = yes ∅
all? r (Γ , x ↦ v) with all? r Γ
... | no ¬a = no λ { (prev , this) → ¬a prev}
... | yes prev = case r x v of λ { (no ¬a) → no (λ {(prev , this) → ¬a this}) ; (yes this) → yes (prev , this)}

¬all⇒∉ : {R : REL name V 0ℓ} {Γ : Context V} {x : name} {v : V} → All R Γ → ¬ R x v → ¬ (x ↦ v ∈ Γ)
¬all⇒∉ (all , this) not-R here = contradiction this not-R
¬all⇒∉ (all , this) not-R (there yes-elem) = ¬all⇒∉ all not-R yes-elem

-- Type witnessing a deleteBinding
infix 3  _-_↦_≡_
data _-_↦_≡_  {V : Set} :  Context V → name →  V → Context V → Set where
  deleteHere : (Γ : Context V) (x : name) (v : V)  → ((Γ , x ↦ v) - x ↦ v ≡ Γ)
  deleteThere : ∀ {y u} (Γ : Context V) (x : name) (v : V) (Γ' : Context V) → ¬ (y ≡ x  × v ≡ u) → Γ - x ↦ v ≡ Γ' → (Γ , y ↦ u) - x ↦ v ≡ (Γ' , y ↦ u)

deleteBinding-unique : ∀ {x V Γ Γ₁ Γ₂} {v : V} → Γ - x ↦ v ≡ Γ₁ → Γ - x ↦ v ≡ Γ₂ → Γ₁ ≡ Γ₂
deleteBinding-unique (deleteHere _ _ _) (deleteHere _ _ _) = refl
deleteBinding-unique (deleteHere _ _ _) (deleteThere _ _ _ _ noteq _) = contradiction (refl , refl) noteq
deleteBinding-unique (deleteThere _ _ _ _ noteq _) (deleteHere _ _ _) = contradiction (refl , refl) noteq
deleteBinding-unique (deleteThere _ _ _ _ _ sub₁) (deleteThere _ _ _ _ _ sub₂) = case deleteBinding-unique sub₁ sub₂ of λ {refl → refl}

deleteBinding :  {V : Set} {_≟ᵥ_ : DecidableEquality V} (Γ : Context V) (x : name) (v : V) → x ↦ v ∈ Γ → Σ[ Γ' ∈ Context V ] (Γ - x ↦ v ≡ Γ')
deleteBinding {V} {_≟ᵥ_} (Γ , y ↦ u) x v elem with y ≟ₙ x ×-dec u ≟ᵥ v
... | no ¬eq = let (Γ' , d') = deleteBinding {V} {_≟ᵥ_} Γ x v (case elem of λ { here → ⊥-elim (¬eq (refl , refl)) ; (there x) → x}) in (Γ' , y ↦ u) , deleteThere Γ x v Γ' (λ { (refl , refl) → ¬eq (refl , refl)}) d'
... | yes (refl , refl) = Γ , deleteHere Γ y u

_≟Γ_ : {V : Set} {_≟ᵥ_ : DecidableEquality V} → DecidableEquality (Context V)
∅  ≟Γ ∅ = yes refl
∅ ≟Γ (Ω , x ↦ x₁) = no (λ ())
(Γ , x ↦ x₁) ≟Γ ∅ = no (λ ())
_≟Γ_ {V} {_≟ᵥ_} (Γ , x ↦ v) (Ω , y ↦ u) with x ≟ₙ y ×-dec v ≟ᵥ u ×-dec _≟Γ_ {_≟ᵥ_ = _≟ᵥ_} Γ Ω
... | no neq = no (λ {refl → neq (refl , (refl , refl))})
... | yes (refl , (refl , refl)) = yes refl

Scope : Set
Scope = Context ⊤

-- todo reorganise

-- Equivalence without congruence requirements
infix 3 _⇔_
record _⇔_ (A : Set) (B : Set) : Set where
  field
    to : A → B
    from : B → A

record ScopeEquivalent (α : Scope) (β : Scope) : Set where
  field
    equiv : ∀ x → x ∈ α ⇔ x ∈ β

record ScopeRenamed (α : Scope) (β : Scope) (x : name) (y : name) : Set where
  field
    equivIfNotRenamed : ∀ a → a ≢ x → a ≢ y → a ∈ α ⇔ a ∈ β
    x∈α : x ∈ α
    x∉β : x ∉ β
    y∉α : y ∉ α
    y∈β : y ∈ β
    x≢y : x ≢ y

extendEquivalence : {α β : Scope} → (a : name) → ScopeEquivalent α β → ScopeEquivalent (α ⸴ a) (β ⸴ a)
extendEquivalence {α} {β} a record { equiv = equiv } = record { equiv = λ a' → record { to = to ; from = from } }
  where
    to : ∀ {a'} → a' ∈ (α ⸴ a) → a' ∈ (β ⸴ a)
    to here = here
    to {a'} (there a'∈α') = there (( _⇔_.to $ equiv a') a'∈α')
    
    from : ∀ {a'} → a' ∈ (β ⸴ a) → a' ∈ (α ⸴ a)
    from here = here
    from {a'} (there a'∈β') = there ((_⇔_.from $ equiv a') a'∈β')

extendRenaming : {α β : Scope} {x y : name} → (a : name) → a ≢ x → a ≢ y → ScopeRenamed α β x y → ScopeRenamed (α ⸴ a) (β ⸴ a) x y
extendRenaming {α} {β} {x} {y} a a≢x a≢y record { equivIfNotRenamed = equivIfNotRenamed ; x∈α = x∈α ; x∉β = x∉β ; y∉α = y∉α ; y∈β = y∈β; x≢y = x≢y }= record {
  equivIfNotRenamed = λ a' a'≢x a'≢y → record { to = to a'≢x a'≢y ; from = from a'≢x a'≢y  } ;
  x∈α = there x∈α ;
  x∉β = λ { here → contradiction refl a≢x ; (there elem) → contradiction elem x∉β };
  y∉α =  λ { here → contradiction refl a≢y ; (there elem) → contradiction elem y∉α } ;
  y∈β = there y∈β;
  x≢y = x≢y
  }
  where
    to : {a' : name} → a' ≢ x → a' ≢ y → a' ∈ (α ⸴ a) → a' ∈ (β ⸴ a)
    to a'≢x a'≢y here = here
    to {a'} a'≢x a'≢y (there a'∈α') = there ((_⇔_.to $ equivIfNotRenamed a' a'≢x a'≢y) a'∈α')

    from : {a' : name} → a' ≢ x → a' ≢ y → a' ∈ (β ⸴ a) → a' ∈ (α ⸴ a)
    from _ _ here = here
    from {a'} a'≢x a'≢y (there a'∈β') = there ((_⇔_.from $ equivIfNotRenamed a' a'≢x a'≢y) a'∈β')

mutualRenaming⇒equivalence : {α β δ : Scope} {x y : name} → ScopeRenamed α β x y → ScopeRenamed α δ x y → ScopeEquivalent β δ
mutualRenaming⇒equivalence {α} {β} {δ} {x} {y} record { equivIfNotRenamed = equivIfNotRenamed₁ ; x∈α = x∈α ; x∉β = x∉β ; y∉α = y∉α; y∈β = y∈β; x≢y = x≢y } record { equivIfNotRenamed = equivIfNotRenamed₂ ; x∈α = _ ; x∉β = x∉δ ; y∉α = _ ; y∈β = y∈δ }
  = record { equiv = λ a → record { to = to a ;from = from a }}
  where
    to : (a : name) → a ∈ β → a ∈ δ
    to a a∈β with a ≟ₙ x | a ≟ₙ y
    ... | yes refl | yes refl = contradiction refl x≢y
    ... | yes refl | no a≢y = contradiction a∈β x∉β
    ... | no a≢x | yes refl = y∈δ
    ... | no a≢x | no a≢y = _⇔_.to (equivIfNotRenamed₂ a a≢x a≢y) a∈α 
      where
        a∈α = _⇔_.from (equivIfNotRenamed₁ a a≢x a≢y) a∈β

    from : (a : name) → a ∈ δ → a ∈ β
    from a a∈δ with a ≟ₙ x | a ≟ₙ y
    ... | yes refl | yes refl = contradiction refl x≢y
    ... | yes refl | no a≢y = contradiction a∈δ x∉δ
    ... | no a≢x | yes refl = y∈β
    ... | no a≢x | no a≢y = _⇔_.to (equivIfNotRenamed₁ a a≢x a≢y) a∈α
      where
        a∈α = _⇔_.from (equivIfNotRenamed₂ a a≢x a≢y) a∈δ

--replaceInScope : (x y : name) (α : Scope) →  x ≢ y →  x ∈ α → Σ[ β ∈ Scope ] ScopeRenamed α β x y
--replaceInScope x y (α' ⸴ .x) x≢y here   = (α' ⸴ y) , (record
  --                                                     { equivIfNotRenamed = λ a a≢x a≢y → record { to = {!!} ; from = {!!} }
     --                                                  ; x∈α = here
        --                                               ; x∉β = {!!}
           --                                            ; y∉α = {!!}
              --                                         ; y∈β = here
                 --                                      ; x≢y = {!!}
                    --                                   })
--replaceInScope x y (α' ⸴ z) x≢y (there x∈α') = {!!}
