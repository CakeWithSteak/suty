open import Relation.Binary.Definitions

module Lang.Term {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Scoping.Context {name} {_≟ₙ_}
open import Data.Bool using (Bool)
open import Lang.Qualifier
open import Lang.Type
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Term (α : Scope) : Set where
  `_#_ : (x : name) → x ∈ α → Term α
  `_`_ :  Qualifier → Bool → Term α
  `_`unit : Qualifier → Term α
  `if_then_else_ : Term α → Term α → Term α → Term α
  `_<_,_> : Qualifier → (x : name) → (y : name) → {x ∈ α} → {y ∈ α} → Term α
  `split_as_,_⇒_ : Term α → (x : name) → (y : name) → Term (α ⸴ x ⸴ y) → {x ∉ α}  → {y ∉ α} → Term α
  `_ƛ_::_⇒_ : (q : Qualifier) → (x : name) → Type → Term (α ⸴ x) → {q ≢ ord} → {x ∉ α} → Term α
  _·_ : (x : name) → (y : name) → {x ∈ α} → {y ∈ α} → Term α
  `let_:=_⇒_ : (x : name) → Term α → Term (α ⸴ x) → {x ∉ α} → Term α
  `eat_ : Term α → Term α

infix 5 `_ƛ_::_⇒_
infixl 7 _·_
infix 9 `_#_
infix 9 `_`_
infix 9 `_`unit
infix 8 `eat_
infix 7 `_<_,_>
infix 4 `split_as_,_⇒_
infix 4 `let_:=_⇒_
infix 3 `if_then_else_
