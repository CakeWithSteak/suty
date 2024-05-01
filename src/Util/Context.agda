open import Relation.Binary.Bundles
open import Level

module Util.Context {Key : DecSetoid 0ℓ 0ℓ} where

open DecSetoid Key renaming (Carrier to name) public
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (⌊_⌋; _×-dec_; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL)
open import Data.Bool using (true; false; if_then_else_)

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

data All (R : REL name V 0ℓ) : Pred (Context V) 0ℓ where
  ∅ : All R ∅
  _,_ : ∀ {x v Γ} (rest : All R Γ) (this : R x v) → All R (Γ , x ↦ v)

deleteBinding : Context V → name → Context V
deleteBinding ∅ x = ∅
deleteBinding (Γ , y ↦ v) x with x ≟ y
... | no _  = (deleteBinding Γ x) , y ↦ v
... | yes _ = Γ

deleteBinding-preserves-all : ∀ {Γ x} {R : REL name V 0ℓ} → All R Γ  → All R (deleteBinding Γ x)
deleteBinding-preserves-all {Γ = ∅} {x} {R} ∅ = ∅
deleteBinding-preserves-all {Γ = Γ₀ , y ↦ w} {x} {R} (before , this) with x ≟ y
... | no _ = deleteBinding-preserves-all before , this
... | yes a = before

Scope : Set
Scope = Context ⊤
