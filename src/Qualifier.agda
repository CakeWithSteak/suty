module Qualifier where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Level
open import Relation.Nullary
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Function.Base

data Qualifier : Set where
  un : Qualifier
  lin : Qualifier
  ord : Qualifier

data _⊑_ : Rel Qualifier 0ℓ where
  refl : {q : Qualifier} → q ⊑ q
  trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
  ord⊑lin : ord ⊑ lin
  lin⊑un : lin ⊑ un

private un-top : ∀ {q} → un ⊑ q → q ≡ un
un-top refl = ≡-refl
un-top (trans unb bq) with un-top unb
...      | ≡-refl = un-top bq

private ord-bottom : ∀ {q} → q  ⊑ ord → q ≡ ord
ord-bottom refl = ≡-refl
ord-bottom (trans ordb bq) with ord-bottom bq
...     | ≡-refl = ord-bottom ordb

infix 4 _≟q_
_≟q_ : DecidableEquality Qualifier 
x ≟q y with x | y
...   | un | un = true because of ≡-refl
...   | ord | ord = true because of ≡-refl
...   | lin | lin = true because of ≡-refl
...   | un | lin = false because of λ ()
...   | un | ord = false because of λ ()
...   | lin | un = false because of λ ()
...   | lin | ord = false because of λ ()
...   | ord | un = false because of λ ()
...   | ord | lin = false because of λ ()

_⊑?_ : (a b : Qualifier) → Dec (a ⊑ b)
un ⊑? un = true because of refl
un ⊑? lin = false because of λ x → case un-top x of λ ()
un ⊑? ord = false because of λ x → case un-top x of λ ()
lin ⊑? un = true because of lin⊑un
lin ⊑? lin = true because of refl
lin ⊑? ord = false because of f
  where
    f : ¬ (lin ⊑ ord)
    f (trans linb bord) = case (ord-bottom bord) of λ { ≡-refl → f linb }
ord ⊑? un = true because of (trans ord⊑lin lin⊑un)
ord ⊑? lin = true because of ord⊑lin
ord ⊑? ord = true because of refl

qualifierPreorder : Preorder 0ℓ 0ℓ 0ℓ
qualifierPreorder = record {
  Carrier = Qualifier ;
  _≈_ = _≡_ ;
  _≲_ = _⊑_ ;
  isPreorder = record {
    isEquivalence = record {
      refl = ≡-refl ;
      sym = ≡-sym ;
      trans = ≡-trans
      } ;
    reflexive = λ { ≡-refl → refl };
    trans = trans }
  }
 
