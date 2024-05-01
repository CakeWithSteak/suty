module Qualifier where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Level

data Qualifier : Set where
  un : Qualifier
  lin : Qualifier
  ord : Qualifier

data _⊑_ : Rel Qualifier 0ℓ where
  refl : {q : Qualifier} → q ⊑ q
  trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
  ord⊑lin : ord ⊑ lin
  lin⊑un : lin ⊑ un

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
 
