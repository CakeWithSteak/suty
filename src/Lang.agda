module Lang where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.String renaming (_≟_ to _≟String_)
open import Relation.Nullary.Decidable
open import Relation.Binary.Definitions
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (refl; _≡_;_≢_)

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

name = AbstractName

eraseAbstractName : AbstractName → String
eraseAbstractName n = AbstractName.humanReadable n

open import Lang.Type public
open import Lang.Term {name} {_≟ₙ_} public
open import Lang.Qualifier public
open import Lang.TypingContext {name} {_≟ₙ_} public
open import Lang.TypingRules  {name} {_≟ₙ_} public
