module Lang where

open import Data.String renaming (_≟_ to _≟ₛ_)
name = String
_≟ₙ_ = _≟ₛ_

open import Lang.Type public
open import Lang.Term {name} {_≟ₙ_} public
open import Lang.Qualifier public
open import Lang.TypingContext {name} {_≟ₙ_} public
open import Lang.TypingRules  {name} {_≟ₙ_} public
