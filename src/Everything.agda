module Everything where

open import Data.String renaming (_≟_ to _≟ₛ_)

name = String

open import Term {name = name} {_≟ₙ_ = _≟ₛ_}
open import TypeChecker {name = name} {_≟ₙ_ = _≟ₛ_}
open import Type
open import Util.Context {name = name} {_≟ₙ_ = _≟ₛ_}
open import Qualifier
open import Relation.Binary.PropositionalEquality

-- imported for nicer printing
open import Data.Product
open import TypingRules
open import TypingContext
open import Relation.Nullary.Decidable
open import Level
open import Relation.Binary using (REL)
open import Data.Bool using (true; false)


--private

un-id : Term ∅
un-id = (` un ƛ "x" :: (` un `Bool) ⇒ (` "x" # here)) {λ ()}

ty-un-id : TypecheckResult ∅ un-id
ty-un-id = typeOf ∅ un-id

lin-id : Term ∅
lin-id = (` lin ƛ "x" :: (` lin `Bool) ⇒ (` "x" # here)) {λ ()}

ty-lin-id : TypecheckResult ∅ lin-id
ty-lin-id = typeOf ∅ lin-id

bad-un-id : Term (∅ ⸴ "y")
bad-un-id = (` un ƛ "x" :: (` un `Bool) ⇒ (` "x" # here)) {λ ()}

ty-bad-un-id : TypecheckResult (∅ , "y" ↦ ` lin `Bool) bad-un-id
ty-bad-un-id = typeOf (∅ , "y" ↦ ` lin `Bool) bad-un-id

t-split : Term ∅
t-split = `let "x" := ` un `unit ⇒
  (`let "y" := ` lin ` false ⇒
    (`let "p" := ` lin < "x" , "y" >  {there here} {here} ⇒
    (`split ` "p" # here as "a" , "b" ⇒ (`if (` "b" # here) then `eat (` "a" # there here) else ` un `unit)) ))

ty-split : TypecheckResult ∅ t-split
ty-split = typeOf ∅ t-split


t-ord-split : Term ∅
t-ord-split = `let "x" := ` ord `unit ⇒
  (`let "y" := ` ord ` false ⇒
    (`let "p" := ` ord < "x" , "y" >  {there here} {here} ⇒
    (`split ` "p" # here as "a" , "b" ⇒ (`if (` "b" # here) then `eat (` "a" # there here) else `eat (` "a" # there here))) ))

ty-ord-split : TypecheckResult ∅ t-ord-split
ty-ord-split = typeOf ∅ t-ord-split
