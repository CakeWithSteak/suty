{-# OPTIONS --guardedness #-}

module Everything where

open import Lang hiding (`_#_; `_`_; `_`unit; `if_then_else_; `_<_,_>; `split_as_,_⇒_; `_ƛ_::_⇒_; _·_; `let_:=_⇒_; `eat_; `_`Bool; `_`Unit; `_`_`×_; `_`_⇒_)
open import TypeChecker
open import Scoping.ScopeChecker
open import Scoping.Context {AbstractName} {_≟ₙ_}
open import Raw.Base hiding (_≟ₙ_)
open Raw.Base.Syntax
open import Raw.Erasure {AbstractName} {_≟ₙ_} (eraseAbstractName)

open import Data.Unit.Polymorphic
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (<_,_>)
open import Relation.Nullary.Decidable
open import Level
open import Relation.Binary using (REL)
open import Data.Bool using (true; false)
open import IO
open import Data.String hiding (intersperse)
open import Data.List hiding (_++_)
open import Function using (_$_)

data ExampleResult : Set where
  ScopeCheckFailed : String → ExampleResult
  IllTyped : Term ∅ → ExampleResult
  WellTyped : Term ∅ → Type → ExampleResult

runExample : RawTerm → ExampleResult
runExample t with scopeCheck t
... | bad err = ScopeCheckFailed err
... | good (t' , _) with typeOf ∅ t'
... | yes ((T , _) , _) = WellTyped t' T
... | no _ = IllTyped t'


runAndShowExample : RawTerm → IO {0ℓ} ⊤
runAndShowExample t with runExample t
... | ScopeCheckFailed err = putStrLn (showRawTerm t ++ "\nIll scoped: " ++ err)
... | IllTyped _ = putStrLn (showRawTerm t ++ "\nIll typed.")
... | WellTyped _ T = putStrLn (showRawTerm t ++ "\n:: " ++ showRawType (proj₁ (eraseType T)))
  
main : Main
main = run (List.sequence′ $ intersperse (putStrLn "==========================") (Data.List.map runAndShowExample examples))
  where
    x = "x"
    y = "y"
    z = "z"
    p = "p"
    a = "a"
    b = "b"
    examples =
      (` un ƛ x :: (` un `Bool) ⇒ ` x)
      ∷ (` lin ƛ x :: (` lin `Bool) ⇒ ` x)
      ∷ (` ord ƛ x :: (` un `Unit) ⇒ ` un `unit ) -- scope check fail: ord function invalid
      ∷ (` un ƛ x :: (` un `Bool) ⇒ ` y) -- unbound variable
      ∷ (` un ƛ x :: (` un ` (` un `Bool) `× (` un `Bool)) ⇒ (`split ` x as y , z ⇒ (`if ` y then ` z else ` un ` false))) -- good
      ∷ (` un ƛ x :: (` un ` (` un `Bool) `× (` un `Bool)) ⇒ (`split ` x as x , z ⇒ (`if ` x then ` z else ` un ` false))) -- good, identical to above (shadowing)
      ∷ (`let x := ` un `unit ⇒
              (`let y := ` lin ` false ⇒
                (`let p := ` lin < x , y >  ⇒
                  (`split ` p as a , b ⇒ (`if (` b) then `eat (` a) else ` un `unit)) ))) -- good
      ∷ (`let x := ` ord `unit ⇒
              (`let y := ` ord ` false ⇒
                (`let p := ` ord < x , y >  ⇒
                  (`split ` p as a , b ⇒ (`if (` b) then `eat (` a) else ` ord `unit)) ))) -- bad: "a" is unused in the "else" case
       ∷ (`let x := ` ord `unit ⇒
              (`let y := ` ord ` false ⇒
                (`let p := ` ord < x , y >  ⇒
                  (`split ` p as a , b ⇒ (`if (` b) then `eat (` a) else `eat (` a))) ))) -- good
       ∷ (`let x := ` ord `unit ⇒
              (`let y := ` ord ` false ⇒
                (`let p := ` ord < y , x >  ⇒
                  (`split ` p as a , b ⇒ (`if (` b) then `eat (` a) else `eat (` a))) ))) -- bad: x and y used out of order
      ∷ (`let x := ` aff `unit ⇒
               (`eat ` x)) -- good: affine var used once
      ∷ (`let x := ` aff `unit ⇒
               (` un `unit)) -- good: affine var unused
       ∷ (`let x := ` aff `unit ⇒
               (` aff < x , x >)) -- bad: affine var used twice
        ∷ (`let x := ` aff `unit ⇒
               (`if (` un ` true) then `eat ` x else ` un `unit)) -- good: affine var used once in one control path and zero times in another
        ∷ (`let x := ` rel `unit ⇒
               (`if (` un ` true) then `eat ` x else `eat ` x))  -- good: relevant var used once in each control path
         ∷ (`let x := ` rel `unit ⇒
               (`if (` un ` true) then `eat ` x else ` un `unit))  -- bad: relevant var used in only one control path
         ∷ (`let x := ` rel `unit ⇒
               (`if (` un ` true) then ` un `unit  else `eat ` x)) -- bad: relevant var used in only one control path
          ∷ (`let x := ` rel `unit ⇒
               (`if (` un ` true) then ` un `unit  else ` un `unit)) -- bad: relevant var used in neither control path
          ∷ (`let x := ` rel `unit ⇒
               (`if (`let y := `eat ` x ⇒ ` un ` true) then ` un `unit  else ` un `unit)) -- good: relevant var used in condition
          ∷ (`let x := ` rel `unit ⇒
               (`if (` un ` true) then ` un `unit  else ` un `unit)) -- bad: relevant var never used
      ∷ []
