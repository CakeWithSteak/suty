module Raw.Base where

open import Qualifier
open import Data.Bool
open import Data.String renaming (_≟_ to _≟ₛ_)
open import Data.Bool.Show renaming (show to showBool)
open import Function using (_$_)

name = String
_≟ₙ_ = _≟ₛ_

data RawType : Set where
  RTyBool : Qualifier → RawType
  RTyUnit : Qualifier → RawType
  RTyProduct : Qualifier → RawType → RawType → RawType
  RTyArrow : Qualifier → RawType → RawType → RawType

data RawTerm : Set where
  RVar : name → RawTerm
  RBool : Qualifier → Bool → RawTerm
  RUnit : Qualifier → RawTerm
  RIf : RawTerm → RawTerm → RawTerm → RawTerm
  RPair : Qualifier → name → name → RawTerm
  RSplit : RawTerm → name → name → RawTerm → RawTerm
  RAbs : Qualifier → name → RawType → RawTerm → RawTerm
  RApp : name → name → RawTerm
  RLet : name → RawTerm → RawTerm → RawTerm
  REat : RawTerm → RawTerm

showRawType : RawType → String
showRawType (RTyBool q) = "` " ++ showQualifier q ++ " `Bool"
showRawType (RTyUnit q) =  "` " ++ showQualifier q ++ " `Unit"
showRawType (RTyProduct q T U) = "` " ++ showQualifier q ++ " ` " ++ showRawType T ++ " `× " ++ showRawType U
showRawType (RTyArrow q T U) = "` " ++ showQualifier q ++ " ` " ++ showRawType T ++ " ⇒ " ++ showRawType U

showRawTerm : RawTerm → String
showRawTerm (RVar x) = "` \"" ++ x ++ "\""
showRawTerm (RBool q b) = "` " ++ showQualifier q ++ " ` " ++ showBool b
showRawTerm (RUnit q) = "` " ++ showQualifier q ++ " `unit"
showRawTerm (RIf t t₁ t₂) = parens $ "`if " ++ showRawTerm t ++ " then " ++ showRawTerm t₁ ++ " else " ++ showRawTerm t₂
showRawTerm (RPair q x y) = parens $ "` " ++ showQualifier q ++ " < " ++ x ++ " , " ++ y ++ " >"
showRawTerm (RSplit t x y t₁) = parens $ "`split " ++ showRawTerm t ++ "as " ++ x ++ " , " ++ y ++ " ⇒ " ++ showRawTerm t₁ ++ ""
showRawTerm (RAbs q x T t) =  parens $ "` " ++ showQualifier q ++ " ƛ \"" ++ x ++ "\" :: " ++ showRawType  T ++ " ⇒ " ++ showRawTerm t
showRawTerm (RApp x y) = parens $ x ++ " · " ++ y
showRawTerm (RLet x t t₁) = parens $ "`let \"" ++ x ++ "\" := " ++ showRawTerm t ++ " ⇒ " ++ showRawTerm t₁
showRawTerm (REat t) = parens $ "`eat " ++ showRawTerm t

module Syntax where
 `_  : name → RawTerm
 `_ = RVar
 `_`_  :  Qualifier → Bool → RawTerm
 `_`_ = RBool
 `_`unit : Qualifier → RawTerm
 `_`unit = RUnit
 `if_then_else_ : RawTerm → RawTerm → RawTerm → RawTerm
 `if_then_else_ = RIf
 `_<_,_> : Qualifier → (x : name) → (y : name) → RawTerm
 `_<_,_> = RPair
 `split_as_,_⇒_ : RawTerm → name → name → RawTerm → RawTerm
 `split_as_,_⇒_ = RSplit
 `_ƛ_::_⇒_ : Qualifier → name → RawType → RawTerm → RawTerm
 `_ƛ_::_⇒_ = RAbs
 _·_ : name → name  → RawTerm
 _·_ = RApp
 `let_:=_⇒_ : name → RawTerm → RawTerm → RawTerm
 `let_:=_⇒_ = RLet
 `eat_ : RawTerm → RawTerm
 `eat_ = REat

 `_`Bool : Qualifier → RawType
 `_`Bool = RTyBool
 `_`Unit : Qualifier → RawType
 `_`Unit = RTyUnit
 `_`_`×_ : Qualifier → RawType → RawType → RawType
 `_`_`×_ = RTyProduct
 `_`_⇒_ : Qualifier → RawType → RawType → RawType
 `_`_⇒_ = RTyArrow

 infix 5 `_ƛ_::_⇒_
 infixl 7 _·_
 infix 9 `_
 infix 9 `_`_
 infix 9 `_`unit
 infix 8 `eat_
 infix 7 `_<_,_>
 infix 4 `split_as_,_⇒_
 infix 4 `let_:=_⇒_
 infix 3 `if_then_else_
