open import Data.String
open import Relation.Binary.Definitions

-- todo: eraseAbstractName should be an injection
module Raw.Erasure {abstractName : Set} {_≟ₙ'_ : DecidableEquality abstractName} (eraseAbstractName : abstractName → String) where

open import Raw.Base
open import Lang.Type
open import Lang.Term {abstractName} {_≟ₙ'_}
open import Lang.Qualifier
open import Scoping.Context
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Product
open import Data.Bool using (Bool)

module _ where
  private
    variable
      α : Scope
      q : Qualifier
      T U : Type
      T' U' : RawType
      notord : q ≢ ord
      x y z : abstractName
      t t₁ t₂ : Term α
      tinner₁ : Term (α ⸴ x)
      tinner₂ : Term ((α ⸴ x) ⸴ y)
      t' t₁' t₂' tinner' : RawTerm
      well-scoped-x : x ∈ α
      well-scoped-y : y ∈ α
      x-uniq : x ∉ α
      y-uniq : x ∉ α
      x-not-y : x ≢ y
      b : Bool

  data EraseType : Type → RawType → Set where
    ETyBool :  EraseType (` q `Bool) (RTyBool q)
    ETyUnit :  EraseType (` q `Unit) (RTyUnit q)
    ETyProduct : EraseType T T' → EraseType U U' → EraseType (` q ` T `× U)  (RTyProduct q T' U')
    ETyArrow : EraseType T T' → EraseType U U' → EraseType ((` q ` T ⇒ U) {notord})  (RTyArrow q T' U')

  data EraseTerm : Term α → RawTerm → Set where
    EVar : EraseTerm (` x # well-scoped-x) (RVar (eraseAbstractName x))
    EBool : EraseTerm {α} (` q ` b) (RBool q b)
    EUnit : EraseTerm {α} (` q `unit) (RUnit q)
    EIf : EraseTerm t t' → EraseTerm t₁ t₁' → EraseTerm t₂ t₂' → EraseTerm (`if t then t₁ else t₂) (RIf t' t₁' t₂')
    EPair : EraseTerm {α} ((` q < x , y >) {well-scoped-x} {well-scoped-y}) (RPair q (eraseAbstractName x) (eraseAbstractName y))
    ESplit : EraseTerm t t' → EraseTerm tinner₂ tinner' → EraseTerm ((`split t as x , y ⇒ tinner₂) {x-uniq} {y-uniq} {x-not-y}) (RSplit t' (eraseAbstractName x) (eraseAbstractName y) tinner')
    EAbs : EraseType T T' → EraseTerm t t' → EraseTerm ((` q ƛ x :: T ⇒ t) {notord} {x-uniq}) (RAbs q (eraseAbstractName x) T' t')
    EApp : EraseTerm {α} ((x · y) {well-scoped-x} {well-scoped-y}) (RApp (eraseAbstractName x) (eraseAbstractName y))
    ELet : EraseTerm t t' → EraseTerm tinner₁ tinner' → EraseTerm ((`let x := t ⇒ tinner₁) {x-uniq}) (RLet (eraseAbstractName x) t' tinner')
    EEat : EraseTerm t t' → EraseTerm (`eat t) (REat t')


eraseType : (T : Type) → Σ[ T' ∈ RawType ] EraseType T T'
eraseType ` q `Bool = RTyBool q , ETyBool
eraseType ` q `Unit = RTyUnit q , ETyUnit
eraseType (` q ` T `× U) with eraseType T | eraseType U
... | (T' , T'-proof) | (U' , U'-proof) = (RTyProduct q T' U') , ETyProduct T'-proof U'-proof
eraseType (` q ` T ⇒ U) with eraseType T | eraseType U
... | (T' , T'-proof) | (U' , U'-proof) = RTyArrow q T' U' , ETyArrow T'-proof U'-proof

eraseTerm : ∀ {α} → (t : Term α) → Σ[ t' ∈ RawTerm ] EraseTerm t t'
eraseTerm (` x # x₁) = (RVar (eraseAbstractName x)) , EVar
eraseTerm (` q ` b) = (RBool q b) , EBool
eraseTerm ` q `unit = (RUnit q) , EUnit
eraseTerm (`if t then t₁ else t₂) with eraseTerm t | eraseTerm t₁ | eraseTerm t₂
... | (t' , p) | (t₁' , p₁) | (t₂' , p₂) = (RIf t' t₁' t₂') , EIf p p₁ p₂
eraseTerm ` q < x , y > = RPair q (eraseAbstractName x) (eraseAbstractName y) , EPair
eraseTerm (`split t as x , y ⇒ t₁) with eraseTerm t | eraseTerm t₁
... | (t' , p) | (t₁' , p₁) = RSplit t' (eraseAbstractName x) (eraseAbstractName y) t₁' , ESplit p p₁ 
eraseTerm (` q ƛ x :: T ⇒ t) with eraseType T | eraseTerm t
... | (T' , p-T) | (t' , p-t) = (RAbs q (eraseAbstractName x) T' t') , (EAbs p-T p-t)
eraseTerm (x · y) = (RApp (eraseAbstractName x) (eraseAbstractName y)) , EApp
eraseTerm (`let x := t ⇒ t₁) with eraseTerm t | eraseTerm t₁
... | (t' , p) | (t₁' , p₁) = RLet (eraseAbstractName x) t' t₁' , ELet p p₁
eraseTerm (`eat t) with eraseTerm t
... | (t' , p) = REat t' , EEat p
