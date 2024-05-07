open import Relation.Binary.Definitions

module Raw.Erasure where

open import Raw.Base
open import Lang.Type
open import Lang.Term {name} {_≟ₙ_}
open import Lang.Qualifier
open import Scoping.Context
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Product
open import Data.Bool using (Bool)

module _ where
  private
    variable
      α β : Scope
      q : Qualifier
      T U : Type
      T' U' : RawType
      notord : q ≢ ord
      t t₁ t₂ : Term α
      tinner : Term β
      t' t₁' t₂' tinner' : RawTerm
      x y z : name
      well-scoped-x : x ∈ α
      well-scoped-y : y ∈ α
      b : Bool

  data EraseType : Type → RawType → Set where
    ETyBool :  EraseType (` q `Bool) (RTyBool q)
    ETyUnit :  EraseType (` q `Unit) (RTyUnit q)
    ETyProduct : EraseType T T' → EraseType U U' → EraseType (` q ` T `× U)  (RTyProduct q T' U')
    ETyArrow : EraseType T T' → EraseType U U' → EraseType ((` q ` T ⇒ U) {notord})  (RTyArrow q T' U')

  data EraseTerm : Term α → RawTerm → Set where
    EVar : EraseTerm (` x # well-scoped-x) (RVar x)
    EBool : EraseTerm {α} (` q ` b) (RBool q b)
    EUnit : EraseTerm {α} (` q `unit) (RUnit q)
    EIf : EraseTerm t t' → EraseTerm t₁ t₁' → EraseTerm t₂ t₂' → EraseTerm (`if t then t₁ else t₂) (RIf t' t₁' t₂')
    EPair : EraseTerm {α} ((` q < x , y >) {well-scoped-x} {well-scoped-y}) (RPair q x y)
    ESplit : EraseTerm t t' → EraseTerm tinner tinner' → EraseTerm (`split t as x , y ⇒ tinner) (RSplit t' x y tinner')
    EAbs : EraseType T T' → EraseTerm t t' → EraseTerm ((` q ƛ x :: T ⇒ t) {notord}) (RAbs q x T' t')
    EApp : EraseTerm {α} ((x · y) {well-scoped-x} {well-scoped-y}) (RApp x y)
    ELet : EraseTerm t t' → EraseTerm tinner tinner' → EraseTerm (`let x := t ⇒ tinner) (RLet x t' tinner')
    EEat : EraseTerm t t' → EraseTerm (`eat t) (REat t')


eraseType : (T : Type) → Σ[ T' ∈ RawType ] EraseType T T'
eraseType ` q `Bool = RTyBool q , ETyBool
eraseType ` q `Unit = RTyUnit q , ETyUnit
eraseType (` q ` T `× U) with eraseType T | eraseType U
... | (T' , T'-proof) | (U' , U'-proof) = (RTyProduct q T' U') , ETyProduct T'-proof U'-proof
eraseType (` q ` T ⇒ U) with eraseType T | eraseType U
... | (T' , T'-proof) | (U' , U'-proof) = RTyArrow q T' U' , ETyArrow T'-proof U'-proof

eraseTerm : ∀ {α} → (t : Term α) → Σ[ t' ∈ RawTerm ] EraseTerm t t'
eraseTerm (` x # x₁) = (RVar x) , EVar
eraseTerm (` q ` b) = (RBool q b) , EBool
eraseTerm ` q `unit = (RUnit q) , EUnit
eraseTerm (`if t then t₁ else t₂) with eraseTerm t | eraseTerm t₁ | eraseTerm t₂
... | (t' , p) | (t₁' , p₁) | (t₂' , p₂) = (RIf t' t₁' t₂') , EIf p p₁ p₂
eraseTerm ` q < x , y > = RPair q x y , EPair
eraseTerm (`split t as x , y ⇒ t₁) with eraseTerm t | eraseTerm t₁
... | (t' , p) | (t₁' , p₁) = RSplit t' x y t₁' , ESplit p p₁ 
eraseTerm (` q ƛ x :: T ⇒ t) with eraseType T | eraseTerm t
... | (T' , p-T) | (t' , p-t) = (RAbs q x T' t') , (EAbs p-T p-t)
eraseTerm (x · y) = (RApp x y) , EApp
eraseTerm (`let x := t ⇒ t₁) with eraseTerm t | eraseTerm t₁
... | (t' , p) | (t₁' , p₁) = RLet x t' t₁' , ELet p p₁
eraseTerm (`eat t) with eraseTerm t
... | (t' , p) = REat t' , EEat p
