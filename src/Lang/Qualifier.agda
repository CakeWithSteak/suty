module Lang.Qualifier where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Level
open import Relation.Nullary
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Function.Base
open import Data.String

data Qualifier : Set where
  un : Qualifier
  aff : Qualifier
  lin : Qualifier
  ord : Qualifier

data _⊑_ : Rel Qualifier 0ℓ where
  un⊑un : un ⊑ un
  lin⊑lin : lin ⊑ lin
  aff⊑aff : aff ⊑ aff
  ord⊑ord : ord ⊑ ord
  aff⊑un : aff ⊑ un
  lin⊑un : lin ⊑ un
  ord⊑un : ord ⊑ un
  lin⊑aff : lin ⊑ aff
  ord⊑aff : ord ⊑ aff
  ord⊑lin : ord ⊑ lin

infix 4 _≟q_
_≟q_ : DecidableEquality Qualifier 
un ≟q un = yes ≡-refl
un ≟q aff = no (λ ())
un ≟q lin = no (λ ())
un ≟q ord = no (λ ())
aff ≟q un = no (λ ())
aff ≟q aff = yes ≡-refl
aff ≟q lin = no (λ ())
aff ≟q ord = no (λ ())
lin ≟q un = no (λ ())
lin ≟q aff = no (λ ())
lin ≟q lin = yes ≡-refl
lin ≟q ord = no (λ ())
ord ≟q un = no (λ ())
ord ≟q aff = no (λ ())
ord ≟q lin = no (λ ())
ord ≟q ord = yes ≡-refl

_⊑?_ : (a b : Qualifier) → Dec (a ⊑ b)
un ⊑? un = yes un⊑un
un ⊑? aff = no (λ ())
un ⊑? lin = no (λ ())
un ⊑? ord = no (λ ())
aff ⊑? un = yes aff⊑un
aff ⊑? aff = yes aff⊑aff
aff ⊑? lin = no (λ ())
aff ⊑? ord = no (λ ())
lin ⊑? un = yes lin⊑un
lin ⊑? aff = yes lin⊑aff
lin ⊑? lin = yes lin⊑lin
lin ⊑? ord = no (λ ())
ord ⊑? un = yes ord⊑un
ord ⊑? aff = yes ord⊑aff
ord ⊑? lin = yes ord⊑lin
ord ⊑? ord = yes ord⊑ord
 
showQualifier : Qualifier → String
showQualifier un = "un"
showQualifier lin = "lin"
showQualifier ord = "ord"
showQualifier aff = "aff"
