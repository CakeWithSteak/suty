open import Relation.Binary.Definitions
module Lang.TypingRules {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Scoping.Context {name} {_≟ₙ_}
open import Lang.Type
open import Lang.Term {name} {_≟ₙ_}
open import Lang.TypingContext {name} {_≟ₙ_}
open import Lang.Qualifier hiding (trans)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Relation.Nullary.Negation using (contradiction; ¬_)
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Bool using (Bool)
open import Function using (_∋_; case_of_; _$_)

private
  variable
    α : Scope
    x y : name
    q : Qualifier
    t t₁ t₂ t₃ : Term α
    T T₁ T₂ : Type
    Γ Γ₂ Γ₃ Γ₄ : TypingContext

infix 2 _⊢_::_,_
data _⊢_::_,_ (Γᵢ : TypingContext) : (t : Term α) (ty : Type) (Γₒ : TypingContext) → Set where
  TUVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) →  (qualifierOf T ≡ un) → Γᵢ ⊢ (` x # p) :: T , Γᵢ
  TLVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ lin) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ
  TOVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ ord) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ

  TBool :  {b : Bool} → Γᵢ ⊢ (Term α ∋ ` q ` b ) :: ` q `Bool , Γᵢ
  TUnit : Γᵢ ⊢ (Term α ∋ ` q `unit) :: ` q `Unit , Γᵢ
  TIf :                 Γᵢ ⊢ t₁ :: ` q `Bool , Γ₂
                       → Γ₂ ⊢ t₂ :: T , Γ₃
                       → Γ₂ ⊢ t₃ :: T , Γ₃
                       ------------------------------------------------------------------------
                       → Γᵢ ⊢ `if t₁ then t₂ else t₃  :: T , Γ₃

  TEat : Γᵢ ⊢ t :: ` q `Unit , Γ₂
              ------------------------------------------------------------------------
           → Γᵢ ⊢ `eat t :: ` un `Unit , Γ₂

  TPair : (p₁ : x ∈ α) → (p₂ : y ∈ α)
            → Γᵢ ⊢ ` y # p₂ :: T₂ , Γ₂ -- the context is first passed into t₂ because pairs of ordered variables must conserve the order of the stack. For other variables the order of evaluation (in pairs) doesn't matter, so this is safe.
            → Γ₂ ⊢ ` x # p₁ :: T₁ , Γ₃
            → q ⟨ T₁ ⟩
            → q ⟨ T₂ ⟩
            ------------------------------------------------------------------------
            → Γᵢ ⊢ ` q < x , y > {p₁} {p₂} :: ` q ` T₁ `× T₂ , Γ₃

  TSplit : (p₁ : x ∉ α) → (p₂ : y ∉ α)
              →  Γᵢ ⊢ t₁ :: ` q ` T₁ `× T₂ , Γ₂
              → ((Γ₂ , x ↦ T₁) , y ↦ T₂) ⊢ t₂ :: T , Γ₃
              → Γ₃ ÷ (∅ , x ↦ T₁) , y ↦ T₂ ≡ Γ₄
              ------------------------------------------------------------------------
              → Γᵢ ⊢ (`split t₁ as x , y ⇒ t₂) {p₁} {p₂} :: T , Γ₄

  TLet : (p : x ∉ α)
           → Γᵢ ⊢ t₁ :: T₁ , Γ₂
           → Γ₂ , x ↦ T₁ ⊢ t₂ :: T₂ , Γ₃
           → Γ₃ ÷ ∅ , x ↦ T₁ ≡ Γ₄
           ------------------------------------------------------------------------
           → Γᵢ ⊢ (`let x := t₁ ⇒ t₂) {p} :: T₂ , Γ₄

  TAbs : (p-uniq : x ∉ α)
            → (p-notord : q ≢ ord)
            → q ⟨⟨ Γᵢ ⟩⟩
            → Γᵢ , x ↦ T₁ ⊢ t :: T₂ , Γ₂
            → Γ₂ ÷ (∅ , x ↦ T₁) ≡ Γ₃
            ------------------------------------------------------------------------
            → Γᵢ ⊢ (` q ƛ x :: T₁ ⇒ t) {p-notord} {p-uniq} :: (` q ` T₁ ⇒ T₂) {p-notord} , Γ₃

  TApp : (p₁ : x ∈ α) (p₂ : y ∈ α) (pq : q ≢ ord)
             → Γᵢ ⊢ ` x # p₁ :: (` q ` T₁ ⇒ T₂) {pq} , Γ₂
             → Γ₂ ⊢ ` y # p₂ :: T₁ , Γ₃
             ------------------------------------------------------------------------
             → Γᵢ ⊢ (x · y) {p₁} {p₂} :: T₂ , Γ₃

infix 2 _⊢_::⊥
_⊢_::⊥ : TypingContext → Term α → Set
_⊢_::⊥ Γ t =  ¬ Σ (Type × TypingContext) (λ (T , Γ') → (Γ ⊢ t :: T , Γ'))

typing-unique : ∀ {Γ'₁ Γ'₂} → (Γ ⊢ t :: T₁ , Γ'₁)→ Γ ⊢ t :: T₂ , Γ'₂ → T₁ ≡ T₂ × Γ'₁ ≡ Γ'₂
typing-unique (TUVar p elem₁ _) (TUVar .p  elem₂ _) with ∈*-unique elem₁ elem₂
... | refl = refl , refl
typing-unique (TUVar p elem is-un) (TLVar .p elem₁ is-lin  _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-un) is-lin of λ ()}
typing-unique (TUVar p elem is-un) (TOVar .p elem₁ is-ord _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-un) is-ord of λ ()}
typing-unique a@(TLVar _ _ _ _ _) b@(TUVar _ _ _) = Data.Product.map sym sym $ typing-unique b a
typing-unique (TLVar p elem _ _ Γ'₁-proof) (TLVar .p elem₁ _ _ Γ'₂-proof) =
  case ∈*-unique elem elem₁ of λ {refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof}
typing-unique (TLVar p elem is-lin _ _) (TOVar .p elem₁ is-ord _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-lin) is-ord of λ ()}
typing-unique a@(TOVar _ _ _ _ _) b@(TUVar _ _ _) = Data.Product.map sym sym $ typing-unique b a
typing-unique a@(TOVar _ _ _ _ _) b@(TLVar _ _ _ _ _) = Data.Product.map sym sym $ typing-unique b a
typing-unique (TOVar p elem _ _ Γ'₁-proof) (TOVar .p elem₁ _ _ Γ'₂-proof) =
  case ∈*-unique elem elem₁ of λ {refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof}
typing-unique TBool TBool = refl , refl
typing-unique TUnit TUnit = refl , refl
typing-unique (TIf cond-bool₁ left-T₁ right-T₁) (TIf cond-bool₂ left-T₂ right-T₂) with typing-unique cond-bool₁ cond-bool₂
... | (refl , refl) = typing-unique left-T₁ left-T₂
typing-unique (TEat a) (TEat b) = refl , proj₂ (typing-unique a b)
typing-unique (TPair _ _ left₁ right₁ _ _) (TPair _ _ left₂ right₂ _ _) with typing-unique left₁ left₂
... | (refl , refl) with typing-unique right₁ right₂
...   | (refl , refl) = refl , refl 
typing-unique (TSplit _ _ arg₁ body₁ div₁) (TSplit _ _ arg₂ body₂ div₂) with typing-unique arg₁ arg₂
... | (refl , refl) with typing-unique body₁ body₂
...   | (refl , refl) with ÷-unique div₁ div₂
...     | refl = refl , refl
typing-unique (TLet _ arg₁ body₁ div₁) (TLet _ arg₂ body₂ div₂) with typing-unique arg₁ arg₂
... | (refl , refl) with typing-unique body₁ body₂
...   | (refl , refl) with ÷-unique div₁ div₂
...     | refl = refl , refl
typing-unique (TAbs _ _ _ body₁ div₁) (TAbs _ _ _ body₂ div₂) with typing-unique body₁ body₂
... | (refl , refl) with ÷-unique div₁ div₂
...   | refl = refl , refl
typing-unique (TApp _ _ _ fun₁ arg₁) (TApp _ _ _ fun₂ arg₂) with typing-unique fun₁ fun₂
... | (refl , refl) with typing-unique arg₁ arg₂
...   | (refl , refl) = refl , refl

typing-contradiction : ∀ {a} {Whatever : Set a} → T₁ ≢ T₂ → Γ ⊢ t :: T₁ , Γ₂ → Γ ⊢ t :: T₂ , Γ₃ → Whatever
typing-contradiction neq a b = contradiction (proj₁ (typing-unique a b)) neq
