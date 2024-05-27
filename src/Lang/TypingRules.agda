open import Relation.Binary.Definitions
module Lang.TypingRules {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Scoping.Context {name} {_≟ₙ_}
open import Lang.Type
open import Lang.Term {name} {_≟ₙ_}
open import Lang.TypingContext {name} {_≟ₙ_}
open import Lang.Qualifier
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Relation.Nullary.Negation using (contradiction; ¬_)
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Bool using (Bool)
open import Function using (_∋_; case_of_; _$_)

private
  variable
    α β : Scope
    x y : name
    q : Qualifier
    t t₁ t₂ t₃ : Term α
    T T₁ T₂ : Type
    Γ Γ₂ Γ₃ Γ₄ Γ₅ : TypingContext
    Ω Ω₁ Ω₂ Ω₃ Ω₄ : Scope

infix 2 _⊢_::_,_⨾_
data _⊢_::_,_⨾_ (Γᵢ : TypingContext) : (t : Term α) (ty : Type) (Γₒ : TypingContext) (Ω : Scope) → Set where
  TUVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) →  (qualifierOf T ≡ un) → Γᵢ ⊢ (` x # p) :: T , Γᵢ ⨾ ∅
  TLVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ lin) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ ⨾ ∅
  TOVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ ord) → (Γₒ : TypingContext) → Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ ⨾ ∅
  TAVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ aff) → (Γₒ : TypingContext) →  Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ ⨾ ∅
  TRVar : (p : x ∈ α) → (elem : x ↦ T ∈* Γᵢ) → (qualifierOf T ≡ rel) → (Γₒ : TypingContext) →  Γᵢ - x ↦ T ≡ Γₒ → Γᵢ ⊢ (` x # p) :: T , Γₒ ⨾ (∅ ⸴ x)

  TBool :  {b : Bool} → Γᵢ ⊢ (Term α ∋ ` q ` b ) :: ` q `Bool , Γᵢ ⨾ ∅
  TUnit : Γᵢ ⊢ (Term α ∋ ` q `unit) :: ` q `Unit , Γᵢ ⨾ ∅
  TIf :                 Γᵢ ⊢ t₁ :: ` q `Bool , Γ₂ ⨾ Ω₁
                       → Γ₂ ⊢ t₂ :: T , Γ₃ ⨾ Ω₂
                       → Γ₂ ⊢ t₃ :: T , Γ₄ ⨾ Ω₃
                       → Γ₃ ∩ₐ Γ₄ ≡ Γ₅
                       → Ω₁ ∪ Ω₂ ∪ Ω₃ ≡ Ω₄
                       ------------------------------------------------------------------------
                       → Γᵢ ⊢ `if t₁ then t₂ else t₃  :: T , Γ₅ ⨾ Ω₄

  TEat : Γᵢ ⊢ t :: ` q `Unit , Γ₂ ⨾ Ω
              ------------------------------------------------------------------------
           → Γᵢ ⊢ `eat t :: ` un `Unit , Γ₂ ⨾ Ω

  TPair : (p₁ : x ∈ α) → (p₂ : y ∈ α)
            → Γᵢ ⊢ ` y # p₂ :: T₂ , Γ₂ ⨾ Ω₁ -- the context is first passed into t₂ because pairs of ordered variables must conserve the order of the stack. For other variables the order of evaluation (in pairs) doesn't matter, so this is safe.
            → Γ₂ ⊢ ` x # p₁ :: T₁ , Γ₃ ⨾ Ω₂
            → q ⟨ T₁ ⟩
            → q ⟨ T₂ ⟩
            → Ω₁ ∪ Ω₂ ≡ Ω₃
            ------------------------------------------------------------------------
            → Γᵢ ⊢ ` q < x , y > {p₁} {p₂} :: ` q ` T₁ `× T₂ , Γ₃ ⨾ Ω₃

  TSplit : (p₁ : x ∉ α) → (p₂ : y ∉ α) → (p₃ : x ≢ y)
              →  Γᵢ ⊢ t₁ :: ` q ` T₁ `× T₂ , Γ₂ ⨾ Ω₁
              → ((Γ₂ , x ↦ T₁) , y ↦ T₂) ⊢ t₂ :: T , Γ₃ ⨾ Ω₂
              → Γ₃ ⨾ Ω₂ ÷ (∅ , x ↦ T₁) , y ↦ T₂ ≡ Γ₄
              → Ω₁ ∪ Ω₂ ≡ Ω₃
              ------------------------------------------------------------------------
              → Γᵢ ⊢ (`split t₁ as x , y ⇒ t₂) {p₁} {p₂} {p₃} :: T , Γ₄ ⨾ Ω₃

  TLet : (p : x ∉ α)
           → Γᵢ ⊢ t₁ :: T₁ , Γ₂ ⨾ Ω₁
           → Γ₂ , x ↦ T₁ ⊢ t₂ :: T₂ , Γ₃ ⨾ Ω₂
           → Γ₃ ⨾ Ω₂ ÷ ∅ , x ↦ T₁ ≡ Γ₄
           → Ω₁ ∪ Ω₂ ≡ Ω₃
           ------------------------------------------------------------------------
           → Γᵢ ⊢ (`let x := t₁ ⇒ t₂) {p} :: T₂ , Γ₄ ⨾ Ω₃

  TAbs : (p-uniq : x ∉ α)
            → (p-notord : q ≢ ord)
            → q ⟨⟨ Γᵢ ⟩⟩
            → Γᵢ , x ↦ T₁ ⊢ t :: T₂ , Γ₂ ⨾ Ω
            → Γ₂ ⨾ Ω ÷ (∅ , x ↦ T₁) ≡ Γ₃
            ------------------------------------------------------------------------
            → Γᵢ ⊢ (` q ƛ x :: T₁ ⇒ t) {p-notord} {p-uniq} :: (` q ` T₁ ⇒ T₂) {p-notord} , Γ₃ ⨾ Ω

  TApp : (p₁ : x ∈ α) (p₂ : y ∈ α) (pq : q ≢ ord)
             → Γᵢ ⊢ ` x # p₁ :: (` q ` T₁ ⇒ T₂) {pq} , Γ₂ ⨾ Ω₁
             → Γ₂ ⊢ ` y # p₂ :: T₁ , Γ₃ ⨾ Ω₂
             → Ω₁ ∪ Ω₂ ≡ Ω₃
             ------------------------------------------------------------------------
             → Γᵢ ⊢ (x · y) {p₁} {p₂} :: T₂ , Γ₃ ⨾ Ω₃

infix 2 _⊢_::⊥
_⊢_::⊥ : TypingContext → Term α → Set
_⊢_::⊥ Γ t =  ¬ Σ (Type × TypingContext × Scope) (λ (T , Γ' , Ω) → (Γ ⊢ t :: T , Γ' ⨾ Ω))

typing-unique : ∀ {Γ'₁ Γ'₂ Ω₁ Ω₂} → (Γ ⊢ t :: T₁ , Γ'₁ ⨾ Ω₁)→ Γ ⊢ t :: T₂ , Γ'₂ ⨾ Ω₂ → T₁ ≡ T₂ × Γ'₁ ≡ Γ'₂ × Ω₁ ≡ Ω₂
typing-unique (TUVar p elem₁ _) (TUVar .p  elem₂ _) with ∈*-unique elem₁ elem₂
... | refl = refl , refl , refl
typing-unique (TUVar p elem is-un) (TLVar .p elem₁ is-lin  _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-un) is-lin of λ ()}
typing-unique (TUVar p elem is-un) (TOVar .p elem₁ is-ord _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-un) is-ord of λ ()}
typing-unique (TLVar p elem _ _ Γ'₁-proof) (TLVar .p elem₁ _ _ Γ'₂-proof) =
  case ∈*-unique elem elem₁ of λ {refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof , refl}
typing-unique (TLVar p elem is-lin _ _) (TOVar .p elem₁ is-ord _ _) =
  case ∈*-unique elem elem₁ of λ {refl → case trans (sym is-lin) is-ord of λ ()}
typing-unique (TOVar p elem _ _ Γ'₁-proof) (TOVar .p elem₁ _ _ Γ'₂-proof) =
  case ∈*-unique elem elem₁ of λ {refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof , refl}
typing-unique (TAVar p elem _ _ Γ'₁-proof) (TAVar .p elem₁ _ _ Γ'₂-proof) =
  case ∈*-unique elem elem₁ of λ {refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof , refl}
typing-unique (TUVar p elem is-un) (TAVar p elem₁ is-aff _ _) =
  case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-aff) is-un) λ () }
typing-unique (TLVar p elem is-lin _ _) (TAVar p elem₁ is-aff _ _) =
  case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-aff) is-lin) λ () }
typing-unique (TOVar p elem is-ord _ _) (TAVar p elem₁ is-aff _ _) =
  case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-aff) is-ord) λ () }
typing-unique (TRVar _ elem is-rel _ _) (TUVar _ elem₁ is-un) = case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-rel) is-un) λ () }
typing-unique (TRVar _ elem is-rel _ x₁) (TLVar _ elem₁ is-lin _ x₃) = case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-rel) is-lin) λ () }
typing-unique (TRVar _ elem is-rel _ x₁) (TOVar _ elem₁ is-ord _ x₃) = case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-rel) is-ord) λ () }
typing-unique (TRVar _ elem is-rel _ x₁) (TAVar _ elem₁ is-aff _ x₃) = case ∈*-unique elem elem₁ of λ {refl → contradiction (trans (sym is-rel) is-aff) λ () }
typing-unique (TRVar _ elem is-rel _ Γ'₁-proof) (TRVar _ elem₁ _ _ Γ'₂-proof) = case ∈*-unique elem elem₁ of λ { refl → refl , deleteBinding-unique Γ'₁-proof Γ'₂-proof , refl  }
typing-unique a@(TAVar _ _ _ _ _) b@(TUVar _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TAVar _ _ _ _ _) b@(TLVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TAVar _ _ _ _ _) b@(TOVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TOVar _ _ _ _ _) b@(TUVar _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TOVar _ _ _ _ _) b@(TLVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TLVar _ _ _ _ _) b@(TUVar _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TUVar _ _ _) b@(TRVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TLVar _ _ _ _ _) b@(TRVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TOVar _ _ _ _ _) b@(TRVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique a@(TAVar _ _ _ _ _) b@(TRVar _ _ _ _ _) = Data.Product.map sym (Data.Product.map sym sym) $ typing-unique b a
typing-unique TBool TBool = refl , refl , refl
typing-unique TUnit TUnit = refl , refl , refl
typing-unique (TIf cond-bool₁ left-T₁ right-T₁ intersect₁ Ω-merge₁) (TIf cond-bool₂ left-T₂ right-T₂ intersect₂ Ω-merge₂) with typing-unique cond-bool₁ cond-bool₂
... | (refl , refl , refl) with typing-unique left-T₁ left-T₂
... | (refl , refl , refl) with typing-unique right-T₁ right-T₂
... | (refl , refl , refl) with affineIntersection-unique intersect₁ intersect₂
... | refl with mergeScopes3-unique Ω-merge₁ Ω-merge₂
... | refl = refl , refl , refl
typing-unique (TEat a) (TEat b) with typing-unique a b
... | refl , refl , refl = refl , refl , refl
typing-unique (TPair _ _ left₁ right₁ _ _ Ω-merge₁) (TPair _ _ left₂ right₂ _ _ Ω-merge₂) with typing-unique left₁ left₂
... | (refl , refl , refl) with typing-unique right₁ right₂
... | (refl , refl , refl) with mergeScopes-unique Ω-merge₁ Ω-merge₂
... | refl = refl , refl , refl
typing-unique (TSplit _ _ _ arg₁ body₁ div₁ Ω-merge₁) (TSplit _ _ _ arg₂ body₂ div₂ Ω-merge₂) with typing-unique arg₁ arg₂
... | (refl , refl , refl) with typing-unique body₁ body₂
... | (refl , refl , refl) with ÷-unique div₁ div₂
... | refl with mergeScopes-unique Ω-merge₁ Ω-merge₂
... | refl = refl , refl , refl
typing-unique (TLet _ arg₁ body₁ div₁ Ω-merge₁) (TLet _ arg₂ body₂ div₂ Ω-merge₂) with typing-unique arg₁ arg₂
... | (refl , refl , refl) with typing-unique body₁ body₂
... | (refl , refl , refl) with ÷-unique div₁ div₂
... | refl with mergeScopes-unique Ω-merge₁ Ω-merge₂
... | refl = refl , refl , refl
typing-unique (TAbs _ _ _ body₁ div₁) (TAbs _ _ _ body₂ div₂) with typing-unique body₁ body₂
... | (refl , refl , refl) with ÷-unique div₁ div₂
... | refl = refl , refl , refl
typing-unique (TApp _ _ _ fun₁ arg₁ Ω-merge₁) (TApp _ _ _ fun₂ arg₂ Ω-merge₂) with typing-unique fun₁ fun₂
... | (refl , refl , refl) with typing-unique arg₁ arg₂
... | (refl , refl , refl) with mergeScopes-unique Ω-merge₁ Ω-merge₂
... | refl = refl , refl , refl

typing-contradiction : ∀ {a} {Whatever : Set a} → T₁ ≢ T₂ → Γ ⊢ t :: T₁ , Γ₂ ⨾ Ω₁ → Γ ⊢ t :: T₂ , Γ₃ ⨾ Ω₂ → Whatever
typing-contradiction neq a b = contradiction (proj₁ (typing-unique a b)) neq
