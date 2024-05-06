open import Relation.Binary.Definitions

module TypeChecker where

open import Lang 
open import Scoping.Context {name} {_≟ₙ_}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Function using (case_of_; _$_)
open import Data.Sum using (inj₁; inj₂)


private
  variable
    α : Scope

private if-untypable-if-either-arm-untypable : ∀ {Γ Γ' T} {t t₁ t₂ : Term α} → Γ ⊢ t :: T , Γ' → (Γ' ⊢ t₁ ::⊥) ⊎ (Γ' ⊢ t₂ ::⊥) → Γ ⊢(`if t then t₁ else t₂) ::⊥
if-untypable-if-either-arm-untypable cond (inj₁ t₁-untypable) = λ { ((T , Γ') , TIf cond' t₁-typable _) → case typing-unique cond cond' of λ {(refl , refl) → contradiction ((T , Γ') , t₁-typable) t₁-untypable}}
if-untypable-if-either-arm-untypable cond (inj₂ t₂-untypable) = λ { ((T , Γ') , TIf cond' _ t₂-typable) → case typing-unique cond cond' of λ {(refl , refl) → contradiction ((T , Γ') , t₂-typable) t₂-untypable}}

TypecheckResult : TypingContext → Term α → Set
TypecheckResult Γ t =  Dec (Σ (Type × TypingContext) λ { (T , Γ') → Γ ⊢ t :: T , Γ' } )

typeOf : (Γ : TypingContext) → (t : Term α) → TypecheckResult Γ t
typeOf Γ (` x # well-scoped) with typeLookup Γ x
...  | no not-elem = no (λ { ((ty , _) , TUVar .well-scoped elem _) → contradiction (ty , elem) not-elem ; ((ty , _) , TLVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ; ((ty , _) , TOVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem})
...  | yes (ty , elem) = yes $ qualifierCases ty
           (λ is-un → (ty , Γ) , (TUVar well-scoped elem is-un))
           (λ is-lin → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TLVar well-scoped elem is-lin Γ' Γ'-proof)
           (λ is-ord → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ') , TOVar well-scoped elem is-ord Γ' Γ'-proof)
typeOf Γ (` q ` b) = yes ((` q `Bool , Γ) , TBool)
typeOf Γ (` q `unit) = yes ((` q `Unit , Γ) , TUnit)
typeOf Γ (`if t₁ then t₂ else t₃) with typeOf Γ t₁
... | no cond-untypable = no (λ { (_ , TIf  {q = q} {Γ₂ = Γ₂} cond-bool _ _) → contradiction ((` q `Bool , Γ₂) , cond-bool) cond-untypable})
... | yes ((T-cond , Γ₂) , cond-proof) with bool? T-cond
... | no' cond-not-bool = no (λ { (_ , TIf  cond-bool _ _) → typing-contradiction cond-not-bool cond-bool cond-proof})
... | yes' (q , refl) with typeOf Γ₂ t₂ | typeOf Γ₂ t₃
... | no a  | _ = no (if-untypable-if-either-arm-untypable cond-proof (inj₁ a))
... | _        | no b =  no (if-untypable-if-either-arm-untypable cond-proof (inj₂ b))
... | yes ((T-left , Γ₃-left) , left-proof) | yes ((T-right , Γ₃-right) , right-proof) with T-left ≟ₜ T-right ×-dec (_≟Γ_ {_≟ᵥ_ = _≟ₜ_} Γ₃-left Γ₃-right)
... | no left≢right = no
         λ { ((T , Γ₃') , TIf cond' left right) → case typing-unique cond-proof cond' of
         λ {(refl , refl) → case typing-unique left left-proof of
         λ {(refl , refl) → case typing-unique right right-proof of
         λ {(refl , refl) → contradiction (refl , refl) left≢right}}}}
... | yes (refl , refl) = yes ((T-left , Γ₃-left) , TIf cond-proof left-proof right-proof)
typeOf Γ ((` q < x , y >) {x-well-scoped} {y-well-scoped}) with typeOf Γ (` y # y-well-scoped)
... | no y-untypable = no (λ { (_ , TPair {T₂ = T₂} {Γ₂ = Γ₂} _ _ y-typable _ _ _) → contradiction ((T₂ , Γ₂) , y-typable) y-untypable})
... | yes ((T₂ , Γ₂) , T₂-proof) with typeOf Γ₂ (` x # x-well-scoped)
... | no x-untypable =  no (λ { (_ , TPair {T₁ = T₁} {Γ₃ = Γ₃} _ _ y-typable x-typable _ _) → case typing-unique T₂-proof y-typable of λ {(refl , refl) → contradiction ((T₁ , Γ₃) , x-typable) x-untypable}})
... | yes ((T₁ , Γ₃) , T₁-proof) with canContain? q T₁ | canContain? q T₂
... | no a | _ = no (λ { ((T , Γ') , TPair _ _ proof-y proof-x containment-x _) → case typing-unique proof-y T₂-proof of λ {(refl , refl) → case typing-unique proof-x T₁-proof of case typing-unique T₁-proof proof-x  of λ {(refl , refl) → contradiction containment-x a}}})
... | _       | no b = no (λ { ((T , Γ') , TPair _ _ proof-y proof-x _ containment-y) → case typing-unique proof-y T₂-proof of λ {(refl , refl) → case typing-unique proof-x T₁-proof of case typing-unique T₂-proof proof-y  of λ {(refl , refl) → contradiction containment-y b}}})
... | yes containment-x | yes containment-y = yes (((` q ` T₁ `× T₂) , Γ₃) , (TPair x-well-scoped y-well-scoped T₂-proof T₁-proof containment-x containment-y))
typeOf Γ (`split t₁ as x , y ⇒ t₂) with typeOf Γ t₁
... | no t₁-untypable = no (λ { (_ , TSplit {q = q} {T₁ = T₁} {T₂ = T₂} {Γ₂ = Γ₂} t₁-typable _ _) → contradiction ((` q ` T₁ `× T₂ , Γ₂) , t₁-typable) t₁-untypable})
... | yes ((T₁ , Γ₂) , T₁-proof) with product? T₁
... | no' not-prod = no (λ { (_ , TSplit  t₁-proof _ _) → case typing-unique T₁-proof t₁-proof of λ {(refl , refl) → contradiction refl not-prod}}) -- todo use typing-contradiction
... | yes' ((q , T₁₁ , T₁₂) , refl) with typeOf ((Γ₂ , x ↦ T₁₁) , y ↦ T₁₂) t₂
... | no t₂-untypable = no (λ { (_ , TSplit {T = T₂} {Γ₃ = Γ₃} t₁-proof t₂-proof _) → case typing-unique T₁-proof t₁-proof of λ {(refl , refl) → contradiction ((T₂ , Γ₃) , t₂-proof) t₂-untypable}})
... | yes ((T₂ , Γ₃) , T₂-proof) with divideContext Γ₃ ((∅ , x ↦ T₁₁) , y ↦ T₁₂)
... | no Γ₃-nodiv = no (λ { (_ , TSplit {Γ₄ = Γ₄} t₁-proof t₂-proof Γ₃-div) → case typing-unique T₁-proof t₁-proof of λ { (refl , refl) → case typing-unique T₂-proof t₂-proof of λ {(refl , refl) → contradiction (Γ₄ , Γ₃-div) Γ₃-nodiv}}})
... | yes (Γ₄ , Γ₄-proof) = yes ((T₂ , Γ₄) , (TSplit T₁-proof T₂-proof Γ₄-proof))
typeOf Γ (` q ƛ x :: T₁ ⇒ t) with q ≟q ord
... | yes q-ord = no λ {(_ , TAbs q-not-ord _ _ _) → contradiction q-ord q-not-ord}
... | no q-not-ord with canContainCtx? q Γ
... | no bad-containment = no (λ {(_ , TAbs _ Γ-containment _ _) → contradiction Γ-containment bad-containment})
... | yes Γ-containment with typeOf (Γ , x ↦ T₁) t
... | no t-untypable = no λ {(_ , TAbs {T₂ = T₂} {Γ₂ = Γ₂} _ _ t-typable _) → contradiction ((T₂ , Γ₂) , t-typable) t-untypable}
... | yes ((T₂ , Γ₂) , T₂-proof) with divideContext Γ₂ (∅ , x ↦ T₁)
... | no Γ₂-nodiv = no λ {(_ , TAbs {Γ₃ = Γ₃} _ _ t-typable Γ₂-div) → case typing-unique T₂-proof t-typable of λ { (refl , refl) → contradiction (Γ₃ , Γ₂-div) Γ₂-nodiv }}
... | yes (Γ₃ , Γ₃-proof) = yes (((` q ` T₁ ⇒ T₂) , Γ₃) , (TAbs q-not-ord Γ-containment T₂-proof Γ₃-proof))
typeOf Γ ((x · y) {well-scoped-x} {well-scoped-y}) with typeOf Γ (` x # well-scoped-x)
... | no x-untypable = no ((λ { (_ , TApp {q = q} {T₁ = T₁} {T₂ = T₂} {Γ₂ = Γ₂} _ _ pq x-typable _) →  contradiction (((` q ` T₁ ⇒ T₂) , Γ₂) , x-typable) x-untypable }))
... | yes ((T₁ , Γ₂) , T₁-proof) with arrow? T₁
... | no' not-arrow = no λ { (_ , TApp _ _ _ x-proof _) → case typing-unique T₁-proof x-proof of λ { (refl , refl) → contradiction refl not-arrow } } -- todo use typing-contradiction
... | yes' (q , (q-not-ord , T₁₁ , T₁₂) , refl) with typeOf Γ₂ (` y # well-scoped-y)
... | no y-untypable = no λ { (_ , TApp {Γ₃ = Γ₃} _ _ _ x-proof y-proof) → case typing-unique T₁-proof x-proof of λ { (refl , refl) → contradiction ((T₁₁ , Γ₃) , y-proof) y-untypable} }
... | yes ((T₂ , Γ₃) , T₂-proof) with T₂ ≟ₜ T₁₁
... | no wrong-T₂ = no λ { (_ , TApp _ _ _ x-proof y-proof) → case typing-unique T₁-proof x-proof of λ { (refl , refl) → case typing-unique T₂-proof y-proof of λ { (refl , refl) → contradiction refl wrong-T₂ }} }
... | yes refl = yes ((T₁₂ , Γ₃) , (TApp well-scoped-x well-scoped-y q-not-ord T₁-proof T₂-proof))
typeOf Γ (`let x := t₁ ⇒ t₂) with typeOf Γ t₁
... | no t₁-untypable = no λ {(_ , TLet {T₁ = T₁} {Γ₂ = Γ₂} t₁-typable _ _) → contradiction ((T₁ , Γ₂) , t₁-typable) t₁-untypable }
... | yes ((T₁ , Γ₂) , T₁-proof) with typeOf (Γ₂ , x ↦ T₁) t₂
... | no t₂-untypable = no λ {(_ , TLet {T₂ = T₂} {Γ₃ = Γ₃} t₁-typable t₂-typable _) → case typing-unique T₁-proof t₁-typable of λ { (refl , refl) → contradiction ((T₂ , Γ₃) , t₂-typable) t₂-untypable } }
... | yes ((T₂ , Γ₃) , T₂-proof) with divideContext Γ₃ (∅ , x ↦ T₁)
... | no Γ₃-nodiv = no  λ {(_ , TLet  {Γ₄ = Γ₄} t₁-typable t₂-typable Γ₃-div) → case typing-unique T₁-proof t₁-typable of λ { (refl , refl) → case typing-unique T₂-proof t₂-typable of λ { (refl , refl) →  contradiction (Γ₄ , Γ₃-div) Γ₃-nodiv} } }
... | yes (Γ₄ , Γ₄-proof) = yes ((T₂ , Γ₄) , (TLet T₁-proof T₂-proof Γ₄-proof))
typeOf Γ (`eat t) with typeOf Γ t
... | no t-untypable = no λ {(_ , TEat {q = q} {Γ₂ = Γ₂} t-typable) → contradiction ((` q `Unit , Γ₂) , t-typable) t-untypable}
... | yes ((T , Γ₂) , T-proof) with unit? T
... | no' not-unit = no (λ { (_ , TEat t-unit) → typing-contradiction not-unit T-proof t-unit })
... | yes' (_ , refl) = yes ((` un `Unit , Γ₂) , TEat T-proof)
