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

private if-untypable-if-either-arm-untypable : ∀ {Γ Γ' T Ω} {t t₁ t₂ : Term α} → Γ ⊢ t :: T , Γ' ⨾ Ω → (Γ' ⊢ t₁ ::⊥) ⊎ (Γ' ⊢ t₂ ::⊥) → Γ ⊢(`if t then t₁ else t₂) ::⊥
if-untypable-if-either-arm-untypable cond (inj₁ t₁-untypable) = λ { ((T , Γ') , TIf cond' t₁-typable _ _ _) → case typing-unique cond cond' of λ {(refl , refl , refl) → contradiction ((T , _) , t₁-typable) t₁-untypable}}
if-untypable-if-either-arm-untypable cond (inj₂ t₂-untypable) = λ { ((T , Γ') , TIf cond' _ t₂-typable _ _) → case typing-unique cond cond' of λ {(refl , refl , refl) → contradiction ((T , _) , t₂-typable) t₂-untypable}}

TypecheckResult : TypingContext → Term α → Set
TypecheckResult Γ t =  Dec (Σ (Type × TypingContext × Scope) λ { (T , Γ' , Ω) → Γ ⊢ t :: T , Γ' ⨾ Ω } )

typeOf : (Γ : TypingContext) → (t : Term α) → TypecheckResult Γ t
typeOf Γ (` x # well-scoped) with typeLookup Γ x
...  | no not-elem = no (λ {
  ((ty , _) , TUVar .well-scoped elem _) → contradiction (ty , elem) not-elem ;
  ((ty , _) , TLVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ;
  ((ty , _) , TOVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ;
  ((ty , _) , TAVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem ;
  ((ty , _) , TRVar .well-scoped elem _ _ _) → contradiction (ty , elem) not-elem})
...  | yes (ty , elem) = yes $ qualifierCases ty
           (λ is-un → (ty , Γ , ∅) , (TUVar well-scoped elem is-un))
           (λ is-lin → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ' , ∅) , TLVar well-scoped elem is-lin Γ' Γ'-proof)
           (λ is-ord → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in  (ty , Γ' , ∅) , TOVar well-scoped elem is-ord Γ' Γ'-proof)
          (λ is-aff → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in (ty , Γ' , ∅) , TAVar well-scoped elem is-aff Γ' Γ'-proof)
          (λ is-rel → let (Γ' , Γ'-proof) = deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ x ty (∈*⇒∈ elem) in (ty , Γ' , (∅ ⸴ x)) , TRVar well-scoped elem is-rel Γ' Γ'-proof)
typeOf Γ (` q ` b) = yes ((` q `Bool , Γ , ∅) , TBool)
typeOf Γ (` q `unit) = yes ((` q `Unit , Γ , ∅) , TUnit)
typeOf Γ (`if t₁ then t₂ else t₃) with typeOf Γ t₁
... | no cond-untypable = no (λ { (_ , TIf  {q = q} {Γ₂ = Γ₂}  cond-bool _ _ _ _) → contradiction ((` q `Bool , Γ₂ , _) , cond-bool) cond-untypable})
... | yes ((T-cond , Γ₂ , Ω₁) , cond-proof) with bool? T-cond
... | no' cond-not-bool = no (λ { (_ , TIf  cond-bool _ _ _ _) → typing-contradiction cond-not-bool cond-bool cond-proof})
... | yes' (q , refl) with typeOf Γ₂ t₂ | typeOf Γ₂ t₃
... | no a  | _ = no (if-untypable-if-either-arm-untypable cond-proof (inj₁ a))
... | _        | no b =  no (if-untypable-if-either-arm-untypable cond-proof (inj₂ b))
... | yes ((T-left , Γ₃-left , Ω₂) , left-proof) | yes ((T-right , Γ₃-right , Ω₃) , right-proof) with T-left ≟ₜ T-right | affineIntersection Γ₃-left Γ₃-right
... | no type-mismatch | _ = no 
      λ { ((T , Γ₃') , TIf cond' left right _ _) → case typing-unique cond-proof cond' of
      λ {(refl , refl , refl) → case typing-unique left left-proof of
      λ {(refl , refl , refl) → case typing-unique right right-proof of
      λ {(refl , refl , refl) → contradiction refl type-mismatch}}}}
... | _ | no no-intersect = no 
      λ { ((T , Γ₃') , TIf cond' left right intersect _) → case typing-unique cond-proof cond' of
      λ {(refl , refl , refl) → case typing-unique left left-proof of
      λ {(refl , refl , refl) → case typing-unique right right-proof of
      λ {(refl , refl , refl) → contradiction (_ , intersect) no-intersect}}}}
... | yes refl | yes (Γ₅ , intersect) with mergeScopes3 Ω₁ Ω₂ Ω₃
... | Ω₄ , Ω₄-proof = yes ((T-left , Γ₅ , Ω₄) , (TIf cond-proof left-proof right-proof intersect Ω₄-proof))
typeOf Γ ((` q < x , y >) {x-well-scoped} {y-well-scoped}) with typeOf Γ (` y # y-well-scoped)
... | no y-untypable = no (λ { (_ , TPair {T₂ = T₂} {Γ₂ = Γ₂} _ _ y-typable _ _ _ _) → contradiction ((T₂ , Γ₂ , _) , y-typable) y-untypable})
... | yes ((T₂ , Γ₂ , Ω₁) , T₂-proof) with typeOf Γ₂ (` x # x-well-scoped)
... | no x-untypable =  no (λ { (_ , TPair {T₁ = T₁} {Γ₃ = Γ₃} _ _ y-typable x-typable _ _ _) → case typing-unique T₂-proof y-typable of λ {(refl , refl , refl) → contradiction ((T₁ , Γ₃ , _) , x-typable) x-untypable}})
... | yes ((T₁ , Γ₃ , Ω₂) , T₁-proof) with canContain? q T₁ | canContain? q T₂
... | no a | _ = no (λ { ((T , Γ') , TPair _ _ proof-y proof-x containment-x _ _) → case typing-unique proof-y T₂-proof of λ {(refl , refl , refl) → case typing-unique proof-x T₁-proof of case typing-unique T₁-proof proof-x  of λ {(refl , refl , refl) → contradiction containment-x a}}})
... | _       | no b = no (λ { ((T , Γ') , TPair _ _ proof-y proof-x _ containment-y _) → case typing-unique proof-y T₂-proof of λ {(refl , refl , refl) → case typing-unique proof-x T₁-proof of case typing-unique T₂-proof proof-y  of λ {(refl , refl , refl) → contradiction containment-y b}}})
... | yes containment-x | yes containment-y with mergeScopes Ω₁ Ω₂
... | Ω₃ , Ω₃-proof = yes (((` q ` T₁ `× T₂) , Γ₃ , Ω₃) , (TPair x-well-scoped y-well-scoped T₂-proof T₁-proof containment-x containment-y Ω₃-proof))
typeOf Γ ((`split t₁ as x , y ⇒ t₂) {x-uniq} {y-uniq} {x≢y}) with typeOf Γ t₁
... | no t₁-untypable = no (λ { (_ , TSplit {q = q} {T₁ = T₁} {T₂ = T₂} {Γ₂ = Γ₂} _ _ _ t₁-typable _ _ _) → contradiction ((` q ` T₁ `× T₂ , Γ₂ , _) , t₁-typable) t₁-untypable})
... | yes ((T₁ , Γ₂ , Ω₁) , T₁-proof) with product? T₁
... | no' not-prod = no (λ { (_ , TSplit  _ _ _ t₁-proof _ _ _) → case typing-unique T₁-proof t₁-proof of λ {(refl , refl , refl) → contradiction refl not-prod}}) -- todo use typing-contradiction
... | yes' ((q , T₁₁ , T₁₂) , refl) with typeOf ((Γ₂ , x ↦ T₁₁) , y ↦ T₁₂) t₂
... | no t₂-untypable = no (λ { (_ , TSplit {T = T₂} {Γ₃ = Γ₃} _ _ _ t₁-proof t₂-proof _ _) → case typing-unique T₁-proof t₁-proof of λ {(refl , refl , refl) → contradiction ((T₂ , Γ₃ , _) , t₂-proof) t₂-untypable}})
... | yes ((T₂ , Γ₃ , Ω₂) , T₂-proof) with divideContext Γ₃ Ω₂ ((∅ , x ↦ T₁₁) , y ↦ T₁₂)
... | no Γ₃-nodiv = no (λ { (_ , TSplit {Γ₄ = Γ₄} _ _ _ t₁-proof t₂-proof Γ₃-div _) → case typing-unique T₁-proof t₁-proof of λ { (refl , refl , refl) → case typing-unique T₂-proof t₂-proof of λ {(refl , refl , refl) → contradiction ((Γ₄ , Γ₃-div)) Γ₃-nodiv}}})
... | yes (Γ₄ , Γ₄-proof) with mergeScopes Ω₁ Ω₂
... | Ω₃ , Ω₃-proof = yes ((T₂ , Γ₄ , Ω₃) , (TSplit x-uniq y-uniq x≢y T₁-proof T₂-proof Γ₄-proof Ω₃-proof ))
typeOf Γ ((` q ƛ x :: T₁ ⇒ t) {q-not-ord} {x-uniq})  with canContainCtx? q Γ
... | no bad-containment = no (λ {(_ , TAbs _ _ Γ-containment _ _) → contradiction Γ-containment bad-containment})
... | yes Γ-containment with typeOf (Γ , x ↦ T₁) t
... | no t-untypable = no λ {(_ , TAbs {T₂ = T₂} {Γ₂ = Γ₂} _ _ _ t-typable _) → contradiction ((T₂ , Γ₂ , _) , t-typable) t-untypable}
... | yes ((T₂ , Γ₂ , Ω) , T₂-proof) with divideContext Γ₂ Ω (∅ , x ↦ T₁)
... | no Γ₂-nodiv = no λ {(_ , TAbs {Γ₃ = Γ₃} _ _ _ t-typable Γ₂-div) → case typing-unique T₂-proof t-typable of λ { (refl , refl , refl) → contradiction ((Γ₃ , Γ₂-div)) Γ₂-nodiv }}
... | yes (Γ₃ , Γ₃-proof) = yes (((` q ` T₁ ⇒ T₂) , Γ₃ , Ω) , (TAbs x-uniq q-not-ord Γ-containment T₂-proof Γ₃-proof))
typeOf Γ ((x · y) {well-scoped-x} {well-scoped-y}) with typeOf Γ (` x # well-scoped-x)
... | no x-untypable = no ((λ { (_ , TApp {q = q} {T₁ = T₁} {T₂ = T₂} {Γ₂ = Γ₂} _ _ pq x-typable  _ _) →  contradiction (((` q ` T₁ ⇒ T₂) , Γ₂ , _) , x-typable) x-untypable }))
... | yes ((T₁ , Γ₂ , Ω₁) , T₁-proof) with arrow? T₁
... | no' not-arrow = no λ { (_ , TApp _ _ _ x-proof _ _) → case typing-unique T₁-proof x-proof of λ { (refl , refl , refl) → contradiction refl not-arrow } } -- todo use typing-contradiction
... | yes' (q , (q-not-ord , T₁₁ , T₁₂) , refl) with typeOf Γ₂ (` y # well-scoped-y)
... | no y-untypable = no λ { (_ , TApp {Γ₃ = Γ₃} _ _ _ x-proof y-proof _) → case typing-unique T₁-proof x-proof of λ { (refl , refl , refl) → contradiction ((T₁₁ , Γ₃ , _) , y-proof) y-untypable} }
... | yes ((T₂ , Γ₃ , Ω₂) , T₂-proof) with T₂ ≟ₜ T₁₁
... | no wrong-T₂ = no λ { (_ , TApp _ _ _ x-proof y-proof _) → case typing-unique T₁-proof x-proof of λ { (refl , refl , refl) → case typing-unique T₂-proof y-proof of λ { (refl , refl , refl) → contradiction refl wrong-T₂ }} }
... | yes refl with mergeScopes Ω₁ Ω₂
... | Ω₃ , Ω₃-proof = yes ((T₁₂ , Γ₃ , Ω₃) , (TApp well-scoped-x well-scoped-y q-not-ord T₁-proof T₂-proof Ω₃-proof))
typeOf Γ ((`let x := t₁ ⇒ t₂) {x-uniq}) with typeOf Γ t₁
... | no t₁-untypable = no λ {(_ , TLet {T₁ = T₁} {Γ₂ = Γ₂} _ t₁-typable _ _ _) → contradiction ((T₁ , Γ₂ , _) , t₁-typable) t₁-untypable }
... | yes ((T₁ , Γ₂ , Ω₁) , T₁-proof) with typeOf (Γ₂ , x ↦ T₁) t₂
... | no t₂-untypable = no λ {(_ , TLet {T₂ = T₂} {Γ₃ = Γ₃} _ t₁-typable t₂-typable _ _) → case typing-unique T₁-proof t₁-typable of λ { (refl , refl , refl) → contradiction ((T₂ , Γ₃ , _) , t₂-typable) t₂-untypable } }
... | yes ((T₂ , Γ₃ , Ω₂) , T₂-proof) with divideContext Γ₃ Ω₂ (∅ , x ↦ T₁)
... | no Γ₃-nodiv = no  λ {(_ , TLet  {Γ₄ = Γ₄} _ t₁-typable t₂-typable Γ₃-div _) → case typing-unique T₁-proof t₁-typable of λ { (refl , refl , refl) → case typing-unique T₂-proof t₂-typable of λ { (refl , refl , refl) →  contradiction ((Γ₄ , Γ₃-div)) Γ₃-nodiv} } }
... | yes (Γ₄ , Γ₄-proof) with mergeScopes Ω₁ Ω₂
... | Ω₃ , Ω₃-proof = yes ((T₂ , Γ₄ , Ω₃) , (TLet x-uniq T₁-proof T₂-proof Γ₄-proof Ω₃-proof))
typeOf Γ (`eat t) with typeOf Γ t
... | no t-untypable = no λ {(_ , TEat {q = q} {Γ₂ = Γ₂} t-typable) → contradiction ((` q `Unit , Γ₂ , _) , t-typable) t-untypable}
... | yes ((T , Γ₂ , Ω) , T-proof) with unit? T
... | no' not-unit = no (λ { (_ , TEat t-unit) → typing-contradiction not-unit T-proof t-unit })
... | yes' (_ , refl) = yes ((` un `Unit , Γ₂ , Ω) , TEat T-proof)

typeOf' : (t : Term ∅) → TypecheckResult ∅ t
typeOf' = typeOf ∅
