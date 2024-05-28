open import Relation.Binary.Definitions

module Lang.TypingContext {name : Set} {_≟ₙ_ : DecidableEquality name} where

open import Lang.Type
open import Lang.Qualifier
open import Scoping.Context {name} {_≟ₙ_}
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Binary using (REL)
open import Data.Bool
open import Function.Base using (case_of_; _$_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred)
open import Data.Product
open import Level
open import Data.Sum
open import Data.Empty
open import Data.Unit renaming (_≟_ to _≟⊤_)

TypingContext : Set
TypingContext = Context Type

-- Ordered inclusion in the typing context: same as normal inclusion for non-ordered types, but requires that the type be at the head of the context for ordered types
data _↦_∈*_ (x : name) (t : Type) : TypingContext → Set where
  here : {Γ : TypingContext} → x ↦ t ∈* (Γ , x ↦ t)
  thereUnordered : ∀ {y u} {Γ : TypingContext} → x ≢ y → False (ordQualified? t) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)
  thereOrdered : ∀ {y u} {Γ : TypingContext} → x ≢ y → True (ordQualified? t) → False (ordQualified? u) → x ↦ t ∈* Γ → x ↦ t ∈* (Γ , y ↦ u)

_↦_∉*_ : name → Type → TypingContext → Set
x ↦ t ∉* Γ  = ¬ ( x ↦ t ∈* Γ )

_↦_∈*?_ : (x : name) (ty : Type) (Γ : TypingContext) → Dec (x ↦ ty ∈* Γ)
x ↦ ty ∈*? ∅ = no (λ ())
x ↦ ty ∈*? (Γ , y ↦ u) with x ≟ₙ y | ty ≟ₜ u | x ↦ ty ∈*? Γ | ordQualified? ty | ordQualified? u 
... | yes refl | yes refl | _ | _ | _ = yes here
... | yes refl | no ty≢u | _ | _ | _ = no λ { here → contradiction refl ty≢u ; (thereUnordered x≢y _ _) → contradiction refl x≢y ; (thereOrdered x≢y _ _ _) → contradiction refl x≢y}
... | no x≢y  | _ | no not-elem | _ | _  = no λ { here → contradiction refl x≢y ; (thereUnordered _ _ elem) → contradiction elem not-elem; (thereOrdered _ _ _ elem) → contradiction elem not-elem}
... | no x≢y | _  | yes elem | no ty-not-ord | _ = yes (thereUnordered x≢y (fromWitnessFalse ty-not-ord) elem)
... | no x≢y | _  | yes elem | yes ty-ord | no u-not-ord = yes (thereOrdered x≢y (fromWitness ty-ord) (fromWitnessFalse u-not-ord) elem)
... | no x≢y | _  | yes elem | yes ty-ord | yes u-ord = no λ { here → contradiction refl x≢y ; (thereUnordered _ ty-not-ord _) → contradiction ty-ord (toWitnessFalse ty-not-ord) ; (thereOrdered _ _ u-not-ord _) → contradiction u-ord (toWitnessFalse u-not-ord)}

∈*-unique : ∀ {x Γ T U} → x ↦ T ∈* Γ → x ↦ U ∈* Γ → T ≡ U
∈*-unique here here = refl
∈*-unique here (thereUnordered x≢x _ _) = contradiction refl x≢x
∈*-unique here (thereOrdered x≢x _ _ _) = contradiction refl x≢x
∈*-unique (thereUnordered x≢x _ _) here = contradiction refl x≢x
∈*-unique (thereUnordered x x₁ a) (thereUnordered x₂ x₃ b) = ∈*-unique a b
∈*-unique (thereUnordered x x₁ a) (thereOrdered x₂ x₃ x₄ b) = ∈*-unique a b
∈*-unique (thereOrdered x≢x _ _ _) here = contradiction refl x≢x
∈*-unique (thereOrdered x x₁ x₂ a) (thereUnordered x₃ x₄ b) = ∈*-unique a b
∈*-unique (thereOrdered x x₁ x₂ a) (thereOrdered x₃ x₄ x₅ b) = ∈*-unique a b

typeLookup : (Γ : TypingContext) (x : name) → Dec (Σ[ ty ∈ Type ] x ↦ ty ∈* Γ)
typeLookup ∅ x = no λ { (ty , ())}
typeLookup (Γ , y ↦ u) x with x ≟ₙ y
... | yes refl  = yes (u , here)
... | no x≢y with typeLookup Γ x
...   | no nosub = no (λ { (ty , here) → contradiction refl x≢y ; (ty , thereUnordered _ _ sub) → contradiction (ty , sub) nosub ; (ty , thereOrdered _ _ _ sub) → contradiction (ty , sub) nosub})
...   | yes (ty , sub) with ordQualified? ty | ordQualified? u
...     | yes ty-ord | no u-not-ord = yes (ty , (thereOrdered x≢y (fromWitness ty-ord) (fromWitnessFalse u-not-ord) sub))
...     | yes ty-ord | yes u-ord = no λ {
          (ty' , here) → contradiction refl x≢y ;
          (ty' , thereUnordered _ ty'-not-ord sub') → case ∈*-unique sub sub' of λ {refl → contradiction ty-ord (toWitnessFalse ty'-not-ord)} ;
          (ty' , thereOrdered _ _  u-not-ord _) → contradiction u-ord (toWitnessFalse u-not-ord)}
...    | no ty-not-ord | _ = yes (ty , (thereUnordered x≢y (fromWitnessFalse ty-not-ord) sub))

-- "Weakens" ∈* into ∈
∈*⇒∈ : ∀ {x t Γ} → x ↦ t ∈* Γ → x ↦ t ∈ Γ
∈*⇒∈ here = here
∈*⇒∈ (thereUnordered _ _ p) = there (∈*⇒∈ p)
∈*⇒∈ (thereOrdered _ _ _ p) = there (∈*⇒∈ p)

data _⨾_÷_≡_ : TypingContext → TypingContext → TypingContext → TypingContext → Set where
  divEmpty : (Γ : TypingContext) (Ω : TypingContext)  → Γ ⨾ Ω ÷ ∅ ≡ Γ
  
  -- When dividing by an unrestricted var, we assume that the returned context (Γ₁) still contains it (otherwise code removed it in error), but we want to remove it to uphold scoping rules, while also keeping all other bindings intact
  divUn : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄ Ω} →                                  Γ₁ ⨾ Ω ÷ Γ₂  ≡ Γ₃ → -- Recurse, using Γ₃ as an intermediate value
                                                                           qualifierOf t ≡ un → -- Rule applies only for unrestricted vars
                                                                                      x ↦ t ∈* Γ₃ → -- Binding should not have disappeared
                                                                             Γ₃ - x ↦ t ≡ Γ₄  → -- Result context Γ₄ must be Γ₃ but with the x ↦ t binding deleted
                                                                             Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  -- For aff qualified types, we allow them to both be in the returned context (in which case we remove them, see above) or not, as they may or may not be used
  divAffUsed : ∀ {x t Γ₁ Γ₂ Γ₃ Ω} → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃ → qualifierOf t ≡ aff → x ↦ t ∉* Γ₃ → Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ t) ≡ Γ₃
  divAffNotUsed : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄ Ω} → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃ → qualifierOf t ≡ aff → x ↦ t ∈* Γ₃ → Γ₃ - x ↦ t ≡ Γ₄  → Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  divRel : ∀ {x t Γ₁ Γ₂ Γ₃ Γ₄ Ω} → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃ → qualifierOf t ≡ rel → x ↦ t ∈* Γ₃ →  x ↦ t ∈ Ω → Γ₃ - x ↦ t ≡ Γ₄ → Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ t) ≡ Γ₄

  -- For lin/ord qualified types, we enforce usage by requiring that the returned context does not contain them
  divMustuse : ∀ {x t Γ₁ Γ₂ Γ₃ Ω} → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃ → (qualifierOf t ≡ lin  ⊎ qualifierOf t ≡ ord) →  x ↦ t ∉* Γ₃ → Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ t) ≡ Γ₃

÷-unique : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Ω} → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃ → Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₄ → Γ₃ ≡ Γ₄
÷-unique (divEmpty _ _) (divEmpty _ _) = refl
÷-unique (divUn sub₁ _ _ sub-gives-res₁) (divUn  sub₂ _ _ sub-gives-res₂) = case ÷-unique sub₁ sub₂ of λ { refl → deleteBinding-unique sub-gives-res₁ sub-gives-res₂ }
÷-unique (divUn _ t-un _ _) (divMustuse _ t-lin-ord _) = [ (λ t-lin → case trans (sym t-lin) t-un of λ ()) , ((λ t-ord → case trans (sym t-ord) t-un of λ ()) ) ] t-lin-ord
÷-unique (divMustuse _ t-lin-ord _) (divUn _ t-un _ _) = [ (λ t-lin → case trans (sym t-lin) t-un of λ ()) , ((λ t-ord → case trans (sym t-ord) t-un of λ ()) ) ] t-lin-ord
÷-unique (divMustuse sub₁ _ _) (divMustuse sub₂ _ _) = ÷-unique sub₁ sub₂
÷-unique (divAffUsed sub₁ _ _) (divAffUsed sub₂ _ _) = ÷-unique sub₁ sub₂
÷-unique (divAffNotUsed sub₁ _ _ sub-gives-res₁) (divAffNotUsed sub₂ _ _ sub-gives-res₂) = case ÷-unique sub₁ sub₂ of λ {refl → deleteBinding-unique sub-gives-res₁ sub-gives-res₂}
÷-unique (divAffUsed sub₁ _ not-in-res) (divAffNotUsed sub₂ _ in-res _) = case ÷-unique sub₁ sub₂ of λ {refl → contradiction in-res not-in-res}
÷-unique (divUn _ t-un _ _) (divAffUsed _ t-aff _) = contradiction (trans (sym t-aff) t-un) (λ ())
÷-unique (divUn x t-un x₂ x₃) (divAffNotUsed x₄ t-aff x₆ x₇) = contradiction (trans (sym t-aff) t-un) (λ ())
÷-unique (divAffUsed x t-aff x₂) (divUn x₃ t-un x₅ x₆) = contradiction (trans (sym t-aff) t-un) (λ ())
÷-unique (divAffUsed x t-aff x₂) (divMustuse x₃ t-lin-ord x₅) =  [ (λ t-lin → case trans (sym t-lin) t-aff of λ ()) , ((λ t-ord → case trans (sym t-ord) t-aff of λ ()) ) ] t-lin-ord
÷-unique a@(divAffNotUsed x x₁ x₂ x₃) b@(divUn x₄ x₅ x₆ x₇) = sym $ ÷-unique b a
÷-unique (divAffNotUsed sub₂ _ in-res _) (divAffUsed sub₁ _ not-in-res) = case ÷-unique sub₁ sub₂ of λ {refl → contradiction in-res not-in-res}
÷-unique (divAffNotUsed x t-aff x₂ x₃) (divMustuse x₄ t-lin-ord x₆) = [ (λ t-lin → case trans (sym t-lin) t-aff of λ ()) , ((λ t-ord → case trans (sym t-ord) t-aff of λ ()) ) ] t-lin-ord
÷-unique a@(divMustuse x x₁ x₂) b@(divAffUsed x₃ x₄ x₅) = sym $ ÷-unique b a
÷-unique a@(divMustuse x x₁ x₂) b@(divAffNotUsed x₃ x₄ x₅ x₆) = sym $ ÷-unique b a
÷-unique (divRel sub₁ is-rel _ elem sub-gives-res₁) (divRel sub₂ _ _ _ sub-gives-res₂) = case ÷-unique sub₁ sub₂ of λ { refl → deleteBinding-unique sub-gives-res₁ sub-gives-res₂}
÷-unique (divRel sub₁ is-rel _ elem sub-gives-res₁) (divUn _ is-un _ _) = contradiction (trans (sym is-rel) is-un) λ ()
÷-unique (divRel sub₁ is-rel _ elem sub-gives-res₁) (divAffUsed _ is-aff _) = contradiction (trans (sym is-rel) is-aff) λ ()
÷-unique (divRel sub₁ is-rel _ elem sub-gives-res₁) (divAffNotUsed _ is-aff _ _) = contradiction (trans (sym is-rel) is-aff) λ ()
÷-unique (divRel sub₁ t-rel  _ elem sub-gives-res₁) (divMustuse _ t-lin-ord _) =  [ (λ t-lin → case trans (sym t-lin) t-rel of λ ()) , ((λ t-ord → case trans (sym t-ord) t-rel of λ ()) ) ] t-lin-ord
÷-unique a@(divUn x x₁ x₂ x₃) b@(divRel x₄ x₅ x₆ x₇ x₈) = sym $ ÷-unique b a
÷-unique a@(divAffUsed x x₁ x₂) b@(divRel x₃ x₄ x₅ x₆ x₇) = sym $ ÷-unique b a
÷-unique a@(divAffNotUsed x x₁ x₂ x₃) b@(divRel x₄ x₅ x₆ x₇ x₈) = sym $ ÷-unique b a
÷-unique a@(divMustuse x x₁ x₂) b@(divRel x₃ x₄ x₅ x₆ x₇) = sym $ ÷-unique b a

divideContext : (Γ₁ : TypingContext) (Ω : TypingContext) (Γ₂ : TypingContext) → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ Γ₂ ≡ Γ₃)
divideContext Γ₁ Ω ∅ = yes (Γ₁ , divEmpty Γ₁ Ω)
divideContext Γ₁ Ω (Γ₂ , x ↦ T) with divideContext Γ₁ Ω Γ₂
... | no nosub = no λ {
  (Γ₄ , divUn {Γ₃ = Γ₃} sub _ _ _) → contradiction (Γ₃ , sub) nosub ;
  (Γ₃ , divAffUsed sub _ _) → contradiction (Γ₃ , sub) nosub ;
  (Γ₄ , divAffNotUsed {Γ₃ = Γ₃} sub _ _ _) → contradiction (Γ₃ , sub) nosub ;
  (Γ₃ , divMustuse sub _ _) → contradiction (Γ₃ , sub) nosub ;
  (Γ₄ , divRel {Γ₃ = Γ₃} sub _ _ _ _) → contradiction (Γ₃ , sub) nosub }
... | yes (Γ₃ , sub) = qualifierCases T div-un div-lin div-ord div-aff div-rel
  where
    div-un : qualifierOf T ≡ un → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)
    div-lin : qualifierOf T ≡ lin → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)
    div-ord : qualifierOf T ≡ ord → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)
    div-aff : qualifierOf T ≡ aff → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)
    div-rel : qualifierOf T ≡ rel → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)
    div-lin-ord : (qualifierOf T ≡ lin) ⊎ (qualifierOf T ≡ ord) → Dec (Σ[ Γ₃ ∈ TypingContext ] Γ₁ ⨾ Ω ÷ (Γ₂ , x ↦ T) ≡ Γ₃)

    div-un T-un with x ↦ T ∈*? Γ₃
    ... | no not-elem = no λ {
      (Γ₄ , divUn sub' _ elem _) → case ÷-unique sub sub' of λ {refl → contradiction elem not-elem} ;
      (Γ₄ , divAffUsed _ T-aff _) → contradiction (trans (sym T-aff) T-un) (λ ()) ;
      (Γ₄ , divAffNotUsed _ T-aff _ _) → contradiction (trans (sym T-aff) T-un) (λ ()) ;
      (Γ₄ , divMustuse _ T-lin-ord _) → [ (λ T-lin → case trans (sym T-lin) T-un of λ ()) , ((λ T-ord → case trans (sym T-ord) T-un of λ ()) ) ] T-lin-ord ;
      (Γ₄ , divRel sub' _ elem _ _) → case ÷-unique sub sub' of λ {refl → contradiction elem not-elem} }
    ... | yes elem with deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ₃ x T (∈*⇒∈ elem)
    ... | Γ₄ , Γ₄-proof = yes (Γ₄ , (divUn sub T-un elem Γ₄-proof))

    div-lin T-lin = div-lin-ord $ inj₁ T-lin
    div-ord T-ord = div-lin-ord $ inj₂ T-ord

    div-lin-ord T-lin-ord with x ↦ T ∈*? Γ₃
    ... | yes elem = no λ {
      (Γ₄ , divUn p T-un x₁ x₂) → [ (λ T-lin → case trans (sym T-lin) T-un of λ ()) , ((λ T-ord → case trans (sym T-ord) T-un of λ ()) ) ] T-lin-ord ;
      (Γ₄ , divAffUsed p T-aff x₁) → [ (λ T-lin → case trans (sym T-lin) T-aff of λ ()) , ((λ T-ord → case trans (sym T-ord) T-aff of λ ()) ) ] T-lin-ord  ;
      (Γ₄ , divAffNotUsed p T-aff x₁ x₂) → [ (λ T-lin → case trans (sym T-lin) T-aff of λ ()) , ((λ T-ord → case trans (sym T-ord) T-aff of λ ()) ) ] T-lin-ord  ;
      (Γ₄ , divMustuse sub' _ not-elem) → case ÷-unique sub sub' of λ {refl → contradiction elem not-elem} ;
      (Γ₄ , divRel _ T-rel _ _ _) →  [ (λ T-lin → case trans (sym T-lin) T-rel of λ ()) , ((λ T-ord → case trans (sym T-ord) T-rel of λ ()) ) ] T-lin-ord }
    ... | no not-elem = yes (Γ₃ , divMustuse sub T-lin-ord not-elem)

    div-aff T-aff with x ↦ T ∈*? Γ₃
    ... | no not-elem = yes (Γ₃ , divAffUsed sub T-aff not-elem)
    ... | yes elem with deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ₃ x T (∈*⇒∈ elem)
    ... | Γ₄ , Γ₄-proof = yes (Γ₄ , divAffNotUsed sub T-aff elem Γ₄-proof)
    
    div-rel T-rel with x ↦ T ∈*? Γ₃
    ... | no x∉Γ₃ = no λ {
        (Γ₄ , divUn _ T-un _ _) → contradiction (trans (sym T-un) T-rel) (λ ());
        (Γ₄ , divAffUsed _ T-aff _) →  contradiction (trans (sym T-aff) T-rel) (λ ());
        (Γ₄ , divAffNotUsed _ T-aff _ _) →  contradiction (trans (sym T-aff) T-rel) (λ ());
        (Γ₄ , divRel sub' _ x∈Γ₃ _ _) → case ÷-unique sub sub' of λ { refl → contradiction x∈Γ₃ x∉Γ₃ };
        (Γ₄ , divMustuse _ T-lin-ord _ ) → [ (λ T-lin → case trans (sym T-lin) T-rel of λ ()) , ((λ T-ord → case trans (sym T-ord) T-rel of λ ()) ) ] T-lin-ord }
    ... | yes x∈Γ₃ with ((x ↦ T ∈? Ω) {_≟ₜ_})
    ... | no x∉Ω = no λ {
        (Γ₄ , divUn _ T-un _ _) → contradiction (trans (sym T-un) T-rel) (λ ());
        (Γ₄ , divAffUsed _ T-aff _) →  contradiction (trans (sym T-aff) T-rel) (λ ());
        (Γ₄ , divAffNotUsed _ T-aff _ _) →  contradiction (trans (sym T-aff) T-rel) (λ ());
        (Γ₄ , divRel sub' _ x∈Γ₃ x∈Ω _) → case ÷-unique sub sub' of λ { refl → contradiction x∈Ω x∉Ω };
        (Γ₄ , divMustuse _ T-lin-ord _ ) → [ (λ T-lin → case trans (sym T-lin) T-rel of λ ()) , ((λ T-ord → case trans (sym T-ord) T-rel of λ ()) ) ] T-lin-ord }
    ... | yes x∈Ω with deleteBinding {_≟ᵥ_ = _≟ₜ_} Γ₃ x T (∈*⇒∈ x∈Γ₃)
    ... | Γ₄ , Γ₄-proof = yes (Γ₄ , divRel sub T-rel x∈Γ₃ x∈Ω Γ₄-proof)

-- Qualifier-dependent context intersection: for a given q, non-q variables must appear in both contexts, while q variables can appear in only one (in which case they are dropped) or both (in whcih case they are kept)
data _∩[_]_≡_ : TypingContext → Qualifier → TypingContext → TypingContext → Set where
  intersectEmptyR : ∀ {Γ q} → Γ ∩[ q ] ∅ ≡ ∅
  intersectEmptyL : ∀ {Γ q} → ∅ ∩[ q ] Γ ≡ ∅
  intersectNonQ : ∀ {Γ₁ Γ₂ Γ x T q} → qualifierOf T ≢ q → Γ₁ ∩[ q ] Γ₂ ≡ Γ → x ↦ T ∈ Γ₁  → Γ₁ ∩[ q ]  (Γ₂ , x ↦ T) ≡ (Γ , x ↦ T)
  intersectQKeep : ∀  {Γ₁ Γ₂ Γ x T q} → qualifierOf T ≡ q →  Γ₁ ∩[ q ] Γ₂ ≡ Γ → x ↦ T ∈ Γ₁ → Γ₁ ∩[ q ] (Γ₂ , x ↦ T) ≡ (Γ , x ↦ T)
  intersectQDrop : ∀  {Γ₁ Γ₂ Γ x T q} → qualifierOf T ≡ q →  Γ₁ ∩[ q ] Γ₂ ≡ Γ → x ↦ T ∉ Γ₁ → Γ₁ ∩[ q ] (Γ₂ , x ↦ T) ≡ Γ

contextIntersection : {q : Qualifier} (Γ₁ Γ₂ : TypingContext) → Dec (Σ TypingContext (λ Γ → Γ₁ ∩[ q ] Γ₂ ≡ Γ))
contextIntersection ∅ ∅ = yes (∅ , intersectEmptyR)
contextIntersection ∅ (Γ₂ , x ↦ x₁) = yes (∅ , intersectEmptyL)
contextIntersection Γ₁ ∅ = yes (∅ , intersectEmptyR)
contextIntersection {q} Γ₁@(_ , _ ↦ _) (Γ₂ , x ↦ T) with contextIntersection Γ₁ Γ₂ | qualifierOf T ≟q q | (x ↦ T ∈? Γ₁) {_≟ᵥ_ = _≟ₜ_}
... | no nosub | _ | _ = no λ {
  (_ , intersectNonQ  {Γ = Γ} _ Γ-proof _) → contradiction (Γ , Γ-proof) nosub ;
  (_ , intersectQKeep {Γ = Γ} _ Γ-proof _) → contradiction (Γ , Γ-proof) nosub ;
  (_ , intersectQDrop {Γ = Γ} _ Γ-proof _) → contradiction (Γ , Γ-proof) nosub}
... | yes (Γ , Γ-proof) | yes is-q | yes in-Γ₁ = yes ((Γ , x ↦ T) , intersectQKeep is-q Γ-proof in-Γ₁)
... | yes (Γ , Γ-proof) | yes is-q | no not-in-Γ₁ = yes (Γ , (intersectQDrop is-q Γ-proof not-in-Γ₁)) 
... | yes (Γ , Γ-proof) | no not-q | yes in-Γ₁ = yes ((Γ , x ↦ T) , (intersectNonQ not-q Γ-proof in-Γ₁))
... | yes (Γ , Γ-proof) | no not-q | no not-in-Γ₁ = no λ {
  (_ , intersectNonQ _ _ in-Γ₁) → contradiction in-Γ₁ not-in-Γ₁ ;
  (_ , intersectQKeep is-q _ _) → contradiction is-q not-q ;
  (_ , intersectQDrop is-q _ _) → contradiction is-q not-q}

contextIntersection-unique : ∀ {Γ₁ Γ₂ Γ Γ' q} → Γ₁ ∩[ q ] Γ₂ ≡ Γ → Γ₁ ∩[ q ] Γ₂ ≡ Γ' → Γ ≡ Γ'
contextIntersection-unique intersectEmptyR intersectEmptyR = refl
contextIntersection-unique intersectEmptyR intersectEmptyL = refl
contextIntersection-unique intersectEmptyL intersectEmptyR = refl
contextIntersection-unique intersectEmptyL intersectEmptyL = refl
contextIntersection-unique intersectEmptyL (intersectQDrop _ sub _) = contextIntersection-unique intersectEmptyL sub
contextIntersection-unique (intersectNonQ {x = x} {T = T} _ sub₁ _) (intersectNonQ _ sub₂ _) = cong ((_, x ↦ T)) (contextIntersection-unique sub₁ sub₂)
contextIntersection-unique (intersectNonQ not-q _ _) (intersectQKeep is-q _ _) = contradiction is-q not-q
contextIntersection-unique (intersectNonQ not-q _ _) (intersectQDrop is-q _ _) = contradiction is-q not-q
contextIntersection-unique (intersectQKeep is-q _ _) (intersectNonQ not-q _ _) = contradiction is-q not-q
contextIntersection-unique (intersectQKeep _ sub₁ _) (intersectQKeep _ sub₂ _) = cong _ (contextIntersection-unique sub₁ sub₂)
contextIntersection-unique (intersectQKeep _ _ elem) (intersectQDrop _ _ not-elem) = contradiction elem not-elem
contextIntersection-unique (intersectQDrop _ sub _) intersectEmptyL = contextIntersection-unique sub intersectEmptyL
contextIntersection-unique (intersectQDrop is-q _ _) (intersectNonQ not-q _ _) = contradiction is-q not-q
contextIntersection-unique (intersectQDrop _ _ not-elem) (intersectQKeep _ _ elem) = contradiction elem not-elem
contextIntersection-unique (intersectQDrop x a x₁) (intersectQDrop x₂ b x₃) = contextIntersection-unique a b

_∩ₐ_≡_ : TypingContext → TypingContext → TypingContext → Set
Γ₁ ∩ₐ Γ₂ ≡ Γ₃ = Γ₁ ∩[ aff ] Γ₂ ≡ Γ₃

_∩ᵣ_≡_ : TypingContext → TypingContext → TypingContext → Set
Γ₁ ∩ᵣ Γ₂ ≡ Γ₃ = Γ₁ ∩[ rel ] Γ₂ ≡ Γ₃

_⟨⟨_⟩⟩ : REL Qualifier TypingContext 0ℓ
q ⟨⟨ Γ ⟩⟩ = All (λ _ ty → q ⟨ ty ⟩) Γ

canContainCtx? : Decidable _⟨⟨_⟩⟩
canContainCtx? q Γ = all? (λ _ ty → canContain? q ty) Γ
