-- Type-safe representation of the λ calculus with Π types by Altenkirch & Kaposi (POPL 2016)
-- and its CPS translation 

module dtlc where

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Level

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

coe : ∀ {i} {A B : Set i} → A ≡ B → A → B
coe refl a = a

-- the language

mutual
  -- contexts
  data Con : Set where
    • : Con
    _,_ : (Γ : Con) → Ty Γ → Con

  infixl 5 _,_

  -- types
  data Ty : Con → Set where
    _[_]T : {Γ Δ : Con} → Ty Δ → Tms Γ Δ → Ty Γ
    Π : {Γ : Con} → (A : Ty Γ) → (B : Ty (Γ , A)) → Ty Γ
    U : {Γ : Con} → Ty Γ
    El : {Γ : Con} → (A : Tm Γ U) → Ty Γ

  infixl 7 _[_]T

  -- substitutions
  data Tms : Con → Con → Set where
    ε : {Γ : Con} → Tms Γ •
    _,_ : {Γ Δ : Con} {A : Ty Δ} →
          (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T) → Tms Γ (Δ , A)
    id : {Γ : Con} → Tms Γ Γ
    _∘_ : {Γ Δ Σ : Con} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
    π₁ : {Γ Δ : Con} {A : Ty Δ} → Tms Γ (Δ , A) → Tms Γ Δ

  infix 6 _∘_

  -- terms
  data Tm : (Γ : Con) → Ty Γ → Set where
    lam : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
          Tm (Γ , A) B → Tm Γ (Π A B)
    app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ , A)} →
          Tm Γ (Π A B) → Tm (Γ , A) B
    π₂ : {Γ Δ : Con} {A : Ty Δ} →
         (δ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁ δ ]T)
    _[_]t : {Γ Δ : Con} {A : Ty Δ} →
            Tm Δ A → (δ : Tms Γ Δ) → Tm Γ (A [ δ ]T)

-- variables
wk : {Γ : Con} {A : Ty Γ} → Tms (Γ , A) Γ
wk = π₁ id

vz : {Γ : Con} {A : Ty Γ} → Tm (Γ , A) (A [ wk ]T)
vz = π₂ id

vs : {Γ : Con} {A B : Ty Γ} → Tm Γ A → Tm (Γ , B) (A [ wk ]T)
vs x = x [ wk ]t

TmΓ≡ : {Γ : Con} {A₀ A₁ : Ty Γ} (A₂ : A₀ ≡ A₁) →
        Tm Γ A₀ ≡ Tm Γ A₁
TmΓ≡ {Γ} refl = refl

-- postulates
postulate
  [id]T : {Γ : Con} {A : Ty Γ} → A [ id ]T ≡ A
  [][]T : {Γ Δ Σ : Con} {A : Ty Σ} (δ : Tms Δ Σ) →
         (σ : Tms Γ Δ) → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
  U[] : {Γ Δ : Con} {δ : Tms Γ Δ} → U [ δ ]T ≡ U
  El[] : {Γ Δ : Con} {A : Tm Δ U} {δ : Tms Γ Δ} →
         El A [ δ ]T ≡ El (coe (TmΓ≡ U[]) (A [ δ ]t))

_↑_ : {Γ Δ : Con} → (δ : Tms Γ Δ) (A : Ty Δ) → Tms (Γ , A [ δ ]T) (Δ , A)
δ ↑ A = (δ ∘ π₁ id) , coe (TmΓ≡ ([][]T δ (π₁ id))) (π₂ id)

postulate
  Π[] : ∀ {Γ Δ A B} → (δ : Tms Γ Δ) → 
       (Π A B) [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ↑ A ]T)

-- application
<_> : {Γ : Con}{A : Ty Γ} → Tm Γ A → Tms Γ (Γ , A)
< t > = id , coe (TmΓ≡ ([id]T ⁻¹)) t

infix 4 <_>

_$_ : {Γ : Con}{A : Ty Γ}{B : Ty (Γ , A)}
      (t : Tm Γ (Π A B))(u : Tm Γ A) → Tm Γ (B [ < u > ]T)
t $ u = (app t) [ < u > ]t

infixl 5 _$_

-- examples

-- • ⊢ λt:U.t
term1 : Tm • (Π U U)
term1 = lam (coe (TmΓ≡ U[]) vz)

-- • ⊢ λt:U.λx:t.x
term2 : Tm • (Π U
              (Π (El (coe (TmΓ≡ U[]) vz))
                  (El (coe (TmΓ≡ U[]) (coe (TmΓ≡ U[]) vz [ wk ]t)))))
term2 = lam (lam (coe (TmΓ≡ El[]) vz))

-- CPS language

mutual
  -- contexts
  data CCon : Set where
    • : CCon
    _,t_ : (Γ : CCon) → {Γ' : CCon} → CTy Γ Γ' → CCon
    _,c_ : {Γ : CCon} → (Γ' : CCon) → CTy Γ Γ' → CCon

  infixl 5 _,t_
  infixl 5 _,c_

  -- types
  data CTy : CCon → CCon → Set where
    U : {Γ Γ' : CCon} → CTy Γ Γ'
    El : {Γ Γ' : CCon} → (A : CTm Γ Γ' U) → CTy Γ Γ'
    Πt : {Γ Γ' : CCon} → (A : CTy Γ Γ') → (B : CTy (Γ ,t A) Γ') → CTy Γ Γ'
    Πc : {Γ Γ' : CCon} → (A : CTy Γ Γ') → (B : CTy Γ (Γ' ,c A)) → CTy Γ Γ'
    _[_]T : {Γ Γ' Δ Δ' : CCon} → CTy Δ Δ' → CTms Γ Γ' Δ Δ' → CTy Γ Γ'

  -- substitutions
  data CTms : CCon → CCon → CCon → CCon → Set where
    ε : {Γ Γ' : CCon} → CTms Γ Γ' • •
    _,t_ : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} →
           (δ : CTms Γ Γ' Δ Δ') → CTm Γ Γ' (A [ δ ]T) → CTms Γ Γ' (Δ ,t A) Δ'
    _,c_ : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} →
           (δ : CTms Γ Γ' Δ Δ') → CTm Γ Γ' (A [ δ ]T) → CTms Γ Γ' Δ (Δ' ,c A)
    id : {Γ Γ' : CCon} → CTms Γ Γ' Γ Γ'
    _∘_ : {Γ Γ' Δ Δ' Σ Σ' : CCon} → CTms Δ Δ' Σ Σ' → CTms Γ Γ' Δ Δ' → CTms Γ Γ' Σ Σ'
    π₁t : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} → CTms Γ Γ' (Δ ,t A) Δ' → CTms Γ Γ' Δ Δ'
    π₁c : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} → CTms Γ Γ' Δ (Δ' ,c A) → CTms Γ Γ' Δ Δ'

  -- terms
  data CTm : (Γ Γ' : CCon) → CTy Γ Γ' → Set where
    lamt : {Γ Γ' : CCon} {A : CTy Γ Γ'} {B : CTy (Γ ,t A) Γ'} →
           CTm (Γ ,t A) Γ' B → CTm Γ Γ' (Πt A B)
    lamc : {Γ Γ' : CCon} {A : CTy Γ Γ'} {B : CTy Γ (Γ' ,c A)} →
           CTm Γ (Γ' ,c A) B → CTm Γ Γ' (Πc A B)
    appt : {Γ Γ' : CCon} {A : CTy Γ Γ'} {B : CTy (Γ ,t A) Γ'} →
           CTm Γ Γ' (Πt A B) → CTm (Γ ,t A) Γ' B
    appc : {Γ Γ' : CCon} {A : CTy Γ Γ'} {B : CTy Γ (Γ' ,c A)} →
           CTm Γ Γ' (Πc A B) → CTm Γ (Γ' ,c A) B
    π₂t : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} →
          (δ : CTms Γ Γ' (Δ ,t A) Δ') → CTm Γ Γ' (A [ π₁t δ ]T)
    π₂c : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} →
          (δ : CTms Γ Γ' Δ (Δ' ,c A)) → CTm Γ Γ' (A [ π₁c δ ]T)
    _[_]t : {Γ Γ' Δ Δ' : CCon} {A : CTy Δ Δ'} →
            CTm Δ Δ' A → (δ : CTms Γ Γ' Δ Δ') → CTm Γ Γ' (A [ δ ]T)

-- variables
wkt : {Γ Γ' : CCon} {A : CTy Γ Γ'} → CTms (Γ ,t A) Γ' Γ Γ'
wkt = π₁t id

wkc : {Γ Γ' : CCon} {A : CTy Γ Γ'} → CTms Γ (Γ' ,c A) Γ Γ'
wkc = π₁c id

vzt : {Γ Γ' : CCon} {A : CTy Γ Γ'} → CTm (Γ ,t A) Γ' (A [ wkt ]T)
vzt = π₂t id

vzc : {Γ Γ' : CCon} {A : CTy Γ Γ'} → CTm Γ (Γ' ,c A) (A [ wkc ]T)
vzc = π₂c id

vst : {Γ Γ' : CCon} {A B : CTy Γ Γ'} → CTm Γ Γ' A → CTm (Γ ,t B) Γ' (A [ wkt ]T)
vst x = x [ wkt ]t

vsc : {Γ Γ' : CCon} {A B : CTy Γ Γ'} → CTm Γ Γ' A → CTm Γ (Γ' ,c B) (A [ wkc ]T)
vsc x = x [ wkc ]t

CTmΓ≡ : {Γ Γ' : CCon} {A₀ A₁ : CTy Γ Γ'} (A₂ : A₀ ≡ A₁) →
        CTm Γ Γ' A₀ ≡ CTm Γ Γ' A₁
CTmΓ≡ {Γ} {Γ'} refl = refl

-- postulates
postulate
  [id]T' : {Γ Γ' : CCon} {A : CTy Γ Γ'} → A [ id ]T ≡ A
  [][]T' : {Γ Γ' Δ Δ' Σ Σ' : CCon} {A : CTy Σ Σ'} (δ : CTms Δ Δ' Σ Σ') →
           (σ : CTms Γ Γ' Δ Δ') → _≡_ {zero} {CTy Γ Γ'} (A [ δ ]T [ σ ]T) (A [ δ ∘ σ ]T)
  ∘asc : {Γ Γ' Δ Δ' Σ Σ' E E' : CCon} {A : CTy E E'}
         (δ : CTms Σ Σ' E E') → (σ : CTms Δ Δ' Σ Σ') → (e : CTms Γ Γ' Δ Δ') → 
         _≡_ {zero} {CTy Γ Γ'} (A [ (δ ∘ σ) ∘ e ]T) (A [ δ ∘ (σ ∘ e) ]T)
  U[]' : {Γ Γ' Δ Δ' : CCon} {δ : CTms Γ Γ' Δ Δ'} → _≡_ {zero} {CTy Γ Γ'} (U [ δ ]T) U
  El[]' : {Γ Γ' Δ Δ' : CCon} {A : CTm Δ Δ' U} {δ : CTms Γ Γ' Δ Δ'} →
          _≡_ {zero} {CTy Γ Γ'} (El A [ δ ]T) (El (coe (CTmΓ≡ U[]') (A [ δ ]t)))

_↑t_ : {Γ Γ' Δ Δ' : CCon} → (δ : CTms Γ Γ' Δ Δ') (A : CTy Δ Δ') → 
       CTms (Γ ,t A [ δ ]T) Γ' (Δ ,t A) Δ'
δ ↑t A = (δ ∘ π₁t id) ,t coe (CTmΓ≡ ([][]T' δ (π₁t id))) (π₂t id)

_↑c_ : {Γ Γ' Δ Δ' : CCon} → (δ : CTms Γ Γ' Δ Δ') (A : CTy Δ Δ') → 
       CTms Γ (Γ' ,c A [ δ ]T) Δ (Δ' ,c A)
δ ↑c A = (δ ∘ π₁c id) ,c coe (CTmΓ≡ ([][]T' δ (π₁c id))) (π₂c id)

postulate
  Πt[] : ∀ {Γ Γ' Δ Δ' A B} → (δ : CTms Γ Γ' Δ Δ') → 
        (Πt A B) [ δ ]T ≡ Πt (A [ δ ]T) (B [ δ ↑t A ]T)
  Πc[] : ∀ {Γ Γ' Δ Δ' A B} → (δ : CTms Γ Γ' Δ Δ') → 
        (Πc A B) [ δ ]T ≡ Πc (A [ δ ]T) (B [ δ ↑c A ]T)

-- application
<_>t : {Γ Γ' : CCon}{A : CTy Γ Γ'} → CTm Γ Γ' A → CTms Γ Γ' (Γ ,t A) Γ'
< t >t = id ,t coe (CTmΓ≡ ([id]T' ⁻¹)) t

infix 4 <_>t

<_>c : {Γ Γ' : CCon}{A : CTy Γ Γ'} → CTm Γ Γ' A → CTms Γ Γ' Γ (Γ' ,c A)
< t >c = id ,c coe (CTmΓ≡ ([id]T' ⁻¹)) t

infix 4 <_>c

_$t_ : {Γ Γ' : CCon}{A : CTy Γ Γ'}{B : CTy (Γ ,t A) Γ'}
       (t : CTm Γ Γ' (Πt A B))(u : CTm Γ Γ' A) → CTm Γ Γ' (B [ < u >t ]T)
t $t u = (appt t) [ < u >t ]t

infix 5 _$t_

_$c_ : {Γ Γ' : CCon}{A : CTy Γ Γ'}{B : CTy Γ (Γ' ,c A)}
       (t : CTm Γ Γ' (Πc A B))(u : CTm Γ Γ' A) → CTm Γ Γ' (B [ < u >c ]T)
t $c u = (appc t) [ < u >c ]t

infix 5 _$c_

-- equalities necessary for the CPS translation
postulate
  wk↑<> : ∀ {Γ Γ' S A B t} {T : CTy (Γ ,t S) Γ'} → 
          Πc (T [ wkc {A = A} ∘ wkc {A = B} ]T) U ≡
          Πc (T [ ((wkt ∘ wkc) ∘ wkc) ↑t S ∘ < t >t ]T) U
         
SubPiU : {Γ Γ' Δ Δ' : CCon} → (A : CTy Δ Δ') → (δ : CTms Γ Γ' Δ Δ') → 
         (Πc (Πc A U) U) [ δ ]T ≡ Πc (Πc (A [ δ ]T) U) U
SubPiU {Γ} {Γ'} {Δ} {Δ'} A δ =
  begin
    (Πc (Πc {Δ} A U) U) [ δ ]T
  ≡⟨ Πc[] {Γ} {Γ'} {Δ} {Δ'} {Πc A U} {U} δ ⟩
    Πc (Πc {Δ} A U [ δ ]T) (U [ δ ↑c Πc A U ]T)
  ≡⟨ cong (λ x → Πc (Πc {Δ} A U [ δ ]T) x) 
          (U[]' {Γ} {Γ' ,c Πc A U [ δ ]T} {Δ} {Δ' ,c Πc A U} {δ ↑c Πc A U}) ⟩ 
    Πc (Πc {Δ} A U [ δ ]T) U
  ≡⟨ cong (λ x → Πc x U) (Πc[] {Γ} {Γ'} {Δ} {Δ'} {A} {U} δ) ⟩
    Πc (Πc {Γ} (A [ δ ]T) (U [ δ ↑c A ]T)) U
  ≡⟨ cong (λ x → Πc (Πc (A [ δ ]T) x) U) 
          (U[]' {Γ} {Γ' ,c A [ δ ]T} {Δ} {Δ' ,c A} {δ ↑c A}) ⟩
    Πc (Πc (A [ δ ]T) U) U
  ∎

Πc[]' : ∀ {Γ Γ' Δ' A} → (δ : CTms Γ Γ' Γ Δ') 
      → (Πc A U) [ δ ]T ≡ Πc (A [ δ ]T) U
Πc[]' {A = A} δ =
  begin
    (Πc A U) [ δ ]T
  ≡⟨ Πc[] δ ⟩
    Πc (A [ δ ]T) (U [ δ ↑c A ]T)
  ≡⟨ cong (λ x → Πc (A [ δ ]T) x) (U[]' {δ = δ ↑c A}) ⟩
    Πc (A [ δ ]T) U
  ∎

-- CPS translation
{-# NO_TERMINATION_CHECK #-}
mutual
  -- translation for contexts
  ÷-Con : Con → CCon
  ÷-Con • = •
  ÷-Con (Γ , T) = (÷-Con Γ ,t ÷ T)

  -- translation for substitutions
  ÷-Tms : ∀ {Γ Δ} → Tms Γ Δ → CTms (÷-Con Γ) • (÷-Con Δ) •
  ÷-Tms ε = ε
  ÷-Tms {Γ} {Δ , T} (δ , t) = ÷-Tms δ ,t coe (CTmΓ≡ (SubComTy T δ)) (cps t)
  ÷-Tms id = id
  ÷-Tms (δ ∘ σ) with ÷-Tms δ | ÷-Tms σ
  ... | δ' | σ' = δ' ∘ σ'
  ÷-Tms (π₁ {Γ} {Δ} {T} δ) with ÷-Tms δ
  ... | δ' = π₁t {÷-Con Γ} {•} {÷-Con Δ} {•} {÷ T} δ'

  -- translation for types
  ÷ : ∀ {Γ} → Ty Γ → CTy (÷-Con Γ) •
  ÷ A = Πc (Πc (+ A) U) U

  + : ∀ {Γ} → Ty Γ → CTy (÷-Con Γ) •
  + U = U
  + {Γ} (El t) = {!!} -- How should we translate this?
  + (Π A B) = Πt (÷ A) (÷ B)
  + (A [ δ ]T) = + A [ ÷-Tms δ ]T 

  -- translation for terms
  cps : {Γ : Con} {A : Ty Γ} → Tm Γ A → CTm (÷-Con Γ) • (÷ A)
  cps (lam {Γ} {A} {B} t) with cps t
  ... | t' with lamt t'
  ... | lt' with lt' [ π₁c {Γ' = • ,c Πc (+ (Π A B)) U} id ]t
  ... | wlt' with _$c_ {Γ' = • ,c Πc (+ (Π A B)) U} 
                       (coe (CTmΓ≡ (Πc[]' wkc)) 
                            (π₂c {Γ' = • ,c Πc (Πt (Πc (Πc (+ A) U) U) 
                                                   (Πc (Πc (+ B) U) U)) U}
                                 id))
                       wlt'
  ... | r with coe (CTmΓ≡ (U[]' {δ = id ,c coe (CTmΓ≡ ([id]T' ⁻¹)) wlt'})) r
  ... | r' = lamc r'
  cps (app {Γ} {A} {B} t) 
    = {!!}
   {- type checking does not terminate when filling in the blank with the following term:
      lamc {A = Πc (+ B) U}
           (coe (CTmΓ≡ U[]') 
                ((coe (CTmΓ≡ (SubPiU (+ (Π A B)) (wkt ∘ wkc)))
                      ((cps t) [ wkt {A = ÷ A} ∘ (wkc {A = Πc (+ B) U}) ]t)) $c 
                 (lamc {A = Πt (÷ A) (÷ B) [ wkt ∘ wkc ]T}
                       (coe (CTmΓ≡ U[]') 
                            ((coe (CTmΓ≡ (trans ([][]T' (((wkt ∘ wkc) ∘ wkc) ↑t ÷ A) 
                                                        < coe (CTmΓ≡ (trans ([][]T' wkt (wkc ∘ wkc)) 
                                                                            (sym (∘asc wkt wkc wkc)))) 
                                                              (vzt [ wkc ∘ wkc ]t) >t) 
                                                (SubPiU (+ B)
                                                        ((((wkt ∘ wkc) ∘ wkc) ↑t ÷ A) ∘
                                                         < coe (CTmΓ≡ (trans ([][]T' wkt (wkc ∘ wkc)) 
                                                                      (sym (∘asc wkt wkc wkc)))) 
                                                               (vzt [ wkc ∘ wkc ]t) >t)))) 
                                  ((coe (CTmΓ≡ (trans ([][]T' (wkt ∘ wkc) wkc) (Πt[] ((wkt ∘ wkc) ∘ wkc)))) 
                                        (vzc {A = Πt (÷ A) (÷ B) [ wkt ∘ wkc ]T})) $t 
                                   (coe (CTmΓ≡ {Γ = ÷-Con Γ ,t ÷ A}
                                               {Γ' = • ,c Πc (+ B) U ,c Πt (÷ A) (÷ B) [ wkt ∘ wkc ]T} 
                                               (trans ([][]T' wkt (wkc ∘ wkc)) (sym (∘asc wkt wkc wkc)))) 
                                        (vzt [ wkc ∘ wkc ]t)))) $c 
                             (coe (CTmΓ≡ (trans (trans ([][]T' wkc wkc) (Πc[]' (wkc ∘ wkc))) 
                                                (wk↑<> {T = + B}))) 
                                  (vsc {A = Πc (+ B) U [ wkc ]T} vzc))))))) -} 
  cps (π₂ {Γ} {Δ} {A} δ) with ÷-Tms δ
  ... | δ' with π₂t δ'
  ... | t' with SubPiU {÷-Con Γ} {•} {÷-Con Δ} {•} (+ A) (π₁t δ')
  ... | p rewrite (p ⁻¹) = t' 
  cps {.Γ} {A [ .δ ]T} (_[_]t {Γ} {Δ} t δ) with cps t | ÷-Tms δ
  ... | t' | δ' with t' [ δ' ]t | SubPiU {÷-Con Γ} {•} {÷-Con Δ} {•} (+ A) δ'
  ... | t'' | p rewrite (p ⁻¹) = t'' 

  -- substitutions commute with translation on types
  SubComTy : {Γ Δ : Con} → (A : Ty Δ) → (δ : Tms Γ Δ) 
           → ÷ (A [ δ ]T) ≡ (÷ A) [ ÷-Tms δ ]T
  SubComTy {Γ} {Δ} A δ = (SubPiU {÷-Con Γ} {•} {÷-Con Δ} {•} (+ A) (÷-Tms δ)) ⁻¹
