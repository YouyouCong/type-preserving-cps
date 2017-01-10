module stlc where

open import Data.Nat

-- the language

-- types
data STy : Set where
  Int : STy
  Arrow : STy → STy → STy

-- contexts
data SCon : Set where
  • : SCon
  _,_ : SCon → STy → SCon

-- variables
data _∋_ : SCon → STy → Set where
  z : {Γ : SCon} {A : STy} → (Γ , A) ∋ A
  s : {Γ : SCon} {A B : STy} → Γ ∋ A → (Γ , B) ∋ A

-- terms
data STm : SCon → STy → Set where
  var : {Γ : SCon} {A : STy} → Γ ∋ A → STm Γ A
  lam : {Γ : SCon} {A B : STy} → STm (Γ , A) B → STm Γ (Arrow A B)
  app : {Γ : SCon} {A B : STy} → STm Γ (Arrow A B) → STm Γ A → STm Γ B

-- examples

-- Γ , y : int ⊢ (λx. x) y : int
term1 : STm (• , Int) Int
term1 = app (lam (var z)) (var z)

-- Γ , x : int ⊬ x x : int
-- term2 : STm (• , Int) Int
-- term2 = app {• , Int} (var z) (var z)

-- • ⊬ x : int
-- term3 : STm • Int
-- term3 = var z

-- CPS language

-- types
data CSTy : Set where
  Int : CSTy
  Arrowt : CSTy → CSTy → CSTy
  Arrowc : CSTy → CSTy → CSTy

-- contexts
data CSCon : Set where
  • : CSCon
  _,_ : CSCon → CSTy → CSCon

-- variables
data _∋c_ : CSCon → CSTy → Set where
  z : {Γ : CSCon} {A : CSTy} → (Γ , A) ∋c A
  s : {Γ : CSCon} {A B : CSTy} → Γ ∋c A → (Γ , B) ∋c A

-- terms
data CSTm : CSCon → CSCon → CSTy → Set where
  vart : {Γ Γ' : CSCon} {A : CSTy} → Γ ∋c A → CSTm Γ Γ' A
  varc : {Γ Γ' : CSCon} {A : CSTy} → Γ' ∋c A → CSTm Γ Γ' A
  lamt : {Γ Γ' : CSCon} {A B : CSTy} → CSTm (Γ , A) Γ' B → CSTm Γ Γ' (Arrowt A B)
  lamc : {Γ Γ' : CSCon} {A B : CSTy} → CSTm Γ (Γ' , A) B → CSTm Γ Γ' (Arrowc A B)
  appt : {Γ Γ' : CSCon} {A B : CSTy} → CSTm Γ Γ' (Arrowt A B) → CSTm Γ Γ' A → CSTm Γ Γ' B
  appc : {Γ Γ' : CSCon} {A B : CSTy} → CSTm Γ Γ' (Arrowc A B) → CSTm Γ Γ' A → CSTm Γ Γ' B

-- CPS translation

mutual
  -- translation for types
  ÷ : STy → CSTy
  ÷ A = Arrowc (Arrowc (+ A) Int) Int

  + : STy → CSTy
  + Int = Int
  + (Arrow A B) = Arrowt (÷ A) (÷ B)

-- translation for contexts
÷-Con : SCon → CSCon
÷-Con • = •
÷-Con (Γ , A) = ÷-Con Γ , ÷ A

-- translation for variables
÷-var : {Γ : SCon} {A : STy} → Γ ∋ A → ÷-Con Γ ∋c ÷ A
÷-var z = z
÷-var (s x) = s (÷-var x)

-- weakening

-- Within Γ n ensures n <= length Γ
data Within : CSCon → ℕ → Set where
  okzero : {Γ : CSCon} → Within Γ zero
  oksuc : {Γ : CSCon} {n : ℕ} {A : CSTy} → Within Γ n → Within (Γ , A) (suc n)

-- add T to Γ as the nth element
add-to-nth : (Γ : CSCon) → (n : ℕ) → Within Γ n → CSTy → CSCon
add-to-nth Γ zero okzero T = Γ , T
add-to-nth • (suc n) () T
add-to-nth (Γ , A) (suc n) (oksuc p) T = add-to-nth Γ n p T , A

-- shift the variable x if the index is greater than or equal to n
varc-shift-above-n : {Γ : CSCon} {A B : CSTy} →
                     Γ ∋c A → (n : ℕ) → {p : Within Γ n} → add-to-nth Γ n p B ∋c A
varc-shift-above-n {Γ} {A} {B} x zero {okzero} = s x
varc-shift-above-n {Γ , .A} {A} {B} z (suc n) {oksuc p} = z
varc-shift-above-n (s x) (suc n) {oksuc p} = s (varc-shift-above-n x n {p})

-- shift variables in a term
term-shift-above-n : {Γ Γ' : CSCon} {A B : CSTy} →
                     CSTm Γ Γ' A → (n : ℕ) → {p : Within Γ' n} →
                     CSTm Γ (add-to-nth Γ' n p B) A
term-shift-above-n (vart x) n {p} = vart x
term-shift-above-n (varc x) n {p} = varc (varc-shift-above-n x n {p})
term-shift-above-n (lamt t) n {p} = lamt (term-shift-above-n t n {p})
term-shift-above-n (lamc {Γ} {Γ'} {A} {B} t) n {p}
  = lamc (term-shift-above-n t (suc n) {oksuc p}) 
term-shift-above-n (appt t₁ t₂) n {p} 
  = appt (term-shift-above-n t₁ n {p}) (term-shift-above-n t₂ n {p})
term-shift-above-n (appc t₁ t₂) n {p} 
  = appc (term-shift-above-n t₁ n {p}) (term-shift-above-n t₂ n {p})

-- weakening
wkc : {Γ Γ' : CSCon} {A B : CSTy} → CSTm Γ Γ' B → CSTm Γ (Γ' , A) B
wkc (vart x) = vart x
wkc (varc x) = varc (s x)
wkc (lamt t) = lamt (wkc t)
wkc (lamc t) = lamc (term-shift-above-n t 1 {oksuc okzero})
wkc (appt t₁ t₂) = appt (wkc t₁) (wkc t₂)
wkc (appc t₁ t₂) = appc (wkc t₁) (wkc t₂)

-- CPS translation
cps : {Γ : SCon} {A : STy} → STm Γ A → CSTm (÷-Con Γ) • (÷ A)
cps (var x) = vart (÷-var x)
cps (lam t) with wkc (lamt (cps t))
... | t' = lamc (appc (varc z) t')
cps (app t₁ t₂) with wkc (cps t₁) | wkc (wkc (cps t₂))
... | t₁' | t₂' = lamc (appc t₁' (lamc (appc (appt (varc z) t₂') (varc (s z)))))


