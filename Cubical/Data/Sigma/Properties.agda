{-

Basic properties about Σ-types

- Characterization of equality in Σ-types using transport ([pathSigma≡sigmaPath])

-}
{-# OPTIONS --cubical --safe --postfix-projections #-}
module Cubical.Data.Sigma.Properties where

open import Cubical.Data.Sigma.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Cubical.Data.Nat

private
  variable
    ℓ : Level
    A : Set ℓ
    B : (a : A) → Set ℓ


ΣPathP : ∀ {x y}
  → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y))
  → x ≡ y
ΣPathP eq = λ i → (fst eq i) , (snd eq i)

Σ≡-iso : {x y : Σ A B}  →
     Iso (Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)))
         (x ≡ y)
Σ≡-iso {A = A} {B = B} {x} {y} = (iso intro elim intro-elim elim-intro)
  where
    intro = ΣPathP

    elim : x ≡ y → Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y ))
    elim eq = (λ i → fst (eq i)) , λ i → snd (eq i)

    intro-elim : ∀ eq → intro (elim eq) ≡ eq
    intro-elim eq = refl

    elim-intro : ∀ eq → elim (intro eq) ≡ eq
    elim-intro eq = refl


Σ≡ : {x y : Σ A B}  →
     Σ (fst x ≡ fst y) (λ a≡ → PathP (λ i → B (a≡ i)) (snd x) (snd y)) ≃
     (x ≡ y)
Σ≡ {A = A} {B = B} {x} {y} = isoToEquiv (Σ≡-iso)

-- Alternative version for path in Σ-types, as in the HoTT book

sigmaPathTransport : (a b : Σ A B) → Set _
sigmaPathTransport {B = B} a b =
  Σ (fst a ≡ fst b) (λ p → transport (λ i → B (p i)) (snd a) ≡ snd b)

_Σ≡T_ : (a b : Σ A B) → Set _
a Σ≡T b = sigmaPathTransport a b

-- now we prove that the alternative path space a Σ≡ b is equal to the usual path space a ≡ b

-- forward direction

private
  pathSigma-π1 : {a b : Σ A B} → a ≡ b → fst a ≡ fst b
  pathSigma-π1 p i = fst (p i)

  filler-π2 : {a b : Σ A B} → (p : a ≡ b) → I → (i : I) → B (fst (p i))
  filler-π2 {B = B} {a = a} p i =
    fill (λ i → B (fst (p i)))
         (λ t → λ { (i = i0) → coe0→i (λ j → B (fst (p j))) t (snd a)
                  ; (i = i1) → snd (p t) })
         (inS (snd a))

  pathSigma-π2 : {a b : Σ A B} → (p : a ≡ b) →
    subst B (pathSigma-π1 p) (snd a) ≡ snd b
  pathSigma-π2 p i = filler-π2 p i i1

pathSigma→sigmaPath : (a b : Σ A B) → a ≡ b → a Σ≡T b
pathSigma→sigmaPath _ _ p = (pathSigma-π1 p , pathSigma-π2 p)

-- backward direction

private
  filler-comp : (a b : Σ A B) → a Σ≡T b → I → I → Σ A B
  filler-comp {B = B} a b (p , q) i =
    hfill (λ t → λ { (i = i0) → a
                   ; (i = i1) → (p i1 , q t) })
          (inS (p i , coe0→i (λ j → B (p j)) i (snd a)))

sigmaPath→pathSigma : (a b : Σ A B) → a Σ≡T b → (a ≡ b)
sigmaPath→pathSigma a b x i = filler-comp a b x i i1

-- first homotopy

private
  homotopy-π1 : (a b : Σ A B) →
    ∀ (x : a Σ≡T b) → pathSigma-π1 (sigmaPath→pathSigma a b x) ≡ fst x
  homotopy-π1 a b x i j = fst (filler-comp a b x j (~ i))

  homotopy-π2 : (a b : Σ A B) → (p : a Σ≡T b) → (i : I) →
             (transport (λ j → B (fst (filler-comp a b p j i))) (snd a) ≡ snd b)
  homotopy-π2 {B = B} a b p i j =
    comp (λ t → B (fst (filler-comp a b p t (i ∨ j))))
         (λ t → λ { (j = i0) → coe0→i (λ t → B (fst (filler-comp a b p t i)))
                                      t (snd a)
                  ; (j = i1) → snd (sigmaPath→pathSigma a b p t)
                  ; (i = i0) → snd (filler-comp a b p t j)
                  ; (i = i1) → filler-π2 (sigmaPath→pathSigma a b p) j t })
         (inS (snd a))

pathSigma→sigmaPath→pathSigma : {a b : Σ A B} →
  ∀ (x : a Σ≡T b) → pathSigma→sigmaPath _ _ (sigmaPath→pathSigma a b x) ≡ x
pathSigma→sigmaPath→pathSigma {a = a} p i =
  (homotopy-π1 a _ p i , homotopy-π2 a _ p (~ i))

-- second homotopy

sigmaPath→pathSigma→sigmaPath : {a b : Σ A B} →
  ∀ (x : a ≡ b) → sigmaPath→pathSigma a b (pathSigma→sigmaPath _ _ x) ≡ x
sigmaPath→pathSigma→sigmaPath {B = B} {a = a} {b = b} p i j =
  hcomp (λ t → λ { (i = i1) → (fst (p j) , filler-π2 p t j)
                 ; (i = i0) → filler-comp a b (pathSigma→sigmaPath _ _ p) j t
                 ; (j = i0) → (fst a , snd a)
                 ; (j = i1) → (fst b , filler-π2 p t i1) })
        (fst (p j) , coe0→i (λ k → B (fst (p k))) j (snd a))

pathSigma≡sigmaPath : (a b : Σ A B) → (a ≡ b) ≡ (a Σ≡T b)
pathSigma≡sigmaPath a b =
  isoToPath (iso (pathSigma→sigmaPath a b)
                 (sigmaPath→pathSigma a b)
                 (pathSigma→sigmaPath→pathSigma {a = a})
                 sigmaPath→pathSigma→sigmaPath)

discreteΣ : Discrete A → ((a : A) → Discrete (B a)) → Discrete (Σ A B)
discreteΣ {B = B} Adis Bdis (a0 , b0) (a1 , b1) = discreteΣ' (Adis a0 a1)
  where
    discreteΣ' : Dec (a0 ≡ a1) → Dec ((a0 , b0) ≡ (a1 , b1))
    discreteΣ' (yes p) = J (λ a1 p → ∀ b1 → Dec ((a0 , b0) ≡ (a1 , b1))) (discreteΣ'') p b1
      where
        discreteΣ'' : (b1 : B a0) → Dec ((a0 , b0) ≡ (a0 , b1))
        discreteΣ'' b1 with Bdis a0 b0 b1
        ... | (yes q) = yes (transport (ua Σ≡) (refl , q))
        ... | (no ¬q) = no (λ r → ¬q (subst (λ X → PathP (λ i → B (X i)) b0 b1) (Discrete→isSet Adis a0 a0 (cong fst r) refl) (cong snd r)))
    discreteΣ' (no ¬p) = no (λ r → ¬p (cong fst r))



-- module _ {A A' : Set ℓ} {ℓ'} {B : A → Set ℓ'} {B' : A' → Set ℓ'} (f : A ≃ A') (g : (x : A) → B x ≃ B' (f .fst x)) where


--   EquivΣ : Σ A B ≃ Σ A' B'
--   EquivΣ .fst (a , b) = f .fst a , g a .fst b
--   EquivΣ .snd .equiv-proof y = ((p .fst .fst , q .fst .fst) , ΣPathP ((p .fst .snd) , \ i → toPathP {A = (λ i → B' (p .fst .snd (~ i)))} (sym (q .fst .snd)) (~ i)))
--                              , \ fb →
--                                let r = p .snd (fb .fst .fst , cong fst (fb .snd) )
--                                    s = q .snd ((transport (cong B (sym (cong fst r))) (fb .fst .snd)) ,
--                                                          {!sym (fromPathP (\ i → cong snd (fb .snd) (~ i)))!})
--                                in  ΣPathP ((ΣPathP (cong fst r , {!cong snd r!})) , {!r!})
--          where
--            p : isContr
--                  (fiber (f .fst) (y .fst))
--            p = f .snd .equiv-proof (y .fst)
--            q : isContr
--                  (fiber
--                   (g (p .fst .fst) .fst)
--                   (transport
--                    (λ i → B' (p .fst .snd (~ i)))
--                    (y .snd)))
--            q = g (p .fst .fst) .snd .equiv-proof (transport (cong B' (sym (p .fst .snd))) (y .snd))
-- (a , b) = f .fst a , g a .fst b
--   EquivΣ .snd = {!isoToEquiv!}

open isHAEquiv renaming (g to inv)

module _ {A A' : Set ℓ} {ℓ'} {B : A → Set ℓ'} {B' : A' → Set ℓ'} (f : HAEquiv A A') (g : (x : A') → HAEquiv (B (f .snd .inv x)) (B' x)) where


--   EquivΣ' : Iso (Σ A B) (Σ A' B')
--   EquivΣ' .Iso.fun (a , b) = f .fst a , g (f .fst a) .fst (transport (cong B (sym (secEq f a))) b)
--   EquivΣ' .Iso.inv (a' , b') = invEq f a' , invEq (g a') b'
--   EquivΣ' .Iso.rightInv (a' , b') = ΣPathP ((retEq f a') , help )
--    where
--    help0 : g a' .fst (invEq (g a') b') ≡ b'
--    help0 = retEq (g a') b'
--    help : PathP (λ i → B' (retEq f a' i))
--                 (g (f .fst (invEq f a')) .fst (transport (λ i → B (secEq f (invEq f a') (~ i)))
--                                                           (invEq (g a') b')))
--                 b'
--    help = transport (\ j →
--     PathP (λ i → B' ((retEq f a') (~ j ∨ i)))
--           (g (retEq f a' (~ j) ) .fst
--            {!transpFill i0
--             (λ i → inS (B (secEq f (invEq f a') (~ i))))
--             (invEq (g a') b') !})
--           b') help0
--   EquivΣ' .Iso.leftInv (a , b) = ΣPathP ((secEq f a) , \ i → toPathP {A = (λ i → B (secEq f a (~ i)))} path (~ i))
--     where
--       path = sym (secEq (g (f .fst a)) (transport (cong B (sym (secEq f a))) b))

-- {-
--   [2118, 2120, 2121] a'
--                        = ?0 (f = f) (g = g) (a' = a') (b' = b') (j = i0) (i = x)
--   [2126, 2128, 2148] ?0 (f = f) (g = g) (a' = a') (b' = b') (j = i1)
--                      (i = x)
--                        = snd (fst (snd f .equiv-proof a')) x
--                        : A'
-- -}
  EquivΣ' : HAEquiv (Σ A B) (Σ A' B')
  EquivΣ' .fst (a , b) = f .fst a , g (f .fst a) .fst (transport (cong B (sym (f .snd .sec a))) b)
  EquivΣ' .snd .inv (a' , b') = f .snd .inv a' , g a' .snd .inv b'
  EquivΣ' .snd .sec (a , b) = ΣPathP ((f .snd .sec a)
    , \ i → toPathP {A = (λ i → B (f .snd .sec a (~ i)))} (sym (g (f .fst a) .snd .sec (transport (cong B (sym (f .snd .sec a))) b))) (~ i) )
  EquivΣ' .snd .ret (a' , b') = ΣPathP ((f .snd .ret a') , toPathP ({!f .snd .com!} ∙ g a' .snd .ret b'))
  EquivΣ' .snd .com = {!!}
    -- d .equiv-proof y = ((p .fst .fst , q .fst .fst) , ΣPathP ((p .fst .snd) , {!q .fst .snd!})) , {!!}
    -- ((p .fst .fst , q .fst .fst) , ΣPathP ((p .fst .snd) , \ i → toPathP {A = (λ i → B' (p .fst .snd (~ i)))} (sym (q .fst .snd)) (~ i)))
    --                          , \ fb →
    --                            let r = p .snd (fb .fst .fst , cong fst (fb .snd) )
    --                                s = q .snd ((transport (cong B (sym (cong fst r))) (fb .fst .snd)) ,
    --                                                      {!sym (fromPathP (\ i → cong snd (fb .snd) (~ i)))!})
    --                            in  ΣPathP ((ΣPathP (cong fst r , {!cong snd r!})) , {!r!})
       where
           -- p : isContr
           --       (fiber (f .fst) (y .fst))
           -- p = f .snd .equiv-proof (y .fst)
           -- q : isContr
           --       (fiber
           --        (g (y .fst) .fst) (y .snd))
           -- q = g (y .fst) .snd .equiv-proof (y .snd) -- (transport (cong B' (sym (p .fst .snd))) (y .snd))


    -- EquivΣ' .fst (a , b) = f .fst a , g (f .fst a) .fst (transport (cong B (sym (secEq f a))) b)
    -- EquivΣ' .snd .equiv-proof y = ((p .fst .fst , q .fst .fst) , ΣPathP ((p .fst .snd) , {!q .fst .snd!})) , {!!}
    -- ((p .fst .fst , q .fst .fst) , ΣPathP ((p .fst .snd) , \ i → toPathP {A = (λ i → B' (p .fst .snd (~ i)))} (sym (q .fst .snd)) (~ i)))
    --                          , \ fb →
    --                            let r = p .snd (fb .fst .fst , cong fst (fb .snd) )
    --                                s = q .snd ((transport (cong B (sym (cong fst r))) (fb .fst .snd)) ,
    --                                                      {!sym (fromPathP (\ i → cong snd (fb .snd) (~ i)))!})
    --                            in  ΣPathP ((ΣPathP (cong fst r , {!cong snd r!})) , {!r!})
--       where
           -- p : isContr
           --       (fiber (f .fst) (y .fst))
           -- p = f .snd .equiv-proof (y .fst)
           -- q : isContr
           --       (fiber
           --        (g (y .fst) .fst) (y .snd))
           -- q = g (y .fst) .snd .equiv-proof (y .snd) -- (transport (cong B' (sym (p .fst .snd))) (y .snd))
