{-# OPTIONS --cubical #-}
module _ where

open import Cubical.Core.Everything
open import Cubical.Foundations.HAEquiv
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma

-- Lemmas about Sigma types vs. isos/equivs, feel free to skip.
open isHAEquiv renaming (g to inv)

module _ {ℓ} {A A' : Set ℓ} {ℓ'} {B : A → Set ℓ'} {B' : A' → Set ℓ'} (f : HAEquiv A A') (g : (x : A') → HAEquiv (B (f .snd .inv x)) (B' x)) where

  EquivΣ' : Iso (Σ A B) (Σ A' B')
  EquivΣ' .Iso.fun (a , b) = f .fst a , g (f .fst a) .fst (transport (cong B (sym (f .snd .sec a))) b)
  EquivΣ' .Iso.inv (a' , b') = f .snd .inv a' , g a' .snd .inv b'
  EquivΣ' .Iso.leftInv (a , b) = ΣPathP ((f .snd .sec a)
    , symP (toPathP {A = (λ i → B (f .snd .sec a (~ i)))} (sym (g (f .fst a) .snd .sec (transport (cong B (sym (f .snd .sec a))) b)))) )
  EquivΣ' .Iso.rightInv (a' , b') = ΣPathP ((f .snd .ret a') ,
    toPathP (fromPathP (cong (\ p → z (p .fst) (p .snd)) eq) ∙ g a' .snd .ret b'))
   where
     T = Σ A' \ x → B (f .snd .inv x)
     z : (x : A') → (y : B (f .snd .inv x)) → B' x
     z x y = g x .fst y
     eq : (\ _ → T) [ (f .fst (f .snd .inv a')) , (transport (λ i → B (f .snd .sec (f .snd .inv a') (~ i)))
        (g a' .snd .inv b')) ≡ a' , (g a' .snd .inv b') ]
     eq = ΣPathP (f .snd .ret a'
                 , transport (\ j → PathP (λ i → B (isHAEquiv.com-ret (f .snd) a' (~ j) i ))
                            (transp (λ i → B (f .snd .sec (f .snd .inv a') (~ i))) i0
                                                                   (g a' .snd .inv b'))
                                                            (g a' .snd .inv b'))
                                               (symP (transpFill {A = B' a'} i0 (λ i → inS (B (f .snd .sec (f .snd .inv a') (~ i))))
                                                                                (g a' .snd .inv b'))))


module _ {ℓ} {A A' : Set ℓ} {ℓ'} {B : A → Set ℓ'} {B' : A' → Set ℓ'}
         (f : Iso A A')
         (g : (x : A) → Iso (B x) (B' (f .Iso.fun x))) where


  EquivΣ : Iso (Σ A B) (Σ A' B')
  EquivΣ = swapIso (EquivΣ' (iso→HAEquiv (swapIso f)) \ x → iso→HAEquiv (swapIso (g x)))



-- Clocks and irrelevance
postulate
  Clk : Set

ClockIrr : (A : Set) → Set _
ClockIrr A = (t : Clk → A) (k1 k2 : Clk) → t k1 ≡ t k2

constClk : {A : Set} → A → Clk → A
constClk a _ = a

postulate
  A : Set
  B : A → Set
  A-irr : ClockIrr A
  B-irr : (a : A) → ClockIrr (B a)

_isRightInvOf_ = retract

-- Here's how we extract ClockIrr from an iso/equiv:
-- composing the right inverse proof with itself.
retractToClockIrr : ∀ {A : Set} {g} → g isRightInvOf (constClk {A}) → ClockIrr A
retractToClockIrr {A} {g} f t k1 k2 =
  sym (cong (\ q → q k1) (f t)) ∙ cong (\ q → q k2) (f t)



-- The theorem for Σ types.
module Equivs (k : Clk) where

  ClockIrrToIso : ∀ {X : Set} → ClockIrr X → Iso X (Clk → X)
  ClockIrrToIso cirr = iso (\ a _ → a) (\ t → t k) (\ t i k' → cirr t k k' i) \ _ → refl

  Aeqv : Iso A (Clk → A)
  Aeqv = ClockIrrToIso A-irr

  Beqv : (x : A) → Iso (B x) (Clk → B x)
  Beqv x = ClockIrrToIso (B-irr x)

  theEqv : Iso (Σ A B) (Σ (Clk → A) \ a → ∀ k → B (a k))
  theEqv = EquivΣ {B = B} {B' = \ t → ∀ k → B (t k)} Aeqv Beqv

  rInv : (Clk → Σ A B) → Σ A B
  rInv p = fst (p k) , transport eq (snd (p k))
     where
       a : A
       a = fst (p k)
       tA : Clk → A
       tA k' = fst (p k')
       eq : B (tA k) ≡ B (tA k)
       eq = (λ i → B (A-irr (λ k' → fst (p k')) k k (~ i)))

  rInv-prf : rInv isRightInvOf (constClk {Σ A B})
  rInv-prf b = let r = Iso.rightInv theEqv (fst ∘ b , snd ∘ b) in funExt (\ k → ΣPathP ((\ i → cong fst r i k) , (\ i → cong snd r i k)))

  -- readable normal form of the proof above.
  rInv-prf-direct : rInv isRightInvOf (\ a _ → a)
  rInv-prf-direct t i k1
     = A-irr (λ x → fst (t x)) k k1 i
     , hcomp (λ j → (λ { (i = i1) → snd (t k1)
                       ; (i = i0) → B-irr (fst (t k))
                                          (\ k' → transport (λ h → B (A-irr (λ x → fst (t x)) k k' (~ h)))
                                                            (snd (t k')))
                                          k k1 (~ j)
                          }))
             (transp (λ j → B (A-irr (λ k' → fst (t k')) k k1 (i ∨ ~ j))) i (snd (t k1)))

  Σ-irr : ClockIrr (Σ A B)
  Σ-irr = retractToClockIrr rInv-prf
