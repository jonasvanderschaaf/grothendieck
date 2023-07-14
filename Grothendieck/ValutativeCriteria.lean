import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.Topology.Maps
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme

-- Just copying in other defs
class ClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_closed_emb: ClosedEmbedding f.1.base
  surj_on_stalks: ∀ x : X, Function.Surjective (PresheafedSpace.stalkMap f.1 x)   

class Separated {X Y : Scheme} (f : X ⟶ Y) : Prop where
  diag_closed_immersion : ClosedImmersion (pullback.diagonal f)

/-  
! The Prop of 'satisfying the uniqueness part of the valuative criterion' (01KD) for 
! a morphism f : X -> S. Given the commutative diagram 
!                     Spec K → X 
!                       ↓      ↓                                          (1)
!                     Spec A → S 
! where A is a valuation ring and K its field of fractions, there is at most one 
! compatible morphism Spec A → X.  
-/ 

def sats_uniq {X S : Scheme} (f : X ⟶ S) : Prop := 
  ∀ (A : Type _) [CommRing A] [IsDomain A] [ValuationRing A] 
    (h : specObj (CommRingCat.of (FractionRing A)) ⟶ X) -- top morphism in (1)
    (i : specObj (CommRingCat.of A) ⟶ S),  -- bottom morphism in (1)
    CommSq h (Scheme.specMap (CommRingCat.ofHom (algebraMap A (FractionRing A)))) f i → -- assume square commutes
      ∀ (l₁ l₂ : specObj (CommRingCat.of A) ⟶ X), --uniqueness of lifts, if any
      l₁ ≫ f = i ∧ Scheme.specMap (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ l₁ = h  → 
      l₂ ≫ f = i ∧ Scheme.specMap (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ l₂ = h  → l₁ = l₂

variable (X Y : Scheme) (f : X ⟶ Y)
#check (sats_uniq f)

example : sats_uniq (𝟙 X) := by
  intro h₁ h₂ h₃ h₄ f₁ f₂ hcomm l₁ l₂ c1 c2
  refine' LocallyRingedSpace.Hom.ext' _ _ _
  ext U x
  simp
  sorry
  sorry


-- Valuative criterion for separatedness (01KY)
theorem val_crit_sep {X S : Scheme} (f : X ⟶ S) : QuasiSeparated f → sats_uniq f → Separated f := by
  sorry