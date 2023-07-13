import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.RingTheory.LocalProperties
import Mathlib.Topology.Maps
universe v u
open CategoryTheory
open AlgebraicGeometry
open Topology

namespace AlgebraicGeometry

-- A closed immersion is a closed immersion of topological spaces which is
-- surjective on stalks. This definition is due to Mumford.
class Scheme.IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop where
  base_closed_emb: ClosedEmbedding f.1.base
  surj_on_stalks: ∀ x : X, Function.Surjective (PresheafedSpace.stalkMap f.1 x) 

example {X : Scheme} : Scheme.IsClosedImmersion (𝟙 X) := by
  constructor
  . rw [Scheme.id_val_base]
    apply closedEmbedding_id

  . intro x r
    use r
    erw [PresheafedSpace.stalkMap.id]
    rfl

theorem isClosedImmersion_stableUnderComposition :
  MorphismProperty.StableUnderComposition @Scheme.IsClosedImmersion := by
    rintro X Y Z f g ⟨hf_closed, hf_surj⟩ ⟨hg_closed, hg_surj⟩
    constructor
    . exact hg_closed.comp hf_closed

    . intro x
      erw [PresheafedSpace.stalkMap.comp]
      have hf_surj_x := hf_surj x
      have hg_surj_fx := hg_surj (f.val.base x)
      exact hf_surj_x.comp hg_surj_fx

theorem iso_is_closed_immersion {X Y : Scheme} {f: X ⟶ Y} [hf: IsIso f] : Scheme.IsClosedImmersion f := by
  constructor
  . have := PresheafedSpace.base_isIso_of_iso f.val
    let f_top_iso := TopCat.homeoOfIso (asIso f.val.base)
    exact Homeomorph.closedEmbedding f_top_iso

  . intro x
    have := PresheafedSpace.stalkMap.isIso f.val x
    apply @And.right (Function.Injective ↑(PresheafedSpace.stalkMap f.val x)) _
    apply ConcreteCategory.bijective_of_isIso

-- Now proving the identity is a closed immersion is a one-liner.
example {X : Scheme} : Scheme.IsClosedImmersion (𝟙 X) := by
  apply iso_is_closed_immersion

variable (R : CommRingCat) (M : Submonoid R) 

theorem isClosedImmersion_respectsIso :
  MorphismProperty.RespectsIso @Scheme.IsClosedImmersion := by
    constructor <;> intro X Y Z e f hf <;> apply isClosedImmersion_stableUnderComposition

    . apply iso_is_closed_immersion

    . assumption
    assumption
    exact iso_is_closed_immersion

/- A surjective hom `R →+* S` induces a surjective hom `R_{f⁻¹(P)} →+* S_P`. 
This is just an application of `localizationPreserves_surjective`, modulo the fact that
`IsLocalization f((f⁻¹(P))ᶜ) R_P`, since `f((f⁻¹(P))ᶜ)` is just `Pᶜ`... -/
lemma surjective_localRingHom_of_surjective {R S : Type u} 
    [CommRing R] [CommRing S] (f : R →+* S) 
    (h : Function.Surjective f) (P : Ideal S) [P.IsPrime] : 
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  @localizationPreserves_surjective R S _ _ f ((P.comap f).primeCompl) 
    (Localization.AtPrime (P.comap f)) (Localization.AtPrime P) _ _ _ _ _ 
    ((Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization) h
  
lemma spec_of_surjective_is_closed_immersion {R S : CommRingCat} (f : R ⟶ S) 
  (h : Function.Surjective f)
  : Scheme.IsClosedImmersion (Scheme.specMap (CommRingCat.ofHom f)) := by
  constructor

  . apply PrimeSpectrum.closedEmbedding_comap_of_surjective
    exact h

  . intro x
    erw [←localRingHom_comp_stalkIso, CommRingCat.coe_comp, CommRingCat.coe_comp]
    show Function.Surjective (_ ∘ _)
    apply Function.Surjective.comp
    apply Function.Surjective.comp

    . let stalk_iso := (StructureSheaf.stalkIso S x).inv
      apply @And.right (Function.Injective stalk_iso) _
      apply ConcreteCategory.bijective_of_isIso

    . exact surjective_localRingHom_of_surjective f h x.asIdeal

    . let stalk_iso := (StructureSheaf.stalkIso ((CommRingCat.of R))
        ((PrimeSpectrum.comap (CommRingCat.ofHom f)) x)).hom
      apply @And.right (Function.Injective stalk_iso) _
      apply ConcreteCategory.bijective_of_isIso

lemma spec_of_mk_is_closed_immersion {R : CommRingCat.{u}} (I : Ideal R) :
  Scheme.IsClosedImmersion (Scheme.specMap (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
spec_of_surjective_is_closed_immersion (CommRingCat.ofHom (Ideal.Quotient.mk I))
  Ideal.Quotient.mk_surjective

end AlgebraicGeometry