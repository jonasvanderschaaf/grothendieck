import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.CategoryTheory.MorphismProperty

import Mathlib.Topology.Maps

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

theorem isClosedImmersion_respectsIso :
  MorphismProperty.RespectsIso @Scheme.IsClosedImmersion := by
    constructor <;> intro X Y Z e f hf <;> apply isClosedImmersion_stableUnderComposition

    . apply iso_is_closed_immersion

    . assumption
    assumption
    exact iso_is_closed_immersion

end AlgebraicGeometry