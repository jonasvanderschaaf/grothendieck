import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.CategoryTheory.MorphismProperty

import Mathlib.Topology.Maps

open CategoryTheory
open AlgebraicGeometry
open Topology

namespace AlgebraicGeometry

variable {X Y : Scheme}

-- A closed immersion is a closed immersion of topological spaces which is
-- surjective on stalks. This definition is due to Mumford.
class Scheme.IsClosedImmersion (f : X ⟶ Y) : Prop where
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

end AlgebraicGeometry