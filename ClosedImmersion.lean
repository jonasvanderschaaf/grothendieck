import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Maps

open CategoryTheory
open AlgebraicGeometry
open Topology

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