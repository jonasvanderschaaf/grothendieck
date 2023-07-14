import Mathlib.RingTheory.Flat
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalks
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Grothendieck.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory AlgebraicGeometry TensorProduct
open CategoryTheory.Limits Scheme

set_option autoImplicit false
namespace AlgebraicGeometry
variable (R S T : CommRingCat) (f : R ⟶ S) (g : R ⟶ T) 

noncomputable def pullbackSpecIso : 
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
  pullback (specMap f) (specMap g) ≅ specObj (CommRingCat.of (S ⊗[R] T)) := 
(PreservesPullback.iso Spec _ _).symm ≪≫ Spec.mapIso 
  ((CommRingCat.pushoutCoconeIsColimit f g).coconePointUniqueUpToIso 
  (colimit.isColimit _) ≪≫ pushoutIsoUnopPullback _ _).op

class Scheme.Hom.IsSeparated {X Y : Scheme} (f : X ⟶ Y) : Prop where
  diag_is_closed_imm: Scheme.IsClosedImmersion (pullback.diagonal f)

class Scheme.IsSeparated {X : Scheme} extends Scheme.Hom.IsSeparated (terminal.from X)

end AlgebraicGeometry

