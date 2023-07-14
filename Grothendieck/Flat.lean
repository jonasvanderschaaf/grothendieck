import Mathlib.RingTheory.Flat
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalks

open CategoryTheory
open AlgebraicGeometry

def RingHom.Flat {A B : Type _} [CommRing A] [Ring B]
  (f : A →+* B) : Prop :=
@Module.Flat A B _ _ f.toModule

-- not sure what namespace this should be in, going to nap now
def Scheme.Hom.Flat {X Y : Scheme} (f : X ⟶ Y) : Prop :=
∀ x : X, (PresheafedSpace.stalkMap f.1 x).Flat

theorem Flat_iff {R S : CommRingCat} (f : R ⟶ S) :
  f.Flat ↔ Scheme.Hom.Flat (Scheme.specMap f) := sorry