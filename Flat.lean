import Mathlib.RingTheory.Flat
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalks

open CategoryTheory
open AlgebraicGeometry

def RingHom.Flat {A B : Type _} [CommRing A] [Ring B]
  (f : A →+* B) : Prop :=
@Module.Flat A B _ _ f.toModule

-- not sure what namespace this should be in, going to nap now
def Scheme.Flat {X Y : Scheme} (f : X ⟶ Y) : Prop :=
∀ x : X, (PresheafedSpace.stalkMap f.1 x).Flat
