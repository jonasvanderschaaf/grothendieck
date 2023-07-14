/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.finite_type
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.AlgebraicGeometry.OpenImmersion.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Over
import Grothendieck.Separated
import Mathlib.AlgebraicGeometry.Properties
/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry.Scheme

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
class Scheme.Hom.LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_of_affine_subset :
    ∀ (U : affineOpens Y) (V : affineOpens X) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
      (Hom.appLe f e).FiniteType

class Scheme.Hom.FiniteType (f : X ⟶ Y) extends LocallyOfFiniteType f, QuasiCompact f

class Scheme.IsVariety {k : CommRingCat} [Field k] 
    (X : Over (specObj k)) 
  extends IsReduced X.left, Hom.IsSeparated X.hom, Hom.FiniteType X.hom

class Scheme.IsIntegralVariety {k : CommRingCat} [Field k] 
    (X : Over (specObj k))
  extends IsIntegral X.left, Hom.IsSeparated X.hom, Hom.FiniteType X.hom 

instance {k : CommRingCat} [Field k] {X : Over (specObj k)} [IsIntegralVariety X] : 
  IsVariety X where
    component_reduced := (@isReducedOfIsIntegral X.left IsIntegralVariety.toIsIntegral).1
    diag_is_closed_imm := IsIntegralVariety.toIsSeparated.1
    finiteType_of_affine_subset := IsIntegralVariety.toFiniteType.toLocallyOfFiniteType.1
    isCompact_preimage := IsIntegralVariety.toFiniteType.toQuasiCompact.1

end AlgebraicGeometry

