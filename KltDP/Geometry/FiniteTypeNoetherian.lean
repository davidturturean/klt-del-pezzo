import KltDP.Geometry.AffineFiniteType
import Mathlib.RingTheory.FiniteType

/-!
# Noetherian affine sections from the actual finite-type base map

This specializes Mathlib's finite-type Noetherian-ring theorem to the
previously constructed base algebra on every actual affine open. It gives
the scheme's full locally Noetherian property, in addition to the already
proved Noetherianity of the individual projective-surface stalks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

theorem isLocallyNoetherian_of_locallyOfFiniteType_toSpec
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsLocallyNoetherian X where
  component_noetherian U := by
    letI := affineSectionsAlgebra f U.2
    letI := affineSectionsAlgebra_finiteType f U.2
    exact Algebra.FiniteType.isNoetherianRing R Γ(X, U)

/-- Projectivity over a field supplies the actual finite-type structure
map, so all affine section rings are Noetherian. -/
theorem IsProjectiveOverField.isLocallyNoetherian
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} (hf : IsProjectiveOverField f) :
    IsLocallyNoetherian X := by
  letI : LocallyOfFiniteType f := hf.locallyOfFiniteType
  exact isLocallyNoetherian_of_locallyOfFiniteType_toSpec f

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

theorem isLocallyNoetherian : IsLocallyNoetherian X.toScheme :=
  X.projective.isLocallyNoetherian

end NormalProjectiveSurface
end KltDP.Geometry
