import KltDP.Geometry.BaseRingDerivedAction
import KltDP.Geometry.CoherentModule
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
Literal statement candidate for Stacks Project Tag 02O6, revision
540451b3e79a131df8eca4c4187448e49dcb262d.

The cohomology model is original abelian-derived global sections with the
independently defined action of the original base ring. Published Tag 01F1
and its common-resolution proof identify this mathematical cohomology with
the module-sheaf formulation. That semantic identification is documented in
the admission dossier; no separate module-derived Lean comparison is claimed.

INACTIVE TEMPLATE. Its declaration is not currently admitted or activated.
-/

universe u

namespace KltDP.Literature.Stacks

open AlgebraicGeometry CategoryTheory

axiom properCohomology_finite
    {A : Type u} [instCommRing : CommRing A] [instNoetherianRing : IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [instProper : IsProper f]
    (M : X.Modules) [instCoherent : KltDP.Geometry.IsCoherentModule M] (n : ℕ) :
    letI := KltDP.Geometry.ModuleCohomology.baseRingRightDerivedModule f M n
    Module.Finite A (KltDP.Geometry.ModuleCohomology.rightDerivedH M n)

end KltDP.Literature.Stacks
