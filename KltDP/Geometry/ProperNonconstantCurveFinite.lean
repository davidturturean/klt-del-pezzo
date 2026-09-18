import KltDP.Topology.CurveConnectedFibers
import KltDP.Geometry.ProperIsoComponents
import KltDP.Geometry.GeometricConnectedFiberTopology
import KltDP.Literature.SteinFactorizationNoetherian

/-!
The original proper nonconstant curve map is finite. This uses the
accepted full Stein factorization: its connected-fiber first factor is
bijective by curve topology, and its original structure-sheaf map is an
isomorphism. No additional Zariski-main statement is used.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperNonconstantCurve

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [NoetherianSpace X]
  [IsLocallyNoetherian Y]

/-- Finiteness of the original proper map follows from actual nonconstancy
on points and the dimension bound on its original source. -/
theorem isFinite_of_nonconstant_base (f : X ⟶ Y) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnonconstant : ¬ ∃ y : Y, ∀ x : X, f.base x = y) : IsFinite f := by
  obtain ⟨T, g, p, hgp, hg, hconnected, hp, hgc, _, _⟩ :=
    KltDP.Literature.Stacks.steinFactorization_noetherian_literal Y X f
  letI : IsProper g := hg
  letI : IsFinite p := hp
  letI : IsIso g.c := hgc
  have hgNonconstant : ¬ ∃ t : T, ∀ x : X, g.base x = t := by
    rintro ⟨t, ht⟩
    apply hnonconstant
    refine ⟨p.base t, fun x => ?_⟩
    rw [← hgp, Scheme.comp_base_apply, ht x]
  have hbij : Function.Bijective g.base :=
    KltDP.Topology.bijective_of_closed_nonconstant_of_connected_fibers hdim
      g.base g.base.hom.continuous g.isClosedMap hgNonconstant
      (GeometricConnectedFiberTopology.isConnected_preimage_singleton g hconnected)
  letI : IsIso g := ProperIsoComponents.isIso_of_bijective g hbij
  rw [← hgp]
  infer_instance

#check KltDP.Geometry.ProperNonconstantCurve.isFinite_of_nonconstant_base
#print axioms KltDP.Geometry.ProperNonconstantCurve.isFinite_of_nonconstant_base

end KltDP.Geometry.ProperNonconstantCurve
