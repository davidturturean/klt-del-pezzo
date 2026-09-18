import KltDP.Geometry.PrimeCurveImageIntersection
import KltDP.Geometry.DisjointCurveContractionTransport

/-!
# Pairwise intersections through an actual single-curve contraction

Only disjointness from the actual contracted curve is required. The two
surviving original curves may meet, and their targets are identified by
the literal images under the same original contraction morphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- The same actual contraction preserves every pair of surviving original curves. -/
theorem IsContraction.intersectionNumber_image_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (C D : S.PrimeCurve)
    (hCE : Disjoint (C : Set S.toScheme) (E : Set S.toScheme))
    (hDE : Disjoint (D : Set S.toScheme) (E : Set S.toScheme))
    (C' D' : T.PrimeCurve)
    (hC' : b.base '' (C : Set S.toScheme) = (C' : Set T.toScheme))
    (hD' : b.base '' (D : Set S.toScheme) = (D' : Set T.toScheme)) :
    C'.intersectionNumber (T.primeCurveCartier hb.regular D') =
      C.intersectionNumber (S.primeCurveCartier hS D) := by
  obtain ⟨z, hz, hfiber, hbl⟩ := hb.centerFiber_eq_curve
  let U : T.toScheme.Opens := ⟨({z} : Set T.toScheme)ᶜ, hz.isOpen_compl⟩
  letI : IsIso (b ∣_ U) := hbl.toSchemeIsAt.isIso_restrict U (by simp [U])
  letI : IsProper b := hb.isProper
  have hU (A : S.PrimeCurve) (hAE : Disjoint (A : Set S.toScheme) (E : Set S.toScheme)) :
      Set.range A.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme) := by
    intro x hx
    rw [A.range_inclusion] at hx
    change b.base x ≠ z
    intro hbx
    have hxE : x ∈ (E : Set S.toScheme) := by rw [← hfiber]; exact hbx
    exact (Set.disjoint_left.mp hAE) hx hxE
  have heqC : C' = CurveOnIsomorphismOpen.imageCurve C b U (hU C hCE) :=
    NormalProjectiveSurface.PrimeCurve.ext (hC'.symm.trans
      (CurveOnIsomorphismOpen.coe_imageCurve C b U (hU C hCE)).symm)
  have heqD : D' = CurveOnIsomorphismOpen.imageCurve D b U (hU D hDE) :=
    NormalProjectiveSurface.PrimeCurve.ext (hD'.symm.trans
      (CurveOnIsomorphismOpen.coe_imageCurve D b U (hU D hDE)).symm)
  rw [heqC, heqD]
  exact CurveOnIsomorphismOpen.imageCurve_intersectionNumber C D b U (hU C hCE) (hU D hDE)
    hS hb.regular hb.over_base

end KltDP.Geometry

#print axioms KltDP.Geometry.IsContraction.intersectionNumber_image_eq
