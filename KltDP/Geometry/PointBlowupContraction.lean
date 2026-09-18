import KltDP.Geometry.SurfacePointBlowupSequenceBirational
import KltDP.Geometry.ClosedPointDimension

/-!
# Original point blowup with its exceptional curve is a contraction

The original point blowup gives birationality and a closed center. The
actual target surface supplies the center's stalk dimension. The literal
fiber equality identifies the original prime curve's image. These are
ordinary consumers of the raw geometric conclusion of Castelnuovo's
criterion; no contraction property or existence theorem is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Keep the original map and original exceptional curve when deriving
all properties in the existing contraction interface. -/
theorem IsPointBlowupAt.isContraction_of_exceptionalFiber
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {z : T.Point} (h : IsPointBlowupAt S T b z)
    (hregular : ∀ t : T.Point, RegularPoint T.toScheme t)
    (E : S.PrimeCurve)
    (hfiber : b.base ⁻¹' ({z} : Set T.toScheme) = (E : Set S.toScheme)) :
    IsContraction S T b E := by
  have hclosed : IsClosed ({z} : Set T.toScheme) := h.toSchemeIsAt.isClosed
  have hmap (s : S.Point) (hs : s ∈ (E : Set S.toScheme)) : b.base s = z := by
    have hs' : s ∈ b.base ⁻¹' ({z} : Set T.toScheme) := by rwa [hfiber]
    exact hs'
  have himage : b.base '' (E : Set S.toScheme) = {z} := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hmap s hs
    · intro ht
      obtain ⟨s, hs⟩ := E.nonempty
      exact ⟨s, hs, (hmap s hs).trans (Set.mem_singleton_iff.mp ht).symm⟩
  exact ⟨hregular, (isBirational_iff_isBirationalScheme b).mpr h.isBirationalScheme,
    z, hclosed, himage, T.closed_stalk_dimension_two z hclosed, h⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupAt.isContraction_of_exceptionalFiber
