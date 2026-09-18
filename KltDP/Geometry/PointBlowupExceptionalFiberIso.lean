import KltDP.Geometry.PointBlowupCenterFiber
import KltDP.Geometry.Resolution

/-!
# The original exceptional-scheme isomorphism gives the original point fiber

The source statement identifies the original curve scheme with the actual
categorical fiber over the original reduced closed center. Taking the
ranges of those original inclusions and transporting through the original
ambient isomorphism proves the literal point-fiber equality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] PointBlowupChart.instCommRing
  PointBlowupChart.instOpenImmersion PointBlowupChart.instMaximal

/-- A scheme-level exceptional identification preserves the full original
point fiber, through the actual point-blowup chart isomorphism. -/
theorem PointBlowupChart.pointFiber_eq_of_exceptionalIso
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ T.toScheme} {z : T.Point}
    (c : PointBlowupChart T.toScheme z) (e : S.toScheme ≅ c.scheme)
    (he : e.hom ≫ c.projection = b) (E : S.PrimeCurve)
    (θ : E.toScheme ≅ PointBlowupGluing.globalCenterFiber c.j c.q c.isClosed)
    (hθ : θ.hom ≫ PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed =
      E.inclusion ≫ e.hom) :
    b.base ⁻¹' ({z} : Set T.toScheme) = (E : Set S.toScheme) := by
  have hrange : Set.range
      (PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed).base =
      e.hom.base '' (E : Set S.toScheme) := by
    calc
      _ = Set.range (θ.hom ≫
          PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed).base := by
        change Set.range (PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed).base =
          Set.range ((PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed).base ∘
            θ.hom.base)
        rw [Set.range_comp, θ.hom.surjective.range_eq, Set.image_univ]
      _ = Set.range (E.inclusion ≫ e.hom).base := congrArg (fun f => Set.range f.base) hθ
      _ = _ := by
        change Set.range (e.hom.base ∘ E.inclusion.base) = _
        rw [Set.range_comp, NormalProjectiveSurface.PrimeCurve.range_inclusion]
  have hpre : b.base ⁻¹' ({z} : Set T.toScheme) = e.hom.base ⁻¹'
      ((PointBlowupGluing.projection c.j c.q c.isClosed).base ⁻¹' {c.j.base c.q}) := by
    ext x
    change b.base x = z ↔
      (PointBlowupGluing.projection c.j c.q c.isClosed).base (e.hom.base x) = c.j.base c.q
    have hx := congrArg (fun f : S.toScheme ⟶ T.toScheme => f.base x) he
    change (PointBlowupGluing.projection c.j c.q c.isClosed).base
      (e.hom.base x) = b.base x at hx
    rw [hx, c.base_eq]
  rw [hpre, ← PointBlowupGluing.range_globalCenterFiberι, hrange,
    Set.preimage_image_eq _ e.hom.isOpenEmbedding.injective]

end KltDP.Geometry

#print axioms KltDP.Geometry.PointBlowupChart.pointFiber_eq_of_exceptionalIso
