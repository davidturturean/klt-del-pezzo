import KltDP.Geometry.Resolution
import KltDP.Geometry.PointBlowupGluing

/-!
# Actual point-blowup fibers away from the center

The original restricted projection is the constructed puncture isomorphism.
Consequently every original point fiber away from the center has at most one
point. The comparison preserves the original IsPointBlowupAt morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- The actual glued projection is injective on its original point
preimage of the center complement. -/
theorem projection_base_injOn_off_center :
    Set.InjOn (projection j q hclosed).base
      ((projection j q hclosed).base ⁻¹' ({j.base q} : Set X)ᶜ) := by
  letI : IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) := by
    rw [← punctureIso_hom]
    infer_instance
  intro x hx y hy hxy
  let x' : ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed).toScheme := ⟨x, hx⟩
  let y' : ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed).toScheme := ⟨y, hy⟩
  have hxy' : ((projection j q hclosed) ∣_ puncture j q hclosed).base x' =
      ((projection j q hclosed) ∣_ puncture j q hclosed).base y' := by
    rw [morphismRestrict_base]
    exact Subtype.ext hxy
  exact congrArg Subtype.val
    (((projection j q hclosed) ∣_ puncture j q hclosed).isOpenEmbedding.injective hxy')

end KltDP.Geometry.PointBlowupGluing

namespace KltDP.Geometry

/-- The original morphism in IsPointBlowupAt has singleton fibers off its
original center, obtained by transporting the actual puncture isomorphism. -/
theorem IsPointBlowupAt.base_injOn_off_center
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ T.toScheme} {z : T.Point}
    (hb : IsPointBlowupAt S T b z) :
    Set.InjOn b.base (b.base ⁻¹' ({z} : Set T.toScheme)ᶜ) := by
  obtain ⟨c, e, he⟩ := hb.blowup
  letI : CommRing c.R := c.instCommRing
  letI : IsOpenImmersion c.j := c.instOpenImmersion
  letI : c.q.asIdeal.IsMaximal := c.instMaximal
  intro x hx y hy hxy
  have hmap (w : S.Point) :
      (PointBlowupGluing.projection c.j c.q c.isClosed).base (e.hom.base w) = b.base w :=
    congrArg (fun f : S.toScheme ⟶ T.toScheme => f.base w) he
  apply e.hom.isOpenEmbedding.injective
  apply PointBlowupGluing.projection_base_injOn_off_center c.j c.q c.isClosed
  · change (PointBlowupGluing.projection c.j c.q c.isClosed).base (e.hom.base x) ≠ c.j.base c.q
    rw [hmap, c.base_eq]
    exact hx
  · change (PointBlowupGluing.projection c.j c.q c.isClosed).base (e.hom.base y) ≠ c.j.base c.q
    rw [hmap, c.base_eq]
    exact hy
  · exact (hmap x).trans (hxy.trans (hmap y).symm)

end KltDP.Geometry

#print axioms KltDP.Geometry.IsPointBlowupAt.base_injOn_off_center
