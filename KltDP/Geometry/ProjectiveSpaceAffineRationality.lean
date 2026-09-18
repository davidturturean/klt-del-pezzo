import KltDP.Compatibility.BirationalRationality
import KltDP.Geometry.ProjectiveSpaceCoordinateCharts
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# Original projective space and its affine chart over the same field

The existing dehomogenization equivalence identifies the original first
projective chart with the affine space indexed by Fin n. Its constants
formula preserves the field map. The chart is open and dense in the
original integral projective space, giving the actual partial isomorphism.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual first chart is the specified n-dimensional affine space. -/
def chartAffineSpaceIso : Spec (CommRingCat.of (chartRing k n)) ≅
    𝔸(Fin n; Spec (CommRingCat.of k)) :=
  Scheme.Spec.mapIso (coordinateRingEquiv k n).symm.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (Fin n) (CommRingCat.of k)).symm

/-- The chart identification preserves the original coefficient-field map. -/
theorem chartAffineSpaceIso_over :
    (chartAffineSpaceIso k n).hom ≫
      (𝔸(Fin n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
        Spec.map (CommRingCat.ofHom (constants k n)) := by
  have hconst : CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k n) ≫
      CommRingCat.ofHom (coordinateRingEquiv k n).symm.toRingHom =
        CommRingCat.ofHom (constants k n) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change (coordinateRingEquiv k n).symm (MvPolynomial.C r) = constants k n r
    apply (coordinateRingEquiv k n).injective
    rw [RingEquiv.apply_symm_apply, coordinateRingEquiv_constants]
  change (Spec.map (CommRingCat.ofHom (coordinateRingEquiv k n).symm.toRingHom) ≫
    (AffineSpace.SpecIso (Fin n) (CommRingCat.of k)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hconst]

/-- Projective space is birational over the original field to precisely
the affine space with one fewer homogeneous coordinate. -/
theorem birationalOver_affineSpace :
    Scheme.BirationalOver (projectiveSpaceToSpec k n)
      (𝔸(Fin n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) := by
  letI : IsIntegral (projectiveSpace k n) := projectiveSpace_isIntegral k n
  letI : IsDomain (chartRing k n) := chartRing_isDomain k n
  letI : IsDominant (chartMorphism k n) :=
    ⟨(chartMorphism k n).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hp := Scheme.Hom.birationalOver (chartMorphism k n)
    (projectiveSpaceToSpec k n) (Spec.map (CommRingCat.ofHom (constants k n)))
    (coordinateChartMorphism_over_base k n 0)
  have ha := Scheme.Hom.birationalOver (chartAffineSpaceIso k n).hom
    (𝔸(Fin n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (constants k n))) (chartAffineSpaceIso_over k n)
  exact hp.symm.trans ha

/-- Rationality through either original chart presentation is equivalent,
with the supplied scheme and its structure morphism unchanged. -/
theorem birationalOver_projectiveSpace_iff {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    Scheme.BirationalOver f (projectiveSpaceToSpec k n) ↔
      Scheme.BirationalOver f
        (𝔸(Fin n; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  ⟨fun h => h.trans (birationalOver_affineSpace k n),
    fun h => h.trans (birationalOver_affineSpace k n).symm⟩

end KltDP.Geometry.ProjectiveChart

#check @KltDP.Geometry.ProjectiveChart.birationalOver_affineSpace
#print axioms KltDP.Geometry.ProjectiveChart.birationalOver_affineSpace
