import KltDP.Compatibility.BirationalRationality
import KltDP.Examples.FrobeniusProductPlaneChart
import KltDP.Examples.FrobeniusStageZeroProjective
import KltDP.Geometry.PlaneBlowupNativeDifferentialBasis

/-!
# The original projective product is birational to the actual affine plane

The existing polynomial-plane chart is open and dense. The existing
polynomial algebra equivalence and the pinned AffineSpace.SpecIso identify
its actual field structure with the specified two-dimensional affine space.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.ProjectiveLineProductRationality

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupSmooth
  FrobeniusProductPlaneChart FrobeniusProjectivePoints FrobeniusStageZeroProjective
  PlaneBlowupNativeDifferentialBasis

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The existing polynomial chart ring gives the actual affine plane. -/
def planeAffineSpaceIso : Spec (CommRingCat.of (planeRing k)) ≅
    𝔸(Fin 2; Spec (CommRingCat.of k)) :=
  Scheme.Spec.mapIso (planeEquiv k).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (Fin 2) (CommRingCat.of k)).symm

/-- This isomorphism respects the original coefficient-field maps. -/
theorem planeAffineSpaceIso_over :
    (planeAffineSpaceIso (k := k)).hom ≫
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = planeStructure := by
  have hconst : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k) ≫
      CommRingCat.ofHom (planeEquiv k).toRingHom = CommRingCat.ofHom planeConstants := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (planeEquiv k).commutes r
  change (Spec.map (CommRingCat.ofHom (planeEquiv k).toRingHom) ≫
    (AffineSpace.SpecIso (Fin 2) (CommRingCat.of k)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hconst]
  rfl

/-- The actual product surface is birational over its original field to
precisely the affine plane indexed by Fin 2. -/
theorem birationalOver_affinePlane :
    Scheme.BirationalOver (projectiveProductSurface (k := k)).structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) := by
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsDominant (planeChart (k := k)) :=
    ⟨(planeChart (k := k)).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hp := Scheme.Hom.birationalOver (planeChart (k := k))
    projectiveProductToSpec planeStructure planeChart_structure
  have ha := Scheme.Hom.birationalOver (planeAffineSpaceIso (k := k)).hom
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
    planeStructure planeAffineSpaceIso_over
  exact hp.symm.trans ha

end KltDP.Examples.ProjectiveLineProductRationality

#check @KltDP.Examples.ProjectiveLineProductRationality.birationalOver_affinePlane
#print axioms KltDP.Examples.ProjectiveLineProductRationality.birationalOver_affinePlane
