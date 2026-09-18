import KltDP.Geometry.PointBlowupTopDifferential
import KltDP.Geometry.SchemeTopDifferentialFactorSquare
import KltDP.Geometry.SmoothPointBlowupAffineIdealFactor

/-!
# The actual whole-point factor on its original affine blowup piece

The derived affine Rees factor is transported through the original affine
square and the original global-center-fiber kernel comparison. The only
coordinate input here is an actual centered standard-smooth plane map;
the smooth-surface producer obtains that map internally in the final join.
No local differential or ideal compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.PointBlowupTopDifferential

open PointBlowupGluing SmoothPointBlowupAffineCanonicalFactor

local instance pointAffineModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k R)))

include hj in
/-- The original affine piece has exactly its original affine field structure. -/
theorem affine_structure :
    affineBlowupι j q hclosed ≫ (projection j q hclosed ≫ f) =
      AffineBlowupTopDifferential.structureMap k R q.asIdeal := by
  change affineBlowupι j q hclosed ≫ (projection j q hclosed ≫ f) =
    AffineBlowup.toSpec q.asIdeal ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  rw [← Category.assoc, affineBlowupι_projection, Category.assoc, hj]

/-- The inverse original affine kernel comparison preserves the literal inclusion. -/
theorem affineKernelIso_inclusion :
    (globalCenterFiberIdealAffineIso j q hclosed).inv ≫
        pulledKernelInclusion (globalCenterFiberι j q hclosed) (affineBlowupι j q hclosed) =
      schemeKernelIdealι (AffineBlowup.exceptionalι q.asIdeal) := by
  rw [Iso.inv_comp_eq]
  exact (globalCenterFiberIdealAffineIso_hom_ι j q hclosed).symm

variable (φ : KltDP.Examples.FrobeniusBlowupContact.planeRing k →ₐ[k] R)
    (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)
    (hcenter : extendedCenter k φ = q.asIdeal)

/-- The original global source factors into the original global exceptional tensor on its affine piece. -/
def affineFactorIso :
    (schemeModulePullback (affineBlowupι j q hclosed)).obj
        ((schemeModulePullback (projection j q hclosed)).obj (sourceSheaf f 2)) ≅
      (schemeModulePullback (affineBlowupι j q hclosed)).obj
        (exceptionalTensor f j q hclosed 2) :=
  SchemeTopDifferentialFactorSquare.factorIso
    (f := f) (π := projection j q hclosed) (l := affineBlowupι j q hclosed)
    (c := j) (b := AffineBlowup.toSpec q.asIdeal)
    (hsq := affineBlowupι_projection j q hclosed)
    (g := projection j q hclosed ≫ f)
    (p := Spec.map (CommRingCat.ofHom (algebraMap k R))) (hp := hj)
    (q := AffineBlowupTopDifferential.structureMap k R q.asIdeal)
    (hl := affine_structure f j q hclosed hj) (n := 2)
    (eJ := (globalCenterFiberIdealAffineIso j q hclosed).symm)
    (e := factorIsoOfIdealEq k φ hφ q.asIdeal hcenter)

/-- The actual whole blowdown differential is preserved on the original affine piece. -/
theorem affineFactorIso_comp :
    (affineFactorIso f j q hclosed hj φ hφ hcenter).hom ≫
        (schemeModulePullback (affineBlowupι j q hclosed)).map
          (exceptionalInclusion f j q hclosed 2) =
      (schemeModulePullback (affineBlowupι j q hclosed)).map
        (blowdownMap f j q hclosed 2) :=
  SchemeTopDifferentialFactorSquare.factorIso_comp
    (f := f) (π := projection j q hclosed) (l := affineBlowupι j q hclosed)
    (c := j) (b := AffineBlowup.toSpec q.asIdeal)
    (hsq := affineBlowupι_projection j q hclosed)
    (g := projection j q hclosed ≫ f) (hg := rfl)
    (p := Spec.map (CommRingCat.ofHom (algebraMap k R))) (hp := hj)
    (q := AffineBlowupTopDifferential.structureMap k R q.asIdeal)
    (hl := affine_structure f j q hclosed hj) (hb := rfl) (n := 2)
    (i := schemeKernelIdealι (globalCenterFiberι j q hclosed))
    (j := schemeKernelIdealι (AffineBlowup.exceptionalι q.asIdeal))
    (eJ := (globalCenterFiberIdealAffineIso j q hclosed).symm)
    (hJ := affineKernelIso_inclusion j q hclosed)
    (e := factorIsoOfIdealEq k φ hφ q.asIdeal hcenter)
    (he := factorIsoOfIdealEq_comp k φ hφ q.asIdeal hcenter)

end KltDP.Geometry.PointBlowupTopDifferential
