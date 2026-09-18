import KltDP.Geometry.AffineDifferentialExteriorTildeIso
import KltDP.Geometry.CartierEulerPairingDegree
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# The canonical module frame supplied by an actual native basis

Use the already proved native-to-intrinsic exterior isomorphism and the
actual determinant frame. Transport to the range of the original affine
open immersion uses its actual inverse and the original open differential.
No smoothness hypothesis occurs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NativeDifferentialCanonicalFrame

open AffineKaehlerTildeDerivation SmoothCanonicalExteriorComparison

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The original intrinsic exterior sheaf is framed by the native determinant. -/
def sheafFrame (b : Basis (Fin 2) A (KaehlerDifferential k A)) :
    relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k A))) 2 ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  (AffineDifferentialExteriorTildeMap.isoOfBasis k A b).symm ≪≫
    AffineModuleTilde.linearEquivIso
      (M := (differentialModule k A).exteriorPower 2) (N := ModuleCat.of A A)
      (AffineTopDifferentialFrame.determinantEquiv b) ≪≫
    AffineModuleTilde.unitIso A

/-- This is an actual identification O(0) ≅ Ω² on the original affine scheme. -/
def zeroIso [IsIntegral (Spec (CommRingCat.of A))]
    (b : Basis (Fin 2) A (KaehlerDifferential k A)) :
    cartierDivisorModule (Spec (CommRingCat.of A)) 0 ≅
      relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k A))) 2 :=
  cartierDivisorModuleZeroIsoUnit (Spec (CommRingCat.of A)) ≪≫ (sheafFrame k A b).symm

variable [Nonempty (Spec (CommRingCat.of A))] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]

local instance : Nonempty j.opensRange := by
  let y : Spec (CommRingCat.of A) := Classical.choice inferInstance
  exact ⟨⟨j.base y, ⟨y, rfl⟩⟩⟩
local instance : IsIntegral j.opensRange.toScheme := isIntegral_of_isOpenImmersion j.opensRange.ι

/-- The same native frame on the actual open range, with its original structure map. -/
def zeroIsoOnRange (σ : X ⟶ Spec (CommRingCat.of k))
    (hj : j ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (b : Basis (Fin 2) A (KaehlerDifferential k A)) :
    cartierDivisorModule j.opensRange.toScheme 0 ≅
      relativeDifferentialExterior (j.opensRange.ι ≫ σ) 2 := by
  letI : IsIntegral (Spec (CommRingCat.of A)) := isIntegral_of_isOpenImmersion j
  letI : GenericPointPreserving j.isoOpensRange.inv :=
    ⟨genericPoint_eq_of_isOpenImmersion j.isoOpensRange.inv⟩
  have hmap : j.isoOpensRange.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) = j.opensRange.ι ≫ σ := by
    rw [← hj, ← Category.assoc, j.isoOpensRange_inv_comp]
  have hzero : DominantCartierPullback.pullbackHom j.isoOpensRange.inv
      (0 : CartierDivisor (Spec (CommRingCat.of A))) = 0 := map_zero _
  exact eqToIso (congrArg (cartierDivisorModule j.opensRange.toScheme) hzero.symm) ≪≫
    CartierRationalCoordinate.canonicalOpenPullbackIso j.isoOpensRange.inv
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) (j.opensRange.ι ≫ σ)
      hmap 0 (zeroIso k A b)

end KltDP.Geometry.NativeDifferentialCanonicalFrame
