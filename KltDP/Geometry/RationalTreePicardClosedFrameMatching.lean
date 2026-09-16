import KltDP.Geometry.RationalTreePicardClosedNodeRestriction
import KltDP.Geometry.RationalTreePicardClosedLineGluing

/-!
# The original line bundle maps into its derived scalar matching sheaf

Actual geometric frames on the two original closed components give two
A-linear coordinate maps on the original global-section module. Their
node transition and its ground-field scalar were derived in preceding
leaves. Those exact coordinates therefore land in the actual scalar
matching kernel, without a matching equation as an input.

The affine counit and the original tilde-kernel comparison give the map
from the original invertible sheaf itself. Bijectivity of this matching
map and global compatibility over the nodal affine charts remain to be
proved; the map alone is not asserted to trivialize the line bundle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]
  (I J : Ideal A) (q : PrimeSpectrum A)
  (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})
  [IsReduced (A ⧸ I ⊔ J)]
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (leftFrame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  (rightFrame : (schemeModulePullback (closedComponentInclusion A J)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf)

/-- The original first-component coordinate map is A-linear. -/
def closedComponentCoordinate : AffineModuleTilde.sectionModule L.obj ⊤ →ₗ[A] A ⧸ I :=
  (closedBranchFrameEquiv A I L leftFrame).toLinearMap.comp
    ((TensorProduct.mk A (AffineModuleTilde.sectionModule L.obj ⊤) (A ⧸ I)).flip 1)

/-- The actual node transition supplies the base scalar used in gluing. -/
def closedFrameScalar : kˣ :=
  reducedNodeScalarUnit A I J q hsupport k
    (closedNodeTransitionUnit A I L J leftFrame rightFrame)

/-- The original component coordinates, with their original scalar maps,
form the pair used by the actual matching kernel. -/
def closedFrameCoordinatePair :
    AffineModuleTilde.sectionModule L.obj ⊤ →ₗ[A] (A ⧸ I) × (A ⧸ J) :=
  (closedComponentCoordinate A I L leftFrame).prod
    (closedComponentCoordinate A J L rightFrame)

/-- The actual node compatibility puts every original section in the
kernel for the derived scalar. No matching condition is assumed. -/
theorem closedFrameCoordinatePair_mem
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    closedFrameCoordinatePair A I J L leftFrame rightFrame m ∈
      LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)) := by
  apply (mem_closedLineKernel_iff A I J
    (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) _).mpr
  change Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)
      (closedBranchFrameEquiv A I L leftFrame (m ⊗ₜ[A] (1 : A ⧸ I))) =
    closedLineGaugeUnit A
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) •
      Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)
        (closedBranchFrameEquiv A J L rightFrame (m ⊗ₜ[A] (1 : A ⧸ J)))
  rw [Units.smul_def, Algebra.smul_def]
  change Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)
      (closedBranchFrameEquiv A I L leftFrame (m ⊗ₜ[A] (1 : A ⧸ I))) =
    algebraMap A (A ⧸ I ⊔ J)
        (algebraMap k A (closedFrameScalar k A I J q hsupport L leftFrame rightFrame : k)) *
      Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)
        (closedBranchFrameEquiv A J L rightFrame (m ⊗ₜ[A] (1 : A ⧸ J)))
  rw [← IsScalarTower.algebraMap_apply k A (A ⧸ I ⊔ J)]
  rw [show algebraMap k (A ⧸ I ⊔ J)
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame : k) =
        (closedNodeTransitionUnit A I L J leftFrame rightFrame : A ⧸ I ⊔ J) from
    reducedNodeScalarUnit_algebraMap A I J q hsupport k _]
  exact closedNodeTransitionUnit_matching A I L J leftFrame rightFrame m

/-- The original global-section map into the actual derived scalar kernel. -/
def closedFrameMatchingLinear :
    AffineModuleTilde.sectionModule L.obj ⊤ →ₗ[A]
      LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)) :=
  (closedFrameCoordinatePair A I J L leftFrame rightFrame).codRestrict _
    (closedFrameCoordinatePair_mem k A I J q hsupport L leftFrame rightFrame)

/-- The map of original module sheaves from the actual line bundle to the
actual matching sheaf, obtained through its proved affine reconstruction. -/
def closedFrameMatchingSheafMap :
    L.obj ⟶ closedLineMatchingSheaf A I J
      (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) := by
  let f : AffineModuleTilde.sectionModule L.obj ⊤ ⟶
      ModuleCat.of A (LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))) :=
    ModuleCat.ofHom
      (X := AffineModuleTilde.sectionModule L.obj ⊤)
      (Y := LinearMap.ker (closedLineDifference A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)))
      (closedFrameMatchingLinear k A I J q hsupport L leftFrame rightFrame)
  exact
    (AffineModuleTilde.invertibleCounitIso L).inv ≫
      AffineModuleTilde.map f ≫
      (AffineModuleTilde.mapIso (ModuleCat.kernelIsoKer
        (closedLineDifferenceHom A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).symm).hom ≫
      (AffineModuleTilde.kernelIso
        (closedLineDifferenceHom A I J
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))).hom

end KltDP.Geometry.RationalTreePicard
