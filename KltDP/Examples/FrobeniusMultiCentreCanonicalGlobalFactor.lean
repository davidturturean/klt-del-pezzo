import KltDP.Examples.FrobeniusMultiCentreCanonicalClusterFactor
import KltDP.Examples.FrobeniusMultiCentreCanonicalComplementFactor
import KltDP.Examples.FrobeniusMultiCentreCanonicalLocalFormula
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The normalized original finite-centre canonical factor

The original cluster opens and unchanged open cover the actual finite-centre
surface. Their normalized factors are isomorphisms through the same original
monic exceptional-tensor inclusion. The accepted monic-factor gluing theorem
constructs the global isomorphism, retaining the original whole differential.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalGlobalFactor

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalDifferentialCharts
open FrobeniusMultiCentreCanonicalTarget FrobeniusMultiCentreCanonicalClusterFactor
open FrobeniusMultiCentreCanonicalComplementFactor FrobeniusMultiCentreCanonicalLocalFormula

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The actual normalized factors on the already proved original covering opens. -/
def canonicalOpenFactorIso (q n : ℕ) (a : Fin n → k) (c : Option (Fin n)) :
    (schemeModulePullback (canonicalCoverOpen q n a c).ι).obj
        ((schemeModulePullback (multiProjection (q + 1) n a)).obj (baseTop (k := k))) ≅
      (schemeModulePullback (canonicalCoverOpen q n a c).ι).obj (multiCanonicalTarget (q + 1) n a) :=
  match c with
  | none => complementCanonicalFactorIso q n a
  | some i => clusterCanonicalFactorIso q n a i

theorem canonicalOpenFactorIso_comp (q n : ℕ) (a : Fin n → k) (c : Option (Fin n)) :
    (canonicalOpenFactorIso q n a c).hom ≫
        (schemeModulePullback (canonicalCoverOpen q n a c).ι).map (multiCanonicalInclusion (q + 1) n a) =
      (schemeModulePullback (canonicalCoverOpen q n a c).ι).map (multiDifferentialMap (q + 1) n a) := by
  cases c with
  | none => exact complementCanonicalFactorIso_comp q n a
  | some i => exact clusterCanonicalFactorIso_comp q n a i

variable [IsAlgClosed k]

/-- The actual global canonical isomorphism is the original monic factor on the original cover. -/
def multiCanonicalFactorIso (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    (schemeModulePullback (multiProjection (q + 1) n a)).obj (baseTop (k := k)) ≅
      multiCanonicalTarget (q + 1) n a := by
  letI := multiCanonicalInclusion_mono q n a ha
  exact schemeModuleMonicFactorIsoOnOpenCover (canonicalCoverOpen q n a)
    (mem_canonicalCoverOpen q n a ha) (multiCanonicalInclusion (q + 1) n a)
    (multiDifferentialMap (q + 1) n a) (canonicalOpenFactorIso q n a)
    (canonicalOpenFactorIso_comp q n a)

/-- Its composite is the original differential, fixing the global factor and all local normalizations. -/
theorem multiCanonicalFactorIso_comp (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    (multiCanonicalFactorIso q n a ha).hom ≫ multiCanonicalInclusion (q + 1) n a =
      multiDifferentialMap (q + 1) n a := by
  letI := multiCanonicalInclusion_mono q n a ha
  exact schemeModuleMonicFactorIsoOnOpenCover_comp (canonicalCoverOpen q n a)
    (mem_canonicalCoverOpen q n a ha) (multiCanonicalInclusion (q + 1) n a)
    (multiDifferentialMap (q + 1) n a) (canonicalOpenFactorIso q n a)
    (canonicalOpenFactorIso_comp q n a)

end KltDP.Examples.FrobeniusMultiCentreCanonicalGlobalFactor
