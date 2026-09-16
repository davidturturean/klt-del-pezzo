import KltDP.Geometry.ProjectiveLineDegreeOneSections
import KltDP.Geometry.AmpleOfAffineNonvanishingCover

/-!
# The original degree-one projective line bundle is Serre ample

The proof uses the constructed original coordinate sections and their
affine nonvanishing cover. The ample line sheaf is the existing monomial
line bundle of exponent one on the original projective line over any field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveLineDegreeOneAmple

open RationalTreePicard ProjectiveLineDegreeOneSections
open ProjectiveLineComparison InvertibleSectionNonvanishingOpen

variable (k : Type u) [Field k]

/-- The existing actual degree-one projective line bundle is ample in the
original Serre sense, with no ample or global-generation hypothesis. -/
theorem degreeOne_isAmple : AmpleSerre.IsAmple (monomialLineBundle k 1) := by
  letI : NoetherianSpace (projectiveSpace k 1) := projectiveSpace_noetherianSpace k 1
  apply AmpleOfAffineNonvanishingCover.isAmple_of_finite_cover (monomialLineBundle k 1)
    isCompact_univ isQuasiSeparated_univ (standardSection k)
  · intro i
    rw [nonvanishingOpen_standardSection]
    exact chartOpen_isAffineOpen k i.down
  · intro x hx
    obtain ⟨i, hi⟩ := ProjectiveLineCanonicalFrame.chartOpen_cover k x
    exact Opens.mem_iSup.mpr ⟨i, by rwa [nonvanishingOpen_standardSection]⟩

end KltDP.Geometry.ProjectiveLineDegreeOneAmple
