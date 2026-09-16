import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.AmpleOfAffineNonvanishingCover

/-! # An actual Serre ample sheaf on every original projective space -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The original degree-one homogeneous line sheaf on Pⁿ is ample in
the existing coherent-sheaf Serre sense, over any field. -/
theorem degreeOne_isAmple : AmpleSerre.IsAmple (degreeOne k n) := by
  letI : NoetherianSpace (projectiveSpace k n) := projectiveSpace_noetherianSpace k n
  apply AmpleOfAffineNonvanishingCover.isAmple_of_finite_cover (degreeOne k n)
    isCompact_univ isQuasiSeparated_univ
    (fun i : ULift.{u} (Fin (n + 1)) => homogeneousSection k n i.down)
  · intro i
    rw [nonvanishingOpen_homogeneousSection]
    exact Proj.isAffineOpen_basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X i.down)
      (ProjectiveChart.coordinate_mem k n i.down) Nat.one_pos
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((chart_cover k n).ge hx)
    exact Opens.mem_iSup.mpr ⟨i, by rwa [nonvanishingOpen_homogeneousSection]⟩

/-- Every original projective space, including P², has an actual ample
invertible sheaf; the witness is the constructed original coordinate sheaf. -/
theorem exists_isAmple :
    ∃ L : InvertibleSheaf (projectiveSpace k n), AmpleSerre.IsAmple L :=
  ⟨degreeOne k n, degreeOne_isAmple k n⟩

end KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
