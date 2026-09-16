import KltDP.Geometry.ProjectiveSpaceDegreeOneAmple
import KltDP.Geometry.AffinePullbackOfNonvanishingCoverAmple

/-!
# Actual ample sheaves from original projective embeddings

Pulling the constructed projective coordinate sheaf through the original
closed immersion supplies a Serre ample line sheaf on every original
scheme projective over a field, including every normal projective surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveSpaceDegreeOneSheaf InvertibleSectionNonvanishingOpen

/-- The original closed-embedding pullback of the constructed coordinate
sheaf is Serre ample on the original source. -/
theorem projectiveSpaceDegreeOne_pullback_isAmple
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k n) [IsClosedImmersion i] :
    AmpleSerre.IsAmple (pullbackInvertibleSheaf i (degreeOne k n)) := by
  letI : NoetherianSpace (projectiveSpace k n) := projectiveSpace_noetherianSpace k n
  letI : NoetherianSpace X := i.isClosedEmbedding.isInducing.noetherianSpace
  apply AffinePullbackOfNonvanishingCoverAmple.isAmple_pullback_of_finite_cover
    i (degreeOne k n) isCompact_univ isQuasiSeparated_univ
    (fun j : ULift.{u} (Fin (n + 1)) => homogeneousSection k n j.down)
  · intro j
    rw [nonvanishingOpen_homogeneousSection]
    exact Proj.isAffineOpen_basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X j.down)
      (ProjectiveChart.coordinate_mem k n j.down) Nat.one_pos
  · intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((chart_cover k n).ge hx)
    exact Opens.mem_iSup.mpr ⟨j, by rwa [nonvanishingOpen_homogeneousSection]⟩

/-- Projectivity over the original field constructs an actual Serre ample
line sheaf; ampleness is a proved result of the original embedding. -/
theorem IsProjectiveOverField.exists_isAmple {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} (hf : IsProjectiveOverField f) :
    ∃ L : InvertibleSheaf X, AmpleSerre.IsAmple L := by
  obtain ⟨n, i, hi, hfactor⟩ := hf
  letI : IsClosedImmersion i := hi
  exact ⟨pullbackInvertibleSheaf i (degreeOne k n),
    projectiveSpaceDegreeOne_pullback_isAmple k n i⟩

/-- Every original normal projective surface has a constructed actual
Serre ample invertible sheaf. -/
theorem NormalProjectiveSurface.exists_isAmple {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) :
    ∃ L : InvertibleSheaf X.toScheme, AmpleSerre.IsAmple L :=
  X.projective.exists_isAmple

end KltDP.Geometry
