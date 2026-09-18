import KltDP.Geometry.KltExceptionalNullRestriction
import KltDP.Geometry.ExceptionalAmpleProjectionLineBundle
import KltDP.Geometry.NefPositiveSquareKeelRestriction

/-!
# Semiampleness of the original exceptional projection

For an actual minimal klt resolution in positive characteristic, clear the
denominators of the original exceptional projection of an ample line bundle.
The same actual line bundle has nef positive square and precisely the
original exceptional null locus. Its actual restriction is trivial by the
proved original forest geometry. Keel then makes this line semiample, and
its complete systems are eventually birational on the original surface.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open ExceptionalAmpleProjection

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  {π : S.toScheme ⟶ X.toScheme}

/-- The original projected class has an actual semiample positive integral
representative. The complete-system map has exactly the original exceptional
prime curves, and all rational-tree restriction data are proved internally. -/
theorem IsMinimalResolution.exists_semiample_original_projection
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (H : InvertibleSheaf S.toScheme) (hH : AmpleSerre.IsAmple H) :
    letI : IsProper π := hmin.toIsResolution.isProper
    letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
      S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hmin.birational
    ∃ n : ℕ, 0 < n ∧ ∃ L : InvertibleSheaf S.toScheme,
      lineClass S L = (n : ℚ) • originalProjectedClass π hbir (lineClass S H) ∧
      Positivity.IsNef S.structureMorphism L ∧
      0 < S.selfIntersection hmin.regular L ∧
      Positivity.IsBig S.structureMorphism L ∧
      Positivity.nullLocus S.structureMorphism L = ActualExceptionalLocus.primeSupport π ∧
      (∀ C : S.PrimeCurve, C.restrictionDegree L = 0 ↔ IsExceptionalCurve π C) ∧
      Positivity.IsSemiample L ∧
      KeelCompleteSystem.EventuallyBirational S.structureMorphism L := by
  letI : IsProper π := hmin.toIsResolution.isProper
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  obtain ⟨n, hn, L, hclass, hnef, hpositive, hbig, hnull, hdegree⟩ :=
    exists_nef_big_original_exceptional_nullLocus π hmin.over_base hbir H hH
  obtain ⟨e⟩ := hmin.exceptional_nullRestriction_trivial_of_klt hklt L hnull
    (fun C hC => (hdegree C).mpr hC)
  exact ⟨n, hn, L, hclass, hnef, hpositive, hbig, hnull, hdegree,
    NefPositiveSquareKeelRestriction.isSemiample_of_nullRestriction_unitIso
      S p hp L hnef hpositive e,
    NefPositiveSquareKeelRestriction.eventuallyBirational S L hnef hpositive⟩

end KltDP.Geometry

#check @KltDP.Geometry.IsMinimalResolution.exists_semiample_original_projection
#print axioms KltDP.Geometry.IsMinimalResolution.exists_semiample_original_projection
