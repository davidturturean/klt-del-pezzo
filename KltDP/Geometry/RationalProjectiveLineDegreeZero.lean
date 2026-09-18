import KltDP.Geometry.RationalTreePicardDegreeIdentification

/-!
# Degree-zero frames on an actual projective line over the original field

The existing degree/exponent comparison and Euler transport identify the
chart exponent of an original invertible sheaf with its Euler degree.
The existing zero-exponent frame then trivializes that same sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

open ModuleCohomology

variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (e : Y ≅ projectiveSpace k 1) (f : Y ⟶ Spec (CommRingCat.of k))
  (he : e.hom ≫ projectiveSpaceToSpec k 1 = f) (M : InvertibleSheaf Y)

include he in
/-- The exponent of the original line equals its Euler degree when the
specified projective-line identification respects its field structure. -/
theorem chartExponent_eq_eulerDegree :
    chartExponent k e M = eulerDegree f M := by
  change ProjectiveLineSheafExponent.exponent k (pullbackInvertibleSheaf e.inv M) = _
  rw [← ProjectiveLineDegree.degree_eq_exponent k]
  unfold ProjectiveLineDegree.degree eulerDegree
  rw [eulerCharacteristic_eq_pullback_inv e f (projectiveSpaceToSpec k 1) he M.obj,
    eulerCharacteristic_unit_eq e f (projectiveSpaceToSpec k 1) he]
  rfl

/-- A degree-zero invertible sheaf on this original rational curve has an
actual frame, obtained through the specified isomorphism over the field. -/
def unitIsoOfEulerDegreeZero (hM : eulerDegree f M = 0) :
    M.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  unitIsoOfChartExponentZero k e M ((chartExponent_eq_eulerDegree e f he M).trans hM)

end KltDP.Geometry.RationalTreePicard
