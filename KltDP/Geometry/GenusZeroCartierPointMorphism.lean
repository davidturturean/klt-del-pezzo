import KltDP.Geometry.GenusZeroCartierPointLinearSystem
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-! The actual arithmetic genus-zero hypothesis supplies the H1 vanishing
needed by the original Cartier-point linear system. No smoothness is assumed.
The actual rational Cartier point is still an explicit input to this helper. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalPoint

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [hiClosed : IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

include hiClosed hker in
/-- The original genus-zero curve maps to P1 with the original point bundle
as the pullback of O(1). Its H1 vanishing follows from properness and genus zero. -/
theorem exists_projectiveLine_morphism_of_genus_zero
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hi : i ≫ f = 𝟙 _)
    (hgenus : CurveCanonical.genus f = 0) :
    ∃ g : X ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = f ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅ cartierDivisorModule X E) := by
  letI := baseModule f (_root_.SheafOfModules.unit X.ringCatSheaf) 1
  letI : FiniteDimensional k (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1) :=
    KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_invertible_field_finiteDimensional
      f (InvertibleSheaf.trivial X) 1
  have hH1 : Subsingleton (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1) :=
    Module.finrank_zero_iff.mp hgenus
  exact exists_projectiveLine_morphism E hE i hker f hi hH1

#print axioms exists_projectiveLine_morphism_of_genus_zero

end KltDP.Geometry.CartierRationalPoint
