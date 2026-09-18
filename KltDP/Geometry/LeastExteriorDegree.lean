import KltDP.Geometry.AmpleQCartierPullbackDegrees
import KltDP.LinearAlgebra.DiscreteDegree
import KltDP.Geometry.Resolution

/-!
# An attained least positive degree on actual exterior minus-one curves

The nonempty family is the subtype of original prime curves which are
minus-one curves and are not contracted by the original morphism. Original
ample pullback positivity and the actual Cartier numerator give the two
proved inputs to the existing discrete minimum theorem. This supporting
lemma does not assert existence of exterior curves or a nef threshold.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RationalWeilIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] [GenericPointPreserving π]

/-- The least positive original Q-Cartier degree is attained by an actual
exterior minus-one curve whenever that actual family is nonempty. -/
theorem exists_least_degree_exterior_minusOne
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • D)
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (hne : ∃ C : S.PrimeCurve, IsMinusOneCurve hS C ∧ ¬ IsExceptionalCurve π C) :
    ∃ P : S.PrimeCurve, IsMinusOneCurve hS P ∧ ¬ IsExceptionalCurve π P ∧
      0 < degreeLinearMap S hS P (QCartierPullback.pullback π D hD) ∧
      IsLeast {d : ℚ | ∃ C : S.PrimeCurve,
        IsMinusOneCurve hS C ∧ ¬ IsExceptionalCurve π C ∧
          d = degreeLinearMap S hS C (QCartierPullback.pullback π D hD)}
        (degreeLinearMap S hS P (QCartierPullback.pullback π D hD)) := by
  let F := {C : S.PrimeCurve // IsMinusOneCurve hS C ∧ ¬ IsExceptionalCurve π C}
  letI : Nonempty F := by
    obtain ⟨C, hminus, hC⟩ := hne
    exact ⟨⟨C, hminus, hC⟩⟩
  let degree : F → ℚ := fun C =>
    degreeLinearMap S hS C.val (QCartierPullback.pullback π D hD)
  have hpositive : ∀ C : F, 0 < degree C := fun C =>
    degreeLinearMap_pullback_pos_of_ample_numerator
      hS π D hD n hn A hA hample C.val C.property.2
  have hintegral : ∀ C : F, ∃ m : ℕ, (m : ℚ) = (n : ℚ) * degree C := fun C =>
    degreeLinearMap_pullback_scaled_integral
      hS π D hD n hn A hA hample C.val C.property.2
  obtain ⟨P, hP, hminimum⟩ :=
    KltDP.LinearAlgebra.DiscreteDegree.exists_positive_minimum degree n hn hpositive hintegral
  refine ⟨P.val, P.property.1, P.property.2, hP, ?_, ?_⟩
  · exact ⟨P.val, P.property.1, P.property.2, rfl⟩
  · rintro d ⟨C, hminus, hC, rfl⟩
    exact hminimum ⟨C, hminus, hC⟩

end KltDP.Geometry.RationalWeilIntersection

namespace KltDP.Geometry.IsResolution

open NormalProjectiveSurface RationalWeilIntersection

/-- For the original resolution and an actual ample anticanonical
Cartier numerator, the original anticanonical pullback has an attained
positive least exterior minus-one degree. Q-Cartier membership is derived
from that numerator, and nonemptiness is required only for this supporting lemma. -/
theorem exists_least_exterior_anticanonical_degree
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π) (KX : X.WeilDivisor)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • (-rationalizeWeilDivisor X KX))
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (hne : ∃ C : S.PrimeCurve,
      IsMinusOneCurve hres.regular C ∧ ¬ IsExceptionalCurve π C) :
    letI : GenericPointPreserving π := ⟨hres.birational.map_genericPoint⟩
    ∃ (hAnti : X.QCartier (-rationalizeWeilDivisor X KX)) (P : S.PrimeCurve),
      IsMinusOneCurve hres.regular P ∧ ¬ IsExceptionalCurve π P ∧
      0 < degreeLinearMap S hres.regular P
        (QCartierPullback.pullback π (-rationalizeWeilDivisor X KX) hAnti) ∧
      IsLeast {d : ℚ | ∃ C : S.PrimeCurve,
        IsMinusOneCurve hres.regular C ∧ ¬ IsExceptionalCurve π C ∧
        d = degreeLinearMap S hres.regular C
          (QCartierPullback.pullback π (-rationalizeWeilDivisor X KX) hAnti)}
        (degreeLinearMap S hres.regular P
          (QCartierPullback.pullback π (-rationalizeWeilDivisor X KX) hAnti)) := by
  letI : IsProper π := hres.isProper
  letI : GenericPointPreserving π := ⟨hres.birational.map_genericPoint⟩
  have hAnti : X.QCartier (-rationalizeWeilDivisor X KX) :=
    (X.qCartier_iff_exists_positive_multiple _).mpr ⟨n, hn, A, hA⟩
  exact ⟨hAnti, exists_least_degree_exterior_minusOne hres.regular π
    (-rationalizeWeilDivisor X KX) hAnti n hn A hA hample hne⟩

end KltDP.Geometry.IsResolution

#check @KltDP.Geometry.IsResolution.exists_least_exterior_anticanonical_degree
#print axioms KltDP.Geometry.RationalWeilIntersection.exists_least_degree_exterior_minusOne
#print axioms KltDP.Geometry.IsResolution.exists_least_exterior_anticanonical_degree
