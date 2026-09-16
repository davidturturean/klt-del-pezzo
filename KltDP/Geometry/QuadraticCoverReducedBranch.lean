import KltDP.Geometry.QuadraticCoverAtlasIntegralWithEmptyCharts
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reduced local branch equations make the original cover integral

In an integrally closed domain, a hypothetical fraction-field square root
of a regular element lies in the original ring. If the original principal
quotient is reduced, the root's square being zero in that quotient forces
the root itself into the principal ideal. Cancellation then forces the
original equation to be a unit. Thus a nonzero nonunit equation with reduced
quotient is nonsquare in the original fraction field.

The geometric adapter applies this to the actual germ of an original atlas
branch section. The actual stalk-to-function-field map agrees with the
original generic germ map, by the structure sheaf's specialization identity.
The existing empty-chart-compatible theorem proves integrality of the same
glued scheme. Neither nonsquareness nor a valuation value is an input.

The reducedness of the literal branch quotient, local integral closedness,
nonzero section and nonunit germ are explicit original local inputs. This
module does not establish those inputs from the manuscript's smooth reduced
branch divisor, identify a geometric branch-subscheme stalk with the quotient,
or prove smoothness of the cover. There is no characteristic restriction.

Reuse: pinned IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow,
Ideal.Quotient.eq_zero_iff_dvd, IsNilpotent.eq_zero and the actual germ maps.
Newer official Mathlib a4d9f2fdd2f64b55969042eef459606961dc63a2 retains
the power descent and quotient APIs (Apache-2.0); no source port is needed.
-/

noncomputable section

universe u v

namespace KltDP.Geometry.QuadraticCover

/-- A nonzero nonunit defining a reduced principal quotient of a normal
domain has no square root in its actual fraction field. -/
theorem nonsquare_of_reduced_branch_quotient
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (s : R) (hs : s ≠ 0) (hnonunit : ¬IsUnit s)
    (hred : IsReduced (R ⧸ Ideal.span ({s} : Set R))) :
    ∀ x : K, x ^ 2 ≠ algebraMap R K s := by
  letI := hred
  intro x hx
  have hxint : IsIntegral R (x ^ 2) := by
    rw [hx]
    exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := R) (K := K) (x := x) (n := 2) (by decide) hxint
  have hy2 : y ^ 2 = s := by
    apply IsFractionRing.injective R K
    rw [map_pow, hy, hx]
  have hynil : IsNilpotent (Ideal.Quotient.mk (Ideal.span ({s} : Set R)) y) := by
    refine ⟨2, ?_⟩
    rw [← map_pow, hy2, Ideal.Quotient.mk_singleton_self]
  obtain ⟨a, ha⟩ := (Ideal.Quotient.eq_zero_iff_dvd s y).mp hynil.eq_zero
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hs
    rw [← hy2, hy0, zero_pow (by decide)]
  have hunit : y * a = 1 := by
    apply mul_left_cancel₀ hy0
    calc
      y * (y * a) = (y * y) * a := (mul_assoc y y a).symm
      _ = s * a := by rw [← pow_two, hy2]
      _ = y := ha.symm
      _ = y * 1 := (mul_one y).symm
  apply hnonunit
  rw [← hy2]
  exact (isUnit_of_mul_eq_one y a hunit).pow 2

end KltDP.Geometry.QuadraticCover

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry

private theorem section_toFunctionField_eq_stalk (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      X.germToFunctionField U s := by
  change (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial))
      ((X.presheaf.germ U x hx) s) = X.germToFunctionField U s
  exact ConcreteCategory.congr_hom
    (X.presheaf.germ_stalkSpecializes hx ((genericPoint_spec X).specializes trivial)) s

/-- Original local branch data imply nonsquareness of the original section
under the canonical generic-point germ map. The quotient is the literal
stalk quotient by that section's germ, not a replacement branch ring. -/
theorem functionField_nonsquare_of_reduced_branch_stalk
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] (x : X) (hx : x ∈ U) (s : Γ(X, U))
    (hnormal : IsIntegrallyClosed (X.presheaf.stalk x)) (hs : s ≠ 0)
    (hnonunit : ¬IsUnit (X.presheaf.germ U x hx s))
    (hred : _root_.IsReduced
      ((X.presheaf.stalk x) ⧸ Ideal.span ({X.presheaf.germ U x hx s} :
        Set (X.presheaf.stalk x)))) :
    ∀ y : X.functionField, y ^ 2 ≠ X.germToFunctionField U s := by
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := hnormal
  letI : IsDomain (X.presheaf.stalk x) :=
    Function.Injective.isDomain (algebraMap (X.presheaf.stalk x) X.functionField)
      (IsFractionRing.injective _ _)
  have hg0 : X.presheaf.germ U x hx s ≠ 0 := by
    intro hzero
    apply hs
    apply germ_injective_of_isIntegral X x hx
    simpa only [map_zero] using hzero
  rw [← section_toFunctionField_eq_stalk X U x hx s]
  exact QuadraticCover.nonsquare_of_reduced_branch_quotient
    (↥X.functionField) (X.presheaf.germ U x hx s) hg0 hnonunit hred

namespace QuadraticCoverAtlas.Data

/-- A reduced local branch equation at one original base point proves
integrality of the unchanged glued quadratic cover. Empty unselected
charts are allowed, and the nonsquare condition is proved from the local
quotient rather than supplied. -/
theorem scheme_isIntegral_of_reduced_branch_stalk
    {X : Scheme.{u}} [IsIntegral X] {ι : Type u}
    (D : QuadraticCoverAtlas.Data X ι) (i : ι) (x : X) (hx : x ∈ D.opens i)
    (hnormal : IsIntegrallyClosed (X.presheaf.stalk x)) (hs : D.sections i ≠ 0)
    (hnonunit : ¬IsUnit (X.presheaf.germ (D.opens i) x hx (D.sections i)))
    (hred : _root_.IsReduced
      ((X.presheaf.stalk x) ⧸ Ideal.span
        ({X.presheaf.germ (D.opens i) x hx (D.sections i)} :
          Set (X.presheaf.stalk x)))) : IsIntegral D.scheme := by
  letI : Nonempty (D.opens i) := ⟨⟨x, hx⟩⟩
  exact D.scheme_isIntegral_of_selected_chart_nonsquare i
    (functionField_nonsquare_of_reduced_branch_stalk X (D.opens i) x hx
      (D.sections i) hnormal hs hnonunit hred)

end QuadraticCoverAtlas.Data

end KltDP.Geometry
