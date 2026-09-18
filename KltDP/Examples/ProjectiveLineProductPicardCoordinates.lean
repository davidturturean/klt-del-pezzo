import KltDP.Examples.ProjectiveLineProductPicardGeneration
import KltDP.Examples.FrobeniusRulingPairingValues

/-!
# Original ruling restriction degrees recover the two Picard coefficients

The actual zero fibers have the previously proved intersection matrix
with zero diagonal and off-diagonal entries one. Restriction degree on
the horizontal and vertical fibers therefore recovers the first and
second ruling coefficients, respectively. Together with generation this
gives an equivalence with the original sheaf Picard group.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Examples.ProjectiveLineProductPicardGeneration

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusStageZeroProjective
open FrobeniusGraphPicardClassFiberClasses FrobeniusRulingClassPairing
open FrobeniusRulingPairingValues

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Keep the original raw product Picard carrier explicit at the degree boundary. -/
private def horizontalDegreeHom : Additive (projectiveProduct k).Pic →+ ℤ :=
  (projectiveProductSurface (k := k)).picardRestrictionDegreeHom
    (horizontalPrimeCurve (0 : k))

private def verticalDegreeHom : Additive (projectiveProduct k).Pic →+ ℤ :=
  (projectiveProductSurface (k := k)).picardRestrictionDegreeHom
    (verticalPrimeCurve (0 : k))

/-- The two coordinates are original curve restriction degrees. -/
def rulingCoordinates : Additive (projectiveProduct k).Pic →+ ℤ × ℤ :=
  (horizontalDegreeHom (k := k)).prod verticalDegreeHom

private theorem horizontalDegree_first : horizontalDegreeHom (firstFiberClass (k := k)) = 1 :=
  (basePairing_horizontal_right firstFiberClass (0 : k)).symm.trans
    basePairing_first_second_one

private theorem horizontalDegree_second : horizontalDegreeHom (secondFiberClass (k := k)) = 0 :=
  (basePairing_horizontal_right secondFiberClass (0 : k)).symm.trans
    basePairing_second_self_zero

private theorem verticalDegree_first : verticalDegreeHom (firstFiberClass (k := k)) = 0 :=
  (basePairing_vertical_right firstFiberClass (0 : k)).symm.trans
    basePairing_first_self_zero

private theorem verticalDegree_second : verticalDegreeHom (secondFiberClass (k := k)) = 1 :=
  (basePairing_vertical_right secondFiberClass (0 : k)).symm.trans
    basePairing_second_first_one

/-- Perform finite-group-coordinate normalization before substituting the actual sheaf objects. -/
private theorem degree_prod_linear_combination {A : Type*} [AddCommGroup A]
    (p q : A →+ ℤ) (a b : A)
    (hpa : p a = 1) (hpb : p b = 0) (hqa : q a = 0) (hqb : q b = 1)
    (v : ℤ × ℤ) :
    (p.prod q) (v.1 • a + v.2 • b) = v := by
  apply Prod.ext
  · change p (v.1 • a + v.2 • b) = v.1
    rw [map_add, map_zsmul, map_zsmul, hpa, hpb]
    simp
  · change q (v.1 • a + v.2 • b) = v.2
    rw [map_add, map_zsmul, map_zsmul, hqa, hqb]
    simp

/-- Actual restriction degrees are a left inverse to the ruling class map. -/
theorem rulingCoordinates_rulingClassHom (v : ℤ × ℤ) :
    rulingCoordinates (rulingClassHom (k := k) v) = v :=
  degree_prod_linear_combination
    (horizontalDegreeHom (k := k)) (verticalDegreeHom (k := k))
    firstFiberClass secondFiberClass horizontalDegree_first horizontalDegree_second
    verticalDegree_first verticalDegree_second v

/-- Distinct integer ruling coefficients give distinct actual Picard classes. -/
theorem rulingClassHom_injective : Function.Injective (rulingClassHom (k := k)) := by
  have h : Function.LeftInverse (rulingCoordinates (k := k)) rulingClassHom :=
    rulingCoordinates_rulingClassHom
  exact h.injective

/-- The original sheaf Picard group has the original two ruling classes as an integral basis. -/
def rulingPicardEquiv : ℤ × ℤ ≃+ Additive (projectiveProduct k).Pic :=
  AddEquiv.ofBijective rulingClassHom ⟨rulingClassHom_injective, rulingClassHom_surjective⟩

theorem rulingPicardEquiv_apply (x y : ℤ) :
    rulingPicardEquiv (k := k) (x, y) = x • firstFiberClass + y • secondFiberClass := rfl

end KltDP.Examples.ProjectiveLineProductPicardGeneration
