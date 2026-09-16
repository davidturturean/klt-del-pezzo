import KltDP.Geometry.CartierEulerPairingDegree
import KltDP.Geometry.RationalTreePicardProjectiveLine
import KltDP.Geometry.ProjectiveLinePicardExponent
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.InvertibleSheafTensor
import KltDP.Examples.FrobeniusExceptionalEulerUnconditional

/-!
# On `P¹`, the Euler degree of a line bundle is its transition exponent

For an invertible sheaf `L` on the accepted `P¹ = projectiveSpace k 1` let
`degree L := χ(L) − χ(O)` (Stacks 0AYR at rank one). The accepted transition exponent
`ProjectiveLineSheafExponent.exponent` identifies `Pic P¹` with `ℤ`
(`ProjectiveLinePicardExponent.hom_injective`, `monomialLineBundle_exponent`), the admitted 0AYX
(through `eulerDegree_tensor`, `topologicalKrullDim P¹ = 1`, properness) makes `degree` additive
under tensor products, and the accepted point-ideal computation gives
`degree (coordinateIdealLine) = −1` with exponent `−1`. Induction on the exponent through the
monomial line bundles `O(n)` then proves

  **`degree_eq_exponent : degree L = exponent L`** for every invertible sheaf `L` on `P¹`,

in particular `degree (monomialLineBundle n) = n`. Export `f04_projective_line_degree_eq_exponent`.

Hypotheses: `k : Type u`, `[Field k]` only (the `H¹(P¹, O)` finiteness used by the accepted
point-ideal computation is the accepted 02O6 consumer `projectiveLine_unit_hOne_finiteDimensional`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.RationalTreePicard
open KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Examples.FrobeniusProjectiveCoordinatePicard
open KltDP.Examples.FrobeniusExceptionalNormalEuler
open KltDP.Examples.FrobeniusExceptionalEulerUnconditional

universe u

namespace KltDP.Geometry.ProjectiveLineDegree

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance projectiveLineDegreeMonoidal (k : Type u) [Field k] :
    MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

variable (k : Type u) [Field k]

/-- `dim P¹ ≤ 1` (accepted `projectiveSpace_topologicalKrullDim`). -/
theorem dim_le_one : topologicalKrullDim (projectiveSpace k 1) ≤ 1 := by
  rw [projectiveSpace_topologicalKrullDim]
  simp

/-- An invertible sheaf is locally free of rank one. -/
theorem isLocallyFreeOfRank_one {X : Scheme.{u}} (L : InvertibleSheaf X) :
    KltDP.SheafOfModules.IsLocallyFreeOfRank (R := X.ringCatSheaf) L.obj 1 := by
  haveI : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  infer_instance

/-- The Euler degree `deg L := χ(L) − χ(O)` of a line bundle on `P¹`. -/
def degree (L : InvertibleSheaf (projectiveSpace k 1)) : ℤ :=
  eulerCharacteristic (projectiveSpaceToSpec k 1) L.obj -
    eulerCharacteristic (projectiveSpaceToSpec k 1)
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)

theorem degree_eq_picardEulerValue (L : InvertibleSheaf (projectiveSpace k 1)) :
    degree k L = picardEulerValue (projectiveSpaceToSpec k 1) L.toPic -
      picardEulerValue (projectiveSpaceToSpec k 1) 1 := by
  unfold degree
  rw [picardEulerValue_toPic, picardEulerValue_one]

/-- The degree depends only on the Picard class. -/
theorem degree_eq_of_toPic_eq {L M : InvertibleSheaf (projectiveSpace k 1)}
    (h : L.toPic = M.toPic) : degree k L = degree k M := by
  rw [degree_eq_picardEulerValue, degree_eq_picardEulerValue, h]

/-- Equal exponents give equal Picard classes (`Pic P¹ → ℤ` is injective). -/
theorem toPic_eq_of_exponent_eq {L M : InvertibleSheaf (projectiveSpace k 1)}
    (h : exponent k L = exponent k M) : L.toPic = M.toPic := by
  apply ProjectiveLinePicardExponent.hom_injective k
  change Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k L.toPic) =
    Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k M.toPic)
  rw [ProjectiveLinePicardExponent.value_toPic, ProjectiveLinePicardExponent.value_toPic, h]

theorem degree_eq_of_exponent_eq {L M : InvertibleSheaf (projectiveSpace k 1)}
    (h : exponent k L = exponent k M) : degree k L = degree k M :=
  degree_eq_of_toPic_eq k (toPic_eq_of_exponent_eq k h)

/-- The tensor product of two line bundles on `P¹`, as a line bundle. -/
abbrev tensor (L M : InvertibleSheaf (projectiveSpace k 1)) : InvertibleSheaf (projectiveSpace k 1) :=
  InvertibleSheafTensor.tensorInvertibleSheaf L M

@[simp]
theorem tensor_obj (L M : InvertibleSheaf (projectiveSpace k 1)) :
    (tensor k L M).obj = L.obj ⊗ M.obj := rfl

/-- Exponents add under tensor products (accepted `exponent_eq_add_of_tensorIso`). -/
theorem exponent_tensor (L M : InvertibleSheaf (projectiveSpace k 1)) :
    exponent k (tensor k L M) = exponent k L + exponent k M :=
  exponent_eq_add_of_tensorIso k L M (tensor k L M) (Iso.refl _)

/-- **0AYX on `P¹`**: degrees add under tensor products. -/
theorem degree_tensor (L M : InvertibleSheaf (projectiveSpace k 1)) :
    degree k (tensor k L M) = degree k L + degree k M := by
  have h := eulerDegree_tensor (projectiveSpaceToSpec k 1) (dim_le_one k) L.obj M.obj
    (isLocallyFreeOfRank_one L) (isLocallyFreeOfRank_one M)
  unfold degree
  exact h

theorem degree_trivial : degree k (InvertibleSheaf.trivial (projectiveSpace k 1)) = 0 :=
  sub_self _

theorem exponent_trivial : exponent k (InvertibleSheaf.trivial (projectiveSpace k 1)) = 0 :=
  exponent_eq_zero_of_iso_unit k _ (Iso.refl _)

/-- The accepted point-ideal line bundle has degree `−1` (02O6 on `P¹`). -/
theorem degree_coordinateIdealLine : degree k (coordinateIdealLine (k := k)) = -1 :=
  coordinateIdeal_euler_difference_eq_neg_one projectiveLine_unit_hOne_finiteDimensional

theorem degree_monomial_neg_one : degree k (monomialLineBundle k (-1)) = -1 := by
  rw [degree_eq_of_exponent_eq k (L := monomialLineBundle k (-1)) (M := coordinateIdealLine)
    (by rw [monomialLineBundle_exponent, coordinateExponent_eq_neg_one]),
    degree_coordinateIdealLine]

theorem degree_monomial_one : degree k (monomialLineBundle k 1) = 1 := by
  have h := degree_tensor k (monomialLineBundle k 1) (monomialLineBundle k (-1))
  rw [degree_eq_of_exponent_eq k (L := tensor k (monomialLineBundle k 1) (monomialLineBundle k (-1)))
      (M := InvertibleSheaf.trivial (projectiveSpace k 1))
      (by rw [exponent_tensor, monomialLineBundle_exponent, monomialLineBundle_exponent,
        exponent_trivial]; norm_num),
    degree_trivial, degree_monomial_neg_one] at h
  omega

/-- **`deg O(n) = n`** on `P¹`. -/
theorem degree_monomial (n : ℤ) : degree k (monomialLineBundle k n) = n := by
  induction n using Int.induction_on with
  | hz =>
    rw [degree_eq_of_exponent_eq k (L := monomialLineBundle k 0)
      (M := InvertibleSheaf.trivial (projectiveSpace k 1))
      (by rw [monomialLineBundle_exponent, exponent_trivial]), degree_trivial]
  | hp i ih =>
    have h := degree_tensor k (monomialLineBundle k i) (monomialLineBundle k 1)
    rw [← degree_eq_of_exponent_eq k (L := monomialLineBundle k (i + 1))
      (M := tensor k (monomialLineBundle k i) (monomialLineBundle k 1))
      (by rw [exponent_tensor, monomialLineBundle_exponent, monomialLineBundle_exponent,
        monomialLineBundle_exponent]), ih, degree_monomial_one] at h
    exact h
  | hn i ih =>
    have h := degree_tensor k (monomialLineBundle k (-i)) (monomialLineBundle k (-1))
    rw [← degree_eq_of_exponent_eq k (L := monomialLineBundle k (-i - 1))
      (M := tensor k (monomialLineBundle k (-i)) (monomialLineBundle k (-1)))
      (by rw [exponent_tensor, monomialLineBundle_exponent, monomialLineBundle_exponent,
        monomialLineBundle_exponent]; ring), ih, degree_monomial_neg_one] at h
    exact h

/-- **The Euler degree of every line bundle on `P¹` is its transition exponent.** -/
theorem degree_eq_exponent (L : InvertibleSheaf (projectiveSpace k 1)) :
    degree k L = exponent k L := by
  rw [degree_eq_of_exponent_eq k (L := L) (M := monomialLineBundle k (exponent k L))
    (by rw [monomialLineBundle_exponent]), degree_monomial]

end KltDP.Geometry.ProjectiveLineDegree

namespace KltDP.Geometry

open ProjectiveLineDegree

/-- **F04 export: on `P¹`, `χ(L) − χ(O) = exponent L` for every line bundle `L`**, and
`χ(O(n)) − χ(O) = n`. -/
theorem f04_projective_line_degree_eq_exponent (k : Type u) [Field k] :
    (∀ L : InvertibleSheaf (projectiveSpace k 1),
      eulerCharacteristic (projectiveSpaceToSpec k 1) L.obj -
        eulerCharacteristic (projectiveSpaceToSpec k 1)
          (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) =
        ProjectiveLineSheafExponent.exponent k L) ∧
    (∀ n : ℤ,
      eulerCharacteristic (projectiveSpaceToSpec k 1)
          (RationalTreePicard.monomialLineBundle k n).obj -
        eulerCharacteristic (projectiveSpaceToSpec k 1)
          (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = n) :=
  ⟨fun L => degree_eq_exponent k L, fun n => degree_monomial k n⟩

/-- Universe check: a single universe `u`. -/
example (k : Type u) [Field k] (n : ℤ) :
    degree k (RationalTreePicard.monomialLineBundle k n) = n :=
  degree_monomial k n

end KltDP.Geometry
