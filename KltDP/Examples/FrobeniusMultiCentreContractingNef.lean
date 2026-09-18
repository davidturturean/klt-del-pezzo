import KltDP.Examples.FrobeniusMultiCentreContractingClass
import KltDP.Examples.FrobeniusMultiCentreRulingNef
import KltDP.Geometry.PrimeCurveNefSum

/-!
# Nefness of the original Frobenius contracting class

The original strict graph is an actual prime curve by its proved projective
line parametrization. Its Cartier class is the negative of its actual kernel
line. The original second ruling is nef, and the computed class M has degree
zero on that graph. Distinct-prime intersection positivity therefore proves
nonnegative M-degree on every original prime curve. A Cartier representative
and its actual invertible sheaf are constructed using the proved surjectivity
of the original Cartier-to-Picard map. No contraction is assumed or constructed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingNef

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveOfClosedImmersion PrimeCurveTransversalPoint PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphProjectiveLine
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreRulingNefClasses FrobeniusMultiCentreRulingNef
open FrobeniusMultiCentreContractingClass

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original global strict graph as an actual prime curve of the surface. -/
def graphPrimeCurve : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve :=
  primeCurveOfIsoProjectiveLine (multiSurfaceSurface (q + 1) n a ha hproj)
    (graphStrictι (q + 1) n a) (globalGraphIsoProjectiveLine (q + 1) n a)

@[simp] theorem coe_graphPrimeCurve :
    (graphPrimeCurve q n a ha hproj :
      Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) =
      Set.range (graphStrictι (q + 1) n a).base := rfl

/-- Its intrinsic Cartier class is the original computed graph-kernel class. -/
theorem graphPrimeCurve_cartierClass :
    cartierPicardHom (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      ((multiSurfaceSurface (q + 1) n a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
        (graphPrimeCurve q n a ha hproj)) =
      -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic := by
  letI := isIntegral_of_iso_projectiveLine (globalGraphIsoProjectiveLine (q + 1) n a)
  exact cartierPicardHom_primeCurveCartier_of_kernel
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (graphPrimeCurve q n a ha hproj) (graphStrictι (q + 1) n a)
    (coe_graphPrimeCurve q n a ha hproj) (multiGraphStrictKernelLine q n a ha) rfl

/-- The original class M has actual restriction degree zero on the graph. -/
theorem contractingClass_graph_degree :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
      (graphPrimeCurve q n a ha hproj) (contractingClass q n a ha) = 0 := by
  rw [← pairing_primeCurve_right (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj), graphPrimeCurve_cartierClass]
  exact contractingClass_graph_pairing q n a ha hproj

/-- At n ≥ 2 this is the original curve plus an actual nonnegative nef power. -/
theorem contractingClass_eq_curveNefSum (hn : 2 ≤ n) :
    contractingClass q n a ha = PrimeCurveNefSum.curveNefSumClass
      (multiSurfaceSurface (q + 1) n a ha hproj)
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (graphPrimeCurve q n a ha hproj) (secondRulingLine (q + 1) n a) (n - 2) := by
  rw [PrimeCurveNefSum.curveNefSumClass, graphPrimeCurve_cartierClass]
  have hline : Additive.ofMul (secondRulingLine (q + 1) n a).toPic =
      multiSecondFiberClass (q + 1) n a :=
    FrobeniusMultiCentreRulingNefClasses.secondRulingLine_class (q + 1) n a
  calc
    contractingClass q n a ha =
        -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic +
          (n - 2) • multiSecondFiberClass (q + 1) n a := by
      rw [contractingClass, ← natCast_zsmul]
      simp only [Nat.cast_sub hn, Nat.cast_ofNat]
    _ = _ := congrArg (fun c : Additive (multiSurface (q + 1) n a).Pic =>
      -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic + (n - 2) • c) hline.symm

/-- Every original prime curve has nonnegative degree against M. -/
theorem contractingClass_degree_nonneg (hn : 2 ≤ n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve) :
    0 ≤ (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
      (contractingClass q n a ha) := by
  have hB := contractingClass_graph_degree q n a ha hproj
  rw [contractingClass_eq_curveNefSum q n a ha hproj hn] at hB ⊢
  exact PrimeCurveNefSum.degree_nonneg _ _ _ _ _
    (secondRulingLine_isNef (q + 1) n a ha hproj) (le_of_eq hB.symm) C

/-- A Cartier divisor representing the original, already constructed M class. -/
def contractingDivisor : CartierDivisor (multiSurfaceSurface (q + 1) n a ha hproj).toScheme :=
  (cartierPicardHom_surjective (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
    (contractingClass q n a ha)).choose

theorem contractingDivisor_class :
    cartierPicardHom (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj) = contractingClass q n a ha :=
  (cartierPicardHom_surjective (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
    (contractingClass q n a ha)).choose_spec

/-- The actual invertible sheaf of this Cartier divisor on the original surface. -/
def contractingLine : InvertibleSheaf (multiSurfaceSurface (q + 1) n a ha hproj).toScheme :=
  cartierDivisorInvertibleSheaf _ (contractingDivisor q n a ha hproj)

theorem contractingLine_class :
    Additive.ofMul (contractingLine q n a ha hproj).toPic = contractingClass q n a ha :=
  contractingDivisor_class q n a ha hproj

/-- The original sheaf M is nef; all curve tests have been proved. -/
theorem contractingLine_isNef (hn : 2 ≤ n) :
    Positivity.IsNef (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  apply (Positivity.isNef_iff_forall_primeCurve
    (multiSurfaceSurface (q + 1) n a ha hproj) _).mpr
  intro C
  have hC := contractingClass_degree_nonneg q n a ha hproj hn C
  rw [← contractingLine_class q n a ha hproj] at hC
  change 0 ≤ C.picardRestrictionDegree (contractingLine q n a ha hproj).toPic at hC
  simpa only [C.picardRestrictionDegree_toPic] using hC

/-- The actual Cartier self-intersection is the computed positive-square formula. -/
theorem contractingDivisor_square :
    intersectionPairing (multiSurfaceSurface (q + 1) n a ha hproj)
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
      (contractingDivisor q n a ha hproj) (contractingDivisor q n a ha hproj) =
        ((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) := by
  rw [← (multiSurfaceSurface (q + 1) n a ha hproj).picardPairing_class
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)]
  change multiPairing (q + 1) n a ha hproj
    (cartierPicardHom (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj))
    (cartierPicardHom (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj)) = _
  rw [contractingDivisor_class]
  exact contractingClass_square q n a ha hproj

end KltDP.Examples.FrobeniusMultiCentreContractingNef
