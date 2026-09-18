import KltDP.Geometry.QuadraticOriginalRootEquationSquare
import KltDP.Geometry.CartierPullbackOriginalIdealGenerator
import KltDP.Geometry.QuadraticOriginalGenericPoint

/-!
# The original pulled branch ideal is the square of the original ramification kernel

The original branch ideal generators give the existing Cartier pullback
formula on each actual quadratic chart. The proved global-section square
identity and actual global-kernel equation identify that pullback ideal
with the square of the original root-zero kernel. Restriction of ideal
sheaves and the original atlas cover give the global equality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover

variable {X : Scheme.{u}} [IsIntegral X] {ι : Type u}
    (D : QuadraticCoverAtlas.Data X ι) [IsIntegral D.scheme]

local instance quadraticOriginalRamificationMultiplicityGeneric : GenericPointPreserving D.morphism :=
  D.morphism_genericPointPreserving
local instance quadraticOriginalRamificationMultiplicityClosed : IsClosedImmersion D.rootZeroGlobalι :=
  D.rootZeroGlobalι_isClosedImmersion

/-- The actual Cartier pullback ideal equals the square of the same original ramification kernel. -/
theorem pullbackIdealData_eq_rootZeroKernel_sq
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (hspan : ∀ i, (effectiveCartierIdealDataOfRegularEquations X E hE).ideal
      ⟨D.opens i, D.affine i⟩ = branchIdeal (D.sections i))
    (hbranch : ∀ i, (D.opens i : Set X).Nonempty →
      D.sections i ∈ nonZeroDivisors Γ(X, D.opens i)) :
    pullbackIdealData D.morphism E hE = idealSheafDataPow D.rootZeroGlobalι.ker 2 := by
  let I := pullbackIdealData D.morphism E hE
  let J := idealSheafDataPow D.rootZeroGlobalι.ker 2
  apply IdealSheafData.ext_of_affine_cover I J (fun i => (D.rootEquationOpen i).1)
  · intro x
    obtain ⟨i, z, rfl⟩ := D.glueData.ι_jointly_surjective x
    exact ⟨i, z, trivial, rfl⟩
  · intro i W hW
    apply IdealSheafData.ideal_eq_of_nonempty
    intro hWne
    let w : W.1 := Classical.choice hWne
    have hbase : (D.opens i : Set X).Nonempty :=
      ⟨D.morphism.base w.val, D.rootEquationOpen_le_preimage i (hW w.property)⟩
    letI : Nonempty (D.opens i) := ⟨⟨hbase.choose, hbase.choose_spec⟩⟩
    have hi : I.ideal (D.rootEquationOpen i) = J.ideal (D.rootEquationOpen i) := by
      dsimp only [I, J]
      rw [pullbackIdealData_ideal_of_generator D.morphism E hE
        ⟨D.opens i, D.affine i⟩ (D.sections i) (hspan i) (hbranch i hbase)
        (D.rootEquationOpen i) (D.rootEquationOpen_le_preimage i)]
      rw [D.rootEquationSection_square, idealSheafDataPow_ideal, D.rootZeroGlobal_kernel_ideal,
        Ideal.span_singleton_pow]
    rw [← Scheme.IdealSheafData.map_ideal I (U := W) (V := D.rootEquationOpen i) hW,
      ← Scheme.IdealSheafData.map_ideal J (U := W) (V := D.rootEquationOpen i) hW, hi]

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.pullbackIdealData_eq_rootZeroKernel_sq
