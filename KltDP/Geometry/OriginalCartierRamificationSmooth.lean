import KltDP.Geometry.OriginalCartierQuadraticIntegral
import KltDP.Geometry.QuadraticRootRegular
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Original smooth branch data on the actual root-zero charts

The actual Cartier branch chart maps by an open immersion into the
original Cartier zero scheme. The original quotient triangle identifies
its map to the original base. Smoothness of that original branch therefore
proves smoothness of the literal quadratic branch quotient and, through
the proved root-zero isomorphism, of the original root-zero chart.

At every actual root-zero point, the original root is a non-zero-divisor,
derived from the nonzero canonical Cartier section and the integral base.
These are produced geometric inputs for the remaining ambient smoothness
argument. No regular local ring or normalized coordinates are assumed,
and ambient-cover smoothness is not claimed by this intermediate module.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

open QuadraticCover InvertibleQuadraticAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)

/-- The actual branch chart maps to the original Cartier zero scheme. -/
def branchChartMap (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    branchScheme ((effectiveCartierQuadraticAtlas X E hE L e).sections i) ⟶
      (effectiveCartierIdealData X E hE L e).glueData.glued :=
  (effectiveCartierBranchChartIso X E hE L e i).inv ≫
    (effectiveCartierIdealData X E hE L e).glueData.ι
      ⟨(effectiveCartierQuadraticAtlas X E hE L e).opens i,
        (effectiveCartierQuadraticAtlas X E hE L e).affine i⟩

instance branchChartMap_isOpenImmersion
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    IsOpenImmersion (branchChartMap X E hE L e i) := by
  dsimp only [branchChartMap]
  infer_instance

@[reassoc]
theorem branchChartMap_toBase (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    branchChartMap X E hE L e i ≫ (effectiveCartierIdealData X E hE L e).gluedTo =
      branchι ((effectiveCartierQuadraticAtlas X E hE L e).sections i) ≫
        ((effectiveCartierQuadraticAtlas X E hE L e).affine i).fromSpec := by
  rw [branchChartMap, Category.assoc, ← effectiveCartierBranchChartIso_hom_toBase,
    Iso.inv_hom_id_assoc]

variable {k : Type u} [Field k] (sX : X ⟶ Spec (CommRingCat.of k))

/-- Actual smoothness of the original Cartier branch descends to its literal branch charts. -/
theorem branchChart_isSmooth
    (hsm : IsSmooth ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo ≫ sX))
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    IsSmooth (branchι ((effectiveCartierQuadraticAtlas X E hE L e).sections i) ≫
      ((effectiveCartierQuadraticAtlas X E hE L e).affine i).fromSpec ≫ sX) := by
  letI : IsSmooth ((effectiveCartierIdealData X E hE L e).gluedTo ≫ sX) := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
    exact hsm
  have h := inferInstanceAs (IsSmooth (branchChartMap X E hE L e i ≫
    (effectiveCartierIdealData X E hE L e).gluedTo ≫ sX))
  rwa [← Category.assoc, branchChartMap_toBase, Category.assoc] at h

/-- The root-zero scheme of the original quadratic chart is smooth over the original field. -/
theorem rootZeroChart_isSmooth
    (hsm : IsSmooth ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo ≫ sX))
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    let A := effectiveCartierQuadraticAtlas X E hE L e
    IsSmooth (rootZeroι (A.sections i) ≫ toBase (A.sections i) ≫
      (A.affine i).fromSpec ≫ sX) := by
  dsimp only
  let A := effectiveCartierQuadraticAtlas X E hE L e
  letI : IsSmooth (branchι (A.sections i) ≫ (A.affine i).fromSpec ≫ sX) :=
    branchChart_isSmooth X E hE L e sX hsm i
  have h := inferInstanceAs (IsSmooth ((rootZeroIsoBranch (A.sections i)).hom ≫
    branchι (A.sections i) ≫ (A.affine i).fromSpec ≫ sX))
  simpa only [← Category.assoc, rootZeroIsoBranch_hom_toBase] using h

/-- The actual root equation is regular at every actual root-zero chart point. -/
theorem root_regular_of_rootZero_point
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    (y : rootZeroScheme ((effectiveCartierQuadraticAtlas X E hE L e).sections i)) :
    root ((effectiveCartierQuadraticAtlas X E hE L e).sections i) ∈
      nonZeroDivisors (CoverAlgebra ((effectiveCartierQuadraticAtlas X E hE L e).sections i)) := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  let z : branchScheme (A.sections i) := (rootZeroIsoBranch (A.sections i)).hom.base y
  letI : Nonempty (A.opens i) :=
    ⟨⟨((branchι (A.sections i)) ≫ (A.affine i).fromSpec).base z,
      branch_point_mem_open (A.affine i) (A.sections i) z⟩⟩
  change root (A.sections i) ∈ nonZeroDivisors (CoverAlgebra (A.sections i))
  letI : IsDomain Γ(X, A.opens i) := IsIntegral.component_integral (A.opens i)
  apply root_mem_nonZeroDivisors
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  letI : Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i) :=
    ⟨⟨((branchι (A.sections i)) ≫ (A.affine i).fromSpec).base z,
      branch_point_mem_open (A.affine i) (A.sections i) z⟩⟩
  exact fromSquareRoot_coefficient_ne_zero X L (cartierDivisorModule X E) e
    (effectiveCartierSection X E hE) (effectiveCartierSection_ne_zero X E hE) i

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroChart_isSmooth
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.root_regular_of_rootZero_point
