import KltDP.Geometry.InvertibleQuadraticAtlas
import KltDP.Geometry.QuadraticBranchLocalInputs

/-!
# Nonzero original sections give nonzero quadratic branch coefficients

On an integral base, a matching section for actual unit transitions is
determined by any one coordinate on a nonempty chart. Two nonempty chart
opens intersect; the original transition equation and injectivity of
structure-sheaf restrictions propagate a zero coordinate to every other
coordinate. Empty chart opens have the actual terminal section ring.

The actual tensor-coordinate isomorphism therefore sends a nonzero global
square-section to nonzero coefficients on every nonempty original affine
refinement chart. The same holds for the original section transported by
an actual square-root isomorphism. No local nonvanishing is assumed.

Combining this with the existing actual branch-point/reduced-quotient
adapter proves integrality of the original square-root cover from a
nonzero original global section and one actual reduced nonempty branch
chart on an integral normal base. Geometric identification of these
branch charts with a prescribed Cartier divisor, their reducedness from
the original smooth branch, and cover smoothness remain separate.

Reuse: pinned `map_injective_of_isIntegral`, nonempty intersection of
opens in an irreducible space, the terminal empty section ring, and actual
module-sheaf evaluation. Newer official Mathlib
a4d9f2fdd2f64b55969042eef459606961dc63a2 retains the restriction-injectivity
theorem (Apache-2.0); no source port or change to the existing atlas is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleQuadraticAtlas

open TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

local instance sourceSectionMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem matching_eq_zero_of_coordinate_zero {ι : Type u}
    (U : ι → X.Opens) (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
    (W : X.Opens) (q : sections X U g W) (i : ι)
    [Nonempty (W ⊓ U i : X.Opens)] (hi : q.val i = 0) : q = 0 := by
  apply Subtype.ext
  funext j
  change q.val j = 0
  by_cases hj : Nonempty (W ⊓ U j : X.Opens)
  · obtain ⟨xi⟩ := (inferInstance : Nonempty (W ⊓ U i : X.Opens))
    obtain ⟨xj⟩ := hj
    obtain ⟨x, hxi, hxj⟩ := nonempty_preirreducible_inter
      (W ⊓ U i).isOpen (W ⊓ U j).isOpen ⟨xi.val, xi.property⟩ ⟨xj.val, xj.property⟩
    letI : Nonempty (W ⊓ U i ⊓ U j : X.Opens) := ⟨⟨x, hxi, hxj.2⟩⟩
    have h := q.property i j
    rw [hi, map_zero] at h
    have hu : IsUnit (res X (inclCoc X U W i j) (g i j)) :=
      (g i j).isUnit.map (res X (inclCoc X U W i j))
    have hzero := hu.mul_right_eq_zero.mp h.symm
    apply map_injective_of_isIntegral X (homOfLE (inclSnd X U W i j))
    simpa only [res, map_zero] using hzero
  · have hbot : W ⊓ U j = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hj ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    haveI : Subsingleton Γ(X, W ⊓ U j) := by
      rw [hbot]
      exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    exact Subsingleton.elim _ _

/-- An original nonzero matching square-section has nonzero coefficient
on every nonempty affine refinement chart. -/
theorem refinedCoefficient_ne_zero {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
    (q : sections X U (productUnits X U g g) ⊤) (hq : q ≠ 0)
    (i : AffineOpenRefinement.Index X U)
    [Nonempty (AffineOpenRefinement.opens X U i)] :
    refinedCoefficient X U g q i ≠ 0 := by
  intro hi
  let j := AffineOpenRefinement.original X U i
  have hV : AffineOpenRefinement.opens X U i ≤ (⊤ : X.Opens) ⊓ U j :=
    le_inf le_top (AffineOpenRefinement.subordinate X U i)
  obtain ⟨x⟩ := (inferInstance : Nonempty (AffineOpenRefinement.opens X U i))
  letI : Nonempty (⊤ ⊓ U j : X.Opens) := ⟨⟨x.val, hV x.property⟩⟩
  have hj : q.val j = 0 := by
    apply map_injective_of_isIntegral X (homOfLE hV)
    simpa only [refinedCoefficient, res, map_zero] using hi
  exact hq (matching_eq_zero_of_coordinate_zero X U (productUnits X U g g) ⊤ q j hj)

/-- The actual coordinate isomorphism carries original global nonvanishing
to every nonempty chart of the unchanged square-section atlas. -/
theorem fromSquareSection_coefficient_ne_zero [X.IsSeparated]
    (L : InvertibleSheaf X) (b : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens)))
    (hb : b ≠ 0) (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    [Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i)] :
    (fromSquareSection X L b).sections i ≠ 0 := by
  let e := ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapIso
    (squareCoordinatesIso X L)).toLinearEquiv
  have hq : squareCoordinates X L b ≠ 0 := by
    intro hzero
    apply hb
    apply e.injective
    simpa only [map_zero] using hzero
  exact refinedCoefficient_ne_zero X L.localTrivializations.X
    (TransitionUnitExtraction.invertibleSheafUnits X L) (squareCoordinates X L b) hq i

/-- Transport by the actual square-root isomorphism preserves the original
global section's nonvanishing, hence the actual local branch coefficients. -/
theorem fromSquareRoot_coefficient_ne_zero [X.IsSeparated]
    (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (b : N.val.obj (op (⊤ : X.Opens))) (hb : b ≠ 0)
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    [Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i)] :
    (fromSquareRoot X L N e b).sections i ≠ 0 := by
  let eTop := ((_root_.SheafOfModules.evaluation X.ringCatSheaf
    (op (⊤ : X.Opens))).mapIso e).toLinearEquiv
  have hb' : e.inv.val.app (op ⊤) b ≠ 0 := by
    intro hzero
    apply hb
    apply eTop.symm.injective
    simpa only [map_zero] using hzero
  exact fromSquareSection_coefficient_ne_zero X L (e.inv.val.app (op ⊤) b) hb' i

/-- The original square-root cover is integral once an actual branch chart
is nonempty and reduced. Local coefficient nonvanishing is derived from
the original global section, and no other chart must be nonempty. -/
theorem fromSquareRoot_scheme_isIntegral_of_reduced_branch [X.IsSeparated]
    (hnormal : IsNormalScheme X) (L : InvertibleSheaf X) (N : X.Modules)
    (e : L.obj ⊗ L.obj ≅ N) (b : N.val.obj (op (⊤ : X.Opens))) (hb : b ≠ 0)
    (i : AffineOpenRefinement.Index X L.localTrivializations.X)
    (y : QuadraticCover.branchScheme ((fromSquareRoot X L N e b).sections i))
    (hred : IsReduced
      (QuadraticCover.branchScheme ((fromSquareRoot X L N e b).sections i))) :
    IsIntegral (fromSquareRoot X L N e b).scheme := by
  let D := fromSquareRoot X L N e b
  letI : Nonempty (AffineOpenRefinement.opens X L.localTrivializations.X i) :=
    ⟨⟨((QuadraticCover.branchι (D.sections i)) ≫ (D.affine i).fromSpec).base y,
      QuadraticCover.branch_point_mem_open (D.affine i) (D.sections i) y⟩⟩
  exact D.scheme_isIntegral_of_reduced_nonempty_branchChart hnormal i y
    (fromSquareRoot_coefficient_ne_zero X L N e b hb i) hred

end KltDP.Geometry.InvertibleQuadraticAtlas
