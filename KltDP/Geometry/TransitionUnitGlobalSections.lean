import KltDP.Geometry.TransitionUnitLocalTriviality
import KltDP.Geometry.GlobalGenerationOfLocalExtensions

/-!
# Actual global sections from original transition-compatible coordinates

Original chart functions satisfying the original unit-cocycle relation
give a global compatible section of the already constructed glued sheaf.
Its restriction and its coefficient in every original frame are the
specified functions. This is the section constructor needed by the
standard projective-coordinate affine-cover consumer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
  (r : ∀ i, Γ(X, U i))
  (hr : ∀ i j,
    res X (inf_le_left : U i ⊓ U j ≤ U i) (r i) =
      (g i j : Γ(X, U i ⊓ U j)) *
        res X (inf_le_right : U i ⊓ U j ≤ U j) (r j))

/-- The actual matching section over the whole original scheme. -/
def globalSectionTopOfCoordinates : sections X U g ⊤ :=
  ⟨fun i => res X (inf_le_right : ⊤ ⊓ U i ≤ U i) (r i), by
    intro i j
    have h := congrArg (res X (inclCoc X U ⊤ i j)) (hr i j)
    simpa only [map_mul, res_res] using h⟩

/-- The compatible global section of the same original glued sheaf. -/
def globalSectionOfCoordinates : (moduleSheaf X U g).sections :=
  GlobalGenerationOfLocalExtensions.sectionOfTop (moduleSheaf X U g)
    (globalSectionTopOfCoordinates X U g r hr)

/-- Restriction preserves the specified original chart coordinates. -/
theorem globalSectionOfCoordinates_val (W : X.Opens) (i : ι) :
    (show sections X U g W from
      (globalSectionOfCoordinates X U g r hr).val (op W)).val i =
      res X (inf_le_right : W ⊓ U i ≤ U i) (r i) := by
  change res X _ (res X _ (r i)) = _
  exact res_res X _ _ (r i)

/-- The actual original frame reads the specified coefficient on every
subopen of the chart. -/
theorem trivialization_globalSectionOfCoordinates (hc : IsCocycle X U g)
    (i : ι) {W : X.Opens} (hW : W ≤ U i) :
    trivialization X U g hc i hW
        ((globalSectionOfCoordinates X U g r hr).val (op W)) = res X hW (r i) := by
  rw [trivialization_apply, globalSectionOfCoordinates_val, res_res]

end KltDP.Geometry.TransitionUnitGluing
