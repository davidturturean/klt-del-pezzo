import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# Actual occurrence of the arbitrary-atlas construction

For every affine base scheme and every global branch section, the single
whole-space chart supplies literal atlas data. In particular the atlas
hypotheses do not require a pre-existing cover scheme or splitting roots,
and the branch section is allowed to vanish.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas

open TransitionUnitGluing QuadraticCover

/-- An actual one-chart atlas for any global branch section on an affine scheme. -/
def globalSectionAtlas (X : Scheme.{u}) [IsAffine X] (a : Γ(X, ⊤)) :
    Data X PUnit.{u + 1} where
  opens := fun _ => ⊤
  affine := fun _ => isAffineOpen_top X
  pair_affine := fun _ _ => by simpa only [inf_idem] using isAffineOpen_top X
  triple_affine := fun _ _ _ => by simpa only [inf_idem] using isAffineOpen_top X
  covers := by simp only [iSup_const]
  units := fun _ _ => 1
  cocycle :=
    { unit_self := fun _ => rfl
      mul_res := by intro i j k; simp only [Units.val_one, map_one, one_mul] }
  sections := fun _ => a
  branch := by intro i j; simp only [Units.val_one, one_pow, one_mul]

/-- The sole local chart is the original actual affine quadratic scheme. -/
theorem globalSectionAtlas_chart (X : Scheme.{u}) [IsAffine X] (a : Γ(X, ⊤)) :
    (globalSectionAtlas X a).chart PUnit.unit = affineScheme a := by
  simp only [Data.chart, Data.frameChart, localChart, globalSectionAtlas, res_self]

/-- The generic construction gives an actual finite flat scheme morphism
for every such branch section, including the zero section. -/
theorem globalSectionAtlas_finite_flat (X : Scheme.{u}) [IsAffine X] (a : Γ(X, ⊤)) :
    IsFinite (globalSectionAtlas X a).morphism ∧
      AlgebraicGeometry.Flat (globalSectionAtlas X a).morphism :=
  ⟨(globalSectionAtlas X a).morphism_isFinite, (globalSectionAtlas X a).morphism_flat⟩

end KltDP.Geometry.QuadraticCoverAtlas
