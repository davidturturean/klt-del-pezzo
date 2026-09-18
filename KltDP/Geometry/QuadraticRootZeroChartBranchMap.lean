import KltDP.Geometry.QuadraticRamificationGluing

/-!
# Transporting a branch-chart map to the actual root-zero chart

The quotient isomorphism and self-restriction equality are proved over
an abstract actual quadratic atlas before substituting a concrete
Cartier module, canonical section and recovery data.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing

variable {X Z : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- A base-compatible branch chart map gives the actual root-zero chart map with the same range. -/
theorem exists_rootZeroChart_map (i : ι)
    (g : branchScheme (D.sections i) ⟶ Z) (b : Z ⟶ X)
    (hg : g ≫ b = branchι (D.sections i) ≫ (D.affine i).fromSpec)
    (hr : Set.range g.base = b.base ⁻¹' (D.opens i : Set X)) :
    ∃ f : D.rootZeroChart i ⟶ Z,
      f ≫ b = D.rootZeroChartToBase i ∧
      Set.range f.base = b.base ⁻¹' (D.opens i : Set X) := by
  let P (s : Γ(X, D.opens i)) : Prop :=
    ∃ f : rootZeroScheme s ⟶ Z,
      f ≫ b = rootZeroι s ≫ toBase s ≫ (D.affine i).fromSpec ∧
      Set.range f.base = b.base ⁻¹' (D.opens i : Set X)
  have hP : P (D.sections i) := by
    refine ⟨(rootZeroIsoBranch (D.sections i)).hom ≫ g, ?_, ?_⟩
    · rw [Category.assoc, hg, ← Category.assoc,
        rootZeroIsoBranch_hom_toBase, Category.assoc]
    · rw [Scheme.comp_base, TopCat.coe_comp, (rootZeroIsoBranch (D.sections i)).hom.surjective.range_comp]
      exact hr
  exact (congrArg P (res_self X (D.opens i) (D.sections i))).mpr hP

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.exists_rootZeroChart_map
