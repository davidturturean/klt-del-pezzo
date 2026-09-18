import KltDP.Geometry.QuadraticCoverAtlasEtale
import KltDP.Geometry.QuadraticRootZeroPoints

/-!
# A nonvanishing original root maps to the original branch complement

This isolates the chart calculation over an abstract actual quadratic
atlas, before substituting the Cartier section and its sheaf recovery.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open QuadraticCover TransitionUnitGluing

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The unchanged atlas map carries a point with nonvanishing root off its original branch. -/
theorem map_mem_offBranchOpen_of_root_not_mem (i : ι) (z : D.chart i)
    (hz : root (res X (le_refl (D.opens i)) (D.sections i)) ∉ z.asIdeal) :
    D.morphism.base ((D.chartι i).base z) ∈ D.offBranchOpen := by
  let s := res X (le_refl (D.opens i)) (D.sections i)
  have hbase := base_mem_basicOpen_of_root_not_mem s z hz
  have hs : s = D.sections i := res_self X (D.opens i) (D.sections i)
  have hb : (toBase s).base z ∈ PrimeSpectrum.basicOpen (D.sections i) :=
    (congrArg (fun t => (toBase s).base z ∈ PrimeSpectrum.basicOpen t) hs).mp hbase
  have hbasic : D.morphism.base ((D.chartι i).base z) ∈ X.basicOpen (D.sections i) := by
    change (D.chartι i ≫ D.morphism).base z ∈ X.basicOpen (D.sections i)
    rw [D.chartι_morphism]
    change (toBase s).base z ∈ (D.affine i).fromSpec ⁻¹ᵁ X.basicOpen (D.sections i)
    rw [(D.affine i).fromSpec_preimage_basicOpen]
    exact hb
  exact Opens.mem_iSup.mpr ⟨i, hbasic⟩

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.map_mem_offBranchOpen_of_root_not_mem
