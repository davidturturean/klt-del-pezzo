import KltDP.Geometry.QuadraticRamificationGluing

/-!
# Original quadratic subcharts and their original ramification pullbacks

The original atlas restriction map includes every affine coefficient
subchart into the same glued cover. Its range is the inverse image of
that actual base open. Pasting the already proved root-zero pullback
squares retains the original global ramification immersion on the same
subchart. No new atlas or base-change equivalence is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
variable {i : ι} {W : X.Opens} (hi : W ≤ D.opens i)

/-- The original quadratic restriction followed by the original glued chart inclusion. -/
def frameGlobalι : D.frameChart hi ⟶ D.scheme :=
  D.map (le_refl (D.opens i)) hi hi ≫ D.chartι i

theorem frameGlobalι_isOpenImmersion (hW : IsAffineOpen W) : IsOpenImmersion (D.frameGlobalι hi) := by
  letI := D.map_isOpenImmersion (le_refl (D.opens i)) hi hi (D.affine i) hW
  dsimp only [frameGlobalι]
  infer_instance

@[reassoc]
theorem frameGlobalι_morphism (hW : IsAffineOpen W) :
    D.frameGlobalι hi ≫ D.morphism = D.frameToBase hi hW := by
  rw [frameGlobalι, Category.assoc, D.chartι_morphism]
  exact D.map_toBase (le_refl (D.opens i)) hi hi (D.affine i) hW

/-- The same original affine subchart is exactly the inverse image of its base open. -/
theorem range_frameGlobalι (hW : IsAffineOpen W) :
    Set.range (D.frameGlobalι hi).base = D.morphism.base ⁻¹' (W : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    change (D.frameGlobalι hi ≫ D.morphism).base z ∈ W
    rw [D.frameGlobalι_morphism hi hW]
    exact D.frameToBase_mem hi hW z
  · intro y hy
    have hyi : y ∈ Set.range (D.chartι i).base := by
      rw [D.range_chartι i]
      exact hi hy
    obtain ⟨z, rfl⟩ := hyi
    have hzbase : (D.chartToBase i).base z ∈ W := by
      change (D.chartι i ≫ D.morphism).base z ∈ W at hy
      rwa [D.chartι_morphism i] at hy
    have hz : z ∈ Set.range (D.map (le_refl (D.opens i)) hi hi).base := by
      rw [D.range_map (le_refl (D.opens i)) hi hi (D.affine i) hW]
      exact hzbase
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, ?_⟩
    change (D.chartι i).base ((D.map (le_refl (D.opens i)) hi hi).base w) = _
    rw [hw]

/-- The original restricted root-zero chart includes into the same original global ramification. -/
def rootZeroFrameGlobalι : D.rootZeroFrame hi ⟶ D.rootZeroGlobalScheme :=
  D.rootZeroFrameMap (le_refl (D.opens i)) hi hi ≫ D.rootZeroGlobalChartι i

/-- The actual restricted root-zero immersion is the pullback of the original global one. -/
theorem rootZeroFrameGlobalIsPullback :
    IsPullback (rootZeroι (res X hi (D.sections i))) (D.rootZeroFrameGlobalι hi)
      (D.frameGlobalι hi) D.rootZeroGlobalι :=
  (D.rootZeroFrameMap_isPullback (le_refl (D.opens i)) hi hi).paste_vert
    (D.rootZeroGlobalChartIsPullback i).flip

@[reassoc]
theorem rootZeroFrameGlobalι_globalι :
    D.rootZeroFrameGlobalι hi ≫ D.rootZeroGlobalι =
      rootZeroι (res X hi (D.sections i)) ≫ D.frameGlobalι hi :=
  (D.rootZeroFrameGlobalIsPullback hi).w.symm

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.range_frameGlobalι
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.rootZeroFrameGlobalIsPullback
