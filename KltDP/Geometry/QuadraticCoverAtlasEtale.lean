import KltDP.Geometry.QuadraticCoverEtale
import KltDP.Geometry.InvertibleQuadraticAtlas

/-!
# Étaleness of the constructed quadratic cover away from its branch section

The nonvanishing open is the union of the literal basic opens of the
original branch coefficients. Their equality on overlaps follows from
the derived unit-square transition equation. The actual restricted
quadratic charts cover the inverse image of this open in the previously
constructed scheme. On each chart, the original branch coefficient is a
unit by the basic-open restriction theorem, so the affine derivative
calculation proves étaleness. Source-locality then gives étaleness of the
actual restricted global morphism. No new gluing or covering conclusion
is supplied as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual nonvanishing open of the branch section, expressed in the original atlas. -/
def offBranchOpen : X.Opens := ⨆ i, X.basicOpen (D.sections i)

/-- Unit-square transition equations identify the nonvanishing opens on actual overlaps. -/
theorem basicOpen_overlap (i j : ι) :
    (D.opens i ⊓ D.opens j) ⊓ X.basicOpen (D.sections i) =
      (D.opens i ⊓ D.opens j) ⊓ X.basicOpen (D.sections j) := by
  have h := congrArg (fun a : Γ(X, D.opens i ⊓ D.opens j) => X.basicOpen a)
    (D.branch i j)
  have hu : IsUnit ((D.units i j : Γ(X, D.opens i ⊓ D.opens j)) ^ 2) :=
    (D.units i j).isUnit.pow 2
  simpa only [res, Scheme.basicOpen_res, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit X hu, inf_left_idem] using h

/-- On each original chart this global open is exactly the coefficient's basic open. -/
theorem opens_inf_offBranchOpen (i : ι) :
    D.opens i ⊓ D.offBranchOpen = X.basicOpen (D.sections i) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx.2
    have hmem : x ∈ (D.opens i ⊓ D.opens j) ⊓ X.basicOpen (D.sections j) :=
      ⟨⟨hx.1, X.basicOpen_le _ hj⟩, hj⟩
    rw [← D.basicOpen_overlap i j] at hmem
    exact hmem.2
  · intro x hx
    exact ⟨X.basicOpen_le _ hx, Opens.mem_iSup.mpr ⟨i, hx⟩⟩

/-- The original quadratic chart over any actual affine subopen maps to the glued scheme. -/
def affineFrameι {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) :
    D.frameChart hi ⟶ D.scheme :=
  D.map (le_refl (D.opens i)) hi hi ≫ D.chartι i

theorem affineFrameι_isOpenImmersion {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) : IsOpenImmersion (D.affineFrameι hi) := by
  letI := D.map_isOpenImmersion (le_refl (D.opens i)) hi hi (D.affine i) hW
  unfold affineFrameι
  infer_instance

@[reassoc]
theorem affineFrameι_morphism {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) :
    D.affineFrameι hi ≫ D.morphism = D.frameToBase hi hW := by
  rw [affineFrameι, Category.assoc, D.chartι_morphism]
  exact D.map_toBase (le_refl (D.opens i)) hi hi (D.affine i) hW

/-- The entire restricted chart has precisely the required original inverse-image range. -/
theorem range_affineFrameι {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hW : IsAffineOpen W) :
    Set.range (D.affineFrameι hi).base = D.morphism.base ⁻¹' (W : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    change (D.affineFrameι hi ≫ D.morphism).base z ∈ W
    rw [D.affineFrameι_morphism hi hW]
    exact D.frameToBase_mem hi hW z
  · intro y hy
    have hyi : y ∈ Set.range (D.chartι i).base := by
      rw [D.range_chartι i]
      exact hi hy
    obtain ⟨z, hz⟩ := hyi
    have hzW : z ∈ Set.range (D.map (le_refl (D.opens i)) hi hi).base := by
      rw [D.range_map _ _ _ (D.affine i) hW]
      change (D.chartToBase i).base z ∈ W
      rw [← D.chartι_morphism i]
      change D.morphism.base ((D.chartι i).base z) ∈ W
      rw [hz]
      exact hy
    obtain ⟨w, hw⟩ := hzW
    refine ⟨w, ?_⟩
    change (D.chartι i).base ((D.map (le_refl (D.opens i)) hi hi).base w) = y
    rw [hw, hz]

/-- The source chart on the actual basic open of a branch coefficient. -/
abbrev offBranchChart (i : ι) : Scheme.{u} :=
  D.frameChart (X.basicOpen_le (D.sections i))

def offBranchChartMap (i : ι) : D.offBranchChart i ⟶ D.scheme :=
  D.affineFrameι (X.basicOpen_le (D.sections i))

instance offBranchChartMap_isOpenImmersion (i : ι) :
    IsOpenImmersion (D.offBranchChartMap i) :=
  D.affineFrameι_isOpenImmersion _ ((D.affine i).basicOpen (D.sections i))

private theorem offBranchChartMap_range_subset (i : ι) :
    Set.range (D.offBranchChartMap i).base ⊆
      Set.range (D.morphism ⁻¹ᵁ D.offBranchOpen).ι.base := by
  rw [Scheme.Opens.range_ι]
  intro y hy
  have hy' : D.morphism.base y ∈ X.basicOpen (D.sections i) := by
    change y ∈ D.morphism.base ⁻¹' (X.basicOpen (D.sections i) : Set X)
    rw [← D.range_affineFrameι (X.basicOpen_le (D.sections i))
      ((D.affine i).basicOpen (D.sections i))]
    exact hy
  exact Opens.mem_iSup.mpr ⟨i, hy'⟩

/-- The actual branch-complement chart inclusion, factored through the original inverse-image open. -/
def offBranchChartι (i : ι) :
    D.offBranchChart i ⟶ (D.morphism ⁻¹ᵁ D.offBranchOpen).toScheme :=
  IsOpenImmersion.lift (D.morphism ⁻¹ᵁ D.offBranchOpen).ι
    (D.offBranchChartMap i) (D.offBranchChartMap_range_subset i)

@[reassoc]
theorem offBranchChartι_ι (i : ι) :
    D.offBranchChartι i ≫ (D.morphism ⁻¹ᵁ D.offBranchOpen).ι =
      D.offBranchChartMap i :=
  IsOpenImmersion.lift_fac _ _ _

instance offBranchChartι_isOpenImmersion (i : ι) :
    IsOpenImmersion (D.offBranchChartι i) := by
  haveI : IsOpenImmersion
      (D.offBranchChartι i ≫ (D.morphism ⁻¹ᵁ D.offBranchOpen).ι) := by
    rw [D.offBranchChartι_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (D.morphism ⁻¹ᵁ D.offBranchOpen).ι

/-- Restricted quadratic charts cover the actual preimage of the nonvanishing open. -/
def offBranchSourceCover : (D.morphism ⁻¹ᵁ D.offBranchOpen).toScheme.OpenCover :=
  Scheme.Cover.mkOfCovers ι D.offBranchChart D.offBranchChartι (by
    intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp y.property
    have hy : y.val ∈ Set.range (D.offBranchChartMap i).base := by
      rw [offBranchChartMap, D.range_affineFrameι _ ((D.affine i).basicOpen (D.sections i))]
      exact hi
    obtain ⟨z, hz⟩ := hy
    refine ⟨i, z, ?_⟩
    apply Subtype.ext
    change (D.offBranchChartι i ≫ (D.morphism ⁻¹ᵁ D.offBranchOpen).ι).base z = y.val
    rw [D.offBranchChartι_ι]
    exact hz)

/-- Cancel an actual open immersion after an étale morphism, using its literal pullback square. -/
private theorem isEtale_of_comp_openImmersion {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) [IsOpenImmersion g] (h : IsEtale (f ≫ g)) :
    IsEtale f := by
  have hP : IsPullback (𝟙 A) f (f ≫ g) g :=
    KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _ (by simp) (by
      ext x
      constructor
      · intro _
        exact ⟨f.base x, rfl⟩
      · intro _
        exact ⟨x, rfl⟩)
  exact IsLocalAtTarget.of_isPullback hP h

/-- The original global cover is étale on the literal nonvanishing open of its branch section. -/
theorem morphism_offBranch_isEtale (h2 : IsUnit (2 : Γ(X, ⊤))) :
    IsEtale (D.morphism ∣_ D.offBranchOpen) := by
  apply IsLocalAtSource.of_openCover (P := @IsEtale) D.offBranchSourceCover
  intro i
  change IsEtale (D.offBranchChartι i ≫ (D.morphism ∣_ D.offBranchOpen))
  apply isEtale_of_comp_openImmersion _ D.offBranchOpen.ι
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, D.offBranchChartι_ι]
  rw [offBranchChartMap, D.affineFrameι_morphism _ ((D.affine i).basicOpen (D.sections i))]
  have h2' : IsUnit (2 : Γ(X, X.basicOpen (D.sections i))) := by
    simpa only [map_ofNat] using h2.map
      (res X (le_top : X.basicOpen (D.sections i) ≤ ⊤))
  have hs : IsUnit (res X (X.basicOpen_le (D.sections i)) (D.sections i)) :=
    X.toRingedSpace.isUnit_res_basicOpen (D.sections i)
  letI := toBase_isEtale _ h2' hs
  change IsEtale (toBase (res X (X.basicOpen_le (D.sections i)) (D.sections i)) ≫
    ((D.affine i).basicOpen (D.sections i)).fromSpec)
  infer_instance

end KltDP.Geometry.QuadraticCoverAtlas.Data

namespace KltDP.Geometry.InvertibleQuadraticAtlas

open MonoidalCategory Opposite

variable (X : Scheme.{u})

local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The original line-bundle square-root construction is étale off its actual branch section. -/
theorem fromSquareRoot_offBranch_isEtale [X.IsSeparated]
    (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (b : N.val.obj (op (⊤ : X.Opens))) (h2 : IsUnit (2 : Γ(X, ⊤))) :
    IsEtale ((fromSquareRoot X L N e b).morphism ∣_
      (fromSquareRoot X L N e b).offBranchOpen) :=
  (fromSquareRoot X L N e b).morphism_offBranch_isEtale h2

end KltDP.Geometry.InvertibleQuadraticAtlas
