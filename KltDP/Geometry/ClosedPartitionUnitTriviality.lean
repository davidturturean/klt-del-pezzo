import KltDP.Geometry.PicardClopenDecomposition
import KltDP.Geometry.RationalTreePicardRationalComponentFrame
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Triviality from a finite closed partition of a reduced scheme

The original closed immersions have disjoint ranges covering the original
reduced target. Finiteness makes each range open. The lift of each original
map to this open piece is a surjective closed immersion into a reduced
scheme, hence an isomorphism. The given pullback frames therefore give
frames on the clopen pieces, and the existing clopen gluing theorem returns
an actual frame of the original sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ClosedPartitionUnitTriviality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {ι : Type u} [Finite ι]
  (Y : ι → Scheme.{u}) (i : ∀ a, Y a ⟶ X)
  [hclosed : ∀ a, IsClosedImmersion (i a)]
  (hdisj : ∀ a b, a ≠ b →
    Disjoint (Set.range (i a).base) (Set.range (i b).base))
  (hcover : ∀ x : X, ∃ a, x ∈ Set.range (i a).base)

include hclosed hdisj hcover

/-- Every range in a finite closed partition is open. -/
theorem range_isOpen (a : ι) : IsOpen (Set.range (i a).base) := by
  classical
  have hc : (Set.range (i a).base)ᶜ =
      ⋃ b : {b : ι // b ≠ a}, Set.range (i b.1).base := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := hcover x
      have hba : b ≠ a := by
        intro h
        subst b
        exact hx hb
      exact Set.mem_iUnion.mpr ⟨⟨b, hba⟩, hb⟩
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      exact (hdisj b.1 a b.2).not_mem_of_mem_left hb
  apply isClosed_compl_iff.mp
  rw [hc]
  exact isClosed_iUnion_of_finite fun b => (i b.1).isClosedEmbedding.isClosed_range

/-- Actual unit frames on the original closed pieces glue to a unit frame
of a module sheaf on the original reduced scheme. -/
def moduleUnitIsoOfClosedPartition [IsReduced X] (M : X.Modules)
    (e : ∀ a, (schemeModulePullback (i a)).obj M ≅
      _root_.SheafOfModules.unit (Y a).ringCatSheaf) :
    M ≅ _root_.SheafOfModules.unit X.ringCatSheaf := by
  classical
  let U : ι → X.Opens := fun a =>
    ⟨Set.range (i a).base, range_isOpen Y i hdisj hcover a⟩
  have hUdisj : ∀ a b, a ≠ b → U a ⊓ U b = ⊥ := by
    intro a b hab
    apply Opens.ext
    exact Set.disjoint_iff_inter_eq_empty.mp (hdisj a b hab)
  have hUcover : (⨆ a, U a) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    obtain ⟨a, ha⟩ := hcover x
    exact Opens.mem_iSup.mpr ⟨a, ha⟩
  refine PicardClopenDecomposition.unitIsoOfClopenCover U hUdisj hUcover M
    (fun a => ?_)
  let l : Y a ⟶ (U a).toScheme :=
    IsOpenImmersion.lift (U a).ι (i a) (by
      rw [Scheme.Opens.range_ι]
      exact Set.Subset.refl _)
  have hl : l ≫ (U a).ι = i a := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (l ≫ (U a).ι) := by
    rw [hl]
    infer_instance
  letI : IsClosedImmersion l := IsClosedImmersion.of_comp l (U a).ι
  letI : IsReduced (U a).toScheme := isReduced_of_isOpenImmersion (U a).ι
  letI : Surjective l := by
    constructor
    intro z
    have hz : (U a).ι.base z ∈ Set.range (i a).base := by
      change (U a).ι.base z ∈ (U a : Set X)
      rw [← Scheme.Opens.range_ι]
      exact ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, (U a).ι.isOpenEmbedding.injective ?_⟩
    change (l ≫ (U a).ι).base y = (U a).ι.base z
    simpa only [hl] using hy
  letI : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  let t : (schemeModulePullback l).obj ((schemeModulePullback (U a).ι).obj M) ≅
      _root_.SheafOfModules.unit (Y a).ringCatSheaf :=
    (schemeModulePullbackCompIso l (U a).ι).app M ≪≫
      (eqToIso (congrArg schemeModulePullback hl)).app M ≪≫ e a
  exact RationalTreePicard.unitIsoOfPullbackUnitIso (asIso l).symm _ t

/-- An invertible sheaf is trivial if its actual pullbacks to the members
of a finite disjoint closed cover of a reduced scheme have unit frames. -/
def unitIsoOfClosedPartition [IsReduced X] (L : InvertibleSheaf X)
    (e : ∀ a, (schemeModulePullback (i a)).obj L.obj ≅
      _root_.SheafOfModules.unit (Y a).ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  moduleUnitIsoOfClosedPartition Y i hdisj hcover L.obj e

end KltDP.Geometry.ClosedPartitionUnitTriviality
