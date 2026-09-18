import KltDP.Geometry.CartierQuadraticBranchCharts
import KltDP.Geometry.QuadraticCoverAtlasEtale
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# The original Cartier complement and the actual smooth cover off the branch

The original Cartier ideal on each original quadratic chart is the
principal ideal of its actual branch coefficient. Its support therefore
has complement exactly the existing atlas nonvanishing open. The proved
atlas étaleness applies to the literal complement of the original Cartier
zero scheme. Over an original smooth base this same inverse-image open
of the original cover is smooth over the original field.

No identification of branch supports or cover smoothness is an input.
Smoothness at points above the branch remains a separate obligation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierOffBranchSmooth

open QuadraticCover

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)

/-- The existing nonvanishing open is the complement of the same original Cartier support. -/
theorem offBranchOpen_eq_cartier_compl :
    (effectiveCartierQuadraticAtlas X E hE L e).offBranchOpen =
      (effectiveCartierIdealDataOfRegularEquations X E hE).support.compl := by
  rw [← effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
  let A := effectiveCartierQuadraticAtlas X E hE L e
  apply SetLike.ext
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, A.opens i by rw [A.covers]; trivial)
  have hs : x ∈ (effectiveCartierIdealData X E hE L e).support ↔
      x ∉ X.basicOpen (A.sections i) := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := effectiveCartierIdealData X E hE L e) (U := ⟨A.opens i, A.affine i⟩) hi]
    rw [effectiveCartierIdealData_eq_quadraticBranchIdeal X E hE L e i,
      branchIdeal, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    rfl
  change x ∈ A.offBranchOpen ↔ x ∉ (effectiveCartierIdealData X E hE L e).support
  rw [hs, not_not]
  constructor
  · intro hx
    have h : x ∈ A.opens i ⊓ A.offBranchOpen := ⟨hi, hx⟩
    rwa [A.opens_inf_offBranchOpen i] at h
  · intro hx
    exact Opens.mem_iSup.mpr ⟨i, hx⟩

variable {k : Type u} [Field k] (σ : X ⟶ Spec (CommRingCat.of k))

include σ

/-- The actual cover is étale over the literal original Cartier complement. -/
theorem isEtale_cartier_compl (h2 : IsUnit (2 : k)) :
    IsEtale ((effectiveCartierQuadraticAtlas X E hE L e).morphism ∣_
      (effectiveCartierIdealDataOfRegularEquations X E hE).support.compl) := by
  have h2' : IsUnit (2 : Γ(X, ⊤)) := by
    have h := h2.map (σ.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    simpa only [map_ofNat] using h
  have h := (effectiveCartierQuadraticAtlas X E hE L e).morphism_offBranch_isEtale h2'
  rwa [offBranchOpen_eq_cartier_compl X E hE L e] at h

/-- Above the actual original Cartier complement the same cover is smooth over the base field. -/
theorem isSmooth_above_cartier_compl [IsSmooth σ] (h2 : IsUnit (2 : k)) :
    let A := effectiveCartierQuadraticAtlas X E hE L e
    let V : X.Opens := (effectiveCartierIdealDataOfRegularEquations X E hE).support.compl
    IsSmooth ((A.morphism ⁻¹ᵁ V).ι ≫ A.morphism ≫ σ) := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  let V : X.Opens := (effectiveCartierIdealDataOfRegularEquations X E hE).support.compl
  letI : IsEtale (A.morphism ∣_ V) := isEtale_cartier_compl X E hE L e σ h2
  letI : IsSmooth (A.morphism ∣_ V) := IsSmoothOfRelativeDimension.isSmooth 0 _
  change IsSmooth ((A.morphism ⁻¹ᵁ V).ι ≫ A.morphism ≫ σ)
  rw [← morphismRestrict_ι_assoc]
  infer_instance

end KltDP.Geometry.OriginalCartierOffBranchSmooth

#print axioms KltDP.Geometry.OriginalCartierOffBranchSmooth.offBranchOpen_eq_cartier_compl
#print axioms KltDP.Geometry.OriginalCartierOffBranchSmooth.isSmooth_above_cartier_compl
