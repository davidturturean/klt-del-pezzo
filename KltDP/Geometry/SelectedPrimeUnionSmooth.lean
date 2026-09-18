import KltDP.Geometry.FiniteDisjointClosedSmoothCover
import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SelectedPrimeCurveCartierUnion

/-!
# Smoothness of the actual reduced selected union

Every selected original prime curve maps into the original vanishing-ideal
gluing by the proved closed-subscheme lifting construction. The original
inclusions give the map triangles, the images, and coverage. When the
selected curves are pairwise disjoint, this is a finite disjoint closed
cover of the reduced union. Actual smoothness of the selected curves
therefore proves smoothness of the original union over the same field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

/-- The original reduced ideal of the actual finite selected curve union. -/
abbrev selectedPrimeUnionIdeal (N : Finset S.PrimeCurve) : S.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)

/-- The selected union's original ideal vanishes on each selected original curve. -/
theorem selectedPrimeUnionIdeal_le_curveKer (N : Finset S.PrimeCurve)
    (C : {C : S.PrimeCurve // C ∈ N}) :
    S.selectedPrimeUnionIdeal N ≤ C.val.inclusion.ker := by
  change S.selectedPrimeUnionIdeal N ≤ C.val.vanishingIdeal.gluedTo.ker
  rw [Scheme.IdealSheafData.ker_gluedTo]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  show (C.val : Set S.toScheme) ⊆ ⋃ D ∈ N, (D : Set S.toScheme)
  intro x hx
  exact Set.mem_iUnion.mpr ⟨C.val, Set.mem_iUnion.mpr ⟨C.property, hx⟩⟩

/-- The actual curve inclusion lifted to the exact selected union scheme. -/
def selectedPrimeUnionCurveMap (N : Finset S.PrimeCurve)
    (C : {C : S.PrimeCurve // C ∈ N}) :
    C.val.toScheme ⟶ (S.selectedPrimeUnionIdeal N).glueData.glued :=
  GluedIdealSheafLift.liftGlued _ C.val.inclusion (S.selectedPrimeUnionIdeal_le_curveKer N C)

@[reassoc]
theorem selectedPrimeUnionCurveMap_comp (N : Finset S.PrimeCurve)
    (C : {C : S.PrimeCurve // C ∈ N}) :
    S.selectedPrimeUnionCurveMap N C ≫ (S.selectedPrimeUnionIdeal N).gluedTo = C.val.inclusion :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

instance selectedPrimeUnionCurveMap_isClosedImmersion (N : Finset S.PrimeCurve)
    (C : {C : S.PrimeCurve // C ∈ N}) : IsClosedImmersion (S.selectedPrimeUnionCurveMap N C) := by
  letI : IsClosedImmersion
      (S.selectedPrimeUnionCurveMap N C ≫ (S.selectedPrimeUnionIdeal N).gluedTo) := by
    rw [selectedPrimeUnionCurveMap_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (S.selectedPrimeUnionIdeal N).gluedTo

/-- Each actual lifted image is the inverse image of the original selected curve. -/
theorem range_selectedPrimeUnionCurveMap (N : Finset S.PrimeCurve)
    (C : {C : S.PrimeCurve // C ∈ N}) :
    Set.range (S.selectedPrimeUnionCurveMap N C).base =
      (S.selectedPrimeUnionIdeal N).gluedTo.base ⁻¹' (C.val : Set S.toScheme) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change (S.selectedPrimeUnionCurveMap N C ≫ (S.selectedPrimeUnionIdeal N).gluedTo).base y ∈ C.val
    rw [selectedPrimeUnionCurveMap_comp]
    exact C.val.range_inclusion.le ⟨y, rfl⟩
  · intro hz
    obtain ⟨y, hy⟩ := C.val.range_inclusion.ge hz
    refine ⟨y, (S.selectedPrimeUnionIdeal N).gluedTo_injective ?_⟩
    change (S.selectedPrimeUnionCurveMap N C ≫ (S.selectedPrimeUnionIdeal N).gluedTo).base y =
      (S.selectedPrimeUnionIdeal N).gluedTo.base z
    rwa [selectedPrimeUnionCurveMap_comp]

/-- The actual selected curves cover the original reduced union scheme. -/
theorem selectedPrimeUnionCurveMap_cover (N : Finset S.PrimeCurve)
    (z : (S.selectedPrimeUnionIdeal N).glueData.glued) :
    ∃ C : {C : S.PrimeCurve // C ∈ N}, z ∈ Set.range (S.selectedPrimeUnionCurveMap N C).base := by
  have hz : (S.selectedPrimeUnionIdeal N).gluedTo.base z ∈
      ⋃ C ∈ N, (C : Set S.toScheme) :=
    (S.selectedPrimeUnionIdeal N).range_gluedTo.le ⟨z, rfl⟩
  obtain ⟨C, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hC, hz⟩ := Set.mem_iUnion.mp hz
  refine ⟨⟨C, hC⟩, ?_⟩
  rw [range_selectedPrimeUnionCurveMap]
  exact hz

/-- Pairwise disjoint smooth selected curves give a smooth original reduced union. -/
theorem selectedPrimeUnion_isSmooth (N : Finset S.PrimeCurve)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D => Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hsm : ∀ C ∈ N, IsSmooth C.toSpec) :
    IsSmooth ((S.selectedPrimeUnionIdeal N).gluedTo ≫ S.structureMorphism) := by
  let J := S.selectedPrimeUnionIdeal N
  letI : IsReduced J.glueData.glued :=
    J.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := J)).symm
  apply isSmooth_of_finite_disjoint_closed_cover
    (fun C : {C : S.PrimeCurve // C ∈ N} => C.val.toScheme)
    (S.selectedPrimeUnionCurveMap N)
    (J.gluedTo ≫ S.structureMorphism) (S.selectedPrimeUnionCurveMap_cover N)
  · intro C D hCD
    rw [S.range_selectedPrimeUnionCurveMap N C, S.range_selectedPrimeUnionCurveMap N D]
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    exact Set.disjoint_left.mp
      (hdisj C.property D.property (fun h => hCD (Subtype.ext h))) hzC hzD
  · intro C
    rw [← Category.assoc, selectedPrimeUnionCurveMap_comp]
    exact hsm C.val C.property

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeUnion_isSmooth
