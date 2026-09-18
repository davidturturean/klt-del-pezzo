import KltDP.Geometry.LinearSystemCoordinateEvaluation
import KltDP.Geometry.PowerSectionFunctionExtension

/-!
# Coordinate ratios determined by original section equations

On any open where an original denominator section is nonvanishing, an
original section equation determines the pullback of the corresponding
projective coordinate. The proof restricts to original affine atlas charts
and uses separatedness of the structure sheaf. No frame on the whole open,
integrality, or affine hypothesis on that open is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open InvertibleSectionNonvanishingOpen TransitionUnitGluing TransitionUnitExtraction
  ProjectiveCoordinateSectionBasicOpen PowerSectionFunctionExtension

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

theorem morphism_preimage_standardOpen (m : Fin (n + 1)) :
    morphism L s f hcover ⁻¹ᵁ standardOpen k n m =
      nonvanishingOpen X L (s m) := by
  have hstd : (ProjectiveChart.coordinateChartMorphism k n m).opensRange =
      standardOpen k n m := ProjectiveChart.coordinateChartMorphism_opensRange k n m
  rw [← hstd, morphism_preimage_coordinateChart]

/-- The actual appLE, with its open-containment proof derived from the
original nonvanishing condition. -/
def appOnNonvanishing (m : Fin (n + 1)) {U : X.Opens}
    (hUm : U ≤ nonvanishingOpen X L (s m)) :
    Γ(projectiveSpace k n, standardOpen k n m) ⟶ Γ(X, U) :=
  (morphism L s f hcover).appLE (standardOpen k n m) U
    (by rw [morphism_preimage_standardOpen]; exact hUm)

/-- The literal original section relation determines the original
coordinate fraction on the entire open, independently of the chosen atlas. -/
theorem appOnNonvanishing_coordinateSection_of_eq
    (m j : Fin (n + 1)) {U : X.Opens}
    (hUm : U ≤ nonvanishingOpen X L (s m)) (b : Γ(X, U))
    (hb : sectionValue L.obj (s j) U = b • sectionValue L.obj (s m) U) :
    appOnNonvanishing L s f hcover m hUm (coordinateSection k n m j) = b := by
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.cond
  intro x hx
  have hxframe : x ∈ ⨆ a, L.localTrivializations.X a := by
    rw [TransitionUnitExtraction.chartOpens_cover X L.obj L.localTrivializations]
    trivial
  obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp hxframe
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open
      (show x ∈ U ⊓ L.localTrivializations.X a from ⟨hx, hxa⟩)
      (U ⊓ L.localTrivializations.X a).2
  let hVU' : V ≤ U := hVU.trans inf_le_left
  let hVa : V ≤ L.localTrivializations.X a := hVU.trans inf_le_right
  let hVm : V ≤ nonvanishingOpen X L (s m) := hVU'.trans hUm
  let c : Chart L s := ⟨⟨V, hV⟩, a, hVa, m, hVm⟩
  have hj : L.obj.val.map (homOfLE hVU').op (sectionValue L.obj (s j) U) =
      sectionValue L.obj (s j) V := (s j).property (homOfLE hVU').op
  have hm : L.obj.val.map (homOfLE hVU').op (sectionValue L.obj (s m) U) =
      sectionValue L.obj (s m) V := (s m).property (homOfLE hVU').op
  have hsec : sectionValue L.obj (s j) V =
      res X hVU' b • sectionValue L.obj (s m) V := by
    have h := congrArg (fun z : L.obj.val.obj (op U) =>
      L.obj.val.map (homOfLE hVU').op z) hb
    dsimp only at h
    rw [L.obj.val.map_smul, hj, hm] at h
    exact h
  have hcoef : coefficient L (s j) a hVa =
      res X hVU' b * coefficient L (s m) a hVa := by
    change chartEquiv X L.obj L.localTrivializations a hVa
      (sectionValue L.obj (s j) V) = _
    rw [hsec, map_smul, smul_eq_mul]
    rfl
  have hcoords : coordinates L s a hVa m hVm j = res X hVU' b := by
    apply (coefficient_isUnit L (s m) a hVa hVm).mul_left_cancel
    rw [denominator_mul_coordinates, hcoef, mul_comm]
  refine ⟨V, hVU', hxV, ?_⟩
  let hU : U ≤ morphism L s f hcover ⁻¹ᵁ standardOpen k n m := by
    rw [morphism_preimage_standardOpen]
    exact hUm
  calc
    _ = (morphism L s f hcover).appLE (standardOpen k n m) V
        (hVU'.trans hU) (coordinateSection k n m j) :=
      ConcreteCategory.congr_hom
        ((morphism L s f hcover).appLE_map hU (homOfLE hVU').op) _
    _ = coordinates L s a hVa m hVm j :=
      morphism_appLE_coordinateSection L s f hcover c (hVU'.trans hU) j
    _ = _ := hcoords

end KltDP.Geometry.LinearSystemMorphism
