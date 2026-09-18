import KltDP.Geometry.LinearSystemDegreeOnePullback
import KltDP.Geometry.PullbackTransitionUnitSections
import KltDP.Geometry.TransitionUnitGlobalSections

/-!
# Original homogeneous sections under the original linear-system comparison

The actual glued pullback coordinates restrict along the actual
subordination map. Original morphism evaluation identifies them with the
normalized coordinates of the supplied sections, and the existing recovery
isomorphism gives those same original sections. This proves normalization
for the specific, already constructed `pullbackDegreeOneIso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction LinearSystemMorphism
  InvertibleSectionNonvanishingOpen ProjectiveCoordinateSectionBasicOpen
  ProjectiveSpaceDegreeOneSheaf RationalTreePicard

private theorem trans_trans_symm_app_eq_of
    {X : Scheme.{u}} {A B C E : X.Modules}
    (e₁ : A ≅ B) (e₂ : B ≅ C) (e₃ : E ≅ C)
    (W : X.Opensᵒᵖ) (x : A.val.obj W) (y : E.val.obj W)
    (h : e₂.hom.val.app W (e₁.hom.val.app W x) = e₃.hom.val.app W y) :
    (e₁ ≪≫ e₂ ≪≫ e₃.symm).hom.val.app W x = y := by
  change e₃.inv.val.app W (e₂.hom.val.app W (e₁.hom.val.app W x)) = y
  rw [h]
  exact congrArg (fun q : E ⟶ E => q.val.app W y) e₃.hom_inv_id

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The actual refined pulled coordinate agrees with the original recovery
coordinate of the supplied section, on every original open. -/
theorem refined_pullback_homogeneous_coordinate
    (W : X.Opens) (j : Fin (n + 1)) (c : Chart L s) :
    res X (inf_le_inf_left W (chart_le_preimage_standardOpen L s f hcover c))
      (((pullbackGluedIso (morphism L s f hcover) (chart k n) (overlapUnit k n)
          (overlapUnit_isCocycle k n) (chart_cover k n)).hom.val.app (op W)
        ((InvertibleSheafSectionPowersPullback.pullbackSection (morphism L s f hcover)
          (degreeOne k n).obj (homogeneousSection k n j)).val (op W))).val
            (ULift.up c.index)) =
      ((normalizedRecoveryIso L s hcover).hom.val.app (op W)
        ((s j).val (op W))).val c := by
  have hp := pullbackGluedIso_hom_app_val_pullbackSection
    (morphism L s f hcover) (chart k n) (overlapUnit k n)
    (overlapUnit_isCocycle k n) (chart_cover k n)
    (homogeneousSection k n j) W (ULift.up c.index)
  refine (congrArg
    (res X (inf_le_inf_left W (chart_le_preimage_standardOpen L s f hcover c))) hp).trans ?_
  simp only [homogeneousSection, trivialization_globalSectionOfCoordinates, res_self]
  have hr := TransitionUnitExtraction.recoveryIso_hom_app_val
    X L.obj (normalizedAtlas L s hcover) (op W) ((s j).val (op W)) c
  have hs : L.obj.val.map
      (homOfLE (inf_le_left : W ⊓ c.affineOpen.1 ≤ W)).op
      ((s j).val (op W)) = (s j).val (op (W ⊓ c.affineOpen.1)) :=
    (s j).property (homOfLE (inf_le_left : W ⊓ c.affineOpen.1 ≤ W)).op
  have he := congrArg
    (fun z : L.obj.val.obj (op (W ⊓ c.affineOpen.1)) =>
      chartEquiv X L.obj (normalizedAtlas L s hcover) c inf_le_right z) hs
  have hn := normalizedAtlas_chartEquiv_section L s hcover c
    (W := W ⊓ c.affineOpen.1) inf_le_right j
  refine Eq.trans ?_ (hr.trans (he.trans hn)).symm
  calc
    _ = res X (inf_le_right : W ⊓ c.affineOpen.1 ≤ c.affineOpen.1)
        ((morphism L s f hcover).appLE (standardOpen k n c.index) c.affineOpen.1
          (chart_le_preimage_standardOpen L s f hcover c)
          (coordinateSection k n c.index j)) := by
      change res X _ (res X _ _) = res X _ (res X _ _)
      simp only [res_res]
      rfl
    _ = res X (inf_le_right : W ⊓ c.affineOpen.1 ≤ c.affineOpen.1)
        (coordinates L s c.frame c.inFrame c.index c.nonvanishing j) :=
      congrArg (res X (inf_le_right : W ⊓ c.affineOpen.1 ≤ c.affineOpen.1))
        (morphism_appLE_coordinateSection L s f hcover c
          (chart_le_preimage_standardOpen L s f hcover c) j)
    _ = _ := coordinates_restrict L s c.frame inf_le_right c.inFrame
      c.index c.nonvanishing j

/-- The specific original degree-one pullback isomorphism sends every
literal pulled homogeneous coordinate to the corresponding supplied section,
on every original open of the original scheme. -/
theorem pullbackDegreeOneIso_hom_app_homogeneousSection
    (j : Fin (n + 1)) (W : X.Opens) :
    (pullbackDegreeOneIso L s f hcover).hom.val.app (op W)
        ((InvertibleSheafSectionPowersPullback.pullbackSection (morphism L s f hcover)
          (degreeOne k n).obj (homogeneousSection k n j)).val (op W)) =
      (s j).val (op W) := by
  unfold pullbackDegreeOneIso
  apply trans_trans_symm_app_eq_of
  apply Subtype.ext
  funext c
  rw [subordinationIso_hom_app_val]
  exact refined_pullback_homogeneous_coordinate L s f hcover W j c

/-- Exact normalization on the original compatible global section families. -/
theorem pullbackDegreeOneIso_homogeneousSection (j : Fin (n + 1)) :
    _root_.SheafOfModules.sectionsMap (pullbackDegreeOneIso L s f hcover).hom
      (InvertibleSheafSectionPowersPullback.pullbackSection (morphism L s f hcover)
        (degreeOne k n).obj (homogeneousSection k n j)) = s j := by
  apply PresheafOfModules.sections_ext
  intro W
  exact pullbackDegreeOneIso_hom_app_homogeneousSection L s f hcover j W.unop

end KltDP.Geometry.LinearSystemPullback
