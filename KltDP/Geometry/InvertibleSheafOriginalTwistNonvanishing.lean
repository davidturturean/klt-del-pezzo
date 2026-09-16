import KltDP.Geometry.InvertibleSheafFiniteAffineExtension
import KltDP.Geometry.InvertibleSheafOpenTwistSections
import KltDP.Geometry.InvertibleSheafTwistOnNonvanishing

/-!
# Original twist maps on the intrinsic nonvanishing open

The actual multiplication-by-power map is bijective on sections of every
original subopen of the intrinsic nonvanishing open. Actual affine chart
frames supply the local inverses. Their compatibility and the original
sheaf condition construct the inverse on arbitrary opens.

No frame, quasicoherence, finite generation, or section-extension datum is
assumed. This permits local generators to be carried to original twists.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafOriginalTwistNonvanishing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance originalTwistNonvanishingMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSectionNonvanishingOpen InvertibleSheafFiniteAffineExtension
open InvertibleSheafOpenTwistSections SchemeModuleOpenPullbackSections

variable {X : Scheme.{u}}

private theorem image_preimage_of_le (U : X.Opens) {V : X.Opens} (hVU : V ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVU]

/-- On every original subopen of an actual affine chart inside D(s), the
original twist map is bijective on the original section carriers. -/
theorem rightTwistMap_app_bijective_on_chart (L : InvertibleSheaf X) (M : X.Modules)
    (s : L.obj.sections) (a : Chart L) (n : ℕ) {V : X.Opens}
    (hVa : V ≤ chartOpen L a) (hVD : V ≤ nonvanishingOpen X L s) :
    Function.Bijective ((rightTwistMap M L s n).val.app (op V)) := by
  let f := (chartOpen L a).ι
  let W := f ⁻¹ᵁ V
  have hW : W ≤ (chartOpen L a).toScheme.basicOpen
      (InvertibleSheafFiniteAffineExtension.chartCoefficient L s a) := by
    rw [chartBasicOpen_eq]
    exact fun x hx => hVD hx
  have hWi : f ''ᵁ W = V := image_preimage_of_le (chartOpen L a) hVa
  let eM := sectionsEquiv f M W V hWi
  let eT := twistSectionsEquiv f M L n W V hWi
  let gY := rightTwistMap (chartModule L M a) (chartLine L a) (chartSection L s a) n
  have hg : Function.Bijective (gY.val.app (op W)) :=
    InvertibleSheafTwistOnNonvanishing.rightTwistMap_app_bijective
      (chartModule L M a) (chartLine L a) (chartFrame L a) (chartSection L s a) n hW
  have hc (t : (chartModule L M a).val.obj (op W)) :
      eT (gY.val.app (op W) t) = (rightTwistMap M L s n).val.app (op V) (eM t) :=
    twistSectionsEquiv_rightTwistMap f M L s n W V hWi t
  constructor
  · intro t v htv
    apply eM.symm.injective
    apply hg.injective
    apply eT.injective
    simpa only [hc, AddEquiv.apply_symm_apply] using htv
  · intro t
    obtain ⟨v, hv⟩ := hg.surjective (eT.symm t)
    exact ⟨eM v, (hc v).symm.trans ((congrArg eT hv).trans (eT.apply_symm_apply t))⟩

private abbrev res (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U) :=
  M.val.map (homOfLE hVU).op

private theorem res_comp (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (t : M.val.obj (op U)) :
    res M hWV (res M hVU t) = res M (hWV.trans hVU) t := by
  change (M.val.presheaf.map (homOfLE hVU).op ≫
    M.val.presheaf.map (homOfLE hWV).op) t = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_naturality {M N : X.Modules} (g : M ⟶ N)
    {U V : X.Opens} (hVU : V ≤ U) (t : M.val.obj (op U)) :
    res N hVU (g.val.app (op U) t) = g.val.app (op V) (res M hVU t) :=
  (PresheafOfModules.naturality_apply g.val (homOfLE hVU).op t).symm

private theorem app_bijective_of_cover {M N : X.Modules} (g : M ⟶ N)
    {I : Type u} (U : X.Opens) (V : I → X.Opens) (hVU : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i)
    (hg : ∀ i, ∀ W : X.Opens, W ≤ V i → Function.Bijective (g.val.app (op W))) :
    Function.Bijective (g.val.app (op U)) := by
  constructor
  · intro t v htv
    apply TopCat.Sheaf.eq_of_locally_eq'
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      V U (fun i => homOfLE (hVU i)) hcover
    intro i
    apply (hg i (V i) le_rfl).injective
    change g.val.app (op (V i)) (res M (hVU i) t) =
      g.val.app (op (V i)) (res M (hVU i) v)
    rw [← res_naturality, ← res_naturality, htv]
  · intro t
    have hlocal (i : I) : ∃ v : M.val.obj (op (V i)),
        g.val.app (op (V i)) v = res N (hVU i) t :=
      (hg i (V i) le_rfl).surjective _
    choose v hv using hlocal
    have hcompat (i j : I) :
        res M (show V i ⊓ V j ≤ V i from inf_le_left) (v i) =
          res M (show V i ⊓ V j ≤ V j from inf_le_right) (v j) := by
      apply (hg i (V i ⊓ V j) inf_le_left).injective
      rw [← res_naturality, ← res_naturality, hv, hv, res_comp, res_comp]
    obtain ⟨w, hw, _⟩ := TopCat.Sheaf.existsUnique_gluing'
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      V U (fun i => homOfLE (hVU i)) hcover v (by
        intro i j
        exact hcompat i j)
    refine ⟨w, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq'
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N)
      V U (fun i => homOfLE (hVU i)) hcover
    intro i
    change res N (hVU i) (g.val.app (op U) w) = res N (hVU i) t
    rw [res_naturality]
    exact (congrArg (g.val.app (op (V i))) (hw i)).trans (hv i)

/-- On every original subopen of the intrinsic nonvanishing open, the
original power-section multiplication map is bijective on sections. -/
theorem rightTwistMap_app_bijective (L : InvertibleSheaf X) (M : X.Modules)
    (s : L.obj.sections) (n : ℕ) {U : X.Opens} (hUD : U ≤ nonvanishingOpen X L s) :
    Function.Bijective ((rightTwistMap M L s n).val.app (op U)) := by
  let V (a : Chart L) := U ⊓ chartOpen L a
  have hcover : U ≤ ⨆ a : Chart L, V a := by
    intro x hx
    have hxc : x ∈ ⨆ a : Chart L, chartOpen L a := by
      have hc : (⨆ a : Chart L, chartOpen L a) = ⊤ :=
        AffineOpenRefinement.covers X L.localTrivializations.X
          (TransitionUnitExtraction.chartOpens_cover X L.obj L.localTrivializations)
      rw [hc]
      trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxc
    exact Opens.mem_iSup.mpr ⟨a, hx, ha⟩
  apply app_bijective_of_cover (rightTwistMap M L s n) U V (fun _ => inf_le_left) hcover
  intro a W hW
  exact rightTwistMap_app_bijective_on_chart L M s a n
    (hW.trans inf_le_right) ((hW.trans inf_le_left).trans hUD)

end KltDP.Geometry.InvertibleSheafOriginalTwistNonvanishing
