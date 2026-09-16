import KltDP.Geometry.RationalTreePicardCoordinateComplement
import KltDP.Geometry.RationalTreePicardRestrictionPullbackSections
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Pullback of glued line bundles: reduction to the frame coordinate

BRIEF16, step 3 (partial). The remaining hypothesis `PullbackGluedClass` (the Picard class of the
pullback of a cocycle-glued line bundle is the class of the pulled-back cocycle) is reduced to a
single frame-coordinate identity, following the accepted `transitionUnits_eq_of_frames` of
`CartierFrames` (that module and `SchemeModulePullbackRestrict`, `PrimeCurveRestrictionPicardClass`
are not part of the 711 checkpoint the lane builds against, so the short statements used from them
are re-proved here under the names `pulledSection`, `pulledChartIso`, `transitionUnits_eq_of_frames'`,
`toPic_eq_picardClass'`, with the accepted proofs).

The pulled-back sheaf `f^*(moduleSheaf X U g)` carries the atlas `pulledAtlas` of pulled-back chart
trivializations (`pulledChartIso`, the accepted composition/equality/unit comparisons applied to
the chart trivializations `chartPullbackIso`), and the pulled-back chart frames `pulledFrame i`
(the pulled-back sections, through the unit of the pullback/pushforward adjunction, of the frames
`chartFrame i` of the glued sheaf, whose `i`-th coordinate is `1`) transform by the pulled-back
cocycle (`pulledFrame_transition`). Hence the transition units of the pulled-back atlas are the
pulled-back cocycle as soon as each pulled-back frame has coordinate `1` in its pulled-back chart
(`transitionUnits_pulledAtlas`), and `PullbackGluedClass` follows from that coordinate identity
(`pullbackGluedClass_of_coordinate`).

What is NOT proved here: the coordinate identity `PulledFrameCoordinate` itself (the analogue of
lane D's `hcore`): by the accepted `chartEquiv_ofOpenCharts` and
`openChartCoordinate_eq_openSectionsInv` it is the identity
`(pullbackTrivializationTranspose _ _ (pulledChartIso f (U i) _ (chartPullbackIso U g hc i))).val.app
(op (f ⁻¹ᵁ U i)) (pulledFrame U g hc f i) = 1`, to be proved by transporting the pulled-back section
through the comparison isomorphisms entering `pulledChartIso` and evaluating the chart transpose on
the frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open TransitionUnitGluing TransitionUnitExtraction SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section PulledSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

/-- Pullback of a section of `M` over `U` to a section of `f^*M` over `f⁻¹U`, through the unit
of the pullback/pushforward adjunction (the accepted `pullbackSection`). -/
def pulledSection (U : X.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullback f).obj M).val.obj (op (f ⁻¹ᵁ U)) :=
  ((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) s

theorem pulledSection_res {U V : X.Opens} (h : V ≤ U) (s : M.val.obj (op U)) :
    ((schemeModulePullback f).obj M).val.map ((Opens.map f.base).map (homOfLE h)).op
        (pulledSection f M U s) =
      pulledSection f M V (M.val.map (homOfLE h).op s) :=
  (PresheafOfModules.naturality_apply
    ((schemeModulePullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op s).symm

theorem pulledSection_smul (U : X.Opens) (a : Γ(X, U)) (s : M.val.obj (op U)) :
    pulledSection f M U (a • s) = f.app U a • pulledSection f M U s :=
  (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U)).hom.map_smul a s

/-- A trivialization of `M` on `U` pulls back to a trivialization of `f^*M` on `f⁻¹U` (the accepted
`schemeModulePullbackTrivialization`). -/
def pulledChartIso (U : X.Opens)
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (schemeModulePullback (f ⁻¹ᵁ U).ι).obj ((schemeModulePullback f).obj M) ≅
      _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).app M ≪≫
    eqToIso (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
      (morphismRestrict_ι f U).symm) ≪≫
    ((schemeModulePullbackCompIso (f ∣_ U) U.ι).app M).symm ≪≫
    (schemeModulePullback (f ∣_ U)).mapIso t ≪≫ schemeModulePullbackUnitIso (f ∣_ U)

end PulledSections

section FramesUniqueness

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- Transition units are determined by frames (the accepted `transitionUnits_eq_of_frames`):
sections `σ i` over the charts with chart coordinate `1`, transforming by `g` on overlaps, force
the extracted units to be `g`. -/
theorem transitionUnits_eq_of_frames' (σ : ∀ i : t.I, M.val.obj (op (t.X i)))
    (hσ : ∀ i, chartEquiv X M t i le_rfl (σ i) = 1)
    (g : ∀ i j : t.I, Γ(X, t.X i ⊓ t.X j)ˣ)
    (hg : ∀ i j : t.I, M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) =
      (g i j : Γ(X, t.X i ⊓ t.X j)) •
        M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
    (i j : t.I) : transitionUnits X M t i j = g i j := by
  have h := transitionUnits_mul_chart X M t i j (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
    (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
    (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
  have hresi : chartEquiv X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) =
      res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) (chartEquiv X M t i le_rfl (σ i)) :=
    chartEquiv_restrict X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) (le_rfl : t.X i ≤ t.X i) (σ i)
  have hi : chartEquiv X M t i (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) = 1 :=
    hresi.trans ((congrArg (fun x => res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i) x) (hσ i)).trans
      (map_one (res X (inf_le_left : t.X i ⊓ t.X j ≤ t.X i))))
  have hresj : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) =
      res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) (chartEquiv X M t j le_rfl (σ j)) :=
    chartEquiv_restrict X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) (le_rfl : t.X j ≤ t.X j) (σ j)
  have hj1 : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) = 1 :=
    hresj.trans ((congrArg (fun x => res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) x) (hσ j)).trans
      (map_one (res X (inf_le_right : t.X i ⊓ t.X j ≤ t.X j))))
  have hσi : M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i) =
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
        M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) :=
    calc M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)
        = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            ((g i j : Γ(X, t.X i ⊓ t.X j)) •
              M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) :=
          (inv_smul_smul (g i j)
            (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))).symm
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j) :=
          congrArg (fun x => (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) • x)
            (hg i j).symm
  have hj : chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
      (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i)) =
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) :=
    calc chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
          (M.val.map (homOfLE (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)).op (σ i))
        = chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
            ((((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
              M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) :=
          congrArg (fun x => chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j) x) hσi
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) •
            chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)
              (M.val.map (homOfLE (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).op (σ j)) :=
          (chartEquiv X M t j (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)).map_smul _ _
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) * 1 :=
          congrArg (fun x => (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) * x) hj1
      _ = (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) := mul_one _
  have hA : res X (le_inf (inf_le_left : t.X i ⊓ t.X j ≤ t.X i)
      (inf_le_right : t.X i ⊓ t.X j ≤ t.X j)) (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) =
      (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) :=
    res_self X _ _
  have h2 : (transitionUnits X M t i j : Γ(X, t.X i ⊓ t.X j)) *
      (((g i j)⁻¹ : Γ(X, t.X i ⊓ t.X j)ˣ) : Γ(X, t.X i ⊓ t.X j)) = 1 :=
    (congrArg₂ (· * ·) hA.symm hj.symm).trans (h.trans hi)
  exact Units.ext (Units.mul_inv_eq_one.mp h2)

/-- The Picard class of an invertible sheaf is the class of the cocycle extracted from any covering
atlas of unit trivializations (the accepted `InvertibleSheaf.toPic_eq_picardClass`). -/
theorem toPic_eq_picardClass' (L : InvertibleSheaf X)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (hU : (⨆ i, t.X i) = ⊤) :
    L.toPic = picardClass X t.X (transitionUnits X L.obj t)
      (transitionUnits_isCocycle X L.obj t) hU := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [picardClass_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨recoveryIso X L.obj t⟩

end FramesUniqueness

section GluedFrames

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)

/-- The chart frame of the glued sheaf: the section over `U i` with `i`-th coordinate `1`. -/
def chartFrame (i : ι) : sections X U g (U i) :=
  (trivialization X U g hc i le_rfl).symm 1

theorem chartFrame_val (i a : ι) :
    (chartFrame U g hc i).val a =
      res X (le_inf inf_le_right (inf_le_left.trans le_rfl) : U i ⊓ U a ≤ U a ⊓ U i) (g a i) := by
  rw [chartFrame, trivialization_symm_val, map_one, mul_one]

/-- The chart frames transform by the cocycle on overlaps. -/
theorem chartFrame_transition (i j : ι) :
    restrict X U g (inf_le_right : U i ⊓ U j ≤ U j) (chartFrame U g hc j) =
      (g i j : Γ(X, U i ⊓ U j)) •
        restrict X U g (inf_le_left : U i ⊓ U j ≤ U i) (chartFrame U g hc i) := by
  apply Subtype.ext
  funext a
  change res X _ ((chartFrame U g hc j).val a) =
    res X (inf_le_left : U i ⊓ U j ⊓ U a ≤ U i ⊓ U j) (g i j) * res X _ ((chartFrame U g hc i).val a)
  rw [chartFrame_val, chartFrame_val, res_res, res_res, mul_comm]
  exact (IsCocycle.mul_res_of_le X U g hc (i := a) (j := i) (l := j)
    (W := U i ⊓ U j ⊓ U a)
    (le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
      (inf_le_left.trans inf_le_right))).symm

variable {Y : Scheme.{u}} (f : Y ⟶ X)

theorem res_preimage_inf_le (i j : ι) (x : Γ(Y, f ⁻¹ᵁ (U i ⊓ U j))) :
    res Y (preimage_inf_le f U i j) x = x := by
  have h : (homOfLE (preimage_inf_le f U i j)).op = 𝟙 (op (f ⁻¹ᵁ (U i ⊓ U j))) :=
    Subsingleton.elim _ _
  change (Y.presheaf.map (homOfLE (preimage_inf_le f U i j)).op).hom x = x
  erw [h, Y.presheaf.map_id]
  rfl

/-- The pulled-back chart frames. -/
def pulledFrame (i : ι) :
    ((schemeModulePullback f).obj (moduleSheaf X U g)).val.obj (op (f ⁻¹ᵁ U i)) :=
  pulledSection f (moduleSheaf X U g) (U i) (chartFrame U g hc i)

/-- The pulled-back chart frames transform by the pulled-back cocycle. -/
theorem pulledFrame_transition (i j : ι) :
    ((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
        (homOfLE (inf_le_right : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ U j)).op (pulledFrame U g hc f j) =
      (pullbackUnits f U g i j : Γ(Y, f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j)) •
        ((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
          (homOfLE (inf_le_left : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ U i)).op
          (pulledFrame U g hc f i) := by
  have e₁ : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
      (homOfLE (inf_le_right : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ U j)).op (pulledFrame U g hc f j) =
      pulledSection f (moduleSheaf X U g) (U i ⊓ U j)
        ((moduleSheaf X U g).val.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op
          (chartFrame U g hc j)) :=
    pulledSection_res f (moduleSheaf X U g) (inf_le_right : U i ⊓ U j ≤ U j) (chartFrame U g hc j)
  have e₂ : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
      (homOfLE (inf_le_left : f ⁻¹ᵁ U i ⊓ f ⁻¹ᵁ U j ≤ f ⁻¹ᵁ U i)).op (pulledFrame U g hc f i) =
      pulledSection f (moduleSheaf X U g) (U i ⊓ U j)
        ((moduleSheaf X U g).val.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op
          (chartFrame U g hc i)) :=
    pulledSection_res f (moduleSheaf X U g) (inf_le_left : U i ⊓ U j ≤ U i) (chartFrame U g hc i)
  rw [e₁, e₂, pullbackUnits_val, res_preimage_inf_le, moduleSheaf_map_apply, moduleSheaf_map_apply,
    chartFrame_transition]
  exact pulledSection_smul f (moduleSheaf X U g) (U i ⊓ U j) _ _

/-- The atlas of pulled-back chart trivializations on the pulled-back glued sheaf. -/
def pulledAtlas (hU : (⨆ i, U i) = ⊤) :
    KltDP.SheafOfModules.LocalTrivializations (R := Y.ringCatSheaf)
      ((schemeModulePullback f).obj (moduleSheaf X U g)) :=
  localTrivializationsOfOpenCharts ((schemeModulePullback f).obj (moduleSheaf X U g))
    (fun i => f ⁻¹ᵁ U i)
    (fun y => by
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← pullbackUnits_cover f U hU] at hy
      exact Opens.mem_iSup.mp hy)
    (fun i => openChartOfPullback _ (f ⁻¹ᵁ U i)
      (pulledChartIso f (moduleSheaf X U g) (U i) (chartPullbackIso U g hc i)))

/-- If every pulled-back frame has coordinate `1` in its pulled-back chart, the transition units
of the pulled-back atlas are the pulled-back cocycle. -/
theorem transitionUnits_pulledAtlas (hU : (⨆ i, U i) = ⊤)
    (hcoord : ∀ i, chartEquiv Y _ (pulledAtlas U g hc f hU) i le_rfl (pulledFrame U g hc f i) = 1)
    (i j : ι) :
    transitionUnits Y _ (pulledAtlas U g hc f hU) i j = pullbackUnits f U g i j :=
  transitionUnits_eq_of_frames' Y _ (pulledAtlas U g hc f hU) (pulledFrame U g hc f) hcoord
    (pullbackUnits f U g) (pulledFrame_transition U g hc f) i j

end GluedFrames

/-- The (yet unproved) frame-coordinate identity: every pulled-back chart frame has coordinate `1`
in the pulled-back chart trivialization. -/
def PulledFrameCoordinate : Prop :=
  ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤) (i : ι),
    chartEquiv Y _ (pulledAtlas U g hc f hU) i le_rfl (pulledFrame U g hc f i) = 1

/-- The pullback compatibility of glued line bundles follows from the frame-coordinate
identity. -/
theorem pullbackGluedClass_of_coordinate (h : PulledFrameCoordinate.{u}) :
    PullbackGluedClass.{u} := by
  intro Y X f ι U g hg hU
  rw [toPic_eq_picardClass' Y (pullbackInvertibleSheaf f (invertibleSheaf X U g hg hU))
    (pulledAtlas U g hg f hU) (pullbackUnits_cover f U hU)]
  exact picardClass_congr _
    (funext fun i => funext fun j => transitionUnits_pulledAtlas U g hg f hU (h f U g hg hU) i j)
    _ _

end KltDP.Geometry.RationalTreePicard
