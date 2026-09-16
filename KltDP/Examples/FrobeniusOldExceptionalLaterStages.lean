import KltDP.Examples.FrobeniusOldExceptionalPicard
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusStrictTransformStepPuncture
import KltDP.Geometry.SchemeModuleMonicFactorOnCover
import KltDP.Geometry.SchemeKernelFrameSquare
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The older exceptional curve on the later stages

For `j + 2 ≤ N` the accepted `finalOldMap A N j h` embeds the strict transform
`C_j = previousStrictTransform (A.stage j)` into stage `N`, as the pullback of `C_j ⊆ stage (j+2)`
along the accepted projection `between A h` (`finalOldMap_isPullback`). Stage `N` is covered by the
preimage of the complement of the centre of stage `j+2` (over which `between A h` is an isomorphism,
by the accepted `toInitial_restrict_isIso` through `stageFinishIso`) and by the preimage of the
complement of `C_j` (over which both kernel modules are the structure sheaf). On the first open the
accepted step-puncture kernel chain identifies `(between A h)^* I(C_j)` with `I(finalOldMap)`, on the
second open both are framed by the unit, and the monic-factor gluing gives

  `(between A h)^* I(C_j) ≅ I(finalOldMap A N j h)`   (`oldInvarianceIso`)

compatibly with the ambient inclusions. Hence `I(finalOldMap A N j h)` is invertible, `C_j` has a
class `oldExceptionalStrictClass N j h` on stage `N`, and this class is the pullback of the
birth-stage class, so that, in the tower's total exceptional classes,

  `C_j = E_j^{(N)} − E_{j+1}^{(N)}`   for every `j + 2 ≤ N`   (`oldExceptionalStrictClasses_tower`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalLaterStages

open KltDP.Geometry
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
open FrobeniusStageComplement.PlaneChartedScheme FrobeniusStrictTransformStepPuncture
open FrobeniusStrictTransformPicardStep FrobeniusStrictTransformClassesTower
open FrobeniusOldExceptionalChartIdeals FrobeniusOldExceptionalPicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-! ### Generic kernel-module lemmas, as in the accepted step-puncture module -/

private theorem kernel_eqToIso_hom_ι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeKernelIdeal h)).hom ≫ schemeKernelIdealι g =
      schemeKernelIdealι f := by
  subst g
  exact Category.id_comp _

private theorem precompKernel_asIso_inv_ι {A B Y : Scheme.{u}}
    (s : A ⟶ B) [IsIso s] (b : B ⟶ Y) :
    (schemeKernelPrecompIso (asIso s) b).inv ≫ schemeKernelIdealι (s ≫ b) =
      schemeKernelIdealι b :=
  schemeKernelPrecompIso_inv_ι (asIso s) b

private theorem localKernelSquareIso_inclusion {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) [IsOpenImmersion p]
    (s : A ⟶ B) [IsIso s] (h : a ≫ p = s ≫ b) :
    ((schemeModulePullback p).mapIso
        ((schemeKernelPrecompIso (asIso s) b).symm ≪≫
          eqToIso (congrArg schemeKernelIdeal h.symm)) ≪≫
        schemeKernelPostcompOpenIso a p).hom ≫ schemeKernelIdealι a =
      (schemeModulePullback p).map (schemeKernelIdealι b) ≫
        (schemeModulePullbackUnitIso p).hom := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    schemeKernelPostcompOpenIso_hom_ι, ← Category.assoc, ← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernel_eqToIso_hom_ι h.symm, precompKernel_asIso_inv_ι]

private theorem localToGlobalKernelIso_inclusion {A B X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (p : V.toScheme ⟶ U.toScheme)
    (e : (schemeModulePullback p).obj (schemeKernelIdeal (f ∣_ U)) ≅
      schemeKernelIdeal (g ∣_ V))
    (he : e.hom ≫ schemeKernelIdealι (g ∣_ V) =
      (schemeModulePullback p).map (schemeKernelIdealι (f ∣_ U)) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((schemeModulePullback p).mapIso (localKernelToGlobalPullbackIso f U).symm ≪≫
        e ≪≫ localKernelToGlobalPullbackIso g V).hom ≫ pulledKernelInclusion g V.ι =
      (schemeModulePullback p).map (pulledKernelInclusion f U.ι) ≫
        (schemeModulePullbackUnitIso p).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, he]
  rw [← Category.assoc, ← Functor.map_comp,
    ← localKernelToGlobalPullbackIso_inclusion f U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem kernelPullbackCompIso_inclusion {A X Y Z : Scheme.{u}}
    (f : A ⟶ Y) (i : X ⟶ Y) (g : Z ⟶ X) :
    (schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f) ≫
        pulledKernelInclusion f (g ≫ i) =
      (schemeModulePullback g).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso g).hom := by
  simp only [pulledKernelInclusion, Category.assoc]
  rw [← Category.assoc ((schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f)),
    ← (schemeModulePullbackCompIso g i).hom.naturality (schemeKernelIdealι f),
    Category.assoc, schemeModulePullbackCompIso_unit]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

private theorem totalKernelTransport_inclusion {A B X Y U V : Scheme.{u}}
    (f : A ⟶ Y) (g : B ⟶ X) (i : V ⟶ Y) (j : U ⟶ X)
    (p : U ⟶ V) (q : U ⟶ Y) (h : q = p ≫ i)
    (e : (schemeModulePullback p).obj ((schemeModulePullback i).obj (schemeKernelIdeal f)) ≅
      (schemeModulePullback j).obj (schemeKernelIdeal g))
    (he : e.hom ≫ pulledKernelInclusion g j =
      (schemeModulePullback p).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((eqToIso (congrArg schemeModulePullback h)).app (schemeKernelIdeal f) ≪≫
        ((schemeModulePullbackCompIso p i).app (schemeKernelIdeal f)).symm ≪≫ e).hom ≫
      pulledKernelInclusion g j = pulledKernelInclusion f q := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [he, ← kernelPullbackCompIso_inclusion f i p, Iso.inv_hom_id_app_assoc]
  exact pulledKernelInclusion_congr f h

private theorem cancel_final_iso {C : Type*} [Category C]
    {M N Q R : C} (e : Q ≅ R) (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ Q)
    (h : a ≫ b ≫ e.hom = c ≫ e.hom) : a ≫ b = c := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc] using h

/-- Multiplication by the unit function is the identity of the structure module. -/
private theorem scalar_one (X : Scheme.{u}) :
    schemeScalarEnd (Y := X) (1 : Γ(X, ⊤)) =
      𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : Γ(X, V.unop) := s
  change s' * X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op 1 = s'
  rw [(X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom.map_one, mul_one]

/-- The kernel generator of a morphism from the empty scheme is an isomorphism (accepted proof). -/
private theorem emptyKernelGenerator_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty X] :
    IsIso (schemeKernelGenerator f 1 (Subsingleton.elim _ _)) := by
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis
    (B := fun U : Y.Opens => U) _
    (Opens.isBasis_iff_nbhd.mpr (fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩))
  intro U
  apply schemeKernelGenerator_app_bijective f 1 (Subsingleton.elim _ _) U
  · rw [map_one, Ideal.span_singleton_one]
    apply top_unique
    intro r _
    exact Subsingleton.elim _ _
  · rw [map_one]
    exact one_mem _

variable {k : Type u} [Field k]

/-! ### The embedding of `C_j` into stage `N` and the projection to the birth stage -/

/-- The accepted embedding of `C_j` into stage `N`, `j + 2 ≤ N`. -/
abbrev oldFinalMap (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    previousStrictTransform (previousStage (k := k) j) ⟶ projectiveContactStage (k := k) N :=
  finalOldMap (projectiveProductInitial (k := k)) N j h

/-- The accepted projection from stage `N` to the birth stage `j+2` of `C_j`. -/
abbrev oldBetween (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    projectiveContactStage (k := k) N ⟶ projectiveContactStage (k := k) (j + 1 + 1) :=
  between (projectiveProductInitial (k := k)) h

theorem oldFinalMap_between (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldFinalMap (k := k) N j h ≫ oldBetween N j h = oldExceptionalStrictι j :=
  finalOldMap_projection (projectiveProductInitial (k := k)) N j h

/-- The complement of the centre of the next blowup in the birth stage `j+2`. -/
abbrev oldCentreComplement (j : ℕ) : (projectiveContactStage (k := k) (j + 1 + 1)).Opens :=
  currentPuncture (k := k) (j + 1 + 1)

/-- The complement of `C_j` in its birth stage. -/
def oldStrictComplement (j : ℕ) : (projectiveContactStage (k := k) (j + 1 + 1)).Opens :=
  ⟨(Set.range (oldExceptionalStrictι (k := k) j).base)ᶜ,
    (oldExceptionalStrictι (k := k) j).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- `C_j` avoids the centre of the next blowup (accepted `nextCenter_not_on_previousStrict`). -/
theorem oldStrict_mem_centreComplement (j : ℕ)
    (z : previousStrictTransform (previousStage (k := k) j)) :
    (oldExceptionalStrictι (k := k) j).base z ∈ oldCentreComplement (k := k) j := by
  change (oldExceptionalStrictι (k := k) j).base z ≠
    ((projectiveProductInitial (k := k)).stage (j + 1 + 1)).chart.base (originPoint (k := k))
  intro heq
  exact nextCenter_not_on_previousStrict (previousStage (k := k) j) ⟨z, heq⟩

/-- The preimage in stage `N` of the centre complement: the locus where `between` is an iso. -/
abbrev oldIsoLocus (N j : ℕ) (h : j + 1 + 1 ≤ N) : (projectiveContactStage (k := k) N).Opens :=
  oldBetween N j h ⁻¹ᵁ oldCentreComplement j

/-- The preimage in stage `N` of the complement of `C_j`. -/
abbrev oldAwayLocus (N j : ℕ) (h : j + 1 + 1 ≤ N) : (projectiveContactStage (k := k) N).Opens :=
  oldBetween N j h ⁻¹ᵁ oldStrictComplement j

theorem oldLoci_cover (N j : ℕ) (h : j + 1 + 1 ≤ N) (x : projectiveContactStage (k := k) N) :
    x ∈ oldIsoLocus (k := k) N j h ∨ x ∈ oldAwayLocus (k := k) N j h := by
  by_cases hx : (oldBetween (k := k) N j h).base x ∈
      Set.range (oldExceptionalStrictι (k := k) j).base
  · left
    obtain ⟨z, hz⟩ := hx
    change (oldBetween (k := k) N j h).base x ∈ oldCentreComplement (k := k) j
    rw [← hz]
    exact oldStrict_mem_centreComplement j z
  · right
    exact hx

/-- `between` restricted to the centre complement is an isomorphism (accepted
`toInitial_restrict_isIso` transported through `stageFinishIso`). -/
theorem oldBetween_eq (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldBetween (k := k) N j h =
      (stageFinishIso (projectiveProductInitial (k := k)) (j + 1 + 1) N h).inv ≫
        ((projectiveProductInitial (k := k)).stage (j + 1 + 1)).toInitial (N - (j + 1 + 1)) := by
  rw [Iso.eq_inv_comp]
  exact stageFinishIso_hom_between (projectiveProductInitial (k := k)) (j + 1 + 1) N h

instance oldBetween_restrict_isIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IsIso (oldBetween (k := k) N j h ∣_ oldCentreComplement j) := by
  have h2 : IsIso (((projectiveProductInitial (k := k)).stage (j + 1 + 1)).toInitial (N - (j + 1 + 1))
      ∣_ oldCentreComplement (k := k) j) :=
    toInitial_restrict_isIso ((projectiveProductInitial (k := k)).stage (j + 1 + 1)) (N - (j + 1 + 1))
  have h1 : IsIso ((stageFinishIso (projectiveProductInitial (k := k)) (j + 1 + 1) N h).inv ∣_
      (((projectiveProductInitial (k := k)).stage (j + 1 + 1)).toInitial (N - (j + 1 + 1)) ⁻¹ᵁ
        oldCentreComplement (k := k) j)) :=
    inferInstance
  rw [oldBetween_eq, morphismRestrict_comp]
  exact IsIso.comp_isIso' h1 h2

/-! ### The iso locus -/

theorem oldFinalMap_mem_isoLocus (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (z : previousStrictTransform (previousStage (k := k) j)) :
    (oldFinalMap (k := k) N j h).base z ∈ oldIsoLocus (k := k) N j h := by
  change (oldFinalMap (k := k) N j h ≫ oldBetween N j h).base z ∈ oldCentreComplement (k := k) j
  rw [oldFinalMap_between]
  exact oldStrict_mem_centreComplement j z

theorem range_oldFinalLocus_subset (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Set.range (oldFinalMap (k := k) N j h ⁻¹ᵁ oldIsoLocus N j h).ι.base ⊆
      Set.range (oldExceptionalStrictι (k := k) j ⁻¹ᵁ oldCentreComplement j).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨z.1, oldStrict_mem_centreComplement j z.1⟩, rfl⟩

/-- `C_j` over the iso locus of stage `N` maps onto `C_j` over the centre complement. -/
def oldLocusMap (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldFinalMap (k := k) N j h ⁻¹ᵁ oldIsoLocus N j h).toScheme ⟶
      (oldExceptionalStrictι (k := k) j ⁻¹ᵁ oldCentreComplement j).toScheme :=
  IsOpenImmersion.lift _ _ (range_oldFinalLocus_subset N j h)

@[reassoc] theorem oldLocusMap_ι (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldLocusMap (k := k) N j h ≫ (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι =
      (oldFinalMap N j h ⁻¹ᵁ oldIsoLocus N j h).ι :=
  IsOpenImmersion.lift_fac _ _ _

instance oldLocusMap_isOpenImmersion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IsOpenImmersion (oldLocusMap (k := k) N j h) := by
  letI : IsOpenImmersion (oldLocusMap (k := k) N j h ≫
      (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι) := by
    rw [oldLocusMap_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι

theorem oldLocusMap_surjective (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Function.Surjective (oldLocusMap (k := k) N j h).base := by
  intro z
  refine ⟨⟨z.1, oldFinalMap_mem_isoLocus N j h z.1⟩,
    (oldExceptionalStrictι (k := k) j ⁻¹ᵁ oldCentreComplement j).ι.isOpenEmbedding.injective ?_⟩
  change (oldLocusMap (k := k) N j h ≫
    (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι).base ⟨z.1, _⟩ = z.1
  rw [oldLocusMap_ι]
  rfl

instance oldLocusMap_isIso (N j : ℕ) (h : j + 1 + 1 ≤ N) : IsIso (oldLocusMap (k := k) N j h) := by
  haveI : Epi (oldLocusMap (k := k) N j h).base :=
    (TopCat.epi_iff_surjective _).mpr (oldLocusMap_surjective N j h)
  exact IsOpenImmersion.to_iso _

theorem oldLocusMap_square (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldFinalMap (k := k) N j h ∣_ oldIsoLocus N j h) ≫
        (oldBetween N j h ∣_ oldCentreComplement j) =
      oldLocusMap N j h ≫ (oldExceptionalStrictι j ∣_ oldCentreComplement j) := by
  apply (cancel_mono (oldCentreComplement (k := k) j).ι).mp
  have hp : (oldBetween (k := k) N j h ∣_ oldCentreComplement j) ≫
        (oldCentreComplement (k := k) j).ι =
      (oldIsoLocus (k := k) N j h).ι ≫ oldBetween N j h :=
    morphismRestrict_ι _ _
  have ha : (oldFinalMap (k := k) N j h ∣_ oldIsoLocus N j h) ≫ (oldIsoLocus (k := k) N j h).ι =
      (oldFinalMap N j h ⁻¹ᵁ oldIsoLocus N j h).ι ≫ oldFinalMap N j h :=
    morphismRestrict_ι _ _
  have hb : (oldExceptionalStrictι (k := k) j ∣_ oldCentreComplement j) ≫
        (oldCentreComplement (k := k) j).ι =
      (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι ≫ oldExceptionalStrictι j :=
    morphismRestrict_ι _ _
  calc ((oldFinalMap (k := k) N j h ∣_ oldIsoLocus N j h) ≫
        (oldBetween N j h ∣_ oldCentreComplement j)) ≫ (oldCentreComplement (k := k) j).ι
      = (oldFinalMap N j h ∣_ oldIsoLocus N j h) ≫ (oldIsoLocus N j h).ι ≫ oldBetween N j h := by
        rw [Category.assoc, hp]
    _ = (oldFinalMap N j h ⁻¹ᵁ oldIsoLocus N j h).ι ≫ oldFinalMap N j h ≫ oldBetween N j h := by
        rw [← Category.assoc, ha, Category.assoc]
    _ = (oldFinalMap N j h ⁻¹ᵁ oldIsoLocus N j h).ι ≫ oldExceptionalStrictι j := by
        rw [oldFinalMap_between]
    _ = oldLocusMap N j h ≫ (oldExceptionalStrictι j ⁻¹ᵁ oldCentreComplement j).ι ≫
          oldExceptionalStrictι j := by
        rw [oldLocusMap_ι_assoc]
    _ = (oldLocusMap N j h ≫ (oldExceptionalStrictι j ∣_ oldCentreComplement j)) ≫
          (oldCentreComplement (k := k) j).ι := by
        rw [Category.assoc, hb]

/-- The local kernels over the iso locus, compared through the restricted projection. -/
def oldLocalLocusKernelIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback (oldBetween (k := k) N j h ∣_ oldCentreComplement j)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j ∣_ oldCentreComplement j)) ≅
      schemeKernelIdeal (oldFinalMap N j h ∣_ oldIsoLocus N j h) :=
  (schemeModulePullback (oldBetween (k := k) N j h ∣_ oldCentreComplement j)).mapIso
    ((schemeKernelPrecompIso (asIso (oldLocusMap N j h))
        (oldExceptionalStrictι j ∣_ oldCentreComplement j)).symm ≪≫
      eqToIso (congrArg schemeKernelIdeal (oldLocusMap_square N j h).symm)) ≪≫
    schemeKernelPostcompOpenIso (oldFinalMap N j h ∣_ oldIsoLocus N j h)
      (oldBetween N j h ∣_ oldCentreComplement j)

theorem oldLocalLocusKernelIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldLocalLocusKernelIso (k := k) N j h).hom ≫
        schemeKernelIdealι (oldFinalMap N j h ∣_ oldIsoLocus N j h) =
      (schemeModulePullback (oldBetween N j h ∣_ oldCentreComplement j)).map
          (schemeKernelIdealι (oldExceptionalStrictι j ∣_ oldCentreComplement j)) ≫
        (schemeModulePullbackUnitIso (oldBetween N j h ∣_ oldCentreComplement j)).hom := by
  have h' := localKernelSquareIso_inclusion (oldFinalMap (k := k) N j h ∣_ oldIsoLocus N j h)
    (oldExceptionalStrictι j ∣_ oldCentreComplement j)
    (oldBetween N j h ∣_ oldCentreComplement j) (oldLocusMap N j h) (oldLocusMap_square N j h)
  convert h' using 3

/-- Both kernels are the pullbacks of the whole-stage kernels of `C_j` and of its image. -/
def oldLocusKernelIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback (oldBetween (k := k) N j h ∣_ oldCentreComplement j)).obj
        ((schemeModulePullback (oldCentreComplement (k := k) j).ι).obj
          (schemeKernelIdeal (oldExceptionalStrictι j))) ≅
      (schemeModulePullback (oldIsoLocus (k := k) N j h).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) :=
  (schemeModulePullback (oldBetween (k := k) N j h ∣_ oldCentreComplement j)).mapIso
      (localKernelToGlobalPullbackIso (oldExceptionalStrictι j) (oldCentreComplement j)).symm ≪≫
    oldLocalLocusKernelIso N j h ≪≫
      localKernelToGlobalPullbackIso (oldFinalMap N j h) (oldIsoLocus N j h)

theorem oldLocusKernelIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldLocusKernelIso (k := k) N j h).hom ≫
        pulledKernelInclusion (oldFinalMap N j h) (oldIsoLocus N j h).ι =
      (schemeModulePullback (oldBetween N j h ∣_ oldCentreComplement j)).map
          (pulledKernelInclusion (oldExceptionalStrictι j) (oldCentreComplement j).ι) ≫
        (schemeModulePullbackUnitIso (oldBetween N j h ∣_ oldCentreComplement j)).hom := by
  have h' := localToGlobalKernelIso_inclusion (oldExceptionalStrictι (k := k) j)
    (oldFinalMap N j h) (oldCentreComplement j) (oldIsoLocus N j h)
    (oldBetween N j h ∣_ oldCentreComplement j)
    (oldLocalLocusKernelIso N j h) (oldLocalLocusKernelIso_inclusion N j h)
  convert h' using 3

/-- Reassociate the pullback of `I(C_j)` through the restricted-projection square. -/
def oldTotalLocusKernelIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback ((oldIsoLocus (k := k) N j h).ι ≫ oldBetween N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) ≅
      (schemeModulePullback (oldIsoLocus (k := k) N j h).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) :=
  (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι (oldBetween (k := k) N j h) (oldCentreComplement j)).symm)).app _ ≪≫
    ((schemeModulePullbackCompIso (oldBetween N j h ∣_ oldCentreComplement j)
      (oldCentreComplement j).ι).app _).symm ≪≫
    oldLocusKernelIso N j h

theorem oldTotalLocusKernelIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldTotalLocusKernelIso (k := k) N j h).hom ≫
        pulledKernelInclusion (oldFinalMap N j h) (oldIsoLocus N j h).ι =
      pulledKernelInclusion (oldExceptionalStrictι j)
        ((oldIsoLocus N j h).ι ≫ oldBetween N j h) := by
  have h' := totalKernelTransport_inclusion (oldExceptionalStrictι (k := k) j)
    (oldFinalMap N j h) (oldCentreComplement j).ι (oldIsoLocus N j h).ι
    (oldBetween N j h ∣_ oldCentreComplement j) ((oldIsoLocus N j h).ι ≫ oldBetween N j h)
    (morphismRestrict_ι (oldBetween N j h) (oldCentreComplement j)).symm
    (oldLocusKernelIso N j h) (oldLocusKernelIso_inclusion N j h)
  convert h' using 3

/-- On the iso locus, the pullback of `I(C_j)` is the kernel module of the image of `C_j`. -/
def oldLocusIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback (oldIsoLocus (k := k) N j h).ι).obj
      ((schemeModulePullback (oldBetween N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j))) ≅
      (schemeModulePullback (oldIsoLocus (k := k) N j h).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) :=
  (schemeModulePullbackCompIso (oldIsoLocus (k := k) N j h).ι (oldBetween N j h)).app _ ≪≫
    oldTotalLocusKernelIso N j h

theorem oldLocusIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldLocusIso (k := k) N j h).hom ≫
        pulledKernelInclusion (oldFinalMap N j h) (oldIsoLocus N j h).ι =
      (schemeModulePullback (oldIsoLocus N j h).ι).map
        (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h)) ≫
        (schemeModulePullbackUnitIso (oldIsoLocus N j h).ι).hom := by
  rw [oldLocusIso, Iso.trans_hom, Category.assoc, oldTotalLocusKernelIso_inclusion, Iso.app_hom]
  exact kernelPullbackCompIso_inclusion (oldExceptionalStrictι (k := k) j) (oldBetween N j h)
    (oldIsoLocus N j h).ι

/-! ### The complement of `C_j` -/

instance oldFinalMap_awayLocus_isEmpty (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IsEmpty ((oldFinalMap (k := k) N j h ⁻¹ᵁ oldAwayLocus N j h).toScheme) := by
  refine ⟨fun z => ?_⟩
  have hz : (oldFinalMap (k := k) N j h ≫ oldBetween N j h).base z.1 ∉
      Set.range (oldExceptionalStrictι (k := k) j).base := z.2
  rw [oldFinalMap_between] at hz
  exact hz ⟨z.1, rfl⟩

instance oldStrict_awayComplement_isEmpty (j : ℕ) :
    IsEmpty ((oldExceptionalStrictι (k := k) j ⁻¹ᵁ oldStrictComplement j).toScheme) :=
  ⟨fun z => (z.2 : (oldExceptionalStrictι (k := k) j).base z.1 ∉
    Set.range (oldExceptionalStrictι (k := k) j).base) ⟨z.1, rfl⟩⟩

/-- The unit frame of `I(finalOldMap)` on the complement of the image of `C_j`. -/
def oldFinalAwayFrame (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    _root_.SheafOfModules.unit (oldAwayLocus (k := k) N j h).toScheme.ringCatSheaf ≅
      (schemeModulePullback (oldAwayLocus (k := k) N j h).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) := by
  letI := emptyKernelGenerator_isIso (oldFinalMap (k := k) N j h ∣_ oldAwayLocus N j h)
  exact asIso (schemeKernelGenerator (oldFinalMap N j h ∣_ oldAwayLocus N j h) 1
      (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (oldFinalMap N j h) (oldAwayLocus N j h)

theorem oldFinalAwayFrame_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldFinalAwayFrame (k := k) N j h).hom ≫
        pulledKernelInclusion (oldFinalMap N j h) (oldAwayLocus N j h).ι =
      𝟙 (_root_.SheafOfModules.unit (oldAwayLocus (k := k) N j h).toScheme.ringCatSheaf) := by
  have h' := localKernelGlobalEquation_inclusion (oldFinalMap (k := k) N j h) (oldAwayLocus N j h) 1
    (Subsingleton.elim _ _)
  rw [scalar_one] at h'
  convert h' using 3

/-- The unit frame of `I(C_j)` on the complement of `C_j`. -/
def oldStrictAwayFrame (j : ℕ) :
    _root_.SheafOfModules.unit (oldStrictComplement (k := k) j).toScheme.ringCatSheaf ≅
      (schemeModulePullback (oldStrictComplement (k := k) j).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) := by
  letI := emptyKernelGenerator_isIso (oldExceptionalStrictι (k := k) j ∣_ oldStrictComplement j)
  exact asIso (schemeKernelGenerator (oldExceptionalStrictι j ∣_ oldStrictComplement j) 1
      (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (oldExceptionalStrictι j) (oldStrictComplement j)

theorem oldStrictAwayFrame_inclusion (j : ℕ) :
    (oldStrictAwayFrame (k := k) j).hom ≫
        pulledKernelInclusion (oldExceptionalStrictι j) (oldStrictComplement j).ι =
      schemeScalarEnd (Y := (oldStrictComplement (k := k) j).toScheme) 1 := by
  have h' := localKernelGlobalEquation_inclusion (oldExceptionalStrictι (k := k) j)
    (oldStrictComplement j) 1 (Subsingleton.elim _ _)
  convert h' using 3

/-- The unit frame of `I(C_j)` transported to the pulled kernel on the complement of the image. -/
def oldPulledAwayFrame (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    _root_.SheafOfModules.unit (oldAwayLocus (k := k) N j h).toScheme.ringCatSheaf ≅
      (schemeModulePullback (oldAwayLocus (k := k) N j h).ι).obj
        ((schemeModulePullback (oldBetween N j h)).obj
          (schemeKernelIdeal (oldExceptionalStrictι j))) :=
  schemeKernelFrameOnSquare (oldExceptionalStrictι j) (oldStrictComplement j).ι
    (oldBetween N j h ∣_ oldStrictComplement j) (oldAwayLocus N j h).ι (oldBetween N j h)
    (morphismRestrict_ι (oldBetween N j h) (oldStrictComplement j)) (oldStrictAwayFrame j)

theorem oldPulledAwayFrame_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldPulledAwayFrame (k := k) N j h).hom ≫
        (schemeModulePullback (oldAwayLocus N j h).ι).map
          (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h)) ≫
        (schemeModulePullbackUnitIso (oldAwayLocus N j h).ι).hom =
      𝟙 (_root_.SheafOfModules.unit (oldAwayLocus (k := k) N j h).toScheme.ringCatSheaf) := by
  have h' := schemeKernelFrameOnSquare_inclusion (oldExceptionalStrictι (k := k) j)
    (oldStrictComplement j).ι (oldBetween N j h ∣_ oldStrictComplement j) (oldAwayLocus N j h).ι
    (oldBetween N j h) (morphismRestrict_ι (oldBetween N j h) (oldStrictComplement j))
    (oldStrictAwayFrame j) 1 (oldStrictAwayFrame_inclusion j)
  rw [map_one, scalar_one] at h'
  convert h' using 3

/-- On the complement of the image of `C_j`, both kernel modules are the structure sheaf. -/
def oldAwayIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback (oldAwayLocus (k := k) N j h).ι).obj
      ((schemeModulePullback (oldBetween N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j))) ≅
      (schemeModulePullback (oldAwayLocus (k := k) N j h).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) :=
  (oldPulledAwayFrame N j h).symm ≪≫ oldFinalAwayFrame N j h

theorem oldAwayIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldAwayIso (k := k) N j h).hom ≫
        pulledKernelInclusion (oldFinalMap N j h) (oldAwayLocus N j h).ι =
      (schemeModulePullback (oldAwayLocus N j h).ι).map
        (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h)) ≫
        (schemeModulePullbackUnitIso (oldAwayLocus N j h).ι).hom := by
  have h1 := oldPulledAwayFrame_inclusion (k := k) N j h
  have h2 := oldFinalAwayFrame_inclusion (k := k) N j h
  unfold oldAwayIso
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, h2, Category.comp_id]
  exact ((Iso.hom_comp_eq_id _).mp h1).symm

/-! ### Gluing -/

/-- The two-open cover of stage `N`. -/
def oldInvarianceCover (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Bool → (projectiveContactStage (k := k) N).Opens
  | true => oldIsoLocus N j h
  | false => oldAwayLocus N j h

theorem oldInvarianceCover_covers (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (x : projectiveContactStage (k := k) N) : ∃ b, x ∈ oldInvarianceCover N j h b :=
  (oldLoci_cover N j h x).elim (fun hx => ⟨true, hx⟩) (fun hx => ⟨false, hx⟩)

/-- The two local isomorphisms between the literal pullbacks. -/
def oldInvarianceLocalIso (N j : ℕ) (h : j + 1 + 1 ≤ N) (b : Bool) :
    (schemeModulePullback (oldInvarianceCover (k := k) N j h b).ι).obj
      ((schemeModulePullback (oldBetween N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j))) ≅
      (schemeModulePullback (oldInvarianceCover (k := k) N j h b).ι).obj
        (schemeKernelIdeal (oldFinalMap N j h)) := by
  cases b with
  | true => exact oldLocusIso N j h
  | false => exact oldAwayIso N j h

theorem oldInvarianceLocalIso_map (N j : ℕ) (h : j + 1 + 1 ≤ N) (b : Bool) :
    (oldInvarianceLocalIso (k := k) N j h b).hom ≫
        (schemeModulePullback (oldInvarianceCover N j h b).ι).map
          (schemeKernelIdealι (oldFinalMap N j h)) =
      (schemeModulePullback (oldInvarianceCover N j h b).ι).map
        (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h)) := by
  cases b with
  | true =>
    have h' := oldLocusIso_inclusion (k := k) N j h
    rw [pulledKernelInclusion] at h'
    exact cancel_final_iso _ _ _ _ h'
  | false =>
    have h' := oldAwayIso_inclusion (k := k) N j h
    rw [pulledKernelInclusion] at h'
    exact cancel_final_iso _ _ _ _ h'

local instance oldFinalKernelInclusion_mono (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Mono (schemeKernelIdealι (oldFinalMap (k := k) N j h)) := by
  unfold schemeKernelIdealι
  infer_instance

/-- The pullback of the ideal of `C_j` to stage `N` is the ideal of its embedded image. -/
def oldInvarianceIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (schemeModulePullback (oldBetween (k := k) N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) ≅
      schemeKernelIdeal (oldFinalMap (k := k) N j h) :=
  schemeModuleMonicFactorIsoOnOpenCover (oldInvarianceCover N j h) (oldInvarianceCover_covers N j h)
    (schemeKernelIdealι (oldFinalMap N j h))
    (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h))
    (oldInvarianceLocalIso N j h) (oldInvarianceLocalIso_map N j h)

@[reassoc] theorem oldInvarianceIso_inclusion (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldInvarianceIso (k := k) N j h).hom ≫ schemeKernelIdealι (oldFinalMap N j h) =
      pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h) := by
  unfold oldInvarianceIso
  exact schemeModuleMonicFactorIsoOnOpenCover_comp (oldInvarianceCover N j h)
    (oldInvarianceCover_covers N j h) (schemeKernelIdealι (oldFinalMap N j h))
    (pulledKernelInclusion (oldExceptionalStrictι j) (oldBetween N j h))
    (oldInvarianceLocalIso N j h) (oldInvarianceLocalIso_map N j h)

/-! ### The Picard class on the later stages -/

/-- The ideal of the embedded image of `C_j` is invertible on stage `N`. -/
theorem oldFinalKernel_isInvertible (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveContactStage (k := k) N).ringCatSheaf)
      (schemeKernelIdeal (oldFinalMap N j h)) := by
  letI : KltDP.SheafOfModules.IsInvertible (R := (projectiveContactStage (k := k) N).ringCatSheaf)
      ((schemeModulePullback (oldBetween (k := k) N j h)).obj
        (schemeKernelIdeal (oldExceptionalStrictι j))) :=
    (pullbackInvertibleSheaf (oldBetween N j h) (oldStrictKernelLine j)).property
  exact KltDP.SheafOfModules.IsInvertible.of_iso
    (R := (projectiveContactStage (k := k) N).ringCatSheaf) (oldInvarianceIso N j h)

/-- The ideal line of the image of `C_j` on stage `N`. -/
def oldFinalKernelLine (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    InvertibleSheaf (projectiveContactStage (k := k) N) :=
  ⟨schemeKernelIdeal (oldFinalMap N j h), oldFinalKernel_isInvertible N j h⟩

/-- The Picard class of `C_j` on stage `N` (ideal-sheaf sign convention). -/
def oldExceptionalStrictClass (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    Additive (projectiveContactStage (k := k) N).Pic :=
  -Additive.ofMul (oldFinalKernelLine (k := k) N j h).toPic

theorem oldFinalKernelLine_toPic (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldFinalKernelLine (k := k) N j h).toPic =
      (pullbackInvertibleSheaf (oldBetween (k := k) N j h) (oldStrictKernelLine j)).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) N)
  apply Units.ext
  change ((oldFinalKernelLine (k := k) N j h).toPic :
      Skeleton (projectiveContactStage (k := k) N).Modules) =
    ((pullbackInvertibleSheaf (oldBetween (k := k) N j h) (oldStrictKernelLine j)).toPic :
      Skeleton (projectiveContactStage (k := k) N).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨(oldInvarianceIso N j h).symm⟩

/-- The class of `C_j` on stage `N` is the pullback of its birth-stage class. -/
theorem oldExceptionalStrictClass_pullback (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldExceptionalStrictClass (k := k) N j h =
      (schemePicardPullbackHom (oldBetween (k := k) N j h)).toAdditive (oldStrictPicardClass j) := by
  change -Additive.ofMul (oldFinalKernelLine (k := k) N j h).toPic =
    (schemePicardPullbackHom (oldBetween (k := k) N j h)).toAdditive
      (-Additive.ofMul (oldStrictKernelLine j).toPic)
  rw [map_neg]
  change -Additive.ofMul (oldFinalKernelLine (k := k) N j h).toPic =
    -Additive.ofMul (schemePicardPullbackHom (oldBetween (k := k) N j h) (oldStrictKernelLine j).toPic)
  rw [schemePicardPullbackHom_toPic, oldFinalKernelLine_toPic]

/-- The total exceptional classes of the birth stage pull back to those of stage `N`. -/
theorem totalExceptionalClass_pullback_between (N j : ℕ) (h : j + 1 + 1 ≤ N) (i : Fin (j + 1 + 1)) :
    (schemePicardPullbackHom (oldBetween (k := k) N j h)).toAdditive
        (totalExceptionalClass (j + 1 + 1) i) =
      totalExceptionalClass N (Fin.castLE h i) := by
  have hb : between (projectiveProductInitial (k := k)) (Fin.castLE h i).isLt =
      between (projectiveProductInitial (k := k)) h ≫ between (projectiveProductInitial (k := k)) i.isLt :=
    (between_comp (projectiveProductInitial (k := k)) i.isLt h).symm
  unfold totalExceptionalClass
  rw [hb, schemePicardPullbackHom_comp]
  rfl

/-- `C_j = E_j^{(N)} − E_{j+1}^{(N)}` on every stage `N ≥ j + 2`, with the total exceptional
classes indexed through `Fin.castLE`. -/
theorem oldExceptionalStrictClass_eq (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldExceptionalStrictClass (k := k) N j h =
      totalExceptionalClass N (Fin.castLE h (Fin.castSucc (Fin.last j))) -
        totalExceptionalClass N (Fin.castLE h (Fin.last (j + 1))) := by
  rw [oldExceptionalStrictClass_pullback, oldStrictPicardClass_eq_total, map_sub,
    totalExceptionalClass_pullback_between, totalExceptionalClass_pullback_between]

/-- The same relation with the total exceptional classes indexed by the stage numbers `j`, `j+1`. -/
theorem oldExceptionalStrictClass_eq' (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    oldExceptionalStrictClass (k := k) N j h =
      totalExceptionalClass N ⟨j, by omega⟩ - totalExceptionalClass N ⟨j + 1, by omega⟩ := by
  rw [show (⟨j, by omega⟩ : Fin N) = Fin.castLE h (Fin.castSucc (Fin.last j)) from rfl,
    show (⟨j + 1, by omega⟩ : Fin N) = Fin.castLE h (Fin.last (j + 1)) from rfl]
  exact oldExceptionalStrictClass_eq N j h

/-- Proposition 10.1, `C_j` clause, on one contact tower: for every `j` and every stage
`N ≥ j + 2`, the class of the (image of the) strict transform of the exceptional curve `E_j` is
`E_j^{(N)} − E_{j+1}^{(N)}`. The classes live in `Additive (projectiveContactStage N).Pic : Type u`
for the base field `k : Type u`. -/
theorem oldExceptionalStrictClasses_tower :
    ∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      oldExceptionalStrictClass (k := k) N j h =
        totalExceptionalClass N ⟨j, by omega⟩ - totalExceptionalClass N ⟨j + 1, by omega⟩ :=
  fun N j h => oldExceptionalStrictClass_eq' N j h

end KltDP.Examples.FrobeniusOldExceptionalLaterStages
