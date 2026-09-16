import KltDP.Geometry.SchemeKernelOpenBaseChange
import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.SchemeKernelFrameSquare
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The kernel ideal of a base change along a morphism which is an isomorphism near the subscheme

Let `π : S ⟶ T` be a morphism, `g : Z ⟶ T` a closed immersion and `V` an open of `T` containing the
range of `g` over which `π` restricts to an isomorphism (`IsIso (π ∣_ V)`).  The base change
`pullback.fst π g : S ×_T Z ⟶ S` is then a closed immersion of `S` whose kernel ideal is the inverse
image along `π` of the kernel ideal of `g`:

  `π^* I(Z) ≅ I(S ×_T Z)`   (`baseChangeKernelIso`),

compatibly with the inclusions into the structure sheaf (`baseChangeKernelIso_inclusion`).  The
isomorphism is glued from the two opens `π ⁻¹ᵁ V` and `π ⁻¹ᵁ (range g)ᶜ`, which cover `S` because
`range g ⊆ V`: over the first the accepted kernel base-change comparisons along open immersions
identify both modules (`isoLocusKernelIso`, whose inclusion compatibility is proved here for the
accepted `kernelRestrictBaseChangeIso` and `kernelOpenBaseChangeIso`), over the second both are
framed by the unit because the base change has empty source there (`awayKernelIso`).  The gluing is
the accepted `schemeModuleMonicFactorIsoOnOpenCover`, as in the accepted `oldInvarianceIso`.

Consequences: the kernel ideal of the base change is invertible whenever the kernel ideal of `g` is,
and its Picard class is the pullback along `π` of the class of `g` (`neg_baseChangeKernelLine_toPic`,
in the ideal-sheaf sign convention `[C] = -[I(C)]`).  This is the local-to-global step that a Picard
class cannot perform on its own: the identity is proved between ideal modules, and only then pushed
to `Pic`.

Nothing here assumes flatness of `π`; the hypothesis used is exactly that `π` is an isomorphism over
an open containing the closed subscheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKernelBaseChangeIsoLocus

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchemeKernelOpenBaseChange KltDP.Geometry.KernelLinePullbackOffRange

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-! ### Two accepted private lemmas, restated -/

/-- Multiplication by the unit function is the identity of the structure module (the accepted
private lemma of `FrobeniusOldExceptionalLaterStages`, restated). -/
private theorem scalar_one' (X : Scheme.{u}) :
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

/-- Cancel a common final isomorphism (the accepted private lemma, restated). -/
private theorem cancel_final_iso' {C : Type*} [Category C]
    {M N Q R : C} (e : Q ≅ R) (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ Q)
    (h : a ≫ b ≫ e.hom = c ≫ e.hom) : a ≫ b = c := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc] using h

/-! ### Inclusion compatibility of the accepted base-change comparisons -/

section Comparisons

variable {X Z : Scheme.{u}}

set_option maxHeartbeats 4000000 in
/-- **The kernel comparison of the base change along `V.ι` preserves the inclusions.** -/
theorem kernelRestrictBaseChangeIso_inclusion (f : Z ⟶ X) (V : X.Opens) :
    (kernelRestrictBaseChangeIso f V).hom ≫ pulledKernelInclusion f V.ι =
      schemeKernelIdealι (pullback.fst V.ι f) := by
  simp only [kernelRestrictBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, schemeKernelPrecompIso_hom_ι]
  exact (Iso.inv_comp_eq _).mpr
    (schemeKernelIdealEqIso_hom_ι (baseChangeRestrictIso_hom_restrict f V)).symm

private theorem kernelOpenBaseChangeIso_rfl {W : Scheme.{u}} (f : Z ⟶ X) {V : X.Opens}
    (e : W ≅ V.toScheme) :
    kernelOpenBaseChangeIso f e (e.hom ≫ V.ι) rfl =
      schemeKernelTransportIso (pullback.fst V.ι f) e.symm (pullback.fst (e.hom ≫ V.ι) f)
          (baseChangeCompIso f e) (baseChangeCompIso_hom_fst f e) ≪≫
        (schemeModulePullback e.hom).mapIso (kernelRestrictBaseChangeIso f V) ≪≫
        (schemeModulePullbackCompIso e.hom V.ι).app (schemeKernelIdeal f) :=
  rfl

set_option maxHeartbeats 4000000 in
/-- **The kernel comparison of the base change along an open immersion preserves the
inclusions.** -/
theorem kernelOpenBaseChangeIso_inclusion {W : Scheme.{u}} (f : Z ⟶ X) {V : X.Opens}
    (e : W ≅ V.toScheme) (j : W ⟶ X) (hj : e.hom ≫ V.ι = j) :
    (kernelOpenBaseChangeIso f e j hj).hom ≫ pulledKernelInclusion f j =
      schemeKernelIdealι (pullback.fst j f) := by
  subst hj
  rw [kernelOpenBaseChangeIso_rfl]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    schemeKernelPullbackCompIso_inclusion]
  rw [← Category.assoc ((schemeModulePullback e.hom).map (kernelRestrictBaseChangeIso f V).hom),
    ← Functor.map_comp, kernelRestrictBaseChangeIso_inclusion]
  have ht := schemeKernelTransportIso_hom_inclusion (pullback.fst V.ι f) e.symm
    (pullback.fst (e.hom ≫ V.ι) f) (baseChangeCompIso f e) (baseChangeCompIso_hom_fst f e)
  rw [pulledKernelInclusion] at ht
  exact ht

end Comparisons

/-! ### The base change of a closed immersion -/

section BaseChange

variable {S T Z : Scheme.{u}} (π : S ⟶ T) (g : Z ⟶ T)

/-! #### Over the iso locus -/

section IsoLocus

variable (V : T.Opens) [IsIso (π ∣_ V)]

/-- The restriction of `π` over `V`, as an isomorphism. -/
def isoLocusIso : (π ⁻¹ᵁ V).toScheme ≅ V.toScheme :=
  asIso (π ∣_ V)

theorem isoLocusIso_hom_ι : (isoLocusIso π V).hom ≫ V.ι = (π ⁻¹ᵁ V).ι ≫ π := by
  rw [isoLocusIso, asIso_hom, morphismRestrict_ι]

/-- **Over the iso locus the kernel of the base change is the pullback of the kernel of `g`.** -/
def isoLocusKernelIso :
    (schemeModulePullback (π ⁻¹ᵁ V).ι).obj (schemeKernelIdeal (pullback.fst π g)) ≅
      (schemeModulePullback ((π ⁻¹ᵁ V).ι ≫ π)).obj (schemeKernelIdeal g) :=
  (kernelRestrictBaseChangeIso (pullback.fst π g) (π ⁻¹ᵁ V)).symm ≪≫
    (schemeKernelIdealEqIso (pullbackRightPullbackFstIso_hom_fst π g (π ⁻¹ᵁ V).ι)).symm ≪≫
    schemeKernelPrecompIso (pullbackRightPullbackFstIso π g (π ⁻¹ᵁ V).ι)
      (pullback.fst ((π ⁻¹ᵁ V).ι ≫ π) g) ≪≫
    kernelOpenBaseChangeIso g (isoLocusIso π V) ((π ⁻¹ᵁ V).ι ≫ π) (isoLocusIso_hom_ι π V)

set_option maxHeartbeats 4000000 in
theorem isoLocusKernelIso_inclusion :
    (isoLocusKernelIso π g V).hom ≫ pulledKernelInclusion g ((π ⁻¹ᵁ V).ι ≫ π) =
      pulledKernelInclusion (pullback.fst π g) (π ⁻¹ᵁ V).ι := by
  simp only [isoLocusKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernelOpenBaseChangeIso_inclusion, schemeKernelPrecompIso_hom_ι]
  rw [← schemeKernelIdealEqIso_hom_ι (pullbackRightPullbackFstIso_hom_fst π g (π ⁻¹ᵁ V).ι)]
  simp only [Iso.inv_hom_id_assoc]
  exact (Iso.inv_comp_eq _).mpr
    (kernelRestrictBaseChangeIso_inclusion (pullback.fst π g) (π ⁻¹ᵁ V)).symm

end IsoLocus

/-! #### Off the range of `g` -/

section Away

variable [IsClosedImmersion g]

/-- The base change has empty source over the complement of the range of `g`. -/
instance baseChangeAway_isEmpty :
    IsEmpty ((pullback.fst π g ⁻¹ᵁ (π ⁻¹ᵁ rangeComplement g)).toScheme) := by
  refine ⟨fun z => ?_⟩
  have hz : π.base ((pullback.fst π g).base z.1) ∉ Set.range g.base := z.2
  refine hz ⟨(pullback.snd π g).base z.1, ?_⟩
  rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, ← pullback.condition]

/-- The unit frame of `I(g)` on the complement of the range of `g`. -/
def awayStrictFrame :
    _root_.SheafOfModules.unit (rangeComplement g).toScheme.ringCatSheaf ≅
      (schemeModulePullback (rangeComplement g).ι).obj (schemeKernelIdeal g) := by
  letI := emptyKernelGenerator_isIso' (g ∣_ rangeComplement g)
  exact asIso (schemeKernelGenerator (g ∣_ rangeComplement g) 1 (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso g (rangeComplement g)

theorem awayStrictFrame_inclusion :
    (awayStrictFrame g).hom ≫ pulledKernelInclusion g (rangeComplement g).ι =
      schemeScalarEnd (Y := (rangeComplement g).toScheme) 1 := by
  have h' := localKernelGlobalEquation_inclusion g (rangeComplement g) 1 (Subsingleton.elim _ _)
  convert h' using 3

/-- The same frame, transported to the pullback of `I(g)` along `π`. -/
def pulledAwayFrame :
    _root_.SheafOfModules.unit (π ⁻¹ᵁ rangeComplement g).toScheme.ringCatSheaf ≅
      (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).obj
        ((schemeModulePullback π).obj (schemeKernelIdeal g)) :=
  schemeKernelFrameOnSquare g (rangeComplement g).ι (π ∣_ rangeComplement g)
    (π ⁻¹ᵁ rangeComplement g).ι π (morphismRestrict_ι π (rangeComplement g)) (awayStrictFrame g)

theorem pulledAwayFrame_inclusion :
    (pulledAwayFrame π g).hom ≫
        (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).map (pulledKernelInclusion g π) ≫
        (schemeModulePullbackUnitIso (π ⁻¹ᵁ rangeComplement g).ι).hom =
      𝟙 (_root_.SheafOfModules.unit (π ⁻¹ᵁ rangeComplement g).toScheme.ringCatSheaf) := by
  have h' := schemeKernelFrameOnSquare_inclusion g (rangeComplement g).ι
    (π ∣_ rangeComplement g) (π ⁻¹ᵁ rangeComplement g).ι π
    (morphismRestrict_ι π (rangeComplement g)) (awayStrictFrame g) 1 (awayStrictFrame_inclusion g)
  rw [map_one, scalar_one'] at h'
  convert h' using 3

/-- The unit frame of the kernel of the base change over the same open. -/
def awayFinalFrame :
    _root_.SheafOfModules.unit (π ⁻¹ᵁ rangeComplement g).toScheme.ringCatSheaf ≅
      (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).obj
        (schemeKernelIdeal (pullback.fst π g)) := by
  letI := emptyKernelGenerator_isIso' (pullback.fst π g ∣_ (π ⁻¹ᵁ rangeComplement g))
  exact asIso (schemeKernelGenerator (pullback.fst π g ∣_ (π ⁻¹ᵁ rangeComplement g)) 1
      (Subsingleton.elim _ _)) ≪≫
    localKernelToGlobalPullbackIso (pullback.fst π g) (π ⁻¹ᵁ rangeComplement g)

theorem awayFinalFrame_inclusion :
    (awayFinalFrame π g).hom ≫
        pulledKernelInclusion (pullback.fst π g) (π ⁻¹ᵁ rangeComplement g).ι =
      𝟙 (_root_.SheafOfModules.unit (π ⁻¹ᵁ rangeComplement g).toScheme.ringCatSheaf) := by
  have h' := localKernelGlobalEquation_inclusion (pullback.fst π g) (π ⁻¹ᵁ rangeComplement g) 1
    (Subsingleton.elim _ _)
  rw [scalar_one'] at h'
  convert h' using 3

/-- **Off the range of `g` both kernel modules are the structure sheaf.** -/
def awayKernelIso :
    (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).obj
        ((schemeModulePullback π).obj (schemeKernelIdeal g)) ≅
      (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).obj
        (schemeKernelIdeal (pullback.fst π g)) :=
  (pulledAwayFrame π g).symm ≪≫ awayFinalFrame π g

theorem awayKernelIso_inclusion :
    (awayKernelIso π g).hom ≫
        pulledKernelInclusion (pullback.fst π g) (π ⁻¹ᵁ rangeComplement g).ι =
      (schemeModulePullback (π ⁻¹ᵁ rangeComplement g).ι).map (pulledKernelInclusion g π) ≫
        (schemeModulePullbackUnitIso (π ⁻¹ᵁ rangeComplement g).ι).hom := by
  have h1 := pulledAwayFrame_inclusion π g
  have h2 := awayFinalFrame_inclusion π g
  rw [awayKernelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, h2, Category.comp_id]
  exact ((Iso.hom_comp_eq_id _).mp h1).symm

end Away

/-! #### The global comparison -/

section Global

variable [IsClosedImmersion g]

/-- The two-open cover of `S`: the iso locus and the complement of the range of `g`. -/
def baseChangeCover (V : T.Opens) : Bool → S.Opens
  | true => π ⁻¹ᵁ V
  | false => π ⁻¹ᵁ rangeComplement g

theorem baseChangeCover_covers (V : T.Opens) (hgV : Set.range g.base ⊆ (V : Set T)) (x : S) :
    ∃ b, x ∈ baseChangeCover π g V b := by
  by_cases hx : π.base x ∈ Set.range g.base
  · exact ⟨true, hgV hx⟩
  · exact ⟨false, hx⟩

/-- The two local comparisons of the pulled kernel with the kernel of the base change. -/
def baseChangeLocalIso (V : T.Opens) [IsIso (π ∣_ V)] (b : Bool) :
    (schemeModulePullback (baseChangeCover π g V b).ι).obj
        ((schemeModulePullback π).obj (schemeKernelIdeal g)) ≅
      (schemeModulePullback (baseChangeCover π g V b).ι).obj
        (schemeKernelIdeal (pullback.fst π g)) := by
  cases b with
  | true =>
    exact (schemeModulePullbackCompIso (π ⁻¹ᵁ V).ι π).app (schemeKernelIdeal g) ≪≫
      (isoLocusKernelIso π g V).symm
  | false => exact awayKernelIso π g

set_option maxHeartbeats 4000000 in
theorem baseChangeLocalIso_map (V : T.Opens) [IsIso (π ∣_ V)] (b : Bool) :
    (baseChangeLocalIso π g V b).hom ≫
        (schemeModulePullback (baseChangeCover π g V b).ι).map
          (schemeKernelIdealι (pullback.fst π g)) =
      (schemeModulePullback (baseChangeCover π g V b).ι).map (pulledKernelInclusion g π) := by
  cases b with
  | true =>
    have h' : ((schemeModulePullbackCompIso (π ⁻¹ᵁ V).ι π).app (schemeKernelIdeal g) ≪≫
          (isoLocusKernelIso π g V).symm).hom ≫
            pulledKernelInclusion (pullback.fst π g) (π ⁻¹ᵁ V).ι =
        (schemeModulePullback (π ⁻¹ᵁ V).ι).map (pulledKernelInclusion g π) ≫
          (schemeModulePullbackUnitIso (π ⁻¹ᵁ V).ι).hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
      rw [← isoLocusKernelIso_inclusion π g V]
      simp only [Iso.inv_hom_id_assoc]
      exact schemeKernelPullbackCompIso_inclusion g π (π ⁻¹ᵁ V).ι
    rw [pulledKernelInclusion] at h'
    exact cancel_final_iso' _ _ _ _ h'
  | false =>
    have h' := awayKernelIso_inclusion π g
    rw [pulledKernelInclusion] at h'
    exact cancel_final_iso' _ _ _ _ h'

local instance baseChangeKernelι_mono : Mono (schemeKernelIdealι (pullback.fst π g)) := by
  unfold schemeKernelIdealι
  infer_instance

set_option maxHeartbeats 4000000 in
/-- **The kernel ideal of the base change is the inverse image along `π` of the kernel ideal of
`g`.** -/
def baseChangeKernelIso (V : T.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set T)) :
    (schemeModulePullback π).obj (schemeKernelIdeal g) ≅ schemeKernelIdeal (pullback.fst π g) :=
  schemeModuleMonicFactorIsoOnOpenCover (baseChangeCover π g V) (baseChangeCover_covers π g V hgV)
    (schemeKernelIdealι (pullback.fst π g)) (pulledKernelInclusion g π)
    (baseChangeLocalIso π g V) (baseChangeLocalIso_map π g V)

set_option maxHeartbeats 4000000 in
theorem baseChangeKernelIso_inclusion (V : T.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set T)) :
    (baseChangeKernelIso π g V hgV).hom ≫ schemeKernelIdealι (pullback.fst π g) =
      pulledKernelInclusion g π :=
  schemeModuleMonicFactorIsoOnOpenCover_comp (baseChangeCover π g V)
    (baseChangeCover_covers π g V hgV) (schemeKernelIdealι (pullback.fst π g))
    (pulledKernelInclusion g π) (baseChangeLocalIso π g V) (baseChangeLocalIso_map π g V)

set_option maxHeartbeats 4000000 in
/-- The kernel ideal of the base change is invertible whenever that of `g` is. -/
theorem isInvertible_baseChangeKernel (V : T.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set T))
    (hg : KltDP.SheafOfModules.IsInvertible (R := T.ringCatSheaf) (schemeKernelIdeal g)) :
    KltDP.SheafOfModules.IsInvertible (R := S.ringCatSheaf)
      (schemeKernelIdeal (pullback.fst π g)) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible π (schemeKernelIdeal g) hg)
    (baseChangeKernelIso π g V hgV)

/-- The ideal line of the base change. -/
def baseChangeKernelLine (V : T.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set T))
    (hg : KltDP.SheafOfModules.IsInvertible (R := T.ringCatSheaf) (schemeKernelIdeal g)) :
    InvertibleSheaf S :=
  ⟨schemeKernelIdeal (pullback.fst π g), isInvertible_baseChangeKernel π g V hgV hg⟩

set_option maxHeartbeats 4000000 in
/-- **The class of the base change is the pullback along `π` of the class of `g`** (ideal-sheaf
sign convention). -/
theorem neg_baseChangeKernelLine_toPic (V : T.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set T))
    (hg : KltDP.SheafOfModules.IsInvertible (R := T.ringCatSheaf) (schemeKernelIdeal g)) :
    -Additive.ofMul (baseChangeKernelLine π g V hgV hg).toPic =
      (schemePicardPullbackHom π).toAdditive
        (-Additive.ofMul
          (InvertibleSheaf.toPic (⟨schemeKernelIdeal g, hg⟩ : InvertibleSheaf T))) := by
  rw [map_neg, toPic_eq_pullback_of_iso π (⟨schemeKernelIdeal g, hg⟩ : InvertibleSheaf T)
    (baseChangeKernelLine π g V hgV hg) (baseChangeKernelIso π g V hgV).symm]
  rfl

end Global

end BaseChange

end KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
