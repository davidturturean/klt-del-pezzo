import KltDP.Geometry.PicardClopenInjective
import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate
import KltDP.Geometry.TransitionUnitPicardComparison

/-!
# The Picard group of a clopen decomposition

BRIEF23, task 1. Let `U : ι → X.Opens` be pairwise disjoint opens covering the scheme `X`
(a clopen decomposition `X = ⊔ᵢ U i`, any index type in universe `u`). Then restriction to the
pieces is a group isomorphism **`X.Pic ≃* (∀ i, (U i).toScheme.Pic)`** (`picardEquiv`).

* Injectivity (`restrictionPi_injective`): a class restricting trivially to every piece comes from
  a module sheaf with an atlas of pullback charts on the cover `U` itself (the accepted
  `localTrivializationsOfOpenCharts`, `openChartOfPullback`); its off-diagonal transition units
  live in the subsingleton rings `Γ(X, U i ⊓ U j) = Γ(X, ⊥)` and the diagonal ones are `1`, so the
  extracted cocycle is gauge-equivalent to the constant cocycle and the accepted `unitIsoOfGauge`
  trivialises the sheaf (`unitIsoOfClopenCover`).
* Surjectivity (`restrictionPi_surjective`): given classes `c i`, represent each by an invertible
  sheaf `L i` with its atlas (`localTrivializations`) and extracted cocycle `g i` on a cover
  `W i` of `U i` (accepted `picardClass_eq_toPic_of_extraction`). Transport each cocycle to `X`
  along the open immersion `(U i).ι` (`transportUnits`: the inverse section-ring map
  `openSectionsInv` after restriction to the preimage of the image), assemble the block cocycle on
  the sigma cover `⟨i, a⟩ ↦ (U i).ι ''ᵁ W i a` with `1` on the (empty) mixed overlaps
  (`sigmaUnits`, `sigmaUnits_isCocycle`), and take the class of the glued line bundle
  (`gluedClass`). Its restriction to `U i` is computed by the accepted `pullbackGluedClass`
  (pullback of a glued class is the class of the pulled-back cocycle) and
  `picardClass_eq_of_refinement` (restrict the sigma cover to the `i`-th block, where the pulled
  back units are the original ones: `refinedUnits_sigma`), and equals `c i`.

The two-piece case `X = U ⊔ V` is `picardEquivTwo`. No finiteness of the index type is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.PicardClopenDecomposition

open KltDP.Geometry KltDP.Geometry.RationalTreePicard KltDP.Geometry.PicardClopen
  SchemeModuleRestriction TransitionUnitExtraction TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

/-! ## Sections of open immersions -/

/-- The section map of an open immersion inverts `openSectionsInv`. -/
theorem app_openSectionsInv (V : X.Opens) {W : X.Opens} (hW : W ≤ V)
    (s : Γ(V.toScheme, V.ι ⁻¹ᵁ W)) : V.ι.app W (openSectionsInv V hW s) = s := by
  haveI : IsIso (V.ι.app W) := Scheme.Hom.isIso_app V.ι W (by simpa using hW)
  exact (asIso (V.ι.app W)).commRingCatIsoToRingEquiv.apply_symm_apply s

/-- The section map of an open immersion commutes with restriction. -/
theorem app_res (V : X.Opens) {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) (s : Γ(X, W₂)) :
    V.ι.app W₁ (res X h s) = res V.toScheme (fun _ hx => h hx) (V.ι.app W₂ s) := by
  have hn := ConcreteCategory.congr_hom (V.ι.naturality (homOfLE h).op) s
  simp only [CommRingCat.comp_apply] at hn
  exact hn

/-! ## Transport of a cocycle along an open immersion -/

section Transport

variable (U : X.Opens) {κ : Type u} (W : κ → U.toScheme.Opens)
  (g : ∀ a b : κ, Γ(U.toScheme, W a ⊓ W b)ˣ)

/-- The images in `X` of the opens of a cover of `U`. -/
def imageCover (a : κ) : X.Opens := U.ι ''ᵁ W a

theorem imageCover_le (a : κ) : imageCover U W a ≤ U := by
  have h : U.ι ''ᵁ W a ≤ U.ι ''ᵁ ⊤ := U.ι.image_le_image_of_le le_top
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at h

theorem preimage_imageCover (a : κ) : U.ι ⁻¹ᵁ imageCover U W a = W a :=
  U.ι.preimage_image_eq (W a)

theorem preimage_imageCover_inf_le (a b : κ) :
    U.ι ⁻¹ᵁ (imageCover U W a ⊓ imageCover U W b) ≤ W a ⊓ W b := by
  intro x hx
  have h1 : x ∈ U.ι ⁻¹ᵁ imageCover U W a := hx.1
  have h2 : x ∈ U.ι ⁻¹ᵁ imageCover U W b := hx.2
  rw [preimage_imageCover] at h1 h2
  exact ⟨h1, h2⟩

theorem preimage_imageCover_inf3_le (a b c : κ) :
    U.ι ⁻¹ᵁ (imageCover U W a ⊓ imageCover U W b ⊓ imageCover U W c) ≤ W a ⊓ W b ⊓ W c := by
  intro x hx
  have h1 : x ∈ U.ι ⁻¹ᵁ imageCover U W a := hx.1.1
  have h2 : x ∈ U.ι ⁻¹ᵁ imageCover U W b := hx.1.2
  have h3 : x ∈ U.ι ⁻¹ᵁ imageCover U W c := hx.2
  rw [preimage_imageCover] at h1 h2 h3
  exact ⟨⟨h1, h2⟩, h3⟩

theorem iSup_imageCover (hW : (⨆ a, W a) = ⊤) : (⨆ a, imageCover U W a) = U := by
  unfold imageCover
  rw [← Scheme.Hom.image_iSup, hW, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

/-- The cocycle `g` transported to `X`: restrict to the preimage of the pairwise image, then
apply the inverse section-ring map of the open immersion. -/
def transportUnits (a b : κ) : Γ(X, imageCover U W a ⊓ imageCover U W b)ˣ :=
  Units.map (openSectionsInv U (inf_le_left.trans (imageCover_le U W a))).toMonoidHom
    (Units.map (res U.toScheme (preimage_imageCover_inf_le U W a b)).toMonoidHom (g a b))

theorem transportUnits_val (a b : κ) :
    (transportUnits U W g a b : Γ(X, imageCover U W a ⊓ imageCover U W b)) =
      openSectionsInv U (inf_le_left.trans (imageCover_le U W a))
        (res U.toScheme (preimage_imageCover_inf_le U W a b) (g a b)) := rfl

/-- The transported family is a cocycle. -/
theorem transportUnits_isCocycle (hg : IsCocycle U.toScheme W g) :
    IsCocycle X (imageCover U W) (transportUnits U W g) where
  unit_self a := by
    rw [transportUnits_val, hg.unit_self, map_one, map_one]
  mul_res a b c := by
    have hle : imageCover U W a ⊓ imageCover U W b ⊓ imageCover U W c ≤ U :=
      inf_le_left.trans (inf_le_left.trans (imageCover_le U W a))
    haveI : IsIso (U.ι.app (imageCover U W a ⊓ imageCover U W b ⊓ imageCover U W c)) :=
      Scheme.Hom.isIso_app U.ι _ (by simpa using hle)
    have hinj := (asIso (U.ι.app (imageCover U W a ⊓ imageCover U W b ⊓ imageCover U W c))).commRingCatIsoToRingEquiv.injective
    apply hinj
    show U.ι.app _ (res X _ (transportUnits U W g a b).val *
      res X _ (transportUnits U W g b c).val) =
      U.ι.app _ (res X _ (transportUnits U W g a c).val)
    rw [map_mul, app_res, app_res, app_res, transportUnits_val, transportUnits_val,
      transportUnits_val, app_openSectionsInv, app_openSectionsInv, app_openSectionsInv,
      res_res, res_res, res_res]
    exact IsCocycle.mul_res_of_le U.toScheme W g hg (preimage_imageCover_inf3_le U W a b c)

end Transport

/-! ## The block cocycle on a clopen decomposition -/

section Sigma

variable {ι : Type u} [DecidableEq ι] (U : ι → X.Opens)
  (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥)
  {κ : ι → Type u} (W : ∀ i, κ i → (U i).toScheme.Opens)
  (g : ∀ i (a b : κ i), Γ((U i).toScheme, W i a ⊓ W i b)ˣ)

/-- The sigma cover of `X`: the images of all the local covers. -/
abbrev sigmaCover (x : Σ i, κ i) : X.Opens := imageCover (U x.1) (W x.1) x.2

omit [DecidableEq ι] in
theorem sigmaCover_le (x : Σ i, κ i) : sigmaCover U W x ≤ U x.1 :=
  imageCover_le (U x.1) (W x.1) x.2

/-- The block cocycle: the transported cocycles on each block, `1` on the mixed overlaps. -/
def sigmaUnits : ∀ x y : Σ i, κ i, Γ(X, sigmaCover U W x ⊓ sigmaCover U W y)ˣ
  | ⟨i, a⟩, ⟨j, b⟩ =>
    if h : i = j then (by subst h; exact transportUnits (U _) (W _) (g _) a b) else 1

theorem sigmaUnits_same (i : ι) (a b : κ i) :
    sigmaUnits U W g ⟨i, a⟩ ⟨i, b⟩ = transportUnits (U i) (W i) (g i) a b := by
  simp only [sigmaUnits, dif_pos]

theorem sigmaUnits_ne {i j : ι} (hij : i ≠ j) (a : κ i) (b : κ j) :
    sigmaUnits U W g ⟨i, a⟩ ⟨j, b⟩ = 1 := by
  simp only [sigmaUnits, dif_neg hij]

omit [DecidableEq ι] in
include hdisj in
theorem sigmaCover_inf3_eq_bot_of_ne {x y z : Σ i, κ i} {i j : ι} (hij : i ≠ j)
    (hx : sigmaCover U W x ⊓ sigmaCover U W y ⊓ sigmaCover U W z ≤ U i)
    (hy : sigmaCover U W x ⊓ sigmaCover U W y ⊓ sigmaCover U W z ≤ U j) :
    sigmaCover U W x ⊓ sigmaCover U W y ⊓ sigmaCover U W z = ⊥ :=
  le_bot_iff.mp ((le_inf hx hy).trans (hdisj i j hij).le)

include hdisj in
/-- The block cocycle is a cocycle. -/
theorem sigmaUnits_isCocycle (hg : ∀ i, IsCocycle (U i).toScheme (W i) (g i)) :
    IsCocycle X (sigmaCover U W) (sigmaUnits U W g) where
  unit_self := by
    rintro ⟨i, a⟩
    rw [sigmaUnits_same]
    exact (transportUnits_isCocycle (U i) (W i) (g i) (hg i)).unit_self a
  mul_res := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨l, c⟩
    by_cases hij : i = j
    · subst hij
      by_cases hil : i = l
      · subst hil
        simp only [sigmaUnits_same]
        exact (transportUnits_isCocycle (U i) (W i) (g i) (hg i)).mul_res a b c
      · haveI : Subsingleton Γ(X, sigmaCover U W ⟨i, a⟩ ⊓ sigmaCover U W ⟨i, b⟩ ⊓
            sigmaCover U W ⟨l, c⟩) :=
          subsingleton_sections_of_eq_bot (sigmaCover_inf3_eq_bot_of_ne U hdisj W hil
            (inf_le_left.trans (inf_le_left.trans (sigmaCover_le U W ⟨i, a⟩)))
            (inf_le_right.trans (sigmaCover_le U W ⟨l, c⟩)))
        exact Subsingleton.elim _ _
    · haveI : Subsingleton Γ(X, sigmaCover U W ⟨i, a⟩ ⊓ sigmaCover U W ⟨j, b⟩ ⊓
          sigmaCover U W ⟨l, c⟩) :=
        subsingleton_sections_of_eq_bot (sigmaCover_inf3_eq_bot_of_ne U hdisj W hij
          (inf_le_left.trans (inf_le_left.trans (sigmaCover_le U W ⟨i, a⟩)))
          (inf_le_left.trans (inf_le_right.trans (sigmaCover_le U W ⟨j, b⟩))))
      exact Subsingleton.elim _ _

omit [DecidableEq ι] in
theorem iSup_sigmaCover (hW : ∀ i, (⨆ a, W i a) = ⊤) (hcov : (⨆ i, U i) = ⊤) :
    (⨆ x, sigmaCover U W x) = ⊤ := by
  rw [iSup_sigma]
  change (⨆ i, ⨆ a, imageCover (U i) (W i) a) = ⊤
  simp only [iSup_imageCover _ _ (hW _)]
  exact hcov

/-- The class of the line bundle glued from the block cocycle. -/
def gluedClass (hg : ∀ i, IsCocycle (U i).toScheme (W i) (g i)) (hW : ∀ i, (⨆ a, W i a) = ⊤)
    (hcov : (⨆ i, U i) = ⊤) : X.Pic :=
  picardClass X (sigmaCover U W) (sigmaUnits U W g) (sigmaUnits_isCocycle U hdisj W g hg)
    (iSup_sigmaCover U W hW hcov)

omit [DecidableEq ι] in
theorem preimage_sigmaCover_le (i : ι) (a : κ i) :
    W i a ≤ (U i).ι ⁻¹ᵁ sigmaCover U W ⟨i, a⟩ :=
  (preimage_imageCover (U i) (W i) a).ge

/-- On the `i`-th block, the pulled-back and refined units are the original units. -/
theorem refinedUnits_sigma (i : ι) :
    refinedUnits (U i).toScheme (fun x => (U i).ι ⁻¹ᵁ sigmaCover U W x)
      (pullbackUnits (U i).ι (sigmaCover U W) (sigmaUnits U W g)) (W i)
      (fun a => ⟨i, a⟩) (preimage_sigmaCover_le U W i) = g i := by
  funext a b
  apply Units.ext
  rw [refinedUnits_val, pullbackUnits_val, sigmaUnits_same, transportUnits_val,
    app_openSectionsInv, res_res, res_res]
  exact res_self (U i).toScheme _ _

/-- **Restriction of the glued class to the `i`-th piece is the `i`-th class.** -/
theorem restriction_gluedClass (hg : ∀ i, IsCocycle (U i).toScheme (W i) (g i))
    (hW : ∀ i, (⨆ a, W i a) = ⊤) (hcov : (⨆ i, U i) = ⊤) (i : ι) :
    schemePicardPullbackHom (U i).ι (gluedClass U hdisj W g hg hW hcov) =
      picardClass (U i).toScheme (W i) (g i) (hg i) (hW i) := by
  have h1 : schemePicardPullbackHom (U i).ι (gluedClass U hdisj W g hg hW hcov) =
      picardClass (U i).toScheme (fun x => (U i).ι ⁻¹ᵁ sigmaCover U W x)
        (pullbackUnits (U i).ι (sigmaCover U W) (sigmaUnits U W g))
        (pullbackUnits_isCocycle (U i).ι (sigmaCover U W) (sigmaUnits U W g)
          (sigmaUnits_isCocycle U hdisj W g hg))
        (pullbackUnits_cover (U i).ι (sigmaCover U W) (iSup_sigmaCover U W hW hcov)) := by
    unfold gluedClass picardClass
    rw [schemePicardPullbackHom_toPic]
    exact pullbackGluedClass (U i).ι (sigmaCover U W) (sigmaUnits U W g)
      (sigmaUnits_isCocycle U hdisj W g hg) (iSup_sigmaCover U W hW hcov)
  have h2 := picardClass_eq_of_refinement (U i).toScheme
    (fun x => (U i).ι ⁻¹ᵁ sigmaCover U W x)
    (pullbackUnits (U i).ι (sigmaCover U W) (sigmaUnits U W g))
    (pullbackUnits_isCocycle (U i).ι (sigmaCover U W) (sigmaUnits U W g)
      (sigmaUnits_isCocycle U hdisj W g hg))
    (W i) (fun a => ⟨i, a⟩) (preimage_sigmaCover_le U W i) (hW i)
  exact h1.trans (h2.trans (picardClass_congr (W i) (refinedUnits_sigma U W g i) _ (hW i)))

end Sigma

/-! ## The Picard group of a clopen decomposition -/

section Decomposition

variable {ι : Type u} [DecidableEq ι] (U : ι → X.Opens)

/-- Restriction to the pieces. -/
def restrictionPi : X.Pic →* (∀ i, (U i).toScheme.Pic) :=
  Pi.monoidHom fun i => schemePicardPullbackHom (U i).ι

omit [DecidableEq ι] in
theorem restrictionPi_apply (c : X.Pic) (i : ι) :
    restrictionPi U c i = schemePicardPullbackHom (U i).ι c := rfl

variable (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : (⨆ i, U i) = ⊤)

omit [DecidableEq ι] in
include hcov in
theorem exists_mem_of_iSup_eq_top (x : X) : ∃ i, x ∈ U i := by
  have hx : x ∈ (⨆ i, U i : X.Opens) := by rw [hcov]; trivial
  exact (Opens.mem_iSup).mp hx

/-- The atlas of pullback charts of a module sheaf on the clopen cover. -/
def atlasOfCover (M : X.Modules)
    (t : ∀ i, (schemeModulePullback (U i).ι).obj M ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M :=
  localTrivializationsOfOpenCharts M U (exists_mem_of_iSup_eq_top U hcov)
    (fun i => openChartOfPullback M (U i) (t i))

include hdisj in
theorem atlasOfCover_isGauge (M : X.Modules)
    (t : ∀ i, (schemeModulePullback (U i).ι).obj M ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf) :
    IsGauge X U (transitionUnits X M (atlasOfCover U hcov M t)) (oneUnits X U) (fun _ => 1) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    have h := (transitionUnits_isCocycle X M (atlasOfCover U hcov M t)).unit_self i
    simp only [Units.val_one, map_one, one_mul, mul_one, oneUnits]
    exact h
  · haveI : Subsingleton Γ(X, U i ⊓ U j) := subsingleton_sections_of_eq_bot (hdisj i j hij)
    exact Subsingleton.elim _ _

/-- **A module sheaf trivial on every piece of a clopen decomposition is trivial.** -/
def unitIsoOfClopenCover (M : X.Modules)
    (t : ∀ i, (schemeModulePullback (U i).ι).obj M ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf) :
    M ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  unitIsoOfGauge (X := X) (M := M) (t := atlasOfCover U hcov M t) (fun _ => 1)
    (atlasOfCover_isGauge U hdisj hcov M t)

include hdisj hcov in
/-- **Injectivity.** -/
theorem restrictionPi_injective : Function.Injective (restrictionPi U) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨L, rfl⟩ := toPic_surjective c
  have ht : ∀ i, Nonempty ((schemeModulePullback (U i).ι).obj L.obj ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf) := fun i => by
    have h : schemePicardPullbackHom (U i).ι L.toPic = 1 := congrFun hc i
    rw [schemePicardPullbackHom_toPic, toPic_eq_one_iff_iso_unit] at h
    exact h
  exact (toPic_eq_one_iff_iso_unit L).mpr
    ⟨unitIsoOfClopenCover U hdisj hcov L.obj (fun i => (ht i).some)⟩

include hdisj hcov in
/-- **Surjectivity.** -/
theorem restrictionPi_surjective : Function.Surjective (restrictionPi U) := by
  intro c
  choose L hL using fun i => toPic_surjective (c i)
  refine ⟨gluedClass U hdisj (fun i => (L i).localTrivializations.X)
    (fun i => invertibleSheafUnits (U i).toScheme (L i))
    (fun i => invertibleSheafUnits_isCocycle (U i).toScheme (L i))
    (fun i => invertibleSheafUnits_cover (U i).toScheme (L i)) hcov, ?_⟩
  funext i
  rw [restrictionPi_apply, restriction_gluedClass, picardClass_eq_toPic_of_extraction]
  exact hL i

/-- **The Picard group of a clopen decomposition is the product of the Picard groups of the
pieces.** -/
def picardEquiv : X.Pic ≃* (∀ i, (U i).toScheme.Pic) :=
  MulEquiv.ofBijective (restrictionPi U)
    ⟨restrictionPi_injective U hdisj hcov, restrictionPi_surjective U hdisj hcov⟩

theorem picardEquiv_apply (c : X.Pic) (i : ι) :
    picardEquiv U hdisj hcov c i = schemePicardPullbackHom (U i).ι c := rfl

end Decomposition

/-! ## Two pieces -/

section Two

variable (U V : X.Opens) (hdisj : U ⊓ V = ⊥) (hcov : U ⊔ V = ⊤)

/-- The two-element cover as a `ULift Bool`-indexed family. -/
def twoCover : ULift.{u} Bool → X.Opens := PicardClopen.cover U V

include hdisj in
theorem twoCover_disjoint : ∀ i j, i ≠ j → twoCover U V i ⊓ twoCover U V j = ⊥ :=
  PicardClopen.cover_inf_eq_bot_of_ne U V hdisj

include hcov in
theorem twoCover_iSup : (⨆ i, twoCover U V i) = ⊤ := by
  apply top_unique
  rw [← hcov]
  exact sup_le (le_iSup (twoCover U V) ⟨true⟩) (le_iSup (twoCover U V) ⟨false⟩)

/-- `X.Pic ≃* U.Pic × V.Pic` for a clopen decomposition `X = U ⊔ V`. -/
def picardEquivTwo : X.Pic ≃* U.toScheme.Pic × V.toScheme.Pic :=
  (picardEquiv (twoCover U V) (twoCover_disjoint U V hdisj) (twoCover_iSup U V hcov)).trans
    { toFun := fun f => (f ⟨true⟩, f ⟨false⟩)
      invFun := fun p i => match i with
        | ⟨true⟩ => p.1
        | ⟨false⟩ => p.2
      left_inv := fun f => by
        funext i
        rcases i with ⟨_ | _⟩ <;> rfl
      right_inv := fun p => rfl
      map_mul' := fun f g => rfl }

end Two

/-- Universe check at universe `0`. -/
example {X₀ : Scheme.{0}} {ι₀ : Type} [DecidableEq ι₀] (U₀ : ι₀ → X₀.Opens)
    (hdisj : ∀ i j, i ≠ j → U₀ i ⊓ U₀ j = ⊥) (hcov : (⨆ i, U₀ i) = ⊤) :
    X₀.Pic ≃* (∀ i, (U₀ i).toScheme.Pic) :=
  picardEquiv U₀ hdisj hcov

end KltDP.Geometry.PicardClopenDecomposition
