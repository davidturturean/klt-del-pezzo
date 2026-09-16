import KltDP.Geometry.ProjectiveLineCanonicalTransition
import KltDP.Geometry.TransitionUnitRecovery
import KltDP.Geometry.ProjectiveLineSections
import KltDP.Compatibility.InvertibleTensorUnit
import KltDP.Geometry.SchemeKaehlerOpenRestrictionComp
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.ModuleOpenRestrictionTensor
import KltDP.Geometry.ModuleOpenOver
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# `deg K_{P¹} = −2`: the overlap unit of the frames `dt`, `ds` of `Ω_{P¹}` (cast-free atlas)

A second atlas of the cotangent sheaf of `P¹` on the two standard opens, whose chart
trivialisations are composites of accepted isomorphisms that each carry a section formula:
`restrictionIso` (`restrictionIso_hom_d`), the equality of structure maps
(`baseRingCompare_d`, built here), `(restrictionIso g q).symm` (`restrictionIso_inv_d`),
`AffineKaehlerTildeLocalization.iso` (`iso_d`, `sectionD_toOpen`), the tilde functor on the pinned
`polynomialEquiv` (`map_app_toOpen`, `polynomialEquiv_D`), `unitIso` and `restrictionUnitIso`.
Consequently the chart trivialisation sends the differential of the chart coordinate to `1`
(**`chartTriv_hom_d`**): the frames of this atlas are `dt` and `ds`.

The transition exponent of `Ω_{P¹}` is the `cocycleExponent` of the transition units of this atlas
(`exponent_eq_atlasCocycleExponent`). On the overlap `Spec k[T, T⁻¹]` the coordinates `t = X₁/X₀`
and `s = X₀/X₁` (`leftFrame`, `rightFrame`, with Laurent coordinates `T` and `T⁻¹`) satisfy
`t · s = 1`, the chart trivialisations of the atlas send `dt`, `ds` to `1` (`chartTriv_hom_d` with
`ofOpenCharts_unitIso_hom_app_eq_one`, through the
frame condition `coordinate_frame_condition` computed from the pinned `Proj` chart on global
sections), and the inverse rule `ds = −s² dt` gives the overlap transition unit `−s²`
(**`atlasUnits_overlap_eq`**, from the accepted `transitionUnits_mul_chart` in the generic form
`transitionUnits_eq_of_chart`).  The two frame conditions of the atlas on the overlap are proved
here (**`atlasFrame_left`**, **`atlasFrame_right`**); the overlap unit itself, the Laurent unit
`−T⁻²`, `exponent Ω_{P¹} = −2` and `deg K_{P¹} = −2` are in
`KltDP.Geometry.ProjectiveLineCanonicalFrameUnit`.

The transport between the two (equal) structure maps `ι ≫ p` and `chartToLine ≫ lineToSpec` of a
standard open is **not** the canonical `eqToIso`: it is `baseRingCompareIso`, the same isomorphism
built from the universal property of `baseRingSheaf` (`SchemeKaehlerSheaf.desc` applied to the
universal derivation of the other structure map). Its term therefore contains no `Eq.rec` outside
the `desc` argument, and its section formula `baseRingCompare_d` is a plain rewrite rule; this is
what makes `chartTriv_hom_d` and `atlasUnits_overlap_eq` elaborate (with the `eqToIso` transport
they exhaust the budgets: `F03_RESTRICTION_ADAPTERS.md`, Task 20).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.SchemeKaehlerOpenRestriction KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.ProjectiveLineChartTriviality KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineSections KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.AffineModuleTilde KltDP.Geometry.AffineKaehlerTildeDerivation
open KltDP.Geometry.ProjectiveLineCanonical

universe u

namespace KltDP.Geometry.ProjectiveLineCanonicalFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Components of a composite isomorphism of module sheaves on sections. -/
theorem trans_hom_val_app {X : Scheme.{u}} {M N P : X.Modules} (e : M ≅ N) (e' : N ≅ P)
    (U : X.Opens) (s : M.val.obj (op U)) :
    (e ≪≫ e').hom.val.app (op U) s = e'.hom.val.app (op U) (e.hom.val.app (op U) s) := rfl

/-- Components of a restricted morphism are the original components on the image opens. -/
theorem restriction_map_app {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsOpenImmersion q]
    {M N : Z.Modules} (φ : M ⟶ N) (V : Y.Opens)
    (m : ((restriction q).obj M).val.obj (op V)) :
    ((restriction q).map φ).val.app (op V) m = φ.val.app (op (q ''ᵁ V)) m := rfl

/-! ### Comparison of differential sheaves along an equality of structure maps

The accepted `SchemeKaehlerOpenRestrictionComp.baseRingSheaf_eqToIso_hom_d` compares the
differential sheaves of two equal structure maps by `eqToIso (congrArg baseRingSheaf h)`. The
comparison below is the same isomorphism obtained from the universal property instead: `desc`
applied to the universal derivation of the second structure map, transported as data along `h`
inside the argument of `desc`. Consequently `baseRingCompare h` is an opaque `desc` application,
its section formula `baseRingCompare_d` is an ordinary rewrite rule, and no unfolding of a cast is
ever forced on a consumer. -/

section Compare

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- **The comparison of differential sheaves along an equality of structure maps**, from the
universal property of `baseRingSheaf g₁`. -/
def baseRingCompare {g₁ g₂ : X ⟶ Spec (CommRingCat.of A)} (h : g₁ = g₂) :
    baseRingSheaf g₁ ⟶ baseRingSheaf g₂ :=
  desc (scalarPresheafHom g₁) (by subst h; exact baseRingDerivation _)

/-- **The section formula**: the comparison takes `d s` to `d s`. -/
theorem baseRingCompare_d {g₁ g₂ : X ⟶ Spec (CommRingCat.of A)} (h : g₁ = g₂)
    (U : X.Opensᵒᵖ) (s : X.presheaf.obj U) :
    (baseRingCompare h).val.app U ((baseRingDerivation g₁).d s) = (baseRingDerivation g₂).d s := by
  subst h
  exact _root_.PresheafOfModules.Derivation.congr_d
    (derivation_postcomp_desc (scalarPresheafHom g₁) (baseRingDerivation g₁)) s

/-- The comparison along `rfl` is the identity. -/
theorem baseRingCompare_refl (g : X ⟶ Spec (CommRingCat.of A)) :
    baseRingCompare (rfl : g = g) = 𝟙 (baseRingSheaf g) := by
  apply hom_ext
  ext U b
  exact baseRingCompare_d (rfl : g = g) U b

theorem baseRingCompare_comp_self (g : X ⟶ Spec (CommRingCat.of A)) :
    baseRingCompare (rfl : g = g) ≫ baseRingCompare (rfl : g = g) = 𝟙 (baseRingSheaf g) := by
  rw [baseRingCompare_refl, Category.comp_id]

/-- The comparison as an isomorphism; its `hom` is the `desc` term, with no cast. -/
def baseRingCompareIso {g₁ g₂ : X ⟶ Spec (CommRingCat.of A)} (h : g₁ = g₂) :
    baseRingSheaf g₁ ≅ baseRingSheaf g₂ where
  hom := baseRingCompare h
  inv := baseRingCompare h.symm
  hom_inv_id := by subst h; exact baseRingCompare_comp_self _
  inv_hom_id := by subst h; exact baseRingCompare_comp_self _

theorem baseRingCompareIso_hom {g₁ g₂ : X ⟶ Spec (CommRingCat.of A)} (h : g₁ = g₂) :
    (baseRingCompareIso h).hom = baseRingCompare h := rfl

end Compare

variable (k : Type u) [Field k]

/-- The chart isomorphism from the standard open onto the affine line. -/
abbrev chartToLine (i : Fin 2) : (chartOpen k i).toScheme ⟶ Spec (.of (Polynomial k)) :=
  (polynomialChartOpenIso k i).inv

/-- The structure map of the affine line. -/
abbrev lineToSpec : Spec (.of (Polynomial k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

theorem ι_comp_toSpec (i : Fin 2) :
    (chartOpen k i).ι ≫ projectiveSpaceToSpec k 1 = chartToLine k i ≫ lineToSpec k := by
  rw [← polynomialChartOpenIso_inv_chartMap k i, Category.assoc, polynomialChartMap_comp_toSpec]

/-- The tilde-level trivialisation of the differential sheaf of the affine line: `dX ↦ 1`. -/
def affineTriv :
    baseRingSheaf (lineToSpec k) ≅
      _root_.SheafOfModules.unit (Spec (.of (Polynomial k))).ringCatSheaf :=
  AffineKaehlerTildeLocalization.iso k (Polynomial k) ≪≫
    linearEquivIso (M := differentialModule k (Polynomial k))
      (N := ModuleCat.of (Polynomial k) (Polynomial k)) (KaehlerDifferential.polynomialEquiv k) ≪≫
    unitIso (Polynomial k)

/-- `unitIso` sends the canonical section of `r` to the structure section of `r`. -/
theorem unitIso_hom_toOpen (V : (Spec (.of (Polynomial k))).Opens) (r : Polynomial k) :
    (unitIso (Polynomial k)).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen (ModuleCat.of (Polynomial k) (Polynomial k)) V r) =
      StructureSheaf.toOpen (Polynomial k) V r := by
  apply Subtype.ext
  funext p
  rw [unitIso_hom_app_val]
  exact unitFiberEquiv_mkLinearMap (Polynomial k) p.val r

/-- **The affine frame**: the tilde trivialisation sends `d X` to `1`. -/
theorem affineTriv_hom_d_X (V : (Spec (.of (Polynomial k))).Opens) :
    (affineTriv k).hom.val.app (op V)
        ((baseRingDerivation (lineToSpec k)).d
          (StructureSheaf.toOpen (Polynomial k) V Polynomial.X)) =
      (1 : Γ(Spec (.of (Polynomial k)), V)) := by
  have hD : (KaehlerDifferential.polynomialEquiv k)
      (KaehlerDifferential.D k (Polynomial k) Polynomial.X) = 1 := by
    rw [KaehlerDifferential.polynomialEquiv_D, Polynomial.derivative_X]
  simp only [affineTriv, trans_hom_val_app]
  rw [AffineKaehlerTildeLocalization.iso_d, sectionD_toOpen]
  change (unitIso (Polynomial k)).hom.val.app (op V)
    ((AffineModuleTilde.map (KaehlerDifferential.polynomialEquiv k).toModuleIso.hom).val.app (op V)
      (ModuleCat.Tilde.toOpen (differentialModule k (Polynomial k)) V
        (KaehlerDifferential.D k (Polynomial k) Polynomial.X))) =
    (1 : Γ(Spec (.of (Polynomial k)), V))
  rw [map_app_toOpen]
  change (unitIso (Polynomial k)).hom.val.app (op V)
    (ModuleCat.Tilde.toOpen (ModuleCat.of (Polynomial k) (Polynomial k)) V
      ((KaehlerDifferential.polynomialEquiv k)
        (KaehlerDifferential.D k (Polynomial k) Polynomial.X))) =
    (1 : Γ(Spec (.of (Polynomial k)), V))
  rw [hD, unitIso_hom_toOpen]
  exact map_one (ConcreteCategory.hom (StructureSheaf.toOpen (Polynomial k) V))

/-- The restricted unit isomorphism is the section-ring isomorphism of the open immersion. -/
theorem restrictionUnitIso_hom_apply {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsOpenImmersion q]
    (V : Y.Opens) (x : ((restriction q).obj (_root_.SheafOfModules.unit Z.ringCatSheaf)).val.obj (op V)) :
    (restrictionUnitIso q).hom.val.app (op V) x = (q.appIso V).hom x := rfl

theorem restrictionUnitIso_hom_one {Y Z : Scheme.{u}} (q : Y ⟶ Z) [IsOpenImmersion q] (V : Y.Opens) :
    (restrictionUnitIso q).hom.val.app (op V) (1 : Γ(Z, q ''ᵁ V)) = (1 : Γ(Y, V)) := by
  rw [restrictionUnitIso_hom_apply]
  exact map_one (ConcreteCategory.hom (q.appIso V).hom)

/-- The affine-line trivialisation transported to the standard open along the chart. -/
def lineTriv (i : Fin 2) :
    (restriction (chartToLine k i)).obj (baseRingSheaf (lineToSpec k)) ≅
      _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf :=
  (restriction (chartToLine k i)).mapIso (affineTriv k) ≪≫ restrictionUnitIso (chartToLine k i)

/-- The same, on the differential sheaf of the composite structure map. -/
def lineTriv' (i : Fin 2) :
    baseRingSheaf (chartToLine k i ≫ lineToSpec k) ≅
      _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf :=
  (restrictionIso (lineToSpec k) (chartToLine k i)).symm ≪≫ lineTriv k i

/-- The chart trivialisation of `Ω_{P¹}` on a standard open, through the affine line. The middle
factor is the cast-free comparison of the two (equal) structure maps of the open subscheme. -/
def chartTriv (i : Fin 2) :
    (restriction (chartOpen k i).ι).obj (cotangent k) ≅
      _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf :=
  restrictionIso (projectiveSpaceToSpec k 1) (chartOpen k i).ι ≪≫
    baseRingCompareIso (ι_comp_toSpec k i) ≪≫ lineTriv' k i

-- The steps below unfold the chart trivialisation on the differential of a section, one
-- accepted component at a time (separate declarations, so that each kernel check is small).
theorem lineTriv_hom_d (i : Fin 2) (V : (chartOpen k i).toScheme.Opens)
    (y : Γ(Spec (.of (Polynomial k)), chartToLine k i ''ᵁ V)) :
    (lineTriv k i).hom.val.app (op V) ((baseRingDerivation (lineToSpec k)).d y) =
      (restrictionUnitIso (chartToLine k i)).hom.val.app (op V)
        ((affineTriv k).hom.val.app (op (chartToLine k i ''ᵁ V))
          ((baseRingDerivation (lineToSpec k)).d y)) := by
  rw [lineTriv, trans_hom_val_app, Functor.mapIso_hom, restriction_map_app]
  rfl

theorem lineTriv'_hom_d (i : Fin 2) (V : (chartOpen k i).toScheme.Opens)
    (y : Γ((chartOpen k i).toScheme, V)) :
    (lineTriv' k i).hom.val.app (op V) ((baseRingDerivation (chartToLine k i ≫ lineToSpec k)).d y) =
      (lineTriv k i).hom.val.app (op V)
        ((baseRingDerivation (lineToSpec k)).d (((chartToLine k i).appIso V).inv y)) := by
  rw [lineTriv', trans_hom_val_app, Iso.symm_hom, restrictionIso_inv_d]
  rfl

/-- **The transport step, with no cast in the term**: the comparison of the two structure maps of
the standard open takes `d y` to `d y`. -/
theorem compare_lineTriv'_hom_d (i : Fin 2) (V : (chartOpen k i).toScheme.Opens)
    (y : Γ((chartOpen k i).toScheme, V)) :
    (baseRingCompareIso (ι_comp_toSpec k i) ≪≫ lineTriv' k i).hom.val.app (op V)
        ((baseRingDerivation ((chartOpen k i).ι ≫ projectiveSpaceToSpec k 1)).d y) =
      (lineTriv' k i).hom.val.app (op V)
        ((baseRingDerivation (chartToLine k i ≫ lineToSpec k)).d y) := by
  rw [trans_hom_val_app, baseRingCompareIso_hom, baseRingCompare_d]

theorem chartTriv_hom_d_restrictionIso (i : Fin 2) (V : (chartOpen k i).toScheme.Opens)
    (τ : Γ(projectiveSpace k 1, (chartOpen k i).ι ''ᵁ V)) :
    (chartTriv k i).hom.val.app (op V) ((baseRingDerivation (projectiveSpaceToSpec k 1)).d τ) =
      (baseRingCompareIso (ι_comp_toSpec k i) ≪≫ lineTriv' k i).hom.val.app (op V)
        ((baseRingDerivation ((chartOpen k i).ι ≫ projectiveSpaceToSpec k 1)).d
          (((chartOpen k i).ι.appIso V).hom τ)) := by
  rw [chartTriv, trans_hom_val_app, restrictionIso_hom_d]

-- Heartbeats raised as in the accepted `SchemeKaehlerOpenRestrictionComp` (`adjointComparison_d`):
-- the chart trivialisation is a three-fold composite of module-sheaf isomorphisms.
set_option maxHeartbeats 4000000 in
/-- **The chart frame is `d(coordinate)`**: the chart trivialisation sends the differential of
any section that the chart identifies with the affine coordinate `X` to `1`. -/
theorem chartTriv_hom_d (i : Fin 2) (V : (chartOpen k i).toScheme.Opens)
    (τ : Γ(projectiveSpace k 1, (chartOpen k i).ι ''ᵁ V))
    (hτ : ((chartToLine k i).appIso V).inv (((chartOpen k i).ι.appIso V).hom τ) =
      StructureSheaf.toOpen (Polynomial k) (chartToLine k i ''ᵁ V) Polynomial.X) :
    (chartTriv k i).hom.val.app (op V)
      ((baseRingDerivation (projectiveSpaceToSpec k 1)).d τ) =
        (1 : Γ((chartOpen k i).toScheme, V)) := by
  rw [chartTriv_hom_d_restrictionIso, compare_lineTriv'_hom_d, lineTriv'_hom_d, hτ, lineTriv_hom_d,
    affineTriv_hom_d_X, restrictionUnitIso_hom_one]

/-- The two standard opens cover `P¹`. -/
theorem chartOpen_cover (x : projectiveSpace k 1) : ∃ i : ULift.{u} (Fin 2), x ∈ chartOpen k i.down := by
  have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  change x ∈ chartOpen k 0 ∨ x ∈ chartOpen k 1 at hx
  rcases hx with hx | hx
  · exact ⟨⟨0⟩, hx⟩
  · exact ⟨⟨1⟩, hx⟩

/-- The frame atlas of `Ω_{P¹}` on the two standard opens. -/
abbrev frameAtlas :
    KltDP.SheafOfModules.LocalTrivializations (R := (projectiveSpace k 1).ringCatSheaf)
      (cotangent k) :=
  localTrivializationsOfOpenCharts (cotangent k)
    (fun i : ULift.{u} (Fin 2) => chartOpen k i.down) (chartOpen_cover k)
    (fun i => (chartTriv k i.down).symm)

/-- The transition units of the frame atlas. -/
abbrev atlasUnits :
    ∀ i j : ULift.{u} (Fin 2),
      Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
  TransitionUnitExtraction.transitionUnits (projectiveSpace k 1) (cotangent k) (frameAtlas k)

theorem exponent_eq_atlasCocycleExponent :
    exponent k (canonicalSheaf k) = cocycleExponent k (atlasUnits k) :=
  exponent_eq_of_iso_to_glued k (canonicalSheaf k) (atlasUnits k)
    (TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1) (cotangent k)
      (frameAtlas k))
    (TransitionUnitExtraction.recoveryIso (projectiveSpace k 1) (cotangent k) (frameAtlas k))

theorem exponent_eq_atlasOverlapExponent :
    exponent k (canonicalSheaf k) =
      overlapExponent k (overlapRestriction k (atlasUnits k ⟨0⟩ ⟨1⟩)) := by
  rw [exponent_eq_atlasCocycleExponent, cocycleExponent]

theorem frameAtlas_unitIso_hom (i : ULift.{u} (Fin 2)) :
    ((frameAtlas k).unitIso i).hom =
      (openChartToOverUnitIso (standardOpens k i) (cotangent k) (chartTriv k i.down).symm).inv := by
  simp only [frameAtlas, KltDP.SheafOfModules.LocalTrivializations.unitIso,
    localTrivializationsOfOpenCharts, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Section formulas on the over site -/

/-- Evaluating an inverse open frame on the over site: the accepted
`OpenFrameTransitionCoefficient.openChartToOverUnitIso_inv_app`, restated (it is private there). -/
theorem overUnitIso_inv_app {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (W : X.Opens) (hW : W ≤ U) (s : M.val.obj (op W)) :
    (U.ι.app W)
        ((openChartToOverUnitIso U M e).inv.val.app (op (Over.mk (homOfLE hW))) s) =
      e.inv.val.app (op (U.ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset U.ι.base (W : Set X))).op s) := by
  letI : IsIso (U.ι.app W) := Scheme.Hom.isIso_app U.ι W (by simpa using hW)
  change (asIso (U.ι.app W)).hom
      ((asIso (U.ι.app W)).inv
        (e.inv.val.app (op (U.ι ⁻¹ᵁ W))
          (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
            (Set.image_preimage_subset U.ι.base (W : Set X))).op s))) = _
  exact Iso.inv_hom_id_apply _ _

/-- Sections over an open `W ≤ U` are determined by their images in the open subscheme `U`. -/
theorem ι_app_injective {X : Scheme.{u}} (U W : X.Opens) (hW : W ≤ U) {a b : Γ(X, W)}
    (h : U.ι.app W a = U.ι.app W b) : a = b := by
  letI : IsIso (U.ι.app W) := Scheme.Hom.isIso_app U.ι W (by simpa using hW)
  have h' := congrArg (fun x => (asIso (U.ι.app W)).inv x) h
  change (asIso (U.ι.app W)).inv ((asIso (U.ι.app W)).hom a) =
    (asIso (U.ι.app W)).inv ((asIso (U.ι.app W)).hom b) at h'
  rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h'

/-! ### `appLE` bookkeeping on sections -/

/-- Equal ring morphisms agree on elements (with the concrete-category coercion). -/
theorem hom_congr_apply {R S : CommRingCat.{u}} {f g : R ⟶ S} (h : f = g) (x : R) : f x = g x := by
  rw [h]

theorem appLE_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (x : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE h).op x) =
      f.appLE U' V (e.trans (f.preimage_le_preimage_of_le h)) x := by
  have := hom_congr_apply (f.map_appLE e (homOfLE h).op) x
  rw [ConcreteCategory.comp_apply] at this
  exact this

theorem map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' (h.trans e) x := by
  have := hom_congr_apply (f.appLE_map e (homOfLE h).op) x
  rw [ConcreteCategory.comp_apply] at this
  exact this

/-- `appLE` along equal morphisms. -/
theorem appLE_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V e = f.appLE U V (by rw [h]; exact e) := by
  subst h
  rfl

/-! ### The chart of a basic open of `Proj` on global sections -/

section Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

/-- The chart immersion of a basic open on its sections: the accepted
`FrobeniusProjectiveCoordinatePicard.overlap_appLE_eq` for a general basic open. -/
theorem awayι_appLE_eq (h : ⊤ ≤ Proj.awayι 𝒜 f f_deg hm ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    (Proj.awayι 𝒜 f f_deg hm).appLE (Proj.basicOpen 𝒜 f) ⊤ h =
      (Proj.basicOpen 𝒜 f).topIso.inv ≫ (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop := by
  have H := Scheme.appLE_comp_appLE (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv
    (Proj.basicOpen 𝒜 f).ι (Proj.basicOpen 𝒜 f) ⊤ ⊤
    (Proj.basicOpen 𝒜 f).ι_preimage_self.ge le_rfl
  show ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι).appLE
    (Proj.basicOpen 𝒜 f) ⊤ h = _
  simpa only [Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv,
    eqToHom_op] using H.symm

/-- Homogeneous sections followed by the chart immersion on global sections are the Gamma–Spec
identification: the accepted `FrobeniusProjectiveCoordinatePicard.awayToSection_overlap_appLE`
for a general basic open. -/
theorem awayToSection_awayι_appLE (h : ⊤ ≤ Proj.awayι 𝒜 f f_deg hm ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    Proj.awayToSection 𝒜 f ≫ (Proj.awayι 𝒜 f f_deg hm).appLE (Proj.basicOpen 𝒜 f) ⊤ h =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv := by
  have hc : Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv ≫
        (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop := by
    rw [Proj.basicOpenIsoSpec_hom, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top,
      Iso.inv_hom_id_assoc]
    try rfl
  rw [awayι_appLE_eq, ← Category.assoc, hc, Category.assoc, ← Scheme.comp_appTop,
    Iso.inv_hom_id, Scheme.id_appTop, Category.comp_id]

end Proj

/-! ### The polynomial chart on global sections -/

theorem chartImmersion_preimage_top (i : Fin 2) :
    ⊤ ≤ chartImmersion k i ⁻¹ᵁ chartOpen k i := by
  intro x _
  rw [← chartImmersion_opensRange k i]
  exact Set.mem_range_self x

theorem polynomialChartMap_preimage_top (i : Fin 2) :
    ⊤ ≤ polynomialChartMap k i ⁻¹ᵁ chartOpen k i := by
  intro x _
  rw [← polynomialChartMap_opensRange k i]
  exact Set.mem_range_self x

/-- **The chart coordinate on global sections**: a homogeneous chart section with polynomial
coordinate `X` is pulled back by the polynomial chart to `X` in `Γ(Spec k[X], ⊤)`. -/
theorem polynomialChartMap_appLE_coordinate (i : Fin 2) (q : chartRing k i)
    (hq : chartPolynomialEquiv k i q = Polynomial.X)
    (h : ⊤ ≤ polynomialChartMap k i ⁻¹ᵁ chartOpen k i) :
    (polynomialChartMap k i).appLE (chartOpen k i) ⊤ h
        ((Proj.awayToSection (grading k) (MvPolynomial.X i)).hom q) =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X := by
  have hC : (polynomialChartMap k i).appLE (chartOpen k i) ⊤ h =
      (chartImmersion k i).appLE (chartOpen k i) ⊤ (chartImmersion_preimage_top k i) ≫
        (chartPolynomialIso k i).inv.appTop := by
    have H := Scheme.appLE_comp_appLE (chartPolynomialIso k i).inv (chartImmersion k i)
      (chartOpen k i) ⊤ ⊤ (chartImmersion_preimage_top k i) le_rfl
    simpa only [Scheme.Hom.appLE_eq_app] using H.symm
  have hA : Proj.awayToSection (grading k) (MvPolynomial.X i) ≫
      (chartImmersion k i).appLE (chartOpen k i) ⊤ (chartImmersion_preimage_top k i) =
        (Scheme.ΓSpecIso (CommRingCat.of (chartRing k i))).inv :=
    awayToSection_awayι_appLE (grading k) (f := MvPolynomial.X i) (m := 1)
      (MvPolynomial.isHomogeneous_X k i) (by decide) (chartImmersion_preimage_top k i)
  have hB := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom)
  have hM : Proj.awayToSection (grading k) (MvPolynomial.X i) ≫
      (polynomialChartMap k i).appLE (chartOpen k i) ⊤ h =
        CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv := by
    rw [hC, ← Category.assoc, hA, hB]
    rfl
  have hq' := hom_congr_apply hM q
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hq'
  exact hq'.trans
    (congrArg (fun r : Polynomial k => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv r) hq)

/-- **The frame condition for a coordinate**: the chart identifies the restriction to the overlap
of a homogeneous section with polynomial coordinate `X` with the affine coordinate `X`. -/
theorem coordinate_frame_condition (i : Fin 2) (q : chartRing k i)
    (hq : chartPolynomialEquiv k i q = Polynomial.X) (hW : overlapOpen k ≤ chartOpen k i) :
    ((chartToLine k i).appIso ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k)).inv
        (((chartOpen k i).ι.appIso ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k)).hom
          ((projectiveSpace k 1).presheaf.map
            (homOfLE (x := (chartOpen k i).ι ''ᵁ (chartOpen k i).ι ⁻¹ᵁ overlapOpen k)
              (y := overlapOpen k)
              (Set.image_preimage_subset (chartOpen k i).ι.base
                (overlapOpen k : Set (projectiveSpace k 1)))).op
            ((projectiveSpace k 1).presheaf.map (homOfLE hW).op
              ((Proj.awayToSection (grading k) (MvPolynomial.X i)).hom q)))) =
      StructureSheaf.toOpen (Polynomial k)
        (chartToLine k i ''ᵁ ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k)) Polynomial.X := by
  have hpre := polynomialChartMap_preimage_top k i
  rw [Scheme.Hom.appIso_hom', appLE_map_apply, appLE_map_apply,
    appLE_of_eq (polynomialChartOpenIso_inv_chartMap k i),
    ← Scheme.appLE_comp_appLE (chartToLine k i) (polynomialChartMap k i) (chartOpen k i)
      (chartToLine k i ''ᵁ ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k))
      ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k) (le_top.trans hpre)
      ((chartToLine k i).preimage_image_eq _).ge,
    ConcreteCategory.comp_apply, ← Scheme.Hom.appIso_hom', Iso.hom_inv_id_apply,
    ← map_appLE_apply (polynomialChartMap k i) hpre le_top,
    polynomialChartMap_appLE_coordinate k i q hq]
  exact (hom_congr_apply (Scheme.toOpen_eq (CommRingCat.of (Polynomial k))
    (chartToLine k i ''ᵁ ((chartOpen k i).ι ⁻¹ᵁ overlapOpen k))) Polynomial.X).symm

/-! ### The coordinates `t = X₁/X₀`, `s = X₀/X₁` and their restrictions to the overlap -/

/-- The coordinate `t = X₁/X₀` on the chart `X₀ ≠ 0`. -/
def leftCoordinate : Γ(projectiveSpace k 1, chartOpen k 0) :=
  (Proj.awayToSection (grading k) (MvPolynomial.X 0)).hom
    ((firstChartPolynomialEquiv k).symm Polynomial.X)

/-- The coordinate `s = X₀/X₁` on the chart `X₁ ≠ 0`. -/
def rightCoordinate : Γ(projectiveSpace k 1, chartOpen k 1) :=
  (Proj.awayToSection (grading k) (MvPolynomial.X 1)).hom
    ((secondChartPolynomialEquiv k).symm Polynomial.X)

theorem leftSectionsEquiv_leftCoordinate :
    leftSectionsEquiv k (leftCoordinate k) = Polynomial.X := by
  rw [leftCoordinate, leftSectionsEquiv_awayToSection, RingEquiv.apply_symm_apply]

theorem rightSectionsEquiv_rightCoordinate :
    rightSectionsEquiv k (rightCoordinate k) = Polynomial.X := by
  rw [rightCoordinate, rightSectionsEquiv_awayToSection, RingEquiv.apply_symm_apply]

/-- `t` restricted to the overlap. -/
def leftFrame : Γ(projectiveSpace k 1, overlapOpen k) :=
  (projectiveSpace k 1).presheaf.map (homOfLE (overlapOpen_le_left k)).op (leftCoordinate k)

/-- `s` restricted to the overlap. -/
def rightFrame : Γ(projectiveSpace k 1, overlapOpen k) :=
  (projectiveSpace k 1).presheaf.map (homOfLE (overlapOpen_le_right k)).op (rightCoordinate k)

theorem overlapSectionsEquiv_leftFrame :
    overlapSectionsEquiv k (leftFrame k) = LaurentPolynomial.T 1 := by
  change overlapSectionsEquiv k (restrictLeft k (leftCoordinate k)) = _
  rw [overlapSectionsEquiv_restrictLeft, leftSectionsEquiv_leftCoordinate, Polynomial.toLaurent_X]

theorem overlapSectionsEquiv_rightFrame :
    overlapSectionsEquiv k (rightFrame k) = LaurentPolynomial.T (-1) := by
  change overlapSectionsEquiv k (restrictRight k (rightCoordinate k)) = _
  rw [overlapSectionsEquiv_restrictRight, rightSectionsEquiv_rightCoordinate, Polynomial.aeval_X]

/-- `t · s = 1` on the overlap. -/
theorem leftFrame_mul_rightFrame : leftFrame k * rightFrame k = 1 := by
  apply (overlapSectionsEquiv k).injective
  rw [map_mul, map_one, overlapSectionsEquiv_leftFrame, overlapSectionsEquiv_rightFrame,
    ← LaurentPolynomial.T_add]
  norm_num [LaurentPolynomial.T_zero]

/-! ### The frames of the atlas: `dt ↦ 1`, `ds ↦ 1` -/

section Generic

variable {X : Scheme.{u}} (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- **The transition unit from the frames** (accepted `transitionUnits_mul_chart`): if the chart
coordinates send `s ↦ 1` (chart `j`) and `s' ↦ 1` (chart `i`) and `s = −(r • s')`, then the
transition unit `i j` on `W` is `−r`. Stated generically so that the linear structure of
`chartEquiv` is the one of its (generic) signature. -/
theorem transitionUnits_eq_of_chart (i j : t.I) {W : X.Opens} (hWi : W ≤ t.X i) (hWj : W ≤ t.X j)
    (s s' : M.val.obj (op W)) (r : Γ(X, W))
    (hj : TransitionUnitExtraction.chartEquiv X M t j hWj s = 1)
    (hi : TransitionUnitExtraction.chartEquiv X M t i hWi s' = 1) (hs : s = -(r • s')) :
    TransitionUnitGluing.res X (le_inf hWi hWj)
      (TransitionUnitExtraction.transitionUnits X M t i j) = -r := by
  have h := TransitionUnitExtraction.transitionUnits_mul_chart X M t i j hWi hWj s
  rw [hj, mul_one, hs, map_neg, LinearEquiv.map_smul, hi, smul_eq_mul, mul_one] at h
  exact h

end Generic

theorem chartPolynomialEquiv_zero : chartPolynomialEquiv k 0 = firstChartPolynomialEquiv k := rfl

theorem chartPolynomialEquiv_one : chartPolynomialEquiv k 1 = secondChartPolynomialEquiv k := rfl

theorem chartPolynomialEquiv_zero_symm_X :
    chartPolynomialEquiv k 0 ((firstChartPolynomialEquiv k).symm Polynomial.X) = Polynomial.X := by
  rw [chartPolynomialEquiv_zero, RingEquiv.apply_symm_apply]

theorem chartPolynomialEquiv_one_symm_X :
    chartPolynomialEquiv k 1 ((secondChartPolynomialEquiv k).symm Polynomial.X) = Polynomial.X := by
  rw [chartPolynomialEquiv_one, RingEquiv.apply_symm_apply]

/-- The frame condition for `t` on the overlap (chart 0). -/
theorem leftFrame_condition :
    ((chartToLine k 0).appIso ((chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)).inv
        (((chartOpen k 0).ι.appIso ((chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)).hom
          ((projectiveSpace k 1).presheaf.map
            (homOfLE (x := (chartOpen k 0).ι ''ᵁ (chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)
              (y := overlapOpen k)
              (Set.image_preimage_subset (chartOpen k 0).ι.base
                (overlapOpen k : Set (projectiveSpace k 1)))).op (leftFrame k))) =
      StructureSheaf.toOpen (Polynomial k)
        (chartToLine k 0 ''ᵁ ((chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)) Polynomial.X :=
  coordinate_frame_condition k 0 ((firstChartPolynomialEquiv k).symm Polynomial.X)
    (chartPolynomialEquiv_zero_symm_X k) (overlapOpen_le_left k)

/-- The frame condition for `s` on the overlap (chart 1). -/
theorem rightFrame_condition :
    ((chartToLine k 1).appIso ((chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)).inv
        (((chartOpen k 1).ι.appIso ((chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)).hom
          ((projectiveSpace k 1).presheaf.map
            (homOfLE (x := (chartOpen k 1).ι ''ᵁ (chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)
              (y := overlapOpen k)
              (Set.image_preimage_subset (chartOpen k 1).ι.base
                (overlapOpen k : Set (projectiveSpace k 1)))).op (rightFrame k))) =
      StructureSheaf.toOpen (Polynomial k)
        (chartToLine k 1 ''ᵁ ((chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)) Polynomial.X :=
  coordinate_frame_condition k 1 ((secondChartPolynomialEquiv k).symm Polynomial.X)
    (chartPolynomialEquiv_one_symm_X k) (overlapOpen_le_right k)

/-- The over-site unit isomorphism of an open-chart atlas is the chart trivialisation
(the accepted `originalAtlas_unitIso_hom`, generically). -/
theorem ofOpenCharts_unitIso_hom {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ x : X, ∃ i, x ∈ V i)
    (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ (restriction (V i).ι).obj M)
    (i : ι) :
    ((localTrivializationsOfOpenCharts M V hV e).unitIso i).hom =
      (openChartToOverUnitIso (V i) M (e i)).inv := by
  simp only [KltDP.SheafOfModules.LocalTrivializations.unitIso, localTrivializationsOfOpenCharts,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Frames of an open-chart atlas**: if the chart trivialisation sends the restriction of a
section `s` to `1`, so does the over-site unit isomorphism of the atlas on `s`. -/
theorem ofOpenCharts_unitIso_hom_app_eq_one {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ (restriction (V i).ι).obj M)
    (i : ι) {W : X.Opens} (hW : W ≤ V i) (s : M.val.obj (op W))
    (h : (e i).inv.val.app (op ((V i).ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := (V i).ι ''ᵁ (V i).ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset (V i).ι.base (W : Set X))).op s) =
        (1 : Γ((V i).toScheme, (V i).ι ⁻¹ᵁ W))) :
    ((localTrivializationsOfOpenCharts M V hV e).unitIso i).hom.val.app
        (op (Over.mk (homOfLE hW))) s = (1 : Γ(X, W)) := by
  have h1 := congrArg (fun φ => φ.val.app (op (Over.mk (homOfLE hW))) s)
    (ofOpenCharts_unitIso_hom M V hV e i)
  refine h1.trans ?_
  beta_reduce
  apply ι_app_injective (V i) W hW
  refine (overUnitIso_inv_app (V i) M (e i) W hW s).trans ?_
  rw [h, map_one]

/-- **The transition unit of an open-chart atlas from its frames**: the two frame conditions at
the chart level and `s = −(r • s')` give the transition unit `−r` (generic; the instantiation at
`P¹` is `atlasUnits_overlap_eq`). -/
theorem transitionUnits_eq_of_ofOpenCharts {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
    (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ (restriction (V i).ι).obj M)
    (i j : ι) {W : X.Opens} (hWi : W ≤ (localTrivializationsOfOpenCharts M V hV e).X i)
    (hWj : W ≤ (localTrivializationsOfOpenCharts M V hV e).X j) (s s' : M.val.obj (op W))
    (r : Γ(X, W))
    (hj : (e j).inv.val.app (op ((V j).ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := (V j).ι ''ᵁ (V j).ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset (V j).ι.base (W : Set X))).op s) =
        (1 : Γ((V j).toScheme, (V j).ι ⁻¹ᵁ W)))
    (hi : (e i).inv.val.app (op ((V i).ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := (V i).ι ''ᵁ (V i).ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset (V i).ι.base (W : Set X))).op s') =
        (1 : Γ((V i).toScheme, (V i).ι ⁻¹ᵁ W)))
    (hs : s = -(r • s')) :
    TransitionUnitGluing.res X (le_inf hWi hWj)
      (TransitionUnitExtraction.transitionUnits X M (localTrivializationsOfOpenCharts M V hV e) i j) =
        -r :=
  transitionUnits_eq_of_chart M (localTrivializationsOfOpenCharts M V hV e) i j hWi hWj s s' r
    ((TransitionUnitExtraction.chartEquiv_apply X M (localTrivializationsOfOpenCharts M V hV e) j
      hWj s).trans (ofOpenCharts_unitIso_hom_app_eq_one M V hV e j hWj s hj))
    ((TransitionUnitExtraction.chartEquiv_apply X M (localTrivializationsOfOpenCharts M V hV e) i
      hWi s').trans (ofOpenCharts_unitIso_hom_app_eq_one M V hV e i hWi s' hi)) hs

/-! ### The overlap transition unit and the degree -/

theorem overlapRestriction_val (u : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)ˣ) :
    (overlapRestriction k u : Γ(projectiveSpace k 1, overlapOpen k)) =
      TransitionUnitGluing.res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
        (u : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)) := rfl

-- Heartbeats raised as in the accepted `SchemeKaehlerOpenRestrictionComp` (`adjointComparison_d`):
-- the frame condition of a chart is read through the chart trivialisation of the atlas.  The two
-- frame hypotheses of the generic atlas lemma are separate declarations, so that each of them is
-- elaborated and kernel-checked on its own budget.
set_option maxHeartbeats 4000000 in
/-- The chart-`1` trivialisation of the frame atlas sends `d s` to `1` on the overlap. -/
theorem atlasFrame_right :
    (chartTriv k 1).symm.inv.val.app (op ((chartOpen k 1).ι ⁻¹ᵁ overlapOpen k))
        ((cotangent k).val.map
          (homOfLE (x := (chartOpen k 1).ι ''ᵁ (chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)
            (y := overlapOpen k)
            (Set.image_preimage_subset (chartOpen k 1).ι.base
              (overlapOpen k : Set (projectiveSpace k 1)))).op
          ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (rightFrame k))) =
      (1 : Γ((chartOpen k 1).toScheme, (chartOpen k 1).ι ⁻¹ᵁ overlapOpen k)) := by
  rw [Iso.symm_inv, ← derivation_restrict]
  exact chartTriv_hom_d k 1 _ _ (rightFrame_condition k)

set_option maxHeartbeats 4000000 in
/-- The chart-`0` trivialisation of the frame atlas sends `d t` to `1` on the overlap. -/
theorem atlasFrame_left :
    (chartTriv k 0).symm.inv.val.app (op ((chartOpen k 0).ι ⁻¹ᵁ overlapOpen k))
        ((cotangent k).val.map
          (homOfLE (x := (chartOpen k 0).ι ''ᵁ (chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)
            (y := overlapOpen k)
            (Set.image_preimage_subset (chartOpen k 0).ι.base
              (overlapOpen k : Set (projectiveSpace k 1)))).op
          ((baseRingDerivation (projectiveSpaceToSpec k 1)).d (leftFrame k))) =
      (1 : Γ((chartOpen k 0).toScheme, (chartOpen k 0).ι ⁻¹ᵁ overlapOpen k)) := by
  rw [Iso.symm_inv, ← derivation_restrict]
  exact chartTriv_hom_d k 0 _ _ (leftFrame_condition k)

end KltDP.Geometry.ProjectiveLineCanonicalFrame
