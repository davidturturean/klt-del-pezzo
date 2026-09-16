import KltDP.Geometry.RationalTreePicardLeafChartTranspose

/-!
# The coordinate comparison on the chart/complement overlap

The transition unit of the leaf-node atlas on `U ⊓ complementOpen` is `1`: for every
open `W ≤ U ⊓ complementOpen` and section `s` of `L` over `W`, the coordinates of
`s` in the complement chart and in the affine chart agree (`hcomplT` of
`RationalTreePicardRestrictionPullbackSections`).

Both coordinates are compared inside the sections of the structure sheaf of the
closed component union `Z' = Z_{Cᶜ}` over `ι'⁻¹ᵁ W`, where the transpose of the
global frame `frameC'♯` evaluates the section. The complement side is
`componentOpenFrame_transpose` (task 6) evaluated on `s`; the chart side is
`chartUnitIsoTranspose_complement` (identification (c), task 7) evaluated on `s`,
after passing from the open subscheme `U` to `Spec Γ(X,U)` through
`leafChartTranspose_eq`. The equality transports of the pushforward comparisons are
the structure-sheaf restriction maps along the equal preimage opens, and the scheme
maps compose by `Scheme.comp_app`/`Scheme.congr_app`. Injectivity of the section maps
of the open immersions and isomorphisms involved then gives the comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

section Evaluation

variable {X Y : Scheme.{u}}

/-- The pushforward equality transport evaluates on structure-sheaf sections by the
restriction map along the equality of preimage opens. -/
theorem pushforward_eqToIso_unit_app {f g : Y ⟶ X} (e : f = g) (W : X.Opens)
    (x : ((schemeModulePushforward f).obj
      (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.obj (op W)) :
    ((eqToIso (congrArg schemeModulePushforward e)).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.app (op W) x =
      Y.presheaf.map (eqToHom (show g ⁻¹ᵁ W = f ⁻¹ᵁ W by subst e; rfl)).op x := by
  subst e
  change x = Y.presheaf.map (eqToHom _).op x
  simp

/-- Two consecutive structure-sheaf restrictions along inverse equalities of opens
compose to the identity. -/
theorem presheaf_map_eqToHom_op_eqToHom_op {A B : Y.Opens} (h₁ : A = B) (h₂ : B = A)
    (z : Γ(Y, A)) :
    Y.presheaf.map (eqToHom h₁).op (Y.presheaf.map (eqToHom h₂).op z) = z := by
  subst h₁
  simp

/-- The section map of an open immersion is injective on opens inside its range. -/
theorem openImmersion_app_injective (j : Y ⟶ X) [IsOpenImmersion j] (V : X.Opens)
    (hV : V ≤ j.opensRange) : Function.Injective (j.app V) := by
  haveI : IsIso (j.app V) := Scheme.Hom.isIso_app j V hV
  exact (asIso (j.app V)).commRingCatIsoToRingEquiv.injective

/-- The section map of an isomorphism of schemes is injective. -/
theorem isIso_app_injective (φ : Y ⟶ X) [IsIso φ] (V : X.Opens) :
    Function.Injective (φ.app V) :=
  (asIso (φ.app V)).commRingCatIsoToRingEquiv.injective

/-- The structure-sheaf restriction along an equality of opens is injective. -/
theorem presheaf_map_eqToHom_injective {A B : Y.Opens} (h : A = B) :
    Function.Injective (Y.presheaf.map (eqToHom h).op) := by
  subst h
  intro a b hab
  simpa using hab

/-- The inverse section-ring isomorphism composed with the section map is the identity. -/
theorem openSectionsInv_app' (V : X.Opens) {W : X.Opens} (hW : W ≤ V)
    (x : Γ(V.toScheme, V.ι ⁻¹ᵁ W)) :
    V.ι.app W (openSectionsInv V hW x) = x := by
  haveI : IsIso (V.ι.app W) := Scheme.Hom.isIso_app V.ι W (by simpa using hW)
  exact (asIso (V.ι.app W)).commRingCatIsoToRingEquiv.apply_symm_apply x

end Evaluation

section Overlap

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)
  {W : X.Opens} (hWU : W ≤ U.1) (hWc : W ≤ complementOpen X C) (s : L.obj.val.obj (op W))

/-- The section `s` evaluated by the transpose of the global complement frame: a
section of the structure sheaf of `Z_{Cᶜ}` over `ι'⁻¹ᵁ W`. -/
abbrev complementFrameValue :
    Γ(componentUnionScheme X ({C}ᶜ), componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W) :=
  (componentFrameTranspose X ({C}ᶜ) L frameC').val.app (op W) s

include hWc in
/-- The complement-side coordinate, read on `Z_{Cᶜ}`, is the frame value. -/
theorem complementOpen_coordinate_value :
    (componentUnionInclusion X ({C}ᶜ)).app W
        (openSectionsInv (complementOpen X C) hWc
          ((complementOpenTranspose L frameC').val.app (op W) s)) =
      complementFrameValue L frameC' s := by
  have key0 := congrArg
    (fun φ : L.obj ⟶ (schemeModulePushforward
        ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι ≫
          componentUnionInclusion X ({C}ᶜ))).obj
        (_root_.SheafOfModules.unit
          (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).toScheme.ringCatSheaf) =>
      φ.val.app (op W) s)
    (componentOpenFrame_transpose X ({C}ᶜ) (complementOpen X C) (complementOpen_subset X C) L
      frameC')
  have key : ((eqToIso (congrArg schemeModulePushforward
      (morphismRestrict_ι (componentUnionInclusion X ({C}ᶜ)) (complementOpen X C)))).hom.app
        (_root_.SheafOfModules.unit
          (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).toScheme.ringCatSheaf)).val.app
        (op W)
      ((componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C).app ((complementOpen X C).ι ⁻¹ᵁ W)
        ((complementOpenTranspose L frameC').val.app (op W) s)) =
    (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι.app
      (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W) (complementFrameValue L frameC' s) := key0
  have key' := (pushforward_eqToIso_unit_app
    (morphismRestrict_ι (componentUnionInclusion X ({C}ᶜ)) (complementOpen X C)) W
    ((componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C).app ((complementOpen X C).ι ⁻¹ᵁ W)
      ((complementOpenTranspose L frameC').val.app (op W) s))).symm.trans key
  have hVy : (complementOpen X C).ι.app W (openSectionsInv (complementOpen X C) hWc
      ((complementOpenTranspose L frameC').val.app (op W) s)) =
      (complementOpenTranspose L frameC').val.app (op W) s :=
    openSectionsInv_app' (complementOpen X C) hWc _
  apply openImmersion_app_injective (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι
    (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W)
    (by
      rw [Scheme.Opens.opensRange_ι]
      exact fun x hx => hWc hx)
  change ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι ≫
      componentUnionInclusion X ({C}ᶜ)).app W (openSectionsInv (complementOpen X C) hWc
        ((complementOpenTranspose L frameC').val.app (op W) s)) = _
  rw [Scheme.congr_app (morphismRestrict_ι (componentUnionInclusion X ({C}ᶜ))
    (complementOpen X C)).symm W]
  change (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).toScheme.presheaf.map
      (eqToHom _).op
      ((componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C).app ((complementOpen X C).ι ⁻¹ᵁ W)
        ((complementOpen X C).ι.app W (openSectionsInv (complementOpen X C) hWc
          ((complementOpenTranspose L frameC').val.app (op W) s)))) = _
  rw [hVy]
  exact key'

set_option maxHeartbeats 800000 in
include hWU in
/-- The chart transpose value corresponds, through `fromSpec`, to the affine transpose
value: `fromSpec.app W` of the chart coordinate is the affine coordinate. -/
theorem chart_fromSpec_value :
    U.2.fromSpec.app W (openSectionsInv U.1 hWU
        ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) =
      (chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s := by
  have key1 : ((eqToIso (congrArg schemeModulePushforward
      (affineOpen_ι_eq_isoSpec_fromSpec U))).hom.app
        (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf)).val.app (op W)
        ((leafChartTranspose L f h frameC frameC').val.app (op W) s) =
      U.2.isoSpec.hom.app (U.2.fromSpec ⁻¹ᵁ W)
        ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s) :=
    congrArg (fun φ => φ.val.app (op W) s) (leafChartTranspose_eq L f h frameC frameC')
  have key1' := (pushforward_eqToIso_unit_app (affineOpen_ι_eq_isoSpec_fromSpec U) W
    ((leafChartTranspose L f h frameC frameC').val.app (op W) s)).symm.trans key1
  have hUy : U.1.ι.app W (openSectionsInv U.1 hWU
      ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) =
      (leafChartTranspose L f h frameC frameC').val.app (op W) s :=
    openSectionsInv_app' U.1 hWU _
  apply isIso_app_injective U.2.isoSpec.hom (U.2.fromSpec ⁻¹ᵁ W)
  have e_b : U.1.toScheme.presheaf.map (eqToHom _).op
      ((U.2.isoSpec.hom ≫ U.2.fromSpec).app W (openSectionsInv U.1 hWU
        ((leafChartTranspose L f h frameC frameC').val.app (op W) s))) =
      U.1.ι.app W (openSectionsInv U.1 hWU
        ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) :=
    (congrArg (fun φ : Γ(X, W) ⟶ Γ(U.1.toScheme, U.1.ι ⁻¹ᵁ W) => φ (openSectionsInv U.1 hWU
      ((leafChartTranspose L f h frameC frameC').val.app (op W) s)))
      (Scheme.congr_app (affineOpen_ι_eq_isoSpec_fromSpec U) W)).symm
  have e_a := (presheaf_map_eqToHom_op_eqToHom_op
    (congrArg (fun m => m ⁻¹ᵁ W) (affineOpen_ι_eq_isoSpec_fromSpec U).symm)
    (congrArg (fun m => m ⁻¹ᵁ W) (affineOpen_ι_eq_isoSpec_fromSpec U))
    ((U.2.isoSpec.hom ≫ U.2.fromSpec).app W (openSectionsInv U.1 hWU
      ((leafChartTranspose L f h frameC frameC').val.app (op W) s)))).symm
  exact e_a.trans ((congrArg (U.1.toScheme.presheaf.map (eqToHom
    (congrArg (fun m => m ⁻¹ᵁ W) (affineOpen_ι_eq_isoSpec_fromSpec U).symm)).op) e_b).trans
    ((congrArg (U.1.toScheme.presheaf.map (eqToHom
      (congrArg (fun m => m ⁻¹ᵁ W) (affineOpen_ι_eq_isoSpec_fromSpec U).symm)).op) hUy).trans
      key1'))

set_option maxHeartbeats 800000 in
include hWU in
/-- The chart-side coordinate, read on `Z_{Cᶜ}`, is the frame value. -/
theorem chart_coordinate_value :
    (componentUnionInclusion X ({C}ᶜ)).app W
        (openSectionsInv U.1 hWU
          ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) =
      complementFrameValue L frameC' s := by
  have hfs := chart_fromSpec_value L f h frameC frameC' hWU s
  -- the affine transpose value, pushed to the complement piece, is the frame value
  have key2 : ((eqToIso (congrArg schemeModulePushforward
      (closedComponentInclusion_fromSpec X ({C}ᶜ) U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf)).val.app
        (op W)
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)).app
          (U.2.fromSpec ⁻¹ᵁ W)
          ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s)) =
      (componentUnionChartIso X ({C}ᶜ) U).hom.app
        (((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X ({C}ᶜ)) ⁻¹ᵁ W)
        ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι.app (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W)
          (complementFrameValue L frameC' s)) :=
    congrArg (fun φ => φ.val.app (op W) s) (chartUnitIsoTranspose_complement L f h frameC frameC')
  have key2' := (pushforward_eqToIso_unit_app (closedComponentInclusion_fromSpec X ({C}ᶜ) U) W
    ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)).app
      (U.2.fromSpec ⁻¹ᵁ W)
      ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s))).symm.trans key2
  -- inject through the chart identification of the complement piece
  have hinj : Function.Injective
      (((componentUnionChartIso X ({C}ᶜ) U).hom ≫
        (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι).app
        (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W)) := by
    change Function.Injective (fun z => (componentUnionChartIso X ({C}ᶜ) U).hom.app _
      ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι.app (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W) z))
    exact (isIso_app_injective (componentUnionChartIso X ({C}ᶜ) U).hom _).comp
      (openImmersion_app_injective (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι
        (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W)
        (by
          rw [Scheme.Opens.opensRange_ι]
          exact fun x hx => hWU hx))
  apply hinj
  change ((componentUnionChartIso X ({C}ᶜ) U).hom ≫
      ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X ({C}ᶜ))).app W
      (openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) = _
  rw [Scheme.congr_app (closedComponentInclusion_fromSpec X ({C}ᶜ) U).symm W]
  change (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).presheaf.map
      (eqToHom _).op
      ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)).app
        (U.2.fromSpec ⁻¹ᵁ W)
        (U.2.fromSpec.app W (openSectionsInv U.1 hWU
          ((leafChartTranspose L f h frameC frameC').val.app (op W) s)))) = _
  rw [hfs]
  exact key2'

include hWc in
/-- The section map of the complement closed immersion is injective on opens inside
the complement open (where the restricted closed immersion is an isomorphism). -/
theorem complementInclusion_app_injective :
    Function.Injective ((componentUnionInclusion X ({C}ᶜ)).app W) := by
  intro y₁ y₂ hy
  have hg := componentUnionInclusion_restrict_isIso X ({C}ᶜ) (complementOpen X C)
    (complementOpen_subset X C)
  have h1 := congrArg ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι.app
    (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ W)) hy
  change ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι ≫
      componentUnionInclusion X ({C}ᶜ)).app W y₁ =
    ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).ι ≫
      componentUnionInclusion X ({C}ᶜ)).app W y₂ at h1
  rw [Scheme.congr_app (morphismRestrict_ι (componentUnionInclusion X ({C}ᶜ))
    (complementOpen X C)).symm W] at h1
  change (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).toScheme.presheaf.map
      (eqToHom _).op
      ((componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C).app ((complementOpen X C).ι ⁻¹ᵁ W)
        ((complementOpen X C).ι.app W y₁)) =
    (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ complementOpen X C).toScheme.presheaf.map
      (eqToHom _).op
      ((componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C).app ((complementOpen X C).ι ⁻¹ᵁ W)
        ((complementOpen X C).ι.app W y₂)) at h1
  have h2 := presheaf_map_eqToHom_injective _ h1
  have h3 := isIso_app_injective (componentUnionInclusion X ({C}ᶜ) ∣_ complementOpen X C) _ h2
  exact openImmersion_app_injective (complementOpen X C).ι W (by simpa using hWc) h3

/-- The coordinate comparison on the chart/complement overlap: the two coordinates of
a section agree. This is `hcomplT`. -/
theorem complementOverlap_coordinate :
    openSectionsInv (complementOpen X C) hWc
        ((complementOpenTranspose L frameC').val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s) :=
  complementInclusion_app_injective hWc
    ((complementOpen_coordinate_value L frameC' hWc s).trans
      (chart_coordinate_value L f h frameC frameC' hWU s).symm)

end Overlap

end KltDP.Geometry.RationalTreePicard
