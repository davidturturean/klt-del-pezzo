import KltDP.Geometry.SchemeKaehlerSheaf
import KltDP.Geometry.ModuleOpenRestrictionTensor
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Actual open restriction of the global differential sheaf

For an original open immersion `j : Y ⟶ X`, transport the original
differential derivation through `j.appIso.inv` on every open. The scalar
compatibility is proved for the original `scalarPresheafHom` of `f` and
`j ≫ f`; no replacement base map is chosen.

The resulting presheaf comparison is bijective on every open. Indeed,
the original section-ring isomorphism is localization at one, and the
pinned differential-localization theorem applies to that exact map.
Restriction preserves local bijectivity of the original sheafification
unit. Its factorization then proves that the actual differential sheaf
comparison is an isomorphism, retaining its action on every derivative.

This is an open-restriction adapter for the original global construction.
It assumes no smoothness, local frame, duality, or canonical-divisor data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerOpenRestriction

open SchemeKaehlerSheaf SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]

/-- The original scalar maps agree through the original inverse
section-ring isomorphism of the open immersion. -/
theorem scalar_appIso_inv (U : Y.Opens) :
    (scalarPresheafHom (j ≫ f)).app (op U) ≫ (j.appIso U).inv =
      (scalarPresheafHom f).app (op (j ''ᵁ U)) := by
  have h : j.appTop ≫ Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      (j.appIso U).inv =
      X.presheaf.map (homOfLE (le_top : j ''ᵁ U ≤ ⊤)).op := by
    simpa only [Scheme.Hom.appLE, Category.assoc] using
      (Scheme.Hom.appLE_appIso_inv j (show U ≤ j ⁻¹ᵁ ⊤ from le_top))
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (j ≫ f).appTop ≫
    Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ≫ (j.appIso U).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.presheaf.map (homOfLE (le_top : j ''ᵁ U ≤ ⊤)).op
  rw [Scheme.comp_appTop]
  simpa only [Category.assoc] using congrArg
    (fun g : Γ(X, ⊤) ⟶ Γ(X, j ''ᵁ U) =>
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ g) h

/-- The original differential presheaf restricted by the actual open
immersion functor and its original section-ring map. -/
abbrev restrictedPresheaf : Y.PresheafOfModules :=
  (_root_.PresheafOfModules.pushforward (restrictionRingHom j)).obj
    (presheaf (scalarPresheafHom f))

/-- Transport the actual presheaf derivation through the inverse
section-ring isomorphism; the transported module action is the original
action used by `restriction`. -/
def restrictedPresheafDerivation :
    (restrictedPresheaf f j).Derivation' (scalarPresheafHom (j ≫ f)) where
  d {U} :=
    (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
      (scalarPresheafHom f)).d.comp (j.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
      (scalarPresheafHom f)).d ((j.appIso U.unop).inv (a * b)) =
      (j.appIso U.unop).inv a •
        (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
          (scalarPresheafHom f)).d ((j.appIso U.unop).inv b) +
      (j.appIso U.unop).inv b •
        (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
          (scalarPresheafHom f)).d ((j.appIso U.unop).inv a)
    rw [map_mul]
    exact (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
      (scalarPresheafHom f)).d_mul _ _
  d_map {U V} i s := by
    have h := ConcreteCategory.congr_hom (j.appIso_inv_naturality i) s
    change (j.appIso V.unop).inv (Y.presheaf.map i s) =
      X.presheaf.map (j.opensFunctor.op.map i) ((j.appIso U.unop).inv s) at h
    change (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
        (scalarPresheafHom f)).d ((j.appIso V.unop).inv (Y.presheaf.map i s)) =
      (presheaf (scalarPresheafHom f)).map (j.opensFunctor.op.map i)
        ((_root_.PresheafOfModules.DifferentialsConstruction.derivation'
          (scalarPresheafHom f)).d ((j.appIso U.unop).inv s))
    rw [h]
    exact (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
      (scalarPresheafHom f)).d_map _ _
  d_app {U} a := by
    have h := ConcreteCategory.congr_hom (scalar_appIso_inv f j U.unop) a
    change (j.appIso U.unop).inv ((scalarPresheafHom (j ≫ f)).app U a) =
      (scalarPresheafHom f).app (op (j ''ᵁ U.unop)) a at h
    change (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
      (scalarPresheafHom f)).d
        ((j.appIso U.unop).inv ((scalarPresheafHom (j ≫ f)).app U a)) = 0
    rw [h]
    exact _root_.PresheafOfModules.Derivation'.d_app
      (_root_.PresheafOfModules.DifferentialsConstruction.derivation'
        (scalarPresheafHom f)) a

/-- The universal presheaf map for this actual transported derivation. -/
def presheafComparison : presheaf (scalarPresheafHom (j ≫ f)) ⟶
    restrictedPresheaf f j :=
  (_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' _).desc
    (restrictedPresheafDerivation f j)

/-- The original presheaf comparison differentiates the original inverse
section-ring map on every open. -/
theorem presheafComparison_d (U : Y.Opens) (s : Γ(Y, U)) :
    (presheafComparison f j).app (op U) (CommRingCat.KaehlerDifferential.d s) =
      CommRingCat.KaehlerDifferential.d ((j.appIso U).inv s) :=
  ModuleCat.Derivation.desc_d ((restrictedPresheafDerivation f j).app (op U)) s

/-- Each component is the canonical differential localization map for
the actual section-ring isomorphism, hence is bijective. -/
theorem presheafComparison_bijective (U : Y.Opens) :
    Function.Bijective ((presheafComparison f j).app (op U)) := by
  let B := Γ(Y, U)
  let C := Γ(X, j ''ᵁ U)
  letI : Algebra k B := ((scalarPresheafHom (j ≫ f)).app (op U)).hom.toAlgebra
  letI : Algebra k C := ((scalarPresheafHom f).app (op (j ''ᵁ U))).hom.toAlgebra
  letI : Algebra B C := (j.appIso U).inv.hom.toAlgebra
  letI : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq (fun a => by
    exact (ConcreteCategory.congr_hom (scalar_appIso_inv f j U) a).symm)
  letI : IsLocalization.Away (1 : B) C :=
    IsLocalization.away_of_isUnit_of_bijective C isUnit_one
      (j.appIso U).symm.commRingCatIsoToRingEquiv.bijective
  let g : KaehlerDifferential k B →ₗ[B] KaehlerDifferential k C :=
    KaehlerDifferential.map k k B C
  let g' : KaehlerDifferential k B →ₗ[B] (restrictedPresheaf f j).obj (op U) :=
    { toFun := fun x => g x
      map_add' := g.map_add
      map_smul' a x := by
        change g (a • x) = (j.appIso U).inv a • g x
        rw [g.map_smul]
        exact (IsScalarTower.algebraMap_smul C a (g x)).symm }
  have hg : ((presheafComparison f j).app (op U)).hom = g' := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation k B)
    intro b
    change (presheafComparison f j).app (op U) (KaehlerDifferential.D k B b) =
      KaehlerDifferential.map k k B C (KaehlerDifferential.D k B b)
    rw [KaehlerDifferential.map_D]
    exact presheafComparison_d f j U b
  change Function.Bijective ((presheafComparison f j).app (op U)).hom
  rw [hg]
  change Function.Bijective g
  constructor
  · intro x y h
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (1 : B)) g).mp h
    obtain ⟨n, hn⟩ := c.property
    have hc1 : (c : B) = 1 := by simpa only [one_pow] using hn.symm
    simpa only [Submonoid.smul_def, hc1, one_smul] using hc
  · intro y
    obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers (1 : B)) g y
    obtain ⟨n, hn⟩ := c.property
    have hc1 : (c : B) = 1 := by simpa only [one_pow] using hn.symm
    exact ⟨x, by simpa only [Submonoid.smul_def, hc1, one_smul] using hc.symm⟩

/-- The original differential-presheaf unit restricted through the
already constructed actual module-restriction functor. -/
def restrictedUnit : restrictedPresheaf f j ⟶
    ((restriction j).obj (baseRingSheaf f)).val :=
  (_root_.PresheafOfModules.pushforward (restrictionRingHom j)).map
    (toSheaf (scalarPresheafHom f))

/-- The original transported derivation into the actual restricted sheaf. -/
def restrictedDerivation :
    ((restriction j).obj (baseRingSheaf f)).val.Derivation'
      (scalarPresheafHom (j ≫ f)) :=
  (restrictedPresheafDerivation f j).postcomp (restrictedUnit f j)

/-- The actual differential-sheaf comparison for the original open immersion. -/
def comparison : baseRingSheaf (j ≫ f) ⟶ (restriction j).obj (baseRingSheaf f) :=
  desc _ (restrictedDerivation f j)

/-- The actual comparison preserves differentiation of every original
section through the original inverse section-ring map. -/
theorem comparison_d (U : Y.Opens) (s : Γ(Y, U)) :
    (comparison f j).val.app (op U) ((baseRingDerivation (j ≫ f)).d s) =
      (baseRingDerivation f).d ((j.appIso U).inv s) :=
  _root_.PresheafOfModules.Derivation.congr_d
    (derivation_postcomp_desc _ (restrictedDerivation f j)) s

/-- The original comparison factors through precisely the original
presheaf comparison and restricted sheafification unit. -/
theorem toSheaf_comp_comparison :
    toSheaf (scalarPresheafHom (j ≫ f)) ≫ (comparison f j).val =
      presheafComparison f j ≫ restrictedUnit f j := by
  rw [comparison, toSheaf_comp_desc]
  apply (_root_.PresheafOfModules.DifferentialsConstruction.isUniversal'
    (scalarPresheafHom (j ≫ f))).postcomp_injective
  ext U s
  have h₁ := _root_.PresheafOfModules.Derivation.congr_d
    ((_root_.PresheafOfModules.DifferentialsConstruction.isUniversal'
      (scalarPresheafHom (j ≫ f))).fac (restrictedDerivation f j)) s
  have h₂ := _root_.PresheafOfModules.Derivation.congr_d
    ((_root_.PresheafOfModules.DifferentialsConstruction.isUniversal'
      (scalarPresheafHom (j ≫ f))).fac (restrictedPresheafDerivation f j)) s
  exact h₁.trans (congrArg ((restrictedUnit f j).app U) h₂).symm

/-- The actual open-immersion differential comparison is an isomorphism. -/
theorem comparison_isIso : IsIso (comparison f j) := by
  let J := Opens.grothendieckTopology Y
  let F := _root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.val
  let φ := scalarPresheafHom (j ≫ f)
  let η := CategoryTheory.toSheafify J (presheaf φ).presheaf
  let a := F.map (presheafComparison f j)
  let b := F.map (restrictedUnit f j)
  let c := (_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map (comparison f j)
  have hfac : η ≫ c.val = a ≫ b := by
    change F.map (toSheaf φ) ≫ F.map (comparison f j).val =
      F.map (presheafComparison f j) ≫ F.map (restrictedUnit f j)
    rw [← F.map_comp, ← F.map_comp, toSheaf_comp_comparison]
  letI : Presheaf.IsLocallyInjective J a :=
    Presheaf.isLocallyInjective_of_injective J a
      (fun U => (presheafComparison_bijective f j U.unop).injective)
  letI : Presheaf.IsLocallySurjective J a :=
    Presheaf.isLocallySurjective_of_surjective J a
      (fun U => (presheafComparison_bijective f j U.unop).surjective)
  letI : Presheaf.IsLocallyInjective J b := by
    change Presheaf.IsLocallyInjective J (CategoryTheory.whiskerLeft j.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (presheaf (scalarPresheafHom f)).presheaf))
    exact restriction_isLocallyInjective j _
  letI : Presheaf.IsLocallySurjective J b := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.whiskerLeft j.opensFunctor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (presheaf (scalarPresheafHom f)).presheaf))
    exact restriction_isLocallySurjective j _
  letI : Presheaf.IsLocallySurjective J η := inferInstance
  have hi : CategoryTheory.Sheaf.IsLocallyInjective c :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
      (a ≫ b) hfac
  have hs : CategoryTheory.Sheaf.IsLocallySurjective c :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  letI : IsIso c := (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso c).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso (comparison f j) (_root_.SheafOfModules.toSheaf Y.ringCatSheaf)

/-- The original differential sheaf restricted to an actual open
subscheme is its original base-ring differential sheaf. -/
def restrictionIso : (restriction j).obj (baseRingSheaf f) ≅ baseRingSheaf (j ≫ f) := by
  letI := comparison_isIso f j
  exact (asIso (comparison f j)).symm

@[simp]
theorem restrictionIso_inv : (restrictionIso f j).inv = comparison f j := rfl

/-- The proved restriction isomorphism retains the original derivative map. -/
theorem restrictionIso_inv_d (U : Y.Opens) (s : Γ(Y, U)) :
    (restrictionIso f j).inv.val.app (op U) ((baseRingDerivation (j ≫ f)).d s) =
      (baseRingDerivation f).d ((j.appIso U).inv s) :=
  comparison_d f j U s

end KltDP.Geometry.SchemeKaehlerOpenRestriction
