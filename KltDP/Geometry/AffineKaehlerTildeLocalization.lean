import KltDP.Geometry.AffineKaehlerTildeDerivation
import KltDP.Geometry.AffineModuleTildeLocalization

/-!
# The actual affine differential sheaf is the differential tilde sheaf

On a basic open, both the ordinary differential module of its original
section ring and the original affine differential tilde sections satisfy
the canonical module-localization property. The actual differential
comparison agrees with these localization maps on affine differentials,
so localization uniqueness proves that it is bijective there.

Basic opens cover every open. The original presheaf comparison is
therefore locally bijective, and its factorization through the original
sheafification unit proves that the actual sheaf comparison is an
isomorphism. No smoothness, local frame, or canonical-sheaf comparison is
assumed. This connects the global construction to the affine module used
by the existing top differential frames.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineKaehlerTildeLocalization

open AffineKaehlerTildeDerivation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The original universal presheaf map to the actual affine tilde sheaf. -/
def presheafComparison :
    SchemeKaehlerSheaf.presheaf (SchemeKaehlerSheaf.scalarPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟶
        (differentialModule k A).tilde.val :=
  (_root_.PresheafOfModules.DifferentialsConstruction.isUniversal' _).desc
    (tildeDerivation k A)

/-- On every original section, the presheaf comparison is the actual
locally-fractional differential section. -/
theorem presheafComparison_d (U : Opens (PrimeSpectrum A))
    (s : Γ(Spec (CommRingCat.of A), U)) :
    (presheafComparison k A).app (op U)
      (CommRingCat.KaehlerDifferential.d s) = sectionD k A U s :=
  ModuleCat.Derivation.desc_d ((tildeDerivation k A).app (op U)) s

/-- The actual sheaf comparison extends precisely this original presheaf map. -/
theorem toSheaf_comp_comparison :
    SchemeKaehlerSheaf.toSheaf (SchemeKaehlerSheaf.scalarPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ≫ (comparison k A).val =
        presheafComparison k A :=
  SchemeKaehlerSheaf.toSheaf_comp_desc _ (tildeDerivation k A)

/-- The actual presheaf comparison on a basic open is the canonical
equivalence between two localizations of the original affine module. -/
theorem presheafComparison_basicOpen_bijective (r : A) :
    Function.Bijective ((presheafComparison k A).app (op (PrimeSpectrum.basicOpen r))) := by
  let U := PrimeSpectrum.basicOpen r
  let B := Γ(Spec (CommRingCat.of A), U)
  letI : Algebra A B := StructureSheaf.openAlgebra A (op U)
  letI : IsLocalization.Away r B := StructureSheaf.IsLocalization.to_basicOpen A r
  letI : Algebra k B := ((SchemeKaehlerSheaf.scalarPresheafHom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app (op U)).hom.toAlgebra
  have hscalar (a : k) : algebraMap k B a = algebraMap A B (algebraMap k A a) := by
    change (SchemeKaehlerSheaf.scalarPresheafHom
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))).app (op U) a = _
    rw [scalarPresheafHom_app]
    rfl
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq hscalar
  let T := (differentialModule k A).tildeInModuleCat.obj (op U)
  letI : Module B T := ((differentialModule k A).tilde.val.obj (op U)).isModule
  letI : IsScalarTower A B T := IsScalarTower.of_algebraMap_smul
    (fun a s => AffineModuleTilde.toOpen_scalar_smul (differentialModule k A) U a s)
  let g : KaehlerDifferential k B →ₗ[B] T :=
    ((presheafComparison k A).app (op U)).hom
  let fD : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k B :=
    KaehlerDifferential.map k k A B
  let fT : KaehlerDifferential k A →ₗ[A] T :=
    (ModuleCat.Tilde.toOpen (differentialModule k A) U).hom
  letI : IsLocalizedModule (Submonoid.powers r) fT :=
    AffineModuleTilde.toOpen_isLocalizedModule (differentialModule k A) r
  have hcomp : (g.restrictScalars A).comp fD = fT := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation k A)
    intro a
    change (presheafComparison k A).app (op U)
      (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)) = _
    rw [KaehlerDifferential.map_D]
    exact (presheafComparison_d k A U (StructureSheaf.toOpen A U a)).trans
      (sectionD_toOpen k A U a)
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers r) fD fT
  have he : g.restrictScalars A = e.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) fD fT
    rw [hcomp]
    apply LinearMap.ext
    intro x
    exact (IsLocalizedModule.linearEquiv_apply (Submonoid.powers r) fD fT x).symm
  change Function.Bijective (g.restrictScalars A)
  rw [he]
  exact e.bijective

private theorem locallyInjective_of_basicOpen
    {P Q : (Opens (PrimeSpectrum A))ᵒᵖ ⥤ AddCommGrp.{u}} (α : P ⟶ Q)
    (hα : ∀ r : A, Function.Injective (α.app (op (PrimeSpectrum.basicOpen r)))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (PrimeSpectrum A)) α := by
  constructor
  intro U s t h x hx
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.unop.isOpen
  refine ⟨PrimeSpectrum.basicOpen r, homOfLE hrU, ?_, hxr⟩
  change P.map (homOfLE hrU).op s = P.map (homOfLE hrU).op t
  apply hα r
  have hs := ConcreteCategory.congr_hom (α.naturality (homOfLE hrU).op) s
  have ht := ConcreteCategory.congr_hom (α.naturality (homOfLE hrU).op) t
  exact hs.trans ((congrArg (Q.map (homOfLE hrU).op) h).trans ht.symm)

private theorem presheafComparison_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      ((_root_.PresheafOfModules.toPresheaf (Spec (CommRingCat.of A)).ringCatSheaf.val).map
        (presheafComparison k A)) :=
  locallyInjective_of_basicOpen A _
    (fun r => (presheafComparison_basicOpen_bijective k A r).injective)

private theorem presheafComparison_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      ((_root_.PresheafOfModules.toPresheaf (Spec (CommRingCat.of A)).ringCatSheaf.val).map
        (presheafComparison k A)) := by
  constructor
  intro U s x hx
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨PrimeSpectrum.basicOpen r, homOfLE hrU, ?_, hxr⟩
  exact (presheafComparison_basicOpen_bijective k A r).surjective
    ((differentialModule k A).tilde.val.map (homOfLE hrU).op s)

/-- The comparison built from the original universal derivation is an
isomorphism from the actual global differential sheaf to the actual tilde. -/
theorem comparison_isIso : IsIso (comparison k A) := by
  let X := Spec (CommRingCat.of A)
  let J := Opens.grothendieckTopology X
  let F := _root_.PresheafOfModules.toPresheaf X.ringCatSheaf.val
  let φ := SchemeKaehlerSheaf.scalarPresheafHom
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let η := CategoryTheory.toSheafify J (SchemeKaehlerSheaf.presheaf φ).presheaf
  let c := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map (comparison k A)
  have hfac : η ≫ c.val = F.map (presheafComparison k A) := by
    change F.map (SchemeKaehlerSheaf.toSheaf φ) ≫
      F.map (comparison k A).val = _
    rw [← F.map_comp, toSheaf_comp_comparison]
  letI : Presheaf.IsLocallyInjective J (F.map (presheafComparison k A)) :=
    presheafComparison_isLocallyInjective k A
  letI : Presheaf.IsLocallySurjective J (F.map (presheafComparison k A)) :=
    presheafComparison_isLocallySurjective k A
  letI : Presheaf.IsLocallySurjective J η := inferInstance
  have hi : CategoryTheory.Sheaf.IsLocallyInjective c :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J
      (F.map (presheafComparison k A)) hfac
  have hs : CategoryTheory.Sheaf.IsLocallySurjective c :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  letI : IsIso c := (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso c).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso (comparison k A) (_root_.SheafOfModules.toSheaf X.ringCatSheaf)

/-- The proved affine comparison, retaining its original forward map. -/
def iso : SchemeKaehlerSheaf.baseRingSheaf
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) ≅ (differentialModule k A).tilde := by
  letI := comparison_isIso k A
  exact asIso (comparison k A)

@[simp]
theorem iso_hom : (iso k A).hom = comparison k A := rfl

/-- The actual isomorphism takes the derivative of every original section
to its original differential tilde section. -/
theorem iso_d (U : Opens (PrimeSpectrum A)) (s : Γ(Spec (CommRingCat.of A), U)) :
    (iso k A).hom.val.app (op U)
      ((SchemeKaehlerSheaf.baseRingDerivation
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d s) = sectionD k A U s :=
  comparison_d k A U s

end KltDP.Geometry.AffineKaehlerTildeLocalization
