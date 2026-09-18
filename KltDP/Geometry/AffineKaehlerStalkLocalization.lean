import KltDP.Geometry.AffineKaehlerTildeLocalization

/-!
# The affine differential sheaf stalk and the original prime localization

The actual affine differential sheaf is first viewed as a presheaf of
modules over its original affine ring, using the same pinned scalar
restriction as `ModuleCat.tildeInModuleCat`. Its actual stalk is identified
with the differential module of the original prime localization by the
proved sheaf comparison, pinned tilde stalk isomorphism, and canonical
Kähler localization equivalence. The formula on every germ of an original
section differential fixes this comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineKaehlerStalkLocalization

open SchemeKaehlerSheaf AffineKaehlerTildeDerivation

variable (A : Type u) [CommRing A]

/-- The actual fixed-affine-ring module presheaf of an original module sheaf. -/
def modulePresheafFunctor :
    (Spec (CommRingCat.of A)).Modules ⥤
      TopCat.Presheaf (ModuleCat.{u} A) (PrimeSpectrum.Top A) :=
  _root_.SheafOfModules.forget (Spec (CommRingCat.of A)).ringCatSheaf ⋙
    _root_.PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      (CategoryTheory.Limits.initialOpOfTerminal CategoryTheory.Limits.isTerminalTop) ⋙
    (whiskeringRight _ _ _).obj
      (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso A).hom.hom)

/-- For an original tilde sheaf this is exactly its pinned module presheaf. -/
theorem modulePresheafFunctor_tilde (M : ModuleCat A) :
    (modulePresheafFunctor A).obj M.tilde = M.tildeInModuleCat := rfl

variable (k : Type u) [CommRing k] [Algebra k A]

/-- The original differential sheaf, with its original affine-ring action. -/
abbrev presheaf : TopCat.Presheaf (ModuleCat.{u} A) (PrimeSpectrum.Top A) :=
  (modulePresheafFunctor A).obj
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A))))

/-- Apply the original scalar-restriction functor to the actual affine
differential-to-tilde isomorphism. -/
def presheafIso : presheaf A k ≅ (differentialModule k A).tildeInModuleCat :=
  (modulePresheafFunctor A).mapIso (AffineKaehlerTildeLocalization.iso k A)

theorem presheafIso_d (U : Opens (PrimeSpectrum A))
    (a : Γ(Spec (CommRingCat.of A), U)) :
    (presheafIso A k).hom.app (op U)
      ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d a) =
        sectionD k A U a :=
  AffineKaehlerTildeLocalization.iso_d k A U a

/-- The actual stalk of the original affine differential sheaf is the
native Kähler module of the original prime localization. -/
def iso (p : PrimeSpectrum A) :
    TopCat.Presheaf.stalk (presheaf A k) p ≅
      ModuleCat.of A (KaehlerDifferential k (Localization.AtPrime p.asIdeal)) :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).mapIso (presheafIso A k) ≪≫
    ModuleCat.Tilde.stalkIso (differentialModule k A) p ≪≫
      (fiberEquiv k A p).toModuleIso

/-- A germ of the original section differential becomes the differential
of that section's value in the original prime localization. -/
theorem iso_germ_d (U : Opens (PrimeSpectrum A)) (p : PrimeSpectrum A) (hp : p ∈ U)
    (a : Γ(Spec (CommRingCat.of A), U)) :
    (iso A k p).hom (TopCat.Presheaf.germ (presheaf A k) U p hp
      ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d a)) =
        KaehlerDifferential.D k (Localization.AtPrime p.asIdeal) (a.val ⟨p, hp⟩) := by
  change fiberEquiv k A p
    (ModuleCat.Tilde.stalkToFiberLinearMap (differentialModule k A) p
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
        (X := PrimeSpectrum.Top A) p).map (presheafIso A k).hom
        (TopCat.Presheaf.germ (presheaf A k) U p hp
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d a)))) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, presheafIso_d,
    ModuleCat.Tilde.stalkToFiberLinearMap_germ]
  change fiberEquiv k A p ((fiberEquiv k A p).symm
    (KaehlerDifferential.D k (Localization.AtPrime p.asIdeal) (a.val ⟨p, hp⟩))) = _
  exact (fiberEquiv k A p).apply_symm_apply _

end KltDP.Geometry.AffineKaehlerStalkLocalization
