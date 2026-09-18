import KltDP.Geometry.AffineKaehlerStalkLocalization
import KltDP.Geometry.AffineStalkKaehlerLocalization

/-!
# The affine differential sheaf at the original structure stalk

The original affine sheaf comparison and the pinned tilde stalk map now
land in the native differentials of the original structure-sheaf stalk.
The base scalars are exactly those induced by the original scheme map.
The image of every germ of an original affine-function differential is
proved for this same comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.AffineKaehlerOriginalStalk

open SchemeKaehlerSheaf AffineKaehlerTildeDerivation IntrinsicNodal

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

private def originalScalarTower (p : PrimeSpectrum A) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
    IsScalarTower k A ((Spec (CommRingCat.of A)).presheaf.stalk p) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    (StructureSheaf.toStalk A p).hom.toAlgebra
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
  exact IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun a : CommRingCat.of k ⟶ (Spec (CommRingCat.of A)).presheaf.stalk p =>
      a.hom r) (AffineStalkKaehlerLocalization.scalar_map k A p)

/-- The original fixed-affine-ring stalk of the actual differential sheaf
is identified with the differentials of the original structure stalk. -/
def iso (p : PrimeSpectrum A) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
    letI := originalScalarTower k A p
    (AffineKaehlerStalkLocalization.presheaf A k).stalk p ≅
      ModuleCat.of A (KaehlerDifferential k ((Spec (CommRingCat.of A)).presheaf.stalk p)) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    (StructureSheaf.toStalk A p).hom.toAlgebra
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
  letI := originalScalarTower k A p
  exact (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).mapIso
    (AffineKaehlerStalkLocalization.presheafIso A k) ≪≫
      ModuleCat.Tilde.stalkIso (differentialModule k A) p ≪≫
        (AffineStalkKaehlerLocalization.fiberEquiv k A p).toModuleIso

/-- The comparison sends an original differential germ to the differential
of that same original function's structure-sheaf germ. -/
theorem iso_germ_toOpen_d (U : Opens (PrimeSpectrum A))
    (p : PrimeSpectrum A) (hp : p ∈ U) (a : A) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
    letI := originalScalarTower k A p
    (iso k A p).hom ((AffineKaehlerStalkLocalization.presheaf A k).germ U p hp
      ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
        (StructureSheaf.toOpen A U a))) =
      KaehlerDifferential.D k ((Spec (CommRingCat.of A)).presheaf.stalk p)
        (StructureSheaf.toStalk A p a) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    (StructureSheaf.toStalk A p).hom.toAlgebra
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
  letI := originalScalarTower k A p
  change AffineStalkKaehlerLocalization.fiberEquiv k A p
    (ModuleCat.Tilde.stalkToFiberLinearMap (differentialModule k A) p
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
        (X := PrimeSpectrum.Top A) p).map
        (AffineKaehlerStalkLocalization.presheafIso A k).hom
        ((AffineKaehlerStalkLocalization.presheaf A k).germ U p hp
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U a))))) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    AffineKaehlerStalkLocalization.presheafIso_d, sectionD_toOpen,
    ModuleCat.Tilde.stalkToFiberLinearMap_germ]
  exact AffineStalkKaehlerLocalization.fiberEquiv_mk_d k A p a

end KltDP.Geometry.AffineKaehlerOriginalStalk
