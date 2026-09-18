import KltDP.Geometry.RationalTreePicardIntrinsicNode
import KltDP.Geometry.AffineKaehlerTildeDerivation

/-!
# Kähler localization at the original affine structure stalk

The canonical localization theorem applies directly to the original
structure-sheaf stalk. Its scalar tower over the original base is proved
from the actual scheme structure map. Thus no replacement of the original
stalk ring or of its base scalars is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineStalkKaehlerLocalization

open IntrinsicNodal AffineKaehlerTildeDerivation

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The original structure morphism induces exactly the original affine
algebra map followed by the original stalk map. -/
theorem scalar_map (p : PrimeSpectrum A) :
    baseToStalkMap (Spec.map (CommRingCat.ofHom (algebraMap k A))) p =
      CommRingCat.ofHom (algebraMap k A) ≫ StructureSheaf.toStalk A p := by
  apply Spec.map_injective
  rw [Spec_map_baseToStalkMap, Spec.map_comp, Scheme.Spec_fromSpecStalk']

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
      a.hom r) (scalar_map k A p)

/-- The canonical Kähler localization equivalence lands in the native
differentials of the same original structure-sheaf stalk, with original base scalars. -/
def fiberEquiv (p : PrimeSpectrum A) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
    letI := originalScalarTower k A p
    LocalizedModule p.asIdeal.primeCompl (differentialModule k A) ≃ₗ[A]
      KaehlerDifferential k ((Spec (CommRingCat.of A)).presheaf.stalk p) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    (StructureSheaf.toStalk A p).hom.toAlgebra
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
  letI := originalScalarTower k A p
  letI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p)
      p.asIdeal := StructureSheaf.IsLocalization.to_stalk A p
  exact IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map k k A ((Spec (CommRingCat.of A)).presheaf.stalk p))

/-- The canonical numerator differential goes to the differential of its
original germ; this fixes the forward localization map. -/
theorem fiberEquiv_mk_d (p : PrimeSpectrum A) (a : A) :
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
      (StructureSheaf.toStalk A p).hom.toAlgebra
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
    fiberEquiv k A p
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (differentialModule k A)
        (KaehlerDifferential.D k A a)) =
      KaehlerDifferential.D k ((Spec (CommRingCat.of A)).presheaf.stalk p)
        (StructureSheaf.toStalk A p a) := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk p) :=
    (StructureSheaf.toStalk A p).hom.toAlgebra
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p
  letI := originalScalarTower k A p
  letI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p)
      p.asIdeal := StructureSheaf.IsLocalization.to_stalk A p
  change IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map k k A ((Spec (CommRingCat.of A)).presheaf.stalk p))
    (LocalizedModule.mk (KaehlerDifferential.D k A a) 1) = _
  rw [← IsLocalizedModule.iso_symm_apply p.asIdeal.primeCompl
    (KaehlerDifferential.map k k A ((Spec (CommRingCat.of A)).presheaf.stalk p)),
    LinearEquiv.apply_symm_apply,
    KaehlerDifferential.map_D]
  rfl

end KltDP.Geometry.AffineStalkKaehlerLocalization
