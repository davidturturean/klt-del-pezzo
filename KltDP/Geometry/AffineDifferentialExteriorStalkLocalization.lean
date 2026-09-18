import KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation
import KltDP.LinearAlgebra.TopExteriorScalarLocalization

/-!
# The original exterior evaluation is the canonical localization isomorphism

The original Kähler map to the structure stalk is a localization. The
proved top exterior scalar-localization theorem applies to its actual
finite basis. Uniqueness of localization then identifies the existing
evaluation map with the canonical localization isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation

open AffineKaehlerTildeDerivation

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

local notation "Aₚ" => originalStalkRing A p
local notation "Ωₚ" => (KaehlerDifferential k Aₚ)

include b in
/-- Localization of the original affine-to-stalk exterior map, with the
same original ground and affine scalar actions. -/
theorem nativeMap_isLocalizedModule :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    IsLocalizedModule p.asIdeal.primeCompl (nativeMap k A p n) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkScalarTower (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI : Module A Ωₚ :=
    KaehlerDifferential.module' (R := k) (S := Aₚ) (R' := A)
  letI : IsScalarTower A Aₚ Ωₚ :=
    KaehlerDifferential.isScalarTower_of_tower (R := k) (S := Aₚ) (R₁ := A) (R₂ := Aₚ)
  letI : IsLocalization.AtPrime Aₚ p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A p
  exact KltDP.LinearAlgebra.TopExteriorScalarLocalization.isLocalizedModule
    p.asIdeal.primeCompl Aₚ (KaehlerDifferential.map k k A Aₚ) b

/-- The pinned localization isomorphism for the same original native map. -/
def localizationIso :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    LocalizedModule p.asIdeal.primeCompl ((differentialModule k A).exteriorPower n)
      ≃ₗ[A] (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := nativeMap_isLocalizedModule k A p b
  exact IsLocalizedModule.iso p.asIdeal.primeCompl (nativeMap k A p n)

/-- The existing localization evaluation is exactly this canonical isomorphism. -/
theorem localizedMap_eq_localizationIso :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    localizedMap k A p n = (localizationIso k A p b).toLinearMap := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := nativeMap_isLocalizedModule k A p b
  apply IsLocalizedModule.linearMap_ext p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl
      ((differentialModule k A).exteriorPower n)) (nativeMap k A p n)
  apply LinearMap.ext
  intro m
  change localizedMap k A p n (LocalizedModule.mk m 1) =
    IsLocalizedModule.iso p.asIdeal.primeCompl (nativeMap k A p n)
      (LocalizedModule.mk m 1)
  rw [localizedMap_mk_one, IsLocalizedModule.iso_mk_one]

end KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation

#check @KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation.localizedMap_eq_localizationIso
#print axioms KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation.localizedMap_eq_localizationIso
