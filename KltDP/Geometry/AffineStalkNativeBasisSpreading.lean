import KltDP.Geometry.KaehlerBasisPrincipalNeighborhood
import KltDP.Geometry.StalkKaehlerFiniteness
import Mathlib.RingTheory.FinitePresentation

/-! Spread the native basis along the original affine germ. The actual
prime is named explicitly, independently of the geometric principal-chart
carrier comparison. All finite-presentation hypotheses are derived. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineStalkNativeBasisSpreading

open IntrinsicNodal KaehlerBasisPrincipalNeighborhood

private theorem affineNativeKaehler_finitePresentation
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := affineSectionsAlgebra g hU
    Module.FinitePresentation Γ(Y, U) (KaehlerDifferential k Γ(Y, U)) := by
  letI := affineSectionsAlgebra g hU
  letI : Algebra.FiniteType k Γ(Y, U) := affineSectionsAlgebra_finiteType g hU
  letI : Algebra.FinitePresentation k Γ(Y, U) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  infer_instance

/-- Exact vectorwise native restriction under the original affine germ. -/
theorem exists_native_basis
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (x : Y) {U : Y.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨x, hx⟩
    letI := affineSectionsAlgebra g hU
    letI := stalkAlgebra g x
    letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := StalkKaehlerFiniteness.affine_stalk_scalarTower g hU x hx
    letI : IsLocalization P.asIdeal.primeCompl (Y.presheaf.stalk x) :=
      hU.isLocalization_stalk ⟨x, hx⟩
    ∀ b₀ : Basis (Fin 2) (Y.presheaf.stalk x)
      (KaehlerDifferential k (Y.presheaf.stalk x)),
    ∃ (r : Γ(Y, U)) (hr : r ∈ P.asIdeal.primeCompl)
      (b : Basis (Fin 2) (Localization.Away r)
        (KaehlerDifferential k (Localization.Away r))),
      (∀ i, nativeRestriction k Γ(Y, U) P.asIdeal.primeCompl
        (Y.presheaf.stalk x) r hr (b i) = b₀ i) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (Localization.Away r) 2 b) = 1 := by
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨x, hx⟩
  letI := affineSectionsAlgebra g hU
  letI := stalkAlgebra g x
  letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower g hU x hx
  letI : IsLocalization P.asIdeal.primeCompl (Y.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hx⟩
  letI : Module.FinitePresentation Γ(Y, U) (KaehlerDifferential k Γ(Y, U)) :=
    affineNativeKaehler_finitePresentation g hU
  exact exists_native_basis_primitive k Γ(Y, U) P.asIdeal.primeCompl
    (Y.presheaf.stalk x)

end KltDP.Geometry.AffineStalkNativeBasisSpreading
