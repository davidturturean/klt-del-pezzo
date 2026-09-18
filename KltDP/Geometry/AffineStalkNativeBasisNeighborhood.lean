import KltDP.Geometry.AffineStalkNativeBasisSpreading
import KltDP.Geometry.AffinePrincipalNeighborhoodPoint

/-! Join the separately proved original affine-germ spreading and
principal-chart point, retaining the exact existing public interface. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineStalkNativeBasisNeighborhood

open IntrinsicNodal KaehlerBasisPrincipalNeighborhood

private theorem attach_condition {α : Type*} {β : α → Type*}
    {S : α → Prop} {P Q : (a : α) → S a → β a → Prop} {F : α → Prop}
    (hF : ∀ a, S a → F a)
    (h : ∃ a, ∃ ha : S a, ∃ b : β a, P a ha b ∧ Q a ha b) :
    ∃ a, ∃ ha : S a, ∃ b : β a, P a ha b ∧ Q a ha b ∧ F a := by
  obtain ⟨a, ha, b, hP, hQ⟩ := h
  exact ⟨a, ha, b, hP, hQ, hF a ha⟩

/-- The native basis is preserved vector by vector on a genuine principal
open of the original affine neighborhood, containing the original point. -/
theorem exists_principal_native_basis
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (x : Y) {U : Y.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    letI := affineSectionsAlgebra g hU
    letI := stalkAlgebra g x
    letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := StalkKaehlerFiniteness.affine_stalk_scalarTower g hU x hx
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    ∀ b₀ : Basis (Fin 2) (Y.presheaf.stalk x)
      (KaehlerDifferential k (Y.presheaf.stalk x)),
    ∃ (r : Γ(Y, U)) (hr : r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (b : Basis (Fin 2) (Localization.Away r)
        (KaehlerDifferential k (Localization.Away r))),
      (∀ i, nativeRestriction k Γ(Y, U)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (Y.presheaf.stalk x) r hr (b i) = b₀ i) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (Localization.Away r) 2 b) = 1 ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec) ∧
      ∃ y : Spec (CommRingCat.of (Localization.Away r)),
        (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec).base y = x := by
  letI := affineSectionsAlgebra g hU
  letI := stalkAlgebra g x
  letI := Y.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower g hU x hx
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  refine fun (b₀ : Basis (Fin 2) (Y.presheaf.stalk x)
    (KaehlerDifferential k (Y.presheaf.stalk x))) => ?_
  exact attach_condition
    (fun r hr => AffinePrincipalNeighborhoodPoint.exists_chart_point x hU hx r hr)
    (AffineStalkNativeBasisSpreading.exists_native_basis g x hU hx b₀)

end KltDP.Geometry.AffineStalkNativeBasisNeighborhood
