import KltDP.Geometry.AffineStalkNativeBasisNeighborhood
import KltDP.Geometry.RegularSurfacePointKaehlerParameters

/-!
# A native differential frame on a genuine target neighborhood

The original regular closed point supplies native Kähler parameters. Finite
presentation follows from the actual finite-type structure map. Spreading
their differential basis gives an actual principal affine open containing
that same point, with a primitive native top differential frame. No target
smoothness or canonical-reference neighborhood is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open IntrinsicNodal KaehlerBasisPrincipalNeighborhood

private theorem combine_parameter_basis
    {α γ δ ι T : Type*} {β : α → Type*} {S : α → Prop}
    {f : γ → ι → T} {g : δ → ι → T}
    {h : (a : α) → S a → β a → ι → T}
    {V : γ → Prop} {E : γ → δ → Prop}
    {R : (a : α) → S a → β a → Prop}
    (hparameter : ∃ v b₀, (∀ i, g b₀ i = f v i) ∧ V v ∧ E v b₀)
    (hbasis : ∀ b₀, ∃ a, ∃ ha : S a, ∃ b : β a,
      (∀ i, h a ha b i = g b₀ i) ∧ R a ha b) :
    ∃ a, ∃ ha : S a, ∃ v, ∃ b : β a,
      V v ∧ (∀ i, h a ha b i = f v i) ∧ R a ha b := by
  obtain ⟨v, b₀, hb₀, hv, _⟩ := hparameter
  obtain ⟨a, ha, b, hb, hR⟩ := hbasis b₀
  exact ⟨a, ha, v, b, hv, (fun i => (hb i).trans (hb₀ i)), hR⟩

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {S : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (π : S ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The principal chart contains the original regular point; its native
basis restricts to the differentials of the original vanishing parameters. -/
theorem exists_regular_closed_principal_native_basis
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    letI := affineSectionsAlgebra X.structureMorphism hU
    letI := stalkAlgebra X.structureMorphism x
    letI := X.toScheme.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := StalkKaehlerFiniteness.affine_stalk_scalarTower X.structureMorphism hU x hx
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    ∃ (r : Γ(X.toScheme, U))
      (hr : r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (v : Fin 2 → maximalIdeal (X.stalk x))
      (b : Basis (Fin 2) (Localization.Away r)
        (KaehlerDifferential k (Localization.Away r))),
      Ideal.span (Set.range (fun i => (v i : X.stalk x))) = maximalIdeal (X.stalk x) ∧
      (∀ i, nativeRestriction k Γ(X.toScheme, U)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.stalk x) r hr (b i) =
        KaehlerDifferential.D k (X.stalk x) (v i)) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (Localization.Away r) 2 b) = 1 ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X.toScheme, U) (Localization.Away r))) ≫ hU.fromSpec) ∧
      ∃ y : Spec (CommRingCat.of (Localization.Away r)),
        (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X.toScheme, U) (Localization.Away r))) ≫ hU.fromSpec).base y = x := by
  letI := affineSectionsAlgebra X.structureMorphism hU
  letI := stalkAlgebra X.structureMorphism x
  letI := X.toScheme.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower X.structureMorphism hU x hx
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  exact combine_parameter_basis
    (X.exists_regular_closed_stalk_kaehler_parameters f π hπ hbir x hclosed hregular)
    (AffineStalkNativeBasisNeighborhood.exists_principal_native_basis
      X.structureMorphism x hU hx)

end KltDP.Geometry.NormalProjectiveSurface
