import KltDP.Geometry.RegularSurfacePointAffineKaehlerParameters
import KltDP.Geometry.AffineStalkNativeBasisNeighborhood
import KltDP.Geometry.AffinePrincipalNeighborhoodStructure

/-!
# Retaining the genuine affine native basis and original parameters

The original vanishing parameter representatives are chosen before spreading.
The resulting literal Spec-localization chart retains its affine Ω¹ basis,
its actual point and structure map, the same native stalk derivative basis,
and the same parameter numerators. This supplies the coefficient caller's
Ω¹ data without inferring it from an Ω² module identification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open IntrinsicNodal KaehlerBasisPrincipalNeighborhood

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {S : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (π : S ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The affine basis, original parameters and all actual chart maps are retained. -/
theorem exists_regular_closed_native_parameter_chart
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x)
    (U : X.toScheme.Opens) (hxU : x ∈ U) :
    letI := stalkAlgebra X.structureMorphism x
    ∃ (V : X.toScheme.affineOpens) (_ : V.1 ≤ U) (hxV : x ∈ V.1)
      (s : Fin 2 → Γ(X.toScheme, V.1))
      (b₀ : Basis (Fin 2) (X.stalk x) (KaehlerDifferential k (X.stalk x))),
      letI := affineSectionsAlgebra X.structureMorphism V.2
      letI := X.toScheme.presheaf.algebra_section_stalk ⟨x, hxV⟩
      letI := StalkKaehlerFiniteness.affine_stalk_scalarTower X.structureMorphism V.2 x hxV
      letI := V.2.isLocalization_stalk ⟨x, hxV⟩
      ∃ (r : Γ(X.toScheme, V.1))
        (hr : r ∉ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal)
        (b : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r))),
        (∀ i, X.toScheme.presheaf.germ V.1 x hxV (s i) ∈ maximalIdeal (X.stalk x)) ∧
        (∀ i, b₀ i = KaehlerDifferential.D k (X.stalk x)
          (X.toScheme.presheaf.germ V.1 x hxV (s i))) ∧
        Ideal.span (Set.range (fun i => X.toScheme.presheaf.germ V.1 x hxV (s i))) =
          maximalIdeal (X.stalk x) ∧
        (∀ i, nativeRestriction k Γ(X.toScheme, V.1)
          (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.stalk x) r hr (b i) = b₀ i) ∧
        (∀ i, nativeRestriction k Γ(X.toScheme, V.1)
          (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.stalk x) r hr
            (KaehlerDifferential.D k (Localization.Away r)
              (algebraMap Γ(X.toScheme, V.1) (Localization.Away r) (s i))) = b₀ i) ∧
        IsOpenImmersion (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X.toScheme, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ∧
        ((Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X.toScheme, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ≫
            X.structureMorphism =
          Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) ∧
        ∃ y : Spec (CommRingCat.of (Localization.Away r)),
          (Spec.map (CommRingCat.ofHom
            (algebraMap Γ(X.toScheme, V.1) (Localization.Away r))) ≫ V.2.fromSpec).base y = x := by
  letI := stalkAlgebra X.structureMorphism x
  obtain ⟨V, hVU, hxV, s, b₀, hs, hb₀, hspan, _⟩ :=
    X.exists_regular_closed_affine_kaehler_parameters f π hπ hbir x hclosed hregular U hxU
  letI := affineSectionsAlgebra X.structureMorphism V.2
  letI := X.toScheme.presheaf.algebra_section_stalk ⟨x, hxV⟩
  letI := StalkKaehlerFiniteness.affine_stalk_scalarTower X.structureMorphism V.2 x hxV
  letI := V.2.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨r, hr, b, hb, _, hopen, y, hy⟩ :=
    AffineStalkNativeBasisNeighborhood.exists_principal_native_basis
      X.structureMorphism x V.2 hxV b₀
  refine ⟨V, hVU, hxV, s, b₀, r, hr, b, hs, hb₀, hspan, hb, ?_, hopen,
    AffinePrincipalNeighborhoodStructure.structure_map X.structureMorphism V.2 r, y, hy⟩
  intro i
  exact (nativeRestriction_D k Γ(X.toScheme, V.1)
    (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.stalk x) r hr (s i)).trans (hb₀ i).symm

end KltDP.Geometry.NormalProjectiveSurface
