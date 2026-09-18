import KltDP.Geometry.SchemeStalkNativeBasisTransport
import KltDP.Geometry.AffinePrincipalNeighborhoodStalkGerms
import KltDP.Geometry.AffinePrincipalNeighborhoodStructure

/-!
# The original native parameter basis on the literal principal Spec stalk

The given original stalk parameters are transported through the actual
open-chart stalk map. The original numerator-germ square proves the exact
D(toStalk(algebraMap sᵢ)) equations; locality preserves their vanishing.
All hypotheses are supplied by the retained original native-parameter chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Geometry.AffinePrincipalNeighborhoodNativeParameters

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U)
    (r : Γ(X, U)) (p : PrimeSpectrum (Localization.Away r))

variable (x : X) (hx : x ∈ U) (hpx : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).base p = x)

include hpx in
/-- Native derivative basis and vanishing on the literal original Spec stalk,
with the literal principal-localization numerators retained. -/
theorem exists_native_parameter_basis :
    letI := affineSectionsAlgebra f hU
    letI := stalkAlgebra f x
    letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) p
    ∀ (s : Fin 2 → Γ(X, U))
      (b₀ : Basis (Fin 2) (X.presheaf.stalk x)
        (KaehlerDifferential k (X.presheaf.stalk x))),
      (∀ i, b₀ i = KaehlerDifferential.D k (X.presheaf.stalk x)
        (X.presheaf.germ U x hx (s i))) →
      (∀ i, X.presheaf.germ U x hx (s i) ∈ maximalIdeal (X.presheaf.stalk x)) →
      ∃ bₚ : Basis (Fin 2) ((Spec (CommRingCat.of (Localization.Away r))).presheaf.stalk p)
          (KaehlerDifferential k ((Spec (CommRingCat.of (Localization.Away r))).presheaf.stalk p)),
        (∀ i, bₚ i = KaehlerDifferential.D k ((Spec (CommRingCat.of (Localization.Away r))).presheaf.stalk p)
          (StructureSheaf.toStalk (Localization.Away r) p (algebraMap Γ(X, U) (Localization.Away r) (s i)))) ∧
        (∀ i, StructureSheaf.toStalk (Localization.Away r) p (algebraMap Γ(X, U) (Localization.Away r) (s i)) ∈
          maximalIdeal ((Spec (CommRingCat.of (Localization.Away r))).presheaf.stalk p)) := by
  subst x
  letI := affineSectionsAlgebra f hU
  letI := stalkAlgebra f ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).base p)
  letI := stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) p
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) := inferInstance
  have hstructure : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) :=
    AffinePrincipalNeighborhoodStructure.structure_map f hU r
  refine fun s b₀ hb₀ hs => ?_
  let bₚ := SchemeStalkNativeBasisTransport.basis f (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) hstructure p b₀
  refine ⟨bₚ, ?_, ?_⟩
  · intro i
    have hD := SchemeStalkNativeBasisTransport.basis_apply_of_eq_D f (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) hstructure p b₀ i
      (X.presheaf.germ U ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).base p) hx (s i)) (hb₀ i)
    exact hD.trans (congrArg
      (KaehlerDifferential.D k ((Spec (CommRingCat.of (Localization.Away r))).presheaf.stalk p))
      (AffinePrincipalNeighborhoodStalkGerms.germ_stalkMap hU r p hx (s i)))
  · intro i
    have hvalue := AffinePrincipalNeighborhoodStalkGerms.germ_stalkMap hU r p hx (s i)
    exact hvalue ▸ (map_nonunit ((Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).stalkMap p).hom _ (hs i))

end KltDP.Geometry.AffinePrincipalNeighborhoodNativeParameters
