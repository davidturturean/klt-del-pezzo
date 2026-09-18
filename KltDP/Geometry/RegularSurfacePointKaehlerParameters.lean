import KltDP.Geometry.DomainBasisOfSpanningRank
import KltDP.Geometry.LocalKaehlerParameterGeneration
import KltDP.Geometry.StalkKaehlerFiniteness
import KltDP.Geometry.StalkKaehlerGenericRank
import KltDP.Geometry.RegularSurfacePointCotangentParameters
import KltDP.Geometry.ClosedPointStalkResidueScalar
import KltDP.Geometry.BirationalSmoothGenericKaehlerBasis

/-!
# Native Kähler parameters at an original regular surface point

The regular point supplies actual vanishing cotangent parameters. The
original residue scalar map, Nakayama, and the generic rank derived from
the given smooth birational source make their very same differentials a
basis. Its determinant frame sends their original wedge to one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {S : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (π : S ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The actual regular-point parameters have a native differential basis,
and their exact top wedge is primitive. No target smoothness or frame is assumed. -/
theorem exists_regular_closed_stalk_kaehler_parameters
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x) :
    letI := stalkAlgebra X.structureMorphism x
    ∃ (v : Fin 2 → maximalIdeal (X.stalk x))
      (b : Basis (Fin 2) (X.stalk x) (KaehlerDifferential k (X.stalk x))),
      (∀ i, b i = KaehlerDifferential.D k (X.stalk x) (v i)) ∧
      Ideal.span (Set.range (fun i => (v i : X.stalk x))) = maximalIdeal (X.stalk x) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (X.stalk x) 2
          (fun i => KaehlerDifferential.D k (X.stalk x) (v i))) = 1 := by
  letI := stalkAlgebra X.structureMorphism x
  letI := stalkAlgebra X.structureMorphism (genericPoint X.toScheme)
  letI := StalkKaehlerFiniteness.stalk_kaehler_finite X.structureMorphism x
  obtain ⟨v, _, _, hv, _⟩ := X.exists_regular_closed_stalk_cotangent_parameters x hclosed hregular
  have hspan : Submodule.span (X.stalk x)
      (Set.range (fun i => KaehlerDifferential.D k (X.stalk x) (v i))) = ⊤ :=
    LocalKaehlerParameterGeneration.span_derivatives k (X.stalk x) v hv
      (ClosedPointStalkResidue.algebraMap_bijective X.structureMorphism x hclosed).2
  have hgeneric : Module.rank X.toScheme.functionField
      (KaehlerDifferential k X.toScheme.functionField) = 2 := by
    simpa using
      (BirationalSmoothGenericKaehlerBasis.basis f X.structureMorphism π hπ hbir).mk_eq_rank.symm
  have hrank : Module.rank (X.stalk x) (KaehlerDifferential k (X.stalk x)) = 2 :=
    (StalkKaehlerGenericRank.rank_eq_functionField X.structureMorphism x).trans hgeneric
  let b := DomainBasisOfSpanningRank.basis
    (fun i => KaehlerDifferential.D k (X.stalk x) (v i)) hspan hrank
  have hb : ∀ i, b i = KaehlerDifferential.D k (X.stalk x) (v i) :=
    DomainBasisOfSpanningRank.basis_apply _ hspan hrank
  refine ⟨v, b, hb, hv, ?_⟩
  have heq : (fun i => KaehlerDifferential.D k (X.stalk x) (v i)) = b := (funext hb).symm
  rw [heq]
  exact AffineTopDifferentialFrame.determinantEquiv_basis_wedge b

end KltDP.Geometry.NormalProjectiveSurface
