import KltDP.Geometry.AffinePairStalkRepresentatives
import KltDP.Geometry.RegularSurfacePointKaehlerParameters

/-!
# Genuine regular-point parameters on an original affine neighborhood

The proved native Kähler parameter basis is represented by two actual
sections on a common affine neighborhood. Its vanishing, maximal-ideal
generation, basis equations and primitive determinant value all retain
the original structure-stalk germ map.
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
/-- Actual affine representatives of the derived native parameter basis,
inside any prescribed neighborhood of the original regular closed point. -/
theorem exists_regular_closed_affine_kaehler_parameters
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x)
    (U : X.toScheme.Opens) (hxU : x ∈ U) :
    letI := stalkAlgebra X.structureMorphism x
    ∃ (V : X.toScheme.affineOpens) (_ : V.1 ≤ U) (hxV : x ∈ V.1)
      (s : Fin 2 → Γ(X.toScheme, V.1))
      (b : Basis (Fin 2) (X.stalk x) (KaehlerDifferential k (X.stalk x))),
      (∀ i, X.toScheme.presheaf.germ V.1 x hxV (s i) ∈ maximalIdeal (X.stalk x)) ∧
      (∀ i, b i = KaehlerDifferential.D k (X.stalk x)
        (X.toScheme.presheaf.germ V.1 x hxV (s i))) ∧
      Ideal.span (Set.range (fun i => X.toScheme.presheaf.germ V.1 x hxV (s i))) =
        maximalIdeal (X.stalk x) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (X.stalk x) 2 (fun i => KaehlerDifferential.D k (X.stalk x)
          (X.toScheme.presheaf.germ V.1 x hxV (s i)))) = 1 := by
  letI := stalkAlgebra X.structureMorphism x
  obtain ⟨v, b, hb, hspan, hdet⟩ :=
    X.exists_regular_closed_stalk_kaehler_parameters f π hπ hbir x hclosed hregular
  obtain ⟨V, hVU, hxV, s, hs⟩ := exists_affine_pair_stalk_representatives
    X.toScheme x (fun i => (v i : X.stalk x)) U hxU
  have heq : (fun i => X.toScheme.presheaf.germ V.1 x hxV (s i)) =
      (fun i => (v i : X.stalk x)) := funext hs
  refine ⟨V, hVU, hxV, s, b, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hs i]
    exact (v i).property
  · intro i
    rw [hs i]
    exact hb i
  · rw [heq]
    exact hspan
  · have hd : (fun i => KaehlerDifferential.D k (X.stalk x)
        (X.toScheme.presheaf.germ V.1 x hxV (s i))) =
        (fun i => KaehlerDifferential.D k (X.stalk x) (v i)) :=
      funext fun i => congrArg (KaehlerDifferential.D k (X.stalk x)) (hs i)
    rw [hd]
    exact hdet

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_regular_closed_affine_kaehler_parameters
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_regular_closed_affine_kaehler_parameters
