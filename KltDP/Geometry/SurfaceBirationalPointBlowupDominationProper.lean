import KltDP.Geometry.SurfaceBirationalPointBlowupDomination
import KltDP.Geometry.SchemePointBlowupSequenceProper
import KltDP.Geometry.SchemePointBlowupSequenceIntegral
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.ProperBirationalDimension

/-!
# Properness of the actual over-X point-blowup model

The point-blowup sequence already constructed for the original correspondence
supplies properness and birationality of its original composite, with an
integral Noetherian source of dimension two. Its unchanged original domain is nonempty.
The maps over X and their agreement with the original partial map are retained.
This does not supply normality, regularity, or projectivity of that source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SurfaceBirationalPointBlowupDomination

open SurfaceBirationalGraphDominationInput

/-- The original correspondence admits an actual integral proper Noetherian model
obtained by point blowups, with its original over-X and open-domain equations. -/
theorem exists_proper_domination_of_regular
    {k : Type u} [Field k] [IsAlgClosed k] (T : NormalProjectiveSurface k)
    {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
    (t : T.toScheme ⟶ X) (v : V ⟶ X) [IsProper v]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme) (q : Z ⟶ V) (hZ : IsIntegral Z),
      letI := hZ
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) Z b ∧
      IsBirationalScheme b ∧ IsProper b ∧
      IsProper (b ≫ T.structureMorphism) ∧ IsNoetherian Z ∧
      topologicalKrullDim Z = 2 ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ Z,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  obtain ⟨Z, b, q, hb, hiso, hq, j, hjb, hjq⟩ :=
    exists_domination_of_regular T t v ht hv hreg
  letI : Nonempty (representative T t v ht hv).domain.toScheme := by
    obtain ⟨x, hx⟩ := (representative T t v ht hv).dense_domain.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI hZ : IsIntegral Z := hb.source_isIntegral _
  letI : IsProper b := hb.isProper_over_noetherian_base T.structureMorphism
  letI : IsNoetherian Z := hb.source_isNoetherian T.structureMorphism
  letI : LocallyOfFiniteType T.structureMorphism := T.projective.locallyOfFiniteType
  have hbir : IsBirationalScheme b := hb.isBirationalScheme _
  have hdim : topologicalKrullDim Z = 2 :=
    (topologicalKrullDim_eq_of_proper_birational b T.structureMorphism hbir).trans T.dimension_two
  exact ⟨Z, b, q, hZ, hb, hbir, inferInstance, inferInstance, inferInstance,
    hdim, hiso, hq, j, hjb, hjq⟩

end KltDP.Geometry.SurfaceBirationalPointBlowupDomination
