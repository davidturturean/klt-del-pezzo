import KltDP.Geometry.SurfaceBirationalPointBlowupDominationProper
import KltDP.Geometry.BirationalSeparatedLeftFactor
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The actual map from the point-blowup model to the original target

The proved equation over X identifies the composite to X with the original
birational composite through T. Cancellation of the original separated
birational map V → X proves birationality of the constructed map Z → V.
If the original T → X is proper, the same equation and the pinned proper
left-factor theorem prove that the same map Z → V is proper.

All original maps, the point-blowup sequence, and the original-domain
agreement are retained. No normality or projectivity of Z is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SurfaceBirationalPointBlowupDomination

open SurfaceBirationalGraphDominationInput

variable {k : Type u} [Field k] [IsAlgClosed k] (T : NormalProjectiveSurface k)
  {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
  (t : T.toScheme ⟶ X) (v : V ⟶ X) [IsProper v]
  (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)

/-- The constructed map to the original target is birational, with the
original point-blowup model, over-X equation, and partial-map agreement. -/
theorem exists_domination_with_birational_target_of_regular
    (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme) (q : Z ⟶ V) (hZ : IsIntegral Z),
      letI := hZ
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) Z b ∧
      IsBirationalScheme b ∧ IsBirationalScheme q ∧ IsProper b ∧
      IsProper (b ≫ T.structureMorphism) ∧ IsNoetherian Z ∧
      topologicalKrullDim Z = 2 ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ Z,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  obtain ⟨Z, b, q, hZ, h⟩ := exists_proper_domination_of_regular T t v ht hv hreg
  letI := hZ
  obtain ⟨hb, hbirb, hproperb, hproperk, hnoeth, hdim, hiso, hq, j, hjb, hjq⟩ := h
  letI : GenericPointPreserving b := ⟨hbirb.map_genericPoint⟩
  letI : GenericPointPreserving t := ⟨ht.map_genericPoint⟩
  have hbt : IsBirationalScheme (b ≫ t) :=
    (BirationalComposition.isBirationalScheme_comp_iff b t).mpr ⟨hbirb, ht⟩
  have hqv : IsBirationalScheme (q ≫ v) := by
    rw [hq]
    exact hbt
  have hbirq : IsBirationalScheme q :=
    isBirationalScheme_left_of_comp_of_isSeparated q v hv hqv
  exact ⟨Z, b, q, hZ, hb, hbirb, hbirq, hproperb, hproperk,
    hnoeth, hdim, hiso, hq, j, hjb, hjq⟩

/-- If the original source map to X is proper, both actual projections
from the constructed point-blowup model are proper and birational. -/
theorem exists_common_proper_domination_of_regular [IsProper t]
    (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme) (q : Z ⟶ V) (hZ : IsIntegral Z),
      letI := hZ
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) Z b ∧
      IsBirationalScheme b ∧ IsBirationalScheme q ∧ IsProper b ∧ IsProper q ∧
      IsProper (b ≫ T.structureMorphism) ∧ IsNoetherian Z ∧
      topologicalKrullDim Z = 2 ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ Z,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  obtain ⟨Z, b, q, hZ, h⟩ :=
    exists_domination_with_birational_target_of_regular T t v ht hv hreg
  letI := hZ
  obtain ⟨hb, hbirb, hbirq, hproperb, hproperk, hnoeth, hdim, hiso, hq, j, hjb, hjq⟩ := h
  letI : IsProper b := hproperb
  letI : IsProper (q ≫ v) := by
    rw [hq]
    infer_instance
  have hproperq : IsProper q := IsProper.of_comp_of_isSeparated q v
  exact ⟨Z, b, q, hZ, hb, hbirb, hbirq, hproperb, hproperq, hproperk,
    hnoeth, hdim, hiso, hq, j, hjb, hjq⟩

end KltDP.Geometry.SurfaceBirationalPointBlowupDomination
