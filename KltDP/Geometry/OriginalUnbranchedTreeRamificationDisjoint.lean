import KltDP.Geometry.OriginalUnbranchedRationalTreePrimeCurves
import KltDP.Geometry.RationalComponentPrimeCurvesIncidence
import KltDP.Geometry.OriginalUnbranchedRamificationDisjoint
import KltDP.Geometry.SelectedCanonicalBranchRange

/-!
# Both original tree sheets avoid the actual ramification curves

The original tree misses the original canonical branch. Its unchanged
component inclusions therefore miss the selected curves on the base.
The original projection identities then prove that every coherent lifted
component avoids every actual prime selected for ramification blowdown.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalUnbranchedTreeRamificationSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeRamificationMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable {C : Scheme.{u}} [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC
local notation "copyCurve" =>
  liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj
local notation "copyMap" =>
  primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj

variable (N : Finset S.PrimeCurve)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

/-- Every actual lifted component survives all the selected ramification contractions. -/
theorem liftedCurve_disjoint_selectedRamification
    (ε : Bool) (D : ↥(irreducibleComponents C)) :
    ∀ P ∈ S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ,
      Disjoint (copyCurve ε D : Set (CoverSurface).toScheme) (P : Set (CoverSurface).toScheme) := by
  have hselected : Disjoint (Set.range f.base) (S.selectedPrimeClosedUnion N : Set S.toScheme) := by
    rw [← S.canonicalBranch_range_eq_selected N E hE hIJ]
    exact hdisj
  have hbase : Disjoint (Set.range (baseCurve D).inclusion.base)
      (S.selectedPrimeClosedUnion N : Set S.toScheme) := by
    rw [(baseCurve D).range_inclusion, RationalComponentPrimeCurves.curve_carrier]
    exact hselected.mono_left (Set.image_subset_range f.base (D : Set C))
  have h := S.lift_disjoint_selectedRamificationPrimeSet N E hE L e hIJ
    (baseCurve D).inclusion (copyMap ε D)
    (primeLift_projection S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D)
    hbase h2 hred hne
  intro P hP
  rw [← closedImage_primeLift S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D]
  exact h P hP

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.liftedCurve_disjoint_selectedRamification
