import KltDP.Geometry.OriginalUnbranchedRationalTreePrimeCurves
import KltDP.Geometry.OriginalUnbranchedPrimeSelfIntersection
import KltDP.Geometry.SplitPrimeCurveLiftIntersection

/-!
# The actual doubled intersection matrix of an original unbranched rational tree

The prime curves and maps are those of the unchanged original quadratic
cover. Original branch disjointness produces each rational component's
split pullback. The coherent whole-tree maps supply the original
projections and disjoint opposite sheets. Classification therefore
identifies the required labels, and the original Cartier projection
formula computes every same-sheet intersection. Opposite-sheet entries
vanish by their derived geometric disjointness.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreeMatrixSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeMatrixMonoidal : MonoidalCategory S.toScheme.Modules :=
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
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

local notation "CoverAtlas" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverRegular" =>
  OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
    S E hE L e h2 hred hne hsm
local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC
local notation "copyCurve" => liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj
local notation "copyLift" => primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj

/-- Two unchanged component copies in the same coherent sheet retain their original intersection. -/
theorem liftedCurve_intersection_same (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    (copyCurve ε D).intersectionNumber
      ((CoverSurface).primeCurveCartier CoverRegular (copyCurve ε F)) =
        (baseCurve D).intersectionNumber (S.primeCurveCartier S.regularPoints_of_isSmooth (baseCurve F)) := by
  letI : IsIntegral (CoverAtlas).scheme := (CoverSurface).integral
  letI : GenericPointPreserving (CoverAtlas).morphism := (CoverAtlas).morphism_genericPointPreserving
  letI : IsFinite (CoverAtlas).morphism := (CoverAtlas).morphism_isFinite
  have hbase (B : ↥(irreducibleComponents C)) :
      Disjoint (baseCurve B : Set S.toScheme)
        (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base) := by
    change Disjoint (Set.range (componentUnionInclusion C {B} ≫ f).base) _
    apply hdisj.mono_left
    rintro x ⟨y, rfl⟩
    exact ⟨(componentUnionInclusion C {B}).base y, rfl⟩
  obtain ⟨qD, hqD, hgeometryD⟩ :=
    S.exists_original_unbranched_prime_copies_preserving_selfIntersection
      E hE L e h2 hred hne hsm (baseCurve D)
      (RationalComponentPrimeCurves.sourceIso S f eC D ≪≫ eC D) (hbase D)
  obtain ⟨qF, hqF, hgeometryF⟩ :=
    S.exists_original_unbranched_prime_copies_preserving_selfIntersection
      E hE L e h2 hred hne hsm (baseCurve F)
      (RationalComponentPrimeCurves.sourceIso S f eC F ≪≫ eC F) (hbase F)
  obtain ⟨hg, hd, hpairing⟩ := SplitPrimeCurveLiftIntersection.lift_intersectionNumber
    (T := CoverSurface) (CoverAtlas).morphism (baseCurve D) (baseCurve F) qD qF
    S.regularPoints_of_isSmooth CoverRegular hqD hqF rfl
    (copyLift ε D) (copyLift ε F) (copyLift (!ε) F)
    (primeLift_projection S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D)
    (primeLift_projection S sC hdim hTree htrans eC E hE L e h2 f hdisj ε F)
    (primeLift_projection S sC hdim hTree htrans eC E hE L e h2 f hdisj (!ε) F)
    (primeLift_disjoint_opposite S sC hdim hTree htrans eC E hE L e h2 f hdisj ε F F)
    (primeLift_disjoint_opposite S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D F)
  rw [closedImage_primeLift S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D,
    closedImage_primeLift S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε F] at hpairing
  exact hpairing

/-- Every actual opposite-sheet component pair is geometrically disjoint. -/
theorem liftedCurve_disjoint_opposite (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    Disjoint (copyCurve ε D : Set (CoverSurface).toScheme)
      (copyCurve (!ε) F : Set (CoverSurface).toScheme) := by
  rw [← closedImage_primeLift S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D,
    ← closedImage_primeLift S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj (!ε) F]
  exact primeLift_disjoint_opposite S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D F

/-- Every actual opposite-sheet matrix entry is zero. -/
theorem liftedCurve_intersection_opposite (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    (copyCurve ε D).intersectionNumber
      ((CoverSurface).primeCurveCartier CoverRegular (copyCurve (!ε) F)) = 0 := by
  have hd := liftedCurve_disjoint_opposite S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D F
  have hneCurves : copyCurve ε D ≠ copyCurve (!ε) F := by
    intro h
    rw [← h] at hd
    obtain ⟨x, hx⟩ := (copyCurve ε D).nonempty
    exact Set.disjoint_left.mp hd hx hx
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
    CoverSurface CoverRegular (copyCurve ε D) (copyCurve (!ε) F)]
  exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    CoverSurface CoverRegular (copyCurve ε D) (copyCurve (!ε) F) hneCurves).mpr hd

/-- Both actual component copies preserve the original diagonal self-intersection. -/
theorem liftedCurve_selfIntersection (ε : Bool) (D : ↥(irreducibleComponents C)) :
    (copyCurve ε D).selfIntersectionNumber CoverRegular =
      (baseCurve D).selfIntersectionNumber S.regularPoints_of_isSmooth :=
  liftedCurve_intersection_same S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj ε D D

/-- The intersection matrix of the actual doubled prime family is two copies of the original matrix. -/
theorem actual_doubled_intersectionMatrix
    (i j : Bool × ↥(irreducibleComponents C)) :
    (CoverSurface).primeCurveMatrix CoverRegular (copyCurve i.1 i.2) (copyCurve j.1 j.2) =
      if i.1 = j.1 then
        S.primeCurveMatrix S.regularPoints_of_isSmooth (baseCurve i.2) (baseCurve j.2)
      else 0 := by
  rcases i with ⟨ε, D⟩
  rcases j with ⟨δ, F⟩
  dsimp only
  by_cases h : ε = δ
  · subst δ
    rw [if_pos rfl]
    exact liftedCurve_intersection_same S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj ε D F
  · rw [if_neg h]
    have hδ : δ = !ε := by
      cases ε <;> cases δ <;> first | rfl | exact False.elim (h rfl)
    subst δ
    exact liftedCurve_intersection_opposite S sC hdim hTree htrans eC E hE L e h2 hred hne hsm f hdisj ε D F

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.actual_doubled_intersectionMatrix
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.liftedCurve_selfIntersection
