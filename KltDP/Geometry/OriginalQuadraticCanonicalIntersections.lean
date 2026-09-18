import KltDP.Geometry.SelectedOriginalCoverCanonicalSquareConditional
import KltDP.Literature.Stacks.AffineMorphismCohomology

/-!
# Canonical intersections of the actual original quadratic cover

The complete independently reviewed affine-cohomology theorem is applied
to the ordinary original-object consumers. The original cover supplies its
pushforward splitting, ramification divisor, and normalized Hurwitz factor.
These endpoints have no affine comparison, splitting, canonical formula,
or intersection projection among their hypotheses.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalQuadraticCanonicalIntersection

open OriginalCartierRamificationSmooth SmoothCanonicalCartierRepresentative

local instance canonicalIntersectionModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance canonicalIntersectionSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
  (L : InvertibleSheaf S.toScheme)
  (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
  (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
  (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne

/-- The actual quadratic morphism doubles the original intersection pairing. -/
theorem picardPairing_pullback
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (p q : S.toScheme.Pic) :
    (T).picardPairing hT (schemePicardPullbackHom (A).morphism p)
        (schemePicardPullbackHom (A).morphism q) = 2 * S.picardPairing hS p q :=
  originalCover_picardPairing_pullback KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S E hE L e h2 hred hne hS hT p q

variable [IsSmoothOfRelativeDimension 2 S.structureMorphism]
  [IsSmoothOfRelativeDimension 1
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism)]

/-- The canonical mixed pairing uses the same original pulled base class. -/
theorem canonical_pairing_pullback
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (p : S.toScheme.Pic) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (T).picardPairing hT
        (cartierPicardClass (T).toScheme (cartierRepresentative (T).structureMorphism))
        (schemePicardPullbackHom (A).morphism p) =
      2 * S.picardPairing hS
        (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic) p :=
  originalCover_canonical_pairing_pullback KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S E hE L e h2 hred hne hS hT p

/-- The actual canonical square is twice the original half-branch canonical square. -/
theorem canonical_selfIntersection
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    let P := cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic
    (T).intersectionPairing hT (cartierRepresentative (T).structureMorphism)
        (cartierRepresentative (T).structureMorphism) = 2 * S.picardPairing hS P P :=
  originalCover_canonical_selfIntersection KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S E hE L e h2 hred hne hS hT

/-- The manuscript's square formula for the actual disjoint minus-two branch. -/
theorem selected_canonical_selfIntersection
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ y : (T).Point, RegularPoint (T).toScheme y)
    (N : Finset S.PrimeCurve) (hselected : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hS = -2)
    (hK : ∀ C ∈ N, C.intersectionNumber (cartierRepresentative S.structureMorphism) = 0) :
    letI : IsIntegral (T).toScheme := (T).integral
    letI : IsSmoothOfRelativeDimension 2 (T).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    (T).intersectionPairing hT (cartierRepresentative (T).structureMorphism)
        (cartierRepresentative (T).structureMorphism) =
      2 * S.intersectionPairing hS (cartierRepresentative S.structureMorphism)
        (cartierRepresentative S.structureMorphism) - (N.card : ℤ) :=
  originalSelectedCover_canonical_selfIntersection
    KltDP.Literature.Stacks.affine_morphism_cohomology_literal
    S E hE L e h2 hred hne hS hT N hselected hdisj hself hK

end KltDP.Geometry.OriginalQuadraticCanonicalIntersection

#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.picardPairing_pullback
#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.canonical_pairing_pullback
#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.selected_canonical_selfIntersection
