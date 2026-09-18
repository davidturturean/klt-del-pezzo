import KltDP.Geometry.AmpleBignessFromRiemannRoch

/-!
# Nef line bundles of positive square are big

The compiled RR argument already applies to any actual nef Cartier divisor
of positive square, using that same divisor to force complementary section
vanishing. Transport through the original Picard class gives the statement
for any original invertible sheaf. No Hodge or ample-plus-nef criterion is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.NefPositiveSelfIntersectionBig

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The existing nef predicate depends only on the original Picard class. -/
theorem isNef_of_toPic_eq {L M : InvertibleSheaf X.toScheme}
    (h : L.toPic = M.toPic) (hL : Positivity.IsNef X.structureMorphism L) :
    Positivity.IsNef X.structureMorphism M := by
  rw [Positivity.isNef_iff_forall_primeCurve X] at hL ⊢
  intro C
  rw [← C.picardRestrictionDegree_toPic M, ← h, C.picardRestrictionDegree_toPic L]
  exact hL C

/-- The existing actual h⁰-growth predicate depends only on the Picard class. -/
theorem isBig_of_toPic_eq {L M : InvertibleSheaf X.toScheme}
    (h : L.toPic = M.toPic) (hL : Positivity.IsBig X.structureMorphism L) :
    Positivity.IsBig X.structureMorphism M := by
  simpa only [Positivity.IsBig, h] using hL

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The actual nef line bundle needs only positive self-intersection and
an original canonical divisor to enter the already compiled RR proof. -/
theorem isBig_of_isCanonical (K : X.WeilDivisor) (hK : IsCanonical X hregular K)
    (L : InvertibleSheaf X.toScheme) (hL : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection hregular L) :
    Positivity.IsBig X.structureMorphism L := by
  let A := X.picardRepresentative L.toPic
  have hclass : cartierPicardClass X.toScheme A = L.toPic :=
    X.cartierPicardClass_picardRepresentative L.toPic
  have hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A) :=
    isNef_of_toPic_eq X hclass.symm hL
  have hAA : 0 < intersectionPairing X hregular A A := by
    rw [← X.picardPairing_class hregular A A, hclass]
    exact hpositive
  exact isBig_of_toPic_eq X hclass
    (AmpleBignessFromRiemannRoch.isBig_of_nef_of_intersection_pos X hregular K hK A hA hAA)

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- On the original smooth projective surface, nefness and positive
self-intersection imply the original actual section-growth definition of big. -/
theorem isBig (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    Positivity.IsBig X.structureMorphism L :=
  isBig_of_isCanonical X X.regularPoints_of_isSmooth (weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) L hL hpositive

end Smooth

end KltDP.Geometry.NefPositiveSelfIntersectionBig
