import KltDP.Geometry.OriginalUnbranchedLiftSelfIntersection
import KltDP.Geometry.RationalCurveClosedImage

/-!
# Original unbranched lifts from actual rational component schemes

The source of a coherent tree-component map is its original reduced
component scheme. The rational closed-image comparison identifies that
scheme with the actual original prime curve, applies the proved arbitrary
lift theorem, and transports the conclusion back to the unchanged map.
The final target prime curve is the actual image of the original map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open PrimeCurveOfClosedImmersion RationalCurveClosedImage

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance originalUnbranchedRationalLiftSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedRationalLiftMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- An actual unbranched rational-component lift preserves the square of its original image. -/
theorem original_unbranched_rational_lift_selfIntersection
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))
    {C : Scheme.{u}} (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))
    (g : C ⟶ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme)
    (hg : g ≫ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism = f) :
    let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
    let H := OriginalCartierRamificationSmooth.regularPoints_of_smooth_base_and_branch
      S E hE L e h2 hred hne hsm
    ∃ hclosed : IsClosedImmersion g,
      letI := hclosed
      (primeCurveOfIsoProjectiveLine T g eC).selfIntersectionNumber H =
        (primeCurveOfIsoProjectiveLine S f eC).selfIntersectionNumber S.regularPoints_of_isSmooth := by
  dsimp only
  let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let P := primeCurveOfIsoProjectiveLine S f eC
  let η : P.toScheme ≅ C := sourceIso S f eC
  have hproj : (η.hom ≫ g) ≫
      (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism = P.inclusion := by
    rw [Category.assoc, hg]
    exact sourceIso_hom_map S f eC
  obtain ⟨hclosed, hs⟩ := S.original_unbranched_lift_selfIntersection
    E hE L e h2 hred hne hsm P (η ≪≫ eC) hdisj (η.hom ≫ g) hproj
  have hclosedg : IsClosedImmersion g :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) η.hom g).mp hclosed
  letI : IsClosedImmersion g := hclosedg
  refine ⟨hclosedg, ?_⟩
  have himage := closedImage_precomp_iso T g eC P η
  rw [← himage]
  exact hs

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.original_unbranched_rational_lift_selfIntersection
