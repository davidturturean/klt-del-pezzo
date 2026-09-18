import KltDP.Geometry.SmoothFieldRegularPoints
import KltDP.Geometry.ProjectiveChartNormal
import KltDP.Topology.Dimension

/-!
# Actual points of a smooth open of a normal projective surface are regular

Normality, Noetherian stalks, integrality, and the dimension bound all
restrict from the original surface along the original open immersion.
The existing smooth-field regularity theorem then applies to that open,
and the actual stalk isomorphism gives regularity on the original surface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (T : NormalProjectiveSurface k)

/-- Every actual point in the original smooth open is regular on the original surface. -/
theorem regularPoint_of_isSmooth_on_open (U : T.toScheme.Opens)
    [IsSmooth (U.ι ≫ T.structureMorphism)] (x : U) :
    RegularPoint T.toScheme (U.ι.base x) := by
  letI : Nonempty (U : Scheme.{u}) := ⟨x⟩
  letI : IsIntegral (U : Scheme.{u}) := isIntegral_of_isOpenImmersion U.ι
  have hnormal : IsNormalScheme (U : Scheme.{u}) :=
    isNormalScheme_of_isOpenImmersion U.ι T.normal
  have hnoeth : ∀ z : (U : Scheme.{u}), IsNoetherianRing
      ((U : Scheme.{u}).presheaf.stalk z) := by
    intro z
    letI : IsNoetherianRing (T.toScheme.presheaf.stalk (U.ι.base z)) :=
      T.projective.isNoetherianRing_stalk (U.ι.base z)
    exact isNoetherianRing_of_ringEquiv (T.toScheme.presheaf.stalk (U.ι.base z))
      (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv
  have hdim : topologicalKrullDim (U : Scheme.{u}) ≤ 2 :=
    (KltDP.Topology.topologicalKrullDim_le_of_isOpenEmbedding U.ι.base U.ι.isOpenEmbedding).trans_eq
      T.dimension_two
  have hreg := SmoothFieldRegularPoints.regularPoint_of_isSmooth_of_isNormalScheme
    (U.ι ≫ T.structureMorphism) hnormal hnoeth hdim x
  exact (regularPoint_iff_of_isOpenImmersion U.ι x).mp hreg

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.regularPoint_of_isSmooth_on_open
