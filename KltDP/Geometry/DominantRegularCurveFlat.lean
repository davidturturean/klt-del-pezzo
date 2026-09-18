import KltDP.Compatibility.BezoutTorsionFreeFlat
import KltDP.Geometry.RegularCurveValuationStalk
import KltDP.Geometry.DominantGenericPoint
import KltDP.Geometry.SchematicImageGenericPrecomposition
import KltDP.Geometry.ProjectiveLineClosedPointCartier
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness of the original dominant morphism to a regular integral curve

Dominance gives injectivity on the original section rings. The actual
affine-localization and germ square then give injectivity on every stalk.
The actual base stalks are valuation rings, hence Bezout domains, so the
torsion-free criterion proves each original stalk map flat. The pinned
stalk criterion gives flatness of the unchanged scheme morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.DominantRegularCurveFlat

attribute [local instance] integralSchemeStalk_isDomain

variable {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    (f : X ⟶ C) [IsDominant f]

/-- Dominance between integral schemes makes every original local-ring
map injective, via the original affine section and germ maps. -/
theorem stalkMap_injective (x : X) : Function.Injective (f.stalkMap x).hom := by
  letI : GenericPointPreserving f := genericPointPreserving_of_isDominant f
  let U : C.Opens := (C.affineCover.map (f.base x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (C.affineCover.map (f.base x))
  have hx : f.base x ∈ U := C.affineCover.covers (f.base x)
  apply IsAffineOpen.stalkMap_injective f hU x hx
  intro s hs
  have hg : X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U s) = 0 := by
    simpa only [Scheme.stalkMap_germ_apply] using hs
  have happ : f.app U s = 0 := by
    apply germ_injective_of_isIntegral X x hx
    simpa only [map_zero] using hg
  have hz : s = 0 := by
    apply SchematicImageGenericPrecomposition.app_injective f U
    simpa only [map_zero] using happ
  simp only [hz, map_zero]

/-- Each actual stalk map to a regular integral curve is flat. -/
theorem stalkMap_flat
    (hregular : ∀ x : C, RegularPoint C x)
    (hdim : topologicalKrullDim C ≤ 1) (x : X) :
    (f.stalkMap x).hom.Flat := by
  letI : ValuationRing (C.presheaf.stalk (f.base x)) :=
    RegularCurveValuationStalk.valuationRing C hregular hdim (f.base x)
  exact KltDP.Compatibility.BezoutTorsionFreeFlat.ringHom_flat_of_injective
    (f.stalkMap x).hom (stalkMap_injective f x)

/-- The original dominant morphism from an integral scheme to an actual
regular integral scheme of dimension at most one is flat. -/
theorem flat_of_regular_curve
    (hregular : ∀ x : C, RegularPoint C x)
    (hdim : topologicalKrullDim C ≤ 1) : Flat f :=
  Flat.of_stalkMap f (stalkMap_flat f hregular hdim)

/-- In particular, an actual dominant morphism from an integral scheme
to the original projective line is flat, over any field. -/
theorem flat_projectiveLine {k : Type u} [Field k]
    (g : X ⟶ projectiveSpace k 1) [IsDominant g] : Flat g := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  exact flat_of_regular_curve g (ProjectiveLineClosedPointCartier.regularPoint k)
    (projectiveSpace_topologicalKrullDim k 1).le

end KltDP.Geometry.DominantRegularCurveFlat

#check @KltDP.Geometry.DominantRegularCurveFlat.stalkMap_injective
#check @KltDP.Geometry.DominantRegularCurveFlat.stalkMap_flat
#check @KltDP.Geometry.DominantRegularCurveFlat.flat_of_regular_curve
#check @KltDP.Geometry.DominantRegularCurveFlat.flat_projectiveLine
#print axioms KltDP.Geometry.DominantRegularCurveFlat.stalkMap_injective
#print axioms KltDP.Geometry.DominantRegularCurveFlat.stalkMap_flat
#print axioms KltDP.Geometry.DominantRegularCurveFlat.flat_of_regular_curve
#print axioms KltDP.Geometry.DominantRegularCurveFlat.flat_projectiveLine
