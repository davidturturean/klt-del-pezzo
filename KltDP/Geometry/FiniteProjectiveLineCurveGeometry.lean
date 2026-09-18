import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Geometry.DominantGenericPoint
import KltDP.Geometry.SchematicImageGenericPrecomposition
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The original finite normal cover of the projective line is a regular curve

An actual affine inverse image gives an integral map of the original
section rings. Surjectivity preserves the generic point, hence makes
that section map injective. Integral incomparability gives the upper
dimension bound; lying over and nontriviality of the base prime spectrum
give the lower bound. The nonempty-affine dimension comparison applies
to these same schemes over the original field.

Normality and the proved global dimension bound then make every actual
Noetherian stalk regular. No curve representation, dimension, regularity,
or replacement structure morphism is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteProjectiveLineCurveGeometry

/-- A domain integral over a one-dimensional domain by an injective map
has dimension one. Only the existing incomparability and lying-over
theorems are needed for this dimension-one specialization. -/
private theorem ring_dimension_one {R A : Type u}
    [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (f : R →+* A) (hinj : Function.Injective f) (hint : f.IsIntegral)
    (hdim : ringKrullDim R = 1) : ringKrullDim A = 1 := by
  apply le_antisymm
  · exact (KltDP.Compatibility.ringKrullDim_le_of_integral f hint).trans hdim.le
  · have hpos : 0 < Order.krullDim (PrimeSpectrum R) := by
      change 0 < ringKrullDim R
      rw [hdim]
      exact zero_lt_one
    letI : Nontrivial (PrimeSpectrum R) :=
      Order.krullDim_pos_iff_of_orderBot.mp hpos
    letI : Nontrivial (PrimeSpectrum A) :=
      (hint.specComap_surjective hinj).nontrivial
    exact (WithBot.one_le_iff_pos _).mpr
      (Order.krullDim_pos_iff_of_orderBot.mpr inferInstance)

variable {k : Type u} [Field k] {B : Scheme.{u}}
    (g : B ⟶ projectiveSpace k 1) [IsFinite g]

/-- Properness, including finite type and separatedness, of the unchanged
composite with the original projective-line structure map. -/
theorem structure_isProper : IsProper (g ≫ projectiveSpaceToSpec k 1) := by
  infer_instance

/-- The original finite surjective integral cover has dimension one. -/
theorem dimension_eq_one [IsAlgClosed k] [IsIntegral B]
    (hsurj : Function.Surjective g.base) : topologicalKrullDim B = 1 := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsDominant g := ⟨hsurj.denseRange⟩
  letI : GenericPointPreserving g := genericPointPreserving_of_isDominant g
  let x : B := Classical.choice inferInstance
  let U : (projectiveSpace k 1).Opens :=
    ((projectiveSpace k 1).affineCover.map (g.base x)).opensRange
  have hx : g.base x ∈ U := (projectiveSpace k 1).affineCover.covers (g.base x)
  have hU : IsAffineOpen U :=
    isAffineOpen_opensRange ((projectiveSpace k 1).affineCover.map (g.base x))
  letI : Nonempty U := ⟨⟨g.base x, hx⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  letI : IsDomain Γ(projectiveSpace k 1, U) := IsIntegral.component_integral U
  letI : IsDomain Γ(B, g ⁻¹ᵁ U) := IsIntegral.component_integral (g ⁻¹ᵁ U)
  have hbase : ringKrullDim Γ(projectiveSpace k 1, U) = 1 :=
    (nonempty_affine_dimension_eq_global (projectiveSpace k 1)
      (projectiveSpaceToSpec k 1) hU).trans (projectiveSpace_topologicalKrullDim k 1)
  have happ : Function.Injective (g.app U).hom :=
    SchematicImageGenericPrecomposition.app_injective g U
  have hint : (g.app U).hom.IsIntegral := IsIntegralHom.integral_app U hU
  calc
    topologicalKrullDim B = ringKrullDim Γ(B, g ⁻¹ᵁ U) :=
      (nonempty_affine_dimension_eq_global B (g ≫ projectiveSpaceToSpec k 1)
        (hU.preimage g)).symm
    _ = 1 := ring_dimension_one (g.app U).hom happ hint hbase

/-- Every point of the original normal finite cover has a regular local
ring, using the original composite map to obtain Noetherian stalks. -/
theorem regularPoint [IsAlgClosed k] [IsIntegral B]
    (hsurj : Function.Surjective g.base) (hnormal : IsNormalScheme B)
    (x : B) : RegularPoint B x := by
  letI : IsLocallyNoetherian B :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec (g ≫ projectiveSpaceToSpec k 1)
  letI : IsNoetherianRing (B.presheaf.stalk x) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian B x
  apply regularPoint_of_normal_of_ringKrullDim_le_one B hnormal x
  exact (ringKrullDim_stalk_le_topologicalKrullDim B x).trans
    (dimension_eq_one g hsurj).le

end KltDP.Geometry.FiniteProjectiveLineCurveGeometry

#check @KltDP.Geometry.FiniteProjectiveLineCurveGeometry.structure_isProper
#check @KltDP.Geometry.FiniteProjectiveLineCurveGeometry.dimension_eq_one
#check @KltDP.Geometry.FiniteProjectiveLineCurveGeometry.regularPoint
#print axioms KltDP.Geometry.FiniteProjectiveLineCurveGeometry.structure_isProper
#print axioms KltDP.Geometry.FiniteProjectiveLineCurveGeometry.dimension_eq_one
#print axioms KltDP.Geometry.FiniteProjectiveLineCurveGeometry.regularPoint
