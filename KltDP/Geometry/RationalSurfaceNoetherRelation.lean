import KltDP.Geometry.BirationalOverNoetherSum
import KltDP.Examples.ProjectiveLineProductRationality
import KltDP.Examples.ProjectiveLineProductCanonicalInvariants

/-!
# The original Noether relation on a rational regular surface

The given actual birational correspondence to the affine plane is compared
with the existing projective-product chart. The constructed common resolution
preserves the original Noether sum, whose projective-product value is ten.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison SmoothCanonicalCartierRepresentative
  SmoothCanonicalCartierExterior
open KltDP.Examples.FrobeniusStageZeroProjective

/-- A regular projective surface birational over its original field to the
actual affine plane satisfies K² + ρ = 10 for any original canonical divisor. -/
theorem NormalProjectiveSurface.noetherRelation_of_birationalOver_affinePlane
    {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hrational : Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    S.NoetherRelationFor hS K := by
  let T : NormalProjectiveSurface k := projectiveProductSurface
  have hT : ∀ t : T.Point, RegularPoint T.toScheme t :=
    KltDP.Examples.FrobeniusRulingClassPairing.baseRegular
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hT
  let KT := cartierRepresentative T.structureMorphism
  let eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2 :=
    representativeIsoExterior T.structureMorphism
  have hST : Scheme.BirationalOver S.structureMorphism T.structureMorphism :=
    hrational.trans KltDP.Examples.ProjectiveLineProductRationality.birationalOver_affinePlane.symm
  change S.intersectionPairing hS K K + (S.picardRank : ℤ) = 10
  calc
    S.intersectionPairing hS K K + (S.picardRank : ℤ) =
        T.intersectionPairing hT KT KT + (T.picardRank : ℤ) :=
      canonical_square_add_picardRank_eq_of_birationalOver S T hS hT hST K KT eK eKT
    _ = 10 := KltDP.Examples.ProjectiveLineProductCanonicalInvariants.noetherRelation

end KltDP.Geometry

#check @KltDP.Geometry.NormalProjectiveSurface.noetherRelation_of_birationalOver_affinePlane
#print axioms KltDP.Geometry.NormalProjectiveSurface.noetherRelation_of_birationalOver_affinePlane
