import KltDP.RingTheory.NormalTwistedAdjunction

/-!
# Equation-independent normal-twisted adjunction on the original affine scheme

The actual Kähler sheaf on `Spec(A/J)` is isomorphic to tilde of the
ambient top-differential module tensored with the actual dual conormal
module. These sheaf isomorphisms are equal for any two regular equations
of the same ideal, by the produced equality of their original module maps.

The target is tilde of the actual module tensor. Comparison with the sheaf
tensor of the ambient canonical and normal sheaves, restriction to common
affine refinements, and global adjunction are not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalTwistedAdjunctionChart

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hregular : (d : A) ∈ nonZeroDivisors A)

local instance normalTwistAddCommGroup :
    AddCommGroup (_root_.TensorProduct (A ⧸ J)
      (_root_.TensorProduct A (A ⧸ J) (⋀[A]^2 (KaehlerDifferential R A)))
      (Module.Dual (A ⧸ J) J.Cotangent)) :=
  Module.addCommMonoidToAddCommGroup (A ⧸ J)

/-- Actual affine Kähler sheaf adjunction retaining the original normal module. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J)))) ≅
      (ModuleCat.of (A ⧸ J)
        (((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
          Module.Dual (A ⧸ J) J.Cotangent)).tilde :=
  AffineKaehlerTildeLocalization.iso R (A ⧸ J) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of (A ⧸ J) (KaehlerDifferential R (A ⧸ J)))
      (N := ModuleCat.of (A ⧸ J)
        (((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
          Module.Dual (A ⧸ J) J.Cotangent))
      (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A J d hJ hregular)

/-- The actual affine sheaf map is independent of the chosen regular equation. -/
theorem iso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    iso R A J e hE heregular = iso R A J d hJ hregular := by
  unfold iso
  rw [KltDP.RingTheory.NormalTwistedAdjunction.equiv_eq R A J d hJ hregular e hE heregular]

end KltDP.Geometry.NormalTwistedAdjunctionChart
