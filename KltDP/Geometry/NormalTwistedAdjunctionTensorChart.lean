import KltDP.Geometry.NormalTwistedAdjunctionChart
import KltDP.Geometry.AffineModuleTildeTensorPullback

/-!
# Local adjunction with the actual ambient pullback and sheaf tensor

The original quotient Kähler sheaf is identified with the tensor of the
actual pulled-back ambient top-differential tilde sheaf and tilde of the
actual dual conormal module. This is a direct consumer of the produced
normal-twist chart and the proved affine tilde tensor comparison.

The result remains independent of the regular equation. Identifying the
second factor with the actual conormal sheaf dual, proving compatibility
on common affine refinements, and global adjunction remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.NormalTwistedAdjunctionTensorChart

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

local instance sheafMonoidal : MonoidalCategory (Spec (CommRingCat.of (A ⧸ J))).Modules :=
  Scheme.Modules.monoidalCategory (Spec (CommRingCat.of (A ⧸ J)))

/-- The original scalar extension of the ambient top differential module. -/
abbrev ambientModule : ModuleCat.{u} (A ⧸ J) :=
  (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj
    (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A)))

/-- The original module dual of the actual ideal conormal module. -/
abbrev normalModule : ModuleCat.{u} (A ⧸ J) :=
  ModuleCat.of (A ⧸ J) (Module.Dual (A ⧸ J) J.Cotangent)

local instance tensorTargetAddCommGroup :
    AddCommGroup (_root_.TensorProduct (A ⧸ J)
      (_root_.TensorProduct A (A ⧸ J) (⋀[A]^2 (KaehlerDifferential R A)))
      (Module.Dual (A ⧸ J) J.Cotangent)) :=
  Module.addCommMonoidToAddCommGroup (A ⧸ J)

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

set_option maxHeartbeats 800000 in
/-- The original affine adjunction chart, with the actual sheaf tensor retained. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ J)))) ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))).tilde ⊗
          (normalModule A J).tilde :=
  NormalTwistedAdjunctionChart.iso R A J d hJ hregular ≪≫
    AffineModuleTildeTensorPullback.iso (Ideal.Quotient.mk J)
      (ModuleCat.of A (⋀[A]^2 (KaehlerDifferential R A))) (normalModule A J)

/-- Equation independence is preserved by the original sheaf tensor comparisons. -/
theorem iso_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    iso R A J e hE heregular = iso R A J d hJ hregular := by
  unfold iso
  rw [NormalTwistedAdjunctionChart.iso_eq R A J d hJ hregular e hE heregular]

end KltDP.Geometry.NormalTwistedAdjunctionTensorChart
