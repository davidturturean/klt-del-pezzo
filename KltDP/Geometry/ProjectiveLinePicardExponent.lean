import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.TensorInvertibleSheaf
import Mathlib.Algebra.Group.Hom.Basic

/-!
# An injective integer exponent on the actual projective-line Picard group

An original Picard unit has an actual module-sheaf representative. Its
proved local invertibility gives standard-chart transitions. Their
exponent is unchanged by actual isomorphisms, additive under the original
tensor product, and zero exactly on the identity class. This constructs
an injective homomorphism to the additive integers, written with the
multiplicative type tag. No divisor-degree comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveLinePicardExponent

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

local instance picardExponentMonoidal : MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

/-- The actual module-sheaf representative, with local invertibility derived from its Picard unit. -/
def representative (p : (projectiveSpace k 1).Pic) :
    InvertibleSheaf (projectiveSpace k 1) := by
  let a : (Skeleton (projectiveSpace k 1).Modules)ˣ := p
  let M : (projectiveSpace k 1).Modules :=
    (fromSkeleton (projectiveSpace k 1).Modules).obj a.val
  have hM : toSkeleton M = a.val := Quotient.out_eq a.val
  exact ⟨M, SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton M (hM.symm ▸ a.isUnit)⟩

/-- This is a representative of the original class, not a replacement Picard object. -/
theorem representative_class (p : (projectiveSpace k 1).Pic) :
    toSkeleton (representative k p).obj =
      (p : Skeleton (projectiveSpace k 1).Modules) :=
  Quotient.out_eq (p : Skeleton (projectiveSpace k 1).Modules)

/-- The integer computed from an actual representative's original overlap transition. -/
def value (p : (projectiveSpace k 1).Pic) : ℤ :=
  ProjectiveLineSheafExponent.exponent k (representative k p)

/-- Every original representative of this class computes the same integer. -/
theorem value_eq_of_class (p : (projectiveSpace k 1).Pic)
    (L : InvertibleSheaf (projectiveSpace k 1))
    (h : toSkeleton L.obj = (p : Skeleton (projectiveSpace k 1).Modules)) :
    value k p = ProjectiveLineSheafExponent.exponent k L := by
  obtain ⟨e⟩ := (show Nonempty ((representative k p).obj ≅ L.obj) from
    Quotient.exact ((representative_class k p).trans h.symm))
  exact ProjectiveLineSheafExponent.exponent_eq_of_iso k (representative k p) L e

/-- Passing an original line bundle to its actual Picard class preserves its exponent. -/
theorem value_toPic (L : InvertibleSheaf (projectiveSpace k 1)) :
    value k L.toPic = ProjectiveLineSheafExponent.exponent k L :=
  value_eq_of_class k L.toPic L (InvertibleSheaf.toPic_val L).symm

/-- The actual identity class has zero exponent. -/
theorem value_one : value k (1 : (projectiveSpace k 1).Pic) = 0 := by
  have h : toSkeleton (representative k 1).obj =
      toSkeleton (𝟙_ (projectiveSpace k 1).Modules) := by
    simpa only [Skeleton.one_eq] using representative_class k 1
  obtain ⟨e⟩ := (show Nonempty ((representative k 1).obj ≅
    𝟙_ (projectiveSpace k 1).Modules) from Quotient.exact h)
  exact ProjectiveLineSheafExponent.exponent_eq_zero_of_iso_unit k (representative k 1)
    (e ≪≫ PresheafOfModules.sheafTensorUnitIso (projectiveSpace k 1).sheaf.val
      (projectiveSpace k 1).ringCatSheaf.cond)

/-- Multiplication in the original tensor Picard group adds transition exponents. -/
theorem value_mul (p q : (projectiveSpace k 1).Pic) :
    value k (p * q) = value k p + value k q := by
  have h : toSkeleton (representative k (p * q)).obj =
      toSkeleton ((representative k p).obj ⊗ (representative k q).obj) := by
    rw [Skeleton.toSkeleton_tensorObj, representative_class, representative_class,
      representative_class]
    rfl
  obtain ⟨e⟩ := (show Nonempty ((representative k (p * q)).obj ≅
    (representative k p).obj ⊗ (representative k q).obj) from Quotient.exact h)
  exact ProjectiveLineSheafExponent.exponent_eq_add_of_tensorIso k
    (representative k p) (representative k q) (representative k (p * q)) e

/-- The exponent is a homomorphism from the original Picard group to the additive integers. -/
def hom : (projectiveSpace k 1).Pic →* Multiplicative ℤ where
  toFun p := Multiplicative.ofAdd (value k p)
  map_one' := congrArg Multiplicative.ofAdd (value_one k)
  map_mul' p q := congrArg Multiplicative.ofAdd (value_mul k p q)

/-- Exponent zero is exactly the identity class in the original Picard group. -/
theorem value_eq_zero_iff (p : (projectiveSpace k 1).Pic) :
    value k p = 0 ↔ p = 1 := by
  constructor
  · intro hp
    let e := ProjectiveLineSheafExponent.unitIsoOfExponentZero k (representative k p) hp
    apply Units.ext
    change (p : Skeleton (projectiveSpace k 1).Modules) = (1 : Skeleton _)
    rw [← representative_class k p, Skeleton.one_eq]
    exact Quotient.sound ⟨e ≪≫
      (PresheafOfModules.sheafTensorUnitIso (projectiveSpace k 1).sheaf.val
        (projectiveSpace k 1).ringCatSheaf.cond).symm⟩
  · rintro rfl
    exact value_one k

/-- Distinct actual Picard classes have distinct transition exponents. -/
theorem hom_injective : Function.Injective (hom k) := by
  apply (injective_iff_map_eq_one (hom k)).mpr
  intro p hp
  apply (value_eq_zero_iff k p).mp
  exact congrArg Multiplicative.toAdd hp

end KltDP.Geometry.ProjectiveLinePicardExponent
