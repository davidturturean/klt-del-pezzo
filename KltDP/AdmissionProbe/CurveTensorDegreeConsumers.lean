import KltDP.Literature.Stacks.CurveTensorDegree
import KltDP.Compatibility.ConstantRankSheaf
import KltDP.Geometry.TensorInvertibleSheaf
import KltDP.Geometry.WeilRestrictionDegree

/-!
# Inactive ordinary consumers of the full curve tensor-degree statement

The first import and its full-statement constant are prospective and do not
exist in the production project. Their required complete telescope is in
`required_literal_interface.md`. This text declares no literature input;
it cannot be staged as a compilable module until root separately supplies
a reviewed proof or admits that exact full published statement.

The remaining proof bodies use the original cohomology, actual sheaf
isomorphisms, original Picard units and actual restriction maps. They never
take degree additivity or a numerical framework as an extra hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open scoped BigOperators
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.AdmissionProbe.CurveTensorDegreeConsumers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Rank-one specialization of the entire finite-rank published statement,
with the original field action and original structure module retained. -/
theorem proper_invertible_tensor_euler
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (L M : InvertibleSheaf Y) :
    letI := Scheme.Modules.monoidalCategory Y
    eulerCharacteristic f (L.obj ⊗ M.obj) -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      (eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
      (eulerCharacteristic f M.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) := by
  letI := Scheme.Modules.monoidalCategory Y
  have hL : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) L.obj 1 := inferInstance
  have hM : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) M.obj 1 := inferInstance
  simpa only [Nat.mul_one, Nat.cast_one, one_mul, add_comm] using
    KltDP.Literature.Stacks.proper_curve_tensor_degree
      (Y := Y) f hdim L.obj M.obj 1 1 hL hM

/-- Multiplication of actual Picard units is represented by the tensor of
their actual locally free rank-one sheaves, so the same Euler difference adds. -/
theorem proper_picardEulerDifference_mul
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (p q : Y.Pic) :
    picardEulerValue f (p * q) - picardEulerValue f 1 =
      (picardEulerValue f p - picardEulerValue f 1) +
      (picardEulerValue f q - picardEulerValue f 1) := by
  letI := Scheme.Modules.monoidalCategory Y
  let L (a : Y.Pic) : InvertibleSheaf Y := by
    let b : (Skeleton Y.Modules)ˣ := a
    let M : Y.Modules := (fromSkeleton Y.Modules).obj b.val
    have hM : toSkeleton M = b.val := Quotient.out_eq b.val
    exact ⟨M, SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton
      (X := Y) M (hM.symm ▸ b.isUnit)⟩
  have hL (a : Y.Pic) : toSkeleton (L a).obj = (a : Skeleton Y.Modules) :=
    Quotient.out_eq (a : Skeleton Y.Modules)
  have hχ (a : Y.Pic) :
      picardEulerValue f a = eulerCharacteristic f (L a).obj := by
    change skeletonEulerValue f (a : Skeleton Y.Modules) = _
    rw [← hL a, skeletonEulerValue_toSkeleton]
  have hprod : toSkeleton (L (p * q)).obj =
      toSkeleton ((L p).obj ⊗ (L q).obj) := by
    rw [Skeleton.toSkeleton_tensorObj, hL, hL, hL]
    rfl
  obtain ⟨e⟩ := (show Nonempty ((L (p * q)).obj ≅ (L p).obj ⊗ (L q).obj) from
    Quotient.exact hprod)
  rw [hχ (p * q), hχ p, hχ q, picardEulerValue_one,
    eulerCharacteristic_eq_of_iso f e]
  exact proper_invertible_tensor_euler f hdim (L p) (L q)

/-- An actual tensor isomorphism computes the original prime-curve line
degree; it is not a replacement tensor law on abstract numerical data. -/
theorem lineDegree_eq_add_of_tensorIso
    {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (L M N : InvertibleSheaf C.toScheme)
    (e : letI := Scheme.Modules.monoidalCategory C.toScheme
      N.obj ≅ L.obj ⊗ M.obj) :
    C.lineDegree N = C.lineDegree L + C.lineDegree M := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  letI := Scheme.Modules.monoidalCategory C.toScheme
  unfold NormalProjectiveSurface.PrimeCurve.lineDegree
  rw [eulerCharacteristic_eq_of_iso C.toSpec e]
  exact proper_invertible_tensor_euler C.toSpec
    (le_of_eq C.dimension_one_toScheme) L M

/-- The previously defined intrinsic degree adds on the original curve Picard group. -/
theorem picardDegree_mul
    {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (p q : C.toScheme.Pic) :
    C.picardDegree (p * q) = C.picardDegree p + C.picardDegree q := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact proper_picardEulerDifference_mul C.toSpec
    (le_of_eq C.dimension_one_toScheme) p q

/-- The existing degree function, bundled only after its actual multiplication law. -/
def picardDegreeHom
    {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve) :
    Additive C.toScheme.Pic →+ ℤ where
  toFun p := C.picardDegree p.toMul
  map_zero' := C.picardDegree_one
  map_add' p q := picardDegree_mul C p.toMul q.toMul

/-- The original Picard pullback transports the proved degree law to restriction. -/
theorem picardRestrictionDegree_mul
    {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (p q : X.toScheme.Pic) :
    C.picardRestrictionDegree (p * q) =
      C.picardRestrictionDegree p + C.picardRestrictionDegree q := by
  unfold NormalProjectiveSurface.PrimeCurve.picardRestrictionDegree
  rw [map_mul]
  exact picardDegree_mul C _ _

/-- The existing finite prime decomposition extends first-variable additivity
to its unchanged linear form on actual Weil divisors. -/
theorem picardWeilRestrictionDegree_mul
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (p q : X.toScheme.Pic) :
    X.picardWeilRestrictionDegree (p * q) =
      X.picardWeilRestrictionDegree p + X.picardWeilRestrictionDegree q := by
  apply LinearMap.ext
  intro Z
  change X.picardWeilRestrictionDegree (p * q) Z =
    X.picardWeilRestrictionDegree p Z + X.picardWeilRestrictionDegree q Z
  simp only [NormalProjectiveSurface.picardWeilRestrictionDegree_apply,
    picardRestrictionDegree_mul, mul_add, Finset.sum_add_distrib]

/-- The actual surface Picard argument is additive and the actual Weil curve
argument retains its existing integer linearity. No symmetry is asserted. -/
def picardWeilRestrictionDegreeHom
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) :
    Additive X.toScheme.Pic →+ (X.WeilDivisor →ₗ[ℤ] ℤ) where
  toFun p := X.picardWeilRestrictionDegree p.toMul
  map_zero' := X.picardWeilRestrictionDegree_one
  map_add' p q := picardWeilRestrictionDegree_mul X p.toMul q.toMul

end KltDP.AdmissionProbe.CurveTensorDegreeConsumers
