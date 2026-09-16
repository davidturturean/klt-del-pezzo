import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.ProperCurveEuler
import KltDP.Compatibility.ConstantRankSheaf

/-!
# Ordinary rank-indexed curve degree, proposed source only

INACTIVE TEXT. The original Euler expression and constant finite-rank
predicate give the degree notation of Stacks 0AYR. Finiteness of the original
cohomology is justified in the separate interpretation module. None of the
ordinary definitions or proofs in this file asserts tensor additivity.

The structure morphism, original coefficient, rank and actual local-basis
proof are explicit. Rank zero and the empty scheme remain permitted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The constant finite-rank predicate of `ConstantRankSheaf` for a module sheaf
on a scheme, with the Zariski-site instance arguments fixed once by the original
structure sheaf. This is a transparent abbreviation: it unfolds definitionally
to `KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Y.ringCatSheaf) E r` and adds
no hypothesis. It exists so that a literal statement quoting it has binder types
that are compact constant applications rather than re-synthesized instance
proofs (which the trust auditor must reproduce syntactically). -/
abbrev IsLocallyFreeOfRankOn (Y : Scheme.{u}) (E : Y.Modules) (r : ℕ) : Prop :=
  KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Y.ringCatSheaf) E r

/-- Degree from Stacks 0AYR on the original proper scheme over the original
field, with the supplied finite constant rank witnessed by actual local bases. -/
def finiteRankDegree
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) : ℤ :=
  eulerCharacteristic f E - (r : ℤ) *
    eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)

/-- An actual sheaf isomorphism preserves the degree, using the induced
base-field linear isomorphism on every original cohomology group. -/
theorem finiteRankDegree_eq_of_iso
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) {E V : Y.Modules} (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) (e : E ≅ V) :
    finiteRankDegree f hdim E r hE =
      finiteRankDegree f hdim V r
        (KltDP.SheafOfModules.IsLocallyFreeOfRank.of_iso
          (R := Y.ringCatSheaf) hE e) := by
  unfold finiteRankDegree
  rw [eulerCharacteristic_eq_of_iso f e]

/-- The existing proper dimension bound truncates the same Euler values.
The separate interpretation theorem proves that these finranks are finite
cohomological dimensions. -/
theorem finiteRankDegree_eq_h0_sub_h1
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) :
    finiteRankDegree f hdim E r hE =
      ((cohomologyDimension f E 0 : ℤ) - (cohomologyDimension f E 1 : ℤ)) -
      (r : ℤ) *
        ((cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 0 : ℤ) -
          (cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 : ℤ)) := by
  unfold finiteRankDegree
  rw [proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim E,
    proper_eulerCharacteristic_eq_h0_sub_h1 (X := Y) f hdim
      (_root_.SheafOfModules.unit Y.ringCatSheaf)]

/-- The original structure module, with its proved rank one, has degree zero. -/
@[simp]
theorem finiteRankDegree_unit
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) :
    finiteRankDegree f hdim (_root_.SheafOfModules.unit Y.ringCatSheaf) 1
      (by infer_instance) = 0 := by
  simp only [finiteRankDegree, Nat.cast_one, one_mul, sub_self]

/-- No uniqueness of rank is imposed on the empty scheme: every supplied
finite rank gives zero because all the actual cohomology groups vanish. -/
theorem finiteRankDegree_eq_zero_of_isEmpty
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsEmpty Y]
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) :
    finiteRankDegree f hdim E r hE = 0 := by
  simp only [finiteRankDegree, eulerCharacteristic_eq_zero_of_isEmpty,
    mul_zero, sub_self]

end KltDP.Geometry.ModuleCohomology
