import KltDP.Geometry.ClosedPoints
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Residue-field degree of finite cycles of closed points

The scalar action on each residue field comes from the original structure
morphism. Finite cycles use the existing `Finsupp` type, and their degree is
the existing linear-combination map with these residue-field dimensions as
weights. Over an algebraically closed field, the proved canonical residue
isomorphism makes every closed-point weight equal to one.

These are degrees of zero-cycles. Identifying a line bundle with a divisor,
descending degree through principal divisors, and defining surface
intersection numbers require separate geometric proofs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ClosedPointCycle

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- An actual closed point of the original scheme. -/
abbrev Point (X : Scheme.{u}) := {x : X // IsClosed ({x} : Set X)}

/-- Finite integral zero-cycles on the original closed points. -/
abbrev Cycle (X : Scheme.{u}) := Point X →₀ ℤ

/-- The dimension of the actual residue field with its original base action.
For locally finite type schemes, closed-point residue extensions are finite. -/
def residueDegree (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : Point X) : ℕ :=
  letI := (baseToResidueFieldMap f x.1).hom.toAlgebra
  Module.finrank k (X.residueField x.1)

/-- The dimension in the degree definition is the dimension of a finite
extension, by the existing Zariski-lemma proof for this exact structure map. -/
theorem residueField_moduleFinite (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : Point X) :
    letI := (baseToResidueFieldMap f x.1).hom.toAlgebra
    Module.Finite k (X.residueField x.1) :=
  baseToResidueFieldMap_finite f x.1 x.2

/-- Algebraic closedness identifies the original base-to-residue map;
no independently chosen scalar structure is used. -/
theorem residueDegree_eq_one [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : Point X) :
    residueDegree f x = 1 := by
  letI := (baseToResidueFieldMap f x.1).hom.toAlgebra
  change Module.finrank k (X.residueField x.1) = 1
  apply _root_.finrank_eq_one (1 : X.residueField x.1) one_ne_zero
  intro y
  obtain ⟨a, ha⟩ := (baseToResidueFieldMap_bijective f x.1 x.2).surjective y
  refine ⟨a, ?_⟩
  change (baseToResidueFieldMap f x.1).hom a * 1 = y
  simpa only [mul_one] using ha

/-- Residue-field-weighted degree, extended linearly over finite cycles. -/
def degree (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : Cycle X →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun x : Point X => (residueDegree f x : ℤ))

/-- Each coefficient is weighted by the dimension of its own residue field. -/
theorem degree_apply (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (D : Cycle X) :
    degree f D = D.sum (fun x n => n * (residueDegree f x : ℤ)) := by
  simp only [degree, Finsupp.linearCombination_apply, zsmul_eq_mul, Int.cast_id]

/-- The degree of a closed point with an arbitrary integral multiplicity. -/
@[simp]
theorem degree_single (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : Point X) (n : ℤ) :
    degree f (Finsupp.single x n) = n * (residueDegree f x : ℤ) := by
  simp only [degree, Finsupp.linearCombination_single, zsmul_eq_mul, Int.cast_id]

/-- Over an algebraically closed field, the residue weights are all one. -/
theorem degree_eq_sum [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (D : Cycle X) :
    degree f D = D.sum (fun _ n => n) := by
  simp only [degree_apply, residueDegree_eq_one, Nat.cast_one, mul_one]

/-- The negative of the cycle of one actual closed point has degree minus one.
This is a zero-cycle assertion; it does not identify a line-bundle degree. -/
theorem degree_negative_point [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : Point X) :
    degree f (Finsupp.single x (-1)) = -1 := by
  simp only [degree_single, residueDegree_eq_one, Nat.cast_one, mul_one]

end KltDP.Geometry.ClosedPointCycle
