import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.SurfaceCohomologyVanishing

/-!
# Intrinsic line degree on the actual prime-curve scheme

For the original integral projective curve, degree is the Euler difference
`χ(L) - χ(O_C)` of Stacks 0AYR. The field action is always that of `C.toSpec`.
No smoothness or regularity of the curve is needed. Grothendieck vanishing
proves the bound one, so the expression is its actual H0/H1 finrank difference.
Finite-dimensionality in these two degrees remains an explicit contract;
the theorem below proves that it suffices for all degrees.

Degree is invariant under actual module-sheaf isomorphisms and descends to
the existing sheaf Picard group. Tensor additivity is not asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace ModuleCohomology

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- Actual coefficient isomorphisms preserve the finite-dimensionality of
the cohomology with the original structure morphism's scalar action. -/
theorem finiteDimensional_iff_of_iso
    (f : Y ⟶ Spec (CommRingCat.of k)) {M N : Y.Modules}
    (e : M ≅ N) (n : ℕ) :
    FiniteDimensional k ((baseFunctor f n).obj M) ↔
      FiniteDimensional k ((baseFunctor f n).obj N) := by
  constructor
  · intro h
    letI := h
    exact ((baseFunctor f n).mapIso e).toLinearEquiv.finiteDimensional
  · intro h
    letI := h
    exact ((baseFunctor f n).mapIso e.symm).toLinearEquiv.finiteDimensional

end ModuleCohomology

namespace NormalProjectiveSurface.PrimeCurve

open ModuleCohomology

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  (C : X.PrimeCurve)

/-- The original curve structure morphism is proper by its proved
projective embedding. -/
theorem toSpec_isProper : IsProper C.toSpec := C.projective.isProper

/-- The actual cohomology of every coefficient module vanishes above one,
including when this integral projective prime curve is singular. -/
theorem cohomology_subsingleton (M : C.toScheme.Modules)
    (n : ℕ) (hn : 1 < n) : Subsingleton (H M n) := by
  apply scheme_H_subsingleton_of_dimension_lt C.toScheme M n
  rw [C.dimension_one_toScheme]
  exact_mod_cast hn

/-- All higher groups are finite-dimensional because they are zero. -/
theorem cohomology_finiteDimensional_of_one_lt (M : C.toScheme.Modules)
    (n : ℕ) (hn : 1 < n) :
    FiniteDimensional k ((baseFunctor C.toSpec n).obj M) := by
  letI := baseModule C.toSpec M n
  letI : Subsingleton ((baseFunctor C.toSpec n).obj M) :=
    C.cohomology_subsingleton M n hn
  exact Module.Finite.of_surjective (0 : k →ₗ[k] H M n)
    (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- The only remaining finiteness inputs are the original H0 and H1.
No proper-cohomology finiteness theorem is assumed by this equivalence. -/
theorem cohomology_finiteDimensional_iff (M : C.toScheme.Modules) :
    (∀ n, FiniteDimensional k ((baseFunctor C.toSpec n).obj M)) ↔
      FiniteDimensional k ((baseFunctor C.toSpec 0).obj M) ∧
        FiniteDimensional k ((baseFunctor C.toSpec 1).obj M) := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ n
    rcases n with _ | (_ | n)
    · exact h0
    · exact h1
    · exact C.cohomology_finiteDimensional_of_one_lt M (n + 2) (by omega)

/-- Bound one computes the same finsum Euler expression. -/
theorem eulerCharacteristic_eq_truncated_one (M : C.toScheme.Modules) :
    eulerCharacteristic C.toSpec M = truncatedEuler C.toSpec M 1 :=
  eulerCharacteristic_eq_truncatedEuler C.toSpec M 1
    (C.cohomology_subsingleton M)

/-- On the actual prime curve the Euler expression has only two terms.
The finranks represent cohomological dimensions whenever the two low
groups satisfy the preceding explicit finiteness contract. -/
theorem eulerCharacteristic_eq_h0_sub_h1 (M : C.toScheme.Modules) :
    eulerCharacteristic C.toSpec M =
      (cohomologyDimension C.toSpec M 0 : ℤ) -
        (cohomologyDimension C.toSpec M 1 : ℤ) := by
  rw [C.eulerCharacteristic_eq_truncated_one M]
  simp [truncatedEuler, Finset.sum_range_succ, sub_eq_add_neg]

/-- The intrinsic line degree expression of Stacks 0AYR on the original
curve. Its finite cohomology interpretation uses the low-degree contract
above for this sheaf and the structure sheaf. -/
def lineDegree (L : InvertibleSheaf C.toScheme) : ℤ :=
  eulerCharacteristic C.toSpec L.obj -
    eulerCharacteristic C.toSpec (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf)

/-- Degree evaluated entirely on the four original low cohomology groups. -/
theorem lineDegree_eq_h0_sub_h1 (L : InvertibleSheaf C.toScheme) :
    C.lineDegree L =
      ((cohomologyDimension C.toSpec L.obj 0 : ℤ) -
        (cohomologyDimension C.toSpec L.obj 1 : ℤ)) -
      ((cohomologyDimension C.toSpec
        (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) 0 : ℤ) -
        (cohomologyDimension C.toSpec
          (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf) 1 : ℤ)) := by
  unfold lineDegree
  rw [C.eulerCharacteristic_eq_h0_sub_h1, C.eulerCharacteristic_eq_h0_sub_h1]

/-- The actual induced cohomology isomorphisms give degree invariance. -/
theorem lineDegree_eq_of_iso {L M : InvertibleSheaf C.toScheme}
    (e : L.obj ≅ M.obj) : C.lineDegree L = C.lineDegree M := by
  unfold lineDegree
  rw [eulerCharacteristic_eq_of_iso C.toSpec e]

/-- The structure-sheaf line has degree zero. -/
@[simp]
theorem lineDegree_trivial :
    C.lineDegree (InvertibleSheaf.trivial C.toScheme) = 0 := by
  simp only [lineDegree, InvertibleSheaf.trivial_obj, sub_self]

/-- An actual trivialization suffices for degree zero. -/
theorem lineDegree_eq_zero_of_iso_unit (L : InvertibleSheaf C.toScheme)
    (e : L.obj ≅ _root_.SheafOfModules.unit C.toScheme.ringCatSheaf) :
    C.lineDegree L = 0 :=
  (C.lineDegree_eq_of_iso (M := InvertibleSheaf.trivial C.toScheme) e).trans
    C.lineDegree_trivial

/-- Degree on the original sheaf Picard group. This is a function; no
additivity under tensor product is included in its type. -/
def picardDegree (p : C.toScheme.Pic) : ℤ :=
  picardEulerValue C.toSpec p - picardEulerValue C.toSpec 1

/-- Descent agrees with the degree of the very same line bundle. -/
@[simp]
theorem picardDegree_toPic (L : InvertibleSheaf C.toScheme) :
    C.picardDegree L.toPic = C.lineDegree L := by
  unfold picardDegree lineDegree
  rw [picardEulerValue_toPic, picardEulerValue_one]

/-- The Picard identity has degree zero. -/
@[simp]
theorem picardDegree_one : C.picardDegree 1 = 0 := by
  simp only [picardDegree, sub_self]

/-- Any two representatives of the same original Picard class have the
same intrinsic degree. -/
theorem lineDegree_eq_of_toPic_eq {L M : InvertibleSheaf C.toScheme}
    (h : L.toPic = M.toPic) : C.lineDegree L = C.lineDegree M := by
  rw [← C.picardDegree_toPic L, ← C.picardDegree_toPic M, h]

end NormalProjectiveSurface.PrimeCurve

end KltDP.Geometry
