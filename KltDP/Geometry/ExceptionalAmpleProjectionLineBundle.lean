import KltDP.Geometry.ExceptionalAmpleProjection
import KltDP.Geometry.PositiveSquareNefNullLocus
import KltDP.Geometry.ActualExceptionalIncidence

/-!
# An original nef and big line bundle with precisely the exceptional null locus

Clear the denominators of the previously constructed original rational Picard
class. Its representative is an actual invertible sheaf on the original source.
The degree and square comparisons retain that exact positive multiple. Taking
the automatically finite type of all original contracted primes gives the whole
original exceptional support, including the empty case.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u v

namespace KltDP.Geometry.ExceptionalAmpleProjection

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  {I : Type v} [Fintype I] (C : I → S.PrimeCurve)
  {X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π) (hinj : Function.Injective C)
  (hcontracted : ∀ i, IsExceptionalCurve π (C i))

include hπ hbir hinj hcontracted in
/-- An actual integral representative of a positive multiple of the exact
projection has nonnegative degrees, positive square, and precisely the original
family as its degree-zero prime curves. -/
theorem exists_nef_positive_integral_multiple (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) :
    ∃ n : ℕ, 0 < n ∧ ∃ L : InvertibleSheaf S.toScheme,
      lineClass S L = (n : ℚ) • projectedClass S hregular C (lineClass S H) ∧
      Positivity.IsNef S.structureMorphism L ∧
      0 < S.selfIntersection hregular L ∧
      ∀ E : S.PrimeCurve, E.restrictionDegree L = 0 ↔ E ∈ Set.range C := by
  let z := projectedClass S hregular C (lineClass S H)
  obtain ⟨n, hn, p, hp⟩ := S.rationalPicard_exists_positive_integral_multiple z
  obtain ⟨A, hA⟩ := cartierPicardClass_surjective S.toScheme p.toMul
  let L := cartierDivisorInvertibleSheaf S.toScheme A
  have hclass : lineClass S L = (n : ℚ) • z := by
    change S.picardTensorInclusion (Additive.ofMul (cartierPicardClass S.toScheme A)) = _
    rw [hA, ofMul_toMul, hp]
  have hnq : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hdegree (E : S.PrimeCurve) :
      (E.restrictionDegree L : ℚ) = (n : ℚ) * S.rationalPicardRestrictionDegree E z := by
    rw [← degree_lineClass S L E, hclass, map_smul, smul_eq_mul]
  have hnef : Positivity.IsNef S.structureMorphism L := by
    apply (Positivity.isNef_iff_forall_primeCurve S L).mpr
    intro E
    have hnonneg : (0 : ℚ) ≤ (E.restrictionDegree L : ℚ) := by
      rw [hdegree]
      exact mul_nonneg hnq.le (degree_projectedClass_nonneg
        S hregular C π hπ hbir hinj hcontracted H hH E)
    exact_mod_cast hnonneg
  have hpositive : 0 < S.selfIntersection hregular L := by
    have hsq : S.rationalPicardIntersectionBilinForm hregular
        (lineClass S L) (lineClass S L) = (S.selfIntersection hregular L : ℚ) :=
      S.rationalPicardIntersectionBilinForm_inclusion hregular
        (Additive.ofMul L.toPic) (Additive.ofMul L.toPic)
    have hpos : (0 : ℚ) < (S.selfIntersection hregular L : ℚ) := by
      rw [← hsq, hclass, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      exact mul_pos hnq (mul_pos hnq (square_projectedClass_pos
        S hregular C π hπ hbir hinj hcontracted H hH))
    exact_mod_cast hpos
  refine ⟨n, hn, L, hclass, hnef, hpositive, ?_⟩
  intro E
  constructor
  · intro hz
    have h := hdegree E
    rw [hz, Int.cast_zero] at h
    have hzero : S.rationalPicardRestrictionDegree E z = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hnq)
    exact (degree_projectedClass_eq_zero_iff
      S hregular C π hπ hbir hinj hcontracted H hH E).mp hzero
  · intro hE
    have hz := (degree_projectedClass_eq_zero_iff
      S hregular C π hπ hbir hinj hcontracted H hH E).mpr hE
    have h := hdegree E
    rw [hz, mul_zero] at h
    exact_mod_cast h

section Smooth

variable [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance source_isSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

include hπ hbir hinj hcontracted in
/-- The exact positive integral multiple is nef and big, and its actual null
locus is the union of the original contracted curves in the supplied family. -/
theorem exists_nef_big_integral_multiple (H : InvertibleSheaf S.toScheme)
    (hH : AmpleSerre.IsAmple H) :
    ∃ n : ℕ, 0 < n ∧ ∃ L : InvertibleSheaf S.toScheme,
      lineClass S L = (n : ℚ) •
        projectedClass S S.regularPoints_of_isSmooth C (lineClass S H) ∧
      Positivity.IsNef S.structureMorphism L ∧
      0 < S.selfIntersection S.regularPoints_of_isSmooth L ∧
      Positivity.IsBig S.structureMorphism L ∧
      Positivity.nullLocus S.structureMorphism L = ⋃ i, (C i : Set S.toScheme) ∧
      ∀ E : S.PrimeCurve, E.restrictionDegree L = 0 ↔ E ∈ Set.range C := by
  obtain ⟨n, hn, L, hclass, hnef, hpositive, hdegree⟩ :=
    exists_nef_positive_integral_multiple S S.regularPoints_of_isSmooth C
      π hπ hbir hinj hcontracted H hH
  refine ⟨n, hn, L, hclass, hnef, hpositive,
    NefPositiveSelfIntersectionBig.isBig S L hnef hpositive, ?_, hdegree⟩
  rw [PositiveSquareNefNullLocus.nullLocus_eq_union S L hnef hpositive]
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨E, hE, hx⟩
    obtain ⟨i, rfl⟩ := (hdegree E).mp hE
    exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨C i, (hdegree (C i)).mpr ⟨i, rfl⟩, hx⟩

end Smooth

end KltDP.Geometry.ExceptionalAmpleProjection

namespace KltDP.Geometry.ExceptionalAmpleProjection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)

local instance original_source_isSmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

/-- The original projected rational class for all original contracted primes;
their finite type is derived from the original proper birational map. -/
def originalProjectedClass (z : S.RationalPicard) : S.RationalPicard := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI := Fintype.ofFinite (ActualExceptionalIncidence.Vertices π)
  exact projectedClass S S.regularPoints_of_isSmooth
    (fun E : ActualExceptionalIncidence.Vertices π => E.val) z

include hπ in
/-- No enumeration, finiteness, matrix-sign, or exceptional-coverage premise is
needed for the whole original exceptional support. The line bundle realizes
the exact positive multiple of the original projected class. -/
theorem exists_nef_big_original_exceptional_nullLocus
    (H : InvertibleSheaf S.toScheme) (hH : AmpleSerre.IsAmple H) :
    ∃ n : ℕ, 0 < n ∧ ∃ L : InvertibleSheaf S.toScheme,
      lineClass S L = (n : ℚ) • originalProjectedClass π hbir (lineClass S H) ∧
      Positivity.IsNef S.structureMorphism L ∧
      0 < S.selfIntersection S.regularPoints_of_isSmooth L ∧
      Positivity.IsBig S.structureMorphism L ∧
      Positivity.nullLocus S.structureMorphism L = ActualExceptionalLocus.primeSupport π ∧
      ∀ E : S.PrimeCurve, E.restrictionDegree L = 0 ↔ IsExceptionalCurve π E := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI := Fintype.ofFinite (ActualExceptionalIncidence.Vertices π)
  obtain ⟨n, hn, L, hclass, hnef, hpositive, hbig, hnull, hdegree⟩ :=
    exists_nef_big_integral_multiple S
      (fun E : ActualExceptionalIncidence.Vertices π => E.val)
      π hπ hbir Subtype.val_injective (fun E => E.property) H hH
  refine ⟨n, hn, L, hclass, hnef, hpositive, hbig,
    hnull.trans (ActualExceptionalIncidence.union_eq_primeSupport π), ?_⟩
  intro E
  rw [hdegree]
  constructor
  · rintro ⟨F, rfl⟩
    exact F.property
  · intro hE
    exact ⟨⟨E, hE⟩, rfl⟩

end KltDP.Geometry.ExceptionalAmpleProjection

#check @KltDP.Geometry.ExceptionalAmpleProjection.exists_nef_big_original_exceptional_nullLocus
#print axioms KltDP.Geometry.ExceptionalAmpleProjection.exists_nef_positive_integral_multiple
#print axioms KltDP.Geometry.ExceptionalAmpleProjection.exists_nef_big_original_exceptional_nullLocus
