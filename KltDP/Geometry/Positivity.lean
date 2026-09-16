import Mathlib.Data.Rat.Cast.Order
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Geometry.CartierEulerPairing

/-!
# Positivity of line bundles: nef, big, semi-ample, and Keel's exceptional locus (F12)

The accepted tree has no positivity notions at all (no `IsNef`, `IsBig`, `IsAmple`, semi-ampleness,
null locus), and the pinned Mathlib has none either (no `IsNef`/`IsBig`/semi-ample anywhere in
`Mathlib/AlgebraicGeometry`), so everything here is new. The definitions follow Keel, *Basepoint
freeness for nef and big line bundles in positive characteristic*, Annals of Mathematics 149 (1999),
253–286, introduction, pages 253–254 (texts quoted in `laneE/F10_LITERALS.md`):

* `IsGloballyGenerated M`: some free sheaf of modules surjects onto `M`.
* `IsSemiample L`: some positive tensor power of `L` is globally generated (Keel, introduction:
  "Once a line bundle `L` has a section, one expects the positive tensor powers `L^{⊗n}` to have
  more sections. If some such power is globally generated, one says that `L` is *semi-ample*").
  Powers are taken in the accepted Picard group `X.Pic`.
* `IsBig f L`: the global sections of the powers satisfy
  `c · n^{dim X} ≤ h⁰(L^n)` for arbitrarily large `n`, for some positive rational `c`.
  The coefficient must allow values below one. On integral projective varieties over an infinite
  field, this is the positive-volume growth criterion (de Fernex--Ein--Mustaţă, *Vanishing theorems
  and singularities in birational geometry*, 2014, §1.4.2, Theorem 1.4.13 and Lemma 1.4.14).
  Rational and real positive thresholds are mathematically equivalent by density of the rationals.
  This file does not prove that scalar equivalence or the comparison with Keel's birational and
  intersection forms. The general-scheme definition also requires dimension and cohomology
  finiteness hypotheses for its conventional interpretation; a single aggregate growth bound
  does not assert bigness on every component of a reducible scheme.
* `subvarietyDegree f L Z`: the degree of `L` on a subvariety in the accepted Stacks 0AYR
  convention `deg L = χ(L) − χ(O)`, which on a prime curve of a surface is the accepted F03
  `PrimeCurve.restrictionDegree` (`subvarietyDegree_eq_restrictionDegree`).
* `IsNef f L`: nonnegative degree on every one-dimensional subvariety (Keel: "`L · C ≥ 0` for every
  irreducible curve `C ⊂ X`").
* `IsExceptionalSubvariety f L Z` and `nullLocus f L`: Keel's Definition 0.1 — a positive-dimensional
  irreducible subvariety on which `L` is not big, and the closure of the union of all of them;
  `nullLocusScheme`, `nullLocusInclusion`, `nullLocusRestrict` give it the reduced induced structure
  (the accepted `Scheme.IdealSheafData.vanishingIdeal` glued subscheme) and `L|_{E(L)}`.

The surface characterisation of `E(L)` is proved in `Geometry/PositivitySurface.lean` under
explicit dimension and bigness-to-degree comparison hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.Positivity

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Subvariety

variable {X : Scheme.{u}} (Z : IrreducibleCloseds X)

/-- The subvariety as a closed subset. -/
def closedSubset : Closeds X := ⟨Z, Z.isClosed⟩

@[simp] theorem coe_closedSubset : (closedSubset Z : Set X) = (Z : Set X) := rfl

/-- The reduced induced closed subscheme structure on an irreducible closed subset (the accepted
glued vanishing-ideal construction, exactly as for prime curves). -/
def toScheme : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (closedSubset Z)).glueData.glued

/-- Its closed immersion into the ambient scheme. -/
def inclusion : toScheme Z ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (closedSubset Z)).gluedTo

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion Z) :=
  (Scheme.IdealSheafData.vanishingIdeal (closedSubset Z)).gluedTo_isClosedImmersion

@[simp] theorem range_inclusion : Set.range (inclusion Z).base = (Z : Set X) :=
  (Scheme.IdealSheafData.vanishingIdeal (closedSubset Z)).range_gluedTo

end Subvariety

/-- The topological dimension as a natural number (`0` when the dimension is `⊥` or infinite). -/
def natDim (X : Scheme.{u}) : ℕ := ((topologicalKrullDim X).unbotD 0).toNat

section GlobalSections

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- `h⁰` descends to isomorphism classes of module sheaves. -/
def skeletonHZero : Skeleton X.Modules → ℕ :=
  Quotient.lift (fun M => cohomologyDimension f M 0) (by
    intro M N h
    obtain ⟨e⟩ := h
    exact cohomologyDimension_eq_of_iso f e 0)

@[simp] theorem skeletonHZero_toSkeleton (M : X.Modules) :
    skeletonHZero f (toSkeleton M) = cohomologyDimension f M 0 := rfl

/-- `h⁰` of a Picard class. -/
def picardHZero (p : X.Pic) : ℕ := skeletonHZero f (p : Skeleton X.Modules)

@[simp] theorem picardHZero_toPic (L : InvertibleSheaf X) :
    picardHZero f L.toPic = cohomologyDimension f L.obj 0 := by
  letI := Scheme.Modules.monoidalCategory X
  unfold picardHZero
  rw [InvertibleSheaf.toPic_val]
  rfl

end GlobalSections

section Definitions

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A module sheaf is generated by global sections when some free sheaf surjects onto it. -/
def IsGloballyGenerated (M : X.Modules) : Prop :=
  ∃ (I : Type u) (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M), Epi φ

/-- **Semi-ample** (Keel, introduction): some positive tensor power is globally generated. Powers
are taken in the accepted Picard group. -/
def IsSemiample (L : InvertibleSheaf X) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ M : InvertibleSheaf X, M.toPic = L.toPic ^ n ∧ IsGloballyGenerated M.obj

/-- **Big** in the maximal-growth form, with a positive rational coefficient and arbitrarily
large exponents. The exponent is the actual power of this input Picard class.

On integral projective varieties this is the intended positive-volume criterion. Its geometric
comparison theorems are not proved here. For general schemes the totalized dimension and `h⁰`
functions require additional finiteness hypotheses for their usual interpretation. -/
def IsBig (L : InvertibleSheaf X) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    c * (n : ℚ) ^ natDim X ≤ (picardHZero f (L.toPic ^ n) : ℚ)

/-- The degree of `L` on a subvariety, in the accepted Stacks 0AYR convention
`deg L = χ(L|_Z) − χ(O_Z)`, the base field acting through `Z ⟶ X ⟶ Spec k`. -/
def subvarietyDegree (L : InvertibleSheaf X) (Z : IrreducibleCloseds X) : ℤ :=
  eulerCharacteristic (inclusion Z ≫ f) (pullbackInvertibleSheaf (inclusion Z) L).obj -
    eulerCharacteristic (inclusion Z ≫ f)
      (_root_.SheafOfModules.unit (toScheme Z).ringCatSheaf)

/-- **Nef**: nonnegative degree on every one-dimensional subvariety. -/
def IsNef (L : InvertibleSheaf X) : Prop :=
  ∀ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 → 0 ≤ subvarietyDegree f L Z

/-- **Keel, Definition 0.1**: a positive-dimensional irreducible subvariety on which `L` is not
big. -/
def IsExceptionalSubvariety (L : InvertibleSheaf X) (Z : IrreducibleCloseds X) : Prop :=
  0 < topologicalKrullDim (Z : Set X) ∧
    ¬ IsBig (inclusion Z ≫ f) (pullbackInvertibleSheaf (inclusion Z) L)

/-- **Keel's exceptional locus `E(L)`** (Definition 0.1): the closure of the union of all
exceptional subvarieties. -/
def nullLocus (L : InvertibleSheaf X) : Set X :=
  closure (⋃ Z ∈ {Z : IrreducibleCloseds X | IsExceptionalSubvariety f L Z}, (Z : Set X))

theorem isClosed_nullLocus (L : InvertibleSheaf X) : IsClosed (nullLocus f L) := isClosed_closure

theorem subset_nullLocus (L : InvertibleSheaf X) {Z : IrreducibleCloseds X}
    (hZ : IsExceptionalSubvariety f L Z) : (Z : Set X) ⊆ nullLocus f L :=
  (Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds X => (Z : Set X)) hZ).trans
    subset_closure

/-- `E(L)` as a closed subset. -/
def nullLocusClosed (L : InvertibleSheaf X) : Closeds X := ⟨nullLocus f L, isClosed_nullLocus f L⟩

/-- `E(L)` with its reduced induced scheme structure (Keel: "the closure, with reduced
structure"). -/
def nullLocusScheme (L : InvertibleSheaf X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (nullLocusClosed f L)).glueData.glued

/-- Its closed immersion into `X`. -/
def nullLocusInclusion (L : InvertibleSheaf X) : nullLocusScheme f L ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (nullLocusClosed f L)).gluedTo

instance nullLocusInclusion_isClosedImmersion (L : InvertibleSheaf X) :
    IsClosedImmersion (nullLocusInclusion f L) :=
  (Scheme.IdealSheafData.vanishingIdeal (nullLocusClosed f L)).gluedTo_isClosedImmersion

/-- `L|_{E(L)}`. -/
def nullLocusRestrict (L : InvertibleSheaf X) : InvertibleSheaf (nullLocusScheme f L) :=
  pullbackInvertibleSheaf (nullLocusInclusion f L) L

end Definitions

section Surface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- On a prime curve of a surface the subvariety degree is the accepted F03 restriction degree. -/
theorem subvarietyDegree_eq_restrictionDegree (L : InvertibleSheaf X.toScheme)
    (C : X.PrimeCurve) :
    subvarietyDegree X.structureMorphism L C.1 = C.restrictionDegree L := rfl

/-- **Nef on a surface**: nonnegative degree on every prime curve (the accepted F03 degree). -/
theorem isNef_iff_forall_primeCurve (L : InvertibleSheaf X.toScheme) :
    IsNef X.structureMorphism L ↔ ∀ C : X.PrimeCurve, 0 ≤ C.restrictionDegree L := by
  constructor
  · intro h C
    exact h C.1 C.2
  · intro h Z hZ
    exact h ⟨Z, hZ⟩

end Surface

end KltDP.Geometry.Positivity
