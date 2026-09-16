import KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine
import KltDP.Examples.FrobeniusMultiCentreFiberProjectiveLine
import KltDP.Examples.FrobeniusMultiCentreRetainedGram
import KltDP.Examples.FrobeniusGraphFiberDisjointSPn

/-!
# The original retained curves form a disjoint family of projective lines

The family consists of the actual global strict graph, strict fibres and old
exceptional components. Its inclusions are the original closed immersions,
its ideal lines are the original kernel lines, and its classes are exactly
those used in the proved geometric retained Gram matrix. The projective-line
isomorphisms and support disjointness are proved for these same objects.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRetainedCurves

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreChainPicard FrobeniusMultiCentreGraphCartierStrict
  FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentreGraphContacts
  FrobeniusMultiCentreFiberContacts FrobeniusGraphFiberDisjointSPn
  FrobeniusMultiCentreGraphProjectiveLine FrobeniusMultiCentreFiberProjectiveLine
  FrobeniusMultiCentreRetainedGram

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

variable (n : ℕ) (a : Fin n → k)

/-- The actual independently constructed retained curves. -/
def retainedCurve : FrobeniusCharacteristicTwo.RetainedLabel n → Scheme.{u}
  | .inl _ => graphStrict 2 n a
  | .inr (.inl i) => fiberStrict 2 n a i
  | .inr (.inr i) => exceptionalCurve 1 n a i (.inl (0 : Fin 1))

/-- Their original inclusions into the original surface. -/
def retainedInclusion : (r : FrobeniusCharacteristicTwo.RetainedLabel n) →
    retainedCurve n a r ⟶ multiSurface 2 n a
  | .inl _ => graphStrictι 2 n a
  | .inr (.inl i) => fiberStrictι 2 n a i
  | .inr (.inr i) => exceptionalCurveι 1 n a i (.inl (0 : Fin 1))

instance retainedInclusion_isClosedImmersion (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    IsClosedImmersion (retainedInclusion n a r) := by
  rcases r with r | (i | i) <;> dsimp [retainedInclusion] <;> infer_instance

variable (ha : Function.Injective a)

/-- Each same original retained curve is isomorphic to the projective line. -/
def retainedCurveIsoProjectiveLine : (r : FrobeniusCharacteristicTwo.RetainedLabel n) →
    retainedCurve n a r ≅ projectiveSpace k 1
  | .inl _ => globalGraphIsoProjectiveLine 2 n a
  | .inr (.inl i) => globalFiberIsoProjectiveLine 1 n a ha i
  | .inr (.inr i) => curveIso 1 n a ha i (.inl (0 : Fin 1))

/-- The original ideal line of each retained curve. -/
def retainedKernelLine : FrobeniusCharacteristicTwo.RetainedLabel n →
    InvertibleSheaf (multiSurface 2 n a)
  | .inl _ => multiGraphStrictKernelLine 1 n a ha
  | .inr (.inl i) => fiberKernelLine 1 n a ha i
  | .inr (.inr i) => exceptionalKernelLine 1 n a ha i (.inl (0 : Fin 1))

theorem retainedKernelLine_obj (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedKernelLine n a ha r).obj = schemeKernelIdeal (retainedInclusion n a r) := by
  rcases r with r | (i | i) <;> rfl

/-- These same curve kernels are the classes whose geometric matrix was computed. -/
theorem retainedClass_eq_kernel (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    retainedClass n a ha r = -Additive.ofMul (retainedKernelLine n a ha r).toPic := by
  rcases r with r | (i | i) <;> rfl

include ha in
/-- Distinct retained curves have disjoint supports in the original surface. -/
theorem retainedInclusion_disjoint (r s : FrobeniusCharacteristicTwo.RetainedLabel n)
    (hrs : r ≠ s) :
    Disjoint (Set.range (retainedInclusion n a r).base) (Set.range (retainedInclusion n a s).base) := by
  rcases r with ⟨⟩ | (i | i) <;> rcases s with ⟨⟩ | (j | j)
  · exact (hrs rfl).elim
  · exact graphStrict_fiberStrict_disjoint' 1 n a j
  · exact graphStrict_disjoint_exceptional_same 1 n a j (0 : Fin 1)
  · exact (graphStrict_fiberStrict_disjoint' 1 n a i).symm
  · exact fiberStrict_disjoint 2 n a ha (fun hij => hrs (congrArg (fun x : Fin n =>
      (Sum.inr (Sum.inl x) : FrobeniusCharacteristicTwo.RetainedLabel n)) hij))
  · by_cases hij : i = j
    · subst j
      exact fiberStrict_disjoint_exceptional_same 1 n a i (0 : Fin 1)
    · exact fiberStrict_disjoint_exceptional 1 n a ha hij (.inl (0 : Fin 1))
  · exact (graphStrict_disjoint_exceptional_same 1 n a i (0 : Fin 1)).symm
  · by_cases hij : j = i
    · subst j
      exact (fiberStrict_disjoint_exceptional_same 1 n a i (0 : Fin 1)).symm
    · exact (fiberStrict_disjoint_exceptional 1 n a ha hij (.inl (0 : Fin 1))).symm
  · exact exceptionalSupport_disjoint_of_ne 1 n a ha (fun hij => hrs (congrArg (fun x : Fin n =>
      (Sum.inr (Sum.inr x) : FrobeniusCharacteristicTwo.RetainedLabel n)) hij)) _ _

end KltDP.Examples.FrobeniusMultiCentreRetainedCurves
