import KltDP.Geometry.Positivity
import KltDP.Geometry.PrimeCurveIntersectionAdditive
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.SectionEffectiveCartier

/-!
# Reducing `GloballyGeneratedRestrictionNonneg` to a section witness

E29 isolated ample ⇒ nef at one named hypothesis, `GloballyGeneratedRestrictionNonneg`: a globally
generated invertible sheaf has non-negative degree on every prime curve. This module discharges
**everything in it except one sections-level statement**, and names precisely what is left.

## What is proved outright, from accepted results only

`restrictionDegree_nonneg_of_effectiveIso` — if an invertible `M` is isomorphic to `O_X(E)` for an
effective Cartier divisor `E` with regular equations whose support misses the curve, then
`0 ≤ C.restrictionDegree M`. The whole chain is accepted:
`intersectionDegree_nonneg` (the degree is a `k`-dimension, hence `≥ 0`) →
`intersectionNumber_eq_intersectionDegree` → `intersectionNumber_eq_restrictionDegree` →
`restrictionDegree_eq_of_iso`. No finiteness side condition has to be supplied here, because the
accepted surface-side development has already discharged them.

## What remains, named exactly

`GloballyGeneratedSectionWitness` — for every globally generated invertible `M` and every prime curve
`C`, some effective divisor representing `M` misses `C`. Then
`globallyGeneratedRestrictionNonneg_of_witness` gives the E29 hypothesis outright (its conclusion is
that hypothesis unfolded, so a consumer may use it directly).

**Why the witness is the honest residue, and what it costs.** Producing it means turning
`Epi (free I ⟶ M.obj)` into a global section of `M` that does not vanish on `C`. The pieces are
identified and the obstruction is specific:

* the sections themselves are **not** the problem — Mathlib's `freeHomEquiv` is an equivalence, so
  `M.freeHomEquiv φ : I → M.sections` recovers generating sections from the epimorphism directly, and
  the accepted `schemeModuleSectionsEquivTop : M.sections ≃ M.val.obj (op ⊤)` lands them in exactly
  the type the accepted `exists_effectiveCartier_of_nonzero_section` consumes (`IsIntegral X.toScheme`
  is an accepted instance);
* what is missing is that some such section is **non-vanishing at `C.genericPoint`**, which is a
  stalk statement. `Epi` in a sheaf category is not sectionwise surjectivity, so it must be routed
  through local surjectivity. The pin has `CategoryTheory.Sites.isLocallySurjective_iff_epi` only for
  `Sheaf J (Type w)`, and `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` for
  presheaves; the accepted tree performs exactly this dance, but for **`AddCommGrp`**-valued sheaves
  (`ClosedEmbeddingPushforwardExact`, `GrothendieckVanishing/ClosedImmersion`), not for
  `SheafOfModules`. Crossing those two functor layers — module sheaves to abelian sheaves to
  presheaves of types — is the remaining work, and it is a module of its own, not a step.

So the geometric half of the E29 hypothesis is now paid for, and the residue is a single
sheaf-theoretic bridge with its route mapped.

Import closure is **accepted-only**: `Positivity` landed in candidate1197, so nothing here waits on
the queue. Nothing is admitted and no literature literal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.GloballyGeneratedNef

open KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- **The degree half, proved from accepted results.** An invertible sheaf isomorphic to `O_X(E)` for
an effective `E` with regular equations missing `C` has non-negative degree on `C`. -/
theorem restrictionDegree_nonneg_of_effectiveIso (C : X.PrimeCurve)
    (M : InvertibleSheaf X.toScheme) (E : CartierDivisor X.toScheme)
    (hE : HasRegularCartierEquations X.toScheme E) (hC : C.NotInSupport E hE)
    (e : (cartierDivisorInvertibleSheaf X.toScheme E).obj ≅ M.obj) :
    0 ≤ C.restrictionDegree M :=
  calc (0 : ℤ) ≤ (C.intersectionDegree E hE hC : ℤ) := C.intersectionDegree_nonneg E hE hC
    _ = C.intersectionNumber E := (C.intersectionNumber_eq_intersectionDegree E hE hC).symm
    _ = C.restrictionDegree (cartierDivisorInvertibleSheaf X.toScheme E) :=
        C.intersectionNumber_eq_restrictionDegree E
    _ = C.restrictionDegree M := C.restrictionDegree_eq_of_iso e

/-- **The named residue.** Every globally generated invertible sheaf is represented, at each prime
curve, by an effective divisor whose support misses that curve. See the header for the precise
sheaf-theoretic bridge this needs. -/
def GloballyGeneratedSectionWitness : Prop :=
  ∀ M : InvertibleSheaf X.toScheme, Positivity.IsGloballyGenerated M.obj →
    ∀ C : X.PrimeCurve, ∃ (E : CartierDivisor X.toScheme)
      (hE : HasRegularCartierEquations X.toScheme E) (_ : C.NotInSupport E hE),
      Nonempty ((cartierDivisorInvertibleSheaf X.toScheme E).obj ≅ M.obj)

/-- **The E29 hypothesis follows from the witness.** The conclusion is
`AmplePositivity.GloballyGeneratedRestrictionNonneg X` unfolded, so a consumer may use it directly. -/
theorem globallyGeneratedRestrictionNonneg_of_witness
    (hW : GloballyGeneratedSectionWitness X) :
    ∀ M : InvertibleSheaf X.toScheme, Positivity.IsGloballyGenerated M.obj →
      ∀ C : X.PrimeCurve, 0 ≤ C.restrictionDegree M := by
  intro M hM C
  obtain ⟨E, hE, hC, ⟨e⟩⟩ := hW M hM C
  exact restrictionDegree_nonneg_of_effectiveIso X C M E hE hC e

end KltDP.Geometry.GloballyGeneratedNef
