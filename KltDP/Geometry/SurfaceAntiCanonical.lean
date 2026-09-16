import KltDP.Geometry.AdjunctionFormulaSeed
import KltDP.Geometry.NumericalEquivalence

/-!
# The anti-canonical class `−K_X` of a surface, relative to a supplied canonical sheaf

`docs/GAPS.md` records `antiCanonical` as declared nowhere, and that is the first half of why the
project's endpoint — a klt del Pezzo surface, i.e. one with `−K_X` **ample** — is not statable.
This module supplies `−K_X` honestly, and connects it to accepted machinery.

**Why it is relative to a supplied `ω`, and why that is not a weakening.** There is no surface
canonical class in the accepted tree: `canonicalClass` exists only for *curves*
(`CurveCanonical.canonicalClass` on `SmoothCurveCanonicalDegree`, and
`ProjectiveLineCanonical.canonicalClass`), and a surface `ω_X = ∧²Ω_X` needs an exterior power of
module sheaves that the pinned Mathlib does not have. The accepted `AdjunctionFormulaSeed` already
faces this and resolves it the same way — it takes `ω : InvertibleSheaf X.toScheme` as an **explicit
argument** and defines `K_X · C := canonicalRestrictionDegree X ω C`. This module stays exactly in
that convention, so every statement here composes with the accepted one at the same `ω`.

* `antiCanonicalClass X ω := (ω.toPic)⁻¹` — the inverse in the accepted `CommGroup (Pic X)`.
* `antiCanonicalClass_mul_self` — it really is the inverse of `[ω]`.
* `antiCanonicalRestrictionDegree X ω C` — `(−K_X) · C`, as the accepted F02 restriction degree.
* **`antiCanonicalRestrictionDegree_eq_neg`** — `(−K_X) · C = −(K_X · C)`. This is the connection to
  accepted machinery: it is proved from the accepted `picardRestrictionDegree_div` at `p = 1` and
  `picardRestrictionDegree_one`, not from any new degree law.
* **`antiCanonical_adjunction`** — under the accepted `AdjunctionIso` hypothesis,
  `(−K_X) · C = C · C − deg K_C`, i.e. the accepted `adjunction_degree` rewritten on the
  anti-canonical side. A second consumer that can cite the definition.

**What would be false if the definition were different?** `antiCanonicalRestrictionDegree_eq_neg`
pins `antiCanonicalClass` to the group inverse: any other class would fail it, since restriction
degree separates classes that differ by a non-numerically-trivial factor. So the definition carries
content rather than naming a choice.

Import closure is **accepted-only** (`AdjunctionFormulaSeed`, `NumericalEquivalence`), so this
certifies independently of lane E's queued entries. This is **not** `isDelPezzo`: that additionally
needs ampleness of this class, which is treated separately and is not claimed here.

Nothing is admitted and no literature literal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AntiCanonical

open KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.AdjunctionSeed

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- **The anti-canonical class `−K_X`**, relative to a supplied canonical sheaf `ω`: the inverse of
`[ω]` in the accepted `CommGroup (Pic X)`. -/
def antiCanonicalClass (ω : InvertibleSheaf X.toScheme) : X.toScheme.Pic := (ω.toPic)⁻¹

/-- `−K_X` is the inverse of `K_X`: the two classes multiply to the trivial class. -/
@[simp]
theorem antiCanonicalClass_mul_self (ω : InvertibleSheaf X.toScheme) :
    antiCanonicalClass X ω * ω.toPic = 1 :=
  inv_mul_cancel _

/-- **`(−K_X) · C`**: the accepted F02 restriction degree of the anti-canonical class along a prime
curve. -/
def antiCanonicalRestrictionDegree (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve) : ℤ :=
  C.picardRestrictionDegree (antiCanonicalClass X ω)

/-- **`(−K_X) · C = −(K_X · C)`.** The connection to accepted machinery: the accepted
`picardRestrictionDegree_div` at `p = 1`, with `picardRestrictionDegree_one`. -/
theorem antiCanonicalRestrictionDegree_eq_neg (ω : InvertibleSheaf X.toScheme)
    (C : X.PrimeCurve) :
    antiCanonicalRestrictionDegree X ω C = - canonicalRestrictionDegree X ω C := by
  unfold antiCanonicalRestrictionDegree antiCanonicalClass canonicalRestrictionDegree
  rw [← one_div, X.picardRestrictionDegree_div C 1 ω.toPic, C.picardRestrictionDegree_one, zero_sub]

section Adjunction

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **Adjunction on the anti-canonical side**: `(−K_X) · C = C · C − deg K_C`, under the accepted
`AdjunctionIso` hypothesis. This is the accepted `adjunction_degree` read through
`antiCanonicalRestrictionDegree_eq_neg`. -/
theorem antiCanonical_adjunction (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve)
    (h : AdjunctionIso X hregular ω C) :
    antiCanonicalRestrictionDegree X ω C =
      C.selfIntersectionNumber hregular - CurveCanonical.canonicalDegree C.toSpec := by
  have hadj := adjunction_degree X hregular ω C h
  rw [antiCanonicalRestrictionDegree_eq_neg]
  omega

end Adjunction

end KltDP.Geometry.AntiCanonical
