import KltDP.Geometry.SurfaceEulerSections
import KltDP.Geometry.ProjectiveStructureSheafHZero

/-!
# The Euler characteristic of a module on a surface, and `χ(O_X) = 1 − h¹ + h²`

`χ(O_X)` is already a *term* everywhere in the accepted tree — it opens the definition of the Euler
pairing (`CartierEulerPairing`), and `eulerCharacteristic_unit_sub_neg` relates it to the zero scheme
of a divisor — but nothing computes it. The two steps that would are each missing:

* the accepted `eulerCharacteristic_eq_zero_sub_one_of_vanishing` gives `χ = h⁰ − h¹` only under
  vanishing **above degree one**, i.e. under an extra hypothesis `h² = 0` that a surface does not
  satisfy; the degree-**two** truncation, which is what the accepted
  `normalProjectiveSurface_H_subsingleton` actually supplies, is not stated anywhere;
* `h⁰(O_X) = 1` is proved, in `ProjectiveStructureSheafHZero.normalProjectiveSurface_hZero_finrank_one`
  — an **accepted module that nothing in the tree imports** (`$W/ACCEPTED_ORPHANS.md`), and stated
  over `Module.finrank k (HZero X)` rather than over `cohomologyDimension`.

This module supplies both and combines them.

* `eulerCharacteristic_eq_alternating_two_of_vanishing` — `χ(M) = h⁰ − h¹ + h²` for any module whose
  cohomology vanishes above degree two, by the accepted `eulerCharacteristic_eq_truncatedEuler` at
  `N = 2`; the proof is the accepted degree-one version's, one truncation further.
* `normalProjectiveSurface_eulerCharacteristic_eq` — the same on a normal projective surface, where
  the vanishing hypothesis is discharged outright by `normalProjectiveSurface_H_subsingleton`.
* `cohomologyDimension_zero_unit_eq_one` — the bridge: `h⁰(O_X) = 1` in the `cohomologyDimension`
  presentation. `HZero X` is an `abbrev` for `H (structureSheaf X) 0`, and `baseHZeroModule f` and
  `baseModule f (structureSheaf X) 0` are the same `Module.compHom … (baseFieldToGlobalSections f)`,
  so the orphan's statement *is* this one up to unfolding and is applied as a term, not rewritten.
* **`normalProjectiveSurface_eulerCharacteristic_unit`** — `χ(O_X) = 1 − h¹(O_X) + h²(O_X)` over an
  algebraically closed field.

Import closure is **accepted-only** (`SurfaceEulerSections`, `ProjectiveStructureSheafHZero`), so this
certifies independently of lane E's queued entries. `StructureSheafCohomology` is imported but
deliberately **not opened**, per the ambiguity guard: names are fully qualified instead.

Nothing is admitted and no literature literal is used. This is not Riemann–Roch: it computes `χ` from
cohomology dimensions and asserts no relation to divisors, and `h¹`/`h²` remain unevaluated.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules)

/-- **`χ(M) = h⁰ − h¹ + h²`** whenever cohomology vanishes above degree two. The accepted
`eulerCharacteristic_eq_zero_sub_one_of_vanishing` is the same statement one truncation lower, and
assumes a vanishing bound a surface does not meet. -/
theorem eulerCharacteristic_eq_alternating_two_of_vanishing
    (hvanish : ∀ i, 2 < i → Subsingleton (H M i)) :
    eulerCharacteristic f M =
      (cohomologyDimension f M 0 : ℤ) - (cohomologyDimension f M 1 : ℤ) +
        (cohomologyDimension f M 2 : ℤ) := by
  rw [eulerCharacteristic_eq_truncatedEuler f M 2 hvanish]
  simp only [truncatedEuler, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    one_mul, neg_one_mul, zero_add]
  ring

end Scheme

section Surface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- **The Euler characteristic of any module on a normal projective surface**, with the vanishing
hypothesis discharged by the accepted `normalProjectiveSurface_H_subsingleton`. -/
theorem normalProjectiveSurface_eulerCharacteristic_eq (M : X.toScheme.Modules) :
    eulerCharacteristic X.structureMorphism M =
      (cohomologyDimension X.structureMorphism M 0 : ℤ) -
          (cohomologyDimension X.structureMorphism M 1 : ℤ) +
        (cohomologyDimension X.structureMorphism M 2 : ℤ) :=
  eulerCharacteristic_eq_alternating_two_of_vanishing X.structureMorphism M
    (fun i hi => normalProjectiveSurface_H_subsingleton X M i hi)

/-- **`h⁰(O_X) = 1`** in the `cohomologyDimension` presentation, over an algebraically closed field.
The accepted orphan states it as `Module.finrank k (HZero X)`; `HZero X` is an `abbrev` for
`H (structureSheaf X) 0` and the two base-field module structures are the same `compHom`, so the
orphan applies as a term. -/
theorem cohomologyDimension_zero_unit_eq_one [IsAlgClosed k] :
    cohomologyDimension X.structureMorphism
        (StructureSheafCohomology.structureSheaf X.toScheme) 0 = 1 :=
  StructureSheafCohomology.normalProjectiveSurface_hZero_finrank_one X

/-- **`χ(O_X) = 1 − h¹(O_X) + h²(O_X)`** on a normal projective surface over an algebraically closed
field: the value of the Euler characteristic that opens the definition of the accepted Euler pairing.
No Riemann–Roch content — `h¹` and `h²` are not evaluated. -/
theorem normalProjectiveSurface_eulerCharacteristic_unit [IsAlgClosed k] :
    eulerCharacteristic X.structureMorphism
        (StructureSheafCohomology.structureSheaf X.toScheme) =
      1 - (cohomologyDimension X.structureMorphism
            (StructureSheafCohomology.structureSheaf X.toScheme) 1 : ℤ) +
        (cohomologyDimension X.structureMorphism
            (StructureSheafCohomology.structureSheaf X.toScheme) 2 : ℤ) := by
  rw [normalProjectiveSurface_eulerCharacteristic_eq X
      (StructureSheafCohomology.structureSheaf X.toScheme),
    cohomologyDimension_zero_unit_eq_one X]
  norm_num

end Surface

end KltDP.Geometry.ModuleCohomology
