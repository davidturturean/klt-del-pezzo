import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.SchemeModulePullbackTensor
import KltDP.Geometry.InvertibleSheafTensor
import KltDP.AdmissionProbe.CurveTensorDegreeConsumers

/-!
# The adjunction formula on a surface: statements and the degree consequence

`X` a normal projective surface over `k`, `ω : InvertibleSheaf X` an (abstract) canonical sheaf,
`C : X.PrimeCurve` a prime curve with cotangent sheaf `Ω_C := Ω_{C/k}` (accepted global
differential sheaf of `C.toSpec`), and, on a regular surface over an algebraically closed field,
`D_C` the Cartier divisor of `C`.

* `canonicalRestrictionDegree X ω C := deg_C(ω|_C)` — **`K_X · C`** as F02's restriction degree of
  the class `[ω]` (`picardRestrictionDegree`), equal to `lineDegree (i^*ω)`.
* `AdjunctionIso X hregular ω C`: the adjunction isomorphism `Ω_C ≅ (ω ⊗ O_X(D_C))|_C`, as a
  hypothesis (a `Prop`).
* `ConormalShortExact X hregular C`: the conormal sequence `0 → O_C(−C) → Ω_X|_C → Ω_C → 0`, as a
  hypothesis: a short exact sequence of modules on `C` whose terms are isomorphic to
  `i^*O_X(−D_C)`, `i^*Ω_X`, `Ω_C`.
* **`adjunction_degree`**: under `AdjunctionIso`, `K_X · C + C · C = deg K_C`
  (`canonicalRestrictionDegree + selfIntersectionNumber = canonicalDegree C.toSpec`), by the
  pullback–tensor comparison and the admitted 0AYX additivity on `C`
  (`lineDegree_eq_add_of_tensorIso`). Export `f04_adjunction_degree_seed`.

**Not proved here:** the adjunction isomorphism and the conormal sequence themselves (they need the
sheaf-level conormal sequence of a regular closed immersion and the determinant of a two-term
exact sequence — see `F04_CANONICAL_PLAN.md`), and `ω_X = ∧²Ω_X` (no exterior power of module
sheaves in the pinned Mathlib or the accepted tree); `ω` is an explicit argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.AdjunctionSeed

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance adjunctionSeedMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- **`K_X · C := deg_C(ω|_C)`**: F02's restriction degree of the class of the canonical sheaf. -/
def canonicalRestrictionDegree (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve) : ℤ :=
  C.picardRestrictionDegree ω.toPic

theorem canonicalRestrictionDegree_eq_lineDegree (ω : InvertibleSheaf X.toScheme)
    (C : X.PrimeCurve) :
    canonicalRestrictionDegree X ω C =
      C.lineDegree (pullbackInvertibleSheaf C.inclusion ω) :=
  C.picardRestrictionDegree_toPic ω

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **The adjunction isomorphism** `Ω_C ≅ (ω ⊗ O_X(D_C))|_C`, as a hypothesis. -/
def AdjunctionIso (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve) : Prop :=
  Nonempty (CurveCanonical.cotangentSheaf C.toSpec ≅
    (schemeModulePullback C.inclusion).obj
      (ω.obj ⊗ cartierDivisorModule X.toScheme (X.primeCurveCartier hregular C)))

/-- **The conormal sequence** `0 → O_C(−C) → Ω_X|_C → Ω_C → 0`, as a hypothesis: a short exact
sequence on `C` with terms isomorphic to `i^*O_X(−D_C)`, `i^*Ω_X`, `Ω_C`. -/
def ConormalShortExact (C : X.PrimeCurve) : Prop :=
  ∃ S : ShortComplex C.toScheme.Modules, S.ShortExact ∧
    Nonempty (S.X₁ ≅ (schemeModulePullback C.inclusion).obj
      (cartierDivisorModule X.toScheme (-(X.primeCurveCartier hregular C)))) ∧
    Nonempty (S.X₂ ≅ (schemeModulePullback C.inclusion).obj
      (CurveCanonical.cotangentSheaf X.structureMorphism)) ∧
    Nonempty (S.X₃ ≅ CurveCanonical.cotangentSheaf C.toSpec)

/-- **Adjunction, degree form**: `K_X · C + C · C = deg K_C` under the adjunction isomorphism. -/
theorem adjunction_degree (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve)
    (h : AdjunctionIso X hregular ω C) :
    canonicalRestrictionDegree X ω C + C.selfIntersectionNumber hregular =
      CurveCanonical.canonicalDegree C.toSpec := by
  obtain ⟨e⟩ := h
  let L := pullbackInvertibleSheaf C.inclusion ω
  let M := pullbackInvertibleSheaf C.inclusion
    (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C))
  let N := pullbackInvertibleSheaf C.inclusion
    (InvertibleSheafTensor.tensorInvertibleSheaf ω
      (cartierDivisorInvertibleSheaf X.toScheme (X.primeCurveCartier hregular C)))
  have h1 : CurveCanonical.canonicalDegree C.toSpec = C.lineDegree N :=
    CurveCanonical.canonicalDegree_eq_of_iso C.toSpec e
  have h2 : C.lineDegree N = C.lineDegree L + C.lineDegree M :=
    KltDP.AdmissionProbe.CurveTensorDegreeConsumers.lineDegree_eq_add_of_tensorIso C L M N
      (schemeModulePullbackTensorIso C.inclusion ω.obj
        (cartierDivisorModule X.toScheme (X.primeCurveCartier hregular C)))
  have h3 : canonicalRestrictionDegree X ω C = C.lineDegree L :=
    canonicalRestrictionDegree_eq_lineDegree X ω C
  have h4 : C.selfIntersectionNumber hregular = C.lineDegree M := rfl
  omega

end Regular

end KltDP.Geometry.AdjunctionSeed

namespace KltDP.Geometry

open AdjunctionSeed

/-- **F04 export (adjunction seed)**: for a prime curve `C` on a regular surface over an
algebraically closed field and any invertible `ω`, the adjunction isomorphism
`Ω_C ≅ (ω ⊗ O_X(D_C))|_C` implies `K_X · C + C · C = deg K_C`. -/
theorem f04_adjunction_degree_seed {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (ω : InvertibleSheaf X.toScheme) (C : X.PrimeCurve) (h : AdjunctionIso X hregular ω C) :
    canonicalRestrictionDegree X ω C + C.selfIntersectionNumber hregular =
      CurveCanonical.canonicalDegree C.toSpec :=
  adjunction_degree X hregular ω C h

/-- Universe check: a single universe `u`. -/
example {k : Type u} [Field k] (X : NormalProjectiveSurface k) (ω : InvertibleSheaf X.toScheme)
    (C : X.PrimeCurve) :
    canonicalRestrictionDegree X ω C = C.lineDegree (pullbackInvertibleSheaf C.inclusion ω) :=
  canonicalRestrictionDegree_eq_lineDegree X ω C

end KltDP.Geometry
