import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Examples.FrobeniusStageSurface

/-!
# `B` and `F̃` as prime curves: the scheme bridge (BRIEF47, Leg 1)

A prime curve `C : X.PrimeCurve` carries its own scheme `C.toScheme`, the reduced closed subscheme of the
vanishing ideal, with inclusion `C.inclusion`. The strict transforms `strictTransform` and
`liftedFiberClosure` are *different* schemes that happen to have the same closed range. Every statement
about `C.restrictedCoefficient` lives on `C.toScheme`; every statement about germs and contact lengths
(`crossingStalkEquiv`, `fiberCrossingStalkEquiv`) lives on the strict transforms. **Nothing connected
them**, which is why the germ-identification target specified in BRIEF45 did not typecheck: it equated a
section on one scheme with a stalk element on the other.

This module supplies the bridge, and only that. The accepted `PrimeCurveInclusionLift` already proves the
general fact — for a prime curve whose carrier is the range of a closed immersion with reduced source, the
immersion factors through `C.inclusion` by an **isomorphism**. Instantiating it needs three inputs, all
accepted and all free here:

* `hP : (C : Set X.toScheme) = Set.range ι.base` is `coe_graphStrictPrimeCurve` resp.
  `coe_fiberStrictPrimeCurve`, both **`rfl`**;
* `IsClosedImmersion ι` is `strictTransformι_isClosedImmersion` resp.
  `fiberClosureInclusion_isClosedImmersion`;
* `IsReduced C` is found by instance search: `strictTransform_isIntegral` with Mathlib's
  `isReduced_of_isIntegral`, resp. the accepted `liftedFiberClosure_isReduced`.

* **`graphStrictLift`, `graphStrictLiftIso`** — `strictTransform ≅ B.toScheme`, with
  `graphStrictLift_inclusion` and the point-level `graphStrictLift_base`;
* **`graphStrict_inclusion_eq`** — `B.inclusion = inv (graphStrictLift …) ≫ strictTransformι`. This is the
  form the remaining legs consume: `restrictedCoefficient` is defined by `C.inclusion.app`, and this
  rewrites that into the strict transform's own immersion.
* the same four for `F̃` (`fiberStrictLift`, `fiberStrictLiftIso`, `fiberStrictLift_inclusion`,
  `fiberStrict_inclusion_eq`, `fiberStrictLift_base`).

**Deliberately not stated: a section-level transport.** `f.app U` has type `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`, whose
*type* depends on `f`, so transporting a section across `lift ≫ inclusion = ι` is a dependent cast — the
`Eq.rec` machinery that has repeatedly cost this project whole sessions. Consumers should rewrite the
**morphism** with `graphStrict_inclusion_eq` before taking `app`, or index by the lift so that the two sides
agree definitionally, the design that already worked for `verticalCrossingPoint`.

**Not proved here**: Leg 2 (the divisor presents `x = c` as the translate of `x = 0`, while the graph-side
equation is that of the point `c` directly — identifying those is a real obligation) and Leg 3 (the tower
transport and chart-open bookkeeping, where `c ≠ 0` first enters).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictCurveLift

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformPrimeCurves
open FrobeniusFiberClosure

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-! ### The strict transform `B` -/

/-- **The strict transform of the graph maps isomorphically onto the prime-curve scheme of `B`.** -/
def graphStrictLift (m : ℕ) :
    strictTransform (k := k) (n + 1) (m + (n + 1)) ⟶ (graphStrictPrimeCurve n hproj m).toScheme :=
  PrimeCurveInclusionLift.lift (graphStrictPrimeCurve n hproj m)
    (strictTransformι (n + 1) (m + (n + 1))) (coe_graphStrictPrimeCurve n hproj m)

theorem graphStrictLift_inclusion (m : ℕ) :
    graphStrictLift n hproj m ≫ (graphStrictPrimeCurve n hproj m).inclusion =
      strictTransformι (k := k) (n + 1) (m + (n + 1)) :=
  PrimeCurveInclusionLift.lift_inclusion _ _ _

instance graphStrictLift_isIso (m : ℕ) : IsIso (graphStrictLift n hproj m) :=
  PrimeCurveInclusionLift.lift_isIso _ _ _

/-- The bridge as an isomorphism. -/
def graphStrictLiftIso (m : ℕ) :
    strictTransform (k := k) (n + 1) (m + (n + 1)) ≅ (graphStrictPrimeCurve n hproj m).toScheme :=
  asIso (graphStrictLift n hproj m)

@[simp] theorem graphStrictLiftIso_hom (m : ℕ) :
    (graphStrictLiftIso n hproj m).hom = graphStrictLift n hproj m := rfl

/-- **The prime-curve inclusion of `B` is the strict transform's own immersion, transported.**
This is the form the germ identification consumes: `restrictedCoefficient` is `C.inclusion.app`, and this
rewrites the morphism before any section is taken. -/
theorem graphStrict_inclusion_eq (m : ℕ) :
    (graphStrictPrimeCurve n hproj m).inclusion =
      inv (graphStrictLift n hproj m) ≫ strictTransformι (k := k) (n + 1) (m + (n + 1)) :=
  PrimeCurveInclusionLift.inclusion_eq_inv_lift _ _ _

/-- Point-level transport. Non-dependent, so no cast is involved. -/
theorem graphStrictLift_base (m : ℕ) (x : strictTransform (k := k) (n + 1) (m + (n + 1))) :
    (graphStrictPrimeCurve n hproj m).inclusion.base ((graphStrictLift n hproj m).base x) =
      (strictTransformι (k := k) (n + 1) (m + (n + 1))).base x := by
  have h := congrArg
    (fun f : strictTransform (k := k) (n + 1) (m + (n + 1)) ⟶
        (stageSurface (n + 1) hproj).toScheme => f.base x)
    (graphStrictLift_inclusion n hproj m)
  simpa only [Scheme.comp_base_apply] using h

/-! ### The strict fibre `F̃` -/

/-- **The strict fibre maps isomorphically onto the prime-curve scheme of `F̃`.** -/
def fiberStrictLift :
    liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1) ⟶
      (fiberStrictPrimeCurve n hproj).toScheme :=
  PrimeCurveInclusionLift.lift (fiberStrictPrimeCurve n hproj)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (coe_fiberStrictPrimeCurve n hproj)

theorem fiberStrictLift_inclusion :
    fiberStrictLift n hproj ≫ (fiberStrictPrimeCurve n hproj).inclusion =
      fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) :=
  PrimeCurveInclusionLift.lift_inclusion _ _ _

instance fiberStrictLift_isIso : IsIso (fiberStrictLift n hproj) :=
  PrimeCurveInclusionLift.lift_isIso _ _ _

/-- The bridge as an isomorphism. -/
def fiberStrictLiftIso :
    liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1) ≅
      (fiberStrictPrimeCurve n hproj).toScheme :=
  asIso (fiberStrictLift n hproj)

@[simp] theorem fiberStrictLiftIso_hom :
    (fiberStrictLiftIso n hproj).hom = fiberStrictLift n hproj := rfl

/-- **The prime-curve inclusion of `F̃` is the fibre closure's own immersion, transported.** -/
theorem fiberStrict_inclusion_eq :
    (fiberStrictPrimeCurve n hproj).inclusion =
      inv (fiberStrictLift n hproj) ≫
        fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) :=
  PrimeCurveInclusionLift.inclusion_eq_inv_lift _ _ _

/-- Point-level transport for `F̃`. -/
theorem fiberStrictLift_base
    (x : liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1)) :
    (fiberStrictPrimeCurve n hproj).inclusion.base ((fiberStrictLift n hproj).base x) =
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base x := by
  have h := congrArg
    (fun f : liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1) ⟶
        (stageSurface (n + 1) hproj).toScheme => f.base x)
    (fiberStrictLift_inclusion n hproj)
  simpa only [Scheme.comp_base_apply] using h

end KltDP.Examples.FrobeniusStrictCurveLift

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformPrimeCurves
open FrobeniusFiberClosure FrobeniusStrictCurveLift

/-- **F29: the strict transforms are the prime-curve schemes of `B` and `F̃`.** The bridge that makes the
germ identification statable at all: a section of `C.toScheme` and a stalk element of the strict transform
live on schemes that are now identified, isomorphically and compatibly with both inclusions. -/
theorem f29_strict_curve_lift (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) :
    graphStrictLift n hproj m ≫ (graphStrictPrimeCurve n hproj m).inclusion =
        strictTransformι (k := k) (n + 1) (m + (n + 1)) ∧
      IsIso (graphStrictLift n hproj m) ∧
    fiberStrictLift n hproj ≫ (fiberStrictPrimeCurve n hproj).inclusion =
        fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∧
      IsIso (fiberStrictLift n hproj) :=
  ⟨graphStrictLift_inclusion n hproj m, graphStrictLift_isIso n hproj m,
    fiberStrictLift_inclusion n hproj, fiberStrictLift_isIso n hproj⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_strict_curve_lift_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) : True := by
  have _ := f29_strict_curve_lift.{u} k n hproj m
  trivial

end KltDP.Examples
