import KltDP.Geometry.ChartKaehlerOpenFrame
import KltDP.Geometry.ChartFrameAtlasSheaf

/-!
# The canonical sheaf of a covering by affine charts carrying Kähler frames

This closes route 1. `ChartFrameAtlasSheaf` glues an atlas of chart frames into an actual
`InvertibleSheaf X` and its class in `X.Pic`; `ChartKaehlerOpenFrame` supplies the two fields that
the Kähler instantiation was missing — a frame on **every** open below each chart, and the
restriction coherence between them.

* **`chartAlgebra`**: the `k`-algebra structure of each chart's section ring, named rather than a
  global instance (the tree's policy for `affineSectionsAlgebra`).
* **`canonicalSheaf`**: from a covering by affine opens, each carrying a frame of its Kähler module,
  the glued invertible sheaf. For a smooth surface with `n = 2` this is `ω_X = ∧²Ω_X`.
* **`canonicalClass`**: its class in the actual Picard group — `K_X`.
* **`canonicalTransitionUnit`**: the transition units are the frame-change determinants of the
  chart frames on the pairwise intersections, which is what makes the class computable.

The frames are **data**, exactly as `ChartFrameAtlasSheaf` takes them: no smoothness hypothesis is
needed here, and smoothness re-enters only when one wants to exhibit the frames (accepted
`isSmooth_field_exists_affine_standardSmooth` plus `AffineTopDifferentialFrame`).

**`hframe`'s `{V W}` are implicit, and a lambda checked against a `∀` binds POSITIONALLY**: Lean
inserts implicit arguments at *application* sites, not when you write `fun` against an expected
`∀`-type. So the witness must supply all six binders, `fun i _ _ hVW hW t => …`; writing four binds
`hVW` to `V` and `hW` to `W`, and the error surfaces far away as `t` having type `hVW ≤ hW`.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.TransitionUnitGluing
open KltDP.Geometry.ChartKaehlerOpenFrame
open KltDP.Geometry.ChartFrameAtlasSheaf
open KltDP.Geometry.TopDifferentialFrameChange

universe u

namespace KltDP.Geometry.KaehlerChartAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
variable {n : ℕ}

/-- The `k`-algebra structure of a chart's section ring. -/
def chartAlgebra (i : ι) : Algebra k Γ(X, U i) :=
  (baseToAffineSectionsMap f (hU i)).hom.toAlgebra

/-- **The invertible sheaf glued from an atlas of Kähler chart frames.** For a smooth surface and
`n = 2` this is `ω_X = ∧²Ω_X`. -/
def canonicalSheaf
    (b : ∀ i, letI := chartAlgebra f U hU i;
      Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))
    (hcov : (⨆ i, U i) = ⊤) : InvertibleSheaf X :=
  sheafOfFrames U (differentialSections f) (differentialRestr f)
    (fun i W hW => chartOpenFrame f (hU i) (b i) W hW)
    (fun i _ _ hVW hW t => chartOpenFrame_restrict f (hU i) (b i) hVW hW t) hcov

/-- **The class of the atlas in the actual Picard group** — for a surface atlas of Kähler frames
this is `K_X`. -/
def canonicalClass
    (b : ∀ i, letI := chartAlgebra f U hU i;
      Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i)))
    (hcov : (⨆ i, U i) = ⊤) : X.Pic :=
  classOfFrames U (differentialSections f) (differentialRestr f)
    (fun i W hW => chartOpenFrame f (hU i) (b i) W hW)
    (fun i _ _ hVW hW t => chartOpenFrame_restrict f (hU i) (b i) hVW hW t) hcov

/-- The transition units of that atlas are the frame-change determinants of the chart frames on the
pairwise intersections. -/
theorem canonicalTransitionUnit
    (b : ∀ i, letI := chartAlgebra f U hU i;
      Basis (Fin n) Γ(X, U i) (KaehlerDifferential k Γ(X, U i))) (i j : ι) :
    transitionUnit U (differentialSections f)
        (fun i W hW => chartOpenFrame f (hU i) (b i) W hW) i j =
      frameChangeUnit
        (chartOpenFrame f (hU i) (b i) (U i ⊓ U j) inf_le_left)
        (chartOpenFrame f (hU j) (b j) (U i ⊓ U j) inf_le_right) := rfl

end KltDP.Geometry.KaehlerChartAtlas
