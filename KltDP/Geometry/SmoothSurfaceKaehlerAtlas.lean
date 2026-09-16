import KltDP.Geometry.KaehlerChartAtlas
import KltDP.Geometry.SmoothCurveCotangentInvertible
import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# A surface smooth of relative dimension two carries a Kähler chart atlas

`KaehlerChartAtlas.canonicalClass` glues `K_X` out of a covering by affine opens **each carrying a
frame of its Kähler module**. Taken alone that is true by construction and denotes nothing: if no
actual surface is known to admit such an atlas, nothing would be false were the definition
different. This module supplies the atlas, so the construction acquires content.

Every ingredient is accepted; none of it is new mathematics:

* `SmoothCurveCotangent.exists_affine_standardSmoothOfRelativeDimension` — despite living in a
  *curve*-named module, it is stated for arbitrary relative dimension `n` and an arbitrary scheme:
  around every point of a scheme smooth of relative dimension `n` over a field there is an affine
  open whose section ring is standard smooth of relative dimension `n` over `k` **through
  `baseToAffineSectionsMap`**, which is exactly the algebra the atlas uses.
* `RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra` — transports that to the `Algebra`
  instance, stated at `f.toAlgebra`, which is definitionally `KaehlerChartAtlas.chartAlgebra`.
* `AffineTopDifferentialFrame.standardSmoothDifferentialBasis` — **the rank normalisation, already
  accepted**: relative dimension two gives a `Fin 2`-indexed basis of `Ω[A⁄k]` directly, so no
  `finrank` comparison across the cover is needed and `SubmersivePresentation` is never handled here.

* **`atlasOpen`/`atlasFrame`** — the cover indexed by the points of `X`, each with its frame.
* **`atlasOpen_iSup`** — it covers.
* **`canonicalSheafOfSmoothSurface`**, **`canonicalClassOfSmoothSurface`** — `ω_X` and `K_X` as
  actual terms, with no atlas hypothesis.
* **`exists_kaehlerChartAtlas`** — the existence statement in the shape `canonicalSheaf` consumes.

The cover is indexed by points, the recorded "move the COVER" pattern, and the same shape the
accepted `SmoothKaehlerLocallyFree.exists_finite_localBases` uses.

Nothing is admitted here. This module assumes no atlas; it produces one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.SmoothCurveCotangent
open KltDP.Geometry.AffineTopDifferentialFrame

universe u

namespace KltDP.Geometry.SmoothSurfaceKaehlerAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
variable [IsSmoothOfRelativeDimension 2 f]

/-- The chosen affine chart around a point, standard smooth of relative dimension two. -/
def atlasOpen (x : X) : X.Opens :=
  (exists_affine_standardSmoothOfRelativeDimension f 2 x).choose

theorem atlasOpen_isAffineOpen (x : X) : IsAffineOpen (atlasOpen f x) :=
  (exists_affine_standardSmoothOfRelativeDimension f 2 x).choose_spec.choose

theorem atlasOpen_mem (x : X) : x ∈ atlasOpen f x :=
  (exists_affine_standardSmoothOfRelativeDimension f 2 x).choose_spec.choose_spec.1

theorem atlasOpen_standardSmooth (x : X) :
    RingHom.IsStandardSmoothOfRelativeDimension 2
      (baseToAffineSectionsMap f (atlasOpen_isAffineOpen f x)).hom :=
  (exists_affine_standardSmoothOfRelativeDimension f 2 x).choose_spec.choose_spec.2

/-- **The chosen charts cover `X`** — each contains its own index point. -/
theorem atlasOpen_iSup : (⨆ x : X, atlasOpen f x) = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_iSup, Opens.coe_top]
  exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, atlasOpen_mem f x⟩

/-- **The Kähler frame on each chosen chart.** Relative dimension two gives the `Fin 2` index
directly, through the accepted `standardSmoothDifferentialBasis`. -/
def atlasFrame (x : X) :
    letI : Algebra k Γ(X, atlasOpen f x) :=
      (baseToAffineSectionsMap f (atlasOpen_isAffineOpen f x)).hom.toAlgebra
    Basis (Fin 2) Γ(X, atlasOpen f x) (KaehlerDifferential k Γ(X, atlasOpen f x)) := by
  letI : Algebra k Γ(X, atlasOpen f x) :=
    (baseToAffineSectionsMap f (atlasOpen_isAffineOpen f x)).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, atlasOpen f x) :=
    (atlasOpen_standardSmooth f x).toAlgebra
  exact standardSmoothDifferentialBasis k Γ(X, atlasOpen f x)

/-- **`ω_X` for a surface smooth of relative dimension two, with no atlas hypothesis.** -/
def canonicalSheafOfSmoothSurface : InvertibleSheaf X :=
  KaehlerChartAtlas.canonicalSheaf f (atlasOpen f) (atlasOpen_isAffineOpen f)
    (atlasFrame f) (atlasOpen_iSup f)

/-- **`K_X` for a surface smooth of relative dimension two, with no atlas hypothesis.** -/
def canonicalClassOfSmoothSurface : X.Pic :=
  KaehlerChartAtlas.canonicalClass f (atlasOpen f) (atlasOpen_isAffineOpen f)
    (atlasFrame f) (atlasOpen_iSup f)

/-- **The atlas that `canonicalSheaf` consumes exists.** This is the nonvacuity statement. -/
theorem exists_kaehlerChartAtlas :
    ∃ (U : X → X.Opens) (hU : ∀ x, IsAffineOpen (U x))
      (_b : ∀ x, letI := KaehlerChartAtlas.chartAlgebra f U hU x;
        Basis (Fin 2) Γ(X, U x) (KaehlerDifferential k Γ(X, U x))),
      (⨆ x, U x) = ⊤ :=
  ⟨atlasOpen f, atlasOpen_isAffineOpen f, atlasFrame f, atlasOpen_iSup f⟩

end KltDP.Geometry.SmoothSurfaceKaehlerAtlas
