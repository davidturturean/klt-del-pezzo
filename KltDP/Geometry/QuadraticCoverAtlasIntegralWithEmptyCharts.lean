import KltDP.Geometry.QuadraticCoverFunctionFieldBranch

/-!
# Integrality of the original quadratic atlas, allowing empty charts

Only one selected original base chart is required to be nonempty. Its
original coefficient is nonsquare in the actual scheme function field.
Whenever the proof encounters a point of another quadratic chart, the
original map to the base proves that this chart's base open is nonempty.
The existing nonsquare-transfer theorem then proves integrality of precisely
that chart. No field map or integral-domain instance is assigned to an empty
chart's zero section ring.

Original chart coverage and the actual open-immersion stalk maps prove
reducedness. The actual pair overlaps of nonempty base charts have points,
by the monic quadratic presentation over the domain of intersection sections.
The original gluing equality then proves density of the selected integral
chart in the unchanged glued scheme, hence global integrality.

This allows the existing AffineOpenRefinement atlas of all affine subopens,
including empty ones. No charts are removed and no gluing comparison or
global-integrality hypothesis is supplied. An actual finite odd valuation
of one original coefficient is an alternative input. Its geometric origin,
regularity and separability remain separate; characteristic two is allowed.

Reuse: pinned AdjoinRoot.nontrivial, generic-point germ injectivity and
isReduced_of_isReduced_stalk; the original PointBlowupIntegral stalk/density
argument and the frozen QuadraticCoverFunctionFieldBranch transfer.
Newer official Mathlib IsReduced.of_openCover uses the same stalk argument
(Apache 2.0); no new descent foundation or newer source port is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

private theorem base_nonempty_of_chart_point (i : ι) (x : D.chart i) :
    Nonempty (D.opens i) :=
  ⟨⟨(D.chartToBase i).base x,
    D.frameToBase_mem (le_refl (D.opens i)) (D.affine i) x⟩⟩

variable [IsIntegral X]

private theorem integral_nonempty_chart (i j : ι)
    [Nonempty (D.opens i)] [Nonempty (D.opens j)]
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) :
    IsIntegral (D.chart j) := by
  change IsIntegral (affineScheme (res X (le_refl (D.opens j)) (D.sections j)))
  rw [res_self]
  apply affineScheme_isIntegral_of_nonsquare (R := Γ(X, D.opens j)) (↥X.functionField)
  · change Function.Injective (X.germToFunctionField (D.opens j))
    exact X.germToFunctionField_injective (D.opens j)
  · change ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens j) (D.sections j)
    exact functionField_nonsquare_of_chart D i j hs

private theorem overlap_nonempty_of_nonempty_bases (i j : ι)
    [Nonempty (D.opens i)] [Nonempty (D.opens j)] : Nonempty (D.overlap i j) := by
  obtain ⟨xi⟩ := (inferInstance : Nonempty (D.opens i))
  obtain ⟨xj⟩ := (inferInstance : Nonempty (D.opens j))
  obtain ⟨x, hxi, hxj⟩ := nonempty_preirreducible_inter
    (D.opens i).isOpen (D.opens j).isOpen ⟨xi.val, xi.property⟩ ⟨xj.val, xj.property⟩
  letI : Nonempty (D.opens i ⊓ D.opens j : X.Opens) := ⟨⟨x, hxi, hxj⟩⟩
  let a : Γ(X, D.opens i ⊓ D.opens j) :=
    res X (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) (D.sections i)
  have hd : (polynomial a).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (polynomial_monic a).ne_zero,
      polynomial_natDegree]
    decide
  letI : Nontrivial (CoverAlgebra a) := AdjoinRoot.nontrivial (polynomial a) hd
  change Nonempty (PrimeSpectrum (CoverAlgebra a))
  infer_instance

private theorem reduced_of_selected_chart (i : ι) [Nonempty (D.opens i)]
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) : IsReduced D.scheme := by
  haveI : ∀ z : D.scheme, _root_.IsReduced (D.scheme.presheaf.stalk z) := by
    intro z
    obtain ⟨j, x, rfl⟩ := D.charts_cover z
    letI : Nonempty (D.opens j) := base_nonempty_of_chart_point D j x
    letI : IsIntegral (D.chart j) := integral_nonempty_chart D i j hs
    exact isReduced_of_injective ((D.chartι j).stalkMap x).hom
      (asIso ((D.chartι j).stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

private theorem selected_chart_dense (i : ι) [Nonempty (D.opens i)]
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) :
    Dense (Set.range (D.chartι i).base) := by
  intro z
  obtain ⟨j, x, rfl⟩ := D.charts_cover z
  letI : Nonempty (D.opens j) := base_nonempty_of_chart_point D j x
  letI : IsIntegral (D.chart j) := integral_nonempty_chart D i j hs
  let w : D.overlap j i := Classical.choice (overlap_nonempty_of_nonempty_bases D j i)
  have hoverlap : Dense (Set.range (D.overlapToChart j i).base) :=
    (D.overlapToChart j i).isOpenEmbedding.isOpen_range.dense
      ⟨(D.overlapToChart j i).base w, ⟨w, rfl⟩⟩
  have hsub : (D.chartι j).base '' Set.range (D.overlapToChart j i).base ⊆
      Set.range (D.chartι i).base := by
    rintro z ⟨y, ⟨t, rfl⟩, rfl⟩
    refine ⟨(D.transition j i ≫ D.overlapToChart i j).base t, ?_⟩
    exact congrArg (fun f : D.overlap j i ⟶ D.scheme => f.base t)
      (D.chartOverlapIsPullback j i).w.symm
  exact closure_mono hsub
    (image_closure_subset_closure_image (D.chartι j).continuous
      ⟨x, hoverlap x, rfl⟩)

/-- One nonsquare coefficient on a selected nonempty original chart proves
integrality of the unchanged cover, even when other original charts are empty. -/
theorem scheme_isIntegral_of_selected_chart_nonsquare (i : ι)
    [Nonempty (D.opens i)]
    (hs : ∀ x : X.functionField,
      x ^ 2 ≠ X.germToFunctionField (D.opens i) (D.sections i)) :
    IsIntegral D.scheme := by
  letI : IsReduced D.scheme := reduced_of_selected_chart D i hs
  letI : IsIntegral (D.chart i) := integral_nonempty_chart D i i hs
  have hirr : IsIrreducible (Set.range (D.chartι i).base) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (D.chart i)).image
        (D.chartι i).base (D.chartι i).continuous.continuousOn
  have hwhole : IsIrreducible (Set.univ : Set D.scheme) := by
    simpa only [(selected_chart_dense D i hs).closure_eq] using hirr.closure
  letI : IrreducibleSpace D.scheme := (irreducibleSpace_def D.scheme).mpr hwhole
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- One actual finite odd valuation suffices for the original glued cover,
with no nonemptiness assumption on any unselected chart. -/
theorem scheme_isIntegral_of_selected_chart_oddValuation (i : ι)
    [Nonempty (D.opens i)]
    (valuation : AddValuation X.functionField (WithTop ℤ)) (z : ℤ)
    (hv : valuation (X.germToFunctionField (D.opens i) (D.sections i)) =
      (z : WithTop ℤ)) (hz : Odd z) : IsIntegral D.scheme :=
  scheme_isIntegral_of_selected_chart_nonsquare D i
    (nonsquare_of_odd_addValuation valuation
      (X.germToFunctionField (D.opens i) (D.sections i)) z hv hz)

end KltDP.Geometry.QuadraticCoverAtlas.Data
