import KltDP.Geometry.QuadraticCoverAtlasGluing
import KltDP.Geometry.QuadraticCoverIntegral

/-!
# Integrality of the actual quadratic cover from its original branch sections

The base is an actual integral scheme. For every chart, the original section
ring embeds into a field in which its original branch coefficient is nonsquare.
The existing quadratic-quotient theorem proves that each actual chart is
integral. Its points give nonempty base opens, whose intersections are nonempty
by irreducibility of the base. The actual monic quadratic quotient on each
intersection is nontrivial, so the actual overlap has a point.

The already constructed overlap maps and gluing inclusions then make every
chart image dense in the constructed scheme. Reducedness follows from the
original open-immersion stalk maps. These facts give global integrality.

No chart-domain, overlap-nonemptiness, dense-image or global-integrality
conclusion is an input to the public theorem. Injective maps into fields
exclude empty base charts; no nonempty-chart premise is silently inferred
from the atlas alone. Characteristic two is allowed. This proves neither
separability nor smoothness. Geometric odd valuations and the transfer of one
function-field nonsquare across the original line-bundle atlas remain separate.

Reuse: pinned AdjoinRoot.nontrivial and the original quotient theorem;
the actual chart/stalk/density argument already used in PointBlowupIntegral.
Newer official Mathlib Properties.IsReduced.of_openCover uses the same stalk
argument (Apache 2.0); no newer sheafification or gluing foundation is ported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

private theorem chart_integral_from_field
    (K : ι → Type v) [∀ i, Field (K i)]
    [∀ i, Algebra Γ(X, D.opens i) (K i)]
    (hinj : ∀ i, Function.Injective (algebraMap Γ(X, D.opens i) (K i)))
    (hs : ∀ i, ∀ x : K i, x ^ 2 ≠ algebraMap Γ(X, D.opens i) (K i) (D.sections i))
    (i : ι) : IsIntegral (D.chart i) := by
  change IsIntegral (affineScheme (res X (le_refl (D.opens i)) (D.sections i)))
  rw [res_self]
  exact affineScheme_isIntegral_of_nonsquare (K i) (hinj i) (D.sections i) (hs i)

private theorem base_open_nonempty
    (hcharts : ∀ i, IsIntegral (D.chart i)) (i : ι) : (D.opens i : Set X).Nonempty := by
  letI : IsIntegral (D.chart i) := hcharts i
  let x : D.chart i := Classical.choice inferInstance
  exact ⟨(D.chartToBase i).base x,
    D.frameToBase_mem (le_refl (D.opens i)) (D.affine i) x⟩

private theorem overlap_nonempty_from_base [IsIntegral X]
    (hcharts : ∀ i, IsIntegral (D.chart i)) (i j : ι) : Nonempty (D.overlap i j) := by
  obtain ⟨x, hxi, hxj⟩ := nonempty_preirreducible_inter
    (D.opens i).isOpen (D.opens j).isOpen
    (base_open_nonempty D hcharts i) (base_open_nonempty D hcharts j)
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

private theorem scheme_reduced_from_charts
    (hcharts : ∀ i, IsIntegral (D.chart i)) : IsReduced D.scheme := by
  haveI : ∀ z : D.scheme, _root_.IsReduced (D.scheme.presheaf.stalk z) := by
    intro z
    obtain ⟨i, x, rfl⟩ := D.charts_cover z
    letI : IsIntegral (D.chart i) := hcharts i
    exact isReduced_of_injective ((D.chartι i).stalkMap x).hom
      (asIso ((D.chartι i).stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

private theorem chart_image_dense [IsIntegral X]
    (hcharts : ∀ i, IsIntegral (D.chart i)) (i : ι) :
    Dense (Set.range (D.chartι i).base) := by
  intro z
  obtain ⟨j, x, rfl⟩ := D.charts_cover z
  letI : IsIntegral (D.chart j) := hcharts j
  let w : D.overlap j i := Classical.choice (overlap_nonempty_from_base D hcharts j i)
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

/-- The actual globally glued quadratic cover is integral when the original
branch section on every actual affine chart remains nonsquare in an actual
field receiving its section ring injectively. The quotient-domain and global
integrality properties are derived, including nonempty actual overlaps. -/
theorem scheme_isIntegral_of_chart_nonsquare [IsIntegral X]
    (K : ι → Type v) [∀ i, Field (K i)]
    [∀ i, Algebra Γ(X, D.opens i) (K i)]
    (hinj : ∀ i, Function.Injective (algebraMap Γ(X, D.opens i) (K i)))
    (hs : ∀ i, ∀ x : K i, x ^ 2 ≠ algebraMap Γ(X, D.opens i) (K i) (D.sections i)) :
    IsIntegral D.scheme := by
  have hcharts : ∀ i, IsIntegral (D.chart i) := chart_integral_from_field D K hinj hs
  letI : IsReduced D.scheme := scheme_reduced_from_charts D hcharts
  let x : X := Classical.choice inferInstance
  have hx : x ∈ ⨆ i, D.opens i := by rw [D.covers]; trivial
  obtain ⟨i, _hi⟩ := Opens.mem_iSup.mp hx
  letI : IsIntegral (D.chart i) := hcharts i
  have hirr : IsIrreducible (Set.range (D.chartι i).base) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (D.chart i)).image
        (D.chartι i).base (D.chartι i).continuous.continuousOn
  have hwhole : IsIrreducible (Set.univ : Set D.scheme) := by
    simpa only [(chart_image_dense D hcharts i).closure_eq] using hirr.closure
  letI : IrreducibleSpace D.scheme := (irreducibleSpace_def D.scheme).mpr hwhole
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end KltDP.Geometry.QuadraticCoverAtlas.Data
