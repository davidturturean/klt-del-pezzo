import KltDP.Examples.FrobeniusGlobalGraphCompatibility
import KltDP.Examples.FrobeniusStrictTransformClosure
import KltDP.Geometry.PrincipalKernelSheaf

/-!
# The original Frobenius graph ideal on the first product chart

The monomial affine curve is proved to be the scheme-theoretic pullback of
the already constructed closed projective graph. Its polynomial equation
therefore generates the restriction of that original graph ideal. The
equation gives a frame of the actual kernel module by multiplication.

This is the first affine chart of the integral graph-class calculation.
The other charts and the global Cartier principal relation remain separate;
no lattice vector or asserted Picard-class identity enters these results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassAffine

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusProductPlaneChart FrobeniusGlobalGraphCompatibility
open FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusStrictTransformClosure ProjectiveLineComparison

variable {k : Type u} [Field k]

private theorem graph_cone_parameter {W : Scheme.{u}} (p : ℕ)
    (f : W ⟶ Spec (CommRingCat.of (planeRing k)))
    (g : W ⟶ projectiveSpace k 1)
    (h : f ≫ planeChart = g ≫ projectiveGraphMorphism p) :
    (f ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫
      polynomialChartMap k 0 = g := by
  have he := congrArg (fun q : W ⟶ FrobeniusProjectivePoints.projectiveProduct k =>
    q ≫ firstProjection) h
  simpa only [Category.assoc, planeChart_fst,
    projectiveGraphMorphism_fst, Category.comp_id] using he

/-- The first affine monomial graph is the actual base change of the
closed projective graph along the original product-plane open immersion. -/
theorem curveInPlane_projectiveGraph_isPullback (p : ℕ) :
    IsPullback (curveInPlane (k := k) p) (polynomialChartMap k 0)
      planeChart (projectiveGraphMorphism p) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (curveInPlane_productChart p)
    (fun s => s.fst ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap))
    (fun s => ?_) (fun s => graph_cone_parameter p s.fst s.snd s.condition)
    (fun s m hm _ => ?_))
  · apply (cancel_mono (planeChart (k := k))).mp
    rw [Category.assoc, curveInPlane_productChart, ← Category.assoc,
      graph_cone_parameter p s.fst s.snd s.condition]
    exact s.condition.symm
  · calc
      m = (m ≫ curveInPlane p) ≫
          Spec.map (CommRingCat.ofHom firstCoordinateMap) := by
        rw [Category.assoc, curveInPlane_firstCoordinate, Category.comp_id]
      _ = _ := congrArg (fun q => q ≫
        Spec.map (CommRingCat.ofHom firstCoordinateMap)) hm

/-- The global graph ideal retains the existing closed graph morphism. -/
def graphIdeal (p : ℕ) : (FrobeniusProjectivePoints.projectiveProduct k).IdealSheafData :=
  (projectiveGraphMorphism (k := k) p).ker

/-- On every affine open of the first plane chart, the original graph
ideal is its monomial kernel through the canonical section isomorphism. -/
theorem graphIdeal_firstChart (p : ℕ)
    (U : (Spec (CommRingCat.of (planeRing k))).affineOpens) :
    (curveInPlane p).ker.ideal U =
      ((graphIdeal (k := k) p).ideal
        ⟨planeChart ''ᵁ U, U.2.image_of_isOpenImmersion _⟩).comap
          (planeChart.appIso U).inv.hom :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (projectiveGraphMorphism p) (curveInPlane p) (polynomialChartMap k 0)
    planeChart (curveInPlane_projectiveGraph_isPullback p) U

/-- The actual section corresponding to `v-u^p` in the original plane. -/
def firstEquation (p : ℕ) : Γ(Spec (CommRingCat.of (planeRing k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (vCoord - uCoord ^ p)

/-- The equation generates the actual global section kernel, without
changing the affine curve or choosing a replacement ideal sheaf. -/
theorem firstEquation_kernel (p : ℕ) :
    RingHom.ker (curveInPlane (k := k) p).appTop.hom =
      Ideal.span {firstEquation (k := k) p} := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).commRingCatIsoToRingEquiv
  have h : RingHom.ker (curveInPlane (k := k) p).appTop.hom =
      (RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
        (curveInPlane p).appTop).hom)).comap e.toRingHom := by
    ext x
    change (curveInPlane p).appTop x = 0 ↔
      (curveInPlane p).appTop (e.symm (e x)) = 0
    rw [e.symm_apply_apply]
  rw [h, curveInPlane_coordinateKernel]
  change (Ideal.span {vCoord - uCoord ^ p}).comap e.toRingHom =
    Ideal.span {e.symm (vCoord - uCoord ^ p)}
  rw [RingEquiv.toRingHom_eq_coe e, Ideal.comap_coe e, ← Ideal.map_symm e,
    Ideal.map_span, Set.image_singleton]

theorem firstEquation_eq_zero (p : ℕ) :
    (curveInPlane (k := k) p).appTop (firstEquation p) = 0 := by
  apply RingHom.mem_ker.mp
  rw [firstEquation_kernel]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Regularity follows from the monic polynomial equation, for every p. -/
theorem firstEquation_regular (p : ℕ) :
    firstEquation (k := k) p ∈
      nonZeroDivisors Γ(Spec (CommRingCat.of (planeRing k)), ⊤) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm (vCoord - uCoord ^ p)) ∈ nonZeroDivisors (planeRing k)
  rw [e.apply_symm_apply, mem_nonZeroDivisors_iff_ne_zero]
  simpa only [uCoord, vCoord, ← map_pow] using
    (Polynomial.monic_X_sub_C (Polynomial.X ^ p : Polynomial k)).ne_zero

/-- Multiplication by the original graph equation frames the actual
kernel module of the affine restriction of the global closed graph. -/
def firstKernelFrameIso (p : ℕ) :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (planeRing k))).ringCatSheaf ≅
      schemeKernelIdeal (curveInPlane (k := k) p) :=
  principalKernelSheafIso (curveInPlane p) (firstEquation p)
    (firstEquation_eq_zero p) (firstEquation_kernel p) (firstEquation_regular p)

@[reassoc]
theorem firstKernelFrameIso_hom_inclusion (p : ℕ) :
    (firstKernelFrameIso (k := k) p).hom ≫ schemeKernelIdealι (curveInPlane p) =
      schemeScalarEnd (Y := Spec (CommRingCat.of (planeRing k))) (firstEquation (k := k) p) :=
  schemeKernelGenerator_comp_ι (curveInPlane p) (firstEquation p) (firstEquation_eq_zero p)

end KltDP.Examples.FrobeniusGraphPicardClassAffine
