import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Geometry.PrincipalKernelSheaf

/-!
# The original projective coordinate point and its actual local ideal

The point is the existing rational point `[1:0]`, not a replacement
closed subscheme. Its polynomial chart is the existing evaluation map.
The actual chart pullback identifies the original ideal on chart opens,
and the canonical Gamma-Spec comparison gives its equation `X`.
The local kernel frame is the original multiplication map by that equation.

This is an actual coordinate-ideal prerequisite. It does not assert a
Proj twisting-sheaf, Picard exponent, divisor degree or self-intersection.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusProjectiveCoordinateIdeal

open KltDP.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The original rational coordinate point `[1:0]`. -/
def coordinatePoint : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1 :=
  FrobeniusProjectivePoints.pointMorphism (0 : k)

instance coordinatePoint_isClosedImmersion :
    IsClosedImmersion (coordinatePoint (k := k)) :=
  section_isClosedImmersion (projectiveSpaceToSpec k 1) coordinatePoint
    (FrobeniusProjectivePoints.pointMorphism_over_base (0 : k))

/-- The actual ideal sheaf of the original point map. -/
def coordinatePointIdeal : (projectiveSpace k 1).IdealSheafData :=
  (coordinatePoint (k := k)).ker

/-- The ordinary polynomial chart retains the actual evaluation map. -/
def affineCoordinatePoint : Spec (CommRingCat.of k) ⟶
    Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))

instance affineCoordinatePoint_isClosedImmersion :
    IsClosedImmersion (affineCoordinatePoint (k := k)) := by
  apply IsClosedImmersion.spec_of_surjective
  intro a
  exact ⟨Polynomial.C a, Polynomial.eval_C⟩

/-- The affine coordinate map factors the original projective point. -/
@[reassoc]
theorem affineCoordinatePoint_chart :
    affineCoordinatePoint (k := k) ≫ ProjectiveLineComparison.polynomialChartMap k 0 =
      coordinatePoint :=
  FrobeniusTranslatedCharts.polynomialChartMap_evaluation (0 : k)

/-- The first affine chart is the actual pullback of the original point. -/
theorem affineCoordinatePoint_isPullback :
    IsPullback (affineCoordinatePoint (k := k)) (𝟙 (Spec (CommRingCat.of k)))
      (ProjectiveLineComparison.polynomialChartMap k 0) coordinatePoint := by
  have hRange : Set.range (coordinatePoint (k := k)).base ⊆
      Set.range (ProjectiveLineComparison.polynomialChartMap k 0).base := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(affineCoordinatePoint (k := k)).base x, ?_⟩
    exact congrArg (fun f : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1 => f.base x)
      affineCoordinatePoint_chart
  have hLift : IsOpenImmersion.lift (ProjectiveLineComparison.polynomialChartMap k 0)
      (coordinatePoint (k := k)) hRange = affineCoordinatePoint :=
    (IsOpenImmersion.lift_uniq (ProjectiveLineComparison.polynomialChartMap k 0)
      coordinatePoint hRange affineCoordinatePoint affineCoordinatePoint_chart).symm
  simpa only [hLift] using IsOpenImmersion.isPullback_lift_id
    coordinatePoint (ProjectiveLineComparison.polynomialChartMap k 0) hRange

/-- Every actual affine chart-open ideal is the restriction of the
original projective point ideal through the original section isomorphism. -/
theorem coordinatePointIdeal_chart
    (U : (Spec (CommRingCat.of (Polynomial k))).affineOpens) :
    (affineCoordinatePoint (k := k)).ker.ideal U =
      ((coordinatePointIdeal (k := k)).ideal
        ⟨ProjectiveLineComparison.polynomialChartMap k 0 ''ᵁ U,
          U.2.image_of_isOpenImmersion _⟩).comap
        ((ProjectiveLineComparison.polynomialChartMap k 0).appIso U).inv.hom :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion coordinatePoint affineCoordinatePoint
    (𝟙 _) (ProjectiveLineComparison.polynomialChartMap k 0)
    affineCoordinatePoint_isPullback U

/-- In the original polynomial coordinates the point has ideal `(X)`. -/
theorem affineCoordinatePoint_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
      (affineCoordinatePoint (k := k)).appTop).hom) =
        Ideal.span {(Polynomial.X : Polynomial k)} := by
  have hΓ : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  rw [affineCoordinatePoint, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom,
    Polynomial.ker_evalRingHom, map_zero, sub_zero]

/-- The actual regular section corresponding to the original variable. -/
def affineCoordinateEquation : Γ(Spec (CommRingCat.of (Polynomial k)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X

/-- The equation generates the actual global section kernel on the chart. -/
theorem affineCoordinatePoint_kernel :
    RingHom.ker (affineCoordinatePoint (k := k)).appTop.hom =
      Ideal.span {affineCoordinateEquation (k := k)} := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).commRingCatIsoToRingEquiv
  have h : RingHom.ker (affineCoordinatePoint (k := k)).appTop.hom =
      (RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
        (affineCoordinatePoint (k := k)).appTop).hom)).comap e.toRingHom := by
    ext x
    change (affineCoordinatePoint (k := k)).appTop x = 0 ↔
      (affineCoordinatePoint (k := k)).appTop (e.symm (e x)) = 0
    rw [e.symm_apply_apply]
  rw [h, affineCoordinatePoint_coordinateKernel]
  change (Ideal.span {(Polynomial.X : Polynomial k)}).comap
      (e : Γ(Spec (CommRingCat.of (Polynomial k)), ⊤) →+* Polynomial k) =
    Ideal.span {e.symm Polynomial.X}
  rw [Ideal.comap_coe e, ← Ideal.map_symm e, Ideal.map_span, Set.image_singleton]

/-- The original coordinate equation is killed by the original point map. -/
theorem affineCoordinateEquation_eq_zero :
    (affineCoordinatePoint (k := k)).appTop affineCoordinateEquation = 0 := by
  apply RingHom.mem_ker.mp
  rw [affineCoordinatePoint_kernel]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Its regularity is derived from the actual polynomial variable. -/
theorem affineCoordinateEquation_regular :
    affineCoordinateEquation (k := k) ∈
      nonZeroDivisors Γ(Spec (CommRingCat.of (Polynomial k)), ⊤) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm Polynomial.X) ∈ nonZeroDivisors (Polynomial k)
  rw [e.apply_symm_apply, mem_nonZeroDivisors_iff_ne_zero]
  exact Polynomial.X_ne_zero

/-- The actual local point ideal has its original coordinate equation frame. -/
def affineCoordinateKernelFrameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf ≅
      schemeKernelIdeal (affineCoordinatePoint (k := k)) :=
  principalKernelSheafIso affineCoordinatePoint affineCoordinateEquation
    affineCoordinateEquation_eq_zero affineCoordinatePoint_kernel affineCoordinateEquation_regular

/-- The frame is the existing kernel lift of multiplication by the
original coordinate section, not a separately chosen isomorphism. -/
theorem affineCoordinateKernelFrameIso_hom :
    (affineCoordinateKernelFrameIso (k := k)).hom =
      schemeKernelGenerator affineCoordinatePoint affineCoordinateEquation
        affineCoordinateEquation_eq_zero := rfl

/-- Inclusion of the original local ideal sends its frame back to the
original coordinate multiplication morphism. -/
@[reassoc]
theorem affineCoordinateKernelFrameIso_hom_ι :
    (affineCoordinateKernelFrameIso (k := k)).hom ≫
      schemeKernelIdealι affineCoordinatePoint = schemeScalarEnd (affineCoordinateEquation (k := k)) :=
  schemeKernelGenerator_comp_ι affineCoordinatePoint affineCoordinateEquation
    affineCoordinateEquation_eq_zero

/-- The original coordinate point has empty inverse image in the other
standard chart. The proof uses the actual overlap projection: the first
coordinate would belong to a prime ideal while having its proved reciprocal. -/
theorem coordinatePoint_preimage_right :
    coordinatePoint (k := k) ⁻¹ᵁ ProjectiveLineComparison.chartOpen k 1 = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  change (coordinatePoint (k := k)).base x ∈
    ProjectiveLineComparison.chartOpen k 1 at hx
  rw [← ProjectiveLineComparison.chartImmersion_opensRange] at hx
  obtain ⟨y, hy⟩ := hx
  let q : Spec (CommRingCat.of (ProjectiveLineComparison.chartRing k 0)) :=
    (Spec.map (CommRingCat.ofHom
      (FrobeniusProjectivePoints.coordinateEvaluation (0 : k)))).base x
  have hxy : (ProjectiveLineComparison.chartImmersion k 0).base q =
      (ProjectiveLineComparison.chartImmersion k 1).base y := by
    change (coordinatePoint (k := k)).base x = _
    exact hy.symm
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback q y hxy
  let t : PrimeSpectrum (ProjectiveLineComparison.overlapRing k) :=
    (ProjectiveLineComparison.overlapPullbackIso k).hom.base z
  have ht : PrimeSpectrum.comap (ProjectiveLineComparison.toOverlapLeft k) t = q := by
    calc
      _ = ((ProjectiveLineComparison.overlapPullbackIso k).hom ≫
          Spec.map (CommRingCat.ofHom (ProjectiveLineComparison.toOverlapLeft k))).base z := rfl
      _ = (pullback.fst (ProjectiveLineComparison.chartImmersion k 0)
          (ProjectiveLineComparison.chartImmersion k 1)).base z :=
        congrArg (fun f : pullback (ProjectiveLineComparison.chartImmersion k 0)
            (ProjectiveLineComparison.chartImmersion k 1) ⟶
              Spec (CommRingCat.of (ProjectiveLineComparison.chartRing k 0)) => f.base z)
          (ProjectiveLineComparison.overlapPullbackIso_hom_left k)
      _ = q := hz
  have hq : ProjectiveLineComparison.coordinate k 0 1 ∈ q.asIdeal := by
    change FrobeniusProjectivePoints.coordinateEvaluation (0 : k)
      (ProjectiveLineComparison.coordinate k 0 1) ∈ x.asIdeal
    rw [ProjectiveLineComparison.coordinate_zero_one_eq_ratio,
      FrobeniusProjectivePoints.coordinateEvaluation_ratio]
    exact x.asIdeal.zero_mem
  have htcoord : ProjectiveLineComparison.toOverlapLeft k
      (ProjectiveLineComparison.coordinate k 0 1) ∈ t.asIdeal := by
    change ProjectiveLineComparison.coordinate k 0 1 ∈
      (PrimeSpectrum.comap (ProjectiveLineComparison.toOverlapLeft k) t).asIdeal
    rw [ht]
    exact hq
  have hone : (1 : ProjectiveLineComparison.overlapRing k) ∈ t.asIdeal := by
    rw [← ProjectiveLineComparison.overlap_coordinates_mul]
    exact t.asIdeal.mul_mem_right _ htcoord
  exact t.isPrime.ne_top (t.asIdeal.eq_top_iff_one.mpr hone)

/-- The actual restriction of the original closed point map to the second
standard open, with its derived empty source. -/
def rightCoordinatePoint :
    ((coordinatePoint (k := k)) ⁻¹ᵁ ProjectiveLineComparison.chartOpen k 1).toScheme ⟶
      (ProjectiveLineComparison.chartOpen k 1).toScheme :=
  coordinatePoint ∣_ ProjectiveLineComparison.chartOpen k 1

instance rightCoordinatePoint_source_isEmpty :
    IsEmpty (((coordinatePoint (k := k)) ⁻¹ᵁ
      ProjectiveLineComparison.chartOpen k 1).toScheme) := by
  refine ⟨fun x => ?_⟩
  exact (coordinatePoint_preimage_right (k := k)).le x.property

instance rightCoordinatePoint_isClosedImmersion :
    IsClosedImmersion (rightCoordinatePoint (k := k)) :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict coordinatePoint
      (ProjectiveLineComparison.chartOpen k 1)).flip inferInstance

/-- Each second-chart ideal is still the original point ideal, now proved
to be the unit ideal through the actual restriction equality. -/
theorem coordinatePointIdeal_right
    (V : (ProjectiveLineComparison.chartOpen k 1).toScheme.affineOpens) :
    (coordinatePointIdeal (k := k)).ideal
      ⟨(ProjectiveLineComparison.chartOpen k 1).ι ''ᵁ V,
        V.2.image_of_isOpenImmersion _⟩ = ⊤ := by
  rw [coordinatePointIdeal, ← Scheme.ker_morphismRestrict_ideal]
  change (rightCoordinatePoint (k := k)).ker.ideal V = ⊤
  rw [Scheme.ker_eq_top_of_isEmpty]
  rfl

/-- The unit equation is killed by the actual empty restriction map. -/
theorem rightCoordinateEquation_eq_zero :
    (rightCoordinatePoint (k := k)).appTop 1 = 0 :=
  Subsingleton.elim _ _

/-- Its actual section kernel is generated by the original unit equation. -/
theorem rightCoordinatePoint_kernel :
    RingHom.ker (rightCoordinatePoint (k := k)).appTop.hom =
      Ideal.span {(1 : Γ((ProjectiveLineComparison.chartOpen k 1).toScheme, ⊤))} := by
  rw [Ideal.span_singleton_one]
  apply top_unique
  intro r _
  exact Subsingleton.elim _ _

/-- The original right-chart kernel frame is multiplication by one. -/
def rightCoordinateKernelFrameIso :
    _root_.SheafOfModules.unit (ProjectiveLineComparison.chartOpen k 1).toScheme.ringCatSheaf ≅
      schemeKernelIdeal (rightCoordinatePoint (k := k)) := by
  letI : IsAffine (ProjectiveLineComparison.chartOpen k 1).toScheme :=
    ProjectiveLineComparison.chartOpen_isAffineOpen k 1
  exact principalKernelSheafIso rightCoordinatePoint 1 rightCoordinateEquation_eq_zero
    rightCoordinatePoint_kernel (one_mem _)

/-- The right frame is the original kernel lift with the original unit equation. -/
theorem rightCoordinateKernelFrameIso_hom :
    (rightCoordinateKernelFrameIso (k := k)).hom =
      schemeKernelGenerator rightCoordinatePoint 1 rightCoordinateEquation_eq_zero := rfl

/-- Its original ideal inclusion recovers multiplication by one. -/
@[reassoc]
theorem rightCoordinateKernelFrameIso_hom_ι :
    (rightCoordinateKernelFrameIso (k := k)).hom ≫
      schemeKernelIdealι rightCoordinatePoint = schemeScalarEnd 1 :=
  schemeKernelGenerator_comp_ι rightCoordinatePoint 1 rightCoordinateEquation_eq_zero

end KltDP.Examples.FrobeniusProjectiveCoordinateIdeal
