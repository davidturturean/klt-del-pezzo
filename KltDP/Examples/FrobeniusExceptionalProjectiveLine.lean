import KltDP.Examples.FrobeniusExceptionalOverlap
import KltDP.Geometry.AffineBlowupExceptionalIntersection
import KltDP.Geometry.ProjectiveLineSections

/-!
# The actual exceptional fiber of the origin blowup is the projective line

Both exceptional affine charts, their scheme-theoretic intersection and
their Laurent coordinate restrictions have already been constructed from
the actual Rees algebra. Here those exact maps are compared with the
actual homogeneous charts of `projectiveSpace k 1`. The existing two-open
gluing theorem then constructs an isomorphism of the whole center fiber
with the projective line. No projective-line fiber identification is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalProjectiveLine

open KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusExceptionalCharts
open FrobeniusExceptionalOverlap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The first actual homogeneous chart ring maps isomorphically to the first exceptional quotient. -/
def leftRingEquiv : KltDP.Geometry.ProjectiveLineComparison.chartRing k 0 ≃+*
    exceptionalChartRing centerIdeal (centerU (k := k)) :=
  (KltDP.Geometry.ProjectiveLineComparison.firstChartPolynomialEquiv k).trans uExceptionalEquiv.symm

/-- The second actual homogeneous chart ring maps isomorphically to the second exceptional quotient. -/
def rightRingEquiv : KltDP.Geometry.ProjectiveLineComparison.chartRing k 1 ≃+*
    exceptionalChartRing centerIdeal (centerV (k := k)) :=
  (KltDP.Geometry.ProjectiveLineComparison.secondChartPolynomialEquiv k).trans vExceptionalEquiv.symm

/-- The actual homogeneous overlap and exceptional overlap are compared through their Laurent maps. -/
def overlapRingEquiv : KltDP.Geometry.ProjectiveLineComparison.overlapRing k ≃+*
    exceptionalOverlapRing centerIdeal (centerU (k := k)) centerV :=
  (KltDP.Geometry.ProjectiveLineComparison.overlapLaurentEquiv k).trans
    exceptionalOverlapLaurentEquiv.symm

private theorem invert_toLaurent_eq_aeval (p : Polynomial k) :
    LaurentPolynomial.invert (Polynomial.toLaurent p) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) p := by
  have h : LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent (R := k)) =
      (Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r)) =
        Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) (Polynomial.C r)
      rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C, Polynomial.aeval_C,
        LaurentPolynomial.C_eq_algebraMap]
    · change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.X : Polynomial k)) =
        Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) Polynomial.X
      rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T, Polynomial.aeval_X]
  exact RingHom.congr_fun h p

/-- The entire first coordinate restriction commutes with the actual ring comparisons. -/
theorem overlapRingEquiv_left (x : KltDP.Geometry.ProjectiveLineComparison.chartRing k 0) :
    exceptionalOverlapLeft centerIdeal (centerU (k := k)) centerV (leftRingEquiv x) =
      overlapRingEquiv (KltDP.Geometry.ProjectiveLineComparison.toOverlapLeft k x) := by
  apply exceptionalOverlapLaurentEquiv.injective
  rw [exceptionalOverlapLaurentEquiv_left]
  simp only [leftRingEquiv, overlapRingEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  exact (KltDP.Geometry.ProjectiveLineComparison.overlapLaurentEquiv_left k x).symm

/-- The entire second coordinate restriction commutes, with the actual inverse coordinate. -/
theorem overlapRingEquiv_right (x : KltDP.Geometry.ProjectiveLineComparison.chartRing k 1) :
    exceptionalOverlapRight centerIdeal (centerU (k := k)) centerV (rightRingEquiv x) =
      overlapRingEquiv (KltDP.Geometry.ProjectiveLineComparison.toOverlapRight k x) := by
  apply exceptionalOverlapLaurentEquiv.injective
  rw [exceptionalOverlapLaurentEquiv_right]
  simp only [rightRingEquiv, overlapRingEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  rw [invert_toLaurent_eq_aeval, KltDP.Geometry.ProjectiveLineSections.overlapLaurentEquiv_right]

/-- The actual first affine-chart comparison as an isomorphism of schemes. -/
def leftChartIso : exceptionalChart centerIdeal (centerU (k := k)) ≅
    Spec (CommRingCat.of (KltDP.Geometry.ProjectiveLineComparison.chartRing k 0)) :=
  Scheme.Spec.mapIso leftRingEquiv.toCommRingCatIso.op

/-- The actual second affine-chart comparison as an isomorphism of schemes. -/
def rightChartIso : exceptionalChart centerIdeal (centerV (k := k)) ≅
    Spec (CommRingCat.of (KltDP.Geometry.ProjectiveLineComparison.chartRing k 1)) :=
  Scheme.Spec.mapIso rightRingEquiv.toCommRingCatIso.op

/-- The actual overlap comparison as an isomorphism of schemes. -/
def overlapIso : exceptionalOverlapScheme centerIdeal (centerU (k := k)) centerV ≅
    Spec (CommRingCat.of (KltDP.Geometry.ProjectiveLineComparison.overlapRing k)) :=
  Scheme.Spec.mapIso overlapRingEquiv.toCommRingCatIso.op

@[reassoc] theorem overlapIso_left :
    exceptionalOverlapLeftMorphism centerIdeal (centerU (k := k)) centerV ≫ leftChartIso.hom =
      overlapIso.hom ≫ Spec.map
        (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapLeft k)) := by
  change Spec.map (CommRingCat.ofHom (exceptionalOverlapLeft centerIdeal centerU centerV)) ≫
      Spec.map (CommRingCat.ofHom leftRingEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom overlapRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapLeft k))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : KltDP.Geometry.ProjectiveLineComparison.chartRing k 0 →+*
      exceptionalOverlapRing centerIdeal centerU centerV => Spec.map (CommRingCat.ofHom f))
  exact RingHom.ext overlapRingEquiv_left

@[reassoc] theorem overlapIso_right :
    exceptionalOverlapRightMorphism centerIdeal (centerU (k := k)) centerV ≫ rightChartIso.hom =
      overlapIso.hom ≫ Spec.map
        (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapRight k)) := by
  change Spec.map (CommRingCat.ofHom (exceptionalOverlapRight centerIdeal centerU centerV)) ≫
      Spec.map (CommRingCat.ofHom rightRingEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom overlapRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapRight k))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : KltDP.Geometry.ProjectiveLineComparison.chartRing k 1 →+*
      exceptionalOverlapRing centerIdeal centerU centerV => Spec.map (CommRingCat.ofHom f))
  exact RingHom.ext overlapRingEquiv_right

/-- The first actual exceptional affine chart maps to the first chart of the projective line. -/
def leftToProjectiveLine : exceptionalChart centerIdeal (centerU (k := k)) ⟶
    KltDP.Geometry.projectiveSpace k 1 :=
  leftChartIso.hom ≫ KltDP.Geometry.ProjectiveLineComparison.chartImmersion k 0

/-- The second actual exceptional affine chart maps to the second chart of the projective line. -/
def rightToProjectiveLine : exceptionalChart centerIdeal (centerV (k := k)) ⟶
    KltDP.Geometry.projectiveSpace k 1 :=
  rightChartIso.hom ≫ KltDP.Geometry.ProjectiveLineComparison.chartImmersion k 1

instance : IsOpenImmersion (leftToProjectiveLine (k := k)) := by
  unfold leftToProjectiveLine
  infer_instance

instance : IsOpenImmersion (rightToProjectiveLine (k := k)) := by
  unfold rightToProjectiveLine
  infer_instance

private theorem projectiveOverlap_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapLeft k)))
      (Spec.map (CommRingCat.ofHom (KltDP.Geometry.ProjectiveLineComparison.toOverlapRight k)))
      (KltDP.Geometry.ProjectiveLineComparison.chartImmersion k 0)
      (KltDP.Geometry.ProjectiveLineComparison.chartImmersion k 1) := by
  let e := KltDP.Geometry.ProjectiveLineComparison.overlapPullbackIso k
  refine IsPullback.of_iso_pullback ?_ e.symm ?_ ?_
  · constructor
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, KltDP.Geometry.ProjectiveLineComparison.overlapPullbackIso_hom_left,
      ← Category.assoc, KltDP.Geometry.ProjectiveLineComparison.overlapPullbackIso_hom_right,
      pullback.condition]
  · apply (cancel_epi e.hom).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact (KltDP.Geometry.ProjectiveLineComparison.overlapPullbackIso_hom_left k).symm
  · apply (cancel_epi e.hom).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact (KltDP.Geometry.ProjectiveLineComparison.overlapPullbackIso_hom_right k).symm

/-- The derived exceptional overlap is the actual overlap of these two projective charts. -/
theorem projectiveComparison_isPullback :
    IsPullback (exceptionalOverlapLeftMorphism centerIdeal (centerU (k := k)) centerV)
      (exceptionalOverlapRightMorphism centerIdeal centerU centerV)
      leftToProjectiveLine rightToProjectiveLine := by
  apply (projectiveOverlap_isPullback (k := k)).of_iso (overlapIso (k := k)).symm
    (leftChartIso (k := k)).symm (rightChartIso (k := k)).symm
    (Iso.refl (KltDP.Geometry.projectiveSpace k 1))
  · apply (cancel_epi (overlapIso (k := k)).hom).mp
    apply (cancel_mono (leftChartIso (k := k)).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact (overlapIso_left (k := k)).symm
  · apply (cancel_epi (overlapIso (k := k)).hom).mp
    apply (cancel_mono (rightChartIso (k := k)).hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact (overlapIso_right (k := k)).symm
  · simp only [Iso.refl_hom, Iso.symm_hom, leftToProjectiveLine, Category.comp_id,
      Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, rightToProjectiveLine, Category.comp_id,
      Iso.inv_hom_id_assoc]

/-- The actual exceptional affine charts cover the center fiber. -/
theorem fiber_two_charts_cover (x : centerFiber (centerIdeal (k := k))) :
    (∃ y, (exceptionalChartToFiber centerIdeal centerU).base y = x) ∨
      (∃ y, (exceptionalChartToFiber centerIdeal centerV).base y = x) := by
  obtain ⟨i, y, hy⟩ := exceptionalCharts_cover centerIdeal
    (centerGenerator (k := k)) span_centerGenerator x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-- Their proved comparisons also cover the whole projective line. -/
theorem projective_two_charts_cover (x : KltDP.Geometry.projectiveSpace k 1) :
    (∃ y, (leftToProjectiveLine (k := k)).base y = x) ∨
      (∃ y, (rightToProjectiveLine (k := k)).base y = x) := by
  obtain ⟨i, y, hy⟩ := (KltDP.Geometry.ProjectiveLineComparison.affineCover k).openCover.exists_eq x
  change Fin 2 at i
  fin_cases i
  · refine Or.inl ⟨leftChartIso.inv.base y, ?_⟩
    rw [← Scheme.comp_base_apply, leftToProjectiveLine, Iso.inv_hom_id_assoc]
    exact hy
  · refine Or.inr ⟨rightChartIso.inv.base y, ?_⟩
    rw [← Scheme.comp_base_apply, rightToProjectiveLine, Iso.inv_hom_id_assoc]
    exact hy

/-- The entire actual scheme-theoretic exceptional fiber of the polynomial-plane
origin blowup is isomorphic to the actual projective line over the coefficient field. -/
def exceptionalFiberProjectiveLineIso : centerFiber (centerIdeal (k := k)) ≅
    KltDP.Geometry.projectiveSpace k 1 :=
  (KltDP.SchemeTwoOpenGluing.isoOfCover
    (exceptionalOverlapLeftMorphism centerIdeal centerU centerV)
    (exceptionalOverlapRightMorphism centerIdeal centerU centerV)
    (exceptionalChartToFiber centerIdeal centerU) (exceptionalChartToFiber centerIdeal centerV)
    (exceptionalOverlap_isPullback centerIdeal centerU centerV) fiber_two_charts_cover).symm ≪≫
  KltDP.SchemeTwoOpenGluing.isoOfCover
    (exceptionalOverlapLeftMorphism centerIdeal centerU centerV)
    (exceptionalOverlapRightMorphism centerIdeal centerU centerV)
    leftToProjectiveLine rightToProjectiveLine projectiveComparison_isPullback projective_two_charts_cover

/-- The global comparison restricts to the constructed first chart comparison. -/
@[reassoc] theorem exceptionalFiberProjectiveLineIso_hom_left :
    exceptionalChartToFiber centerIdeal (centerU (k := k)) ≫
      exceptionalFiberProjectiveLineIso.hom = leftToProjectiveLine := by
  dsimp only [exceptionalFiberProjectiveLineIso, Iso.trans_hom, Iso.symm_hom,
    KltDP.SchemeTwoOpenGluing.isoOfCover]
  rw [← Category.assoc, KltDP.SchemeTwoOpenGluing.a_fromTarget,
    KltDP.SchemeTwoOpenGluing.leftι_toTarget]

/-- The global comparison restricts to the constructed second chart comparison. -/
@[reassoc] theorem exceptionalFiberProjectiveLineIso_hom_right :
    exceptionalChartToFiber centerIdeal (centerV (k := k)) ≫
      exceptionalFiberProjectiveLineIso.hom = rightToProjectiveLine := by
  dsimp only [exceptionalFiberProjectiveLineIso, Iso.trans_hom, Iso.symm_hom,
    KltDP.SchemeTwoOpenGluing.isoOfCover]
  rw [← Category.assoc, KltDP.SchemeTwoOpenGluing.b_fromTarget,
    KltDP.SchemeTwoOpenGluing.rightι_toTarget]

end KltDP.Examples.FrobeniusExceptionalProjectiveLine
