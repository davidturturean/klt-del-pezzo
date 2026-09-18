import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveSpaceTupleMorphism
import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.PrimeCurveComplementPicardKernel
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Prime.Lemmas

/-!
# The original coordinate hyperplane in the actual projective plane

The homogeneous prime `(X₀)` has closure equal to the complement of
the first affine chart. The actual point `[0:0:1]` specializes from it
and is distinct from it. Its closure is therefore an actual prime curve.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProjectivePlaneBoundary

open ProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type u) [Field k]

/-- The original coordinate-chart image, in the form used by `appIso`. -/
def chartOpen (i : Fin 3) : (projectiveSpace k 2).Opens :=
  (coordinateChartMorphism k 2 i) ''ᵁ ⊤

theorem mem_chartOpen_iff (x : projectiveSpace k 2) (i : Fin 3) :
    x ∈ chartOpen k i ↔
      (MvPolynomial.X i : homogeneousRing k 2) ∉ x.asHomogeneousIdeal := by
  rw [chartOpen, Scheme.Hom.image_top_eq_opensRange,
    coordinateChartMorphism_opensRange]
  rfl

private theorem coordinate_zero_prime :
    Prime (MvPolynomial.X (0 : Fin 3) : homogeneousRing k 2) := by
  apply (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv k 2)).mp
  rw [MvPolynomial.finSuccEquiv_X_zero]
  exact Polynomial.prime_X

private def coordinateIdeal : HomogeneousIdeal (grading k 2) :=
  ⟨Ideal.span {MvPolynomial.X (0 : Fin 3)},
    Ideal.homogeneous_span (grading k 2) _ (by
      intro f hf
      rcases Set.mem_singleton_iff.mp hf with rfl
      exact ⟨1, coordinate_mem k 2 0⟩)⟩

private theorem coordinate_mem_irrelevant (i : Fin 3) :
    (MvPolynomial.X i : homogeneousRing k 2) ∈
      HomogeneousIdeal.irrelevant (grading k 2) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne (grading k 2)
    (coordinate_mem k 2 i) (by decide : (1 : ℕ) ≠ 0)

/-- The original homogeneous prime of the coordinate hyperplane. -/
def boundaryPoint : projectiveSpace k 2 where
  asHomogeneousIdeal := coordinateIdeal k
  isPrime := (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero (R := k) (0 : Fin 3))).mpr
    (coordinate_zero_prime k)
  not_irrelevant_le := by
    intro h
    have hx : (MvPolynomial.X (1 : Fin 3) : homogeneousRing k 2) ∈
        Ideal.span {MvPolynomial.X (0 : Fin 3)} := h (coordinate_mem_irrelevant k 1)
    have hd := Ideal.mem_span_singleton.mp hx
    have heq := MvPolynomial.X_dvd_X.mp hd
    exact (by decide : (0 : Fin 3) ≠ 1) heq

/-- The closure is the literal complement of the original first chart. -/
theorem closure_boundaryPoint :
    closure ({boundaryPoint k} : Set (projectiveSpace k 2)) =
      (chartOpen k 0 : Set (projectiveSpace k 2))ᶜ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus (grading k 2)
    ((Ideal.span {(MvPolynomial.X (0 : Fin 3) : homogeneousRing k 2)} :
      Ideal (homogeneousRing k 2)) : Set (homogeneousRing k 2)) = _
  rw [ProjectiveSpectrum.zeroLocus_span]
  rw [chartOpen, Scheme.Hom.image_top_eq_opensRange,
    coordinateChartMorphism_opensRange]
  change ProjectiveSpectrum.zeroLocus (grading k 2) {MvPolynomial.X (0 : Fin 3)} =
    (ProjectiveSpectrum.basicOpen (grading k 2) (MvPolynomial.X (0 : Fin 3)) :
      Set (ProjectiveSpectrum (grading k 2)))ᶜ
  rw [ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]

private theorem boundaryPoint_mem_chart_one : boundaryPoint k ∈ chartOpen k 1 := by
  rw [mem_chartOpen_iff]
  change (MvPolynomial.X (1 : Fin 3) : homogeneousRing k 2) ∉
    Ideal.span {MvPolynomial.X (0 : Fin 3)}
  simpa only [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X] using
    (by decide : (0 : Fin 3) ≠ 1)

/-- The boundary generic point differs from the original surface generic point. -/
theorem boundaryPoint_ne_genericPoint :
    boundaryPoint k ≠ genericPoint (projectivePlaneSurface k).toScheme := by
  have hz : (projectiveSpaceZeroPrime k 2 : projectiveSpace k 2) ∈ chartOpen k 0 := by
    apply (mem_chartOpen_iff k (projectiveSpaceZeroPrime k 2) 0).mpr
    change (MvPolynomial.X (0 : Fin 3) : homogeneousRing k 2) ∉
      (⊥ : Ideal (homogeneousRing k 2))
    simpa only [Ideal.mem_bot] using MvPolynomial.X_ne_zero (R := k) (0 : Fin 3)
  have hmem : genericPoint (projectivePlaneSurface k).toScheme ∈ chartOpen k 0 := by
    apply ((genericPoint_spec (projectivePlaneSurface k).toScheme).mem_open_set_iff
      (chartOpen k 0).isOpen).mpr
    exact ⟨projectiveSpaceZeroPrime k 2, Set.mem_univ _, hz⟩
  intro h
  have hb : boundaryPoint k ∈ chartOpen k 0 := h.symm ▸ hmem
  have hn := (mem_chartOpen_iff k (boundaryPoint k) 0).mp hb
  exact hn (Ideal.subset_span (Set.mem_singleton _))

/-- The concrete tuple `[0:0:1]` is a distinct specialization, so the
boundary generic point is not a closed point of the original plane. -/
theorem boundaryPoint_not_closed :
    ¬ IsClosed ({boundaryPoint k} : Set (projectiveSpace k 2)) := by
  let r : Fin 3 → k := fun i => if i = 2 then 1 else 0
  have hr : r 2 = 1 := by simp [r]
  let z : projectiveSpace k 2 :=
    (tupleMorphism 2 (RingHom.id k) r 2 hr).base (IsLocalRing.closedPoint k)
  have hz0 : z ∉ chartOpen k 0 := by
    rw [chartOpen, Scheme.Hom.image_top_eq_opensRange]
    change z ∉ Set.range (coordinateChartMorphism k 2 0).base
    rw [tupleMorphism_base_mem_range_iff]
    simp [r]
  have hz1 : z ∉ chartOpen k 1 := by
    rw [chartOpen, Scheme.Hom.image_top_eq_opensRange]
    change z ∉ Set.range (coordinateChartMorphism k 2 1).base
    rw [tupleMorphism_base_mem_range_iff]
    simp [r]
  intro hclosed
  have hz : z ∈ closure ({boundaryPoint k} : Set (projectiveSpace k 2)) := by
    rw [closure_boundaryPoint]
    exact hz0
  rw [hclosed.closure_eq] at hz
  have heq : z = boundaryPoint k := Set.mem_singleton_iff.mp hz
  exact hz1 (heq.symm ▸ boundaryPoint_mem_chart_one k)

/-- The actual prime curve given by the original coordinate hyperplane. -/
def primeCurve : (projectivePlaneSurface k).PrimeCurve :=
  (projectivePlaneSurface k).primeCurveOfNonclosedPoint (boundaryPoint k)
    (boundaryPoint_ne_genericPoint k) (boundaryPoint_not_closed k)

theorem primeCurve_carrier :
    (primeCurve k : Set (projectivePlaneSurface k).toScheme) =
      (chartOpen k 0 : Set (projectiveSpace k 2))ᶜ :=
  closure_boundaryPoint k

variable [IsAlgClosed k]

/-- Every original prime outside the first chart is this original boundary. -/
theorem eq_primeCurve_of_genericPoint_not_mem
    (C : (projectivePlaneSurface k).PrimeCurve)
    (hC : C.genericPoint ∉ chartOpen k 0) : C = primeCurve k := by
  apply PrimeCurveComplementKernel.eq_of_genericPoint_mem C (primeCurve k)
  rw [primeCurve_carrier]
  exact hC

end KltDP.Geometry.ProjectivePlaneBoundary

#check @KltDP.Geometry.ProjectivePlaneBoundary.primeCurve
#check @KltDP.Geometry.ProjectivePlaneBoundary.eq_primeCurve_of_genericPoint_not_mem
#print axioms KltDP.Geometry.ProjectivePlaneBoundary.primeCurve
#print axioms KltDP.Geometry.ProjectivePlaneBoundary.primeCurve_carrier
#print axioms KltDP.Geometry.ProjectivePlaneBoundary.eq_primeCurve_of_genericPoint_not_mem
