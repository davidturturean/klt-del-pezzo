import KltDP.Examples.ProjectiveLinePointAtInfinity
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# All original closed points of the projective line

In the original finite polynomial chart, a closed point is a maximal
ideal of k[X]. Its nonzero prime generator has a root over the original
algebraically closed field. Maximality identifies that ideal with the
original evaluation ideal (X-c). The accepted chart comparison identifies
the resulting scheme point with the original `FrobeniusProjectivePoints.point c`.
The already proved complement of this chart consists of the original
point at infinity. No rationality witness is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.ProjectiveLineClosedPoints

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusGraphContact FrobeniusGraphStalkContact ProjectiveLinePointAtInfinity

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every closed point of the original polynomial affine line is an
original scalar-evaluation point. -/
theorem exists_parameterSchemePoint_of_isClosed (q : PrimeSpectrum (Polynomial k))
    (hq : IsClosed ({q} : Set (PrimeSpectrum (Polynomial k)))) :
    ∃ c : k, q = parameterSchemePoint c := by
  have hmax : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq
  have hne : q.asIdeal ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hmax (Ideal.polynomial_not_isField (R := k))
  letI : q.asIdeal.IsPrime := q.isPrime
  let p := Submodule.IsPrincipal.generator q.asIdeal
  have hp : Prime p := Submodule.IsPrincipal.prime_generator_of_isPrime q.asIdeal hne
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p
    (Polynomial.degree_pos_of_irreducible hp.irreducible).ne'
  have hle : q.asIdeal ≤ RingHom.ker (Polynomial.evalRingHom c) := by
    rw [← Ideal.span_singleton_generator q.asIdeal, Ideal.span_le]
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    change Polynomial.eval c p = 0
    exact hc
  have hker : (RingHom.ker (Polynomial.evalRingHom c)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)
  have heq := hmax.eq_of_le hker.ne_top hle
  refine ⟨c, ?_⟩
  apply PrimeSpectrum.ext
  exact heq.trans (Polynomial.ker_evalRingHom c)

/-- Every original closed projective-line point in the original finite
chart is the already constructed point with one scalar coordinate. -/
theorem exists_point_of_isClosed_of_mem_chart (z : projectiveSpace k 1)
    (hz : IsClosed ({z} : Set (projectiveSpace k 1))) (hchart : z ∈ chartOpen k 0) :
    ∃ c : k, z = FrobeniusProjectivePoints.point c := by
  have hrange : z ∈ (polynomialChartMap k 0).opensRange := by
    rw [polynomialChartMap_opensRange]
    exact hchart
  obtain ⟨q, hq⟩ := hrange
  have hpre : (polynomialChartMap k 0).base ⁻¹' {z} = {q} := by
    ext r
    change (polynomialChartMap k 0).base r = z ↔ r = q
    rw [← hq]
    exact (polynomialChartMap k 0).isOpenEmbedding.injective.eq_iff
  have hclosed : IsClosed ({q} : Set (PrimeSpectrum (Polynomial k))) := by
    rw [← hpre]
    exact hz.preimage (polynomialChartMap k 0).continuous
  obtain ⟨c, hc⟩ := exists_parameterSchemePoint_of_isClosed q hclosed
  refine ⟨c, ?_⟩
  rw [point_eq_chart, ← hc]
  exact hq.symm

/-- Every closed scheme point of the original projective line over
the original algebraically closed field is finite or the original infinity point. -/
theorem eq_point_or_eq_infinity (z : projectiveSpace k 1)
    (hz : IsClosed ({z} : Set (projectiveSpace k 1))) :
    (∃ c : k, z = FrobeniusProjectivePoints.point c) ∨
      z = ProjectiveLinePointAtInfinity.infinityPoint := by
  by_cases hchart : z ∈ chartOpen k 0
  · exact Or.inl (exists_point_of_isClosed_of_mem_chart z hz hchart)
  · exact Or.inr (eq_infinityPoint_of_not_mem_chart z hchart)

end KltDP.Examples.ProjectiveLineClosedPoints
