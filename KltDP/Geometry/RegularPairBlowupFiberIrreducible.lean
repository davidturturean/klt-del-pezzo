import KltDP.Geometry.AffineBlowupRegularPairExceptional
import KltDP.Geometry.AffineBlowupExceptionalIntersection
import Mathlib.Data.Fin.VecNotation

/-!
# Irreducibility of the original center fiber on two regular-parameter charts

Each original exceptional quotient chart is a polynomial ring over the
original prime center quotient. Its original ratio gives a point in both
charts. The first chart is therefore dense in their union, which the actual
generator cover identifies with the entire original scheme-theoretic fiber.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RegularPairBlowupFiber

open AffineBlowup AffineBlowupRegularPairChart

private theorem irreducibleSpace_of_two_sets
    {T : Type u} [TopologicalSpace T] {A B : Set T}
    (hA : IsIrreducible A) (hB : IsIrreducible B) (hopen : IsOpen A)
    (hmeet : (A ∩ B).Nonempty) (hcover : A ∪ B = Set.univ) :
    IrreducibleSpace T := by
  have hBsub : B ⊆ closure A :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hB.2 hopen
      (by rwa [Set.inter_comm])).trans (closure_mono Set.inter_subset_right)
  have hclosure : closure A = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    exact hx.elim (fun hxA => subset_closure hxA) (fun hxB => hBsub hxB)
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set T)
  rw [← hclosure]
  exact hA.closure

variable {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime] (a b : I)
    (ha : (a : R) ∈ nonZeroDivisors R)
    (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
      nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
    (hI : I = Ideal.span {(a : R), (b : R)})

include ha hb hI

/-- The original quotient chart is integral, using the actual proved
polynomial presentation over the original prime center quotient. -/
theorem exceptionalChart_isDomain : IsDomain (exceptionalChartRing I a) :=
  MulEquiv.isDomain (Polynomial (R ⧸ I))
    (exceptionalChartEquiv I a b ha hb hI).toMulEquiv

/-- The two actual exceptional-chart images intersect. The original
left generic point belongs to the right chart because its actual ratio
maps to the nonzero polynomial variable in the original quotient. -/
theorem exceptionalChart_images_inter_nonempty :
    (Set.range (exceptionalChartToFiber I a).base ∩
      Set.range (exceptionalChartToFiber I b).base).Nonempty := by
  letI : IsDomain (exceptionalChartRing I a) := exceptionalChart_isDomain I a b ha hb hI
  let p : exceptionalChart I a := ⟨⊥, Ideal.bot_prime⟩
  let z : centerFiber I := (exceptionalChartToFiber I a).base p
  refine ⟨z, ⟨p, rfl⟩, ?_⟩
  rw [exceptionalChartToFiber_range]
  have hz : (centerFiberι I).base z =
      (chartι I a).base ((exceptionalChartInclusion I a).base p) :=
    congrArg (fun f : exceptionalChart I a ⟶ scheme I => f.base p)
      (exceptionalChartToFiber_ι I a)
  change (centerFiberι I).base z ∈ Set.range (chartι I b).base
  rw [hz]
  change (exceptionalChartInclusion I a).base p ∈
    (chartι I a).base ⁻¹' Set.range (chartι I b).base
  rw [chart_preimage_chart_range]
  change Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b) ∉
    (⊥ : Ideal (exceptionalChartRing I a))
  rw [Ideal.mem_bot]
  intro hzero
  have h := congrArg (exceptionalChartEquiv I a b ha hb hI) hzero
  rw [exceptionalChartEquiv_fraction, map_zero] at h
  exact Polynomial.X_ne_zero h

/-- With the two actual regular-pair presentations, the entire original
scheme-theoretic center fiber is irreducible. No fiber model, rationality
or irreducibility premise is supplied. -/
theorem centerFiber_irreducible
    (hb' : (b : R) ∈ nonZeroDivisors R)
    (ha' : Ideal.Quotient.mk (Ideal.span {(b : R)}) (a : R) ∈
      nonZeroDivisors (R ⧸ Ideal.span {(b : R)})) :
    IrreducibleSpace (centerFiber I) := by
  letI : IsDomain (exceptionalChartRing I a) := exceptionalChart_isDomain I a b ha hb hI
  letI : IsDomain (exceptionalChartRing I b) :=
    exceptionalChart_isDomain I b a hb' ha' (hI.trans Ideal.span_pair_comm)
  letI : IrreducibleSpace (exceptionalChart I a) := by
    change IrreducibleSpace (Spec (CommRingCat.of (exceptionalChartRing I a)))
    infer_instance
  letI : IrreducibleSpace (exceptionalChart I b) := by
    change IrreducibleSpace (Spec (CommRingCat.of (exceptionalChartRing I b)))
    infer_instance
  let A : Set (centerFiber I) := Set.range (exceptionalChartToFiber I a).base
  let B : Set (centerFiber I) := Set.range (exceptionalChartToFiber I b).base
  have hA : IsIrreducible A := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (exceptionalChart I a)).image
        (exceptionalChartToFiber I a).base (exceptionalChartToFiber I a).continuous.continuousOn
  have hB : IsIrreducible B := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (exceptionalChart I b)).image
        (exceptionalChartToFiber I b).base (exceptionalChartToFiber I b).continuous.continuousOn
  apply irreducibleSpace_of_two_sets hA hB
    (exceptionalChartToFiber I a).isOpenEmbedding.isOpen_range
    (exceptionalChart_images_inter_nonempty I a b ha hb hI)
  let s : Fin 2 → I := ![a, b]
  have hs : Ideal.span (Set.range (fun i => (s i : R))) = I := by
    have hfun : (fun i => (s i : R)) = ![(a : R), (b : R)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun, Matrix.range_cons_cons_empty]
    exact hI.symm
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨i, p, hp⟩ := exceptionalCharts_cover I s hs x
  fin_cases i
  · exact Or.inl ⟨p, hp⟩
  · exact Or.inr ⟨p, hp⟩

end KltDP.Geometry.RegularPairBlowupFiber

#print axioms KltDP.Geometry.RegularPairBlowupFiber.centerFiber_irreducible
