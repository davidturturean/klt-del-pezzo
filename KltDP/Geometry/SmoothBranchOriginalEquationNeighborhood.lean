import KltDP.Geometry.GluedBranchOriginalEquationChart
import KltDP.Geometry.SmoothCartierEquationSectionFrame

/-!
# Actual branch-normalized neighborhoods of an original prescribed equation

At an original branch point, refine the simultaneous smooth chart inside
the original coefficient open. The actual quotient point supplies the
ambient prime containing that coefficient. The determinant construction
then gives a smaller original affine open containing the same point,
with a differential basis beginning with the same restricted equation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SmoothBranchOriginalEquationNeighborhood

open TransitionUnitGluing GluedAdjunctionChartBasis
open GluedAdjunctionBasicOpenAlgebra GluedConormalBasicOpenLocalization

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)
  [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]

include hI in
/-- Every original branch point has a refined affine neighborhood whose
actual differential basis begins with the original restricted coefficient. -/
theorem exists_refined_basis (U : X.affineOpens) (s : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {s}) (hs : s ∈ nonZeroDivisors Γ(X, U.1))
    (x : I.glueData.glued) (hx : I.gluedTo.base x ∈ U.1) :
    ∃ V : X.affineOpens, ∃ hVU : V.1 ≤ U.1,
      I.gluedTo.base x ∈ V.1 ∧
      res X hVU s ∈ nonZeroDivisors Γ(X, V.1) ∧
      letI : Algebra k Γ(X, V.1) := GluedChartKaehlerPullback.chartAlgebra f V
      Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, V.1) ∧
      ∃ b : Basis (Fin 2) Γ(X, V.1) (KaehlerDifferential k Γ(X, V.1)),
        b 0 = KaehlerDifferential.D k Γ(X, V.1) (res X hVU s) := by
  obtain ⟨c, hc, hxc, hceq, hcs⟩ :=
    GluedBranchOriginalEquationChart.exists_subordinate f I hI U s hU hs x hx
  let z : PrimeSpectrum (Γ(X, c.U.1) ⧸ I.ideal c.U) :=
    (I.glueDataObjIso c.U).inv.base ⟨x, hxc⟩
  have hz : (I.glueData.ι c.U).base z = x := by
    have he : (I.glueDataObjIso c.U).inv ≫ I.glueData.ι c.U = (I.gluedTo ⁻¹ᵁ c.U.1).ι := by
      rw [← I.glueDataObjIso_hom_ι c.U, Iso.inv_hom_id_assoc]
    change ((I.glueDataObjIso c.U).inv ≫ I.glueData.ι c.U).base ⟨x, hxc⟩ = x
    rw [he]
    rfl
  let p : PrimeSpectrum Γ(X, c.U.1) := PrimeSpectrum.comap (Ideal.Quotient.mk (I.ideal c.U)) z
  have hps : res X hc s ∈ p.asIdeal := by
    change Ideal.Quotient.mk (I.ideal c.U) (res X hc s) ∈ z.asIdeal
    have hzero : Ideal.Quotient.mk (I.ideal c.U) (res X hc s) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hceq]
      exact Ideal.mem_span_singleton_self _
    rw [hzero]
    exact z.asIdeal.zero_mem
  have hp : c.U.2.fromSpec.base p = I.gluedTo.base x := by
    calc
      _ = (I.glueData.ι c.U ≫ I.gluedTo).base z := by
        rw [I.ι_gluedTo c.U, I.glueDataObjι_ι c.U]
        rfl
      _ = _ := by rw [Scheme.comp_base_apply, hz]
  obtain ⟨r, hr, b, hb⟩ :=
    SmoothCartierEquationSectionFrame.exists_basicOpen_basis f I c (res X hc s) hceq hcs p hps
  have hxr : I.gluedTo.base x ∈ (X.affineBasicOpen r).1 := by
    rw [← hp]
    change p ∈ c.U.2.fromSpec ⁻¹ᵁ X.basicOpen r
    rw [c.U.2.fromSpec_preimage_basicOpen]
    exact hr
  have hres : sectionMap c.U r (res X hc s) =
      res X ((X.affineBasicOpen_le r).trans hc) s :=
    res_res X (X.affineBasicOpen_le r) hc s
  refine ⟨X.affineBasicOpen r, (X.affineBasicOpen_le r).trans hc, hxr, ?_, ?_⟩
  · rw [← hres]
    exact equation_regular c.U r (res X hc s) hcs
  · letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
    letI : Algebra k Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    refine ⟨ambient_standardSmooth f c.U r, b, ?_⟩
    exact hb.trans (congrArg (KaehlerDifferential.D k Γ(X, (X.affineBasicOpen r).1)) hres)

end KltDP.Geometry.SmoothBranchOriginalEquationNeighborhood

#print axioms KltDP.Geometry.SmoothBranchOriginalEquationNeighborhood.exists_refined_basis
