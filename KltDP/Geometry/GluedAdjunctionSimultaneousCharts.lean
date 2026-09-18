import KltDP.Geometry.GluedIdealInvertible
import KltDP.Geometry.GluedAdjunctionQuotientSmoothNeighborhood
import KltDP.Geometry.SmoothCurveCotangentInvertible

/-!
# Simultaneous original smooth charts with regular equations

Original ambient smoothness and local regular principality give a common
affine chart by the pinned common-basic-open theorem. Original smoothness
of the closed subscheme then supplies a further ambient basic open whose
actual quotient section ring is standard smooth. Every chart property is
derived from these global hypotheses.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionSimultaneousCharts

open GluedAdjunctionBasicOpenAlgebra GluedConormalBasicOpenLocalization

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

include hI in
/-- Original ambient smoothness and the original regular equation admit a common chart. -/
theorem exists_ambient [IsSmoothOfRelativeDimension 2 f] (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ d : Γ(X, U.1),
      I.ideal U = Ideal.span {d} ∧ d ∈ nonZeroDivisors Γ(X, U.1) ∧
      letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
      Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1) := by
  obtain ⟨U, hxU, d, hU, hd⟩ := hI x
  obtain ⟨V, hV, hxV, hVsm⟩ :=
    SmoothCurveCotangent.exists_affine_standardSmoothOfRelativeDimension f 2 x
  let V' : X.affineOpens := ⟨V, hV⟩
  letI : Algebra k Γ(X, V'.1) := GluedChartKaehlerPullback.chartAlgebra f V'
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, V'.1) := hVsm.toAlgebra
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter U.2 hV x ⟨hxU, hxV⟩
  have hW : X.affineBasicOpen r = X.affineBasicOpen (U := V') s := Subtype.ext hrs
  refine ⟨X.affineBasicOpen r, hxr, sectionMap U r d,
    equation_span I U r d hU, equation_regular U r d hd, ?_⟩
  rw [hW]
  exact ambient_standardSmooth f V' s

include hI in
/-- Every point of the original closed subscheme has an actual simultaneous
ambient dimension-two and quotient dimension-one chart with a regular equation. -/
theorem exists_chart [IsSmoothOfRelativeDimension 2 f]
    [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)] (x : I.glueData.glued) :
    ∃ U : X.affineOpens, x ∈ I.gluedTo ⁻¹ᵁ U.1 ∧ ∃ d : Γ(X, U.1),
      I.ideal U = Ideal.span {d} ∧ d ∈ nonZeroDivisors Γ(X, U.1) ∧
      letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
      Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1) ∧
        Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, U.1) ⧸ I.ideal U) := by
  obtain ⟨U, hxU, d, hU, hd, hA⟩ := exists_ambient f I hI (I.gluedTo.base x)
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1) := hA
  let p : PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U) :=
    (I.glueDataObjIso U).inv.base ⟨x, hxU⟩
  have hp : (I.glueData.ι U).base p = x := by
    have he : (I.glueDataObjIso U).inv ≫ I.glueData.ι U = (I.gluedTo ⁻¹ᵁ U.1).ι := by
      rw [← I.glueDataObjIso_hom_ι U, Iso.inv_hom_id_assoc]
    change ((I.glueDataObjIso U).inv ≫ I.glueData.ι U).base ⟨x, hxU⟩ = x
    rw [he]
    rfl
  obtain ⟨r, hxr, hQ⟩ :=
    GluedAdjunctionQuotientSmoothNeighborhood.exists_basicOpen f I U p
  refine ⟨X.affineBasicOpen r, ?_, sectionMap U r d,
    equation_span I U r d hU, equation_regular U r d hd, ?_⟩
  · change I.gluedTo.base x ∈ X.basicOpen r
    simpa only [Scheme.comp_base_apply, hp] using hxr
  · letI : Algebra k Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    exact ⟨ambient_standardSmooth f U r, hQ⟩

end KltDP.Geometry.GluedAdjunctionSimultaneousCharts
