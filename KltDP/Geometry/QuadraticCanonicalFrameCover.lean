import KltDP.Geometry.SmoothBranchOriginalEquationNeighborhood
import KltDP.Geometry.SmoothOriginalUnitNeighborhood
import KltDP.Geometry.QuadraticOriginalSubchart
import KltDP.Geometry.StandardSmoothNativeTopDifferential

/-!
# A covering family of actual canonical frames for the original quadratic atlas

Each chart retains an original atlas index, a subordinate original affine
open, its actual restricted coefficient, and an actual differential basis.
Every base point lies either in that coefficient's unit locus or in the
original branch scheme. The two proved neighborhood producers therefore
supply these frames everywhere. Their original quadratic subcharts cover
the same globally glued cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing

variable {k : Type u} [Field k] {X : Scheme.{u}} {ι : Type u}
  (D : QuadraticCoverAtlas.Data X ι) (f : X ⟶ Spec (CommRingCat.of k))

/-- Actual local coordinate data, with no canonical factor or isomorphism field. -/
structure CanonicalFrameChart where
  index : ι
  U : X.affineOpens
  le : U.1 ≤ D.opens index
  nonempty : (U.1 : Set X).Nonempty
  regular : res X le (D.sections index) ∈ nonZeroDivisors Γ(X, U.1)
  smooth :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)
  basis :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1))
  unit_or_branch :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    IsUnit (res X le (D.sections index)) ∨
      basis 0 = KaehlerDifferential.D k Γ(X, U.1) (res X le (D.sections index))

variable [IsIntegral X] (I : X.IdealSheafData) (hI : IdealLocallyPrincipalRegular I)
  [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]
  (hmatch : ∀ i, I.ideal ⟨D.opens i, D.affine i⟩ = Ideal.span {D.sections i})
  (hregular : ∀ i, (D.opens i : Set X).Nonempty →
    D.sections i ∈ nonZeroDivisors Γ(X, D.opens i))

include hI hmatch hregular in
/-- The actual geometric hypotheses produce an original frame chart at every original base point. -/
theorem exists_canonicalFrameChart (x : X) :
    ∃ c : D.CanonicalFrameChart f, x ∈ c.U.1 := by
  have hxcover : x ∈ ⨆ i, D.opens i := by rw [D.covers]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxcover
  let U : X.affineOpens := ⟨D.opens i, D.affine i⟩
  by_cases hu : x ∈ X.basicOpen (D.sections i)
  · obtain ⟨V, hVU, hxV, hunit, hsm⟩ :=
      SmoothOriginalUnitNeighborhood.exists_refined_unit f U (D.sections i) x hu
    letI : Algebra k Γ(X, V.1) := GluedChartKaehlerPullback.chartAlgebra f V
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, V.1) := hsm
    obtain ⟨b, _, _⟩ := AffineNativeTopDifferential.exists_coordinate_basis k Γ(X, V.1) 2
    exact ⟨⟨i, V, hVU, ⟨x, hxV⟩, hunit.mem_nonZeroDivisors, hsm, b, Or.inl hunit⟩, hxV⟩
  · have hxrange : x ∈ Set.range (I.glueDataObjι U ≫ U.1.ι).base := by
      rw [I.range_glueDataObjι_ι U, hmatch i, X.zeroLocus_span, X.zeroLocus_singleton]
      exact ⟨hu, hxi⟩
    obtain ⟨z, hz⟩ := hxrange
    let w := (I.glueData.ι U).base z
    have hw : I.gluedTo.base w = x := by
      change (I.glueData.ι U ≫ I.gluedTo).base z = x
      rw [I.ι_gluedTo U]
      exact hz
    obtain ⟨V, hVU, hxV, hsV, hsm, b, hb⟩ :=
      SmoothBranchOriginalEquationNeighborhood.exists_refined_basis f I hI U (D.sections i)
        (hmatch i) (hregular i ⟨x, hxi⟩) w (by rw [hw]; exact hxi)
    have hxV' : x ∈ V.1 := by simpa only [hw] using hxV
    exact ⟨⟨i, V, hVU, ⟨x, hxV'⟩, hsV, hsm, b, Or.inr hb⟩, hxV'⟩

include hI hmatch hregular in
/-- The corresponding original quadratic subcharts cover the same original global cover. -/
theorem canonicalFrameCharts_cover (y : D.scheme) :
    ∃ c : D.CanonicalFrameChart f, ∃ z : D.frameChart c.le,
      (D.frameGlobalι c.le).base z = y := by
  obtain ⟨c, hc⟩ := D.exists_canonicalFrameChart f I hI hmatch hregular (D.morphism.base y)
  have hy : y ∈ Set.range (D.frameGlobalι c.le).base := by
    rw [D.range_frameGlobalι c.le c.U.2]
    exact hc
  obtain ⟨z, hz⟩ := hy
  exact ⟨c, z, hz⟩

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.canonicalFrameCharts_cover
