import KltDP.Geometry.GluedAdjunctionSimultaneousCharts

/-!
# The original simultaneous adjunction charts form a basis

The chart records contain only actual equations and standard smoothness
of the original section rings. Their existence is proved from the original
global hypotheses. Principal refinement preserves every field, and the
pinned affine common-basic-open theorem gives simultaneous refinements
of two charts near each point of their intersection.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.GluedAdjunctionChartBasis

open GluedAdjunctionBasicOpenAlgebra GluedConormalBasicOpenLocalization

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)

/-- An actual simultaneous chart, without any transition-map assumption. -/
structure Chart where
  U : X.affineOpens
  d : Γ(X, U.1)
  equation : I.ideal U = Ideal.span {d}
  regular : d ∈ nonZeroDivisors Γ(X, U.1)
  ambient :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)
  curve :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, U.1) ⧸ I.ideal U)

namespace Chart

variable {f I} (c : Chart f I)

/-- The actual open of the original closed subscheme belonging to a chart. -/
abbrev sourceOpen : I.glueData.glued.Opens := I.gluedTo ⁻¹ᵁ c.U.1

/-- Restrict the original chart along the original ambient principal open. -/
def basicOpen (r : Γ(X, c.U.1)) : Chart f I where
  U := X.affineBasicOpen r
  d := sectionMap c.U r c.d
  equation := equation_span I c.U r c.d c.equation
  regular := equation_regular c.U r c.d c.regular
  ambient := by
    letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
    exact ambient_standardSmooth f c.U r
  curve := by
    letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, c.U.1) ⧸ I.ideal c.U) := c.curve
    exact quotient_standardSmooth f I c.U r

theorem basicOpen_le (r : Γ(X, c.U.1)) : (c.basicOpen r).sourceOpen ≤ c.sourceOpen :=
  I.gluedTo.preimage_le_preimage_of_le (X.affineBasicOpen_le r)

/-- The same actual ambient open is a principal refinement of both original charts. -/
theorem exists_common_basicOpen (e : Chart f I) (x : I.glueData.glued)
    (hx : x ∈ c.sourceOpen ⊓ e.sourceOpen) :
    ∃ (r : Γ(X, c.U.1)) (s : Γ(X, e.U.1)),
      (c.basicOpen r).U = (e.basicOpen s).U ∧ x ∈ (c.basicOpen r).sourceOpen := by
  obtain ⟨r, s, hrs, hxr⟩ :=
    exists_basicOpen_le_affine_inter c.U.2 e.U.2 (I.gluedTo.base x) hx
  exact ⟨r, s, Subtype.ext hrs, hxr⟩

end Chart

variable (hI : IdealLocallyPrincipalRegular I)
  [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]

include hI in
/-- The original hypotheses produce an actual chart at each original closed-scheme point. -/
theorem exists_mem (x : I.glueData.glued) : ∃ c : Chart f I, x ∈ c.sourceOpen := by
  obtain ⟨U, hx, d, hU, hd, hA, hQ⟩ :=
    GluedAdjunctionSimultaneousCharts.exists_chart f I hI x
  exact ⟨⟨U, d, hU, hd, hA, hQ⟩, hx⟩

include hI in
/-- These actual simultaneous chart opens form a basis of the original closed subscheme. -/
theorem isBasis : Opens.IsBasis (Set.range (Chart.sourceOpen (f := f) (I := I))) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro W x hx
  obtain ⟨c, hxc⟩ := exists_mem f I hI x
  obtain ⟨V, hVopen, hV⟩ :=
    (IsClosedImmersion.base_closed (f := I.gluedTo)).toIsEmbedding.toIsInducing.isOpen_iff.mp
      W.isOpen
  let Vop : X.Opens := ⟨V, hVopen⟩
  have hyV : I.gluedTo.base x ∈ Vop := by
    have : x ∈ I.gluedTo.base ⁻¹' V := by rw [hV]; exact hx
    exact this
  obtain ⟨r, hr, hxr⟩ := c.U.2.exists_basicOpen_le ⟨I.gluedTo.base x, hyV⟩ hxc
  refine ⟨(c.basicOpen r).sourceOpen, ⟨c.basicOpen r, rfl⟩, hxr, ?_⟩
  intro y hy
  show y ∈ (W : Set I.glueData.glued)
  rw [← hV]
  exact hr hy

end KltDP.Geometry.GluedAdjunctionChartBasis
