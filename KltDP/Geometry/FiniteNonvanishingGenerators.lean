import KltDP.Geometry.GloballyGeneratedUnitCoefficient
import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import Mathlib.Topology.Compactness.Compact

/-!
# A finite original nonvanishing generating subcover

The nonvanishing opens of an actual generating family of an invertible
sheaf cover the original scheme. Quasi-compactness selects a finite subset
of that same index type. No base field, separation, or Noetherian hypothesis
is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.FiniteNonvanishingGenerators

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen TransitionUnitExtraction

variable {X : Scheme.{u}}

/-- Every point lies in the intrinsic nonvanishing open of an original
member of the supplied generating family. -/
theorem exists_mem_nonvanishing (L : InvertibleSheaf X)
    (G : L.obj.GeneratingSections) (x : X) :
    ∃ a : G.I, x ∈ nonvanishingOpen X L (G.s a) := by
  let t := L.localTrivializations
  have hx : x ∈ (⨆ a, t.X a) := by
    rw [chartOpens_cover X L.obj t]
    trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ := GloballyGeneratedUnitCoefficient.exists_generator_unit_coefficient
    G (t.X a) x ha (t.unitIso a)
  exact ⟨j, (mem_nonvanishingOpen_iff_isUnit_germ X L (G.s j) t a x ha).mpr hj⟩

/-- The intrinsic opens of the actual generating family cover X. -/
theorem iSup_nonvanishing_eq_top (L : InvertibleSheaf X)
    (G : L.obj.GeneratingSections) :
    (⨆ a : G.I, nonvanishingOpen X L (G.s a)) = ⊤ := by
  apply top_unique
  intro x hx
  exact Opens.mem_iSup.mpr (exists_mem_nonvanishing L G x)

/-- Compactness selects finitely many of the original generators whose
intrinsic nonvanishing opens still cover the original scheme. -/
theorem exists_finite_nonvanishing_subcover (L : InvertibleSheaf X)
    (hX : IsCompact (Set.univ : Set X)) (G : L.obj.GeneratingSections) :
    ∃ S : Finset G.I, (⨆ a : S, nonvanishingOpen X L (G.s a.val)) = ⊤ := by
  classical
  have hc : (Set.univ : Set X) ⊆
      ⋃ a : G.I, (nonvanishingOpen X L (G.s a) : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr (exists_mem_nonvanishing L G x)
  obtain ⟨S, hS⟩ := hX.elim_finite_subcover
    (fun a : G.I => (nonvanishingOpen X L (G.s a) : Set X))
    (fun a => (nonvanishingOpen X L (G.s a)).2) hc
  refine ⟨S, top_unique ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hS hx)
  exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

end KltDP.Geometry.FiniteNonvanishingGenerators
