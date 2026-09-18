import KltDP.Geometry.LinearSystemMorphism

/-!
# The original nonvanishing opens are inverse images of projective charts

The normalized coordinate basic opens recover the original section opens.
Consequently the actual glued morphism pulls each original standard
projective chart back to precisely the corresponding section's nonvanishing
open, with no additional assumptions on the source scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

theorem basicOpen_coefficient (s : L.obj.sections) (i : L.localTrivializations.I)
    {W : X.Opens} (hWi : W ≤ L.localTrivializations.X i) :
    X.basicOpen (coefficient L s i hWi) = W ⊓ nonvanishingOpen X L s := by
  calc
    _ = X.basicOpen (res X hWi (chartCoefficient X L.obj L.localTrivializations s i)) :=
      congrArg (fun a : Γ(X, W) => X.basicOpen a)
        (chartCoefficient_restrict X L.obj L.localTrivializations s i hWi).symm
    _ = W ⊓ X.basicOpen (chartCoefficient X L.obj L.localTrivializations s i) :=
      X.basicOpen_res _ (homOfLE hWi).op
    _ = _ := by
      rw [← chart_inf_nonvanishingOpen X L s L.localTrivializations i,
        ← inf_assoc, inf_eq_left.mpr hWi]

variable {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

theorem basicOpen_coordinates (i : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) (j : Fin (n + 1)) :
    X.basicOpen (coordinates L s i hWi m hWm j) =
      W ⊓ nonvanishingOpen X L (s j) := by
  rw [coordinates, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit X ((coefficient_isUnit L (s m) i hWi hWm).unit⁻¹).isUnit,
    basicOpen_coefficient, inf_left_idem]

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

theorem chartMap_base_mem_range_iff (c : Chart L s)
    (x : Spec Γ(X, c.affineOpen.1)) (j : Fin (n + 1)) :
    (chartMap f L s c).base x ∈ Set.range (ProjectiveChart.coordinateChartMorphism k n j).base ↔
      c.affineOpen.2.fromSpec.base x ∈ nonvanishingOpen X L (s j) := by
  rw [chartMap, ProjectiveChart.tupleMorphism_base_mem_range_iff,
    ← c.affineOpen.2.fromSpec_preimage_basicOpen]
  change c.affineOpen.2.fromSpec.base x ∈ X.basicOpen
    (coordinates L s c.frame c.inFrame c.index c.nonvanishing j) ↔ _
  rw [basicOpen_coordinates]
  constructor
  · exact And.right
  · intro hj
    refine ⟨?_, hj⟩
    rw [← c.affineOpen.2.range_fromSpec]
    exact Set.mem_range_self x

/-- The actual morphism has the original section's nonvanishing open as
the exact inverse image of the corresponding standard projective chart. -/
theorem morphism_preimage_coordinateChart
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) (j : Fin (n + 1)) :
    morphism L s f hcover ⁻¹ᵁ (ProjectiveChart.coordinateChartMorphism k n j).opensRange =
      nonvanishingOpen X L (s j) := by
  ext x
  change (morphism L s f hcover).base x ∈
    Set.range (ProjectiveChart.coordinateChartMorphism k n j).base ↔ _
  let c : Chart L s := (chartCover L s hcover).f x
  have hx : x ∈ Set.range c.affineOpen.2.fromSpec.base :=
    (chartCover L s hcover).covers x
  obtain ⟨z, hz⟩ := hx
  have hp := chartMap_base_mem_range_iff L s f c z j
  rw [← chart_morphism L s f hcover c, Scheme.comp_base_apply, hz] at hp
  exact hp

end KltDP.Geometry.LinearSystemMorphism
