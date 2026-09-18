import KltDP.Geometry.LinearSystemNormalizedCoordinates
import KltDP.Geometry.AffineFiniteType

/-!
# Actual affine chart maps of a finite linear system

Each chart is an original affine subopen in an original line-bundle frame
where one of the specified sections is nonvanishing. Its normalized tuple
defines an actual map to projective space over the original field. On every
common affine subopen, the exact maps agree by their proved coordinate scaling.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

/-- An original affine chart, frame, and a selected nonvanishing section. -/
structure Chart where
  affineOpen : X.affineOpens
  frame : L.localTrivializations.I
  inFrame : affineOpen.1 ≤ L.localTrivializations.X frame
  index : Fin (n + 1)
  nonvanishing : affineOpen.1 ≤ nonvanishingOpen X L (s index)

/-- The original normalized coordinates on the spectrum of an actual affine chart. -/
def chartMap (c : Chart L s) : Spec Γ(X, c.affineOpen.1) ⟶ projectiveSpace k n :=
  ProjectiveChart.tupleMorphism n (baseToAffineSectionsMap f c.affineOpen.2).hom
    (coordinates L s c.frame c.inFrame c.index c.nonvanishing) c.index
    (coordinates_self L s c.frame c.inFrame c.index c.nonvanishing)

/-- Each original chart map respects the actual structure morphism. -/
theorem chartMap_structure (c : Chart L s) :
    chartMap f L s c ≫ projectiveSpaceToSpec k n = c.affineOpen.2.fromSpec ≫ f := by
  rw [chartMap, ProjectiveChart.tupleMorphism_structure, CommRingCat.ofHom_hom,
    Spec_map_baseToAffineSectionsMap]

/-- The exact original chart maps agree after restriction to any common affine subopen. -/
theorem chartMap_compatible (c d : Chart L s) {W : X.Opens}
    (hW : IsAffineOpen W) (hWc : W ≤ c.affineOpen.1) (hWd : W ≤ d.affineOpen.1) :
    Spec.map (CommRingCat.ofHom (res X hWc)) ≫ chartMap f L s c =
      Spec.map (CommRingCat.ofHom (res X hWd)) ≫ chartMap f L s d := by
  apply ProjectiveChart.tupleMorphism_compatible
  · exact (congrArg CommRingCat.Hom.hom
      (baseToAffineSectionsMap_restrict f c.affineOpen.2 hW hWc)).trans
        (congrArg CommRingCat.Hom.hom
          (baseToAffineSectionsMap_restrict f d.affineOpen.2 hW hWd)).symm
  · intro j
    rw [coordinates_restrict, coordinates_restrict, coordinates_restrict]
    exact coordinates_scale L s c.frame d.frame
      (hWc.trans c.inFrame) (hWd.trans d.inFrame) c.index d.index
      (hWc.trans c.nonvanishing) (hWd.trans d.nonvanishing) j

/-- The original affine charts cover when the specified section opens cover. -/
theorem chartOpens_cover (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) :
    (⨆ c : Chart L s, c.affineOpen.1) = ⊤ := by
  apply top_unique
  intro x hx
  have hs : x ∈ ⨆ j, nonvanishingOpen X L (s j) := by rw [hcover]; exact hx
  obtain ⟨m, hm⟩ := Opens.mem_iSup.mp hs
  have ht : x ∈ ⨆ i, L.localTrivializations.X i := by
    rw [TransitionUnitExtraction.chartOpens_cover]
    exact hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ht
  have hxi : x ∈ L.localTrivializations.X i ⊓ nonvanishingOpen X L (s m) := ⟨hi, hm⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hxi
      (L.localTrivializations.X i ⊓ nonvanishingOpen X L (s m)).2
  exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, i, hUV.trans inf_le_left, m,
    hUV.trans inf_le_right⟩, hxU⟩

end KltDP.Geometry.LinearSystemMorphism
