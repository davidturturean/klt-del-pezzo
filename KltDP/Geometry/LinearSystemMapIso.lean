import KltDP.Geometry.LinearSystemIsoCoordinates
import KltDP.Geometry.LinearSystemMorphism

/-!
# Isomorphism invariance of the actual linear-system morphism

Common affine subopens of the two original chart systems cover the source.
On them the original transition unit gives the scaling identity for the
unchanged tuple morphisms. Thus transporting the original sections by an
actual invertible-sheaf isomorphism preserves the actual glued morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing InvertibleSectionNonvanishingOpen LinearSystemMorphism

variable {X : Scheme.{u}} (L M : InvertibleSheaf X) {n : ℕ}
  (s : Fin (n + 1) → L.obj.sections) (t : Fin (n + 1) → M.obj.sections)

private structure CommonChart where
  left : Chart L s
  right : Chart M t
  affineOpen : X.affineOpens
  le_left : affineOpen.1 ≤ left.affineOpen.1
  le_right : affineOpen.1 ≤ right.affineOpen.1

private theorem exists_commonChart
    (hL : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (hM : (⨆ j, nonvanishingOpen X M (t j)) = ⊤) (x : X) :
    ∃ c : CommonChart L M s t, x ∈ c.affineOpen.1 := by
  have hxL : x ∈ ⨆ c : Chart L s, c.affineOpen.1 := by
    rw [LinearSystemMorphism.chartOpens_cover L s hL]
    trivial
  have hxM : x ∈ ⨆ c : Chart M t, c.affineOpen.1 := by
    rw [LinearSystemMorphism.chartOpens_cover M t hM]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hxL
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hxM
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open
      (show x ∈ c.affineOpen.1 ⊓ d.affineOpen.1 from ⟨hc, hd⟩)
      (c.affineOpen.1 ⊓ d.affineOpen.1).2
  exact ⟨⟨c, d, ⟨U, hU⟩, hUV.trans inf_le_left, hUV.trans inf_le_right⟩, hxU⟩

private def commonCover
    (hL : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (hM : (⨆ j, nonvanishingOpen X M (t j)) = ⊤) : X.OpenCover where
  J := CommonChart L M s t
  obj c := Spec Γ(X, c.affineOpen.1)
  map c := c.affineOpen.2.fromSpec
  f x := (exists_commonChart L M s t hL hM x).choose
  covers x := by
    rw [IsAffineOpen.range_fromSpec]
    exact (exists_commonChart L M s t hL hM x).choose_spec

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- Equality of the original maps can be checked on every common affine chart restriction. -/
theorem morphism_eq_of_chartMap_restrictions
    (hL : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (hM : (⨆ j, nonvanishingOpen X M (t j)) = ⊤)
    (hchart : ∀ (c : Chart L s) (d : Chart M t) {W : X.Opens}
      (hW : IsAffineOpen W) (hWc : W ≤ c.affineOpen.1) (hWd : W ≤ d.affineOpen.1),
      Spec.map (CommRingCat.ofHom (res X hWc)) ≫ chartMap f L s c =
        Spec.map (CommRingCat.ofHom (res X hWd)) ≫ chartMap f M t d) :
    morphism L s f hL = morphism M t f hM := by
  apply (commonCover L M s t hL hM).hom_ext
  intro a
  change a.affineOpen.2.fromSpec ≫ morphism L s f hL =
    a.affineOpen.2.fromSpec ≫ morphism M t f hM
  calc
    _ = (Spec.map (CommRingCat.ofHom (res X a.le_left)) ≫
        a.left.affineOpen.2.fromSpec) ≫ morphism L s f hL :=
      congrArg (fun g => g ≫ morphism L s f hL)
        (a.left.affineOpen.2.map_fromSpec a.affineOpen.2 (homOfLE a.le_left).op).symm
    _ = Spec.map (CommRingCat.ofHom (res X a.le_left)) ≫ chartMap f L s a.left := by
      rw [Category.assoc, chart_morphism]
    _ = Spec.map (CommRingCat.ofHom (res X a.le_right)) ≫ chartMap f M t a.right :=
      hchart a.left a.right a.affineOpen.2 a.le_left a.le_right
    _ = _ := by
      rw [← chart_morphism M t f hM a.right, ← Category.assoc]
      exact congrArg (fun g => g ≫ morphism M t f hM)
        (a.right.affineOpen.2.map_fromSpec a.affineOpen.2 (homOfLE a.le_right).op)

/-- Transporting the original covering sections through an actual line-sheaf
isomorphism preserves the original projective morphism over the same field. -/
theorem morphism_sectionsMap_iso (e : L.obj ≅ M.obj)
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) :
    morphism M (isoSections L M e s) f (isoSections_cover L M e s hcover) =
      morphism L s f hcover := by
  symm
  apply morphism_eq_of_chartMap_restrictions L M s (isoSections L M e s) f hcover
    (isoSections_cover L M e s hcover)
  intro c d W hW hWc hWd
  apply ProjectiveChart.tupleMorphism_compatible
  · exact (congrArg CommRingCat.Hom.hom
      (baseToAffineSectionsMap_restrict f c.affineOpen.2 hW hWc)).trans
        (congrArg CommRingCat.Hom.hom
          (baseToAffineSectionsMap_restrict f d.affineOpen.2 hW hWd)).symm
  · intro j
    rw [coordinates_restrict, coordinates_restrict, coordinates_restrict]
    exact coordinates_sectionsMap_iso_scale L M e s c.frame d.frame
      (hWc.trans c.inFrame) (hWd.trans d.inFrame) c.index d.index
      (hWc.trans c.nonvanishing) (hWd.trans d.nonvanishing) j

end KltDP.Geometry.LinearSystemNaturality
