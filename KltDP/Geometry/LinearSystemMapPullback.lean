import KltDP.Geometry.LinearSystemPullbackCoordinates
import KltDP.Geometry.LinearSystemMorphism

/-!
# Naturality of the actual linear-system morphism under scheme pullback

Common affine source subopens refine the original source chart system and
the inverse images of the original target charts. The actual appLE square
and the proved pulled-coordinate scaling identify their unchanged tuple
maps. Scheme-cover extensionality then gives the original global identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing InvertibleSectionNonvanishingOpen LinearSystemMorphism

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

private structure PullbackCommonChart where
  source : Chart (pullbackInvertibleSheaf h L) (pullbackSections h L s)
  target : Chart L s
  affineOpen : Y.affineOpens
  le_source : affineOpen.1 ≤ source.affineOpen.1
  le_target : affineOpen.1 ≤ h ⁻¹ᵁ target.affineOpen.1

private theorem exists_pullbackCommonChart
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) (y : Y) :
    ∃ a : PullbackCommonChart h L s, y ∈ a.affineOpen.1 := by
  have hy : y ∈ ⨆ c : Chart (pullbackInvertibleSheaf h L) (pullbackSections h L s),
      c.affineOpen.1 := by
    rw [LinearSystemMorphism.chartOpens_cover (pullbackInvertibleSheaf h L)
      (pullbackSections h L s) (pullbackSections_cover h L s hcover)]
    trivial
  have hx : h.base y ∈ ⨆ d : Chart L s, d.affineOpen.1 := by
    rw [LinearSystemMorphism.chartOpens_cover L s hcover]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hy
  obtain ⟨d, hd⟩ := Opens.mem_iSup.mp hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    (isBasis_affine_open Y).exists_subset_of_mem_open
      (show y ∈ c.affineOpen.1 ⊓ h ⁻¹ᵁ d.affineOpen.1 from ⟨hc, hd⟩)
      (c.affineOpen.1 ⊓ h ⁻¹ᵁ d.affineOpen.1).2
  exact ⟨⟨c, d, ⟨W, hW⟩, hWV.trans inf_le_left, hWV.trans inf_le_right⟩, hyW⟩

private def pullbackCommonCover
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) : Y.OpenCover where
  J := PullbackCommonChart h L s
  obj a := Spec Γ(Y, a.affineOpen.1)
  map a := a.affineOpen.2.fromSpec
  f y := (exists_pullbackCommonChart h L s hcover y).choose
  covers y := by
    rw [IsAffineOpen.range_fromSpec]
    exact (exists_pullbackCommonChart h L s hcover y).choose_spec

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

private theorem baseToAffineSectionsMap_appLE {U : X.Opens} {W : Y.Opens}
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ h ⁻¹ᵁ U) :
    baseToAffineSectionsMap f hU ≫ h.appLE U W hWU =
      baseToAffineSectionsMap (h ≫ f) hW := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_baseToAffineSectionsMap, Spec_map_baseToAffineSectionsMap,
    ← Category.assoc, IsAffineOpen.Spec_map_appLE_fromSpec, Category.assoc]

/-- The original affine tuple maps agree on every common source subopen. -/
theorem chartMap_pullback_compatible
    (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)
    (c : Chart (pullbackInvertibleSheaf h L) (pullbackSections h L s)) (d : Chart L s)
    {W : Y.Opens} (hW : IsAffineOpen W) (hWc : W ≤ c.affineOpen.1)
    (hWd : W ≤ h ⁻¹ᵁ d.affineOpen.1) :
    Spec.map (CommRingCat.ofHom (res Y hWc)) ≫
      chartMap (h ≫ f) (pullbackInvertibleSheaf h L) (pullbackSections h L s) c =
    Spec.map (h.appLE d.affineOpen.1 W hWd) ≫ chartMap f L s d := by
  apply ProjectiveChart.tupleMorphism_compatible
  · exact (congrArg CommRingCat.Hom.hom
      (baseToAffineSectionsMap_restrict (h ≫ f) c.affineOpen.2 hW hWc)).trans
        (congrArg CommRingCat.Hom.hom
          (baseToAffineSectionsMap_appLE h f d.affineOpen.2 hW hWd)).symm
  · intro j
    exact coordinates_pullback_scale h L s hcover c d hWc hWd j

/-- The actual morphism of the original pulled sections is the original composite map. -/
theorem morphism_pullback (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤) :
    morphism (pullbackInvertibleSheaf h L) (pullbackSections h L s) (h ≫ f)
      (pullbackSections_cover h L s hcover) = h ≫ morphism L s f hcover := by
  apply (pullbackCommonCover h L s hcover).hom_ext
  intro a
  change a.affineOpen.2.fromSpec ≫
      morphism (pullbackInvertibleSheaf h L) (pullbackSections h L s) (h ≫ f)
        (pullbackSections_cover h L s hcover) =
    a.affineOpen.2.fromSpec ≫ (h ≫ morphism L s f hcover)
  calc
    _ = (Spec.map (CommRingCat.ofHom (res Y a.le_source)) ≫
        a.source.affineOpen.2.fromSpec) ≫
          morphism (pullbackInvertibleSheaf h L) (pullbackSections h L s) (h ≫ f)
            (pullbackSections_cover h L s hcover) :=
      congrArg (fun g => g ≫ morphism (pullbackInvertibleSheaf h L)
        (pullbackSections h L s) (h ≫ f) (pullbackSections_cover h L s hcover))
          (a.source.affineOpen.2.map_fromSpec a.affineOpen.2 (homOfLE a.le_source).op).symm
    _ = Spec.map (CommRingCat.ofHom (res Y a.le_source)) ≫
        chartMap (h ≫ f) (pullbackInvertibleSheaf h L) (pullbackSections h L s) a.source := by
      rw [Category.assoc, chart_morphism]
    _ = Spec.map (h.appLE a.target.affineOpen.1 a.affineOpen.1 a.le_target) ≫
        chartMap f L s a.target :=
      chartMap_pullback_compatible h L s f hcover a.source a.target
        a.affineOpen.2 a.le_source a.le_target
    _ = _ := by
      rw [← chart_morphism L s f hcover a.target, ← Category.assoc,
        IsAffineOpen.Spec_map_appLE_fromSpec, Category.assoc]

end KltDP.Geometry.LinearSystemNaturality
