import KltDP.Geometry.LinearSystemAffineCharts
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The actual projective morphism of a finite covering tuple of sections

The actual normalized affine chart maps glue along their original maps to
the scheme. Common affine subopens cover each actual pullback overlap,
including when an intersection is not affine. The existing scheme gluing
construction yields the morphism and its original field-structure identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (L : InvertibleSheaf X) {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

private abbrev OverlapChart (c d : Chart L s) :=
  {W : X.affineOpens // W.1 ≤ c.affineOpen.1 ∧ W.1 ≤ d.affineOpen.1}

private def overlapMap (c d : Chart L s) (W : OverlapChart L s c d) :
    Spec Γ(X, W.1.1) ⟶ pullback c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec :=
  pullback.lift (Spec.map (CommRingCat.ofHom (res X W.2.1)))
    (Spec.map (CommRingCat.ofHom (res X W.2.2)))
    ((c.affineOpen.2.map_fromSpec W.1.2 (homOfLE W.2.1).op).trans
      (d.affineOpen.2.map_fromSpec W.1.2 (homOfLE W.2.2).op).symm)

private theorem overlapMap_fst (c d : Chart L s) (W : OverlapChart L s c d) :
    overlapMap L s c d W ≫ pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec =
      Spec.map (CommRingCat.ofHom (res X W.2.1)) :=
  pullback.lift_fst _ _ _

private theorem overlapMap_snd (c d : Chart L s) (W : OverlapChart L s c d) :
    overlapMap L s c d W ≫ pullback.snd c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec =
      Spec.map (CommRingCat.ofHom (res X W.2.2)) :=
  pullback.lift_snd _ _ _

private theorem overlapMap_toX (c d : Chart L s) (W : OverlapChart L s c d) :
    overlapMap L s c d W ≫
        (pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫
          c.affineOpen.2.fromSpec) = W.1.2.fromSpec := by
  rw [← Category.assoc, overlapMap_fst]
  exact c.affineOpen.2.map_fromSpec W.1.2 (homOfLE W.2.1).op

private instance overlapMap_isOpenImmersion (c d : Chart L s) (W : OverlapChart L s c d) :
    IsOpenImmersion (overlapMap L s c d W) := by
  haveI : IsOpenImmersion (overlapMap L s c d W ≫
      (pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫
        c.affineOpen.2.fromSpec)) := by
    rw [overlapMap_toX]
    infer_instance
  exact IsOpenImmersion.of_comp (overlapMap L s c d W)
    (pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫ c.affineOpen.2.fromSpec)

private theorem exists_overlapChart (c d : Chart L s)
    (x : (pullback c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec : Scheme)) :
    ∃ W : OverlapChart L s c d, x ∈ Set.range (overlapMap L s c d W).base := by
  let g := pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫
    c.affineOpen.2.fromSpec
  have hg : g = pullback.snd c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫
      d.affineOpen.2.fromSpec := pullback.condition
  have hx : g.base x ∈ c.affineOpen.1 ⊓ d.affineOpen.1 := by
    constructor
    · rw [← c.affineOpen.2.range_fromSpec]
      exact ⟨(pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec).base x, rfl⟩
    · rw [hg, ← d.affineOpen.2.range_fromSpec]
      exact ⟨(pullback.snd c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec).base x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hx
      (c.affineOpen.1 ⊓ d.affineOpen.1).2
  let W : OverlapChart L s c d :=
    ⟨⟨U, hU⟩, hUV.trans inf_le_left, hUV.trans inf_le_right⟩
  have hxrange : g.base x ∈ Set.range hU.fromSpec.base := by
    rwa [hU.range_fromSpec]
  obtain ⟨z, hz⟩ := hxrange
  refine ⟨W, z, ?_⟩
  apply g.isOpenEmbedding.injective
  change (overlapMap L s c d W ≫ g).base z = g.base x
  rw [overlapMap_toX]
  exact hz

private def overlapCover (c d : Chart L s) :
    Scheme.OpenCover.{u} (pullback c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec) where
  J := OverlapChart L s c d
  obj W := Spec Γ(X, W.1.1)
  map W := overlapMap L s c d W
  f x := (exists_overlapChart L s c d x).choose
  covers x := (exists_overlapChart L s c d x).choose_spec

variable (f : X ⟶ Spec (CommRingCat.of k))

/-- The original affine chart maps agree on the actual scheme-theoretic pullback overlap. -/
theorem chartMap_pullback_compatible (c d : Chart L s) :
    pullback.fst c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫ chartMap f L s c =
      pullback.snd c.affineOpen.2.fromSpec d.affineOpen.2.fromSpec ≫ chartMap f L s d := by
  apply (overlapCover L s c d).hom_ext
  intro W
  change overlapMap L s c d W ≫ (_ ≫ chartMap f L s c) =
    overlapMap L s c d W ≫ (_ ≫ chartMap f L s d)
  rw [← Category.assoc, ← Category.assoc, overlapMap_fst, overlapMap_snd]
  exact chartMap_compatible f L s c d W.1.2 W.2.1 W.2.2

variable (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

include hcover in
private theorem exists_chart (x : X) :
    ∃ c : Chart L s, x ∈ Set.range c.affineOpen.2.fromSpec.base := by
  have hx : x ∈ ⨆ c : Chart L s, c.affineOpen.1 := by
    rw [chartOpens_cover L s hcover]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hx
  exact ⟨c, by rwa [c.affineOpen.2.range_fromSpec]⟩

/-- The original normalized affine charts form an actual open cover. -/
def chartCover : X.OpenCover where
  J := Chart L s
  obj c := Spec Γ(X, c.affineOpen.1)
  map c := c.affineOpen.2.fromSpec
  f x := (exists_chart L s hcover x).choose
  covers x := (exists_chart L s hcover x).choose_spec

/-- The actual projective morphism defined by the specified finite covering tuple. -/
def morphism : X ⟶ projectiveSpace k n :=
  (chartCover L s hcover).glueMorphisms (chartMap f L s)
    (chartMap_pullback_compatible L s f)

/-- Its restriction to each original affine chart is the original normalized tuple map. -/
theorem chart_morphism (c : Chart L s) :
    c.affineOpen.2.fromSpec ≫ morphism L s f hcover = chartMap f L s c :=
  (chartCover L s hcover).ι_glueMorphisms _ _ c

/-- The glued map is over the original field with its original structure morphism. -/
theorem morphism_structure :
    morphism L s f hcover ≫ projectiveSpaceToSpec k n = f := by
  apply (chartCover L s hcover).hom_ext
  intro c
  change c.affineOpen.2.fromSpec ≫ (morphism L s f hcover ≫ projectiveSpaceToSpec k n) = _
  rw [← Category.assoc, chart_morphism, chartMap_structure]
  rfl

end KltDP.Geometry.LinearSystemMorphism
