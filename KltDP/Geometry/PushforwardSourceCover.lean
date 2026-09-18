import KltDP.Compatibility.AffineZariskiDirectedCover

/-!
# The original inverse-image cover of an arbitrary scheme morphism

The original affine Zariski site of the target indexes the actual inverse
image opens of the source. Common original affine basic subopens provide
directedness, using the same pointwise overlap argument as the compiled
`AffineZariskiSite.directedCover`. The cover, transitions and colimit all
retain the original source scheme. No geometric property of the morphism
is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PushforwardAffinizationCharts

open Scheme.AffineZariskiSite

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original inverse-image inclusion attached to an original affine-site arrow. -/
theorem preimageLE {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    f ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ V.1 :=
  fun _ hx => toOpens_mono i.le hx

/-- The actual source opens lying over all original affine opens of the target. -/
def sourceCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers Y.AffineZariskiSite
    (fun U => (f ⁻¹ᵁ U.1).toScheme) (fun U => (f ⁻¹ᵁ U.1).ι)
    (fun x => by
      have hx : f.base x ∈ ⨆ U : Y.affineOpens, U.1 := by
        rw [iSup_affineOpens_eq_top]
        trivial
      obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
      exact ⟨⟨U.1, U.2⟩, ⟨x, hxU⟩, rfl⟩)

instance : Preorder (sourceCover f).J :=
  inferInstanceAs (Preorder Y.AffineZariskiSite)

instance : SmallCategory (sourceCover f).J :=
  inferInstanceAs (SmallCategory Y.AffineZariskiSite)

/-- Actual original affine basic subopens cover every original source overlap. -/
instance : Scheme.Cover.LocallyDirected (sourceCover f) where
  trans {U V} i := X.homOfLE (preimageLE f i)
  trans_id U := Scheme.homOfLE_rfl X (f ⁻¹ᵁ U.1)
  trans_comp i j := (Scheme.homOfLE_homOfLE X _ _).symm
  w i := Scheme.homOfLE_ι X _
  directed {U V} x := by
    let a : X :=
      (pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U.1).ι).base x
    have haU : f.base a ∈ U.1 :=
      ((pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι).base x).2
    have haV : f.base a ∈ V.1 := by
      change f.base ((pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫
        (f ⁻¹ᵁ U.1).ι).base x) ∈ V.1
      rw [pullback.condition]
      exact ((pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι).base x).2
    obtain ⟨r, s, e, har⟩ :=
      exists_basicOpen_le_affine_inter U.2 V.2 (f.base a) ⟨haU, haV⟩
    have hrs : U.basicOpen r = V.basicOpen s := Subtype.ext e
    let y : (f ⁻¹ᵁ (U.basicOpen r).1).toScheme := ⟨a, har⟩
    refine ⟨U.basicOpen r, homOfLE (U.basicOpen_le r),
      eqToHom hrs ≫ homOfLE (V.basicOpen_le s), y, ?_⟩
    apply (show IsOpenImmersion (pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫
      (f ⁻¹ᵁ U.1).ι) from inferInstance).base_open.injective
    change (pullback.lift (W := (f ⁻¹ᵁ (U.basicOpen r).1).toScheme)
      (X.homOfLE (preimageLE f (homOfLE (U.basicOpen_le r))))
      (X.homOfLE (preimageLE f
        (eqToHom hrs ≫ homOfLE (V.basicOpen_le s))))
      (by simp) ≫ pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫
        (f ⁻¹ᵁ U.1).ι).base y =
      (pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ (f ⁻¹ᵁ U.1).ι).base x
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl

/-- The source diagram consists of the actual inverse-image schemes and inclusions. -/
def sourceDiagram : Y.AffineZariskiSite ⥤ Scheme.{u} :=
  Scheme.Cover.functorOfLocallyDirected (sourceCover f)

/-- The actual source scheme and its original open inclusions form the source cocone. -/
def sourceCocone : Cocone (sourceDiagram f) :=
  Scheme.Cover.coconeOfLocallyDirected (sourceCover f)

/-- The original source scheme is the colimit of these actual inverse-image charts. -/
def sourceIsColimit : IsColimit (sourceCocone f) :=
  Scheme.Cover.isColimitCoconeOfLocallyDirected (sourceCover f)

end KltDP.Geometry.PushforwardAffinizationCharts
