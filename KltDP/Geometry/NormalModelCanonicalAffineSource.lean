import KltDP.Geometry.NormalModelCanonicalOpenFrame
import KltDP.Geometry.SmoothSurfaceKaehlerAtlas

/-!
# An actual affine source chart of the existing normalized frame

The original smooth relative-dimension-two atlas supplies the affine ring
and its genuine Kähler basis. Its original spectrum map and primeIdealOf
point feed the already proved normalized Cartier-frame constructor. Both
the source order and the exact original ground-field structure are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

attribute [local instance] integralSchemeStalk_isDomain

open CartierRationalCoordinate DominantCartierPullback

local instance affineSourceReferenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance affineSourceOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The original smooth atlas supplies the literal Spec source and native
basis, while the actual canonical-frame pullback preserves normalization. -/
theorem exists_affine_source_chart
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F) :
    ∃ (T : F.neighborhood.Opens) (hT : IsAffineOpen T) (hpoint : F.point ∈ T),
      let sF := F.toModel ≫ (v ≫ X.structureMorphism)
      letI := affineSectionsAlgebra sF hT
      ∃ b : Basis (Fin 2) Γ(F.neighborhood, T) (KaehlerDifferential k Γ(F.neighborhood, T)),
      let j := hT.fromSpec
      let y := hT.primeIdealOf ⟨F.point, hpoint⟩
      let hy : j.base y = F.point := hT.fromSpec_primeIdealOf ⟨F.point, hpoint⟩
      letI : Nonempty (Spec Γ(F.neighborhood, T)) := ⟨y⟩
      letI : IsIntegral (Spec Γ(F.neighborhood, T)) := isIntegral_of_isOpenImmersion j
      let sB := (j ≫ F.toModel) ≫ (v ≫ X.structureMorphism)
      let hp : (j ≫ F.toModel).base y = x := by
        rw [Scheme.comp_base_apply, hy, F.point_eq]
      letI : IsSmoothOfRelativeDimension 2 sB := by
        change IsSmoothOfRelativeDimension 2 ((j ≫ F.toModel) ≫ (v ≫ X.structureMorphism))
        rw [Category.assoc]
        exact IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2) F.smooth j
      let G := ofCanonicalDivisor (v ≫ X.structureMorphism) (j ≫ F.toModel) y x hp
        (pullbackHom j F.divisor)
        (canonicalOpenPullbackIso j sF sB
          (Category.assoc j F.toModel (v ≫ X.structureMorphism)).symm F.divisor F.canonicalIso)
      sB = Spec.map (CommRingCat.ofHom (algebraMap k Γ(F.neighborhood, T))) ∧
        IsNormalized X U KU eKU v x G ∧ G.order = F.order := by
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  letI : IsSmoothOfRelativeDimension 2 sF := F.smooth
  let T := SmoothSurfaceKaehlerAtlas.atlasOpen sF F.point
  let hT : IsAffineOpen T := SmoothSurfaceKaehlerAtlas.atlasOpen_isAffineOpen sF F.point
  have hpoint : F.point ∈ T := SmoothSurfaceKaehlerAtlas.atlasOpen_mem sF F.point
  letI := affineSectionsAlgebra sF hT
  let b := SmoothSurfaceKaehlerAtlas.atlasFrame sF F.point
  refine ⟨T, hT, hpoint, b, ?_⟩
  let j := hT.fromSpec
  let y := hT.primeIdealOf ⟨F.point, hpoint⟩
  have hy : j.base y = F.point := hT.fromSpec_primeIdealOf ⟨F.point, hpoint⟩
  letI : Nonempty (Spec Γ(F.neighborhood, T)) := ⟨y⟩
  letI : IsIntegral (Spec Γ(F.neighborhood, T)) := isIntegral_of_isOpenImmersion j
  refine ⟨?_, ofCanonicalDivisor_open_normalized X U KU eKU v x F hF j y hy⟩
  change (j ≫ F.toModel) ≫ (v ≫ X.structureMorphism) = _
  rw [Category.assoc]
  exact (Spec_map_baseToAffineSectionsMap sF hT).symm

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.exists_affine_source_chart
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.exists_affine_source_chart
