import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback
import KltDP.Geometry.RationalOpenPullbackComposition
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportComp

/-!
# Original normalized canonical coordinates under successive open pullbacks

The original exterior differentials compose through the original pullback
comparison. The same is true of the original rational-module comparison.
Cancelling these actual isomorphisms identifies the normalized coordinates
without identifying any independently chosen canonical sheaf isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

open OpenImmersionRational DominantCartierPullback

attribute [local irreducible] canonicalOpenPullbackIso

local instance compositionOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- Two successive original normalized open pullbacks have the same rational
coordinate as the normalized pullback through their original composite. -/
theorem coordinate_canonicalOpenPullbackIso_comp
    {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (sX : X ⟶ Spec (CommRingCat.of k))
    (sY : Y ⟶ Spec (CommRingCat.of k)) (sZ : Z ⟶ Spec (CommRingCat.of k))
    (hg : g ≫ sX = sY) (hf : f ≫ sY = sZ)
    (D : CartierDivisor X)
    (e : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2) :
    let hfg : (f ≫ g) ≫ sX = sZ := by rw [Category.assoc, hg, hf]
    coordinate Z (pullbackHom f (pullbackHom g D))
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
        (canonicalOpenPullbackIso f sY sZ hf (pullbackHom g D)
          (canonicalOpenPullbackIso g sX sY hg D e)) =
      coordinate Z (pullbackHom (f ≫ g) D)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
        (canonicalOpenPullbackIso (f ≫ g) sX sZ hfg D e) := by
  let hfg : (f ≫ g) ≫ sX = sZ := by rw [Category.assoc, hg, hf]
  let M := SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2
  let cX := coordinate X D M e
  let eY := canonicalOpenPullbackIso g sX sY hg D e
  let cY := coordinate Y (pullbackHom g D)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2) eY
  let c₂ := coordinate Z (pullbackHom f (pullbackHom g D))
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso f sY sZ hf (pullbackHom g D) eY)
  let c₁ := coordinate Z (pullbackHom (f ≫ g) D)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso (f ≫ g) sX sZ hfg D e)
  let dg := SchemeKaehlerExteriorPullbackTransport.map sX g sY hg 2
  let df := SchemeKaehlerExteriorPullbackTransport.map sY f sZ hf 2
  let dfg := SchemeKaehlerExteriorPullbackTransport.map sX (f ≫ g) sZ hfg 2
  let a := (schemeModulePullbackCompIso f g).hom.app M
  have hd : (schemeModulePullback f).map dg ≫ df = a ≫ dfg := by
    simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp] using
      SchemeKaehlerExteriorPullbackTransport.map_comp sX g f sY hg
        (f ≫ g) rfl sZ hf hfg 2
  have hY : dg ≫ cY =
      (schemeModulePullback g).map cX ≫ (rationalModulePullbackIso g).hom :=
    map_comp_coordinate_canonicalOpenPullbackIso g sX sY hg D e
  have h₂ : df ≫ c₂ =
      (schemeModulePullback f).map cY ≫ (rationalModulePullbackIso f).hom :=
    map_comp_coordinate_canonicalOpenPullbackIso f sY sZ hf (pullbackHom g D) eY
  have h₁ : dfg ≫ c₁ =
      (schemeModulePullback (f ≫ g)).map cX ≫
        (rationalModulePullbackIso (f ≫ g)).hom :=
    map_comp_coordinate_canonicalOpenPullbackIso (f ≫ g) sX sZ hfg D e
  letI : IsIso dfg := SchemeKaehlerExteriorPullbackTransport.map_isIso
    sX (f ≫ g) sZ hfg 2
  change c₂ = c₁
  apply (cancel_epi (a ≫ dfg)).mp
  calc
    (a ≫ dfg) ≫ c₂ = ((schemeModulePullback f).map dg ≫ df) ≫ c₂ :=
      congrArg (fun b => b ≫ c₂) hd.symm
    _ = (schemeModulePullback f).map dg ≫
        ((schemeModulePullback f).map cY ≫ (rationalModulePullbackIso f).hom) := by
      rw [Category.assoc, h₂]
    _ = (schemeModulePullback f).map (dg ≫ cY) ≫
        (rationalModulePullbackIso f).hom := by rw [Functor.map_comp, Category.assoc]
    _ = (schemeModulePullback f).map
        ((schemeModulePullback g).map cX ≫ (rationalModulePullbackIso g).hom) ≫
        (rationalModulePullbackIso f).hom := by rw [hY]
    _ = (schemeModulePullback f).map ((schemeModulePullback g).map cX) ≫
        ((schemeModulePullback f).map (rationalModulePullbackIso g).hom ≫
          (rationalModulePullbackIso f).hom) := by rw [Functor.map_comp, Category.assoc]
    _ = (schemeModulePullback f).map ((schemeModulePullback g).map cX) ≫
        ((schemeModulePullbackCompIso f g).hom.app (rationalFunctionModule X) ≫
          (rationalModulePullbackIso (f ≫ g)).hom) := by
      rw [rationalModulePullbackIso_comp f g]
    _ = a ≫ ((schemeModulePullback (f ≫ g)).map cX ≫
        (rationalModulePullbackIso (f ≫ g)).hom) := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun b => b ≫ (rationalModulePullbackIso (f ≫ g)).hom)
          ((schemeModulePullbackCompIso f g).hom.naturality cX)
    _ = a ≫ (dfg ≫ c₁) := congrArg (fun b => a ≫ b) h₁.symm
    _ = (a ≫ dfg) ≫ c₁ := (Category.assoc a dfg c₁).symm

/-- Equality of the original open maps gives equality of their normalized
rational coordinates; no comparison of independently chosen forms is used. -/
theorem coordinate_canonicalOpenPullbackIso_congr
    {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g)
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ sX = sY) (hg : g ≫ sX = sY)
    (D : CartierDivisor X)
    (e : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2) :
    coordinate Y (pullbackHom f D)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2)
        (canonicalOpenPullbackIso f sX sY hf D e) =
      coordinate Y (pullbackHom g D)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2)
        (canonicalOpenPullbackIso g sX sY hg D e) := by
  cases h
  rfl

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_canonicalOpenPullbackIso_comp
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_canonicalOpenPullbackIso_comp
#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_canonicalOpenPullbackIso_congr
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_canonicalOpenPullbackIso_congr
