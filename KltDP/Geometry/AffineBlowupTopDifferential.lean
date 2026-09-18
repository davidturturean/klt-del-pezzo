import KltDP.Geometry.AffineNativeTopDifferentialSheaf
import KltDP.Geometry.AffineBlowupExceptionalIdealRefinement
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSource
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The original affine blowup differential on its actual refined charts

The original blowdown induces the global exterior-square differential. An
actual open chart over the original affine base identifies its pullback with
the original affine intrinsic map. The whole-map square is the already proved
composition law, with the actual structure-map equalities derived here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup SchemeKaehlerSheaf AffineNativeTopDifferential

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)

/-- The original structure morphism of the actual affine blowup. -/
def structureMap : scheme I ⟶ Spec (CommRingCat.of k) :=
  toSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))

abbrev topSheaf : (scheme I).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (structureMap k R I)) 2

/-- The actual global exterior differential of the original blowdown. -/
def blowdownMap : (schemeModulePullback (toSpec I)).obj (intrinsic k R 2) ⟶ topSheaf k R I :=
  SchemeKaehlerExteriorPullbackTransport.map
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) (toSpec I) (structureMap k R I) rfl 2

variable {B : Type u} [CommRing B] [Algebra k B] (ψ : R →ₐ[k] B)
variable (j : Spec (CommRingCat.of B) ⟶ scheme I)
variable (h : j ≫ toSpec I = Spec.map (CommRingCat.ofHom ψ.toRingHom))

include h in
theorem chart_structure :
    j ≫ structureMap k R I = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  rw [structureMap, ← Category.assoc, h]
  exact AffineNativeTopDifferential.spec_comp k ψ

/-- The actual differential from the original global top sheaf to the chart top sheaf. -/
def chartGlobalMap (ψ : R →ₐ[k] B) (j : Spec (CommRingCat.of B) ⟶ scheme I)
    (h : j ≫ toSpec I = Spec.map (CommRingCat.ofHom ψ.toRingHom)) :
    (schemeModulePullback j).obj (topSheaf k R I) ⟶ intrinsic k B 2 :=
  SchemeKaehlerExteriorPullbackTransport.map (structureMap k R I) j
    (Spec.map (CommRingCat.ofHom (algebraMap k B))) (chart_structure k R I ψ j h) 2

/-- The original pullback-composition comparison identifies the two actual sources. -/
def chartSourceIso :
    (schemeModulePullback j).obj ((schemeModulePullback (toSpec I)).obj (intrinsic k R 2)) ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj (intrinsic k R 2) :=
  SchemeKaehlerExteriorPullbackTransport.sourceIso
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) (toSpec I) j
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) h 2

private def chart_square_proof :=
  SchemeKaehlerExteriorPullbackTransport.map_comp_sourceIso
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) (toSpec I) j (structureMap k R I) rfl
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) h
    (Spec.map (CommRingCat.ofHom (algebraMap k B))) (chart_structure k R I ψ j h)
    (AffineNativeTopDifferential.spec_comp k ψ) 2

/-- The whole global differential restricts to the whole original affine intrinsic map. -/
theorem chart_square :
    (schemeModulePullback j).map (blowdownMap k R I) ≫ chartGlobalMap k R I ψ j h =
      (chartSourceIso k R I ψ j h).hom ≫ intrinsicMap k ψ 2 :=
  chart_square_proof k R I ψ j h

variable [IsOpenImmersion j]

/-- Open immersion makes this same original chart differential invertible. -/
def chartGlobalIso : (schemeModulePullback j).obj (topSheaf k R I) ≅ intrinsic k B 2 := by
  letI : IsIso (chartGlobalMap k R I ψ j h) :=
    SchemeKaehlerExteriorPullbackTransport.map_isIso (structureMap k R I) j
      (Spec.map (CommRingCat.ofHom (algebraMap k B))) (chart_structure k R I ψ j h) 2
  exact asIso (chartGlobalMap k R I ψ j h)

theorem chartGlobalIso_hom : (chartGlobalIso k R I ψ j h).hom = chartGlobalMap k R I ψ j h := rfl

end KltDP.Geometry.AffineBlowupTopDifferential
