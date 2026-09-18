import KltDP.Geometry.NormalModelCanonicalFrame
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportComp

/-!
# The original differential in a normalized canonical coordinate

The existing normalization witness is a nonempty common open. The actual
exterior composition law turns that witness into a square for the original
differential on the whole frame neighborhood, restricted to that same open.
No scalar or differential-compatibility premise is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalizedFrameDifferentialSquare

open NormalModelCanonical CartierRationalCoordinate OpenImmersionRational

attribute [local irreducible] canonicalOpenPullbackIso

local instance targetOpenIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance openGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : B ⟶ A) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- An actual normalized frame determines the rational coordinate of the
original differential on a nonempty open. The factor `p` is the original
map to the target reference open, and its composite with this smaller
open immersion is proved to be an open immersion from normalization. -/
theorem exists_original_differential_coordinate_square
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (p : F.neighborhood ⟶ U.toScheme)
    (hp : p ≫ U.ι = F.toModel ≫ v) :
    let sU := U.ι ≫ X.structureMorphism
    let sF := F.toModel ≫ (v ≫ X.structureMorphism)
    let hpbase : p ≫ sU = sF := by
      simpa only [Category.assoc] using congrArg (fun a => a ≫ X.structureMorphism) hp
    ∃ (Z : F.neighborhood.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ p),
        letI : IsOpenImmersion (Z.ι ≫ p) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sU p sF hpbase 2 ≫
              coordinate F.neighborhood F.divisor
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sF 2)
                F.canonicalIso) ≫ (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι p).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sU 2) ≫
            (schemeModulePullback (Z.ι ≫ p)).map
              (coordinate U.toScheme KU
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sU 2) eKU) ≫
              (rationalModulePullbackIso (Z.ι ≫ p)).hom := by
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  dsimp only
  obtain ⟨Z, hne, j, hj, htriangle, hcoordinate⟩ := hF
  letI := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := hj
  have hjp : j = Z.ι ≫ p := by
    apply (cancel_mono U.ι).mp
    exact htriangle.trans (by simp only [Category.assoc, hp])
  subst j
  refine ⟨Z, hne, inferInstance, ?_⟩
  let sU := U.ι ≫ X.structureMorphism
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sZ := Z.ι ≫ sF
  have hpbase : p ≫ sU = sF := by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ X.structureMorphism) hp
  have htbase : (Z.ι ≫ p) ≫ sU = sZ := by rw [Category.assoc, hpbase]
  let cZ := coordinate Z.toScheme
    (DominantCartierPullback.pullbackHom Z.ι F.divisor)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso Z.ι sF sZ rfl F.divisor F.canonicalIso)
  have hl := map_comp_coordinate_canonicalOpenPullbackIso Z.ι sF sZ rfl
    F.divisor F.canonicalIso
  have ht := map_comp_coordinate_canonicalOpenPullbackIso (Z.ι ≫ p) sU sZ
    htbase KU eKU
  have hc := SchemeKaehlerExteriorPullbackTransport.map_comp sU p Z.ι sF hpbase
    (Z.ι ≫ p) rfl sZ rfl htbase 2
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp] at hc
  change cZ = _ at hcoordinate
  rw [← hcoordinate] at ht
  rw [Functor.map_comp, Category.assoc, ← hl, ← Category.assoc, hc,
    Category.assoc, ht]

end KltDP.Geometry.NormalizedFrameDifferentialSquare

#check @KltDP.Geometry.NormalizedFrameDifferentialSquare.exists_original_differential_coordinate_square
#print axioms KltDP.Geometry.NormalizedFrameDifferentialSquare.exists_original_differential_coordinate_square
