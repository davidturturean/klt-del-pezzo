import KltDP.Geometry.NormalizedFrameDifferentialSquare
import KltDP.Geometry.CanonicalCoordinateOpenComposition

/-!
# A normalized canonical frame over an actual target-reference open map

The original normalization witness is transported through the actual open
map into the target reference. Its map is forced by the original triangle,
and its normalized coordinate follows from the proved composition law.
The resulting square uses the original differential on the original chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalizedFrameTargetOpenSquare

open NormalModelCanonical CartierRationalCoordinate OpenImmersionRational

attribute [local irreducible] canonicalOpenPullbackIso

local instance targetOpenIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance openGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- The original normalization gives the actual differential-coordinate
square on an arbitrary original open chart of the target reference. The
chart divisor and its canonical isomorphism are the literal normalized
pullbacks of the original reference; neither is independently supplied. -/
theorem exists_original_differential_coordinate_square
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {A : Scheme.{u}} [IsIntegral A] (i : A ⟶ U.toScheme) [IsOpenImmersion i]
    (sA : A ⟶ Spec (CommRingCat.of k))
    (hi : i ≫ (U.ι ≫ X.structureMorphism) = sA)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F)
    (q : F.neighborhood ⟶ A)
    (hq : (q ≫ i) ≫ U.ι = F.toModel ≫ v) :
    let sF := F.toModel ≫ (v ≫ X.structureMorphism)
    let hqbase : q ≫ sA = sF := by
      rw [← hi]
      simpa only [Category.assoc] using
        congrArg (fun a => a ≫ X.structureMorphism) hq
    let DA := DominantCartierPullback.pullbackHom i KU
    let eDA := canonicalOpenPullbackIso i (U.ι ≫ X.structureMorphism) sA hi KU eKU
    ∃ (Z : F.neighborhood.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ q),
        letI : IsOpenImmersion (Z.ι ≫ q) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sA q sF hqbase 2 ≫
              coordinate F.neighborhood F.divisor
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sF 2)
                F.canonicalIso) ≫ (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι q).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫
            (schemeModulePullback (Z.ι ≫ q)).map
              (coordinate A DA
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eDA) ≫
              (rationalModulePullbackIso (Z.ι ≫ q)).hom := by
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  dsimp only
  obtain ⟨Z, hne, j, hj, htriangle, hcoordinate⟩ := hF
  letI := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := hj
  have hjq : j = (Z.ι ≫ q) ≫ i := by
    apply (cancel_mono U.ι).mp
    calc
      j ≫ U.ι = (Z.ι ≫ F.toModel) ≫ v := htriangle
      _ = Z.ι ≫ (F.toModel ≫ v) := Category.assoc _ _ _
      _ = Z.ι ≫ ((q ≫ i) ≫ U.ι) := congrArg (fun a => Z.ι ≫ a) hq.symm
      _ = ((Z.ι ≫ q) ≫ i) ≫ U.ι := by simp only [Category.assoc]
  subst j
  letI : IsOpenImmersion (Z.ι ≫ q) := IsOpenImmersion.of_comp (Z.ι ≫ q) i
  refine ⟨Z, hne, inferInstance, ?_⟩
  let sU := U.ι ≫ X.structureMorphism
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sZ := Z.ι ≫ sF
  have hqbase : q ≫ sA = sF := by
    rw [← hi]
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ X.structureMorphism) hq
  have htbase : (Z.ι ≫ q) ≫ sA = sZ := by rw [Category.assoc, hqbase]
  let DA := DominantCartierPullback.pullbackHom i KU
  let eDA := canonicalOpenPullbackIso i sU sA hi KU eKU
  let cZ := coordinate Z.toScheme
    (DominantCartierPullback.pullbackHom Z.ι F.divisor)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso Z.ι sF sZ rfl F.divisor F.canonicalIso)
  have hcomposition := coordinate_canonicalOpenPullbackIso_comp
    (Z.ι ≫ q) i sU sA sZ hi htbase KU eKU
  have hcoordinateA : cZ = coordinate Z.toScheme
      (DominantCartierPullback.pullbackHom (Z.ι ≫ q) DA)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
      (canonicalOpenPullbackIso (Z.ι ≫ q) sA sZ htbase DA eDA) := by
    change cZ = _ at hcoordinate
    exact hcoordinate.trans hcomposition.symm
  have hl := map_comp_coordinate_canonicalOpenPullbackIso Z.ι sF sZ rfl
    F.divisor F.canonicalIso
  have ht := map_comp_coordinate_canonicalOpenPullbackIso (Z.ι ≫ q) sA sZ
    htbase DA eDA
  have hc := SchemeKaehlerExteriorPullbackTransport.map_comp sA q Z.ι sF hqbase
    (Z.ι ≫ q) rfl sZ rfl htbase 2
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp] at hc
  rw [← hcoordinateA] at ht
  rw [Functor.map_comp, Category.assoc, ← hl, ← Category.assoc, hc,
    Category.assoc, ht]

end KltDP.Geometry.NormalizedFrameTargetOpenSquare

#check @KltDP.Geometry.NormalizedFrameTargetOpenSquare.exists_original_differential_coordinate_square
#print axioms KltDP.Geometry.NormalizedFrameTargetOpenSquare.exists_original_differential_coordinate_square
