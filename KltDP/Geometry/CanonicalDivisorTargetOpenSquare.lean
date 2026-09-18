import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.NormalModelLocalFrameConstructor

/-!
# The original normalized square for a supplied canonical Cartier divisor

The LocalFrame constructor is reduced with an abstract original source
scheme and abstract Cartier data. The result mentions the supplied scheme,
divisor and isomorphism directly, so later affine callers need not reduce
the constructor through their native differential and stalk instances.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalDivisorTargetOpenSquare

open NormalModelCanonical CartierRationalCoordinate OpenImmersionRational

attribute [local irreducible] canonicalOpenPullbackIso

local instance referenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance chartGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Normalization of the constructed original frame supplies the same
square on its supplied source scheme and Cartier identification. -/
theorem exists_original_square
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {A : Scheme.{u}} [IsIntegral A] (i : A ⟶ U.toScheme) [IsOpenImmersion i]
    (sA : A ⟶ Spec (CommRingCat.of k))
    (hi : i ≫ (U.ι ≫ X.structureMorphism) = sA)
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (v : V ⟶ X.toScheme) (x : V) (j : W ⟶ V) [IsOpenImmersion j]
    (w : W) (hw : j.base w = x)
    [IsSmoothOfRelativeDimension 2 (j ≫ (v ≫ X.structureMorphism))]
    (D : CartierDivisor W)
    (eD : cartierDivisorModule W D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (j ≫ (v ≫ X.structureMorphism)) 2)
    (hF : IsNormalized X U KU eKU v x
      (LocalFrame.ofCanonicalDivisor (v ≫ X.structureMorphism) j w x hw D eD))
    (q : W ⟶ A) (hq : (q ≫ i) ≫ U.ι = j ≫ v) :
    let sW := j ≫ (v ≫ X.structureMorphism)
    let hqbase : q ≫ sA = sW := by
      rw [← hi]
      simpa only [Category.assoc] using
        congrArg (fun a => a ≫ X.structureMorphism) hq
    let DA := DominantCartierPullback.pullbackHom i KU
    let eDA := canonicalOpenPullbackIso i (U.ι ≫ X.structureMorphism) sA hi KU eKU
    ∃ (Z : W.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ q),
        letI : IsOpenImmersion (Z.ι ≫ q) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sA q sW hqbase 2 ≫
              coordinate W D
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sW 2) eD) ≫
            (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι q).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫
            (schemeModulePullback (Z.ι ≫ q)).map
              (coordinate A DA
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eDA) ≫
              (rationalModulePullbackIso (Z.ι ≫ q)).hom := by
  dsimp only
  obtain ⟨Z, hne, l, hl, htriangle, hcoordinate⟩ := hF
  letI := hne
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := hl
  have hlq : l = (Z.ι ≫ q) ≫ i := by
    apply (cancel_mono U.ι).mp
    calc
      l ≫ U.ι = (Z.ι ≫ j) ≫ v := htriangle
      _ = Z.ι ≫ (j ≫ v) := Category.assoc _ _ _
      _ = Z.ι ≫ ((q ≫ i) ≫ U.ι) := congrArg (fun a => Z.ι ≫ a) hq.symm
      _ = ((Z.ι ≫ q) ≫ i) ≫ U.ι := by simp only [Category.assoc]
  subst l
  letI : IsOpenImmersion (Z.ι ≫ q) := IsOpenImmersion.of_comp (Z.ι ≫ q) i
  refine ⟨Z, hne, inferInstance, ?_⟩
  let sU := U.ι ≫ X.structureMorphism
  let sW := j ≫ (v ≫ X.structureMorphism)
  let sZ := Z.ι ≫ sW
  have hqbase : q ≫ sA = sW := by
    rw [← hi]
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ X.structureMorphism) hq
  have htbase : (Z.ι ≫ q) ≫ sA = sZ := by rw [Category.assoc, hqbase]
  let DA := DominantCartierPullback.pullbackHom i KU
  let eDA := canonicalOpenPullbackIso i sU sA hi KU eKU
  let cZ := coordinate Z.toScheme
    (DominantCartierPullback.pullbackHom Z.ι D)
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
    (canonicalOpenPullbackIso Z.ι sW sZ rfl D eD)
  have hcomposition := coordinate_canonicalOpenPullbackIso_comp
    (Z.ι ≫ q) i sU sA sZ hi htbase KU eKU
  have hcoordinateA : cZ = coordinate Z.toScheme
      (DominantCartierPullback.pullbackHom (Z.ι ≫ q) DA)
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sZ 2)
      (canonicalOpenPullbackIso (Z.ι ≫ q) sA sZ htbase DA eDA) := by
    change cZ = _ at hcoordinate
    exact hcoordinate.trans hcomposition.symm
  have hz := map_comp_coordinate_canonicalOpenPullbackIso (X := W) Z.ι sW sZ rfl D eD
  have ht := map_comp_coordinate_canonicalOpenPullbackIso (Z.ι ≫ q) sA sZ
    htbase DA eDA
  have hc := SchemeKaehlerExteriorPullbackTransport.map_comp sA q Z.ι sW hqbase
    (Z.ι ≫ q) rfl sZ rfl htbase 2
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp] at hc
  rw [← hcoordinateA] at ht
  rw [Functor.map_comp, Category.assoc, ← hz, ← Category.assoc, hc,
    Category.assoc]
  exact congrArg (fun a => (schemeModulePullbackCompIso Z.ι q).hom.app
    (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫ a) ht

end KltDP.Geometry.CanonicalDivisorTargetOpenSquare

#check @KltDP.Geometry.CanonicalDivisorTargetOpenSquare.exists_original_square
#print axioms KltDP.Geometry.CanonicalDivisorTargetOpenSquare.exists_original_square
