import KltDP.Geometry.CanonicalDivisorTargetOpenSquare

/-!
# Packaging the actual normalized target identification

The witness is the original canonical open pullback isomorphism. Hiding this
specific term behind an existential lets later affine arguments retain its
proved original differential square without expanding that isomorphism.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalDivisorTargetOpenSquare

open NormalModelCanonical CartierRationalCoordinate OpenImmersionRational

attribute [local irreducible] canonicalOpenPullbackIso

local instance witnessReferenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance witnessOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Normalization of the constructed original frame supplies the same
square on its supplied source scheme and Cartier identification. -/
theorem exists_target_identification
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
    ∃ eDA : cartierDivisorModule A DA ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2,
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
  refine ⟨canonicalOpenPullbackIso i (U.ι ≫ X.structureMorphism) sA hi KU eKU, ?_⟩
  exact exists_original_square X U KU eKU i sA hi v x j w hw D eD hF q hq

end KltDP.Geometry.CanonicalDivisorTargetOpenSquare

#check @KltDP.Geometry.CanonicalDivisorTargetOpenSquare.exists_target_identification
#print axioms KltDP.Geometry.CanonicalDivisorTargetOpenSquare.exists_target_identification
