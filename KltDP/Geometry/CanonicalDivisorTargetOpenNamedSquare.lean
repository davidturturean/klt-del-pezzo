import KltDP.Geometry.OriginalCanonicalDifferentialSquare
import KltDP.Geometry.CanonicalDivisorTargetOpenSquareWitness

/-! The original normalized target witness supplies the named square package. -/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalDivisorTargetOpenSquare

open NormalModelCanonical CartierRationalCoordinate

local instance namedReferenceIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance namedOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Normalization of the constructed original frame supplies the same
square on its supplied source scheme and Cartier identification. -/
theorem normalized_square
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
    OriginalCanonicalDifferentialSquare sA sW q hqbase DA D eD := by
  exact ⟨exists_target_identification X U KU eKU i sA hi v x j w hw D eD hF q hq⟩

end KltDP.Geometry.CanonicalDivisorTargetOpenSquare

#check @KltDP.Geometry.CanonicalDivisorTargetOpenSquare.normalized_square
#print axioms KltDP.Geometry.CanonicalDivisorTargetOpenSquare.normalized_square
