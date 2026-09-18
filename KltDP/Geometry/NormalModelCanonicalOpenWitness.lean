import KltDP.Geometry.NormalModelCanonicalFrame
import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.CanonicalOpenCoordinateCongruence

/-!
# Actual open-scheme witnesses for canonical normalization

An original open immersion into the frame neighborhood has an actual open
range. Its pinned range isomorphism changes a scheme witness into the literal
open-subset witness in `IsNormalized`, preserving both original maps and the
actual canonical rational-coordinate equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical

open CartierRationalCoordinate DominantCartierPullback

attribute [local irreducible] canonicalOpenPullbackIso

local instance integralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- A genuine open scheme witness supplies the existing original
normalization predicate through its actual range isomorphism. -/
theorem isNormalized_of_open_witness
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V Z : Scheme.{u}} [IsIntegral V] [IsIntegral Z]
    (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (l : Z ⟶ F.neighborhood) (j : Z ⟶ U.toScheme)
    [IsOpenImmersion l] [IsOpenImmersion j]
    (htriangle : j ≫ U.ι = (l ≫ F.toModel) ≫ v)
    (hcoordinate : coordinate Z (pullbackHom l F.divisor)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (l ≫ (F.toModel ≫ (v ≫ X.structureMorphism))) 2)
        (canonicalOpenPullbackIso l (F.toModel ≫ (v ≫ X.structureMorphism))
          (l ≫ (F.toModel ≫ (v ≫ X.structureMorphism))) rfl F.divisor F.canonicalIso) =
      coordinate Z (pullbackHom j KU)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (l ≫ (F.toModel ≫ (v ≫ X.structureMorphism))) 2)
        (canonicalOpenPullbackIso j (U.ι ≫ X.structureMorphism)
          (l ≫ (F.toModel ≫ (v ≫ X.structureMorphism)))
          (by simpa only [Category.assoc] using
            congrArg (fun a => a ≫ X.structureMorphism) htriangle) KU eKU)) :
    IsNormalized X U KU eKU v x F := by
  let A := l.opensRange
  letI : Nonempty A.toScheme := ⟨⟨l.base (genericPoint Z), ⟨genericPoint Z, rfl⟩⟩⟩
  letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  let r : A.toScheme ⟶ Z := l.isoOpensRange.inv
  have hr : r ≫ l = A.ι := l.isoOpensRange_inv_comp
  have hnew : (r ≫ j) ≫ U.ι = (A.ι ≫ F.toModel) ≫ v := by
    rw [Category.assoc, htriangle]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ F.toModel ≫ v) hr
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sU := U.ι ≫ X.structureMorphism
  let sZ := l ≫ sF
  let sA := A.ι ≫ sF
  have hj : j ≫ sU = sZ := by
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ X.structureMorphism) htriangle
  have hrbase : r ≫ sZ = sA := by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ sF) hr
  have hrl : (r ≫ l) ≫ sF = sA := by rw [hr]
  have hleft := coordinate_canonicalOpenPullbackIso_comp r l sF sZ sA
    rfl hrbase F.divisor F.canonicalIso
  have hrange := coordinate_canonicalOpenPullbackIso_congr (r ≫ l) A.ι
    hr sF sA hrl rfl F.divisor F.canonicalIso
  have hmiddle := canonicalOpenPullback_coordinate_congr sZ sA r hrbase
    (pullbackHom l F.divisor) (pullbackHom j KU)
    (canonicalOpenPullbackIso l sF sZ rfl F.divisor F.canonicalIso)
    (canonicalOpenPullbackIso j sU sZ hj KU eKU) hcoordinate
  have hright := coordinate_canonicalOpenPullbackIso_comp r j sU sZ sA
    hj hrbase KU eKU
  refine ⟨A, inferInstance, r ≫ j, inferInstance, hnew, ?_⟩
  exact hrange.symm.trans (hleft.symm.trans (hmiddle.trans hright))

end KltDP.Geometry.NormalModelCanonical

#check @KltDP.Geometry.NormalModelCanonical.isNormalized_of_open_witness
#print axioms KltDP.Geometry.NormalModelCanonical.isNormalized_of_open_witness
