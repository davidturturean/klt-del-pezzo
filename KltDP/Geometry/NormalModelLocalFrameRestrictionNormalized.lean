import KltDP.Geometry.NormalModelLocalFrameRestriction
import KltDP.Geometry.CanonicalCoordinateOpenComposition
import KltDP.Geometry.CanonicalOpenCoordinateCongruence

/-!
# Restriction preserves the actual canonical normalization

Pull the original normalization witness back through the original smaller
neighborhood. Both its model triangle and its rational-coordinate equality
follow from the original restriction square and the already proved open
composition formulas. The smaller neighborhood still contains the point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical.LocalFrame

open CartierRationalCoordinate DominantCartierPullback

attribute [local irreducible] canonicalOpenPullbackIso

local instance targetOpenIntegral {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance restrictionNormalizedOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Shrinking through the original point preserves the genuine original
rational-form normalization, with its nonempty common-open witness. -/
theorem restrict_isNormalized
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (Z : F.neighborhood.Opens) (hZ : F.point ∈ Z)
    (hF : IsNormalized X U KU eKU v x F) :
    IsNormalized X U KU eKU v x (F.restrict Z hZ) := by
  letI : Nonempty Z.toScheme := ⟨⟨F.point, hZ⟩⟩
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  obtain ⟨A, hne, j, hj, htriangle, hcoordinate⟩ := hF
  letI := hne
  letI : Nonempty A := ⟨Classical.choice hne⟩
  letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  letI := hj
  let T := Z.ι ⁻¹ᵁ A
  letI : Nonempty T.toScheme := ⟨Classical.choice (preimage_nonempty Z.ι A)⟩
  letI : IsIntegral T.toScheme := isIntegral_of_isOpenImmersion T.ι
  let i : T.toScheme ⟶ A.toScheme := Z.ι ∣_ A
  have hi : i ≫ A.ι = T.ι ≫ Z.ι := morphismRestrict_ι Z.ι A
  have hnew : (i ≫ j) ≫ U.ι =
      (T.ι ≫ (Z.ι ≫ F.toModel)) ≫ v := by
    rw [Category.assoc, htriangle]
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ F.toModel ≫ v) hi
  refine ⟨T, inferInstance, i ≫ j, inferInstance, hnew, ?_⟩
  let sU := U.ι ≫ X.structureMorphism
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sZ := (Z.ι ≫ F.toModel) ≫ (v ≫ X.structureMorphism)
  let sA := A.ι ≫ sF
  let sT := T.ι ≫ sZ
  have hZbase : Z.ι ≫ sF = sZ := (Category.assoc _ _ _).symm
  have hjbase : j ≫ sU = sA := by
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ X.structureMorphism) htriangle
  have hibase : i ≫ sA = sT := by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ sF) hi
  have hleftbase : (T.ι ≫ Z.ι) ≫ sF = sT := by rw [Category.assoc, hZbase]
  have hrightbase : (i ≫ A.ι) ≫ sF = sT := by rw [Category.assoc]; exact hibase
  let DA := pullbackHom A.ι F.divisor
  let eA := canonicalOpenPullbackIso A.ι sF sA rfl F.divisor F.canonicalIso
  let EA := pullbackHom j KU
  let eA' := canonicalOpenPullbackIso j sU sA hjbase KU eKU
  have h₁ := coordinate_canonicalOpenPullbackIso_comp T.ι Z.ι sF sZ sT
    hZbase rfl F.divisor F.canonicalIso
  have h₂ := coordinate_canonicalOpenPullbackIso_congr (T.ι ≫ Z.ι) (i ≫ A.ι)
    hi.symm sF sT hleftbase hrightbase F.divisor F.canonicalIso
  have h₃ := coordinate_canonicalOpenPullbackIso_comp i A.ι sF sA sT
    rfl hibase F.divisor F.canonicalIso
  have hA : coordinate A.toScheme DA
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA =
    coordinate A.toScheme EA
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA' := hcoordinate
  have h₄ := canonicalOpenPullback_coordinate_congr sA sT i hibase
    DA EA eA eA' hA
  have h₅ := coordinate_canonicalOpenPullbackIso_comp i j sU sA sT
    hjbase hibase KU eKU
  exact h₁.trans (h₂.trans (h₃.symm.trans (h₄.trans h₅)))

end KltDP.Geometry.NormalModelCanonical.LocalFrame

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame.restrict_isNormalized
#print axioms KltDP.Geometry.NormalModelCanonical.LocalFrame.restrict_isNormalized
