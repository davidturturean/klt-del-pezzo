import KltDP.Geometry.NormalModelCanonicalOpenWitness
import KltDP.Geometry.CommonTargetCanonicalRestriction
import KltDP.Geometry.OpenImmersionNonemptyOverlap

/-!
# Passing to an actual locally normalized canonical reference

A literal equality of the two restricted rational coordinates on an actual
nonempty target overlap transfers normalization. The original frame, point,
and Cartier divisor remain unchanged. In the regular-point application the
reference equality is produced by the original local extension theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical

open CartierRationalCoordinate DominantCartierPullback OpenImmersionRational
open CommonTargetCanonical

attribute [local irreducible] canonicalOpenPullbackIso

local instance transferIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

local instance transferOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Transfer the same actual local frame through the actual common-reference
coordinate square; the new reference need not contain every target prime. -/
theorem isNormalized_of_reference_overlap
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (U W T : X.toScheme.Opens) [Nonempty U.toScheme] [Nonempty W.toScheme]
    [Nonempty T.toScheme] (hTU : T ≤ U) (hTW : T ≤ W)
    (KU : CartierDivisor U.toScheme) (KW : CartierDivisor W.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (eKW : cartierDivisorModule W.toScheme KW ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (W.ι ≫ X.structureMorphism) 2)
    (hcoordinate : coordinate T.toScheme
        (pullbackHom (X.toScheme.homOfLE hTW) KW)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (T.ι ≫ X.structureMorphism) 2)
        (canonicalRestrictionIso X W T hTW KW eKW) =
      coordinate T.toScheme (pullbackHom (X.toScheme.homOfLE hTU) KU)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          (T.ι ≫ X.structureMorphism) 2)
        (canonicalRestrictionIso X U T hTU KU eKU))
    {V : Scheme.{u}} [IsIntegral V] (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (hF : IsNormalized X U KU eKU v x F) :
    IsNormalized X W KW eKW v x F := by
  obtain ⟨A, hne, j, hj, htriangle, hFcoordinate⟩ := hF
  letI := hne
  letI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  letI := hj
  let iU := X.toScheme.homOfLE hTU
  let iW := X.toScheme.homOfLE hTW
  obtain ⟨Z, hZ, r, hrOpen, hr⟩ := exists_nonempty_open_overlap j iU
  letI := hZ
  letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
  letI := hrOpen
  let l : Z.toScheme ⟶ F.neighborhood := Z.ι ≫ A.ι
  let jW : Z.toScheme ⟶ W.toScheme := r ≫ iW
  have hnew : jW ≫ W.ι = (l ≫ F.toModel) ≫ v := by
    calc
      _ = r ≫ T.ι := by dsimp only [jW, iW]; rw [Category.assoc, Scheme.homOfLE_ι]
      _ = (r ≫ iU) ≫ U.ι := by dsimp only [iU]; rw [Category.assoc, Scheme.homOfLE_ι]
      _ = (Z.ι ≫ j) ≫ U.ι := congrArg (fun a => a ≫ U.ι) hr.symm
      _ = _ := by simpa only [l, Category.assoc] using congrArg (fun a => Z.ι ≫ a) htriangle
  let sF := F.toModel ≫ (v ≫ X.structureMorphism)
  let sU := U.ι ≫ X.structureMorphism
  let sW := W.ι ≫ X.structureMorphism
  let sA := A.ι ≫ sF
  let sT := T.ι ≫ X.structureMorphism
  let sZ := l ≫ sF
  have hjbase : j ≫ sU = sA := by
    simpa only [Category.assoc] using congrArg (fun a => a ≫ X.structureMorphism) htriangle
  have hZbase : Z.ι ≫ sA = sZ := (Category.assoc Z.ι A.ι sF).symm
  have hiUbase : iU ≫ sU = sT := restriction_structure X U T hTU
  have hiWbase : iW ≫ sW = sT := restriction_structure X W T hTW
  have hrbase : r ≫ sT = sZ := by
    rw [← hiUbase, ← Category.assoc, ← hr, Category.assoc, hjbase, hZbase]
  have hZjb : (Z.ι ≫ j) ≫ sU = sZ := by rw [Category.assoc, hjbase, hZbase]
  have hriUb : (r ≫ iU) ≫ sU = sZ := by rw [Category.assoc, hiUbase, hrbase]
  have h₁ := coordinate_canonicalOpenPullbackIso_comp Z.ι A.ι sF sA sZ
    rfl hZbase F.divisor F.canonicalIso
  have h₂ := canonicalOpenPullback_coordinate_congr sA sZ Z.ι hZbase
    (pullbackHom A.ι F.divisor) (pullbackHom j KU)
    (canonicalOpenPullbackIso A.ι sF sA rfl F.divisor F.canonicalIso)
    (canonicalOpenPullbackIso j sU sA hjbase KU eKU) hFcoordinate
  have h₃ := coordinate_canonicalOpenPullbackIso_comp Z.ι j sU sA sZ
    hjbase hZbase KU eKU
  have h₄ := coordinate_canonicalOpenPullbackIso_congr (Z.ι ≫ j) (r ≫ iU)
    hr sU sZ hZjb hriUb KU eKU
  have h₅ := coordinate_canonicalOpenPullbackIso_comp r iU sU sT sZ hiUbase hrbase KU eKU
  have h₆ := canonicalOpenPullback_coordinate_congr sT sZ r hrbase
    (pullbackHom iW KW) (pullbackHom iU KU)
    (canonicalRestrictionIso X W T hTW KW eKW)
    (canonicalRestrictionIso X U T hTU KU eKU) hcoordinate
  have h₇ := coordinate_canonicalOpenPullbackIso_comp r iW sW sT sZ hiWbase hrbase KW eKW
  exact isNormalized_of_open_witness X W KW eKW v x F l jW hnew
    (h₁.symm.trans (h₂.trans (h₃.trans (h₄.trans (h₅.symm.trans (h₆.symm.trans h₇))))))

end KltDP.Geometry.NormalModelCanonical

#check @KltDP.Geometry.NormalModelCanonical.isNormalized_of_reference_overlap
#print axioms KltDP.Geometry.NormalModelCanonical.isNormalized_of_reference_overlap
