import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.SchemeKaehlerOpenRestrictionComp
import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.ProjectiveLineChartTriviality
import KltDP.Geometry.ModuleOpenOver
import KltDP.Geometry.ModuleOpenRestrictionTensor
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The cotangent sheaf of `P¹` is invertible; the canonical class `K_{P¹}`

On each standard chart `Spec k[t] → P¹` the accepted global differential sheaf restricts to the
differential sheaf of the affine line (accepted `SchemeKaehlerOpenRestriction.restrictionIso`,
`polynomialChartMap_structureMap`), which is the tilde of `Ω[k[t]/k]` (accepted
`AffineKaehlerTildeLocalization.iso`); the pinned `KaehlerDifferential.polynomialEquiv`
(`d P ↦ P'`, inverse `1 ↦ dt`) makes it free on the frame `dt`, hence trivial
(`chartUnitIso`). Transporting to the standard opens (as the accepted
`ProjectiveLineChartTriviality.chartRestrictionUnitIso` does) gives explicit local
trivializations of `Ω_{P¹}` on the two standard opens (`localTrivializations`), so

  **`Ω_{P¹}` is invertible** (`cotangent_isInvertible`), `ω_{P¹} := Ω_{P¹}` is an
  `InvertibleSheaf` (`canonicalSheaf`), `K_{P¹} := [Ω_{P¹}] ∈ Pic P¹` (`canonicalClass`), and
  **`deg K_{P¹} = exponent Ω_{P¹}`** (`canonicalDegree_eq_exponent`, from
  `ProjectiveLineDegreeExponent.degree_eq_exponent`).

**Not proved here:** the value `exponent Ω_{P¹} = −2` (the transition of the two frames `dt`,
`ds`, `s = 1/t`, is `ds = −t⁻² dt`: the computation of the transition unit of
`localTrivializations` through `restrictionIso_inv_d`, `iso_d`, `polynomialEquiv_D` and
`Derivation.leibniz_of_mul_eq_one` is recorded in `F04_CANONICAL_PLAN.md`), hence
`deg K_{P¹} = −2`; and `g(P¹) = 0` (`H¹(P¹, O) = 0`, no Čech comparison in the tree).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SchemeModuleRestriction KltDP.Geometry.SchemeKaehlerSheaf
open KltDP.Geometry.SchemeKaehlerOpenRestriction KltDP.Geometry.ProjectiveLineChartTriviality
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.AffineModuleTilde
open KltDP.Geometry.AffineKaehlerTildeDerivation

universe u

namespace KltDP.Geometry.ProjectiveLineCanonical

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

/-- `Ω_{P¹}`: the accepted global differential sheaf of `P¹ → Spec k`. -/
abbrev cotangent : (projectiveSpace k 1).Modules :=
  CurveCanonical.cotangentSheaf (projectiveSpaceToSpec k 1)

/-- The polynomial chart composed with the structure map is the polynomial algebra map. -/
theorem polynomialChartMap_comp_toSpec (i : Fin 2) :
    polynomialChartMap k i ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  rw [polynomialChartMap_structureMap, Polynomial.algebraMap_eq]

/-- `Ω_{P¹}` restricted along a polynomial chart is the tilde of `Ω[k[t]/k]`. -/
def chartTildeIso (i : Fin 2) :
    (restriction (polynomialChartMap k i)).obj (cotangent k) ≅
      (differentialModule k (Polynomial k)).tilde :=
  restrictionIso (projectiveSpaceToSpec k 1) (polynomialChartMap k i) ≪≫
    eqToIso (congrArg (fun f => SchemeKaehlerSheaf.baseRingSheaf f)
      (polynomialChartMap_comp_toSpec k i)) ≪≫
    AffineKaehlerTildeLocalization.iso k (Polynomial k)

/-- `Ω[k[t]/k]` is free on `dt` (pinned `polynomialEquiv`), so the chart restriction is trivial. -/
def chartUnitIso (i : Fin 2) :
    (restriction (polynomialChartMap k i)).obj (cotangent k) ≅
      _root_.SheafOfModules.unit (Spec (.of (Polynomial k))).ringCatSheaf :=
  chartTildeIso k i ≪≫
    linearEquivIso (M := differentialModule k (Polynomial k))
      (N := ModuleCat.of (Polynomial k) (Polynomial k)) (KaehlerDifferential.polynomialEquiv k) ≪≫
    unitIso (Polynomial k)

private def restrictionObjIsoOfEq {X Y : Scheme.{u}} {f g : Y ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (M : X.Modules) :
    (restriction f).obj M ≅ (restriction g).obj M := by
  cases h
  exact Iso.refl _

/-- `Ω_{P¹}` is trivial on each standard open (transport of `chartUnitIso` along the accepted
chart isomorphism, as in `chartRestrictionUnitIso`). -/
def chartOpenUnitIso (i : Fin 2) :
    (restriction (chartOpen k i).ι).obj (cotangent k) ≅
      _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf := by
  let f := polynomialChartMap k i
  let q := (polynomialChartOpenIso k i).inv
  have hq : q ≫ f = (chartOpen k i).ι := polynomialChartOpenIso_inv_chartMap k i
  exact ((restrictionCompIso f q).app (cotangent k) ≪≫
      restrictionObjIsoOfEq hq (cotangent k)).symm ≪≫
    (restriction q).mapIso (chartUnitIso k i) ≪≫ restrictionUnitIso q

/-- Explicit local trivializations of `Ω_{P¹}` on the two standard opens (frames `dt`, `ds`). -/
def localTrivializations :
    KltDP.SheafOfModules.LocalTrivializations (R := (projectiveSpace k 1).ringCatSheaf)
      (cotangent k) :=
  localTrivializationsOfOpenCharts (cotangent k)
    (fun i : ULift.{u} (Fin 2) => chartOpen k i.down)
    (fun x => by
      have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
        rw [chartOpen_sup]
        trivial
      change x ∈ chartOpen k 0 ∨ x ∈ chartOpen k 1 at hx
      rcases hx with hx | hx
      · exact ⟨⟨0⟩, hx⟩
      · exact ⟨⟨1⟩, hx⟩)
    (fun i => (chartOpenUnitIso k i.down).symm)

/-- **`Ω_{P¹}` is invertible.** -/
theorem cotangent_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveSpace k 1).ringCatSheaf) (cotangent k) :=
  (localTrivializations k).isInvertible

/-- `ω_{P¹} = Ω_{P¹}` as an invertible sheaf. -/
def canonicalSheaf : InvertibleSheaf (projectiveSpace k 1) :=
  CurveCanonical.canonicalSheaf (projectiveSpaceToSpec k 1) (cotangent_isInvertible k)

@[simp]
theorem canonicalSheaf_obj : (canonicalSheaf k).obj = cotangent k := rfl

/-- **`K_{P¹} := [Ω_{P¹}] ∈ Pic P¹`.** -/
def canonicalClass : (projectiveSpace k 1).Pic :=
  CurveCanonical.canonicalClass (projectiveSpaceToSpec k 1) (cotangent_isInvertible k)

/-- **`deg K_{P¹} = exponent Ω_{P¹}`**: the canonical degree is the transition exponent of the
cotangent sheaf on the standard cover. -/
theorem canonicalDegree_eq_exponent :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) =
      ProjectiveLineSheafExponent.exponent k (canonicalSheaf k) :=
  ProjectiveLineDegree.degree_eq_exponent k (canonicalSheaf k)

/-- The genus of `P¹` as defined: `dim_k H¹(P¹, O)` (its vanishing is not proved here). -/
abbrev genus : ℕ := CurveCanonical.genus (projectiveSpaceToSpec k 1)

end KltDP.Geometry.ProjectiveLineCanonical
