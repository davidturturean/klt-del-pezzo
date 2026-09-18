import KltDP.Geometry.QuadraticCoverBaseChangeSquare
import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# Actual affine charts of the base change of a glued quadratic cover

For an original cover atlas `D`, an actual morphism `f : Y ⟶ X`, and an
actual affine open of `Y` subordinate to a preimage of one original chart,
the quadratic quotient with its coefficient mapped by the original `appLE`
is the actual pullback of `D.morphism`. No comparison isomorphism is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
  (f : Y ⟶ X) (i : ι) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ D.opens i)

/-- The original map on sections, with the original source and target opens. -/
def baseChangeCoefficientHom : Γ(X, D.opens i) →+* Γ(Y, V) :=
  (f.appLE (D.opens i) V hV).hom

/-- The actual mapped branch coefficient of the original whole chart. -/
def baseChangeCoefficient : Γ(Y, V) :=
  D.baseChangeCoefficientHom f i V hV (res X le_rfl (D.sections i))

@[simp]
theorem baseChangeCoefficient_eq :
    D.baseChangeCoefficient f i V hV =
      f.appLE (D.opens i) V hV (D.sections i) := by
  simp only [baseChangeCoefficient, res_self, baseChangeCoefficientHom]

/-- The original quadratic quotient after actual section-ring base change. -/
abbrev baseChangeChart : Scheme.{u} := affineScheme (D.baseChangeCoefficient f i V hV)

/-- Its original coefficient-induced map into the original quadratic chart. -/
def baseChangeChartToChart : D.baseChangeChart f i V hV ⟶ D.chart i := by
  letI : Algebra Γ(X, D.opens i) Γ(Y, V) :=
    (D.baseChangeCoefficientHom f i V hV).toAlgebra
  exact baseChangeProjection (S := Γ(Y, V)) (res X le_rfl (D.sections i))

/-- The chart is the actual pullback of the original global cover morphism. -/
theorem baseChangeChartIsPullback (hVA : IsAffineOpen V) :
    IsPullback (D.baseChangeChartToChart f i V hV ≫ D.chartι i)
      (toBase (D.baseChangeCoefficient f i V hV)) D.morphism (hVA.fromSpec ≫ f) := by
  letI : Algebra Γ(X, D.opens i) Γ(Y, V) :=
    (D.baseChangeCoefficientHom f i V hV).toAlgebra
  rw [← IsAffineOpen.Spec_map_appLE_fromSpec f (D.affine i) hVA hV]
  exact (baseChangeIsPullback (S := Γ(Y, V))
    (res X le_rfl (D.sections i))).paste_horiz (D.chartIsPullback i)

/-- The proved canonical identification retains the original `D.morphism` and `f`. -/
def baseChangeChartIso (hVA : IsAffineOpen V) :
    D.baseChangeChart f i V hV ≅ pullback D.morphism (hVA.fromSpec ≫ f) :=
  (D.baseChangeChartIsPullback f i V hV hVA).isoPullback

@[simp, reassoc]
theorem baseChangeChartIso_hom_fst (hVA : IsAffineOpen V) :
    (D.baseChangeChartIso f i V hV hVA).hom ≫ pullback.fst _ _ =
      D.baseChangeChartToChart f i V hV ≫ D.chartι i :=
  (D.baseChangeChartIsPullback f i V hV hVA).isoPullback_hom_fst

@[simp, reassoc]
theorem baseChangeChartIso_hom_snd (hVA : IsAffineOpen V) :
    (D.baseChangeChartIso f i V hV hVA).hom ≫ pullback.snd _ _ =
      toBase (D.baseChangeCoefficient f i V hV) :=
  (D.baseChangeChartIsPullback f i V hV hVA).isoPullback_hom_snd

#print axioms baseChangeChartIsPullback
#print axioms baseChangeChartIso

end KltDP.Geometry.QuadraticCoverAtlas.Data
