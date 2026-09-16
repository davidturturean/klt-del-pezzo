import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# Sections of a glued closed subscheme over affine charts

The accepted closed subscheme of an ideal sheaf `I` is glued from the quotient
charts `Spec (Γ(X, U) ⧸ I(U))`, and the accepted `glueDataObjIso` identifies the
chart with the preimage of the affine open `U`. Consequently the sections of the
subscheme over that preimage are the quotient ring `Γ(X, U) ⧸ I(U)`.

For the intersection subscheme `C ∩ D` of a prime curve and an effective Cartier
divisor, on an affine restricted chart with local equation `d|_C`, this gives
`Γ(C ∩ D, i⁻¹U) ≃+* Γ(C, U) ⧸ (d|_C)`: the local ring-of-functions identification
used by the sum formula for `intersectionDegree`. The identification of this
quotient with `O_{C,y} ⧸ (d|_C)` at a chart containing a single intersection point,
and the existence of such separating affine charts, are not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- Sections of the glued closed subscheme over the preimage of an affine open
are the quotient of the sections of `X` by the ideal. -/
def gluedSectionsIso :
    Γ(I.glueData.glued, I.gluedTo ⁻¹ᵁ (U : X.Opens)) ≅
      CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
  (I.gluedTo ⁻¹ᵁ (U : X.Opens)).topIso.symm ≪≫ Scheme.Γ.mapIso (I.glueDataObjIso U).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I.ideal U))

/-- The ring-equivalence form. -/
def gluedSectionsEquiv :
    Γ(I.glueData.glued, I.gluedTo ⁻¹ᵁ (U : X.Opens)) ≃+* (Γ(X, U) ⧸ I.ideal U) :=
  (I.gluedSectionsIso U).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Scheme.IdealSheafData

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- On an affine restricted chart, the functions of `C ∩ D` over the chart are the
functions of `C` modulo the restricted local equation. -/
def intersectionChartSectionsEquiv (c : C.GenericChart D)
    (hU : IsAffineOpen (C.chartPreimage D c.1)) :
    Γ(C.intersectionScheme D hD hC,
        C.intersectionInclusion D hD hC ⁻¹ᵁ C.chartPreimage D c.1) ≃+*
      (Γ(C.toScheme, C.chartPreimage D c.1) ⧸
        Ideal.span ({C.restrictedCoefficient D c.1} : Set Γ(C.toScheme, C.chartPreimage D c.1))) :=
  ((effectiveCartierIdealDataOfRegularEquations C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC)).gluedSectionsEquiv
        ⟨C.chartPreimage D c.1, hU⟩).trans
    (Ideal.quotEquivOfEq
      (effectiveCartierIdealDataOfRegularEquations_ideal_chart C.toScheme
        (C.restrictCartier D hD hC) (C.restrictCartier_hasRegularEquations D hD hC)
        (C.restrictedChart D hD hC c) hU))

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
