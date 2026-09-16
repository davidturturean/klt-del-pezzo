import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.SchemeKaehlerPullbackRestrictionComp

/-!
# The actual global Kähler sheaf on the original quotient charts

The base algebra on an ambient affine chart is obtained from the original
structure morphism. The original quotient-chart inclusion composed with
the global structure morphism is its actual quotient-algebra spectrum map.
The existing Kähler pullback comparison and this proved equality identify
the global differential sheaf on the quotient chart with its original
affine differential sheaf. No structure-map compatibility is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedChartKaehlerPullback

open SchemeKaehlerSheaf SchemeKaehlerOpenRestriction

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData) (U : X.affineOpens)

/-- The original base algebra on the original ambient affine section ring. -/
def chartAlgebra : Algebra R Γ(X, U.1) :=
  (baseToAffineSectionsMap f U.2).hom.toAlgebra

/-- The original glued-chart structure map is the actual quotient-algebra spectrum map. -/
theorem chartBaseMap_comp :
    letI : Algebra R Γ(X, U.1) := chartAlgebra f U
    I.glueData.ι U ≫ (I.gluedTo ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U))) := by
  letI : Algebra R Γ(X, U.1) := chartAlgebra f U
  rw [← Category.assoc, I.ι_gluedTo U, I.glueDataObjι_ι U, Category.assoc,
    ← Spec_map_baseToAffineSectionsMap f U.2, ← Spec.map_comp]
  congr 1

/-- The actual global differential sheaf pulled to the quotient chart is the
original affine differential sheaf for its induced base algebra. -/
def iso :
    letI : Algebra R Γ(X, U.1) := chartAlgebra f U
    (schemeModulePullback (I.glueData.ι U)).obj (baseRingSheaf (I.gluedTo ≫ f)) ≅
      baseRingSheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U)))) := by
  letI : Algebra R Γ(X, U.1) := chartAlgebra f U
  exact pullbackIso (I.gluedTo ≫ f) (I.glueData.ι U) ≪≫
    eqToIso (congrArg baseRingSheaf (chartBaseMap_comp f I U))

end KltDP.Geometry.GluedChartKaehlerPullback
