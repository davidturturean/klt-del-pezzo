import KltDP.Geometry.PushforwardRelativeSpecConstruction

/-!
# The actual normalization by integral closure of the pushforward algebra

The normalization target is independently the gluing of the actual
integral-closure spectra. Their original inclusion induces the canonical
isomorphism from the relative spectrum of the whole pushforward algebra
for universally closed maps. Both original maps to the base and the
original source factorization are retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]

/-- The scheme glued from the actual original integral-closure subalgebras. -/
def normalization : Scheme.{u} := (normalizationDatum f).glued

/-- The original structural map from those integral-closure charts. -/
def normalizationToBase : normalization f ⟶ Y := (normalizationDatum f).toBase

/-- The literal chartwise inclusions induce an isomorphism of the two actual glued targets. -/
def normalizationComparison : relativeSpec f ≅ normalization f :=
  HasColimit.isoOfNatIso (F := (datum f).functor) (G := (normalizationDatum f).functor)
    (IntegralClosureSpectrumDiagram.comparison f)

/-- The comparison on each original chart is induced by the integral-element inclusion. -/
@[reassoc] theorem chart_normalizationComparison (U : Y.AffineZariskiSite) :
    chart f U ≫ (normalizationComparison f).hom =
      (IntegralClosureSpectrumDiagram.comparisonHom f).app U ≫
        colimit.ι (normalizationDatum f).functor U :=
  HasColimit.isoOfNatIso_ι_hom (F := (datum f).functor)
    (G := (normalizationDatum f).functor) (IntegralClosureSpectrumDiagram.comparison f) U

/-- The canonical comparison preserves the original map to the base. -/
@[reassoc] theorem normalizationComparison_toBase :
    (normalizationComparison f).hom ≫ normalizationToBase f = toBase f := by
  apply colimit.hom_ext
  intro U
  change chart f U ≫ (normalizationComparison f).hom ≫ normalizationToBase f =
    chart f U ≫ toBase f
  rw [chart_normalizationComparison_assoc]
  change (IntegralClosureSpectrumDiagram.comparisonHom f).app U ≫
    colimit.ι (normalizationDatum f).functor U ≫ (normalizationDatum f).toBase =
      colimit.ι (datum f).functor U ≫ (datum f).toBase
  rw [Scheme.Cover.RelativeGluingData.ι_toBase,
    Scheme.Cover.RelativeGluingData.ι_toBase]
  change (IntegralClosureSpectrumDiagram.comparisonHom f).app U ≫
    (IntegralClosureSpectrumDiagram.toBaseSpectra f).app U ≫ U.2.fromSpec =
      (PushforwardAffineDiagram.toBaseSpectra f).app U ≫ U.2.fromSpec
  rw [← Category.assoc]
  exact congrArg (fun a => a ≫ U.2.fromSpec)
    (NatTrans.congr_app (IntegralClosureSpectrumDiagram.comparisonHom_toBase f) U)

/-- The original source map into the actual integral-closure gluing. -/
def toNormalization : X ⟶ normalization f :=
  fromSource f ≫ (normalizationComparison f).hom

/-- The original source, original integral closure and original base form the actual factorization. -/
@[reassoc] theorem toNormalization_toBase : toNormalization f ≫ normalizationToBase f = f := by
  rw [toNormalization, Category.assoc, normalizationComparison_toBase, fromSource_toBase]

end KltDP.Geometry.PushforwardRelativeSpec
