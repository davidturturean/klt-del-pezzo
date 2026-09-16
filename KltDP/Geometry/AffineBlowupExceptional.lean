import KltDP.Geometry.AffineBlowupCenter
import KltDP.Geometry.PrimeCurveSubscheme
import KltDP.Geometry.SchemeConormal

/-!
# The actual global exceptional closed scheme and its conormal sheaf

The extended center is the previously constructed actual ideal-sheaf data
on the Rees Proj. Its quotient charts are glued by the pinned ideal-sheaf
glue data, using the already reviewed generic closed-inclusion adapter.
The resulting closed scheme, inclusion, kernel ideal module, and conormal
module sheaf are actual objects and morphisms.

Regular principal equations on the ambient charts are already proved.
Identifying the new sheaf's affine restrictions with the previously
computed cotangent modules, and hence proving that it is invertible,
remain separate comparison theorems. No global normal-bundle or
intersection formula is part of these definitions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual extended center on the existing affine blowup. -/
def exceptionalIdeal : (scheme I).IdealSheafData := extendedCenter I (toSpec I)

/-- The global exceptional closed scheme, obtained by gluing the actual
quotients by the extended center. -/
def exceptionalScheme : Scheme.{u} := (exceptionalIdeal I).glueData.glued

/-- Its actual inclusion into the original Rees Proj. -/
def exceptionalι : exceptionalScheme I ⟶ scheme I := (exceptionalIdeal I).gluedTo

instance : IsClosedImmersion (exceptionalι I) :=
  (exceptionalIdeal I).gluedTo_isClosedImmersion

/-- The underlying closed set is exactly the support of the actual extended ideal. -/
theorem range_exceptionalι :
    Set.range (exceptionalι I).base = (exceptionalIdeal I).support :=
  (exceptionalIdeal I).range_gluedTo

/-- An actual affine quotient chart identifies the inverse image of its
ambient affine open in the global exceptional scheme. -/
def exceptionalAffineChartIso (U : (scheme I).affineOpens) :
    Spec (CommRingCat.of (Γ(scheme I, U.1) ⧸ (exceptionalIdeal I).ideal U)) ≅
      ((exceptionalι I) ⁻¹ᵁ U.1).toScheme :=
  (exceptionalIdeal I).glueDataObjIso U

/-- The affine comparison retains the actual restricted inclusion map. -/
theorem exceptionalAffineChartIso_hom_restrict (U : (scheme I).affineOpens) :
    (exceptionalAffineChartIso I U).hom ≫ (exceptionalι I) ∣_ U.1 =
      (exceptionalIdeal I).glueDataObjι U :=
  (exceptionalIdeal I).glueDataObjIso_hom_restrict U

/-- Regular local equations for this exact ideal were derived from the
actual Rees-chart equations. This is a theorem, not a field of its data. -/
theorem exceptionalIdeal_locallyPrincipalRegular :
    ExtendedCenterLocallyPrincipalRegular I (toSpec I) :=
  toSpec_extendedCenterLocallyPrincipalRegular I

/-- The global ideal module is the actual sheaf kernel of the structural
map to the exceptional closed scheme. -/
def exceptionalIdealModule : (scheme I).Modules := schemeKernelIdeal (exceptionalι I)

/-- The actual global conormal module sheaf on the exceptional scheme. -/
def exceptionalConormalSheaf : (exceptionalScheme I).Modules :=
  schemeConormalSheaf (exceptionalι I)

end KltDP.Geometry.AffineBlowup
