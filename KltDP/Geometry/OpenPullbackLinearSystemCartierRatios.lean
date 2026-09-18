import KltDP.Geometry.OpenPullbackCartierSectionValues
import KltDP.Geometry.ProjectiveImageChartFieldGeneration

/-!
# Actual open-pullback linear-system coordinates in the original function field

The original sections may have a base locus on the ambient scheme. On
any actual open immersion where their literal pullbacks generate, the
original linear-system coordinates, transported by the inverse original
function-field isomorphism, are the original global Cartier section ratios.
No extension or ambient basepoint-freeness hypothesis is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OpenPullbackLinearSystemCartierRatios

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open LinearSystemMorphism InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsOpenImmersion f] (D : CartierDivisor X)
  {n : ℕ} (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)

/-- Exactly the original pullback line and original pulled section tuple. -/
abbrev pulledLine := pullbackInvertibleSheaf f (cartierDivisorInvertibleSheaf X D)

abbrev pulledTuple : Fin (n + 1) → (pulledLine f D).obj.sections :=
  fun i => InvertibleSheafSectionPowersPullback.pullbackSection f
    (cartierDivisorModule X D) (s i)

variable (c : Chart (pulledLine f D) (pulledTuple f D s)) [Nonempty c.affineOpen.1]

/-- A nonvanishing selected pulled section has nonzero original ambient
Cartier rational value. Injectivity is through the actual open pullback. -/
theorem denominator_value_ne_zero :
    cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) ≠ 0 := by
  intro hzero
  have hv : OpenPullbackCartierSectionValues.rationalValue f D c.affineOpen.1
      ((pulledTuple f D s c.index).val (op c.affineOpen.1)) =
      OpenPullbackCartierSectionValues.rationalValue f D c.affineOpen.1 0 := by
    rw [OpenPullbackCartierSectionValues.rationalValue_pullbackSection,
      OpenPullbackCartierSectionValues.rationalValue_zero, hzero]
  have hlocal := (OpenPullbackCartierSectionValues.rationalValue_injective
    f D c.affineOpen.1) hv
  have hcoeff : coefficient (pulledLine f D) (pulledTuple f D s c.index)
      c.frame c.inFrame = 0 := by
    unfold coefficient
    rw [hlocal, map_zero]
  exact (coefficient_isUnit (pulledLine f D) (pulledTuple f D s c.index)
    c.frame c.inFrame c.nonvanishing).ne_zero hcoeff

/-- The actual normalized coordinate, read through the inverse original
open function-field isomorphism, is the original global section ratio. -/
theorem inverse_germ_coordinates (j : Fin (n + 1)) :
    (functionFieldIso f).inv
        (Y.germToFunctionField c.affineOpen.1
          (coordinates (pulledLine f D) (pulledTuple f D s)
            c.frame c.inFrame c.index c.nonvanishing j)) =
      cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
        cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) := by
  have h := coordinates_smul_section (pulledLine f D) (pulledTuple f D s)
    c.frame c.inFrame c.index c.nonvanishing j
  have hv := congrArg (OpenPullbackCartierSectionValues.rationalValue f D c.affineOpen.1) h
  rw [OpenPullbackCartierSectionValues.rationalValue_smul,
    OpenPullbackCartierSectionValues.rationalValue_pullbackSection,
    OpenPullbackCartierSectionValues.rationalValue_pullbackSection] at hv
  exact (eq_div_iff (denominator_value_ne_zero f D s c)).mpr hv

variable {k : Type u} [Field k] (b : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen Y (pulledLine f D) (pulledTuple f D s j)) = ⊤)

/-- This applies to the original linear-system morphism of the original
pulled sections, with its original base structure and chart section map. -/
theorem inverse_morphism_coordinate_germ (j : Fin (n + 1)) :
    (functionFieldIso f).inv
        (Y.germToFunctionField c.affineOpen.1
          ((morphism (pulledLine f D) (pulledTuple f D s) (f ≫ b) hcover).appLE
            (standardOpen k n c.index) c.affineOpen.1
            (chart_le_preimage_standardOpen (pulledLine f D) (pulledTuple f D s)
              (f ≫ b) hcover c) (coordinateSection k n c.index j))) =
      cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
        cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) := by
  rw [morphism_appLE_coordinateSection]
  exact inverse_germ_coordinates f D s c j

end KltDP.Geometry.OpenPullbackLinearSystemCartierRatios
