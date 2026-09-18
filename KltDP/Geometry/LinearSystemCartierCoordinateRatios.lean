import KltDP.Geometry.LinearSystemCoordinateEvaluation
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.CartierDivisorTrivialization

/-!
# Original linear-system coordinates are actual Cartier section ratios

The original normalized coordinate multiplies the selected original
section to the corresponding section. For the actual Cartier module,
its inclusion into rational functions gives the exact quotient of the
original global rational values. The denominator is nonzero because
the selected section is nonvanishing on a nonempty original chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitExtraction InvertibleSectionNonvanishingOpen
  ProjectiveCoordinateSectionBasicOpen

/-- The normalized coordinate is an actual local section multiplier,
independently of which original invertible atlas frame was chosen. -/
theorem coordinates_smul_section {X : Scheme.{u}} (L : InvertibleSheaf X)
    {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
    (i : L.localTrivializations.I) {W : X.Opens}
    (hWi : W ≤ L.localTrivializations.X i) (m : Fin (n + 1))
    (hWm : W ≤ nonvanishingOpen X L (s m)) (j : Fin (n + 1)) :
    letI : Module Γ(X, W) (L.obj.val.obj (op W)) := (L.obj.val.obj (op W)).isModule
    let vm : L.obj.val.obj (op W) := (s m).val (op W)
    let vj : L.obj.val.obj (op W) := (s j).val (op W)
    coordinates L s i hWi m hWm j • vm = vj := by
  dsimp only
  apply (chartEquiv X L.obj L.localTrivializations i hWi).injective
  rw [map_smul]
  change coordinates L s i hWi m hWm j * coefficient L (s m) i hWi =
    coefficient L (s j) i hWi
  exact (mul_comm _ _).trans (denominator_mul_coordinates L s i hWi m hWm j)

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)

/-- A compatible original Cartier section has its original global
rational value on every nonempty original open. -/
theorem cartier_section_value_on_open
    (s : (cartierDivisorInvertibleSheaf X D).obj.sections)
    (U : X.Opens) [Nonempty U] :
    rationalFunctionModuleSectionsEquiv X U (s.val (op U)).val =
      cartierGlobalSectionRationalValue X D (s.val (op ⊤)) := by
  rw [← s.property (homOfLE (le_top : U ≤ ⊤)).op]
  exact cartierGlobalSectionRationalValue_restrict X D (s.val (op ⊤)) U

variable {n : ℕ} (s : Fin (n + 1) → (cartierDivisorInvertibleSheaf X D).obj.sections)
  (c : Chart (cartierDivisorInvertibleSheaf X D) s) [Nonempty c.affineOpen.1]

/-- Nonvanishing on the actual nonempty chart forces the selected
original top section, and hence its rational value, to be nonzero. -/
theorem cartier_denominator_value_ne_zero :
    cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) ≠ 0 := by
  apply cartierGlobalSectionRationalValue_ne_zero
  intro hzero
  have hlocal : (s c.index).val (op c.affineOpen.1) = 0 := by
    calc
      _ = (cartierDivisorModule X D).val.map
          (homOfLE (le_top : c.affineOpen.1 ≤ ⊤)).op
            ((s c.index).val (op ⊤)) :=
        ((s c.index).property (homOfLE (le_top : c.affineOpen.1 ≤ ⊤)).op).symm
      _ = 0 := by rw [hzero, map_zero]
  have hcoeff : coefficient (cartierDivisorInvertibleSheaf X D)
      (s c.index) c.frame c.inFrame = 0 := by
    change chartEquiv X (cartierDivisorInvertibleSheaf X D).obj
      (cartierDivisorInvertibleSheaf X D).localTrivializations c.frame c.inFrame
        ((s c.index).val (op c.affineOpen.1)) = 0
    rw [hlocal, map_zero]
  exact (coefficient_isUnit (cartierDivisorInvertibleSheaf X D)
    (s c.index) c.frame c.inFrame c.nonvanishing).ne_zero hcoeff

/-- The original normalized coordinate's germ is precisely the ratio
of the original Cartier global-section rational values. -/
theorem germ_coordinates_eq_cartierRatio (j : Fin (n + 1)) :
    X.germToFunctionField c.affineOpen.1
        (coordinates (cartierDivisorInvertibleSheaf X D) s
          c.frame c.inFrame c.index c.nonvanishing j) =
      cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
        cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) := by
  have h := coordinates_smul_section (cartierDivisorInvertibleSheaf X D) s
    c.frame c.inFrame c.index c.nonvanishing j
  have he := congrArg
    (fun t : (cartierDivisorModule X D).val.obj (op c.affineOpen.1) =>
      rationalFunctionModuleSectionsEquiv X c.affineOpen.1 t.val) h
  change rationalFunctionModuleSectionsEquiv X c.affineOpen.1
      (coordinates (cartierDivisorInvertibleSheaf X D) s
        c.frame c.inFrame c.index c.nonvanishing j •
          ((s c.index).val (op c.affineOpen.1)).val) =
    rationalFunctionModuleSectionsEquiv X c.affineOpen.1 ((s j).val (op c.affineOpen.1)).val at he
  rw [map_smul, Algebra.smul_def, cartier_section_value_on_open,
    cartier_section_value_on_open] at he
  exact (eq_div_iff (cartier_denominator_value_ne_zero X D s c)).mpr he

/-- The actual original linear-system morphism pulls the original
coordinate fraction back to the exact original Cartier section ratio. -/
theorem morphism_coordinate_germ_eq_cartierRatio
    {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (hcover : (⨆ j, nonvanishingOpen X (cartierDivisorInvertibleSheaf X D) (s j)) = ⊤)
    (j : Fin (n + 1)) :
    X.germToFunctionField c.affineOpen.1
        ((morphism (cartierDivisorInvertibleSheaf X D) s f hcover).appLE
          (standardOpen k n c.index) c.affineOpen.1
          (chart_le_preimage_standardOpen (cartierDivisorInvertibleSheaf X D) s f hcover c)
          (coordinateSection k n c.index j)) =
      cartierGlobalSectionRationalValue X D ((s j).val (op ⊤)) /
        cartierGlobalSectionRationalValue X D ((s c.index).val (op ⊤)) := by
  rw [morphism_appLE_coordinateSection]
  exact germ_coordinates_eq_cartierRatio X D s c j

end KltDP.Geometry.LinearSystemMorphism
