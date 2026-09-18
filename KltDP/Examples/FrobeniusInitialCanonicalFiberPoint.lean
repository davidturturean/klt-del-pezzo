import KltDP.Examples.FrobeniusProjectiveCoordinatePicard
import KltDP.Examples.FrobeniusGraphPicardClassChartSections
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal
import KltDP.Geometry.GluedSubschemeStalkKernel
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.SchematicImageToImageIso

/-!
# The original coordinate point as an effective Cartier divisor

The original point kernel has the regular equation X on the first chart
and the unit equation on the other chart. These proved equations construct
its effective Cartier divisor using the existing general constructor.
Its negative Cartier sheaf is identified with the original point ideal,
so its Cartier-to-Picard class is the inverse original ideal class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFiberPoint

open KltDP.Geometry ProjectiveLineComparison
open SchemeKernelIdealIsoTransport SchematicImageToImageIso
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinateTransition
open FrobeniusProjectiveCoordinatePicard FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusProjectivePoints

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance pointCartierLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance pointCartierProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance pointCartierChartNonempty (i : Fin 2) : Nonempty (chartOpen k i) :=
  ⟨⟨(rulingProjection (k := k) 0).base (genericPoint (projectiveProduct k)),
    rulingGeneric_mem 0 i⟩⟩

local instance pointCartierFirstNonempty : Nonempty (firstOpen (k := k)) := by
  rw [firstOpen_eq]
  infer_instance

/-- The first original ambient-section generator is a nonzerodivisor. -/
theorem firstSection_regular :
    firstSection (k := k) ∈ nonZeroDivisors Γ(projectiveSpace k 1, firstOpen (k := k)) := by
  let e := ((polynomialChartMap k 0).appIso ⊤).commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e) e.injective
  change e (e.symm affineCoordinateEquation) ∈
    nonZeroDivisors Γ(Spec (CommRingCat.of (Polynomial k)), ⊤)
  rw [e.apply_symm_apply]
  exact affineCoordinateEquation_regular

/-- The second standard chart, as an actual affine open of the projective line. -/
def coordinateRightAffineOpen : (projectiveSpace k 1).affineOpens :=
  ⟨chartOpen k 1, chartOpen_isAffineOpen k 1⟩

/-- The original point is absent from the second chart, so its ideal there is the unit ideal. -/
theorem coordinateRightIdeal_eq_top :
    (coordinatePointIdeal (k := k)).ideal coordinateRightAffineOpen = ⊤ := by
  change (coordinatePoint (k := k)).ker.ideal coordinateRightAffineOpen = ⊤
  apply ker_ideal_eq_top_of_disjoint
  intro z hz
  change z ∈ coordinatePoint (k := k) ⁻¹ᵁ chartOpen k 1 at hz
  rw [coordinatePoint_preimage_right] at hz
  exact hz

/-- The original point ideal has regular generators on an actual affine cover. -/
theorem coordinatePointIdeal_locallyPrincipalRegular :
    IdealLocallyPrincipalRegular (coordinatePointIdeal (k := k)) := by
  intro x
  have hx : x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  rcases hx with hx | hx
  · refine ⟨firstAffineOpen, ?_, firstSection, firstSection_ideal, firstSection_regular⟩
    simpa only [firstAffineOpen, firstOpen_eq] using hx
  · exact ⟨coordinateRightAffineOpen, hx, 1,
      by rw [coordinateRightIdeal_eq_top, Ideal.span_singleton_one], Submonoid.one_mem _⟩

/-- The effective Cartier divisor of the original point [1:0], constructed from its ideal. -/
def coordinateCartier : CartierDivisor (projectiveSpace k 1) :=
  cartierDivisorOfIdeal (projectiveSpace k 1) coordinatePointIdeal
    coordinatePointIdeal_locallyPrincipalRegular

/-- Its regular-equation property is derived from the original point's local ideal equations. -/
theorem coordinateCartier_hasRegularEquations :
    HasRegularCartierEquations (projectiveSpace k 1) (coordinateCartier (k := k)) :=
  cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- The constructed divisor retains exactly the original point ideal-sheaf data. -/
theorem coordinateCartier_idealData :
    effectiveCartierIdealDataOfRegularEquations (projectiveSpace k 1) coordinateCartier
      coordinateCartier_hasRegularEquations = coordinatePointIdeal (k := k) :=
  cartierDivisorOfIdeal_idealData _ _ _

/-- The first principal regular chart retains the original ambient coordinate section. -/
def coordinateFirstPrincipalChart :
    PrincipalRegularChart (projectiveSpace k 1) (coordinatePointIdeal (k := k)) where
  openSet := firstAffineOpen
  nonempty := ⟨⟨(rulingProjection (k := k) 0).base (genericPoint (projectiveProduct k)),
    by change _ ∈ firstOpen (k := k)
       rw [firstOpen_eq]
       exact rulingGeneric_mem 0 0⟩⟩
  generator := firstSection
  span_eq := firstSection_ideal
  regular := firstSection_regular

/-- The other principal regular chart has the actual unit equation. -/
def coordinateRightPrincipalChart :
    PrincipalRegularChart (projectiveSpace k 1) (coordinatePointIdeal (k := k)) where
  openSet := coordinateRightAffineOpen
  nonempty := ⟨⟨(rulingProjection (k := k) 0).base (genericPoint (projectiveProduct k)),
    rulingGeneric_mem 0 1⟩⟩
  generator := 1
  span_eq := by rw [coordinateRightIdeal_eq_top, Ideal.span_singleton_one]
  regular := Submonoid.one_mem _

/-- The original first generator gives a regular chart of the constructed divisor. -/
def coordinateFirstRegularChart :
    RegularCartierEquationChart (projectiveSpace k 1) (coordinateCartier (k := k)) :=
  cartierDivisorOfIdeal_regularChart _ _ _ coordinateFirstPrincipalChart

/-- The original unit generator gives the other regular chart. -/
def coordinateRightRegularChart :
    RegularCartierEquationChart (projectiveSpace k 1) (coordinateCartier (k := k)) :=
  cartierDivisorOfIdeal_regularChart _ _ _ coordinateRightPrincipalChart

/-- The negative Cartier sheaf is the original point kernel, through the actual image comparison. -/
def coordinateCartierKernelIso :
    cartierDivisorModule (projectiveSpace k 1) (-coordinateCartier (k := k)) ≅
      (coordinateIdealLine (k := k)).obj :=
  cartierDivisorOfIdeal_kernelIso (projectiveSpace k 1) coordinatePointIdeal
      coordinatePointIdeal_locallyPrincipalRegular ≪≫
    (schemeKernelPrecompIso (toImageIso (coordinatePoint (k := k)))
      (SchematicImageGlued.inclusion (coordinatePoint (k := k)))).symm ≪≫
    schemeKernelIdealEqIso (toImageIso_hom_inclusion (coordinatePoint (k := k)))

/-- The original point ideal has the class of the negative constructed Cartier divisor. -/
theorem coordinateIdealLine_toPic :
    (coordinateIdealLine (k := k)).toPic =
      cartierPicardClass (projectiveSpace k 1) (-coordinateCartier (k := k)) := by
  letI := Scheme.Modules.monoidalCategory (projectiveSpace k 1)
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, cartierPicardClass_val]
  exact Quotient.sound ⟨(coordinateCartierKernelIso (k := k)).symm⟩

/-- The effective point's Cartier class is the inverse original point-ideal class. -/
theorem coordinateCartier_picard :
    cartierPicardHom (projectiveSpace k 1) (coordinateCartier (k := k)) =
      -Additive.ofMul (coordinateIdealLine (k := k)).toPic := by
  rw [coordinateIdealLine_toPic, cartierPicardClass_neg, ofMul_inv, neg_neg]
  rfl

end KltDP.Examples.FrobeniusInitialCanonicalFiberPoint
