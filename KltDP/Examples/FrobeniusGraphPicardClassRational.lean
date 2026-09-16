import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Geometry.CartierPicardHom

/-!
# The actual rational graph equation on the original product

The actual polynomial chart, its section isomorphism, and the original
generic-point germ embed the chart ring in the product's function field.
In these coordinates the nonzero rational function is exactly y-x^p.
Its first-chart germ is that of the already constructed original graph
kernel equation. Its actual principal Cartier divisor has trivial Picard
class by the existing proved principal-module isomorphism.

Identifying that principal divisor with the graph minus the two ruling
divisors remains a separate equality of actual Cartier divisors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRational

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

instance diagonalOpen_nonempty (i : Fin 2) : Nonempty (diagonalOpen (k := k) i) := by
  let q : Spec (CommRingCat.of (planeRing k)) := Nonempty.some inferInstance
  refine ⟨⟨(productChart i i).base q, ?_⟩⟩
  rw [diagonalOpen, Scheme.Hom.image_top_eq_opensRange]
  exact ⟨q, rfl⟩

/-- The original chart's coordinates embedded by its actual generic-point germ. -/
def chartFunctionFieldMap (i : Fin 2) : planeRing k →+* (projectiveProduct k).functionField :=
  ((projectiveProduct k).germToFunctionField (diagonalOpen i)).hom.comp
    (((productChart i i).appIso ⊤).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom)

/-- The map is an embedding, since both section comparisons are isomorphisms. -/
theorem chartFunctionFieldMap_injective (i : Fin 2) :
    Function.Injective (chartFunctionFieldMap (k := k) i) :=
  ((projectiveProduct k).germToFunctionField_injective (diagonalOpen i)).comp
    (((productChart i i).appIso ⊤).symm.commRingCatIsoToRingEquiv.injective.comp
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.injective)

/-- The two affine coordinate functions are actual functions on the original surface. -/
def rationalX : (projectiveProduct k).functionField := chartFunctionFieldMap 0 uCoord

def rationalY : (projectiveProduct k).functionField := chartFunctionFieldMap 0 vCoord

/-- The rational function comes from the original monomial graph equation. -/
def graphFunction (p : ℕ) : (projectiveProduct k).functionField :=
  chartFunctionFieldMap 0 (vCoord - uCoord ^ p)

theorem graphFunction_eq_coordinates (p : ℕ) :
    graphFunction (k := k) p = rationalY - rationalX ^ p := by
  simp only [graphFunction, map_sub, map_pow, rationalX, rationalY]

/-- This is the germ of the equation of the original graph ideal, with no scale change. -/
theorem graphFunction_eq_original_section (p : ℕ) :
    graphFunction (k := k) p =
      (projectiveProduct k).germToFunctionField (diagonalOpen 0) (diagonalSection p 0) := rfl

/-- Nonvanishing is derived from the actual chart embedding and monic polynomial. -/
theorem graphFunction_ne_zero (p : ℕ) : graphFunction (k := k) p ≠ 0 := by
  intro h
  have hpoly : (vCoord - uCoord ^ p : planeRing k) ≠ 0 := by
    simpa only [uCoord, vCoord, ← map_pow] using
      (Polynomial.monic_X_sub_C (Polynomial.X ^ p : Polynomial k)).ne_zero
  apply hpoly
  apply chartFunctionFieldMap_injective 0
  simpa only [map_zero] using h

/-- The nonzero original graph function is a rational unit, as required for Cartier divisors. -/
def graphFunctionUnit (p : ℕ) : (projectiveProduct k).functionFieldˣ :=
  Units.mk0 (graphFunction p) (graphFunction_ne_zero p)

def graphPrincipalDivisor (p : ℕ) : CartierDivisor (projectiveProduct k) :=
  principalCartierDivisorHom (projectiveProduct k) (Additive.ofMul (graphFunctionUnit p))

/-- Existing actual principal triviality applies to this particular constructed function. -/
theorem graphPrincipalDivisor_picard (p : ℕ) :
    cartierPicardHom (projectiveProduct k) (graphPrincipalDivisor (k := k) p) = 0 :=
  cartierPicardHom_principal (projectiveProduct k) (Additive.ofMul (graphFunctionUnit p))

end KltDP.Examples.FrobeniusGraphPicardClassRational
