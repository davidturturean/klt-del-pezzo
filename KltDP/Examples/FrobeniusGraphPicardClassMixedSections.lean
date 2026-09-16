import KltDP.Examples.FrobeniusGraphPicardClassMixedCoordinates

/-!
# The mixed graph equation as an equality of original regular sections

The actual chart-section isomorphism transports 1-u^p*v and v to the
original mixed image open. Restriction to its overlap with the matching
diagonal gives h=v*g_ii as an equality in that original open's section
ring. Injectivity of the original generic-point germ transfers the proved
function-field identity; it does not replace the original section rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassMixedSections

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRational
open FrobeniusGraphPicardClassMixedBasicOpens FrobeniusGraphPicardClassMixedCoordinates

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The actual original mixed image carries this transported regular polynomial. -/
def mixedAmbientEquation (p : ℕ) (i : Fin 2) :
    Γ(projectiveProduct k, productOpen i (otherIndex i)) :=
  ((productChart i (otherIndex i)).appIso ⊤).inv (mixedEquation p)

/-- The original outer coordinate on that same image open. -/
def mixedAmbientOuter (i : Fin 2) : Γ(projectiveProduct k, productOpen i (otherIndex i)) :=
  ((productChart i (otherIndex i)).appIso ⊤).inv outerSection

def mixedDiagonalOverlap (i : Fin 2) : (projectiveProduct k).Opens :=
  productOpen i (otherIndex i) ⊓ diagonalOpen i

instance mixedDiagonalOverlap_nonempty (i : Fin 2) :
    Nonempty (mixedDiagonalOverlap (k := k) i) :=
  ⟨⟨genericPoint (projectiveProduct k),
    genericPoint_mem_nonempty_open (projectiveProduct k) (productOpen i (otherIndex i)),
    genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen i)⟩⟩

/-- The mixed equation is the original diagonal equation times the actual outer coordinate,
as an equality of regular sections on the actual overlap. -/
theorem mixed_equation_regular_factor (p : ℕ) (i : Fin 2) :
    (projectiveProduct k).presheaf.map
        (homOfLE (show mixedDiagonalOverlap i ≤ productOpen i (otherIndex i)
          from inf_le_left)).op (mixedAmbientEquation p i) =
      (projectiveProduct k).presheaf.map
          (homOfLE (show mixedDiagonalOverlap i ≤ productOpen i (otherIndex i)
            from inf_le_left)).op (mixedAmbientOuter i) *
        (projectiveProduct k).presheaf.map
          (homOfLE (show mixedDiagonalOverlap i ≤ diagonalOpen i
            from inf_le_right)).op (diagonalSection p i) := by
  apply (projectiveProduct k).germToFunctionField_injective (mixedDiagonalOverlap i)
  rw [map_mul, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  simp only [mixedAmbientEquation, mixedEquation_polynomial, mixedAmbientOuter]
  change productFunctionFieldMap i (otherIndex i) (1 - uCoord ^ p * vCoord) =
    productFunctionFieldMap i (otherIndex i) vCoord *
      chartFunctionFieldMap i (vCoord - uCoord ^ p)
  exact mixed_equation_factor p i

end KltDP.Examples.FrobeniusGraphPicardClassMixedSections
