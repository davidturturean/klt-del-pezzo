import KltDP.Examples.FrobeniusGraphPicardClassRational
import KltDP.Geometry.ProjectiveLineSections

/-!
# Reciprocal ruling coordinates in the original product function field

The two product projections and their actual maps of local rings send the
original projective-line coordinate sections to the function field of the
original surface. Their reciprocal relation follows from the existing
restriction maps on the actual projective-line overlap. No rational
coordinate identity is assumed.

These functions provide local equations for the ruling-divisor comparison.
The identification with the polynomial-plane chart coordinates and the
graph-minus-rulings equality are subsequent comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates

open KltDP.Geometry ProjectiveLineComparison ProjectiveLineSections
open FrobeniusProjectivePoints FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The two original scheme projections, indexed only to share the proof. -/
def rulingProjection (d : Fin 2) : projectiveProduct k ⟶ projectiveSpace k 1 :=
  if d = 0 then pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)
  else pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

/-- The original generic point lies over both standard opens of either ruling. -/
theorem rulingGeneric_mem (d i : Fin 2) :
    (rulingProjection (k := k) d).base (genericPoint (projectiveProduct k)) ∈
      chartOpen k i := by
  have h := genericPoint_mem_nonempty_open (projectiveProduct k) (diagonalOpen i)
  rw [diagonalOpen, Scheme.Hom.image_top_eq_opensRange] at h
  change genericPoint (projectiveProduct k) ∈ Set.range (productChart i i).base at h
  rw [productChart_range] at h
  fin_cases d
  · simpa [rulingProjection] using h.1
  · simpa [rulingProjection] using h.2

/-- The original coordinate section on the first standard projective open. -/
def leftCoordinateSection : Γ(projectiveSpace k 1, chartOpen k 0) :=
  (leftSectionsEquiv k).symm Polynomial.X

/-- The original reciprocal section on the second standard projective open. -/
def rightCoordinateSection : Γ(projectiveSpace k 1, chartOpen k 1) :=
  (rightSectionsEquiv k).symm Polynomial.X

/-- Reciprocality holds in the actual overlap section ring. -/
theorem restricted_coordinates_mul :
    restrictLeft k (leftCoordinateSection (k := k)) *
      restrictRight k (rightCoordinateSection (k := k)) = 1 := by
  apply (overlapSectionsEquiv k).injective
  simp only [map_mul, map_one, overlapSectionsEquiv_restrictLeft,
    overlapSectionsEquiv_restrictRight, leftCoordinateSection, rightCoordinateSection,
    RingEquiv.apply_symm_apply, Polynomial.toLaurent_X, Polynomial.aeval_X,
    ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The first ruling coordinate through the actual projection's stalk map. -/
def rulingLeft (d : Fin 2) : (projectiveProduct k).functionField :=
  (rulingProjection d).stalkMap (genericPoint (projectiveProduct k))
    ((projectiveSpace k 1).presheaf.germ (chartOpen k 0)
      ((rulingProjection d).base (genericPoint (projectiveProduct k)))
      (rulingGeneric_mem d 0) leftCoordinateSection)

/-- The reciprocal ruling coordinate through that same original stalk map. -/
def rulingRight (d : Fin 2) : (projectiveProduct k).functionField :=
  (rulingProjection d).stalkMap (genericPoint (projectiveProduct k))
    ((projectiveSpace k 1).presheaf.germ (chartOpen k 1)
      ((rulingProjection d).base (genericPoint (projectiveProduct k)))
      (rulingGeneric_mem d 1) rightCoordinateSection)

/-- The two original rational coordinates are multiplicative inverses. -/
theorem rulingCoordinates_mul (d : Fin 2) :
    rulingLeft (k := k) d * rulingRight d = 1 := by
  let x := (rulingProjection (k := k) d).base (genericPoint (projectiveProduct k))
  have hx : x ∈ overlapOpen k := by
    rw [overlapOpen_eq_inf]
    exact ⟨rulingGeneric_mem d 0, rulingGeneric_mem d 1⟩
  let φ : Γ(projectiveSpace k 1, overlapOpen k) →+*
      (projectiveProduct k).functionField :=
    ((rulingProjection d).stalkMap (genericPoint (projectiveProduct k))).hom.comp
      ((projectiveSpace k 1).presheaf.germ (overlapOpen k) x hx).hom
  have hl : φ (restrictLeft k leftCoordinateSection) = rulingLeft d := by
    exact congrArg
      (fun z => (rulingProjection d).stalkMap (genericPoint (projectiveProduct k)) z)
      (ConcreteCategory.congr_hom
        ((projectiveSpace k 1).presheaf.germ_res
          (homOfLE (overlapOpen_le_left k)) x hx) (leftCoordinateSection (k := k)))
  have hr : φ (restrictRight k rightCoordinateSection) = rulingRight d := by
    exact congrArg
      (fun z => (rulingProjection d).stalkMap (genericPoint (projectiveProduct k)) z)
      (ConcreteCategory.congr_hom
        ((projectiveSpace k 1).presheaf.germ_res
          (homOfLE (overlapOpen_le_right k)) x hx) (rightCoordinateSection (k := k)))
  rw [← hl, ← hr, ← map_mul, restricted_coordinates_mul, map_one]

/-- Nonvanishing follows from the proved actual reciprocal, not a coordinate hypothesis. -/
theorem rulingLeft_ne_zero (d : Fin 2) : rulingLeft (k := k) d ≠ 0 := by
  intro h
  have hm := rulingCoordinates_mul (k := k) d
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

theorem rulingRight_eq_inverse (d : Fin 2) :
    rulingRight (k := k) d = (rulingLeft d)⁻¹ := by
  apply mul_left_cancel₀ (rulingLeft_ne_zero d)
  rw [rulingCoordinates_mul, mul_inv_cancel₀ (rulingLeft_ne_zero d)]

/-- The unit retains the two original chart-section representatives. -/
def rulingCoordinateUnit (d : Fin 2) : (projectiveProduct k).functionFieldˣ where
  val := rulingLeft d
  inv := rulingRight d
  val_inv := rulingCoordinates_mul d
  inv_val := by rw [mul_comm]; exact rulingCoordinates_mul d

end KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates
