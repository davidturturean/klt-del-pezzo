import KltDP.Examples.FrobeniusGraphPicardClassEquationTransition
import KltDP.Geometry.CartierEquationUnits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual Cartier divisors of the two infinity rulings

Each original projection gives a two-open cover. The local equations are
1 on the finite-coordinate open and the reciprocal coordinate on the
other open. The actual overlap coordinate unit proves compatibility in
the Cartier quotient sheaf; the existing sheaf gluing theorem constructs
the global divisors. No ruling divisor or gluing equation is assumed.

Their Picard comparison with the pulled-back point ideal and the graph
ideal remains separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors

open KltDP.Geometry ProjectiveLineComparison ProjectiveLineSections
open FrobeniusProjectivePoints FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRulingCoordinates

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def rulingOpen (d i : Fin 2) : (projectiveProduct k).Opens :=
  rulingProjection d ⁻¹ᵁ chartOpen k i

instance rulingOpen_nonempty (d i : Fin 2) : Nonempty (rulingOpen (k := k) d i) :=
  ⟨⟨genericPoint (projectiveProduct k), rulingGeneric_mem d i⟩⟩

theorem rulingOpen_cover (d : Fin 2) : (⨆ i : Fin 2, rulingOpen (k := k) d i) = ⊤ := by
  apply top_unique
  intro x _
  have hx : (rulingProjection d).base x ∈ chartOpen k 0 ⊔ chartOpen k 1 := by
    rw [chartOpen_sup]
    trivial
  rcases hx with hx | hx
  · exact Opens.mem_iSup.mpr ⟨0, hx⟩
  · exact Opens.mem_iSup.mpr ⟨1, hx⟩

instance rulingOpen_inter_nonempty (d i j : Fin 2) :
    Nonempty (rulingOpen (k := k) d i ⊓ rulingOpen d j : (projectiveProduct k).Opens) :=
  ⟨⟨genericPoint (projectiveProduct k), rulingGeneric_mem d i, rulingGeneric_mem d j⟩⟩

def rulingOverlap (d : Fin 2) : (projectiveProduct k).Opens :=
  rulingOpen d 0 ⊓ rulingOpen d 1

instance rulingOverlap_nonempty (d : Fin 2) : Nonempty (rulingOverlap (k := k) d) :=
  rulingOpen_inter_nonempty d 0 1

theorem rulingOverlap_le (d : Fin 2) :
    rulingOverlap (k := k) d ≤ rulingProjection d ⁻¹ᵁ overlapOpen k := by
  intro x hx
  change (rulingProjection d).base x ∈ overlapOpen k
  rw [overlapOpen_eq_inf]
  exact hx

/-- The original projective-line overlap unit, retaining both coordinate sections. -/
def lineOverlapCoordinateUnit : Γ(projectiveSpace k 1, overlapOpen k)ˣ where
  val := restrictLeft k leftCoordinateSection
  inv := restrictRight k rightCoordinateSection
  val_inv := restricted_coordinates_mul
  inv_val := by rw [mul_comm]; exact restricted_coordinates_mul

/-- The actual unit pulled back to the overlap of a product ruling. -/
def rulingOverlapCoordinateUnit (d : Fin 2) : Γ(projectiveProduct k, rulingOverlap d)ˣ :=
  Units.map ((rulingProjection d).appLE (overlapOpen k) (rulingOverlap d)
    (rulingOverlap_le d)).hom.toMonoidHom lineOverlapCoordinateUnit

/-- Its rational image is the previously constructed original ruling-coordinate unit. -/
theorem rulingOverlapCoordinateUnit_image (d : Fin 2) :
    Units.map ((projectiveProduct k).germToFunctionField (rulingOverlap d)).hom.toMonoidHom
      (rulingOverlapCoordinateUnit (k := k) d) = rulingCoordinateUnit d := by
  apply Units.ext
  change (projectiveProduct k).germToFunctionField (rulingOverlap d)
      ((rulingProjection d).appLE (overlapOpen k) (rulingOverlap d) _
        (restrictLeft k leftCoordinateSection)) = rulingLeft d
  simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply, Scheme.germToFunctionField,
    TopCat.Presheaf.germ_res_apply]
  rw [← Scheme.stalkMap_germ_apply]
  simp only [restrictLeft, TopCat.Presheaf.germ_res_apply, rulingLeft]

/-- The reciprocal equation is a regular unit on every common subopen. -/
theorem reciprocal_cartier_class_zero (d : Fin 2) (V : (projectiveProduct k).Opens)
    [Nonempty V] (h₀ : V ≤ rulingOpen d 0) (h₁ : V ≤ rulingOpen d 1) :
    cartierEquationClassHom (projectiveProduct k) V
      (Additive.ofMul ((rulingCoordinateUnit (k := k) d)⁻¹)) = 0 := by
  have hV : V ≤ rulingOverlap d := le_inf h₀ h₁
  let a : Γ(projectiveProduct k, V)ˣ :=
    Units.map ((projectiveProduct k).presheaf.map (homOfLE hV).op).hom.toMonoidHom
      (rulingOverlapCoordinateUnit d)
  have ha : Units.map ((projectiveProduct k).germToFunctionField V).hom.toMonoidHom a =
      rulingCoordinateUnit d :=
    (germToFunctionField_map_unit_restriction (projectiveProduct k) hV
      (rulingOverlapCoordinateUnit d)).trans (rulingOverlapCoordinateUnit_image d)
  have h := cartierEquationClassHom_map_regular_unit (projectiveProduct k) V (a⁻¹)
  simpa only [map_inv, ha] using h

/-- Local rational equations of the actual infinity fiber of a projection. -/
def rulingInfinityEquation (d i : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  if i = 0 then 1 else (rulingCoordinateUnit d)⁻¹

/-- These two equations define compatible sections of the actual Cartier sheaf. -/
theorem rulingInfinity_equations_compatible (d : Fin 2) :
    TopCat.Presheaf.IsCompatible (cartierDivisorSheaf (projectiveProduct k)).val
      (rulingOpen d)
      (fun i => cartierEquationClassHom (projectiveProduct k) (rulingOpen d i)
        (Additive.ofMul (rulingInfinityEquation d i))) := by
  intro i j
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen d i ⊓ rulingOpen d j ≤ rulingOpen d i from inf_le_left)).op
      (cartierEquationClassHom (projectiveProduct k) (rulingOpen d i)
        (Additive.ofMul (rulingInfinityEquation d i))) =
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen d i ⊓ rulingOpen d j ≤ rulingOpen d j from inf_le_right)).op
      (cartierEquationClassHom (projectiveProduct k) (rulingOpen d j)
        (Additive.ofMul (rulingInfinityEquation d j)))
  rw [cartierEquationClassHom_restrict, cartierEquationClassHom_restrict]
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [rulingInfinityEquation] using
      (reciprocal_cartier_class_zero (k := k) d
        (rulingOpen d 0 ⊓ rulingOpen d 1) inf_le_left inf_le_right).symm
  · simpa [rulingInfinityEquation] using
      reciprocal_cartier_class_zero (k := k) d
        (rulingOpen d 1 ⊓ rulingOpen d 0) inf_le_right inf_le_left
  · rfl

/-- Sheaf gluing supplies the global divisor with exactly those restrictions. -/
theorem exists_rulingInfinityDivisor (d : Fin 2) :
    ∃ D : CartierDivisor (projectiveProduct k), ∀ i : Fin 2,
      (cartierDivisorSheaf (projectiveProduct k)).val.map
          (homOfLE (show rulingOpen d i ≤ ⊤ from le_top)).op D =
        cartierEquationClassHom (projectiveProduct k) (rulingOpen d i)
          (Additive.ofMul (rulingInfinityEquation d i)) := by
  obtain ⟨D, hD, -⟩ := (cartierDivisorSheaf (projectiveProduct k)).existsUnique_gluing'
    (rulingOpen d) ⊤ (fun i => homOfLE (show rulingOpen d i ≤ ⊤ from le_top))
    (rulingOpen_cover (k := k) d).ge
    (fun i => cartierEquationClassHom (projectiveProduct k) (rulingOpen d i)
      (Additive.ofMul (rulingInfinityEquation d i))) (rulingInfinity_equations_compatible d)
  exact ⟨D, hD⟩

/-- A constructed Cartier divisor of the original infinity ruling. -/
def rulingInfinityDivisor (d : Fin 2) : CartierDivisor (projectiveProduct k) :=
  (exists_rulingInfinityDivisor (k := k) d).choose

theorem rulingInfinityDivisor_restrict (d i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen d i ≤ ⊤ from le_top)).op (rulingInfinityDivisor d) =
      cartierEquationClassHom (projectiveProduct k) (rulingOpen d i)
        (Additive.ofMul (rulingInfinityEquation (k := k) d i)) :=
  (exists_rulingInfinityDivisor (k := k) d).choose_spec i

end KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors
