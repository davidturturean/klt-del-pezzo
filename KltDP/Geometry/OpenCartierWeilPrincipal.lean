import KltDP.Geometry.OpenCartierWeil
import KltDP.Geometry.WeilClassGroup

/-!
# Principal divisors extended from an open containing all prime generic points

The existing Cartier-to-Weil extension preserves the actual rational function
transported along the original open immersion. Consequently, Cartier divisors
whose difference is principal give linearly equivalent divisors on the surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OpenCartierWeil

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
variable (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance : Nonempty V := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- Extension of a principal Cartier divisor uses the same actual rational
function under the original function-field isomorphism of the open immersion. -/
theorem restrictedWeilHom_principal
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V)
    (f : V.toScheme.functionFieldˣ) :
    restrictedWeilHom V (principalCartierDivisorHom V.toScheme (Additive.ofMul f)) =
      X.principalDivisor (transportUnit V f) := by
  apply Finsupp.ext
  intro C
  change restrictedCoefficient V _ C = C.order (transportUnit V f)
  have hmem : C.genericPoint ∈ V.ι ''ᵁ (⊤ : V.toScheme.Opens) :=
    (Scheme.Hom.map_mem_image_iff V.ι (U := ⊤)
      (x := (⟨C.genericPoint, hV C⟩ : V.toScheme))).mpr trivial
  apply restrictedCoefficient_eq_of_equation V _ C ⊤ hmem f
  have hi : (homOfLE (show (⊤ : V.toScheme.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : V.toScheme.Opens)) := Subsingleton.elim _ _
  rw [hi]
  exact (ConcreteCategory.congr_hom
    ((cartierDivisorSheaf V.toScheme).val.map_id (op (⊤ : V.toScheme.Opens)))
    (principalCartierDivisorHom V.toScheme (Additive.ofMul f))).symm

/-- A principal difference on the same large open extends to a principal
difference on the original surface, with its explicit function witness. -/
theorem restrictedWeilHom_sub_of_principal
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V)
    (D E : CartierDivisor V.toScheme) (f : V.toScheme.functionFieldˣ)
    (hDE : D - E = principalCartierDivisorHom V.toScheme (Additive.ofMul f)) :
    restrictedWeilHom V D - restrictedWeilHom V E =
      X.principalDivisor (transportUnit V f) := by
  rw [← map_sub, hDE, restrictedWeilHom_principal V hV f]

theorem restrictedWeilHom_linearlyEquivalent_of_principal
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V)
    (D E : CartierDivisor V.toScheme) (f : V.toScheme.functionFieldˣ)
    (hDE : D - E = principalCartierDivisorHom V.toScheme (Additive.ofMul f)) :
    X.LinearlyEquivalent (restrictedWeilHom V D) (restrictedWeilHom V E) :=
  ⟨transportUnit V f, restrictedWeilHom_sub_of_principal V hV D E f hDE⟩

end KltDP.Geometry.OpenCartierWeil
