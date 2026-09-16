import KltDP.Geometry.SurfaceEulerSections
import KltDP.Geometry.SectionEffectiveWeil

/-!
# Effective integral divisors from the original surface Euler bound

The actual cohomology Euler inequality and H2 vanishing first produce a
nonzero section of the original O(D). Its original rational value then
supplies an effective finite Weil divisor in the original linear-equivalence
class. Both steps use the existing constructions and the same scheme.

Finiteness, positive Euler characteristic and H2 vanishing are explicit
cohomological hypotheses. This file proves their consequence; it does not
assert Riemann--Roch, Serre duality, or the hypotheses of an adjoint theorem.
The Cartier statement holds over an arbitrary field. The final Weil
statement uses the existing regular-surface Cartier representative.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open ModuleCohomology

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original Cartier sheaf's genuine Euler and vanishing data give an
effective integral representative, with the original principal relation. -/
theorem exists_effectiveWeil_of_cartier_euler_pos
    (D : CartierDivisor X.toScheme)
    (hfinite : ∀ i, FiniteDimensional k
      ((baseFunctor X.structureMorphism i).obj (cartierDivisorModule X.toScheme D)))
    (h₂ : Subsingleton (H (cartierDivisorModule X.toScheme D) 2))
    (hχ : 0 < eulerCharacteristic X.structureMorphism
      (cartierDivisorModule X.toScheme D)) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧
      X.LinearlyEquivalent Z (X.cartierToWeilHom D) := by
  obtain ⟨s, hs⟩ := normalProjectiveSurface_exists_nonzero_section_of_euler_pos
    X (cartierDivisorModule X.toScheme D) hfinite h₂ hχ
  exact X.exists_effectiveWeil_of_nonzero_cartier_section D s hs

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The conclusion concerns the original Weil divisor, not a numerical
class or a replacement surface. The output has the existing finite support. -/
theorem exists_effectiveWeil_of_euler_pos
    (D : X.WeilDivisor)
    (hfinite : ∀ i, FiniteDimensional k
      ((baseFunctor X.structureMorphism i).obj
        (cartierDivisorModule X.toScheme ((X.regularCartierWeilEquiv hregular).symm D))))
    (h₂ : Subsingleton
      (H (cartierDivisorModule X.toScheme ((X.regularCartierWeilEquiv hregular).symm D)) 2))
    (hχ : 0 < eulerCharacteristic X.structureMorphism
      (cartierDivisorModule X.toScheme ((X.regularCartierWeilEquiv hregular).symm D))) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D := by
  obtain ⟨s, hs⟩ := normalProjectiveSurface_exists_nonzero_section_of_euler_pos
    X (cartierDivisorModule X.toScheme ((X.regularCartierWeilEquiv hregular).symm D))
    hfinite h₂ hχ
  exact X.exists_effectiveWeil_of_nonzero_section hregular D s hs

end Regular

end KltDP.Geometry.NormalProjectiveSurface
