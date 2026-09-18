import KltDP.Geometry.SemiampleActualPowers
import KltDP.Geometry.LinearSystemNonvanishingPreimage

/-!
# The projective map of an actual positive tensor power

Semiampleness on a quasi-compact scheme constructs a finite linear system
of an actual positive tensor power. The already proved chart construction
then gives its original field-linear projective morphism. Its coordinate
chart preimages are the nonvanishing opens of these same sections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- Actual finite section data of a positive tensor power. This data is
constructed from semiampleness below. -/
structure PowerSystem where
  exponent : ℕ
  positive : 0 < exponent
  dimension : ℕ
  sections : Fin (dimension + 1) → (power L exponent).obj.sections
  covers : (⨆ j, nonvanishingOpen X (power L exponent) (sections j)) = ⊤

/-- The original semiampleness witness produces the actual finite power system. -/
def powerSystem (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsSemiample L) :
    PowerSystem L :=
  Classical.choice (show Nonempty (PowerSystem L) from by
    obtain ⟨m, hm, n, s, hs⟩ := SemiampleActualPowers.exists_actual_power_tuple L hX hL
    exact ⟨⟨m, hm, n, s, hs⟩⟩)

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The original projective map defined by the actual tensor-power sections. -/
def PowerSystem.toProjective (D : PowerSystem L) : X ⟶ projectiveSpace k D.dimension :=
  LinearSystemMorphism.morphism (power L D.exponent) D.sections f D.covers

/-- This actual map preserves the original field structure. -/
theorem PowerSystem.toProjective_structure (D : PowerSystem L) :
    PowerSystem.toProjective L f D ≫ projectiveSpaceToSpec k D.dimension = f :=
  LinearSystemMorphism.morphism_structure (power L D.exponent) D.sections f D.covers

/-- The actual coordinate charts pull back to the same original power-section opens. -/
theorem PowerSystem.toProjective_preimage_coordinateChart (D : PowerSystem L)
    (j : Fin (D.dimension + 1)) :
    PowerSystem.toProjective L f D ⁻¹ᵁ
        (ProjectiveChart.coordinateChartMorphism k D.dimension j).opensRange =
      nonvanishingOpen X (power L D.exponent) (D.sections j) :=
  LinearSystemMorphism.morphism_preimage_coordinateChart
    (power L D.exponent) D.sections f D.covers j

end KltDP.Geometry.SemiampleProjectiveMap
