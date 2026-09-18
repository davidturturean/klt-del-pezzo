import KltDP.Geometry.SchematicBirationalComparison
import KltDP.Geometry.SchematicImageGenericPoint
import KltDP.Geometry.BirationalOpenSquare

/-!
# Birationality from an original matrix-domain triangle

The matrix domain cuts out an actual nonempty open of the original
schematic image. The original image factor lifts to that open. The given
two original map equations derive its open/closed immersion triangle;
the proved generic-point and birational-composition results then transfer
birationality to the original whole image factor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageMatrixTriangle

variable {X T U P Z : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral U]
  (q : T ⟶ P) [QuasiCompact q] (v : U ⟶ T) [IsOpenImmersion v]
  (j : U ⟶ X) [IsOpenImmersion j] (i : X ⟶ Z) [IsClosedImmersion i]
  (D : P.Opens) (w : U ⟶ D.toScheme) (p : D.toScheme ⟶ Z)

local instance actual_image_integral : IsIntegral (SchematicImageGlued.image q) :=
  SchematicImageIntegral.image_isIntegral q

/-- The actual image factor is birational whenever the original matrix-domain
triangle recovers an original closed embedding on a nonempty original open. -/
theorem toImage_isBirationalScheme
    (hq : w ≫ D.ι = v ≫ q) (hi : w ≫ p = j ≫ i) :
    IsBirationalScheme (SchematicImageGlued.toImage q) := by
  let Y := SchematicImageGlued.image q
  let c := SchematicImageGlued.inclusion q
  let a₀ := SchematicImageGlued.toImage q
  letI : IsIntegral Y := SchematicImageIntegral.image_isIntegral q
  let V : Y.Opens := c ⁻¹ᵁ D
  have hfactor : (v ≫ a₀) ≫ c = w ≫ D.ι := by
    rw [Category.assoc, SchematicImageGlued.toImage_inclusion]
    exact hq.symm
  have hrange : Set.range (v ≫ a₀).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change ((v ≫ a₀) ≫ c).base x ∈ D
    rw [hfactor]
    exact (w.base x).property
  let a : U ⟶ V.toScheme := IsOpenImmersion.lift V.ι (v ≫ a₀) hrange
  have ha : a ≫ V.ι = v ≫ a₀ := IsOpenImmersion.lift_fac _ _ _
  letI : Nonempty V := Nonempty.map a.base inferInstance
  letI : IsIntegral V.toScheme := inferInstance
  let cD : V.toScheme ⟶ D.toScheme := c ∣_ D
  have hw : a ≫ cD = w := by
    apply (cancel_mono D.ι).mp
    calc
      (a ≫ cD) ≫ D.ι = a ≫ (cD ≫ D.ι) := Category.assoc _ _ _
      _ = a ≫ (V.ι ≫ c) := congrArg (fun z => a ≫ z) (morphismRestrict_ι c D)
      _ = (a ≫ V.ι) ≫ c := (Category.assoc _ _ _).symm
      _ = (v ≫ a₀) ≫ c := congrArg (fun z => z ≫ c) ha
      _ = w ≫ D.ι := hfactor
  letI : GenericPointPreserving a₀ := SchematicImageIntegral.toImage_genericPointPreserving q
  letI : GenericPointPreserving a :=
    BirationalOpenSquare.genericPointPreserving a₀ v V.ι a ha
  have htriangle : a ≫ (cD ≫ p) = j ≫ i := by
    rw [← Category.assoc, hw]
    exact hi
  have hab := SchematicBirationalComparison.isBirationalScheme_of_open_closed_triangle
    a (cD ≫ p) j i htriangle
  exact (BirationalOpenSquare.isBirationalScheme_iff a₀ v V.ι a ha).mp hab

end KltDP.Geometry.SchematicImageMatrixTriangle
