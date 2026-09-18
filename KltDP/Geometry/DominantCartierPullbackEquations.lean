import KltDP.Geometry.DominantCartierPullback
import KltDP.Geometry.CartierDivisorTrivialization

/-!
Actual global Cartier equations transport through the signed pullback by
naturality of its original sheaf map. The inverse images of the existing
equation charts cover the source, giving a local test for equality. These
are bounded adaptations of CartierOpenRestrictionEquations; no global
rational equation or effective-divisor hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

variable {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
variable (π : X ⟶ Y) [GenericPointPreserving π]

/-- An equation for the original global divisor gives the actual pulled
equation on its inverse-image open. -/
theorem pullbackHom_globalEquation_preimage (D : CartierDivisor Y)
    (U : Y.Opens) [Nonempty U] (g : Y.functionFieldˣ)
    (hg : cartierEquationClassHom Y U (Additive.ofMul g) =
      (cartierDivisorSheaf Y).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    cartierEquationClassHom X (π ⁻¹ᵁ U)
        (Additive.ofMul (Units.map (functionFieldMap π).hom.toMonoidHom g)) =
      (cartierDivisorSheaf X).val.map
        (homOfLE (show π ⁻¹ᵁ U ≤ ⊤ from le_top)).op (pullbackHom π D) := by
  calc
    _ = (cartierPullback π).val.app (op U)
        (cartierEquationClassHom Y U (Additive.ofMul g)) :=
      (cartierPullback_equation π U g).symm
    _ = (cartierPullback π).val.app (op U)
        ((cartierDivisorSheaf Y).val.map
          (homOfLE (show U ≤ ⊤ from le_top)).op D) := congrArg _ hg
    _ = _ := NatTrans.naturality_apply (cartierPullback π).val
      (homOfLE (show U ≤ ⊤ from le_top)).op D

/-- The original equation charts of any signed Cartier divisor cover
the source after taking inverse images. -/
theorem preimageEquationCharts_cover (D : CartierDivisor Y) :
    (⊤ : X.Opens) ≤ iSup (fun c : CartierEquationChart Y D => π ⁻¹ᵁ c.openSet) := by
  intro x _
  obtain ⟨W, i, hW, hxW⟩ :=
    cartierEquationCharts_coversTop Y D ⊤ (π.base x) trivial
  obtain ⟨c, ⟨j⟩⟩ := hW
  exact Opens.mem_iSup.mpr ⟨c, j.le hxW⟩

end KltDP.Geometry.DominantCartierPullback
