import KltDP.Geometry.BirationalCartierModuleIso
import KltDP.Geometry.CanonicalExteriorOnIsomorphismOpen
import KltDP.Geometry.SmoothOpenCanonicalWeil

/-!
# Canonical Weil classes under the original birational morphism

Both canonical representatives are constructed independently from the actual
exterior square of differentials. The original differential comparison on the
isomorphism open supplies the divisor-module isomorphism, and the proved
Cartier-to-Weil comparison then identifies the pushforward class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalWeilBirational

variable {k : Type u} [Field k] (S Y : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (π : S.toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = S.structureMorphism)
    (U : Y.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)]
    [IsSmoothOfRelativeDimension 2 (U.ι ≫ Y.structureMorphism)]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The canonical divisor-module comparison is constructed from the original
differential maps, rather than supplied as a birational compatibility premise. -/
def canonicalDivisorModuleIso :
    (schemeModulePullback (π ⁻¹ᵁ U).ι).obj
        (cartierDivisorModule S.toScheme
          (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism)) ≅
      (schemeModulePullback (π ∣_ U)).obj
        (cartierDivisorModule U.toScheme (SmoothOpenCanonicalWeil.cartierRepresentative Y U)) :=
  (schemeModulePullback (π ⁻¹ᵁ U).ι).mapIso
      (SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism) ≪≫
    (CanonicalExteriorOnIsomorphismOpen.pullbackIso
      S.structureMorphism Y.structureMorphism π hπ U 2).symm ≪≫
    ((schemeModulePullback (π ∣_ U)).mapIso
      (SmoothOpenCanonicalWeil.representativeIsoExterior Y U)).symm

include hπ in
/-- Pushforward of the actual source canonical class equals the canonical
class constructed from the target's smooth open containing every prime generic point. -/
theorem pushforward_canonical_weilClass [IsProper π]
    (hbir : IsBirationalScheme π)
    (hU : ∀ C : Y.PrimeCurve, C.genericPoint ∈ U) :
    BirationalWeilClassPushforward.pushforward π hbir
        (S.weilClassMap
          (SmoothCanonicalCartierRepresentative.weilRepresentative S)) =
      Y.weilClassMap (SmoothOpenCanonicalWeil.weilRepresentative Y U) := by
  exact BirationalCartierOnIsomorphismOpen.pushforward_weilClass_of_pullback_module_iso
    π hbir U hU
    (SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism)
    (SmoothOpenCanonicalWeil.cartierRepresentative Y U)
    (canonicalDivisorModuleIso S Y π hπ U)

end KltDP.Geometry.CanonicalWeilBirational
