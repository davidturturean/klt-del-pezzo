import KltDP.RingTheory.IntegralMapIntoNormalOverring
import KltDP.Geometry.PushforwardAffineIntegralClosure
import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.NormalOpenSections

/-!
# Original sections of a universally closed birational map to a normal target

The original section map on an affine target open is integral by the
compiled universally-closed theorem. The inverse of the original generic
stalk isomorphism embeds its target section ring into the target function
field. Normality puts every such integral element back in the original
target section ring. No pushforward isomorphism is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalNormalAffineSections

/-- Bijectivity concerns the literal original section map, with no
replacement affine-preimage ring or independently chosen function field. -/
theorem app_bijective
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [UniversallyClosed π]
    (hbir : IsBirationalScheme π) (hnormal : IsNormalScheme X)
    (U : X.AffineZariskiSite) [Nonempty U.1] :
    Function.Bijective (π.app U.1) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  let e : X.functionField ≃+* S.functionField :=
    (asIso (functionFieldMap π)).commRingCatIsoToRingEquiv
  let j : Γ(S, π ⁻¹ᵁ U.1) →+* X.functionField :=
    e.symm.toRingHom.comp (S.germToFunctionField (π ⁻¹ᵁ U.1)).hom
  letI : IsIntegrallyClosedIn Γ(X, U.1) X.functionField :=
    isIntegrallyClosedIn_openSections_of_isNormal X hnormal U.1
  have hj : Function.Injective j :=
    e.symm.injective.comp (S.germToFunctionField_injective (π ⁻¹ᵁ U.1))
  have hcomm : j.comp (π.app U.1).hom = algebraMap Γ(X, U.1) X.functionField := by
    ext s
    change e.symm (S.germToFunctionField (π ⁻¹ᵁ U.1) (π.app U.1 s)) =
      X.germToFunctionField U.1 s
    rw [← functionFieldMap_germ π U.1 s]
    exact e.symm_apply_apply _
  exact KltDP.RingTheory.IntegralMapIntoNormalOverring.bijective
    (π.app U.1).hom (PushforwardAffineIntegralClosure.app_isIntegral π U) j hj hcomm

/-- The original affine-open section morphism is an isomorphism in rings. -/
theorem app_isIso
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [UniversallyClosed π]
    (hbir : IsBirationalScheme π) (hnormal : IsNormalScheme X)
    (U : X.AffineZariskiSite) [Nonempty U.1] : IsIso (π.app U.1) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (app_bijective π hbir hnormal U)

end KltDP.Geometry.BirationalNormalAffineSections
