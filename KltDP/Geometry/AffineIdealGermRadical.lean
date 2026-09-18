import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Ideal

/-! The original germ map on an affine open preserves radical ideals. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The pinned affine-stalk localization applies to the literal germ map. -/
theorem affineIdeal_map_germ_radical (X : Scheme.{u}) (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) (J : Ideal Γ(X, U.1)) :
    Ideal.map (X.presheaf.germ U.1 x hx).hom J.radical =
      (Ideal.map (X.presheaf.germ U.1 x hx).hom J).radical := by
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := U.2.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) J

end KltDP.Geometry
