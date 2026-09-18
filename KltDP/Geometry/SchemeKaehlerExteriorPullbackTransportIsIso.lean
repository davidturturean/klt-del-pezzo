import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSource
import KltDP.Geometry.SchemeKaehlerExteriorOpenRestriction

/-!
# Invertibility of the original exterior differential on an unchanged open

The original open differential is invertible by its proved exterior restriction
isomorphism. If a projection becomes an open immersion on an original open,
the composition law therefore proves that its actual pulled differential is
invertible. No inverse map or compatibility is supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g) (n : ℕ)

/-- The original transported differential along an actual open immersion is invertible. -/
theorem map_isIso [IsOpenImmersion j] : IsIso (map f j g hg n) := by
  letI := SchemeKaehlerExteriorOpenRestriction.map_isIso f j n
  unfold map
  infer_instance

/-- Restricting the original map to an unchanged open gives an invertible whole map. -/
theorem pullback_map_isIso_of_open_comp (l : Z ⟶ Y)
    [IsOpenImmersion l] [IsOpenImmersion (l ≫ j)] :
    IsIso ((schemeModulePullback l).map (map f j g hg n)) := by
  have hq : (l ≫ j) ≫ f = l ≫ g := by rw [Category.assoc, hg]
  letI := map_isIso g l (l ≫ g) rfl n
  letI := map_isIso f (l ≫ j) (l ≫ g) hq n
  haveI : IsIso ((schemeModulePullback l).map (map f j g hg n) ≫
      map g l (l ≫ g) rfl n) := by
    rw [map_comp_sourceIso f j l g hg (l ≫ j) rfl (l ≫ g) rfl hq n]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (map g l (l ≫ g) rfl n)

end KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
