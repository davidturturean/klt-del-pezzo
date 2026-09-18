import KltDP.Geometry.ModuleCohomologyRanks

/-!
# Dimension bounds from the original short exact cohomology sequence

The maps are the original base-field cohomology maps. H0 is left exact;
when the right term has zero cohomology in degree n, the left-to-middle
map in that degree is surjective. These are the two bounds needed for
twisting by an actual prime curve on a surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

set_option autoImplicit false

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The actual H0 map of a short exact sequence gives the finite dimension bound. -/
theorem cohomologyDimension_zero_le_of_shortExact
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [FiniteDimensional k ((baseFunctor f 0).obj S.X₂)] :
    cohomologyDimension f S.X₁ 0 ≤ cohomologyDimension f S.X₂ 0 :=
  LinearMap.finrank_le_finrank_of_injective (baseMap_zero_injective f S hS)

/-- Vanishing of the actual right term makes the original left-to-middle
cohomology map surjective, so the middle dimension cannot increase. -/
theorem cohomologyDimension_middle_le_of_subsingleton_right
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [FiniteDimensional k ((baseFunctor f n).obj S.X₁)]
    [Subsingleton (H S.X₃ n)] :
    cohomologyDimension f S.X₂ n ≤ cohomologyDimension f S.X₁ n := by
  have hs : Function.Surjective ((baseFunctor f n).map S.f).hom := by
    intro x
    exact exact_middle S hS n x (Subsingleton.elim _ _)
  have hr := LinearMap.finrank_range_le ((baseFunctor f n).map S.f).hom
  rw [LinearMap.range_eq_top.mpr hs] at hr
  simpa only [finrank_top] using hr

end KltDP.Geometry.ModuleCohomology

#check @KltDP.Geometry.ModuleCohomology.cohomologyDimension_zero_le_of_shortExact
#print axioms KltDP.Geometry.ModuleCohomology.cohomologyDimension_zero_le_of_shortExact
#check @KltDP.Geometry.ModuleCohomology.cohomologyDimension_middle_le_of_subsingleton_right
#print axioms KltDP.Geometry.ModuleCohomology.cohomologyDimension_middle_le_of_subsingleton_right
