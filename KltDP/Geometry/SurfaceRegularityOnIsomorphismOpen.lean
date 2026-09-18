import KltDP.Geometry.RegularPointsOnIsomorphismOpen
import KltDP.Geometry.SurfaceFiniteness
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# Original surface singular points and an isomorphism open

The generic stalk-transport theorem applies to the existing finite set of
singular points of a normal projective surface. Smooth source surfaces
supply the required regularity through the already proved regularity theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RegularPointsOnIsomorphismOpen

/-- The existing finite set of actual singular surface points lies outside
the target open on which the original map is an isomorphism. -/
theorem singularPoints_subset_compl {k : Type u} [Field k] {X : Scheme.{u}}
    (Y : NormalProjectiveSurface k) (π : X ⟶ Y.toScheme) (U : Y.toScheme.Opens)
    [IsIso (π ∣_ U)] (hreg : ∀ x : X, RegularPoint X x) :
    (Y.singularPoints : Set Y.Point) ⊆ (U : Set Y.Point)ᶜ := by
  intro y hy
  apply singularLocus_subset_compl π U hreg
  exact (Y.mem_singularPoints y).mp hy

/-- Smoothness of the original surface supplies regularity on the target
isomorphism open, through the original source stalks. -/
theorem regularPoint_of_mem_of_isSmooth {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism] {Y : Scheme.{u}}
    (π : X.toScheme ⟶ Y) (U : Y.Opens) [IsIso (π ∣_ U)]
    (y : Y) (hy : y ∈ U) : RegularPoint Y y :=
  regularPoint_of_mem π U X.regularPoints_of_isSmooth y hy

end KltDP.Geometry.RegularPointsOnIsomorphismOpen
