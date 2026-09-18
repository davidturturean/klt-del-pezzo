import KltDP.Geometry.BirationalIsomorphismOpen
import KltDP.Geometry.ProperOpenDimension

/-!
# Dimension preservation by an original proper birational morphism

The original generic stalk inverse produces a nonempty isomorphism open.
The accepted closed-point dimension comparison then applies to that same
morphism and its actual composite with the target's field structure.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- An original proper birational morphism preserves dimension over an
algebraically closed field, by its derived nonempty isomorphism open. -/
theorem topologicalKrullDim_eq_of_proper_birational
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Y) [IsProper π]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (hbir : IsBirationalScheme π) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  obtain ⟨U, hU, hπU⟩ := exists_isomorphism_open_of_isBirationalScheme π hbir
  letI : Nonempty U := hU
  letI : IsIso (π ∣_ U) := hπU
  exact topologicalKrullDim_eq_of_proper_isomorphism_open π σ U

/-- The actual integral target of a proper birational map from the original
surface has dimension two. -/
theorem target_dimension_two_of_proper_birational
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) {Y : Scheme.{u}} [IsIntegral Y]
    (π : X.toScheme ⟶ Y) [IsProper π]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (hbir : IsBirationalScheme π) : topologicalKrullDim Y = 2 :=
  (topologicalKrullDim_eq_of_proper_birational π σ hbir).symm.trans X.dimension_two

end KltDP.Geometry
