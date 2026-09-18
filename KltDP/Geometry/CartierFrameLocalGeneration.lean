import KltDP.Geometry.CartierFrameSectionCoefficient

/-!
# Original Cartier frames generate on every smaller neighborhood

Restrict the original equation chart without changing its rational
equation. The original frame restricts to the frame of that chart, so the
accepted section-coordinate equivalence supplies every local coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierFrameLocalGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    (c : CartierEquationChart X D) (V : X.Opens) [Nonempty V]
    (hV : V ≤ c.openSet)

/-- Restrict the original chart while retaining its original equation. -/
def restrictedChart : CartierEquationChart X D where
  openSet := V
  nonempty := inferInstance
  equation := c.equation
  represents := cartierGlobalEquation_restrict X D (homOfLE hV)
    c.equation c.represents

/-- The original fractional section `1/f` is unchanged by restriction. -/
theorem cartierFrame_restrict :
    (cartierDivisorModule X D).val.map (homOfLE hV).op (cartierFrame X D c) =
      cartierFrame X D (restrictedChart X D c V hV) := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X V).injective
  change rationalFunctionModuleSectionsEquiv X V
      ((rationalFunctionModule X).val.map (homOfLE hV).op
        (cartierFrame X D c).val) = _
  rw [rationalFunctionModuleSectionsEquiv_naturality, cartierFrame_field]
  exact (cartierFrame_field X D (restrictedChart X D c V hV)).symm

variable (M : X.Modules) (e : cartierDivisorModule X D ≅ M)

/-- The same restriction identity holds after the given original module
isomorphism. -/
theorem frame_restrict :
    M.val.map (homOfLE hV).op (CartierRationalCoordinate.frame X D M e c) =
      CartierRationalCoordinate.frame X D M e (restrictedChart X D c V hV) := by
  change M.val.map (homOfLE hV).op
      (e.hom.val.app (op c.openSet) (cartierFrame X D c)) =
    e.hom.val.app (op V) (cartierFrame X D (restrictedChart X D c V hV))
  rw [← _root_.PresheafOfModules.naturality_apply e.hom.val (homOfLE hV).op
    (cartierFrame X D c), cartierFrame_restrict]

/-- Every actual section on a smaller neighborhood is a scalar multiple
of the restriction of the original Cartier frame. -/
theorem exists_smul_frame_on (s : M.val.obj (op V)) :
    ∃ a : Γ(X, V),
      a • M.val.map (homOfLE hV).op (CartierRationalCoordinate.frame X D M e c) = s := by
  refine ⟨CartierRationalCoordinate.sectionCoefficient X D M e
    (restrictedChart X D c V hV) s, ?_⟩
  rw [frame_restrict]
  exact CartierRationalCoordinate.sectionCoefficient_smul_frame X D M e
    (restrictedChart X D c V hV) s

end KltDP.Geometry.CartierFrameLocalGeneration

#check @KltDP.Geometry.CartierFrameLocalGeneration.exists_smul_frame_on
#print axioms KltDP.Geometry.CartierFrameLocalGeneration.exists_smul_frame_on
