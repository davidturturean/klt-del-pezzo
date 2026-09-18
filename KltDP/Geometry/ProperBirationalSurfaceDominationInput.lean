import KltDP.Geometry.ProperBirationalSurfaceFiniteBadSet
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.SmoothFieldRegularPoints

/-!
The actual hypotheses for point-blowup domination, derived for the
original proper birational morphism from an arbitrary integral scheme
to a regular normal projective surface. The finite set is exactly the
original target non-isomorphism locus. This proves input geometry only;
no domination, factorization or literature theorem is assumed.

Algebraic closedness is explicit because the reused closed-point stalk
dimension and smooth-regularity producers have that scope.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperBirationalSurface

/-- All actual domination hypotheses, including the exact bad set and
the original isomorphism restriction, for a regular target surface. -/
theorem exists_domination_input_of_regular
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (B : Set T.toScheme) (hfinite : B.Finite)
      (hclosed : ∀ x ∈ B, IsClosed ({x} : Set T.toScheme)),
      B = targetNonisomorphismLocus f ∧ IsNoetherian T.toScheme ∧
      (∀ x ∈ B, RegularPoint T.toScheme x ∧
        ringKrullDim (T.toScheme.presheaf.stalk x) = 2) ∧
      IsIso (f ∣_ finiteClosedPointComplement T.toScheme B hfinite hclosed) := by
  refine ⟨targetNonisomorphismLocus f, targetNonisomorphismLocus_finite T f hbir,
    isClosed_singleton_of_mem_targetNonisomorphismLocus T f hbir,
    rfl, ?_, ?_, isIso_finiteClosedPointComplement_targetNonisomorphismLocus T f hbir⟩
  · letI : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian
    exact ⟨⟩
  · intro x hx
    exact ⟨hreg x, T.closed_stalk_dimension_two x
      (isClosed_singleton_of_mem_targetNonisomorphismLocus T f hbir x hx)⟩

/-- Smoothness over the original algebraically closed field discharges
regularity; no extra regularity witness is required. -/
theorem exists_domination_input_of_smooth
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) [IsSmooth T.structureMorphism] :
    ∃ (B : Set T.toScheme) (hfinite : B.Finite)
      (hclosed : ∀ x ∈ B, IsClosed ({x} : Set T.toScheme)),
      B = targetNonisomorphismLocus f ∧ IsNoetherian T.toScheme ∧
      (∀ x ∈ B, RegularPoint T.toScheme x ∧
        ringKrullDim (T.toScheme.presheaf.stalk x) = 2) ∧
      IsIso (f ∣_ finiteClosedPointComplement T.toScheme B hfinite hclosed) := by
  apply exists_domination_input_of_regular T f hbir
  exact SmoothFieldRegularPoints.regularPoint_of_isSmooth_of_isNormalScheme
    T.structureMorphism T.normal (fun x => inferInstance) T.dimension_two.le

end KltDP.Geometry.ProperBirationalSurface
