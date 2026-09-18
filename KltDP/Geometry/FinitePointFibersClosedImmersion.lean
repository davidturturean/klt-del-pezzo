import KltDP.Geometry.AffineChartResidueFiberRank
import KltDP.Geometry.AffineRestrictionPullbackSquare
import KltDP.Geometry.AffineFiniteType
import KltDP.CommutativeAlgebra.FiniteAlgebraResidueFibers
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! A finite original morphism whose original rational-point fibers are
points is a closed immersion. All residue tensor identifications are
derived from the original affine restriction and the canonical residue
field equivalence. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct
universe u

namespace KltDP.Geometry.FinitePointFibersClosedImmersion

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
  (π : X ⟶ Y) [IsFinite π]
  (hfib : ∀ i : Spec (CommRingCat.of k) ⟶ Y, i ≫ σ = 𝟙 _ →
    IsIso (pullback.snd π i))

include hfib in
/-- The original map on affine sections is surjective, checked at every
actual maximal ideal by finite-algebra Nakayama. -/
theorem app_surjective (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (π.app U).hom := by
  letI : Algebra k Γ(Y, U) := affineSectionsAlgebra σ hU
  letI : Algebra.FiniteType k Γ(Y, U) := affineSectionsAlgebra_finiteType σ hU
  letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := IsFinite.finite_app U hU
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have H : IsPullback hV.fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, π ⁻¹ᵁ U))))
      π hU.fromSpec := AffineRestrictionPullbackSquare.isPullback π U hU hV
  have hc : hU.fromSpec ≫ σ =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(Y, U))) :=
    (Spec_map_baseToAffineSectionsMap σ hU).symm
  apply KltDP.CommutativeAlgebra.FiniteAlgebraResidueFibers.algebraMap_surjective
    (R := Γ(Y, U)) (A := Γ(X, π ⁻¹ᵁ U))
  intro p hp
  exact AffineChartResidueFiberRank.finrank_eq_one k Γ(Y, U) Γ(X, π ⁻¹ᵁ U)
    σ π hV.fromSpec hU.fromSpec H hc hfib p

include hfib in
/-- The local ring surjections reconstruct a closed immersion of the
original schemes and original morphism. -/
theorem isClosedImmersion : IsClosedImmersion π := by
  apply IsLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : Y.affineOpens => (U : Y.Opens)) (iSup_affineOpens_eq_top Y)
  intro U
  exact AffineRestrictionPullbackSquare.restriction_isClosedImmersion π U.1 U.2
    (U.2.preimage π) (app_surjective σ π hfib U.1 U.2)

#check KltDP.Geometry.FinitePointFibersClosedImmersion.isClosedImmersion
#print axioms KltDP.Geometry.FinitePointFibersClosedImmersion.app_surjective
#print axioms KltDP.Geometry.FinitePointFibersClosedImmersion.isClosedImmersion

end KltDP.Geometry.FinitePointFibersClosedImmersion
