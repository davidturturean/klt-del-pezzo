import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Actual affine sheaves of rank-one PID modules

Pinned PID freeness and the actual tilde functor turn a basis of a finite
torsion-free rank-one module into a unit-sheaf isomorphism. A projective
module is torsion-free because its defining splitting embeds it into a
free module. The final specialization uses the original scheme Spec k[t].

The source sheaf here is the original `ModuleCat.tilde M`. No identification
of an arbitrary invertible sheaf with a tilde sheaf is assumed or asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The defining projective splitting embeds a module into a torsion-free free module. -/
theorem projective_noZeroSMulDivisors (M : ModuleCat.{u} R) [Module.Projective R M] :
    NoZeroSMulDivisors R M := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  exact Function.Injective.noZeroSMulDivisors s hs.injective s.map_zero
    (fun r m => s.map_smul r m)

/-- Pinned PID freeness supplies the actual rank-one coordinate equivalence. -/
def pidRankOneLinearEquiv [IsPrincipalIdealRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [NoZeroSMulDivisors R M]
    (hRank : Module.finrank R M = 1) : M ≃ₗ[R] R :=
  LinearEquiv.ofFinrankEq M R (hRank.trans (Module.finrank_self R).symm)

/-- The original affine tilde sheaf of a finite torsion-free rank-one PID module is trivial. -/
def pidTildeUnitIso [IsPrincipalIdealRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [NoZeroSMulDivisors R M]
    (hRank : Module.finrank R M = 1) :
    M.tilde ≅ _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf :=
  linearEquivIso (M := M) (N := ModuleCat.of R R) (pidRankOneLinearEquiv M hRank) ≪≫
    unitIso R

/-- The actual finite projective rank-one case uses its proved torsion-free property. -/
def projectiveTildeUnitIso [IsPrincipalIdealRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (hRank : Module.finrank R M = 1) :
    M.tilde ≅ _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf := by
  letI := projective_noZeroSMulDivisors M
  exact pidTildeUnitIso M hRank

/-- In particular the base scheme here is literally Spec of the polynomial ring. -/
def affineLineTildeUnitIso (k : Type u) [Field k] (M : ModuleCat.{u} (Polynomial k))
    [Module.Finite (Polynomial k) M] [Module.Projective (Polynomial k) M]
    (hRank : Module.finrank (Polynomial k) M = 1) :
    M.tilde ≅ _root_.SheafOfModules.unit (Spec (.of (Polynomial k))).ringCatSheaf :=
  projectiveTildeUnitIso M hRank

end KltDP.Geometry.AffineModuleTilde
