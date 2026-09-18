import KltDP.Geometry.UnimodularPicardFiniteFree
import KltDP.Geometry.RationalSurfacePicardInvariants
import KltDP.Lattices.PerfectIntegralGram
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A unimodular finite basis of the original rational surface Picard group

Actual birationality over the original field supplies the already proved
unimodularity theorem. The original Picard-to-numerical equivalence supplies
finite freeness, and Mathlib's finite basis has Gram determinant of absolute
value one for the original integral intersection form.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
open LinearMap
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)

include hS

theorem picard_free_and_finite_of_birationalOver_affinePlane
    (hrational : Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    Module.Free ℤ (Additive S.toScheme.Pic) ∧
      Module.Finite ℤ (Additive S.toScheme.Pic) :=
  S.picard_free_and_finite_of_picardUnimodular hS
    (S.picardUnimodular_of_birationalOver_affinePlane hS hrational)

/-- An actual finite integral basis, with the exact Gram determinant needed
by the integral node obstruction; all hypotheses concern the original surface. -/
theorem exists_picard_basis_det_natAbs_one
    (hrational : Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℤ (Additive S.toScheme.Pic),
      (BilinForm.toMatrix b (S.integralPicardIntersectionBilinForm hS)).det.natAbs = 1 := by
  have hU := S.picardUnimodular_of_birationalOver_affinePlane hS hrational
  obtain ⟨hfree, hfinite⟩ := S.picard_free_and_finite_of_picardUnimodular hS hU
  letI : Module.Free ℤ (Additive S.toScheme.Pic) := hfree
  letI : Module.Finite ℤ (Additive S.toScheme.Pic) := hfinite
  let b := Module.finBasis ℤ (Additive S.toScheme.Pic)
  refine ⟨_, b, ?_⟩
  exact KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one b
    (S.integralPicardIntersectionBilinForm hS)
    (S.integralPicardIntersectionBilinForm_bijective_of_picardUnimodular hS hU)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picard_free_and_finite_of_birationalOver_affinePlane
#print axioms KltDP.Geometry.NormalProjectiveSurface.picard_free_and_finite_of_birationalOver_affinePlane
#check @KltDP.Geometry.NormalProjectiveSurface.exists_picard_basis_det_natAbs_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_picard_basis_det_natAbs_one
