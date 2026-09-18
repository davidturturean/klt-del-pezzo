import KltDP.Geometry.CurvePositiveDegreeBig
import KltDP.Geometry.SchemeModulePullbackUnit
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Eventual nonzero original sections of a positive-degree power with a fixed twist

The approved tensor-degree identity and the compiled power calculation give
the actual Euler value n deg(L) + χ(M). This is positive for every sufficiently
large n when deg(L) is positive. The original proper-curve Euler formula
then gives positive actual H0 dimension and a compatible original section
whose top value is nonzero. The original field need not be algebraically closed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveEventualTwistedSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance tensorModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

open InvertibleSheafSectionPowers InvertibleSheafTensor

variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- The actual Euler value of an original tensor power with a fixed original twist. -/
theorem eulerCharacteristic_power_tensor (hdim : topologicalKrullDim Y ≤ 1)
    (L M : InvertibleSheaf Y) (n : ℕ) :
    eulerCharacteristic f (tensorInvertibleSheaf (power L n) M).obj =
      (n : ℤ) * (eulerCharacteristic f L.obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
          eulerCharacteristic f M.obj := by
  have h := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.proper_invertible_tensor_euler
    f hdim (power L n) M
  rw [CurvePositiveDegreeBig.eulerCharacteristic_power f hdim L n] at h
  change eulerCharacteristic f ((power L n).obj ⊗ M.obj) = _
  linarith

/-- A positive original Euler value on a proper curve produces a nonzero compatible section. -/
theorem exists_nonzero_section_of_euler_pos (hdim : topologicalKrullDim Y ≤ 1)
    (M : InvertibleSheaf Y) (hχ : 0 < eulerCharacteristic f M.obj) :
    ∃ s : M.obj.sections, s.val (op ⊤) ≠ 0 := by
  classical
  letI := baseSectionsModule f M.obj
  have heuler := proper_eulerCharacteristic_eq_h0_sub_h1 f hdim M.obj
  have hpos : 0 < cohomologyDimension f M.obj 0 := by omega
  rw [cohomologyDimension_zero_eq_finrank_sections f M.obj] at hpos
  letI : Nontrivial (sections M.obj) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : sections M.obj)
  refine ⟨(schemeModuleSectionsEquivTop M.obj).symm v, ?_⟩
  change (schemeModuleSectionsEquivTop M.obj)
    ((schemeModuleSectionsEquivTop M.obj).symm v) ≠ 0
  simpa only [Equiv.apply_symm_apply] using hv

/-- Every sufficiently large original power with any fixed invertible twist has an actual
nonzero section. Properness and dimension at most one suffice over an arbitrary field. -/
theorem eventually_exists_nonzero_tensor_section (hdim : topologicalKrullDim Y ≤ 1)
    (L M : InvertibleSheaf Y)
    (hdeg : 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ s : (tensorInvertibleSheaf (power L n) M).obj.sections,
        s.val (op ⊤) ≠ 0 := by
  let d : ℤ := eulerCharacteristic f L.obj -
    eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)
  let z : ℤ := eulerCharacteristic f M.obj
  have hd : (1 : ℤ) ≤ d := by omega
  obtain ⟨N, hN⟩ := exists_nat_gt (-z)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hnd : (n : ℤ) ≤ (n : ℤ) * d := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℤ) ≤ n)
  apply exists_nonzero_section_of_euler_pos f hdim
    (tensorInvertibleSheaf (power L n) M)
  rw [eulerCharacteristic_power_tensor f hdim L M n]
  change 0 < (n : ℤ) * d + z
  omega

end KltDP.Geometry.CurveEventualTwistedSections
