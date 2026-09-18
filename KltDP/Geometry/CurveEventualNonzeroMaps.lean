import KltDP.Geometry.CurveEventualTwistedSections
import KltDP.Geometry.InvertibleSectionTwistMap
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# Eventual nonzero maps from any fixed line bundle to a positive-degree power

Represent the inverse of the original fixed line bundle's Picard class
by an actual invertible sheaf, with its actual tensor cancellation isomorphism.
The eventual twisted sections then give nonzero original sheaf morphisms
to the original tensor-power representatives.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveEventualNonzeroMaps

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance tensorModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

open InvertibleSheafSectionPowers InvertibleSheafTensor

private theorem exists_leftTensorInverse {Y : Scheme.{u}} (H : InvertibleSheaf Y) :
    ∃ M : InvertibleSheaf Y,
      Nonempty (M.obj ⊗ H.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨M, hM⟩ := RationalTreePicard.toPic_surjective (H.toPic⁻¹)
  refine ⟨M, (RationalTreePicard.toPic_eq_one_iff_iso_unit
    (tensorInvertibleSheaf M H)).mp ?_⟩
  rw [AmpleSerreDegreeBound.tensorInvertibleSheaf_toPic, hM, inv_mul_cancel]

private def tensorCancelIso {Y : Scheme.{u}} (P M H : InvertibleSheaf Y)
    (e : M.obj ⊗ H.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (tensorInvertibleSheaf P M).obj ⊗ H.obj ≅ P.obj :=
  (α_ P.obj M.obj H.obj) ≪≫ (tensorLeft P.obj).mapIso e ≪≫
    schemeStructureTensorRightIso P.obj

/-- For every fixed original H, all sufficiently large original powers of a positive-degree
line bundle L admit an actual nonzero map from H. No section or inverse witness is assumed. -/
theorem eventually_exists_nonzero_map
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (H L : InvertibleSheaf Y)
    (hdeg : 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ σ : H.obj ⟶ (power L n).obj, σ ≠ 0 := by
  obtain ⟨M, ⟨e⟩⟩ := exists_leftTensorInverse H
  obtain ⟨N, hN⟩ := CurveEventualTwistedSections.eventually_exists_nonzero_tensor_section
    f hdim L M hdeg
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn
  exact InvertibleSectionTwistMap.exists_nonzero_map H
    (tensorInvertibleSheaf (power L n) M).obj (power L n).obj
    (tensorCancelIso (power L n) M H e) s hs

end KltDP.Geometry.CurveEventualNonzeroMaps
