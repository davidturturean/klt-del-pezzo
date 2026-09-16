import KltDP.Literature.Stacks.CurveTensorDegreeLiteral
import KltDP.Geometry.PrimeCurveLineDegree

/-!
# Ordinary expansion and original prime-curve comparison

INACTIVE TEXT. This file proves adapters from the separately proposed full
0AYX declaration. It declares no additional literature input. The first
theorem supplies the exact scalar interface of the unchanged ordinary
Picard/restriction consumer candidate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open scoped CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Literature.Stacks

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Expanding only the ordinary rank-indexed degree definition yields the
full scalar identity on the original module sheaves and original base field. -/
theorem proper_curve_tensor_degree
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (E V : Y.Modules) (n m : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E n)
    (hV : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) V m) :
    letI := Scheme.Modules.monoidalCategory Y
    eulerCharacteristic f (E ⊗ V) -
        ((n * m : ℕ) : ℤ) * eulerCharacteristic f
          (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      (n : ℤ) * (eulerCharacteristic f V -
        (m : ℤ) * eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
      (m : ℤ) * (eulerCharacteristic f E -
        (n : ℤ) * eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) := by
  letI := Scheme.Modules.monoidalCategory Y
  simpa only [finiteRankDegree] using
    proper_curve_tensor_degree_literal (Y := Y) f hdim E V n m hE hV

end KltDP.Literature.Stacks

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The rank-one notation of 0AYR agrees with the existing intrinsic degree
of this very sheaf on the original, possibly singular, projective prime curve. -/
theorem finiteRankDegree_eq_lineDegree
    {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (C : X.PrimeCurve) (L : InvertibleSheaf C.toScheme) :
    letI : IsProper C.toSpec := C.toSpec_isProper
    finiteRankDegree C.toSpec (le_of_eq C.dimension_one_toScheme) L.obj 1
      (by infer_instance) = C.lineDegree L := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  simp only [finiteRankDegree, lineDegree, Nat.cast_one, one_mul]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
