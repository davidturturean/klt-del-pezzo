import KltDP.Geometry.AffineModuleTildeExteriorMap
import KltDP.Geometry.ExteriorPowerFrameUnitBijective
import KltDP.Geometry.AffineModuleTildeFiniteType
import KltDP.Geometry.AffineInvertibleCounit
import KltDP.Compatibility.FreeSheafTransportedBasis

/-!
# Actual exterior frames for a finite free affine module

A basis of the original module supplies the original tilde sheaf with a
finite free presentation. The existing transported-basis construction gives
compatible frames on every open. The accepted exterior frame comparison
therefore proves invertibility of the original top exterior sheaf and of its
actual affine counit. Its original exterior unit is invertible on every open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTildeExteriorMap

open AffineModuleTilde ExteriorPowerFrameComparison ChartFrameAtlasSheaf
open KltDP.Compatibility.FreeSheafTransportedBasis

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The original module basis gives an actual free presentation of its tilde. -/
def freeIsoOfBasis {I : Type u} [Finite I] (b : Basis I R M) :
    _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ≅ M.tilde :=
  (freeCoproductIso R I).symm ≪≫
    (AffineModuleTilde.functor R).mapIso (finiteCoproductIsoPi R I) ≪≫
      AffineModuleTilde.linearEquivIso
        (M := ModuleCat.of R (I → R)) (N := M) b.equivFun.symm

variable {n : ℕ} (b : Basis (Fin n) R M)

/-- Compatible frames on all original opens, derived from the native basis. -/
def openFrame (W : Opens (PrimeSpectrum R)) :
    Basis (Fin n) Γ(Spec (.of R), W) (M.tilde.val.obj (op W)) :=
  (transportedBasis (Spec (.of R)).ringCatSheaf (ULift.{u} (Fin n)) M.tilde
    (freeIsoOfBasis M (b.reindex (Equiv.ulift.{u, 0} (α := Fin n)).symm)) (op W)).reindex
      (Equiv.ulift.{u, 0} (α := Fin n))

theorem openFrame_restrict {V W : Opens (PrimeSpectrum R)} (h : V ≤ W) (i : Fin n) :
    M.tilde.val.map (homOfLE h).op (openFrame M b W i) = openFrame M b V i := by
  unfold openFrame
  rw [Basis.reindex_apply, Basis.reindex_apply]
  exact transportedBasis_map (Spec (.of R)).ringCatSheaf (ULift.{u} (Fin n)) M.tilde
    (freeIsoOfBasis M (b.reindex (Equiv.ulift.{u, 0} (α := Fin n)).symm))
    (homOfLE h).op _

def frameCover : PUnit.{u+1} → Opens (PrimeSpectrum R) := fun _ => ⊤

theorem frameCover_covers : (⨆ i, frameCover (R := R) i) = ⊤ := by
  simp [frameCover]

def coverFrame (i : PUnit.{u+1}) (W : Opens (PrimeSpectrum R))
    (_h : W ≤ frameCover (R := R) i) := openFrame M b W

theorem coverFrame_restrict (i : PUnit.{u+1}) {V W : Opens (PrimeSpectrum R)}
    (h : V ≤ W) (hW : W ≤ frameCover (R := R) i) (t : Fin n) :
    moduleRestr M.tilde h (coverFrame M b i W hW t) =
      coverFrame M b i V (h.trans hW) t :=
  openFrame_restrict M b h t

/-- The independently defined exterior sheaf itself is invertible. -/
def exteriorInvertible : InvertibleSheaf (Spec (.of R)) :=
  InvertibleSheaf.ofIso
    (sheafOfFrames (frameCover (R := R)) (moduleSections M.tilde) (moduleRestr M.tilde)
      (coverFrame M b) (coverFrame_restrict M b) (frameCover_covers (R := R)))
    (sheafIso M.tilde (frameCover (R := R)) (coverFrame M b)
      (coverFrame_restrict M b) (frameCover_covers (R := R))).symm

theorem exteriorInvertible_obj :
    (exteriorInvertible M b).obj = SchemeExteriorPower.sheaf M.tilde n := rfl

include b in
/-- The original exterior unit is invertible on every original open. -/
theorem unit_isIso (W : Opens (PrimeSpectrum R)) :
    IsIso ((SchemeExteriorPower.toSheaf M.tilde n).app (op W)) :=
  toSheaf_isIso M.tilde (frameCover (R := R)) (coverFrame M b)
    (coverFrame_restrict M b) (frameCover_covers (R := R)) PUnit.unit le_top

include b in
/-- The original affine counit is invertible for this actual exterior sheaf. -/
theorem counit_isIso : IsIso (AffineModuleTilde.counit (SchemeExteriorPower.sheaf M.tilde n)) :=
  counit_isIso_of_localTrivializations (SchemeExteriorPower.sheaf M.tilde n)
    (exteriorInvertible M b).localTrivializations

end KltDP.Geometry.AffineModuleTildeExteriorMap
