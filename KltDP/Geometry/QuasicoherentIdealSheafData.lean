import KltDP.Geometry.AffineOpenModuleDenominators
import KltDP.Geometry.AffineQuasicoherentImageIdeal
import KltDP.Compatibility.SheafSubmodule
import Mathlib.AlgebraicGeometry.IdealSheaf

/-!
# Scheme ideal data from the original quasicoherent ideal subsheaf

The original component image ideals commute with localization on every
affine open. Denominator extension of the original source proves the
reverse inclusion; the defining section is a unit on its basic open.
This gives Mathlib's scheme ideal data directly from the original maps.
For an actual quasicoherent ideal subsheaf, every affine ideal is exactly
its original section submodule, rather than an unspecified associated ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M : X.Modules}
  (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- Original quasicoherence makes component images commute with
restriction from any affine open to its intrinsic basic opens. -/
theorem componentIdeal_map_basicOpen [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    (componentIdeal g U.1).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      componentIdeal g (X.basicOpen f) := by
  classical
  apply le_antisymm (componentIdeal_map_le g _)
  rintro _ ⟨s, rfl⟩
  let i := (homOfLE (X.basicOpen_le f)).op
  let J := (componentIdeal g U.1).map (X.presheaf.map i).hom
  change g.val.app (op (X.basicOpen f)) s ∈ J
  obtain ⟨n, t, ht⟩ := AffineOpenModule.exists_restrict_eq_pow_smul U.2 M f s
  have heq : X.presheaf.map i (g.val.app (op U.1) t) =
      @Mul.mul (Γ(X, X.basicOpen f)) inferInstance
        (X.presheaf.map i (f ^ n)) (g.val.app (op (X.basicOpen f)) s) := by
    calc
      _ = g.val.app (op (X.basicOpen f)) (M.val.map i t) :=
        (_root_.PresheafOfModules.naturality_apply g.val i t).symm
      _ = g.val.app (op (X.basicOpen f)) (X.presheaf.map i (f ^ n) • s) :=
        congrArg (g.val.app (op (X.basicOpen f))) ht
      _ = _ := (g.val.app (op (X.basicOpen f))).hom.map_smul _ _
  have hmem : X.presheaf.map i (g.val.app (op U.1) t) ∈ J :=
    Ideal.mem_map_of_mem (X.presheaf.map i).hom ⟨t, rfl⟩
  have hunit : IsUnit (X.presheaf.map i (f ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).pow n
  apply (J.unit_mul_mem_iff_mem hunit).mp
  change @Mul.mul (Γ(X, X.basicOpen f)) inferInstance
    (X.presheaf.map i (f ^ n)) (g.val.app (op (X.basicOpen f)) s) ∈ J
  rw [← heq]
  exact hmem

/-- Scheme ideal data made from the original component image ideals. -/
def ofMorphism [M.IsQuasicoherent] : X.IdealSheafData where
  ideal U := componentIdeal g U.1
  map_ideal_basicOpen U f := componentIdeal_map_basicOpen g U f

/-- Its affine ideals retain the actual original component maps. -/
@[simp]
theorem ofMorphism_ideal [M.IsQuasicoherent] (U : X.affineOpens) :
    (ofMorphism g).ideal U = componentIdeal g U.1 := rfl

variable (I : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule)

/-- Convert an actual quasicoherent ideal subsheaf to scheme ideal data. -/
def ofSubmodule [I.toSheafOfModules.IsQuasicoherent] : X.IdealSheafData :=
  ofMorphism I.ι

/-- Every affine ideal is the original section submodule of the actual subsheaf. -/
@[simp]
theorem ofSubmodule_ideal [I.toSheafOfModules.IsQuasicoherent] (U : X.affineOpens) :
    (ofSubmodule I).ideal U = I.obj (op U.1) := by
  change LinearMap.range (I.ι.val.app (op U.1)).hom = _
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact t.property
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

end KltDP.Geometry.QuasicoherentImageIdeal
