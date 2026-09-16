import KltDP.Geometry.AffineQuasicoherentCounit
import Mathlib.RingTheory.Ideal.Maps

/-!
# Actual image ideals of quasicoherent modules on an affine scheme

For an original morphism from a module sheaf to the structure module, its
component ranges are ideals and respect restriction. On Spec R, original
quasicoherence supplies denominator extension for the source module.
Naturality then clears the same denominator in the original image ideal;
the defining function is a unit on its basic open, so it can be cancelled.

The result is equality with the extension of the original global image
ideal. No injectivity, finite generation, Noetherianity, image-preservation
or localization hypothesis is added. Passing from arbitrary affine opens
of a general scheme to this Spec statement remains a separate adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M : X.Modules}
  (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The ideal is the range of the original component map into regular functions. -/
def componentIdeal (U : X.Opens) : Ideal Γ(X, U) :=
  LinearMap.range (g.val.app (op U)).hom

/-- Original naturality makes these actual component ideals stable under restriction. -/
theorem componentIdeal_restrict {V W : X.Opens} (i : V ⟶ W)
    (s : Γ(X, W)) (hs : s ∈ componentIdeal g W) :
    X.presheaf.map i.op s ∈ componentIdeal g V := by
  obtain ⟨t, rfl⟩ := hs
  refine ⟨M.val.map i.op t, ?_⟩
  exact _root_.PresheafOfModules.naturality_apply g.val i.op t

/-- Extending the original ideal along a restriction gives one inclusion. -/
theorem componentIdeal_map_le {V W : X.Opens} (i : V ⟶ W) :
    (componentIdeal g W).map (X.presheaf.map i.op).hom ≤ componentIdeal g V := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro s hs
  exact componentIdeal_restrict g i s hs

section Affine

open AffineModuleTilde

variable {R : Type u} [CommRing R] {N : (Spec (.of R)).Modules}
  (φ : N ⟶ _root_.SheafOfModules.unit (Spec (.of R)).ringCatSheaf)

/-- Quasicoherence of the original source proves equality with the actual
global image ideal localized to a basic open. -/
theorem componentIdeal_map_top_basicOpen [N.IsQuasicoherent] (f : R) :
    (componentIdeal φ ⊤).map
        ((Spec (.of R)).presheaf.map
          (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op).hom =
      componentIdeal φ (PrimeSpectrum.basicOpen f) := by
  classical
  apply le_antisymm (componentIdeal_map_le φ _) 
  rintro _ ⟨s, rfl⟩
  let U := PrimeSpectrum.basicOpen f
  let i : U ⟶ (⊤ : (Spec (.of R)).Opens) := homOfLE le_top
  let J := (componentIdeal φ ⊤).map ((Spec (.of R)).presheaf.map i.op).hom
  change φ.val.app (op U) s ∈ J
  obtain ⟨n, t, ht⟩ :=
    (denominatorExtension_of_isQuasicoherent N).existence f le_top s
  have ht' : N.val.map i.op t =
      StructureSheaf.toOpen R U (f ^ n) • (s : N.val.obj (op U)) := ht
  have heq : (Spec (.of R)).presheaf.map i.op (φ.val.app (op ⊤) t) =
      @Mul.mul (Γ(Spec (.of R), U)) inferInstance
        (StructureSheaf.toOpen R U (f ^ n)) (φ.val.app (op U) s) := by
    calc
      _ = φ.val.app (op U) (N.val.map i.op t) :=
        (_root_.PresheafOfModules.naturality_apply φ.val i.op t).symm
      _ = φ.val.app (op U)
          (StructureSheaf.toOpen R U (f ^ n) • (s : N.val.obj (op U))) :=
        congrArg (φ.val.app (op U)) ht'
      _ = _ := (φ.val.app (op U)).hom.map_smul _ _
  have hmem : (Spec (.of R)).presheaf.map i.op (φ.val.app (op ⊤) t) ∈ J :=
    Ideal.mem_map_of_mem ((Spec (.of R)).presheaf.map i.op).hom ⟨t, rfl⟩
  have hunit : IsUnit (StructureSheaf.toOpen R U (f ^ n)) := by
    rw [map_pow]
    exact (StructureSheaf.isUnit_to_basicOpen_self R f).pow n
  apply (J.unit_mul_mem_iff_mem hunit).mp
  change @Mul.mul (Γ(Spec (.of R), U)) inferInstance
    (StructureSheaf.toOpen R U (f ^ n)) (φ.val.app (op U) s) ∈ J
  rw [← heq]
  exact hmem

end Affine

end KltDP.Geometry.QuasicoherentImageIdeal
