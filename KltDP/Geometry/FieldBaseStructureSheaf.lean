import KltDP.Geometry.AffinizationStructureSheaf
import KltDP.Geometry.ProperGlobalSectionsFinite

/-! Over the original field spectrum, bijectivity of the original
constant-section map implies that the entire original pushforward
structure-sheaf map is an isomorphism. The singleton top-open basis
avoids any replacement of the source or its global functions. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.FieldBaseStructureSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual top-section map suffices on the original one-point base. -/
theorem c_isIso_of_baseFieldToGlobalSections_bijective
    (f : X ⟶ Spec (CommRingCat.of k))
    (hf : Function.Bijective (baseFieldToGlobalSections f)) : IsIso f.c := by
  let e : CommRingCat.of k ≅ Γ(X, ⊤) :=
    (RingEquiv.ofBijective (baseFieldToGlobalSections f) hf).toCommRingCatIso
  have happ : f.appTop = ((Scheme.ΓSpecIso (CommRingCat.of k)) ≪≫ e).hom := by
    ext r
    change f.appTop r = f.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom r))
    rw [(Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply]
  letI : IsIso f.appTop := by rw [happ]; infer_instance
  let V : Unit → (Spec (CommRingCat.of k)).Opens := fun _ => ⊤
  have hB : Opens.IsBasis (Set.range V) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    refine ⟨⊤, ⟨(), rfl⟩, by trivial, ?_⟩
    intro y _
    have hy : y = x := Subsingleton.elim _ _
    simpa only [hy] using hx
  letI : IsIso (AffinizationStructureSheaf.structureMap f) := by
    apply TopCat.Sheaf.isIso_of_isIso_basis hB
    intro j
    change IsIso f.appTop
    infer_instance
  exact (TopCat.Sheaf.forget CommRingCat _).map_isIso
    (AffinizationStructureSheaf.structureMap f)

end KltDP.Geometry.FieldBaseStructureSheaf

#check @KltDP.Geometry.FieldBaseStructureSheaf.c_isIso_of_baseFieldToGlobalSections_bijective
#print axioms KltDP.Geometry.FieldBaseStructureSheaf.c_isIso_of_baseFieldToGlobalSections_bijective
