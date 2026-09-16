import KltDP.Compatibility.ExteriorPowerPresheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The original exterior scalar-restriction map for a ring equivalence

The inverse sends a native exterior product over the target ring to the same
product over the restricted source ring. Its alternating universal property
uses the inverse ring equivalence, and the existing scalar-restriction counit
returns the original source module. Both inverse identities are proved on
native pure wedges using the pinned exterior-power universal property.

The resulting isomorphism has exactly the pre-existing
`ExteriorPowerPresheaf.fromRestrictScalars` as its forward morphism.
-/

noncomputable section

open CategoryTheory

universe u

namespace KltDP.Compatibility.ExteriorPowerRestrictScalarsRingEquiv

open ExteriorPowerPresheaf

variable {A B : Type u} [CommRing A] [CommRing B]
  (e : A ≃+* B) (M : ModuleCat.{u} B) (n : ℕ)

/-- The inverse alternating construction, still over the original target ring. -/
private def inverseOverB :
    M.exteriorPower n ⟶
      (ModuleCat.restrictScalars e.symm.toRingHom).obj
        (((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun := fun m => ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m
      map_update_add' := fun m i x y =>
        (exteriorPower.ιMulti A n
          (M := (ModuleCat.restrictScalars e.toRingHom).obj M)).map_update_add m i x y
      map_update_smul' := by
        intro inst m i r x
        change (exteriorPower.ιMulti A n
            (M := (ModuleCat.restrictScalars e.toRingHom).obj M))
            (Function.update m i (r • x)) =
          e.symm r • (exteriorPower.ιMulti A n
            (M := (ModuleCat.restrictScalars e.toRingHom).obj M)) (Function.update m i x)
        have he : e.toRingHom (e.symm r) = r := by
          change e (e.symm r) = r
          exact e.apply_symm_apply r
        have h := (exteriorPower.ιMulti A n
          (M := (ModuleCat.restrictScalars e.toRingHom).obj M)).map_update_smul
            m i (e.symm r) x
        simpa only [ModuleCat.restrictScalars.smul_def, he] using h
      map_eq_zero_of_eq' := fun m _ _ hm hij =>
        (exteriorPower.ιMulti A n
          (M := (ModuleCat.restrictScalars e.toRingHom).obj M)).map_eq_zero_of_eq m hm hij }

private theorem inverseOverB_mk (m : Fin n → M) :
    inverseOverB e M n (ModuleCat.exteriorPower.mk (M := M) m) =
      ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- The inverse on the actual restricted exterior module, using the existing
ring-equivalence counit. -/
def inverse :
    (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) ⟶
      ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n :=
  (ModuleCat.restrictScalars e.toRingHom).map (inverseOverB e M n) ≫
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.app
      (((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n)).hom

/-- The inverse is normalized on the native target-ring exterior product. -/
@[simp]
theorem inverse_mk (m : Fin n → M) :
    inverse e M n (ModuleCat.exteriorPower.mk (M := M) m) =
      ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m := by
  change inverseOverB e M n (ModuleCat.exteriorPower.mk (M := M) m) = _
  exact inverseOverB_mk e M n m

/-- The original forward morphism viewed over the target ring, using the
existing ring-equivalence unit. Its underlying map is unchanged. -/
private def forwardOverB :
    (ModuleCat.restrictScalars e.symm.toRingHom).obj
      (((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n) ⟶
        M.exteriorPower n :=
  (ModuleCat.restrictScalars e.symm.toRingHom).map
      (fromRestrictScalars e.toRingHom M n) ≫
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso.app (M.exteriorPower n)).inv

private theorem forwardOverB_mk (m : Fin n → M) :
    forwardOverB e M n (ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m) =
      ModuleCat.exteriorPower.mk (M := M) m := by
  change fromRestrictScalars e.toRingHom M n
    (ModuleCat.exteriorPower.mk
      (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m) = _
  exact fromRestrictScalars_mk e.toRingHom M n m

theorem forward_inverse : fromRestrictScalars e.toRingHom M n ≫ inverse e M n = 𝟙 _ := by
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro m
  change inverse e M n
    (fromRestrictScalars e.toRingHom M n (ModuleCat.exteriorPower.mk m)) =
      ModuleCat.exteriorPower.mk m
  rw [fromRestrictScalars_mk, inverse_mk]

theorem inverse_forward : inverse e M n ≫ fromRestrictScalars e.toRingHom M n = 𝟙 _ := by
  have hB : inverseOverB e M n ≫ forwardOverB e M n = 𝟙 (M.exteriorPower n) := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    change forwardOverB e M n (inverseOverB e M n (ModuleCat.exteriorPower.mk m)) =
      ModuleCat.exteriorPower.mk m
    rw [inverseOverB_mk, forwardOverB_mk]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact CategoryTheory.congr_fun hB x

/-- The isomorphism whose forward morphism is exactly the existing comparison. -/
def fromRestrictScalarsIso :
    ((ModuleCat.restrictScalars e.toRingHom).obj M).exteriorPower n ≅
      (ModuleCat.restrictScalars e.toRingHom).obj (M.exteriorPower n) where
  hom := fromRestrictScalars e.toRingHom M n
  inv := inverse e M n
  hom_inv_id := forward_inverse e M n
  inv_hom_id := inverse_forward e M n

@[simp]
theorem fromRestrictScalarsIso_hom :
    (fromRestrictScalarsIso e M n).hom = fromRestrictScalars e.toRingHom M n := rfl

/-- The original scalar-restriction morphism is an isomorphism for an actual
ring equivalence, in every exterior degree including zero. -/
instance fromRestrictScalars_isIso : IsIso (fromRestrictScalars e.toRingHom M n) :=
  inferInstanceAs (IsIso (fromRestrictScalarsIso e M n).hom)

/-- Native-wedge normalization for the inverse of the resulting actual iso. -/
@[simp]
theorem iso_inv_mk (m : Fin n → M) :
    (fromRestrictScalarsIso e M n).inv (ModuleCat.exteriorPower.mk (M := M) m) =
      ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.toRingHom).obj M) m :=
  inverse_mk e M n m

end KltDP.Compatibility.ExteriorPowerRestrictScalarsRingEquiv
