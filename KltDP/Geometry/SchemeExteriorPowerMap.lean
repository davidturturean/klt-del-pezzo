import KltDP.Compatibility.ExteriorPowerPresheafMap
import KltDP.Geometry.SchemeExteriorPower

/-!
# Maps of the original exterior-power sheaves

An actual morphism of modules on the same scheme induces the sheafification
of its pointwise exterior-power map. The original sheafification units and
the original wedges are natural for this map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeExteriorPower

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The map of the existing exterior sheaves induced by the original
same-scheme module morphism. -/
def map (f : M ⟶ N) (n : ℕ) : sheaf M n ⟶ sheaf N n :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
    (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf f.val n)

@[simp]
theorem map_id (M : X.Modules) (n : ℕ) : map (𝟙 M) n = 𝟙 (sheaf M n) := by
  let F := _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  change F.map (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf (𝟙 M.val) n) =
    𝟙 (F.obj (presheaf M n))
  exact (congrArg (fun g : presheaf M n ⟶ presheaf M n => F.map g)
    (KltDP.Compatibility.ExteriorPowerPresheaf.map_id X.presheaf M.val n)).trans
      (F.map_id (presheaf M n))

@[simp]
theorem map_comp (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  let F := _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  change F.map
      (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf (f.val ≫ g.val) n) =
    F.map (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf f.val n) ≫
      F.map (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf g.val n)
  exact (congrArg (fun h : presheaf M n ⟶ presheaf P n => F.map h)
    (KltDP.Compatibility.ExteriorPowerPresheaf.map_comp X.presheaf f.val g.val n)).trans
      (F.map_comp _ _)

/-- The original sheafification unit commutes with the exterior-power map. -/
@[reassoc]
theorem toSheaf_naturality (f : M ⟶ N) (n : ℕ) :
    KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf f.val n ≫ toSheaf N n =
      toSheaf M n ≫ (map f n).val :=
  (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).unit.naturality
      (KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf f.val n)

/-- Sectionwise naturality holds on every original exterior-presheaf section. -/
@[simp]
theorem map_toSheaf (f : M ⟶ N) (n : ℕ) (W : X.Opens)
    (q : (presheaf M n).obj (op W)) :
    (map f n).val.app (op W) ((toSheaf M n).app (op W) q) =
      (toSheaf N n).app (op W)
        ((KltDP.Compatibility.ExteriorPowerPresheaf.map X.presheaf f.val n).app
          (op W) q) := by
  exact congrArg (fun g : presheaf M n ⟶ (sheaf N n).val =>
    g.app (op W) q) (toSheaf_naturality f n).symm

/-- The map sends a wedge of original sections to the wedge of their original
images on the same open. -/
@[simp]
theorem map_wedge (f : M ⟶ N) (n : ℕ) (W : X.Opens)
    (v : Fin n → M.val.obj (op W)) :
    (map f n).val.app (op W) (wedge M n W v) =
      wedge N n W (fun i => f.val.app (op W) (v i)) := by
  change (map f n).val.app (op W)
      ((toSheaf M n).app (op W) (exteriorPower.ιMulti Γ(X, W) n v)) =
    (toSheaf N n).app (op W)
      (exteriorPower.ιMulti Γ(X, W) n (fun i => f.val.app (op W) (v i)))
  rw [map_toSheaf]
  exact congrArg ((toSheaf N n).app (op W))
    (KltDP.Compatibility.ExteriorPowerPresheaf.map_mk X.presheaf f.val n (op W) v)

/-- An isomorphism of the original module sheaves induces an isomorphism of
their existing exterior sheaves. -/
def mapIso (e : M ≅ N) (n : ℕ) : sheaf M n ≅ sheaf N n where
  hom := map e.hom n
  inv := map e.inv n
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

@[simp]
theorem mapIso_hom (e : M ≅ N) (n : ℕ) : (mapIso e n).hom = map e.hom n := rfl

@[simp]
theorem mapIso_inv (e : M ≅ N) (n : ℕ) : (mapIso e n).inv = map e.inv n := rfl

end KltDP.Geometry.SchemeExteriorPower
