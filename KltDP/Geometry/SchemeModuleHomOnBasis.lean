import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Extending actual linear section maps from an open basis

The pinned cover-dense sheaf theorem extends the underlying additive map.
Original section-ring linearity is checked on the subordinate basis
cover, using the original module restriction laws. This supplies the
ordinary descent needed to turn the quadratic chart coefficient maps
into maps of the actual global module sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

set_option autoImplicit false

namespace KltDP.Geometry.SchemeModuleHomOnBasis

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M N : X.Modules)
  {ι : Type u} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
  (φ : ∀ i, M.val.obj (op (B i)) →ₗ[Γ(X, B i)] N.val.obj (op (B i)))
  (hφ : ∀ i j (h : B j ≤ B i) (s : M.val.obj (op (B i))),
    N.val.map (homOfLE h).op (φ i s) = φ j (M.val.map (homOfLE h).op s))

/-- The actual linear maps form an additive natural transformation on the basis. -/
def basisMorphism :
    (inducedFunctor B).op ⋙ M.val.presheaf ⟶
      (inducedFunctor B).op ⋙ N.val.presheaf where
  app i := AddCommGrp.ofHom (φ i.unop).toAddMonoidHom
  naturality := by
    intro i j f
    ext s
    exact (hφ i.unop j.unop f.unop.le s).symm

/-- The canonical sheaf extension of those actual additive basis maps. -/
def additiveMorphism : M.val.presheaf ⟶ N.val.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.val.presheaf
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N) hB
    (basisMorphism M N B φ hφ)

theorem additiveMorphism_app (i : ι) (s : M.val.obj (op (B i))) :
    (additiveMorphism M N B hB φ hφ).app (op (B i)) s = φ i s := by
  rw [additiveMorphism, TopCat.Sheaf.extend_hom_app]
  rfl

/-- Its restriction to each subordinate basis open is the original map. -/
theorem additiveMorphism_restrict (U : X.Opens) (i : ι) (h : B i ≤ U)
    (s : M.val.obj (op U)) :
    N.val.map (homOfLE h).op ((additiveMorphism M N B hB φ hφ).app (op U) s) =
      φ i (M.val.map (homOfLE h).op s) := by
  have hn := ConcreteCategory.congr_hom
    ((additiveMorphism M N B hB φ hφ).naturality (homOfLE h).op) s
  change (additiveMorphism M N B hB φ hφ).app (op (B i))
    (M.val.map (homOfLE h).op s) = _ at hn
  rw [additiveMorphism_app] at hn
  exact hn.symm

include hB hφ

/-- Linearity descends through the actual basis cover of every original open. -/
theorem additiveMorphism_smul (U : X.Opens) (r : Γ(X, U)) (s : M.val.obj (op U)) :
    ((additiveMorphism M N B hB φ hφ).app (op U) (r • s) : N.val.obj (op U)) =
      @SMul.smul Γ(X, U) (N.val.obj (op U)) inferInstance r
        ((additiveMorphism M N B hB φ hφ).app (op U) s) := by
  let I := {i : ι // B i ≤ U}
  have hcover : U ≤ ⨆ i : I, B i.val := by
    intro x hx
    obtain ⟨V, ⟨i, rfl⟩, hxi, hiU⟩ :=
      (Opens.isBasis_iff_nbhd.mp hB) hx
    exact Opens.mem_iSup.mpr ⟨⟨i, hiU⟩, hxi⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    (fun i : I => B i.val) U (fun i => homOfLE i.property) hcover
  intro i
  change N.val.map (homOfLE i.property).op
      ((additiveMorphism M N B hB φ hφ).app (op U) (r • s)) =
    N.val.map (homOfLE i.property).op
      (@SMul.smul Γ(X, U) (N.val.obj (op U)) inferInstance r
        ((additiveMorphism M N B hB φ hφ).app (op U) s))
  rw [additiveMorphism_restrict]
  let t : N.val.obj (op U) := (additiveMorphism M N B hB φ hφ).app (op U) s
  refine Eq.trans ?_ (N.val.map_smul (homOfLE i.property).op r t).symm
  rw [M.val.map_smul, map_smul]
  exact congrArg
    (fun q : N.val.obj (op (B i.val)) => (X.ringCatSheaf.val.map (homOfLE i.property).op r) • q)
    (additiveMorphism_restrict M N B hB φ hφ U i.val i.property s).symm

/-- The constructed morphism of the original module sheaves. -/
def morphism : M ⟶ N where
  val := {
    app U := ModuleCat.ofHom {
      toFun := fun s => ((additiveMorphism M N B hB φ hφ).app U s : N.val.obj U)
      map_add' := map_add _
      map_smul' := additiveMorphism_smul M N B hB φ hφ U.unop }
    naturality := by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact ConcreteCategory.congr_hom
        ((additiveMorphism M N B hB φ hφ).naturality f) s }

/-- Descent retains each original sectionwise linear map exactly. -/
theorem morphism_app (i : ι) (s : M.val.obj (op (B i))) :
    (morphism M N B hB φ hφ).val.app (op (B i)) s = φ i s :=
  additiveMorphism_app M N B hB φ hφ i s

end KltDP.Geometry.SchemeModuleHomOnBasis

#check @KltDP.Geometry.SchemeModuleHomOnBasis.morphism
#print axioms KltDP.Geometry.SchemeModuleHomOnBasis.morphism
