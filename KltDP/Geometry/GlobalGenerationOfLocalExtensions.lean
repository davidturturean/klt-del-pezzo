import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.Positivity
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Global generation from extensions of actual local generators

If the generators on an original open cover extend to original global
sections, those extensions generate the original sheaf. The proof uses
the actual free-sheaf epimorphisms on the Over sites, then the original
sheaf separation axiom. No affine, coherent, or finiteness assumption is
needed for this categorical gluing step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GlobalGenerationOfLocalExtensions

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

private abbrev res (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U) :=
  M.val.map (homOfLE hVU).op

private theorem res_comp (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (t : M.val.obj (op U)) :
    res M hWV (res M hVU t) = res M (hWV.trans hVU) t := by
  change (M.val.presheaf.map (homOfLE hVU).op ≫
    M.val.presheaf.map (homOfLE hWV).op) t = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- Original global sections determine their compatible restriction family. -/
def sectionOfTop (M : X.Modules) (t : M.val.obj (op (⊤ : X.Opens))) : M.sections :=
  PresheafOfModules.sectionsMk (fun V => res M (show V.unop ≤ ⊤ from le_top) t)
    (fun {V W} j => by
      change res M j.unop.le (res M (show V.unop ≤ ⊤ from le_top) t) = _
      exact res_comp M le_top j.unop.le t)

@[simp]
theorem sectionOfTop_top (M : X.Modules) (t : M.val.obj (op (⊤ : X.Opens))) :
    (sectionOfTop M t).val (op ⊤) = t := by
  change M.val.presheaf.map (𝟙 (op (⊤ : X.Opens))) t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

private theorem hom_ext_of_over_cover {M N : X.Modules} (a b : M ⟶ N)
    {I : Type u} (U : I → X.Opens) (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (hab : ∀ i, (_root_.SheafOfModules.overFunctor X.ringCatSheaf (U i)).map a =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf (U i)).map b) : a = b := by
  ext V t
  let W (i : I) := V.unop ⊓ U i
  have hW : V.unop ≤ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    W V.unop (fun _ => homOfLE inf_le_left) hW
  intro i
  have hi := congrArg (fun q => q.val.app
    (op (Over.mk (homOfLE (show W i ≤ U i from inf_le_right))))
      (res M (show W i ≤ V.unop from inf_le_left) t)) (hab i)
  change a.val.app (op (W i)) (res M inf_le_left t) =
    b.val.app (op (W i)) (res M inf_le_left t) at hi
  exact (PresheafOfModules.naturality_apply a.val (homOfLE inf_le_left).op t).symm.trans
    (hi.trans (PresheafOfModules.naturality_apply b.val (homOfLE inf_le_left).op t))

/-- A family containing an extension of each actual local generator gives
an epimorphism from the original free sheaf. -/
theorem epi_of_generator_extensions (M : X.Modules)
    {I J : Type u} (U : I → X.Opens) (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (G : ∀ i, (M.over (U i)).GeneratingSections) (T : J → M.sections)
    (hT : ∀ i, ∀ k : (G i).I, ∃ j : J,
      (T j).val (op (U i)) = ((G i).s k).val (op (Over.mk (𝟙 (U i))))) :
    Epi (M.freeHomEquiv.symm T) where
  left_cancellation {N} a b hab := by
    have hsection (j : J) :
        _root_.SheafOfModules.sectionsMap a (T j) =
          _root_.SheafOfModules.sectionsMap b (T j) := by
      have h := congrArg (fun q => N.freeHomEquiv q j) hab
      simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
        Equiv.apply_symm_apply] using h
    apply hom_ext_of_over_cover a b U hcover
    intro i
    let F := _root_.SheafOfModules.overFunctor X.ringCatSheaf (U i)
    apply (cancel_epi (G i).π).mp
    apply (N.over (U i)).freeHomEquiv.injective
    funext k
    simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
      _root_.SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    obtain ⟨j, hj⟩ := hT i k
    let v : V.unop ⟶ Over.mk (𝟙 (U i)) := Over.homMk V.unop.hom
    have hlocal : ((G i).s k).val V = (T j).val (op V.unop.left) := by
      calc
        _ = M.val.map V.unop.hom.op
            (((G i).s k).val (op (Over.mk (𝟙 (U i))))) :=
          (((G i).s k).property v.op).symm
        _ = M.val.map V.unop.hom.op ((T j).val (op (U i))) :=
          congrArg (M.val.map V.unop.hom.op) hj.symm
        _ = _ := (T j).property V.unop.hom.op
    change a.val.app (op V.unop.left) (((G i).s k).val V) =
      b.val.app (op V.unop.left) (((G i).s k).val V)
    rw [hlocal]
    exact congrArg (fun s : N.sections => s.val (op V.unop.left)) (hsection j)

/-- Extension of all actual local generators implies original global
generation. The global free family and epimorphism are constructed. -/
theorem isGloballyGenerated (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (G : ∀ i, (M.over (U i)).GeneratingSections)
    (hG : ∀ i, ∀ k : (G i).I, ∃ t : M.val.obj (op (⊤ : X.Opens)),
      res M (show U i ≤ ⊤ from le_top) t =
        ((G i).s k).val (op (Over.mk (𝟙 (U i))))) :
    Positivity.IsGloballyGenerated M := by
  let T := sectionOfTop M
  refine ⟨M.val.obj (op (⊤ : X.Opens)), M.freeHomEquiv.symm T, ?_⟩
  apply epi_of_generator_extensions M U hcover G T
  intro i k
  exact hG i k

end KltDP.Geometry.GlobalGenerationOfLocalExtensions
