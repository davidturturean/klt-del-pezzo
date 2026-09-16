/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SheafOverTerminal
import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Compatibility.SheafModuleEpiStalk
import KltDP.Compatibility.FreeSheafSections
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Actual finite-type module sheaves on a one-point space

A covering family on a nonempty one-point space contains the whole space.
The original finite local generators therefore give an actual finite-free
epimorphism onto the original sheaf. The original local lifting theorem makes
that epimorphism surjective on global sections, and evaluation of the original
finite free sheaf is a finite module.

The proof uses no quasicoherence, chosen global generators, section-surjectivity
premise, or finiteness conclusion as input. For a field spectrum these facts
will apply to the actual global-section module with its original scalar action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.SheafModuleFiniteTypeOnPoint

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- Restriction to the terminal open recovers the original restricted morphism. -/
theorem overTop_map_homFromOverTerminal
    {M N : _root_.SheafOfModules.{u} R} (φ : M.over ⊤ ⟶ N.over ⊤) :
    (_root_.SheafOfModules.overFunctor R ⊤).map
        (KltDP.SheafOfModules.homFromOverTerminal R ⊤ isTerminalTop φ) = φ := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  rfl

local instance overTop_faithful :
    (_root_.SheafOfModules.overFunctor R ⊤).Faithful where
  map_injective {M N} f g h := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    exact congrArg
      (fun q : M.over ⊤ ⟶ N.over ⊤ =>
        q.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))) h

/-- An original generating family on the terminal Over-site gives an actual
free epimorphism on the original site, with the same generator index. -/
theorem exists_free_epi_of_overTop_generators (M : _root_.SheafOfModules.{u} R)
    (G : (M.over ⊤).GeneratingSections) :
    ∃ (p : _root_.SheafOfModules.free (R := R) G.I ⟶ M), Epi p := by
  let F := _root_.SheafOfModules.overFunctor R ⊤
  let e := _root_.SheafOfModules.mapFreeIso F G.I
    (_root_.SheafOfModules.unitOverIso (R := R) ⊤).symm
  let φ : (_root_.SheafOfModules.free (R := R) G.I).over ⊤ ⟶ M.over ⊤ :=
    e.inv ≫ G.π
  letI : Epi φ := inferInstanceAs (Epi (e.inv ≫ G.π))
  let p := KltDP.SheafOfModules.homFromOverTerminal R ⊤ isTerminalTop φ
  have hp : Epi (F.map p) := by
    change Epi ((_root_.SheafOfModules.overFunctor R ⊤).map
      (KltDP.SheafOfModules.homFromOverTerminal R ⊤ isTerminalTop φ))
    rw [overTop_map_homFromOverTerminal]
    infer_instance
  exact ⟨p, F.epi_of_epi_map hp⟩

variable [Subsingleton X] [Nonempty X]

/-- A nonempty open of the actual one-point space is the whole space. -/
theorem open_eq_top_of_mem (U : Opens X) (x : X) (hx : x ∈ U) : U = ⊤ := by
  apply top_unique
  intro y hy
  exact (Subsingleton.elim x y) ▸ hx

/-- The actual local finite generators include a generating family on the
whole space. This retains the original generator index and its finiteness. -/
theorem exists_finite_free_epi (M : _root_.SheafOfModules.{u} R)
    [_root_.SheafOfModules.IsFiniteType M] :
    ∃ (I : Type u) (_ : Finite I)
      (p : _root_.SheafOfModules.free (R := R) I ⟶ M), Epi p := by
  let q := M.localGeneratorsDataOfIsFiniteType
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨U, f, ⟨i, ⟨g⟩⟩, hxU⟩ := q.coversTop ⊤ x (by trivial)
  have hi : q.X i = ⊤ := open_eq_top_of_mem (q.X i) x (g.le hxU)
  have hG : ∃ G : (M.over ⊤).GeneratingSections, Finite G.I := by
    rw [← hi]
    exact ⟨q.generators i, inferInstance⟩
  obtain ⟨G, hfinite⟩ := hG
  obtain ⟨p, hp⟩ := exists_free_epi_of_overTop_generators M G
  exact ⟨G.I, hfinite, p, hp⟩

/-- An actual sheaf epimorphism on the one-point space is surjective on its
original global sections: its local lifts are already global. -/
theorem top_surjective_of_epi {M N : _root_.SheafOfModules.{u} R}
    (f : M ⟶ N) [Epi f] :
    Function.Surjective (f.val.app (op (⊤ : Opens X))) := by
  intro s
  let x : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨V, i, t, hxV, ht⟩ :=
    SheafModuleEpiStalk.exists_local_lift_of_epi f ⊤ s x (by trivial)
  have hV : V = ⊤ := open_eq_top_of_mem V x hxV
  subst V
  have hi : i = 𝟙 (⊤ : Opens X) := Subsingleton.elim _ _
  subst i
  refine ⟨t, ht.trans ?_⟩
  change N.val.map (𝟙 (op (⊤ : Opens X))) s = s
  exact ConcreteCategory.congr_hom (N.val.map_id (op ⊤)) s

/-- Finite type on a nonempty one-point space gives a finite module of actual
global sections over the original global section ring. -/
theorem top_finite_of_isFiniteType (M : _root_.SheafOfModules.{u} R)
    [_root_.SheafOfModules.IsFiniteType M] :
    Module.Finite (R.val.obj (op (⊤ : Opens X))) (M.val.obj (op ⊤)) := by
  obtain ⟨I, hI, p, hp⟩ := exists_finite_free_epi M
  letI : Finite I := hI
  letI : Fintype I := Fintype.ofFinite I
  letI : Epi p := hp
  let e := Compatibility.FreeSheafSections.freeEvalIso R I (op (⊤ : Opens X))
  letI : Module.Finite (R.val.obj (op (⊤ : Opens X)))
      ((_root_.SheafOfModules.free (R := R) I).val.obj (op ⊤)) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact Module.Finite.of_surjective (p.val.app (op ⊤)).hom (top_surjective_of_epi p)

end KltDP.SheafModuleFiniteTypeOnPoint
