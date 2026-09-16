import KltDP.Compatibility.SheafGeneratorSubmodule
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Some generator of a locally trivial line has a unit germ

On the Over-site of an open `U`, the sections whose germs at a fixed point
lie in a specified stalk ideal form an actual module subsheaf of the unit.
Restriction stability is the germ restriction identity, and locality uses
the actual covering sieve to choose a neighbourhood containing the point.

A generating family of the unit cannot lie in the maximal-ideal subsheaf:
the accepted categorical submodule argument would put `1` in that ideal.
Thus at least one generator has a unit germ.  The conclusion is a unit in
the original local ring, stronger than a merely nonzero ring element.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.GeneratingUnitGerm

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) (U : X.Opens) (x : X)

/-- The actual ideal subsheaf on the Over-site whose sections have germs
in the specified ideal of the original stalk. -/
def pointIdealOver (I : Ideal (X.presheaf.stalk x)) :
    (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).Submodule where
  obj V := {
    carrier := {s | ∀ hx : x ∈ V.unop.left, X.presheaf.germ V.unop.left x hx s ∈ I}
    zero_mem' := by intro hx; simpa only [map_zero] using I.zero_mem
    add_mem' := by
      intro a b ha hb hx
      simpa only [map_add] using I.add_mem (ha hx) (hb hx)
    smul_mem' := by
      intro a b hb hx
      change Γ(X, V.unop.left) at a b
      change X.presheaf.germ V.unop.left x hx (a * b) ∈ I
      rw [map_mul]
      exact I.mul_mem_left _ (hb hx) }
  map {V W} f := by
    intro s hs
    change ∀ hx : x ∈ W.unop.left,
      X.presheaf.germ W.unop.left x hx (X.presheaf.map f.unop.left.op s) ∈ I
    intro hx
    rw [X.presheaf.germ_res_apply]
    exact hs _
  isSheaf {V} s hs := by
    intro hx
    obtain ⟨W, i, hi, hxW⟩ := hs x hx
    have hi' := (Sieve.overEquiv_iff _ i).1 hi
    change ∀ hw : x ∈ W,
      X.presheaf.germ W x hw (X.presheaf.map i.op s) ∈ I at hi'
    simpa only [X.presheaf.germ_res_apply] using hi' hxW

/-- At any specified point of an open, some member of a generating family
of the unit has a coefficient with unit germ. -/
theorem exists_generator_isUnit_germ (hx : x ∈ U)
    (G : (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)).GeneratingSections) :
    ∃ i : G.I, IsUnit (X.presheaf.germ U x hx
      ((G.s i).val (op (Over.mk (𝟙 U))))) := by
  classical
  by_contra h
  push_neg at h
  let P := pointIdealOver X U x (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have hG : ∀ (i : G.I) (V : (Over U)ᵒᵖ), (G.s i).val V ∈ P.obj V := by
    intro i V
    change ∀ hxV : x ∈ V.unop.left,
      X.presheaf.germ V.unop.left x hxV ((G.s i).val V) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x)
    intro hxV
    let j : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom
    have hn := (G.s i).property j.op
    change X.presheaf.map V.unop.hom.op ((G.s i).val (op (Over.mk (𝟙 U)))) =
      (G.s i).val V at hn
    have hg : X.presheaf.germ V.unop.left x hxV ((G.s i).val V) =
        X.presheaf.germ U x hx ((G.s i).val (op (Over.mk (𝟙 U)))) := by
      calc
        _ = X.presheaf.germ V.unop.left x hxV
            (X.presheaf.map V.unop.hom.op ((G.s i).val (op (Over.mk (𝟙 U))))) :=
          congrArg (fun r : Γ(X, V.unop.left) => X.presheaf.germ V.unop.left x hxV r) hn.symm
        _ = _ := X.presheaf.germ_res_apply V.unop.hom x hxV _
    rw [hg]
    exact (IsLocalRing.mem_maximalIdeal _).2 (h i)
  have h1 := KltDP.SheafGeneratorSubmodule.section_mem_of_generators_mem G P hG
    (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  have hz : (1 : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    simpa only [map_one] using h1 hx
  exact (IsLocalRing.not_mem_maximalIdeal.mpr isUnit_one) hz

end KltDP.Geometry.GeneratingUnitGerm
