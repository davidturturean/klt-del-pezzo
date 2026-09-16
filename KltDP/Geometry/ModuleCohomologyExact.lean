import KltDP.Geometry.ModuleCohomology
import KltDP.Compatibility.SheafModuleExactness
import KltDP.Compatibility.SheafCohomologyExact

/-!
# Exact cohomology sequences for actual scheme modules

The original short exact sequence is a sequence in `X.Modules`. Exactness
of the underlying additive sheaves is proved by the forgetful-functor
adapter. The cohomology groups and their maps are the existing Ext-based
`H` and `zariskiFunctor`; neither exactness of the underlying sequence nor
exactness of its cohomology is an additional hypothesis.

The connecting map here is additive. Its canonical scalar linearity,
coherent cohomology finiteness and Euler additivity are separate steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)

/-- The actual connecting homomorphism attached to a short exact sequence
of modules on the original scheme. -/
def connecting (n : ℕ) : H S.X₃ n →+ H S.X₁ (n + 1) :=
  CategoryTheory.Sheaf.H.δ
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl

/-- The six consecutive actual cohomology groups and their induced maps. -/
def longSequence (n : ℕ) : ComposableArrows AddCommGrp.{u} 5 :=
  ComposableArrows.mk₅
    ((zariskiFunctor X n).map S.f)
    ((zariskiFunctor X n).map S.g)
    (AddCommGrp.ofHom (connecting S hS n))
    ((zariskiFunctor X (n + 1)).map S.f)
    ((zariskiFunctor X (n + 1)).map S.g)

theorem longSequence_exact (n : ℕ) : (longSequence S hS n).Exact :=
  CategoryTheory.Sheaf.H.longSequence_exact
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl

include hS in
/-- Elementwise exactness at the middle coefficient module in any degree. -/
theorem exact_middle (n : ℕ) (x : H S.X₂ n)
    (hx : (zariskiFunctor X n).map S.g x = 0) :
    ∃ y : H S.X₁ n, (zariskiFunctor X n).map S.f y = x :=
  CategoryTheory.Sheaf.H.longSequence_exact₂
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n x hx

/-- The obstruction to lifting a cohomology class is its connecting class. -/
theorem exact_before_connecting (n : ℕ) (x : H S.X₃ n)
    (hx : connecting S hS n x = 0) :
    ∃ y : H S.X₂ n, (zariskiFunctor X n).map S.g y = x :=
  CategoryTheory.Sheaf.H.longSequence_exact₃
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl x hx

/-- Exactness in the next degree at the first coefficient module. -/
theorem exact_after_connecting (n : ℕ) (x : H S.X₁ (n + 1))
    (hx : (zariskiFunctor X (n + 1)).map S.f x = 0) :
    ∃ y : H S.X₃ n, connecting S hS n y = x :=
  CategoryTheory.Sheaf.H.longSequence_exact₁
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n (n + 1) rfl x hx

include hS in
/-- Vanishing at both ends implies vanishing for the middle module. -/
theorem subsingleton_middle (n : ℕ)
    (hleft : Subsingleton (H S.X₁ n)) (hright : Subsingleton (H S.X₃ n)) :
    Subsingleton (H S.X₂ n) :=
  CategoryTheory.Sheaf.H.subsingleton_H_X₂_of_shortExact
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS) n hleft hright

include hS in
/-- H1 vanishing gives surjectivity on actual global sections. -/
theorem sections_surjective_of_hOne_zero [Subsingleton (H S.X₁ 1)] :
    Function.Surjective (S.g.val.app (.op (⊤ : Opens X))) := by
  letI : Subsingleton (((S.map (SheafOfModules.toSheaf X.ringCatSheaf)).X₁).H 1) :=
    inferInstanceAs (Subsingleton (H S.X₁ 1))
  exact CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    (KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS)
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))

end KltDP.Geometry.ModuleCohomology
