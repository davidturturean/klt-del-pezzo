import KltDP.Geometry.GlobalGenerationOfLocalExtensions
import KltDP.Geometry.ModuleCohomologyExact
import KltDP.Geometry.SchemeModulePullbackUnit
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! Global generation from the original short exact sequence and actual H1 vanishing.
The original quotient sections are lifted by cohomology; exactness then proves
that all original global sections of the middle sheaf generate it. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.GlobalGenerationShortExact

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)

include hS in
/-- Actual H1 vanishing lifts compatible global section families, not only top values. -/
theorem sectionsMap_surjective (hH1 : Subsingleton (ModuleCohomology.H S.X₁ 1)) :
    Function.Surjective (_root_.SheafOfModules.sectionsMap S.g) := by
  letI := hH1
  intro s
  obtain ⟨v, hv⟩ := ModuleCohomology.sections_surjective_of_hOne_zero S hS (s.val (op ⊤))
  refine ⟨(schemeModuleSectionsEquivTop S.X₂).symm v, ?_⟩
  apply (schemeModuleSectionsEquivTop S.X₃).injective
  change S.g.val.app (op ⊤)
    ((schemeModuleSectionsEquivTop S.X₂) ((schemeModuleSectionsEquivTop S.X₂).symm v)) =
      s.val (op ⊤)
  rw [Equiv.apply_symm_apply]
  exact hv

include hS in
/-- Globally generated ends and vanishing H1 of the left term generate the original middle. -/
theorem isGloballyGenerated
    (hleft : Positivity.IsGloballyGenerated S.X₁)
    (hright : Positivity.IsGloballyGenerated S.X₃)
    (hH1 : Subsingleton (ModuleCohomology.H S.X₁ 1)) :
    Positivity.IsGloballyGenerated S.X₂ := by
  obtain ⟨I₁, π₁, hπ₁⟩ := hleft
  obtain ⟨I₃, π₃, hπ₃⟩ := hright
  letI := hπ₁
  letI := hπ₃
  letI : Epi S.g := hS.epi_g
  refine ⟨S.X₂.sections, S.X₂.freeHomEquiv.symm id, ?_⟩
  constructor
  intro M a b hab
  have hsections (s : S.X₂.sections) :
      _root_.SheafOfModules.sectionsMap a s = _root_.SheafOfModules.sectionsMap b s := by
    have h := congrArg (fun q => M.freeHomEquiv q s) hab
    simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
      Equiv.apply_symm_apply, id_eq] using h
  have hfirst : S.f ≫ a = S.f ≫ b := by
    apply (cancel_epi π₁).mp
    have hπ : (π₁ ≫ S.f) ≫ a = (π₁ ≫ S.f) ≫ b := by
      apply M.freeHomEquiv.injective
      funext j
      simpa only [_root_.SheafOfModules.freeHomEquiv_comp_apply] using
        hsections (S.X₂.freeHomEquiv (π₁ ≫ S.f) j)
    simpa only [Category.assoc] using hπ
  have hzero : S.f ≫ (a - b) = 0 := by
    rw [Preadditive.comp_sub, hfirst, sub_self]
  obtain ⟨q, hq⟩ := hS.exact.desc' (a - b) hzero
  have hqzero : q = 0 := by
    apply (cancel_epi π₃).mp
    apply M.freeHomEquiv.injective
    funext j
    simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply]
    obtain ⟨s, hs⟩ := sectionsMap_surjective S hS hH1 (S.X₃.freeHomEquiv π₃ j)
    rw [← hs]
    apply _root_.PresheafOfModules.sections_ext
    intro U
    change q.val.app U (S.g.val.app U (s.val U)) = 0
    have hx := congrArg (fun d : S.X₂ ⟶ M => d.val.app U (s.val U)) hq
    change q.val.app U (S.g.val.app U (s.val U)) =
      a.val.app U (s.val U) - b.val.app U (s.val U) at hx
    rw [hx]
    exact sub_eq_zero.mpr
      (congrArg (fun t : M.sections => t.val U) (hsections s))
  rw [hqzero, CategoryTheory.Limits.comp_zero] at hq
  exact sub_eq_zero.mp hq.symm

#print axioms sectionsMap_surjective
#print axioms isGloballyGenerated

end KltDP.Geometry.GlobalGenerationShortExact
