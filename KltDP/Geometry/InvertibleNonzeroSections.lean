import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.TransitionUnitExtraction
import KltDP.Geometry.BaseFieldCohomology

/-!
# A nonzero map of original line bundles is injective on original sections

The accepted Cartier comparison embeds each original line bundle into the
original rational-function module. Thus restriction to a nonempty open is
injective. A nonzero sheaf morphism has a nonzero component on some common
rank-one chart, by the actual sheaf condition. On that chart the map is
multiplication by a nonzero element of the original integral section ring.
This gives injectivity on the original top-open sections and on original H0
with the existing base-field action. No section or morphism is constructed
from a numerical growth hypothesis here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleNonzeroSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology TransitionUnitExtraction

private theorem rankOne_injective_of_ne_zero
    {R P Q : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (eP : P ≃ₗ[R] R) (eQ : Q ≃ₗ[R] R) (g : P →ₗ[R] Q) (hg : g ≠ 0) :
    Function.Injective g := by
  have hrepr (x : P) : g x = eP x • g (eP.symm 1) := by
    have hx : eP x • eP.symm 1 = x := by
      apply eP.injective
      rw [eP.map_smul, eP.apply_symm_apply, smul_eq_mul, mul_one]
    rw [← g.map_smul, hx]
  have hc : eQ (g (eP.symm 1)) ≠ 0 := by
    intro hc
    have hz : g (eP.symm 1) = 0 := eQ.injective (hc.trans eQ.map_zero.symm)
    apply hg
    ext x
    simpa only [LinearMap.zero_apply, hrepr x, hz, smul_zero]
  have hcoord (x : P) : eQ (g x) = eP x * eQ (g (eP.symm 1)) := by
    rw [hrepr x, eQ.map_smul, smul_eq_mul]
  intro x y h
  apply eP.injective
  apply mul_right_cancel₀ hc
  exact (hcoord x).symm.trans ((congrArg eQ h).trans (hcoord y))

variable (X : Scheme.{u}) [IsIntegral X]

private theorem rational_restriction_injective {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) :
    Function.Injective ((rationalFunctionModule X).val.map i.op) := by
  intro s t h
  apply (rationalFunctionModuleSectionsEquiv X U).injective
  exact (rationalFunctionModuleSectionsEquiv_naturality X i s).symm.trans
    ((congrArg (rationalFunctionModuleSectionsEquiv X V) h).trans
      (rationalFunctionModuleSectionsEquiv_naturality X i t))

/-- Actual line-bundle sections are determined by restriction to a nonempty open. -/
theorem restriction_injective (L : InvertibleSheaf X) {U V : X.Opens}
    [Nonempty V] (i : V ⟶ U) : Function.Injective (L.obj.val.map i.op) := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  letI : Nonempty U := ⟨⟨v.val, i.le v.property⟩⟩
  obtain ⟨D, ⟨e⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  intro s t h
  apply ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv.injective
  apply Subtype.ext
  apply rational_restriction_injective X i
  have he : (cartierDivisorModule X D).val.map i.op (e.hom.val.app (op U) s) =
      (cartierDivisorModule X D).val.map i.op (e.hom.val.app (op U) t) :=
    (_root_.PresheafOfModules.naturality_apply e.hom.val i.op s).symm.trans
      ((congrArg (e.hom.val.app (op V)) h).trans
        (_root_.PresheafOfModules.naturality_apply e.hom.val i.op t))
  exact congrArg Subtype.val he

private theorem exists_nonzero_framed_component (L M : InvertibleSheaf X)
    (g : L.obj ⟶ M.obj) (hg : g ≠ 0) :
    ∃ (U : X.Opens) (_ : Nonempty U)
      (_ : L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
      (_ : M.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)),
      g.val.app (op U) ≠ 0 := by
  classical
  by_contra! h
  apply hg
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change g.val.app W s = 0
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M.obj).cond
  intro x hx
  have hxL : x ∈ ⨆ i, L.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X L]
    trivial
  have hxM : x ∈ ⨆ i, M.localTrivializations.X i := by
    rw [invertibleSheafUnits_cover X M]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxL
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxM
  let V : X.Opens := W.unop ⊓ L.localTrivializations.X i ⊓ M.localTrivializations.X j
  have hxV : x ∈ V := ⟨⟨hx, hxi⟩, hxj⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let eL := L.localTrivializations.unitIsoOver i
    (homOfLE (show V ≤ L.localTrivializations.X i from inf_le_left.trans inf_le_right))
  let eM := M.localTrivializations.unitIsoOver j
    (homOfLE (show V ≤ M.localTrivializations.X j from inf_le_right))
  let hVW : V ≤ W.unop := inf_le_left.trans inf_le_left
  refine ⟨V, hVW, hxV, ?_⟩
  change M.obj.val.map (homOfLE hVW).op (g.val.app W s) =
    M.obj.val.map (homOfLE hVW).op 0
  rw [map_zero, ← _root_.PresheafOfModules.naturality_apply,
    h V inferInstance eL eM]
  rfl

/-- Every nonzero original line-bundle map is injective on the actual top-open sections. -/
theorem globalSections_injective (L M : InvertibleSheaf X)
    (g : L.obj ⟶ M.obj) (hg : g ≠ 0) :
    Function.Injective (globalSectionsLinearMap g) := by
  obtain ⟨U, hU, eL, eM, hne⟩ := exists_nonzero_framed_component X L M g hg
  letI := hU
  have hne' : (g.val.app (op U)).hom ≠ 0 := by
    intro hzero
    exact hne (ModuleCat.hom_ext hzero)
  have hi : Function.Injective (g.val.app (op U)) :=
    rankOne_injective_of_ne_zero
      (overTrivializationSectionEquiv X L.obj U eL (𝟙 U))
      (overTrivializationSectionEquiv X M.obj U eM (𝟙 U))
      (g.val.app (op U)).hom hne'
  intro s t h
  apply restriction_injective X L (homOfLE (show U ≤ ⊤ from le_top))
  apply hi
  rw [_root_.PresheafOfModules.naturality_apply,
    _root_.PresheafOfModules.naturality_apply]
  exact congrArg (M.obj.val.map (homOfLE (show U ≤ ⊤ from le_top)).op) h

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The unchanged map on actual H0 is injective with the original base-field scalar action. -/
theorem baseHZero_injective (L M : InvertibleSheaf X)
    (g : L.obj ⟶ M.obj) (hg : g ≠ 0) :
    letI := baseModule f L.obj 0
    letI := baseModule f M.obj 0
    Function.Injective (baseLinearMap f 0 g) := by
  letI := baseModule f L.obj 0
  letI := baseModule f M.obj 0
  intro s t h
  apply (hZeroEquivGlobalSections L.obj).injective
  apply globalSections_injective X L M g hg
  exact (hZeroEquivGlobalSections_naturality g s).trans
    ((congrArg (hZeroEquivGlobalSections M.obj) h).trans
      (hZeroEquivGlobalSections_naturality g t).symm)

end KltDP.Geometry.InvertibleNonzeroSections
