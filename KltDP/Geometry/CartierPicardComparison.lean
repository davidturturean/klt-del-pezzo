import KltDP.Geometry.CartierPicardAssembly

/-!
# The actual Cartier-to-Picard comparison on an integral scheme

The rational coordinate maps define a morphism into the actual rational
function module. For the divisor assembled from inverse generator values,
local equations put its image in O(D). On each trivialization chart this
map is the composite of the original line-bundle coordinates and the
proved coordinates of O(D), so it is bijective there. The existing
sheafification-on-a-cover theorem supplies an actual sheaf isomorphism.

Consequently every actual Picard class is represented by O(D). Together
with the previously proved principal kernel, this identifies the actual
Cartier class group with the actual Picard group. No representative,
comparison isomorphism, or surjectivity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

private theorem empty_open_sectionRing_subsingleton (V : X.Opens)
    (hV : ¬ Nonempty V) : Subsingleton Γ(X, V) := by
  have hbot : V = ⊥ := by
    apply SetLike.ext
    intro x
    exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
  subst V
  exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

section Coordinates

variable (M : X.Modules) (U : X.Opens) [Nonempty U]
  (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))

/-- The original rational coordinate, regarded as a section of the
actual rational-function module; the empty open uses its zero module. -/
def lineBundleRationalApp (V : X.Opens) :
    M.val.obj (op V) →ₗ[Γ(X, V)] (rationalFunctionModule X).val.obj (op V) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    exact (rationalFunctionModuleSectionsEquiv X V).symm.toLinearMap.comp
      (lineBundleGenericCoordinate X M U e V)
  · exact 0

theorem lineBundleRationalApp_field (V : X.Opens) [Nonempty V]
    (s : M.val.obj (op V)) :
    rationalFunctionModuleSectionsEquiv X V (lineBundleRationalApp X M U e V s) =
      lineBundleGenericCoordinate X M U e V s := by
  classical
  simp only [lineBundleRationalApp, dif_pos (inferInstance : Nonempty V),
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The rational-section maps commute with actual restriction maps,
including restrictions to the empty open. -/
theorem lineBundleRationalApp_naturality {V W : X.Opens} (i : W ⟶ V)
    (s : M.val.obj (op V)) :
    lineBundleRationalApp X M U e W (M.val.map i.op s) =
      (rationalFunctionModule X).val.map i.op (lineBundleRationalApp X M U e V s) := by
  classical
  by_cases hW : Nonempty W
  · letI := hW
    letI : Nonempty V := by
      obtain ⟨⟨x, hx⟩⟩ := hW
      exact ⟨⟨x, i.le hx⟩⟩
    apply (rationalFunctionModuleSectionsEquiv X W).injective
    rw [lineBundleRationalApp_field, rationalFunctionModuleSectionsEquiv_naturality,
      lineBundleRationalApp_field]
    exact lineBundleGenericCoordinate_naturality X M U e i s
  · letI := empty_open_sectionRing_subsingleton X W hW
    letI : Subsingleton ((rationalFunctionModule X).val.obj (op W)) :=
      Module.subsingleton Γ(X, W) _
    exact Subsingleton.elim _ _

/-- The actual module-sheaf morphism induced by the rational coordinates. -/
def lineBundleToRationalFunctions : M ⟶ rationalFunctionModule X :=
  _root_.SheafOfModules.Hom.mk {
    app V := ModuleCat.ofHom
      (X := M.val.obj V) (Y := (rationalFunctionModule X).val.obj V)
      (lineBundleRationalApp X M U e V.unop)
    naturality := by
      intro V W i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact lineBundleRationalApp_naturality X M U e i.unop s }

variable [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M]
  (D : CartierDivisor X)
  (hD : ∀ c : LineBundleTrivializationChart X M,
    (cartierDivisorSheaf X).val.map
        (homOfLE (show c.openSet ≤ ⊤ from le_top)).op D =
      cartierEquationClassHom X c.openSet
        (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹)))

include hD

/-- The assembled divisor has the stated inverse-generator equation on
every nonempty subopen of each original trivialization chart. -/
theorem lineBundleCartierEquation_restrict (c : LineBundleTrivializationChart X M)
    {V : X.Opens} [Nonempty V] (i : V ⟶ c.openSet) :
    cartierEquationClassHom X V
        (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹)) =
      (cartierDivisorSheaf X).val.map
        (homOfLE (show V ≤ ⊤ from le_top)).op D :=
  cartierGlobalEquation_restrict X D i _ (hD c).symm

/-- Rational coordinates lie in the actual principal fractional module
on every equation chart of the assembled divisor. -/
theorem lineBundleGenericCoordinate_mem_equation (V : X.Opens) [Nonempty V]
    (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X V (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show V ≤ ⊤ from le_top)).op D)
    (s : M.val.obj (op V)) :
    lineBundleGenericCoordinate X M U e V s ∈ principalEquationSubmodule X V f := by
  apply mem_principalEquationSubmodule_of_locally_mem X V f
  intro x hx
  obtain ⟨W, j, hW, hxW⟩ := lineBundleTrivializationCharts_coversTop X M V x hx
  obtain ⟨c, ⟨i⟩⟩ := hW
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  refine ⟨W, j, hxW, ?_⟩
  have hclass := (lineBundleCartierEquation_restrict X M U e D hD c i).trans
    (cartierGlobalEquation_restrict X D j f hf).symm
  have heq := principalEquationSubmodule_eq_of_class_eq X W
    ((lineBundleChartValueUnit X M U e c)⁻¹) f hclass
  rw [← heq]
  rw [← lineBundleGenericCoordinate_naturality X M U e j s,
    lineBundleGenericCoordinate_factor_chart X M U e c i]
  have hm := (principalEquationSubmoduleEquiv X W
    ((lineBundleChartValueUnit X M U e c)⁻¹)
    (overTrivializationSectionEquiv X M c.openSet c.trivialization i
      (M.val.map j.op s))).property
  simpa only [principalEquationSubmoduleEquiv_apply, inv_inv,
    lineBundleChartValueUnit_val] using hm

/-- The rational-section morphism lands in the actual defining
submodule of O(D), by the proved local equation membership. -/
theorem lineBundleRationalApp_mem_cartier (V : X.Opens) (s : M.val.obj (op V)) :
    lineBundleRationalApp X M U e V s ∈ cartierSectionSubmodule X D V := by
  intro W i hW
  letI := hW
  intro f hf
  rw [← lineBundleRationalApp_naturality, lineBundleRationalApp_field]
  exact lineBundleGenericCoordinate_mem_equation X M U e D hD W f hf _

/-- The actual rational-coordinate map with codomain restricted to O(D). -/
def lineBundleToCartierModule : M ⟶ cartierDivisorModule X D :=
  _root_.SheafOfModules.Hom.mk {
    app V := ModuleCat.ofHom ((lineBundleRationalApp X M U e V.unop).codRestrict
      (cartierSectionSubmodule X D V.unop)
      (lineBundleRationalApp_mem_cartier X M U e D hD V.unop))
    naturality := by
      intro V W i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      exact lineBundleRationalApp_naturality X M U e i.unop s }

/-- On a nonempty trivialization subopen, the morphism is precisely the
composite of the two actual coordinate equivalences. -/
theorem lineBundleToCartierModule_app_eq_coordinates
    (c : LineBundleTrivializationChart X M) {V : X.Opens} [Nonempty V]
    (i : V ⟶ c.openSet) (s : M.val.obj (op V)) :
    (lineBundleToCartierModule X M U e D hD).val.app (op V) s =
      cartierEquationSectionEquiv X D V ((lineBundleChartValueUnit X M U e c)⁻¹)
        (lineBundleCartierEquation_restrict X M U e D hD c i)
        (overTrivializationSectionEquiv X M c.openSet c.trivialization i s) := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X V).injective
  change rationalFunctionModuleSectionsEquiv X V (lineBundleRationalApp X M U e V s) = _
  rw [lineBundleRationalApp_field, cartierEquationSectionEquiv_apply_field,
    inv_inv, lineBundleChartValueUnit_val]
  exact lineBundleGenericCoordinate_factor_chart X M U e c i s

/-- The original comparison is locally bijective on the actual rank-one
atlas; the empty subopen case uses its zero section modules. -/
theorem lineBundleToCartierModule_mem_sheafificationW :
    PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.val)
      (lineBundleToCartierModule X M U e D hD).val := by
  apply PresheafOfModules.sheafificationW_of_bijective_on_coversTop
    (R := X.ringCatSheaf) (lineBundleToCartierModule X M U e D hD).val
    (fun c : LineBundleTrivializationChart X M => c.openSet)
    (lineBundleTrivializationCharts_coversTop X M)
  intro c V i
  classical
  by_cases hV : Nonempty V
  · letI := hV
    let a := overTrivializationSectionEquiv X M c.openSet c.trivialization i
    let b := cartierEquationSectionEquiv X D V
      ((lineBundleChartValueUnit X M U e c)⁻¹)
      (lineBundleCartierEquation_restrict X M U e D hD c i)
    have heq : (fun s => (lineBundleToCartierModule X M U e D hD).val.app (op V) s) =
        (fun s => (a ≪≫ₗ b) s) := by
      funext s
      exact lineBundleToCartierModule_app_eq_coordinates X M U e D hD c i s
    exact (congrArg Function.Bijective heq).mpr (a ≪≫ₗ b).bijective
  · letI := empty_open_sectionRing_subsingleton X V hV
    letI : Subsingleton (M.val.obj (op V)) := Module.subsingleton Γ(X, V) _
    letI : Subsingleton ((cartierDivisorModule X D).val.obj (op V)) :=
      Module.subsingleton Γ(X, V) _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The proved local bijectivity gives an actual isomorphism M ≅ O(D).
The counits are the established comparisons for sheafifying actual sheaves. -/
def lineBundleCartierIso : M ≅ cartierDivisorModule X D := by
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (lineBundleToCartierModule X M U e D hD).val) :=
    (PresheafOfModules.sheafificationW_iff (𝟙 X.ringCatSheaf.val) _).mp
      (lineBundleToCartierModule_mem_sheafificationW X M U e D hD)
  exact (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).symm ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (lineBundleToCartierModule X M U e D hD).val) ≪≫
    PresheafOfModules.sheafificationForgetIso X.ringCatSheaf (cartierDivisorModule X D)

end Coordinates

/-- Every actual locally free rank-one module sheaf on an integral
scheme is O(D) for an actual global Cartier divisor. -/
theorem exists_cartierDivisor_module_iso (M : X.Modules)
    [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M] :
    ∃ D : CartierDivisor X, Nonempty (M ≅ cartierDivisorModule X D) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := exists_genericPoint_trivialization X M
  letI : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  obtain ⟨D, hD⟩ := exists_cartierDivisor_of_lineBundle X M U e
  exact ⟨D, ⟨lineBundleCartierIso X M U e D hD⟩⟩

/-- Every element of the actual Picard group is represented by the
constructed line bundle of an actual Cartier divisor. -/
theorem cartierPicardClass_surjective : Function.Surjective (cartierPicardClass X) := by
  intro c
  letI := Scheme.Modules.monoidalCategory X
  obtain ⟨M, hM, hclass⟩ := exists_invertible_representative_of_picard X c
  letI := hM
  obtain ⟨D, ⟨a⟩⟩ := exists_cartierDivisor_module_iso X M
  refine ⟨D, ?_⟩
  apply Units.ext
  change (cartierPicardClass X D : Skeleton X.Modules) = (c : Skeleton X.Modules)
  rw [cartierPicardClass_val, ← hclass]
  exact Quotient.sound ⟨a.symm⟩

/-- The geometric additive Cartier-to-Picard homomorphism is surjective. -/
theorem cartierPicardHom_surjective : Function.Surjective (cartierPicardHom X) := by
  intro c
  obtain ⟨D, hD⟩ := cartierPicardClass_surjective X c.toMul
  exact ⟨D, congrArg Additive.ofMul hD⟩

/-- The descended Cartier class map is injective because its original
kernel is exactly the subgroup of actual principal Cartier divisors. -/
theorem cartierClassToPicard_injective : Function.Injective (cartierClassToPicard X) := by
  intro A B h
  obtain ⟨D, rfl⟩ := cartierClassMap_surjective X A
  obtain ⟨E, rfl⟩ := cartierClassMap_surjective X B
  change cartierPicardHom X D = cartierPicardHom X E at h
  change (D : CartierClassGroup X) = E
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [← cartierPicardHom_ker X]
  change cartierPicardHom X (D - E) = 0
  rw [map_sub, h, sub_self]

/-- The descended map is surjective because every actual Picard class
has the Cartier representative constructed above. -/
theorem cartierClassToPicard_surjective : Function.Surjective (cartierClassToPicard X) := by
  intro c
  obtain ⟨D, hD⟩ := cartierPicardHom_surjective X c
  exact ⟨cartierClassMap X D, hD⟩

/-- Actual Cartier divisors modulo actual principal divisors are
isomorphic to the actual Picard group, written additively. -/
def cartierClassPicardEquiv : CartierClassGroup X ≃+ Additive X.Pic :=
  AddEquiv.ofBijective (cartierClassToPicard X)
    ⟨cartierClassToPicard_injective X, cartierClassToPicard_surjective X⟩

/-- The group equivalence is the original constructed O(D) class map. -/
@[simp]
theorem cartierClassPicardEquiv_apply (D : CartierDivisor X) :
    (cartierClassPicardEquiv X (cartierClassMap X D)).toMul = cartierPicardClass X D := rfl

end KltDP.Geometry
