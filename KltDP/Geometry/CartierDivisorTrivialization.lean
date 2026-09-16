import KltDP.Geometry.CartierDivisorModule
import KltDP.Geometry.InvertibleSheaf

/-!
# Actual rank-one trivializations of O(D)

The coordinate map on a nonempty equation chart is `a ↦ a/f`, with
`O(D) = f⁻¹ O`. It is an actual linear equivalence on each smaller open.
Naturality is proved in the original function field; the empty open uses
the actual terminal section ring. These equivalences form an isomorphism
of module sheaves over the chart. The actual local equations of a global
Cartier section then provide a covering atlas of singleton free bases.
Thus invertibility is proved for the constructed O(D), rather than supplied
as a field or inferred from an assumed Cartier/Picard identification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual principal fractional module identifies linearly with
the sections of O(D) on an equation chart. -/
def cartierPrincipalSectionEquiv (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    principalEquationSubmodule X U f ≃ₗ[Γ(X, U)]
      (cartierDivisorModule X D).val.obj (op U) where
  toFun s := ⟨(rationalFunctionModuleSectionsEquiv X U).symm s.val,
    (mem_cartierSectionSubmodule_iff X D U f hf _).mpr (by
      simpa only [LinearEquiv.apply_symm_apply] using s.property)⟩
  invFun s := ⟨rationalFunctionModuleSectionsEquiv X U s.val,
    (mem_cartierSectionSubmodule_iff X D U f hf s.val).mp s.property⟩
  left_inv s := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  right_inv s := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  map_add' s t := Subtype.ext (map_add (rationalFunctionModuleSectionsEquiv X U).symm s.val t.val)
  map_smul' a s := Subtype.ext ((rationalFunctionModuleSectionsEquiv X U).symm.map_smul a s.val)

/-- Actual coordinates on a nonempty equation chart, normalized by `a/f`. -/
def cartierEquationSectionEquiv (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    Γ(X, U) ≃ₗ[Γ(X, U)] (cartierDivisorModule X D).val.obj (op U) :=
  principalEquationSubmoduleEquiv X U f ≪≫ₗ cartierPrincipalSectionEquiv X D U f hf

/-- The coordinate map has the required sign in the original function field. -/
theorem cartierEquationSectionEquiv_apply_field (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (a : Γ(X, U)) :
    rationalFunctionModuleSectionsEquiv X U (cartierEquationSectionEquiv X D U f hf a).val =
      X.germToFunctionField U a * (↑(f⁻¹) : X.functionField) := by
  change rationalFunctionModuleSectionsEquiv X U
      ((rationalFunctionModuleSectionsEquiv X U).symm
        (principalEquationSubmoduleEquiv X U f a).val) = _
  rw [LinearEquiv.apply_symm_apply, principalEquationSubmoduleEquiv_apply]

omit [IsIntegral X] in
private theorem section_subsingleton_of_not_nonempty (U : X.Opens) (hU : ¬ Nonempty U) :
    Subsingleton Γ(X, U) := by
  have hbot : U = ⊥ := by
    apply SetLike.ext
    intro x
    exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
  subst U
  exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

/-- Coordinates on every object of an equation chart's over-site.
The empty object uses its actual terminal section modules. -/
def cartierEquationSectionEquivOn (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (V : Over U) :
    Γ(X, V.left) ≃ₗ[Γ(X, V.left)] (cartierDivisorModule X D).val.obj (op V.left) := by
  classical
  by_cases hV : Nonempty V.left
  · letI := hV
    exact cartierEquationSectionEquiv X D V.left f
      (cartierGlobalEquation_restrict X D (U := U) (V := V.left) V.hom f hf)
  · letI := section_subsingleton_of_not_nonempty X V.left hV
    letI : Subsingleton ((cartierDivisorModule X D).val.obj (op V.left)) :=
      Module.subsingleton Γ(X, V.left) _
    exact LinearEquiv.ofSubsingleton _ _

theorem cartierEquationSectionEquivOn_apply_field (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D)
    (V : Over U) [Nonempty V.left] (a : Γ(X, V.left)) :
    rationalFunctionModuleSectionsEquiv X V.left
        (cartierEquationSectionEquivOn X D U f hf V a).val =
      X.germToFunctionField V.left a * (↑(f⁻¹) : X.functionField) := by
  classical
  simp only [cartierEquationSectionEquivOn, dif_pos (inferInstance : Nonempty V.left)]
  exact cartierEquationSectionEquiv_apply_field X D V.left f _ a

/-- The actual module-sheaf trivialization on an equation chart.
The transition compatibility is proved on sections through the same
rational function `a/f`, including the actual empty-open case. -/
def cartierEquationOverIso (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (cartierDivisorModule X D).over U := by
  apply (_root_.SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun V => (cartierEquationSectionEquivOn X D U f hf V.unop).toModuleIso) ?_
  intro V W j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  classical
  by_cases hW : Nonempty W.unop.left
  · letI := hW
    letI : Nonempty V.unop.left := by
      obtain ⟨⟨x, hx⟩⟩ := hW
      exact ⟨⟨x, j.unop.left.le hx⟩⟩
    apply Subtype.ext
    apply (rationalFunctionModuleSectionsEquiv X W.unop.left).injective
    change rationalFunctionModuleSectionsEquiv X W.unop.left
        (cartierEquationSectionEquivOn X D U f hf W.unop
          (X.presheaf.map j.unop.left.op a)).val =
      rationalFunctionModuleSectionsEquiv X W.unop.left
        ((rationalFunctionModule X).val.map j.unop.left.op
          (cartierEquationSectionEquivOn X D U f hf V.unop a).val)
    rw [cartierEquationSectionEquivOn_apply_field,
      rationalFunctionModuleSectionsEquiv_naturality,
      cartierEquationSectionEquivOn_apply_field]
    exact congrArg (fun b : X.functionField => b * (↑(f⁻¹) : X.functionField))
      (X.presheaf.germ_res_apply j.unop.left (genericPoint X)
        (genericPoint_mem_nonempty_open X W.unop.left) a)
  · letI := section_subsingleton_of_not_nonempty X W.unop.left hW
    letI : Subsingleton ((cartierDivisorModule X D).val.obj (op W.unop.left)) :=
      Module.subsingleton Γ(X, W.unop.left) _
    exact @Subsingleton.elim
      ((cartierDivisorModule X D).val.obj (op W.unop.left)) inferInstance _ _

/-- An actual nonempty equation chart for the specified global Cartier section. -/
structure CartierEquationChart (D : CartierDivisor X) where
  openSet : X.Opens
  nonempty : Nonempty openSet
  equation : X.functionFieldˣ
  represents :
    letI := nonempty
    cartierEquationClassHom X openSet (Additive.ofMul equation) =
      (cartierDivisorSheaf X).val.map (homOfLE (show openSet ≤ ⊤ from le_top)).op D

instance (D : CartierDivisor X) (c : CartierEquationChart X D) : Nonempty c.openSet := c.nonempty

/-- The actual local-representative theorem supplies equation charts covering X. -/
theorem cartierEquationCharts_coversTop (D : CartierDivisor X) :
    (Opens.grothendieckTopology X).CoversTop
      (fun c : CartierEquationChart X D => c.openSet) := by
  intro V x hx
  obtain ⟨U, i, hxU, f, hf⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  let c : CartierEquationChart X D := {
    openSet := U
    nonempty := inferInstance
    equation := f
    represents := by simpa only [hi] using hf }
  refine ⟨V ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
  exact ⟨c, ⟨homOfLE inf_le_right⟩⟩

/-- The proved chart isomorphisms give an actual singleton free atlas for O(D). -/
def cartierDivisorLocalTrivializations (D : CartierDivisor X) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) (cartierDivisorModule X D) where
  I := CartierEquationChart X D
  X c := c.openSet
  coversTop := cartierEquationCharts_coversTop X D
  iso c := _root_.SheafOfModules.freeUniqueIsoUnit
      (R := X.ringCatSheaf.over c.openSet) PUnit ≪≫
    cartierEquationOverIso X D c.openSet c.equation c.represents

/-- O(D) is locally free of rank one, by its actual constructed trivializations. -/
instance cartierDivisorModule_isInvertible (D : CartierDivisor X) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (cartierDivisorModule X D) :=
  KltDP.SheafOfModules.LocalTrivializations.isInvertible (R := X.ringCatSheaf)
    (cartierDivisorLocalTrivializations X D)

/-- The actual invertible sheaf associated with the global Cartier divisor D. -/
def cartierDivisorInvertibleSheaf (D : CartierDivisor X) : InvertibleSheaf X :=
  InvertibleSheaf.ofLocalTrivializations (cartierDivisorModule X D)
    (cartierDivisorLocalTrivializations X D)

end KltDP.Geometry
