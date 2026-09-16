import KltDP.Geometry.CartierPicardSurjectivity
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Cartier equations from the actual rational coordinates of a line bundle

Every nonempty trivialization chart has an actual generator. Its rational
coordinate is nonzero, and changing charts multiplies that coordinate by
the image of an actual regular unit. The inverse rational coordinates
therefore define compatible sections of the actual Cartier divisor sheaf.
The pinned sheaf-gluing theorem assembles them into a global Cartier
divisor. No global divisor representative or transition equation is
included among the assumptions.

The comparison between the resulting O(D) and the original module sheaf
is a subsequent construction. This file does not yet assert surjectivity
of the Cartier-to-Picard map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem scalar_coordinate_generator {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (e : P ≃ₗ[R] R) (s : P) :
    e s • e.symm (1 : R) = s := by
  apply e.injective
  rw [e.map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]

private theorem coordinate_change_one_isUnit {R : Type*} [CommRing R]
    (e : R ≃ₗ[R] R) : IsUnit (e 1) := by
  obtain ⟨a, ha⟩ := e.surjective 1
  have hmul : e a = a * e 1 := by
    simpa only [smul_eq_mul, mul_one] using e.map_smul a (1 : R)
  exact isUnit_of_mul_eq_one_right a (e 1) (hmul.symm.trans ha)

variable (X : Scheme.{u}) [IsIntegral X]

/-- A nonempty open with an actual rank-one trivialization of M. -/
structure LineBundleTrivializationChart (M : X.Modules) where
  openSet : X.Opens
  nonempty : Nonempty openSet
  trivialization : M.over openSet ≅
    _root_.SheafOfModules.unit (X.ringCatSheaf.over openSet)

instance {M : X.Modules} (c : LineBundleTrivializationChart X M) :
    Nonempty c.openSet := c.nonempty

/-- The original rank-one atlas supplies enough actual nonempty charts. -/
theorem lineBundleTrivializationCharts_coversTop (M : X.Modules)
    [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M] :
    (Opens.grothendieckTopology X).CoversTop
      (fun c : LineBundleTrivializationChart X M => c.openSet) := by
  let t := KltDP.SheafOfModules.LocalTrivializations.ofIsInvertible
    (R := X.ringCatSheaf) M
  intro V x hx
  obtain ⟨W, i, hW, hxW⟩ := t.coversTop V x hx
  obtain ⟨j, ⟨a⟩⟩ := hW
  let c : LineBundleTrivializationChart X M := {
    openSet := t.X j
    nonempty := ⟨⟨x, a.le hxW⟩⟩
    trivialization := t.unitIso j }
  exact ⟨W, i, ⟨c, ⟨a⟩⟩, hxW⟩

/-- The actual section corresponding to one in a trivialization chart. -/
def lineBundleChartGenerator (M : X.Modules) (c : LineBundleTrivializationChart X M) :
    M.val.obj (op c.openSet) :=
  (overTrivializationSectionEquiv X M c.openSet c.trivialization (𝟙 c.openSet)).symm
    (1 : Γ(X, c.openSet))

/-- A chart generator restricts to the same chart's generator on every subopen. -/
theorem lineBundleChartGenerator_restrict (M : X.Modules)
    (c : LineBundleTrivializationChart X M) {V : X.Opens} (i : V ⟶ c.openSet) :
    M.val.map i.op (lineBundleChartGenerator X M c) =
      (overTrivializationSectionEquiv X M c.openSet c.trivialization i).symm
        (1 : Γ(X, V)) := by
  apply (overTrivializationSectionEquiv X M c.openSet c.trivialization i).injective
  rw [LinearEquiv.apply_symm_apply]
  refine (overTrivializationSectionEquiv_naturality X M c.openSet c.trivialization
    (𝟙 c.openSet) i i (by simp) (lineBundleChartGenerator X M c)).trans ?_
  change X.presheaf.map i.op
      ((overTrivializationSectionEquiv X M c.openSet c.trivialization
        (𝟙 c.openSet))
        ((overTrivializationSectionEquiv X M c.openSet c.trivialization
          (𝟙 c.openSet)).symm (1 : Γ(X, c.openSet)))) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact (X.presheaf.map i.op).hom.map_one

variable (M : X.Modules) (U : X.Opens) [Nonempty U]
  (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))

/-- The original function-field value of a chart's actual generator. -/
def lineBundleChartValue (c : LineBundleTrivializationChart X M) : X.functionField :=
  lineBundleGenericCoordinate X M U e c.openSet (lineBundleChartGenerator X M c)

/-- A chart generator cannot have zero rational coordinate: its
restriction to the nonempty intersection with U is nonzero. -/
theorem lineBundleChartValue_ne_zero (c : LineBundleTrivializationChart X M) :
    lineBundleChartValue X M U e c ≠ 0 := by
  intro hzero
  let W : X.Opens := c.openSet ⊓ U
  letI : Nonempty W := ⟨⟨genericPoint X,
    genericPoint_mem_nonempty_open X c.openSet, genericPoint_mem_nonempty_open X U⟩⟩
  let i : W ⟶ c.openSet := homOfLE inf_le_left
  let j : W ⟶ U := homOfLE inf_le_right
  have hcoord : lineBundleGenericCoordinate X M U e W
      (M.val.map i.op (lineBundleChartGenerator X M c)) =
        lineBundleGenericCoordinate X M U e W 0 :=
    (lineBundleGenericCoordinate_naturality X M U e i
      (lineBundleChartGenerator X M c)).trans
        (hzero.trans (map_zero (lineBundleGenericCoordinate X M U e W)).symm)
  have hsection := (lineBundleGenericCoordinate_injective_on_chart X M U e j) hcoord
  have hvalue := congrArg
    (overTrivializationSectionEquiv X M c.openSet c.trivialization i) hsection
  rw [lineBundleChartGenerator_restrict, LinearEquiv.apply_symm_apply, map_zero] at hvalue
  exact one_ne_zero hvalue

/-- The nonzero coordinate is packaged as a unit of the actual function field. -/
def lineBundleChartValueUnit (c : LineBundleTrivializationChart X M) : X.functionFieldˣ :=
  Units.mk0 (lineBundleChartValue X M U e c) (lineBundleChartValue_ne_zero X M U e c)

@[simp]
theorem lineBundleChartValueUnit_val (c : LineBundleTrivializationChart X M) :
    (lineBundleChartValueUnit X M U e c : X.functionField) =
      lineBundleChartValue X M U e c := rfl

/-- On every nonempty subopen of a chart, rational coordinates are the
regular chart coefficient times the fixed rational value of its generator. -/
theorem lineBundleGenericCoordinate_factor_chart (c : LineBundleTrivializationChart X M)
    {V : X.Opens} [Nonempty V] (i : V ⟶ c.openSet) (s : M.val.obj (op V)) :
    lineBundleGenericCoordinate X M U e V s =
      (X.germToFunctionField V).hom
          (overTrivializationSectionEquiv X M c.openSet c.trivialization i s) *
        lineBundleChartValue X M U e c := by
  let θ := overTrivializationSectionEquiv X M c.openSet c.trivialization i
  have hgen : lineBundleGenericCoordinate X M U e V (θ.symm (1 : Γ(X, V))) =
      lineBundleChartValue X M U e c := by
    rw [← lineBundleChartGenerator_restrict X M c i]
    exact lineBundleGenericCoordinate_naturality X M U e i (lineBundleChartGenerator X M c)
  calc
    lineBundleGenericCoordinate X M U e V s =
        lineBundleGenericCoordinate X M U e V (θ s • θ.symm (1 : Γ(X, V))) :=
      congrArg _ (scalar_coordinate_generator θ s).symm
    _ = θ s • lineBundleGenericCoordinate X M U e V (θ.symm (1 : Γ(X, V))) :=
      (lineBundleGenericCoordinate X M U e V).map_smul _ _
    _ = (X.germToFunctionField V).hom (θ s) * lineBundleChartValue X M U e c := by
      rw [hgen]
      rfl

/-- On an actual overlap, changing generators changes the rational
value by an actual regular unit of that overlap. -/
theorem exists_unit_lineBundleChartValue_ratio (c d : LineBundleTrivializationChart X M)
    {V : X.Opens} [Nonempty V] (i : V ⟶ c.openSet) (j : V ⟶ d.openSet) :
    ∃ a : Γ(X, V)ˣ,
      lineBundleChartValueUnit X M U e c =
        Units.map (X.germToFunctionField V).hom.toMonoidHom a *
          lineBundleChartValueUnit X M U e d := by
  let θc := overTrivializationSectionEquiv X M c.openSet c.trivialization i
  let θd := overTrivializationSectionEquiv X M d.openSet d.trivialization j
  let α := θc.symm ≪≫ₗ θd
  obtain ⟨a, ha⟩ := coordinate_change_one_isUnit α
  refine ⟨a, ?_⟩
  apply Units.ext
  change lineBundleChartValue X M U e c =
    (X.germToFunctionField V).hom (a : Γ(X, V)) * lineBundleChartValue X M U e d
  calc
    lineBundleChartValue X M U e c =
        lineBundleGenericCoordinate X M U e V
          (M.val.map i.op (lineBundleChartGenerator X M c)) :=
      (lineBundleGenericCoordinate_naturality X M U e i
        (lineBundleChartGenerator X M c)).symm
    _ = (X.germToFunctionField V).hom
        (θd (M.val.map i.op (lineBundleChartGenerator X M c))) *
          lineBundleChartValue X M U e d :=
      lineBundleGenericCoordinate_factor_chart X M U e d j _
    _ = (X.germToFunctionField V).hom (a : Γ(X, V)) *
        lineBundleChartValue X M U e d := by
      rw [lineBundleChartGenerator_restrict X M c i, ha]
      rfl

/-- The inverse generator values are compatible actual Cartier equations. -/
theorem lineBundleChartEquation_eq_on_overlap (c d : LineBundleTrivializationChart X M)
    {V : X.Opens} [Nonempty V] (i : V ⟶ c.openSet) (j : V ⟶ d.openSet) :
    cartierEquationClassHom X V (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹)) =
      cartierEquationClassHom X V (Additive.ofMul ((lineBundleChartValueUnit X M U e d)⁻¹)) := by
  obtain ⟨a, ha⟩ := exists_unit_lineBundleChartValue_ratio X M U e c d i j
  have hinv : (lineBundleChartValueUnit X M U e c)⁻¹ =
      (lineBundleChartValueUnit X M U e d)⁻¹ *
        Units.map (X.germToFunctionField V).hom.toMonoidHom (a⁻¹) := by
    rw [ha, mul_inv_rev, map_inv]
  rw [hinv, cartierEquationClassHom_mul_regular_unit]

/-- The actual Cartier quotient sheaf glues the proved local equations
into a global Cartier divisor with precisely those restrictions. -/
theorem exists_cartierDivisor_of_lineBundle [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M] :
    ∃ D : CartierDivisor X,
      ∀ c : LineBundleTrivializationChart X M,
        (cartierDivisorSheaf X).val.map
            (homOfLE (show c.openSet ≤ ⊤ from le_top)).op D =
          cartierEquationClassHom X c.openSet
            (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹)) := by
  let cover := fun c : LineBundleTrivializationChart X M => c.openSet
  have hcover : (⊤ : X.Opens) ≤ iSup cover := by
    intro x hx
    obtain ⟨V, i, hV, hxV⟩ := lineBundleTrivializationCharts_coversTop X M ⊤ x hx
    obtain ⟨c, ⟨a⟩⟩ := hV
    exact Opens.mem_iSup.mpr ⟨c, a.le hxV⟩
  let sf := fun c : LineBundleTrivializationChart X M =>
    cartierEquationClassHom X c.openSet
      (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹))
  have hcompatible : TopCat.Presheaf.IsCompatible (cartierDivisorSheaf X).val cover sf := by
    intro c d
    letI : Nonempty (c.openSet ⊓ d.openSet : X.Opens) :=
      ⟨⟨genericPoint X, genericPoint_mem_nonempty_open X c.openSet,
        genericPoint_mem_nonempty_open X d.openSet⟩⟩
    change (cartierDivisorSheaf X).val.map
        (homOfLE (show c.openSet ⊓ d.openSet ≤ c.openSet from inf_le_left)).op (sf c) =
      (cartierDivisorSheaf X).val.map
        (homOfLE (show c.openSet ⊓ d.openSet ≤ d.openSet from inf_le_right)).op (sf d)
    change (cartierDivisorSheaf X).val.map
        (homOfLE (show c.openSet ⊓ d.openSet ≤ c.openSet from inf_le_left)).op
        (cartierEquationClassHom X c.openSet
          (Additive.ofMul ((lineBundleChartValueUnit X M U e c)⁻¹))) = _
    rw [cartierEquationClassHom_restrict, cartierEquationClassHom_restrict]
    exact lineBundleChartEquation_eq_on_overlap X M U e c d
      (homOfLE inf_le_left) (homOfLE inf_le_right)
  obtain ⟨D, hD, -⟩ := (cartierDivisorSheaf X).existsUnique_gluing' cover ⊤
    (fun c => homOfLE (show cover c ≤ ⊤ from le_top)) hcover sf hcompatible
  exact ⟨D, hD⟩

end KltDP.Geometry
