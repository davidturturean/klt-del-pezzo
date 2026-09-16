import KltDP.Geometry.CartierPicardKernel
import KltDP.Geometry.TensorInvertibleSheaf

/-!
# Rational coordinates toward Cartier-to-Picard surjectivity

This first stage constructs actual rational coordinates from a rank-one
trivialization near the generic point. A section on a nonempty open V is
restricted to V intersect U, expressed in the actual U-trivialization,
and sent to the original function field by its ordinary germ map. These
maps are linear over the original section rings and compatible with
restriction. The rank-one atlas supplies such a U for every actual
locally free rank-one module sheaf, including representatives of Picard
classes by the proved tensor-invertible converse.

No generic stalk-module placeholder is introduced. Divisor assembly from
the resulting rational coordinates and the surjectivity theorem remain
separate obligations; neither is asserted in this file.

Reuse inspection: pinned Mathlib provides actual over-site evaluation,
module restriction, and the germ restriction identity used below. The
newer official 5aedf732b6987e8c26ab3c9ebc855314f82b045f sources inspected
did not supply a general scheme Cartier-to-Picard surjectivity proof.
The reviewed TauCeti Cartier files supply equations and units, whereas
the reviewed Mazur general dictionary remains conditional or unfinished.
Those unproved endpoints are not imported or assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual rank-one atlas has an actual trivialization on an open
containing the generic point. -/
theorem exists_genericPoint_trivialization (M : X.Modules)
    [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M] :
    ∃ U : X.Opens, genericPoint X ∈ U ∧
      Nonempty (M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  let t := KltDP.SheafOfModules.LocalTrivializations.ofIsInvertible
    (R := X.ringCatSheaf) M
  obtain ⟨V, i, hV, hx⟩ := t.coversTop ⊤ (genericPoint X) trivial
  obtain ⟨j, ⟨a⟩⟩ := hV
  exact ⟨t.X j, a.le hx, ⟨t.unitIso j⟩⟩

/-- Evaluation of an actual over-site trivialization is the actual
linear coordinate equivalence on every smaller open. -/
def overTrivializationSectionEquiv (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (i : V ⟶ U) : M.val.obj (op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk i))).mapIso e).toLinearEquiv

/-- The coordinate maps commute with the actual structure-sheaf restrictions. -/
theorem overTrivializationSectionEquiv_naturality (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V W : X.Opens} (i : V ⟶ U) (j : W ⟶ U) (k : W ⟶ V)
    (hk : k ≫ i = j) (s : M.val.obj (op V)) :
    overTrivializationSectionEquiv X M U e j (M.val.map k.op s) =
      X.presheaf.map k.op (overTrivializationSectionEquiv X M U e i s) :=
  PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk k hk : Over.mk j ⟶ Over.mk i).op s

private instance nonempty_intersection (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) :=
  ⟨⟨genericPoint X, genericPoint_mem_nonempty_open X U,
    genericPoint_mem_nonempty_open X V⟩⟩

/-- An actual trivialization on U gives an actual function-field-valued
linear map on each nonempty V by restriction to V intersect U. -/
def lineBundleGenericCoordinate (M : X.Modules) (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) [Nonempty V] : M.val.obj (op V) →ₗ[Γ(X, V)] X.functionField where
  toFun s := (X.germToFunctionField (V ⊓ U)).hom
    (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
      (M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op s))
  map_add' s t := by
    change (X.germToFunctionField (V ⊓ U)).hom
        (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
          ((M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op).hom (s + t))) = _
    rw [(M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op).hom.map_add,
      map_add, map_add]
  map_smul' a s := by
    change (X.germToFunctionField (V ⊓ U)).hom
        (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
          (M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op (a • s))) = _
    rw [M.val.map_smul,
      (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)).map_smul]
    change (X.germToFunctionField (V ⊓ U)).hom
        ((X.presheaf.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op a) *
          overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
            (M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op s)) =
      algebraMap Γ(X, V) X.functionField a *
        (X.germToFunctionField (V ⊓ U)).hom
          (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
            (M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op s))
    exact ((X.germToFunctionField (V ⊓ U)).hom.map_mul _ _).trans
      (congrArg (fun b : X.functionField => b *
        (X.germToFunctionField (V ⊓ U)).hom
          (overTrivializationSectionEquiv X M U e (homOfLE inf_le_right)
            (M.val.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op s)))
        (X.presheaf.germ_res_apply
          (homOfLE (show V ⊓ U ≤ V from inf_le_left)) (genericPoint X)
          (genericPoint_mem_nonempty_open X (V ⊓ U)) a))

/-- Rational coordinates are unchanged by restriction between nonempty
opens. All comparisons use the same original generic-point germ. -/
theorem lineBundleGenericCoordinate_naturality (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V W : X.Opens} [Nonempty V] [Nonempty W] (i : W ⟶ V)
    (s : M.val.obj (op V)) :
    lineBundleGenericCoordinate X M U e W (M.val.map i.op s) =
      lineBundleGenericCoordinate X M U e V s := by
  let jV : V ⊓ U ⟶ V := homOfLE inf_le_left
  let jW : W ⊓ U ⟶ W := homOfLE inf_le_left
  let k : W ⊓ U ⟶ V ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
  let aV : V ⊓ U ⟶ U := homOfLE inf_le_right
  let aW : W ⊓ U ⟶ U := homOfLE inf_le_right
  have hres : M.val.map jW.op (M.val.map i.op s) =
      M.val.map k.op (M.val.map jV.op s) := by
    change M.val.presheaf.map jW.op (M.val.presheaf.map i.op s) =
      M.val.presheaf.map k.op (M.val.presheaf.map jV.op s)
    calc
      _ = M.val.presheaf.map (i.op ≫ jW.op) s :=
        (ConcreteCategory.congr_hom (M.val.presheaf.map_comp i.op jW.op) s).symm
      _ = M.val.presheaf.map (jV.op ≫ k.op) s :=
        congrArg (fun j => M.val.presheaf.map j s) (Subsingleton.elim _ _)
      _ = _ := ConcreteCategory.congr_hom (M.val.presheaf.map_comp jV.op k.op) s
  change (X.germToFunctionField (W ⊓ U)).hom
      (overTrivializationSectionEquiv X M U e aW (M.val.map jW.op (M.val.map i.op s))) =
    (X.germToFunctionField (V ⊓ U)).hom
      (overTrivializationSectionEquiv X M U e aV (M.val.map jV.op s))
  rw [hres, overTrivializationSectionEquiv_naturality X M U e aV aW k
    (Subsingleton.elim _ _)]
  exact X.presheaf.germ_res_apply k (genericPoint X)
    (genericPoint_mem_nonempty_open X (W ⊓ U)) _

/-- On a subopen of the original chart, the rational coordinate is
exactly the germ of the original chart coordinate. -/
theorem lineBundleGenericCoordinate_on_chart (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} [Nonempty V] (i : V ⟶ U) (s : M.val.obj (op V)) :
    lineBundleGenericCoordinate X M U e V s =
      (X.germToFunctionField V).hom (overTrivializationSectionEquiv X M U e i s) := by
  let j : V ⊓ U ⟶ V := homOfLE inf_le_left
  let a : V ⊓ U ⟶ U := homOfLE inf_le_right
  change (X.germToFunctionField (V ⊓ U)).hom
      (overTrivializationSectionEquiv X M U e a (M.val.map j.op s)) = _
  rw [overTrivializationSectionEquiv_naturality X M U e i a j (Subsingleton.elim _ _)]
  exact X.presheaf.germ_res_apply j (genericPoint X)
    (genericPoint_mem_nonempty_open X (V ⊓ U)) _

/-- The actual chart generator has rational coordinate one. -/
theorem lineBundleGenericCoordinate_generator (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    lineBundleGenericCoordinate X M U e U
      ((overTrivializationSectionEquiv X M U e (𝟙 U)).symm (1 : Γ(X, U))) = 1 := by
  rw [lineBundleGenericCoordinate_on_chart X M U e (𝟙 U),
    LinearEquiv.apply_symm_apply]
  exact (X.germToFunctionField U).hom.map_one

/-- Rational coordinates are injective on every nonempty subopen of
the original chart, by the actual integral-scheme germ injection. -/
theorem lineBundleGenericCoordinate_injective_on_chart (M : X.Modules)
    (U : X.Opens) [Nonempty U]
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} [Nonempty V] (i : V ⟶ U) :
    Function.Injective (lineBundleGenericCoordinate X M U e V) := by
  intro s t h
  rw [lineBundleGenericCoordinate_on_chart X M U e i,
    lineBundleGenericCoordinate_on_chart X M U e i] at h
  exact (overTrivializationSectionEquiv X M U e i).injective
    ((X.germToFunctionField_injective V) h)

/-- Every actual Picard class has an actual locally free rank-one
representative with its original skeleton class. -/
theorem exists_invertible_representative_of_picard (c : X.Pic) :
    letI := Scheme.Modules.monoidalCategory X
    ∃ M : X.Modules, KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M ∧
      toSkeleton M = (c : Skeleton X.Modules) := by
  letI := Scheme.Modules.monoidalCategory X
  let M : X.Modules := (fromSkeleton X.Modules).obj (c : Skeleton X.Modules)
  have hM : toSkeleton M = (c : Skeleton X.Modules) := Quotient.out_eq _
  refine ⟨M, ?_, hM⟩
  apply SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton M
  rw [hM]
  exact c.isUnit

/-- Thus every Picard class supplies a genuine generic-point chart for
the rational-coordinate construction above. This is not yet a Cartier
representative or the surjectivity theorem. -/
theorem exists_picard_genericPoint_trivialization (c : X.Pic) :
    letI := Scheme.Modules.monoidalCategory X
    ∃ (M : X.Modules) (U : X.Opens),
      toSkeleton M = (c : Skeleton X.Modules) ∧ genericPoint X ∈ U ∧
        Nonempty (M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  letI := Scheme.Modules.monoidalCategory X
  obtain ⟨M, hM, hc⟩ := exists_invertible_representative_of_picard X c
  letI := hM
  obtain ⟨U, hU, e⟩ := exists_genericPoint_trivialization X M
  exact ⟨M, U, hc, hU, e⟩

end KltDP.Geometry
