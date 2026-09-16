import KltDP.Geometry.CartierEulerPairingTwisted
import KltDP.Literature.Stacks.CurveTensorDegree
import KltDP.Compatibility.GrothendieckVanishing.TopologicalKrullDim
import KltDP.Topology.Dimension
import KltDP.Geometry.CartierPrincipalPicard
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeModulePullbackTensor

/-!
# The zero scheme of an effective divisor has dimension `≤ 1`; the Euler pairing as a degree

`X` a normal projective surface over `k`, `D₂` an effective Cartier divisor with regular equations,
`i : Z → X` any closed immersion with kernel ideal sheaf `I(D₂)` (for instance the zero scheme
`Z(D₂)` with its inclusion).

**Dimension.** The generic point of `X` lies off the support of `I(D₂)`: the germ of a regular
equation at the generic point is the chart's rational equation, a unit of the function field
(`genericPoint_not_mem_support`). Hence the image of `i` (contained in the support of `i.ker`) is a
proper closed subset of the irreducible surface, so its dimension is at most `dim X − 1 = 1`
(accepted `topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed`, `dimension_two`), and `Z`
embeds into it: **`topologicalKrullDim Z ≤ 1`** (`topologicalKrullDim_le_one_of_ker`,
`topologicalKrullDim_effectiveCartierScheme_le_one`). No principal ideal theorem is needed.

**Degree.** Stacks 0AYX on `Z` (the admitted literal `proper_curve_tensor_degree_literal`, rank one)
makes `deg_Z(i^*L) := χ_Z(i^*L) − χ_Z(O_Z)` (`restrictedEulerDegree`) additive under tensor; with
`i^*O(D) ⊗ i^*O(D') ≅ i^*O(D + D')` and `i^*O(−D) ⊗ i^*O(D) ≅ O_Z` (accepted pullback–tensor and
pullback–unit comparisons, `cartierTensorIso`, `O(0) ≅ O`) this gives `restrictedEulerDegree_add`
and `restrictedEulerDegree_neg`. Combined with Task 18's unconditional
`D₁ · D₂ = −deg_Z(i^*O_X(−D₁))`:

  **`cartierEulerPairing D₁ D₂ = deg_Z(i^*O_X(D₁))`** for every `D₁`, and the pairing is
  **additive in the other argument** against every effective `D₂` with regular equations
  (`cartierEulerPairing_add_left_of_hasRegularEquations`, `_add_right_`).

Export `f03_euler_pairing_degree_effective`.

**Not proved here:** linearity in a non-effective argument (every Cartier divisor as a difference of
effective ones with regular equations); coherence of `i_*M` on `X`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KltDP.Geometry.ModuleCohomology Topology TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance eulerPairingDegreeMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- `O_Y(0) ≅ O_Y` on an integral scheme (the principal divisor of `1`). -/
def cartierDivisorModuleZeroIsoUnit (Y : Scheme.{u}) [IsIntegral Y] :
    cartierDivisorModule Y 0 ≅ _root_.SheafOfModules.unit Y.ringCatSheaf := by
  have h : principalCartierDivisorHom Y (Additive.ofMul (1 : Y.functionFieldˣ)) = 0 := by simp
  exact h ▸ principalCartierModuleIsoUnit Y 1

section Pullback

variable {Y Z : Scheme.{u}} [IsIntegral Y] (i : Z ⟶ Y)

/-- `i^*O_Y(D) ⊗ i^*O_Y(E) ≅ i^*O_Y(D + E)`. -/
def pullbackCartierTensorIso (D E : CartierDivisor Y) :
    (schemeModulePullback i).obj (cartierDivisorModule Y D) ⊗
        (schemeModulePullback i).obj (cartierDivisorModule Y E) ≅
      (schemeModulePullback i).obj (cartierDivisorModule Y (D + E)) :=
  (schemeModulePullbackTensorIso i _ _).symm ≪≫
    (schemeModulePullback i).mapIso (cartierTensorIso Y D E)

/-- `i^*O_Y(−D) ⊗ i^*O_Y(D) ≅ O_Z`. -/
def pullbackCartierNegTensorIso (D : CartierDivisor Y) :
    (schemeModulePullback i).obj (cartierDivisorModule Y (-D)) ⊗
        (schemeModulePullback i).obj (cartierDivisorModule Y D) ≅
      _root_.SheafOfModules.unit Z.ringCatSheaf :=
  pullbackCartierTensorIso i (-D) D ≪≫
    (schemeModulePullback i).mapIso
      (eqToIso (congrArg (cartierDivisorModule Y) (neg_add_cancel D)) ≪≫
        cartierDivisorModuleZeroIsoUnit Y) ≪≫
    schemeModulePullbackUnitIso i

/-- The pulled-back Cartier module is locally free of rank one. -/
theorem pullback_cartierDivisorModule_isLocallyFreeOfRank_one (D : CartierDivisor Y) :
    KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Z.ringCatSheaf)
      ((schemeModulePullback i).obj (cartierDivisorModule Y D)) 1 := by
  haveI : KltDP.SheafOfModules.IsInvertible (R := Z.ringCatSheaf)
      ((schemeModulePullback i).obj (cartierDivisorModule Y D)) :=
    schemeModulePullback_isInvertible i _ (cartierDivisorInvertibleSheaf Y D).property
  infer_instance

end Pullback

/-- **Rank-one 0AYX**: on a proper scheme of dimension `≤ 1`, `deg(E ⊗ V) = deg E + deg V` for
`deg E := χ(E) − χ(O)` and locally free `E`, `V` of rank one (the admitted literal, expanded). -/
theorem eulerDegree_tensor {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f] (hdim : topologicalKrullDim Y ≤ 1)
    (E V : Y.Modules)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Y.ringCatSheaf) E 1)
    (hV : KltDP.SheafOfModules.IsLocallyFreeOfRank (R := Y.ringCatSheaf) V 1) :
    eulerCharacteristic f (E ⊗ V) -
        eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      (eulerCharacteristic f E -
          eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
        (eulerCharacteristic f V -
          eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) := by
  have h : eulerCharacteristic f (E ⊗ V) -
        ((1 * 1 : ℕ) : ℤ) * eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) =
      ((1 : ℕ) : ℤ) * (eulerCharacteristic f V -
          ((1 : ℕ) : ℤ) * eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) +
        ((1 : ℕ) : ℤ) * (eulerCharacteristic f E -
          ((1 : ℕ) : ℤ) * eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :=
    KltDP.Literature.Stacks.proper_curve_tensor_degree f hdim E V 1 1 hE hV
  simp only [Nat.mul_one, Nat.cast_one, one_mul] at h
  omega

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

section Dimension

variable (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-- The generic point of the surface is not in the support of the divisor ideal of an effective
divisor with regular equations: the germ of a regular equation there is the chart's rational
equation, a unit of the function field. -/
theorem genericPoint_not_mem_support :
    genericPoint X.toScheme ∉
      (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support := by
  obtain ⟨c, hη⟩ := hD (genericPoint X.toScheme)
  intro hmem
  have hunit : IsUnit (X.toScheme.germToFunctionField c.chart.openSet c.coefficient) := by
    rw [c.germ_eq]
    exact c.chart.equation.isUnit
  exact (PrimeCurve.mem_support_iff_not_isUnit_germ D hD c _ hη).mp hmem hunit

/-- **A closed subscheme with kernel `I(D)` has dimension `≤ 1`**: its image is a proper closed
subset of the irreducible two-dimensional surface. -/
theorem topologicalKrullDim_le_one_of_ker {Z : Scheme.{u}} (i : Z ⟶ X.toScheme)
    [IsClosedImmersion i]
    (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D hD) :
    topologicalKrullDim Z ≤ 1 := by
  have hemb : IsEmbedding i.base := i.isClosedEmbedding.isEmbedding
  have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hne : Set.range i.base ≠ Set.univ := by
    intro h
    have hmem : genericPoint X.toScheme ∈ Set.range i.base := by
      rw [h]
      exact Set.mem_univ _
    have hsupp := i.range_subset_ker_support hmem
    rw [hker] at hsupp
    exact X.genericPoint_not_mem_support D hD hsupp
  have h1 : topologicalKrullDim Z ≤ topologicalKrullDim (Set.range i.base) :=
    KltDP.Topology.topologicalKrullDim_le_of_isEmbedding
      (Set.codRestrict i.base (Set.range i.base) fun x => Set.mem_range_self x)
      (hemb.codRestrict _ _)
  have h2 : topologicalKrullDim (Set.range i.base) + 1 ≤ 2 :=
    (topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed hclosed hne).trans_eq
      X.dimension_two
  have hS1 : topologicalKrullDim (Set.range i.base) ≤ 1 := by
    generalize hd : topologicalKrullDim (Set.range i.base) = d at h2 ⊢
    rcases d with _ | m
    · exact bot_le
    · have h2' : ((m : ℕ∞) : WithBot ℕ∞) + 1 ≤ 2 := h2
      rw [← WithBot.coe_one, ← WithBot.coe_add] at h2'
      have h3 : m + 1 ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp h2'
      have hm : m ≠ ⊤ := by
        rintro rfl
        simp at h3
      have h4 : m < 2 := (ENat.add_one_le_iff hm).mp h3
      have h5 : m ≤ 1 :=
        (ENat.lt_add_one_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp
          (by simpa only [one_add_one_eq_two] using h4)
      exact WithBot.coe_le_coe.mpr h5
  exact h1.trans hS1

/-- **`topologicalKrullDim Z(D) ≤ 1`** for the zero scheme of an effective divisor with regular
equations. -/
theorem topologicalKrullDim_effectiveCartierScheme_le_one :
    topologicalKrullDim (effectiveCartierScheme X.toScheme D hD) ≤ 1 :=
  X.topologicalKrullDim_le_one_of_ker D hD (effectiveCartierInclusion X.toScheme D hD)
    (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).ker_gluedTo

end Dimension

section Degree

variable (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
  {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)

include hker in
/-- **`deg_Z(i^*O(D + D')) = deg_Z(i^*O(D)) + deg_Z(i^*O(D'))`** (0AYX on `Z`). -/
theorem restrictedEulerDegree_add (D D' : CartierDivisor X.toScheme) :
    X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (D + D')) =
      X.restrictedEulerDegree i (cartierDivisorModule X.toScheme D) +
        X.restrictedEulerDegree i (cartierDivisorModule X.toScheme D') := by
  haveI : IsProper (i ≫ X.structureMorphism) := inferInstance
  have h := eulerDegree_tensor (i ≫ X.structureMorphism)
    (X.topologicalKrullDim_le_one_of_ker D₂ hD₂ i hker)
    ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme D))
    ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme D'))
    (pullback_cartierDivisorModule_isLocallyFreeOfRank_one i D)
    (pullback_cartierDivisorModule_isLocallyFreeOfRank_one i D')
  rw [eulerCharacteristic_eq_of_iso (i ≫ X.structureMorphism)
    (pullbackCartierTensorIso i D D')] at h
  unfold restrictedEulerDegree
  omega

include hker in
/-- **`deg_Z(i^*O(−D)) = −deg_Z(i^*O(D))`** (0AYX on `Z`). -/
theorem restrictedEulerDegree_neg (D : CartierDivisor X.toScheme) :
    X.restrictedEulerDegree i (cartierDivisorModule X.toScheme (-D)) =
      -X.restrictedEulerDegree i (cartierDivisorModule X.toScheme D) := by
  haveI : IsProper (i ≫ X.structureMorphism) := inferInstance
  have h := eulerDegree_tensor (i ≫ X.structureMorphism)
    (X.topologicalKrullDim_le_one_of_ker D₂ hD₂ i hker)
    ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme (-D)))
    ((schemeModulePullback i).obj (cartierDivisorModule X.toScheme D))
    (pullback_cartierDivisorModule_isLocallyFreeOfRank_one i (-D))
    (pullback_cartierDivisorModule_isLocallyFreeOfRank_one i D)
  rw [eulerCharacteristic_eq_of_iso (i ≫ X.structureMorphism)
    (pullbackCartierNegTensorIso i D)] at h
  unfold restrictedEulerDegree
  omega

include hker in
/-- **`D₁ · D₂ = deg_Z(i^*O_X(D₁))`** for every effective `D₂` with regular equations, every closed
immersion `i : Z → X` with kernel `I(D₂)` and every `D₁`. -/
theorem cartierEulerPairing_eq_restrictedEulerDegree (D₁ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      X.restrictedEulerDegree i (cartierDivisorModule X.toScheme D₁) := by
  rw [X.cartierEulerPairing_eq_neg_restrictedEulerDegree_of_ker D₂ hD₂ i hker D₁,
    X.restrictedEulerDegree_neg D₂ hD₂ i hker D₁, neg_neg]

include hker in
/-- **Additivity in the first argument** against an effective `D₂` with regular equations. -/
theorem cartierEulerPairing_add_left_of_ker (D₁ D₁' : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (D₁ + D₁') D₂ =
      X.cartierEulerPairing D₁ D₂ + X.cartierEulerPairing D₁' D₂ := by
  rw [X.cartierEulerPairing_eq_restrictedEulerDegree D₂ hD₂ i hker (D₁ + D₁'),
    X.cartierEulerPairing_eq_restrictedEulerDegree D₂ hD₂ i hker D₁,
    X.cartierEulerPairing_eq_restrictedEulerDegree D₂ hD₂ i hker D₁',
    X.restrictedEulerDegree_add D₂ hD₂ i hker D₁ D₁']

end Degree

section ZeroScheme

variable (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)

/-- **`D₁ · D₂ = deg_{Z(D₂)}(i^*O_X(D₁))`** along the zero scheme of `D₂`. -/
theorem cartierEulerPairing_eq_restrictedEulerDegree_effectiveCartierInclusion
    (D₁ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      X.restrictedEulerDegree (effectiveCartierInclusion X.toScheme D₂ hD₂)
        (cartierDivisorModule X.toScheme D₁) :=
  X.cartierEulerPairing_eq_restrictedEulerDegree D₂ hD₂ (effectiveCartierInclusion X.toScheme D₂ hD₂)
    (effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂).ker_gluedTo D₁

include hD₂ in
/-- **Additivity in the first argument** against an effective `D₂` with regular equations. -/
theorem cartierEulerPairing_add_left_of_hasRegularEquations (D₁ D₁' : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (D₁ + D₁') D₂ =
      X.cartierEulerPairing D₁ D₂ + X.cartierEulerPairing D₁' D₂ :=
  X.cartierEulerPairing_add_left_of_ker D₂ hD₂ (effectiveCartierInclusion X.toScheme D₂ hD₂)
    (effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂).ker_gluedTo D₁ D₁'

include hD₂ in
/-- **Additivity in the second argument** for an effective first argument, by symmetry. -/
theorem cartierEulerPairing_add_right_of_hasRegularEquations
    (D₁ D₁' : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₂ (D₁ + D₁') =
      X.cartierEulerPairing D₂ D₁ + X.cartierEulerPairing D₂ D₁' := by
  rw [X.cartierEulerPairing_comm, X.cartierEulerPairing_add_left_of_hasRegularEquations D₂ hD₂ D₁ D₁',
    X.cartierEulerPairing_comm D₂ D₁, X.cartierEulerPairing_comm D₂ D₁']

end ZeroScheme

end NormalProjectiveSurface

open NormalProjectiveSurface

/-- **F03 export (Task 18, degree form): the Euler pairing against an effective divisor is the
degree of the restricted line bundle, and is additive in the other argument.** For an effective
Cartier divisor `D₂` with regular equations on a normal projective surface: (1) its zero scheme has
dimension `≤ 1`; (2) for every closed immersion `i : Z → X` with kernel `I(D₂)` and every `D₁`,
`D₁ · D₂ = deg_Z(i^*O_X(D₁))` with `deg_Z(i^*L) = χ_Z(i^*L) − χ_Z(O_Z)`; (3) `(D₁ + D₁') · D₂ =
D₁ · D₂ + D₁' · D₂`; (4) `D₂ · (D₁ + D₁') = D₂ · D₁ + D₂ · D₁'`. -/
theorem f03_euler_pairing_degree_effective {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂) :
    topologicalKrullDim (effectiveCartierScheme X.toScheme D₂ hD₂) ≤ 1 ∧
    (∀ {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
      (_ : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme D₂ hD₂)
      (D₁ : CartierDivisor X.toScheme),
      X.cartierEulerPairing D₁ D₂ =
        X.restrictedEulerDegree i (cartierDivisorModule X.toScheme D₁)) ∧
    (∀ D₁ D₁' : CartierDivisor X.toScheme,
      X.cartierEulerPairing (D₁ + D₁') D₂ =
        X.cartierEulerPairing D₁ D₂ + X.cartierEulerPairing D₁' D₂) ∧
    (∀ D₁ D₁' : CartierDivisor X.toScheme,
      X.cartierEulerPairing D₂ (D₁ + D₁') =
        X.cartierEulerPairing D₂ D₁ + X.cartierEulerPairing D₂ D₁') :=
  ⟨X.topologicalKrullDim_effectiveCartierScheme_le_one D₂ hD₂,
    fun {Z} i _ hker D₁ =>
      X.cartierEulerPairing_eq_restrictedEulerDegree (Z := Z) D₂ hD₂ i hker D₁,
    fun D₁ D₁' => X.cartierEulerPairing_add_left_of_hasRegularEquations D₂ hD₂ D₁ D₁',
    fun D₁ D₁' => X.cartierEulerPairing_add_right_of_hasRegularEquations D₂ hD₂ D₁ D₁'⟩

/-- Universe check: a single universe `u`. -/
example {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (D₂ : CartierDivisor X.toScheme) (hD₂ : HasRegularCartierEquations X.toScheme D₂)
    (D₁ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      X.restrictedEulerDegree (effectiveCartierInclusion X.toScheme D₂ hD₂)
        (cartierDivisorModule X.toScheme D₁) :=
  X.cartierEulerPairing_eq_restrictedEulerDegree_effectiveCartierInclusion D₂ hD₂ D₁

end KltDP.Geometry
