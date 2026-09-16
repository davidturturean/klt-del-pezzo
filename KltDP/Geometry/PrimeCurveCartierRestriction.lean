import KltDP.Geometry.EffectiveCartierDegree
import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.CartierEquationUnits
import KltDP.Geometry.PrimeCurveStalkCoordinates

/-!
# Restriction of an effective Cartier divisor to a prime curve not in its support

Let `X` be a normal projective surface, `C : X.PrimeCurve` an actual prime curve with
its reduced closed subscheme `C.toScheme` and closed immersion `i = C.inclusion`, and
`D : CartierDivisor X.toScheme` with regular local equations (`hD`). The hypothesis
"`C ⊄ Supp D`" is stated as `NotInSupport C D hD`: the generic point of `C` is not in
the support of the divisor ideal `O ∩ O(-D)` (`effectiveCartierIdealDataOfRegularEquations`).

Constructed here (ordinary proofs, no literature input):

* on every regular chart `(U, d)` of `D` containing the generic point of `C`, the
  germ of `d` there is a unit, hence the restricted regular function
  `i.app U d ∈ Γ(C, i⁻¹ U)` is nonzero and defines a unit `restrictedEquation` of the
  function field of `C`;
* the restricted equations of two charts differ on the overlap by the image of the
  restricted transition unit of `D`, so their Cartier classes agree; the Cartier
  divisor sheaf of `C.toScheme` glues them (pinned `existsUnique_gluing'`) into
  `restrictCartier : CartierDivisor C.toScheme`, the actual `D|_C`, with the exact
  restrictions recorded by `restrictCartier_spec`;
* `restrictCartier_hasRegularEquations`: `D|_C` is effective with the restricted
  charts as regular equation charts; `cartierTransitionUnit_restrictCartier`: its
  transition units are the `i.app`-images of those of `D` (the image cocycle);
* the intersection subscheme `intersectionScheme = effectiveCartierScheme C.toScheme (D|_C)`
  with its closed immersions into `C.toScheme` and `X.toScheme`, and
  `intersectionDegree = deg(D|_C) = dim_k Γ(C ∩ D, O)` (finite dimensional);
* the set-level identification `range_intersectionToSurface`: the image of `C ∩ D` in
  `X` is `C ∩ Supp D`, through `mem_support_restrictCartier_iff` (support membership is
  non-invertibility of the equation germ, transported by the local stalk map of `i`).

Not proved here: the isomorphism `O_C(D|_C) ≅ i^* O_X(D)` and the scheme-theoretic
identification of the intersection subscheme with the fibre product `C ×_X D`; see
`F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-! ### A point of the curve scheme over the generic point -/

theorem exists_genericLift : ∃ y : C.toScheme, C.inclusion.base y = C.genericPoint := by
  have h : C.genericPoint ∈ Set.range C.inclusion.base := by
    rw [C.range_inclusion]
    exact C.genericPoint_mem
  exact h

/-- A point of the actual curve scheme mapping to the generic point of the curve. -/
def genericLift : C.toScheme := C.exists_genericLift.choose

theorem inclusion_genericLift : C.inclusion.base C.genericLift = C.genericPoint :=
  C.exists_genericLift.choose_spec

/-- Every point of the curve scheme maps into the original curve. -/
theorem inclusion_base_mem (y : C.toScheme) : C.inclusion.base y ∈ C := by
  have h : C.inclusion.base y ∈ Set.range C.inclusion.base := Set.mem_range_self y
  rw [C.range_inclusion] at h
  exact h

variable (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-! ### The hypothesis `C ⊄ Supp D` and unit germs -/

/-- `C` is not contained in the support of `D`: the generic point of `C` lies outside
the support of the divisor ideal `O ∩ O(-D)`. -/
def NotInSupport : Prop :=
  C.genericPoint ∉ (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support

/-- Off the support of the divisor ideal, the germ of every regular equation is a unit. -/
theorem germ_isUnit_of_not_mem_support (c : RegularCartierEquationChart X.toScheme D)
    (x : X.toScheme) (hx : x ∈ c.chart.openSet)
    (hxs : x ∉ (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support) :
    IsUnit (X.toScheme.presheaf.germ c.chart.openSet x hx c.coefficient) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVc⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open hx c.chart.openSet.2
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let d := RegularCartierEquationChart.restrict X.toScheme D c V hVc
  have hideal : (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).ideal ⟨V, hV⟩ =
      Ideal.span ({d.coefficient} : Set Γ(X.toScheme, V)) :=
    effectiveCartierIdealDataOfRegularEquations_ideal_chart X.toScheme D hD d hV
  have hmem := Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := effectiveCartierIdealDataOfRegularEquations X.toScheme D hD) (U := ⟨V, hV⟩) hxV
  rw [hideal, X.toScheme.zeroLocus_span, X.toScheme.zeroLocus_singleton] at hmem
  have hbasic : x ∈ X.toScheme.basicOpen d.coefficient := by
    by_contra hnot
    exact hxs (hmem.mpr hnot)
  rw [X.toScheme.mem_basicOpen d.coefficient x hxV] at hbasic
  have key : X.toScheme.presheaf.germ c.chart.openSet x hx c.coefficient =
      X.toScheme.presheaf.germ V x hxV d.coefficient :=
    (X.toScheme.presheaf.germ_res_apply (homOfLE hVc) x hxV c.coefficient).symm
  rw [key]
  exact hbasic

/-! ### Restricted equations -/

/-- The chart open pulled back to the curve scheme. -/
abbrev chartPreimage (c : RegularCartierEquationChart X.toScheme D) : C.toScheme.Opens :=
  C.inclusion ⁻¹ᵁ c.chart.openSet

theorem genericLift_mem_chartPreimage (c : RegularCartierEquationChart X.toScheme D)
    (hη : C.genericPoint ∈ c.chart.openSet) : C.genericLift ∈ C.chartPreimage D c := by
  change C.inclusion.base C.genericLift ∈ c.chart.openSet
  rw [C.inclusion_genericLift]
  exact hη

/-- The regular equation of `D` restricted along the closed immersion of the curve. -/
def restrictedCoefficient (c : RegularCartierEquationChart X.toScheme D) :
    Γ(C.toScheme, C.chartPreimage D c) :=
  C.inclusion.app c.chart.openSet c.coefficient

/-- The restricted equation is nonzero when the generic point of `C` is off the support:
its germ at the point over the generic point is the image of a unit. -/
theorem restrictedCoefficient_ne_zero (c : RegularCartierEquationChart X.toScheme D)
    (hη : C.genericPoint ∈ c.chart.openSet) (hC : C.NotInSupport D hD) :
    C.restrictedCoefficient D c ≠ 0 := by
  intro h0
  have hy : C.inclusion.base C.genericLift ∈ c.chart.openSet := by
    rw [C.inclusion_genericLift]
    exact hη
  have hxs : C.inclusion.base C.genericLift ∉
      (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support := by
    rw [C.inclusion_genericLift]
    exact hC
  have hunit := germ_isUnit_of_not_mem_support D hD c (C.inclusion.base C.genericLift) hy hxs
  have hgerm := Scheme.stalkMap_germ_apply C.inclusion c.chart.openSet C.genericLift hy c.coefficient
  have hunit' : IsUnit (C.toScheme.presheaf.germ (C.chartPreimage D c) C.genericLift hy
      (C.restrictedCoefficient D c)) := by
    rw [restrictedCoefficient, ← hgerm]
    exact hunit.map (C.inclusion.stalkMap C.genericLift).hom
  rw [h0, map_zero] at hunit'
  exact not_isUnit_zero hunit'

theorem germToFunctionField_restrictedCoefficient_ne_zero
    (c : RegularCartierEquationChart X.toScheme D)
    (hη : C.genericPoint ∈ c.chart.openSet) (hC : C.NotInSupport D hD) :
    letI : Nonempty (C.chartPreimage D c) := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c hη⟩⟩
    C.toScheme.germToFunctionField (C.chartPreimage D c) (C.restrictedCoefficient D c) ≠ 0 := by
  letI : Nonempty (C.chartPreimage D c) := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c hη⟩⟩
  intro h
  apply C.restrictedCoefficient_ne_zero D hD c hη hC
  apply C.toScheme.germToFunctionField_injective (C.chartPreimage D c)
  rw [h, map_zero]

/-- The restricted equation as a unit of the function field of the curve. -/
def restrictedEquation (c : RegularCartierEquationChart X.toScheme D)
    (hη : C.genericPoint ∈ c.chart.openSet) (hC : C.NotInSupport D hD) :
    C.toScheme.functionFieldˣ :=
  letI : Nonempty (C.chartPreimage D c) := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c hη⟩⟩
  Units.mk0 (C.toScheme.germToFunctionField (C.chartPreimage D c) (C.restrictedCoefficient D c))
    (C.germToFunctionField_restrictedCoefficient_ne_zero D hD c hη hC)

/-- Regular charts of `D` whose open contains the generic point of `C`; these cover the curve. -/
abbrev GenericChart : Type u :=
  {c : RegularCartierEquationChart X.toScheme D // C.genericPoint ∈ c.chart.openSet}

theorem exists_genericChart (hD : HasRegularCartierEquations X.toScheme D) (y : C.toScheme) :
    ∃ c : C.GenericChart D, y ∈ C.chartPreimage D c.1 := by
  obtain ⟨c, hyc⟩ := hD (C.inclusion.base y)
  exact ⟨⟨c, C.genericPoint_mem_of_mem ⟨C.inclusion.base y, hyc⟩ (C.inclusion_base_mem y)⟩, hyc⟩

/-! ### Compatibility of the restricted equations: the image cocycle -/

/-- The two equations of `D` agree as Cartier classes on the overlap of two charts. -/
theorem chart_class_eq_on_inf (c d : C.GenericChart D) :
    letI : Nonempty (c.1.chart.openSet ⊓ d.1.chart.openSet : X.toScheme.Opens) :=
      ⟨⟨C.genericPoint, c.2, d.2⟩⟩
    cartierEquationClassHom X.toScheme (c.1.chart.openSet ⊓ d.1.chart.openSet)
        (Additive.ofMul c.1.chart.equation) =
      cartierEquationClassHom X.toScheme (c.1.chart.openSet ⊓ d.1.chart.openSet)
        (Additive.ofMul d.1.chart.equation) := by
  letI : Nonempty (c.1.chart.openSet ⊓ d.1.chart.openSet : X.toScheme.Opens) :=
    ⟨⟨C.genericPoint, c.2, d.2⟩⟩
  exact (cartierGlobalEquation_restrict X.toScheme D
    (homOfLE (inf_le_left : c.1.chart.openSet ⊓ d.1.chart.openSet ≤ c.1.chart.openSet))
    c.1.chart.equation c.1.chart.represents).trans
    (cartierGlobalEquation_restrict X.toScheme D
      (homOfLE (inf_le_right : c.1.chart.openSet ⊓ d.1.chart.openSet ≤ d.1.chart.openSet))
      d.1.chart.equation d.1.chart.represents).symm

/-- The accepted transition unit of `D` between two charts containing the generic point of `C`. -/
def chartTransitionUnit (c d : C.GenericChart D) :
    Γ(X.toScheme, c.1.chart.openSet ⊓ d.1.chart.openSet)ˣ :=
  letI : Nonempty (c.1.chart.openSet ⊓ d.1.chart.openSet : X.toScheme.Opens) :=
    ⟨⟨C.genericPoint, c.2, d.2⟩⟩
  cartierTransitionUnit X.toScheme (c.1.chart.openSet ⊓ d.1.chart.openSet)
    c.1.chart.equation d.1.chart.equation (C.chart_class_eq_on_inf D c d)

/-- The function-field value of the restricted transition unit is the ratio of the
restricted equations: the cocycle of `D|_C` is the image under `i.app` of the cocycle of `D`. -/
theorem germToFunctionField_map_chartTransitionUnit (hC : C.NotInSupport D hD)
    (c d : C.GenericChart D) :
    letI : Nonempty (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
        C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
    Units.map (C.toScheme.germToFunctionField
        (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet))).hom.toMonoidHom
        (Units.map (C.inclusion.app (c.1.chart.openSet ⊓ d.1.chart.openSet)).hom.toMonoidHom
          (C.chartTransitionUnit D c d)) =
      C.restrictedEquation D hD c.1 c.2 hC / C.restrictedEquation D hD d.1 d.2 hC := by
  let Uc : X.toScheme.Opens := c.1.chart.openSet
  let Ud : X.toScheme.Opens := d.1.chart.openSet
  letI : Nonempty (Uc ⊓ Ud : X.toScheme.Opens) := ⟨⟨C.genericPoint, c.2, d.2⟩⟩
  letI : Nonempty (C.inclusion ⁻¹ᵁ (Uc ⊓ Ud)) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
      C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
  letI : Nonempty (C.chartPreimage D c.1) := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
  letI : Nonempty (C.chartPreimage D d.1) := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
  let a : Γ(X.toScheme, Uc ⊓ Ud)ˣ := C.chartTransitionUnit D c d
  have ha : X.toScheme.germToFunctionField (Uc ⊓ Ud) (a : Γ(X.toScheme, Uc ⊓ Ud)) =
      (c.1.chart.equation : X.toScheme.functionField) / d.1.chart.equation := by
    have h := map_cartierTransitionUnit X.toScheme (Uc ⊓ Ud) c.1.chart.equation
      d.1.chart.equation (C.chart_class_eq_on_inf D c d)
    have h' := congrArg (fun u : X.toScheme.functionFieldˣ => (u : X.toScheme.functionField)) h
    simpa only [Units.coe_map, Units.val_div_eq_div_val] using h'
  let rc : Γ(X.toScheme, Uc ⊓ Ud) :=
    X.toScheme.presheaf.map (homOfLE (inf_le_left : Uc ⊓ Ud ≤ Uc)).op c.1.coefficient
  let rd : Γ(X.toScheme, Uc ⊓ Ud) :=
    X.toScheme.presheaf.map (homOfLE (inf_le_right : Uc ⊓ Ud ≤ Ud)).op d.1.coefficient
  have hrc : X.toScheme.germToFunctionField (Uc ⊓ Ud) rc =
      (c.1.chart.equation : X.toScheme.functionField) :=
    (X.toScheme.presheaf.germ_res_apply (homOfLE inf_le_left) (_root_.genericPoint X.toScheme)
      (genericPoint_mem_nonempty_open X.toScheme (Uc ⊓ Ud)) c.1.coefficient).trans c.1.germ_eq
  have hrd : X.toScheme.germToFunctionField (Uc ⊓ Ud) rd =
      (d.1.chart.equation : X.toScheme.functionField) :=
    (X.toScheme.presheaf.germ_res_apply (homOfLE inf_le_right) (_root_.genericPoint X.toScheme)
      (genericPoint_mem_nonempty_open X.toScheme (Uc ⊓ Ud)) d.1.coefficient).trans d.1.germ_eq
  have hcoef : rc = (a : Γ(X.toScheme, Uc ⊓ Ud)) * rd := by
    apply X.toScheme.germToFunctionField_injective (Uc ⊓ Ud)
    rw [map_mul, hrc, ha, hrd]
    exact (div_mul_cancel₀ _ (Units.ne_zero d.1.chart.equation)).symm
  have hcoefC : C.inclusion.app (Uc ⊓ Ud) rc =
      C.inclusion.app (Uc ⊓ Ud) (a : Γ(X.toScheme, Uc ⊓ Ud)) * C.inclusion.app (Uc ⊓ Ud) rd := by
    rw [hcoef, map_mul]
  have hnatc : C.inclusion.app (Uc ⊓ Ud) rc =
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_left : Uc ⊓ Ud ≤ Uc))).op (C.restrictedCoefficient D c.1) :=
    ConcreteCategory.congr_hom (C.inclusion.naturality (homOfLE (inf_le_left : Uc ⊓ Ud ≤ Uc)).op)
      c.1.coefficient
  have hnatd : C.inclusion.app (Uc ⊓ Ud) rd =
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_right : Uc ⊓ Ud ≤ Ud))).op (C.restrictedCoefficient D d.1) :=
    ConcreteCategory.congr_hom (C.inclusion.naturality (homOfLE (inf_le_right : Uc ⊓ Ud ≤ Ud)).op)
      d.1.coefficient
  have hec : C.toScheme.germToFunctionField (C.inclusion ⁻¹ᵁ (Uc ⊓ Ud)) (C.inclusion.app (Uc ⊓ Ud) rc) =
      (C.restrictedEquation D hD c.1 c.2 hC : C.toScheme.functionField) := by
    rw [hnatc]
    exact C.toScheme.presheaf.germ_res_apply ((Opens.map C.inclusion.base).map
      (homOfLE (inf_le_left : Uc ⊓ Ud ≤ Uc))) (_root_.genericPoint C.toScheme)
      (genericPoint_mem_nonempty_open C.toScheme _) (C.restrictedCoefficient D c.1)
  have hed : C.toScheme.germToFunctionField (C.inclusion ⁻¹ᵁ (Uc ⊓ Ud)) (C.inclusion.app (Uc ⊓ Ud) rd) =
      (C.restrictedEquation D hD d.1 d.2 hC : C.toScheme.functionField) := by
    rw [hnatd]
    exact C.toScheme.presheaf.germ_res_apply ((Opens.map C.inclusion.base).map
      (homOfLE (inf_le_right : Uc ⊓ Ud ≤ Ud))) (_root_.genericPoint C.toScheme)
      (genericPoint_mem_nonempty_open C.toScheme _) (C.restrictedCoefficient D d.1)
  apply Units.ext
  change C.toScheme.germToFunctionField (C.inclusion ⁻¹ᵁ (Uc ⊓ Ud))
      (C.inclusion.app (Uc ⊓ Ud) (a : Γ(X.toScheme, Uc ⊓ Ud))) =
    (C.restrictedEquation D hD c.1 c.2 hC : C.toScheme.functionField) /
      (C.restrictedEquation D hD d.1 d.2 hC : C.toScheme.functionField)
  rw [eq_div_iff (Units.ne_zero _), ← hed, ← hec, ← map_mul, hcoefC]

/-- On the pulled-back overlap of two charts, the restricted equations have the same
Cartier class: their ratio is the restriction of the transition unit of `D`. -/
theorem restrictedEquation_class_eq (hC : C.NotInSupport D hD) (c d : C.GenericChart D) :
    letI : Nonempty (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
        C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
    cartierEquationClassHom C.toScheme (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet))
        (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC)) =
      cartierEquationClassHom C.toScheme (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet))
        (Additive.ofMul (C.restrictedEquation D hD d.1 d.2 hC)) := by
  letI : Nonempty (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
      C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
  rw [cartierEquationClassHom_eq_iff]
  exact ⟨_, C.germToFunctionField_map_chartTransitionUnit D hD hC c d⟩

/-- The transition unit of `D|_C` between two restricted charts is the image under `i.app`
of the transition unit of `D`: the transition cocycle of `O_C(D|_C)` on the restricted
charts is the image cocycle of `O_X(D)` (item 1b, cocycle level). -/
theorem cartierTransitionUnit_restrictCartier (hC : C.NotInSupport D hD) (c d : C.GenericChart D) :
    letI : Nonempty (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
        C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
    cartierTransitionUnit C.toScheme (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet))
        (C.restrictedEquation D hD c.1 c.2 hC) (C.restrictedEquation D hD d.1 d.2 hC)
        (C.restrictedEquation_class_eq D hD hC c d) =
      Units.map (C.inclusion.app (c.1.chart.openSet ⊓ d.1.chart.openSet)).hom.toMonoidHom
        (C.chartTransitionUnit D c d) := by
  letI : Nonempty (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
      C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
  apply Units.map_injective (C.toScheme.germToFunctionField_injective
    (C.inclusion ⁻¹ᵁ (c.1.chart.openSet ⊓ d.1.chart.openSet)))
  rw [map_cartierTransitionUnit]
  exact (C.germToFunctionField_map_chartTransitionUnit D hD hC c d).symm

/-! ### Gluing: the restricted Cartier divisor `D|_C` -/

/-- The restricted equations glue to a global Cartier divisor on the curve whose
restriction to every pulled-back chart is the class of the restricted equation. -/
theorem exists_restrictCartier (hC : C.NotInSupport D hD) :
    ∃ E : CartierDivisor C.toScheme, ∀ c : C.GenericChart D,
      letI : Nonempty (C.chartPreimage D c.1) :=
        ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
      (cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op E =
        cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
          (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC)) := by
  let cover := fun c : C.GenericChart D => C.chartPreimage D c.1
  have hcover : (⊤ : C.toScheme.Opens) ≤ iSup cover := by
    intro y _
    obtain ⟨c, hyc⟩ := C.exists_genericChart D hD y
    exact Opens.mem_iSup.mpr ⟨c, hyc⟩
  let sf := fun c : C.GenericChart D =>
    letI : Nonempty (C.chartPreimage D c.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
    cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
      (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC))
  have hcompatible : TopCat.Presheaf.IsCompatible (cartierDivisorSheaf C.toScheme).val cover sf := by
    intro c d
    letI : Nonempty (C.chartPreimage D c.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
    letI : Nonempty (C.chartPreimage D d.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
    letI : Nonempty ((cover c ⊓ cover d : C.toScheme.Opens)) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2,
        C.genericLift_mem_chartPreimage D d.1 d.2⟩⟩
    change (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show cover c ⊓ cover d ≤ cover c from inf_le_left)).op
        (cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
          (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC))) =
      (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show cover c ⊓ cover d ≤ cover d from inf_le_right)).op
        (cartierEquationClassHom C.toScheme (C.chartPreimage D d.1)
          (Additive.ofMul (C.restrictedEquation D hD d.1 d.2 hC)))
    rw [cartierEquationClassHom_restrict, cartierEquationClassHom_restrict]
    exact C.restrictedEquation_class_eq D hD hC c d
  obtain ⟨E, hE, -⟩ := (cartierDivisorSheaf C.toScheme).existsUnique_gluing' cover ⊤
    (fun c => homOfLE (show cover c ≤ ⊤ from le_top)) hcover sf hcompatible
  exact ⟨E, hE⟩

/-- The actual restriction `D|_C` of the effective Cartier divisor `D` to the prime curve. -/
def restrictCartier (hC : C.NotInSupport D hD) : CartierDivisor C.toScheme :=
  (C.exists_restrictCartier D hD hC).choose

theorem restrictCartier_spec (hC : C.NotInSupport D hD) (c : C.GenericChart D) :
    letI : Nonempty (C.chartPreimage D c.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
    (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op (C.restrictCartier D hD hC) =
      cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
        (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC)) :=
  (C.exists_restrictCartier D hD hC).choose_spec c

/-- The restricted chart: a regular equation chart of `D|_C` from a chart of `D`. -/
def restrictedChart (hC : C.NotInSupport D hD) (c : C.GenericChart D) :
    RegularCartierEquationChart C.toScheme (C.restrictCartier D hD hC) where
  chart :=
    { openSet := C.chartPreimage D c.1
      nonempty := ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
      equation := C.restrictedEquation D hD c.1 c.2 hC
      represents := (C.restrictCartier_spec D hD hC c).symm }
  coefficient := C.restrictedCoefficient D c.1
  germ_eq := rfl

/-- `D|_C` is an effective Cartier divisor on the curve: the restricted charts cover. -/
theorem restrictCartier_hasRegularEquations (hC : C.NotInSupport D hD) :
    HasRegularCartierEquations C.toScheme (C.restrictCartier D hD hC) := by
  intro y
  obtain ⟨c, hyc⟩ := C.exists_genericChart D hD y
  exact ⟨C.restrictedChart D hD hC c, hyc⟩

/-! ### The intersection subscheme `C ∩ D` and its degree -/

/-- The scheme-theoretic intersection `C ∩ D`: the effective Cartier subscheme of `D|_C`. -/
def intersectionScheme (hC : C.NotInSupport D hD) : Scheme.{u} :=
  effectiveCartierScheme C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC)

/-- The closed immersion `C ∩ D → C`. -/
def intersectionInclusion (hC : C.NotInSupport D hD) : C.intersectionScheme D hD hC ⟶ C.toScheme :=
  effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC)

instance intersectionInclusion_isClosedImmersion (hC : C.NotInSupport D hD) :
    IsClosedImmersion (C.intersectionInclusion D hD hC) :=
  inferInstanceAs (IsClosedImmersion (effectiveCartierInclusion C.toScheme
    (C.restrictCartier D hD hC) (C.restrictCartier_hasRegularEquations D hD hC)))

/-- The closed immersion `C ∩ D → X`, through the curve. -/
def intersectionToSurface (hC : C.NotInSupport D hD) : C.intersectionScheme D hD hC ⟶ X.toScheme :=
  C.intersectionInclusion D hD hC ≫ C.inclusion

instance intersectionToSurface_isClosedImmersion (hC : C.NotInSupport D hD) :
    IsClosedImmersion (C.intersectionToSurface D hD hC) := by
  unfold intersectionToSurface
  infer_instance

/-- `deg(D|_C) = dim_k Γ(C ∩ D, O)`, the candidate right-hand side of Stacks 0AYY on `C`. -/
def intersectionDegree (hC : C.NotInSupport D hD) : ℕ :=
  effectiveCartierDegree C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec

/-- The global sections of the intersection subscheme form a finite-dimensional
`k`-space (proper over `k`, coherent structure sheaf, accepted 02O6 consumer). -/
theorem intersectionDegree_finiteDimensional (hC : C.NotInSupport D hD) :
    letI : IsProper C.toSpec := C.toSpec_isProper
    FiniteDimensional k ((ModuleCohomology.baseFunctor
      (effectiveCartierToSpec C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec) 0).obj
      (_root_.SheafOfModules.unit (C.intersectionScheme D hD hC).ringCatSheaf)) := by
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact effectiveCartierDegree_finiteDimensional C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC) C.toSpec


/-! ### The underlying set of the intersection subscheme -/

/-- Support membership of a regular-equation divisor ideal at a point of a chart is
non-invertibility of the equation's germ there (any integral scheme). -/
theorem mem_support_iff_not_isUnit_germ {Y : Scheme.{u}} [IsIntegral Y] (E : CartierDivisor Y)
    (hE : HasRegularCartierEquations Y E) (c : RegularCartierEquationChart Y E)
    (z : Y) (hz : z ∈ c.chart.openSet) :
    z ∈ (effectiveCartierIdealDataOfRegularEquations Y E hE).support ↔
      ¬ IsUnit (Y.presheaf.germ c.chart.openSet z hz c.coefficient) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVc⟩ :=
    (isBasis_affine_open Y).exists_subset_of_mem_open hz c.chart.openSet.2
  letI : Nonempty V := ⟨⟨z, hzV⟩⟩
  let d := RegularCartierEquationChart.restrict Y E c V hVc
  have hideal : (effectiveCartierIdealDataOfRegularEquations Y E hE).ideal ⟨V, hV⟩ =
      Ideal.span ({d.coefficient} : Set Γ(Y, V)) :=
    effectiveCartierIdealDataOfRegularEquations_ideal_chart Y E hE d hV
  have hmem := Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := effectiveCartierIdealDataOfRegularEquations Y E hE) (U := ⟨V, hV⟩) hzV
  rw [hideal, Y.zeroLocus_span, Y.zeroLocus_singleton] at hmem
  have key : Y.presheaf.germ c.chart.openSet z hz c.coefficient =
      Y.presheaf.germ V z hzV d.coefficient :=
    (Y.presheaf.germ_res_apply (homOfLE hVc) z hzV c.coefficient).symm
  rw [hmem, key]
  exact not_congr (Y.mem_basicOpen d.coefficient z hzV)

/-- A point of the curve lies in the support of `D|_C` exactly when its image lies in
the support of `D` (the stalk map of the closed immersion is a local homomorphism). -/
theorem mem_support_restrictCartier_iff (hC : C.NotInSupport D hD) (y : C.toScheme) :
    y ∈ (effectiveCartierIdealDataOfRegularEquations C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC)).support ↔
      C.inclusion.base y ∈ (effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support := by
  obtain ⟨c, hyc⟩ := C.exists_genericChart D hD y
  rw [mem_support_iff_not_isUnit_germ (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC) (C.restrictedChart D hD hC c) y hyc,
    mem_support_iff_not_isUnit_germ D hD c.1 (C.inclusion.base y) hyc]
  have hgerm := Scheme.stalkMap_germ_apply C.inclusion c.1.chart.openSet y hyc c.1.coefficient
  change ¬ IsUnit (C.toScheme.presheaf.germ (C.chartPreimage D c.1) y hyc
    (C.restrictedCoefficient D c.1)) ↔ _
  rw [restrictedCoefficient, ← hgerm]
  exact not_congr (isUnit_map_iff (C.inclusion.stalkMap y).hom _)

/-- Points of the intersection subscheme map into the support of `D|_C`. -/
theorem intersectionInclusion_base_mem_support (hC : C.NotInSupport D hD)
    (z : C.intersectionScheme D hD hC) :
    (C.intersectionInclusion D hD hC).base z ∈
      (effectiveCartierIdealDataOfRegularEquations C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC)).support := by
  have h := range_effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC)
  have hz : (effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC)).base z ∈
      Set.range (effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC)).base := Set.mem_range_self z
  rw [h] at hz
  exact hz

/-- Every point of the support of `D|_C` lies in the intersection subscheme. -/
theorem exists_intersection_point_of_mem_support (hC : C.NotInSupport D hD) (y : C.toScheme)
    (hy : y ∈ (effectiveCartierIdealDataOfRegularEquations C.toScheme (C.restrictCartier D hD hC)
        (C.restrictCartier_hasRegularEquations D hD hC)).support) :
    ∃ z : C.intersectionScheme D hD hC, (C.intersectionInclusion D hD hC).base z = y := by
  have h := range_effectiveCartierInclusion C.toScheme (C.restrictCartier D hD hC)
    (C.restrictCartier_hasRegularEquations D hD hC)
  have hy' : y ∈ ((effectiveCartierIdealDataOfRegularEquations C.toScheme (C.restrictCartier D hD hC)
      (C.restrictCartier_hasRegularEquations D hD hC)).support : Set C.toScheme) := hy
  rw [← h] at hy'
  exact hy'

/-- The intersection subscheme `C ∩ D` has underlying set `C ∩ Supp D` in the surface. -/
theorem range_intersectionToSurface (hC : C.NotInSupport D hD) :
    Set.range (C.intersectionToSurface D hD hC).base =
      (C : Set X.toScheme) ∩
        ((effectiveCartierIdealDataOfRegularEquations X.toScheme D hD).support : Set X.toScheme) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hz := C.intersectionInclusion_base_mem_support D hD hC z
    refine ⟨C.inclusion_base_mem _, ?_⟩
    change (C.intersectionInclusion D hD hC ≫ C.inclusion).base z ∈ _
    rw [Scheme.comp_base_apply]
    exact (C.mem_support_restrictCartier_iff D hD hC _).mp hz
  · rintro ⟨hxC, hxs⟩
    have hx : x ∈ Set.range C.inclusion.base := by
      rw [C.range_inclusion]
      exact hxC
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨z, rfl⟩ := C.exists_intersection_point_of_mem_support D hD hC y
      ((C.mem_support_restrictCartier_iff D hD hC y).mpr hxs)
    refine ⟨z, ?_⟩
    change (C.intersectionInclusion D hD hC ≫ C.inclusion).base z = _
    rw [Scheme.comp_base_apply]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
