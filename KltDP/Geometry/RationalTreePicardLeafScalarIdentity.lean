import KltDP.Geometry.RationalTreePicardLeafNodeGluing
import KltDP.Geometry.RationalTreePicardRationalComponentFrame

/-!
# The scalar identity and the unconditional trivialization

The leaf gauge unit is the inverse of the node-scalar gauge unit
`nodeScalarGauge L f h frameC frameC'`, the constant section of the inverse node scalar on
the leaf open. Its scalar identity `LeafScalarIdentity` is a computation with constant
sections: restriction of constants (`res_baseSections`), the value of a constant section on
the affine chart (`fromSpec_app_baseSections`, through `Spec_map_baseToAffineSectionsMap`
and the naturality of `ΓSpecIso`), the value on the closed leaf piece, and the description
of the lifted node scalar as the constant section of the node scalar
(`LeafNodeChart.chartScalarSection_eq`). The product of the two constants is the constant
`g⁻¹ * g = 1`.

Consequently `leafNodeUnitIso : L.obj ≅ unit` is the UNCONDITIONAL trivialization of the
original line bundle on the curve, given frames on the leaf component and on the
complementary union and the leaf-node chart data (no scalar or coordinate hypothesis).
With the frames produced from zero component exponents (`componentFrameOfExponentZero`),
`leafNodeUnitIsoOfExponentZero` and `leafNodeUnitIsoOfExponentZero₂` state this with the
exponent hypotheses only.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction TransitionUnitGluing

section Constants

/-- The section map of a morphism commutes with restriction from the whole space. -/
theorem app_map_le_top {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens) (z : Γ(X, ⊤)) :
    g.app W (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op z) =
      Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ W ≤ ⊤)).op (g.appTop z) :=
  congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ W) => φ z)
    (g.naturality (homOfLE (le_top : W ≤ ⊤)).op)

/-- `Spec` of a ring homomorphism on global sections, through `ΓSpecIso`. -/
theorem Spec_map_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) :=
  (congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ r) (Scheme.ΓSpecIso_inv_naturality φ)).symm

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- Restriction of a constant section is the constant section. -/
theorem res_baseSections {V W : X.Opens} (hWV : W ≤ V) (c : k) :
    res X hWV (baseSections f V c) = baseSections f W c := by
  change res X hWV (res X le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
    res X le_top (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
  rw [res_res]

/-- A constant section, read on the affine chart `Spec Γ(X, U)`, is the constant of the
base-to-sections homomorphism. -/
theorem fromSpec_app_baseSections (U : X.affineOpens) (W : X.Opens) (c : k) :
    U.2.fromSpec.app W (baseSections f W c) =
      (Spec Γ(X, U.1)).presheaf.map (homOfLE (le_top : U.2.fromSpec ⁻¹ᵁ W ≤ ⊤)).op
        ((Scheme.ΓSpecIso Γ(X, U.1)).inv (baseToAffineSectionsMap f U.2 c)) := by
  change U.2.fromSpec.app W (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) = _
  rw [app_map_le_top]
  change (Spec Γ(X, U.1)).presheaf.map (homOfLE (le_top : U.2.fromSpec ⁻¹ᵁ W ≤ ⊤)).op
    ((U.2.fromSpec ≫ f).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = _
  rw [← Spec_map_baseToAffineSectionsMap f U.2, Spec_map_appTop_ΓSpecIso_inv]

end Constants

section ScalarIdentity

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)

/-- The lifted node scalar of the chart is the constant section of the node scalar on the
closed leaf piece. -/
theorem LeafNodeChart.chartScalarSection_eq :
    h.chartScalarSection L f frameC frameC' =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv
        (Ideal.Quotient.mk (componentChartIdeal X {C} U)
          (baseToAffineSectionsMap f U.2 (h.chartScalar L f frameC frameC' : k))) :=
  rfl

/-- The inverse node-scalar gauge unit is the constant section of the inverse node scalar. -/
theorem coe_nodeScalarGauge_inv :
    (((nodeScalarGauge L f h frameC frameC')⁻¹ : Γ(X, leafOpen X C)ˣ) :
        Γ(X, leafOpen X C)) =
      baseSections f (leafOpen X C) (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k) :=
  rfl

/-- The constant section of the inverse node scalar on the chart, read on the closed leaf
piece over `W`, is the constant of the inverse node scalar. -/
theorem chart_baseSections_value (W : X.Opens) (c : k) :
    (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫ U.2.fromSpec).app W
        (baseSections f W c) =
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
          U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv
          (Ideal.Quotient.mk (componentChartIdeal X {C} U)
            (baseToAffineSectionsMap f U.2 c))) := by
  change (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)).app
    (U.2.fromSpec ⁻¹ᵁ W) (U.2.fromSpec.app W (baseSections f W c)) = _
  rw [fromSpec_app_baseSections, app_map_le_top,
    Spec_map_appTop_ΓSpecIso_inv
      (CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X {C} U)))]
  rfl

/-- Preimages along a composite, reassociated. -/
theorem preimage_comp_assoc {X Y Z T : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (g₃ : Z ⟶ T)
    (V : T.Opens) :
    (g₁ ≫ g₂) ⁻¹ᵁ (g₃ ⁻¹ᵁ V) = (g₁ ≫ (g₂ ≫ g₃)) ⁻¹ᵁ V :=
  rfl

/-- The section map of a composite, followed by a further morphism, evaluated, and compared
with any morphism equal to the full composite. Stated for arbitrary morphisms so that its
instances need no unfolding of the specific morphisms. -/
theorem comp_congr_app_apply {X Y Z T : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (g₃ : Z ⟶ T)
    {m : X ⟶ T} (e : m = g₁ ≫ (g₂ ≫ g₃)) (V : T.Opens) (x : Γ(T, V)) :
    (g₁ ≫ g₂).app (g₃ ⁻¹ᵁ V) (g₃.app V x) =
      X.presheaf.map (eqToHom ((preimage_comp_assoc g₁ g₂ g₃ V).trans
        (congrArg (fun m => m ⁻¹ᵁ V) e.symm))).op (m.app V x) := by
  subst e
  change (g₁ ≫ (g₂ ≫ g₃)).app V x =
    X.presheaf.map (𝟙 (op ((g₁ ≫ (g₂ ≫ g₃)) ⁻¹ᵁ V))) ((g₁ ≫ (g₂ ≫ g₃)).app V x)
  exact (ConcreteCategory.congr_hom (X.presheaf.map_id (op ((g₁ ≫ (g₂ ≫ g₃)) ⁻¹ᵁ V)))
    ((g₁ ≫ (g₂ ≫ g₃)).app V x)).symm

/-- Restriction along the reassociated equality of preimages agrees with restriction along
the equality of the full composite. Stated for arbitrary morphisms. -/
theorem map_eqToHom_op_assoc {X Y Z T : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (g₃ : Z ⟶ T)
    {m : X ⟶ T} (e : m = g₁ ≫ (g₂ ≫ g₃)) (V : T.Opens) (z : Γ(X, m ⁻¹ᵁ V)) :
    X.presheaf.map (eqToHom ((preimage_comp_assoc g₁ g₂ g₃ V).trans
        (congrArg (fun m => m ⁻¹ᵁ V) e.symm))).op z =
      X.presheaf.map (eqToHom (congrArg (fun m => m ⁻¹ᵁ V) e.symm)).op z := by
  subst e
  rfl

/-- The transported lifted node scalar, with its restriction taken along the reassociated
equality of preimages. -/
theorem transportedNodeScalar_eq (W : X.Opens) :
    transportedNodeScalar L f h frameC frameC' =
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
            (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
          (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op
        ((Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
            U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op (h.chartScalarSection L f frameC frameC')) :=
  (map_eqToHom_op_assoc (componentUnionChartIso X {C} U).hom
    (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C})
    (closedComponentInclusion_fromSpec X {C} U) W _).symm

/-- The inverse node-scalar gauge unit, read on the chart piece of the leaf component, is
the constant of the inverse node scalar read through the closed piece of the chart. -/
theorem leafGauge_chart_value (W : X.Opens) (hWl : W ≤ leafOpen X C) :
    ((componentUnionChartIso X {C} U).hom ≫ (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι).app
        (componentUnionInclusion X {C} ⁻¹ᵁ W)
        ((componentUnionInclusion X {C}).app W
          (res X hWl (((nodeScalarGauge L f h frameC frameC')⁻¹ : Γ(X, leafOpen X C)ˣ) :
            Γ(X, leafOpen X C)))) =
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
            (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
          (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫ U.2.fromSpec).app W
          (baseSections f W (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k))) := by
  rw [coe_nodeScalarGauge_inv, res_baseSections]
  exact comp_congr_app_apply _ _ _ (closedComponentInclusion_fromSpec X {C} U) W _

/-- The product of the constant of the inverse node scalar (read through the closed piece
of the chart) and the transported lifted node scalar is `1`. -/
theorem constant_product_one (W : X.Opens) :
    (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
            (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
          (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫ U.2.fromSpec).app W
          (baseSections f W (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k))) *
      transportedNodeScalar L f h frameC frameC' = 1 := by
  -- both constants are values of one ring homomorphism from the base field
  have hβ : (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
            (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
          (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫ U.2.fromSpec).app W
          (baseSections f W (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k))) =
      (baseToAffineSectionsMap f U.2 ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X {C} U)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
            U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
              (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
            (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op)
        (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k) :=
    congrArg (fun y => (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
            (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
          (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op y)
      (chart_baseSections_value (C := C) (U := U) f W
        (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k))
  have hT : transportedNodeScalar L f h frameC frameC' =
      (baseToAffineSectionsMap f U.2 ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X {C} U)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
            U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
              (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
            (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op)
        (h.chartScalar L f frameC frameC' : k) :=
    (transportedNodeScalar_eq L f h frameC frameC' W).trans
      (congrArg (fun σ => (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
              (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
            (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op
          ((Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
            (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
              U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op σ))
        (LeafNodeChart.chartScalarSection_eq L f h frameC frameC'))
  have hprod : (baseToAffineSectionsMap f U.2 ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X {C} U)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
            U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
              (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
            (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op)
        (((h.chartScalar L f frameC frameC')⁻¹ : kˣ) : k) *
      (baseToAffineSectionsMap f U.2 ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (componentChartIdeal X {C} U)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).inv ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
            U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op ≫
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
          (eqToHom ((preimage_comp_assoc (componentUnionChartIso X {C} U).hom
              (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι (componentUnionInclusion X {C}) W).trans
            (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm))).op)
        (h.chartScalar L f frameC frameC' : k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  exact (congrArg₂ (fun x y => x * y) hβ hT).trans hprod

/-- The scalar identity holds for the inverse of the node-scalar gauge unit. -/
theorem leafScalarIdentity_nodeScalarGauge_inv :
    LeafScalarIdentity L f h frameC frameC' (nodeScalarGauge L f h frameC frameC')⁻¹ := by
  intro W _ hWl
  rw [leafGauge_chart_value L f h frameC frameC' W hWl]
  exact constant_product_one L f h frameC frameC' W

/-- The UNCONDITIONAL trivialization: a line bundle on the curve with frames on the leaf
component and on the complementary union, at a leaf-node chart, is trivial. -/
def leafNodeUnitIso (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q}) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIsoOfScalar L f h frameC frameC' hcut (nodeScalarGauge L f h frameC frameC')⁻¹
    (leafScalarIdentity_nodeScalarGauge_inv L f h frameC frameC')

/-- Zero component exponent on the leaf `P^1` and a frame on the complementary union: the
line bundle is trivial. -/
def leafNodeUnitIsoOfExponentZero (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hzero : componentExponent k X {C} e L = 0)
    (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIso L f h (componentFrameOfExponentZero k X {C} e L hzero) frameC' hcut

/-- The leaf component and the union of the other components both identified with the
projective line, with zero component exponents: the line bundle is trivial. -/
def leafNodeUnitIsoOfExponentZero₂ (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (e' : componentUnionScheme X ({C}ᶜ) ≅ projectiveSpace k 1)
    (hzero : componentExponent k X {C} e L = 0)
    (hzero' : componentExponent k X ({C}ᶜ) e' L = 0) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIso L f h (componentFrameOfExponentZero k X {C} e L hzero)
    (componentFrameOfExponentZero k X ({C}ᶜ) e' L hzero') hcut

end ScalarIdentity

end KltDP.Geometry.RationalTreePicard
