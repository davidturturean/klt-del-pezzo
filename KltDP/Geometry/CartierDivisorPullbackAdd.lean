import KltDP.Geometry.CartierDivisorPullback

/-!
# Additivity of the pullback of Cartier divisors

The accepted `pullbackDivisor π D hD` (pullback of a Cartier divisor `D` with regular equations
along a generic-point-preserving morphism `π` of integral schemes) is glued from the pulled-back
equations of the regular charts of `D`.  This module proves that it is additive: for `D`, `E` and
`D + E` with regular equations,
`pullbackDivisor π (D + E) = pullbackDivisor π D + pullbackDivisor π E` (`pullbackDivisor_add`),
and hence commutes with natural multiples (`pullbackDivisor_nsmul`); regular equations of sums,
multiples and of the zero divisor are constructed (`regularChartMul`,
`hasRegularCartierEquations_add`, `hasRegularCartierEquations_nsmul`); the divisors with regular
equations form an additive submonoid `regularDivisors` on which the pullback is an additive
homomorphism `pullbackDivisorHom`, and an isomorphism of integral schemes preserves the generic
point (`genericPointPreserving_of_isIso`).  Both sides are compared on
the cover of `X` by the preimages of the common opens of a regular chart of each of `D`, `E`,
`D + E`: there the three restrictions are the
classes of the pulled-back equations, and the equation of `D + E` differs from the product of the
equations of `D` and `E` by a regular unit of `Y` (`cartierEquationClassHom_eq_iff`), whose
pullback along `π` is a regular unit of `X`.

This is the additivity of `pullbackDivisor` required by BRIEF24/BRIEF25 task 3 (in particular for
isomorphisms); the transport of the fibre identity of the Frobenius towers itself is not treated
here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierDivisorPullbackAdd

open KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [GenericPointPreserving π]

/-- Restriction of the pulled-back divisor to any nonempty open inside the preimage of a regular
chart of `D`: the class of the pulled-back equation. -/
theorem pullbackDivisor_restrict_le (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
    (c : RegularCartierEquationChart Y D) {W : X.Opens} [Nonempty W]
    (hW : W ≤ π ⁻¹ᵁ c.chart.openSet) :
    (cartierDivisorSheaf X).val.map (homOfLE (show W ≤ ⊤ from le_top)).op (pullbackDivisor π D hD) =
      cartierEquationClassHom X W (Additive.ofMul (pulledEquation π D c)) :=
  (cartierGlobalEquation_restrict X (pullbackDivisor π D hD) (homOfLE hW) (pulledEquation π D c)
    (pullbackDivisor_restrict π D hD c).symm).symm

variable (D E : CartierDivisor Y)

/-- A regular chart of each of `D`, `E` and `D + E`. -/
abbrev TripleChart : Type u :=
  RegularCartierEquationChart Y D × RegularCartierEquationChart Y E ×
    RegularCartierEquationChart Y (D + E)

/-- The common open of the three charts. -/
abbrev tripleOpen (t : TripleChart D E) : Y.Opens :=
  t.1.chart.openSet ⊓ t.2.1.chart.openSet ⊓ t.2.2.chart.openSet

theorem tripleOpen_le_first (t : TripleChart D E) : tripleOpen D E t ≤ t.1.chart.openSet :=
  inf_le_left.trans inf_le_left

theorem tripleOpen_le_second (t : TripleChart D E) : tripleOpen D E t ≤ t.2.1.chart.openSet :=
  inf_le_left.trans inf_le_right

theorem tripleOpen_le_sum (t : TripleChart D E) : tripleOpen D E t ≤ t.2.2.chart.openSet :=
  inf_le_right

omit [IsIntegral X] [GenericPointPreserving π] in
/-- The preimages of the common opens cover `X`. -/
theorem triple_cover (hD : HasRegularCartierEquations Y D) (hE : HasRegularCartierEquations Y E)
    (hDE : HasRegularCartierEquations Y (D + E)) :
    (⊤ : X.Opens) ≤ iSup (fun t : TripleChart D E => π ⁻¹ᵁ tripleOpen D E t) := by
  intro x _
  obtain ⟨c, hc⟩ := hD (π.base x)
  obtain ⟨d, hd⟩ := hE (π.base x)
  obtain ⟨e, he⟩ := hDE (π.base x)
  exact Opens.mem_iSup.mpr ⟨(c, d, e), ⟨⟨hc, hd⟩, he⟩⟩

/-- On the common open of `Y`, the equation of `D + E` and the product of the equations of `D` and
`E` have the same class. -/
theorem tripleChart_equation_class (t : TripleChart D E) :
    cartierEquationClassHom Y (tripleOpen D E t) (Additive.ofMul t.2.2.chart.equation) =
      cartierEquationClassHom Y (tripleOpen D E t)
        (Additive.ofMul (t.1.chart.equation * t.2.1.chart.equation)) := by
  rw [ofMul_mul, map_add,
    cartierGlobalEquation_restrict Y (D + E) (homOfLE (tripleOpen_le_sum D E t))
      t.2.2.chart.equation t.2.2.chart.represents,
    cartierGlobalEquation_restrict Y D (homOfLE (tripleOpen_le_first D E t))
      t.1.chart.equation t.1.chart.represents,
    cartierGlobalEquation_restrict Y E (homOfLE (tripleOpen_le_second D E t))
      t.2.1.chart.equation t.2.1.chart.represents, map_add]

/-- The pulled-back equations satisfy the same relation on the preimage. -/
theorem pulledEquation_sum_class (t : TripleChart D E) :
    cartierEquationClassHom X (π ⁻¹ᵁ tripleOpen D E t)
        (Additive.ofMul (pulledEquation π (D + E) t.2.2)) =
      cartierEquationClassHom X (π ⁻¹ᵁ tripleOpen D E t)
        (Additive.ofMul (pulledEquation π D t.1 * pulledEquation π E t.2.1)) := by
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff Y _ _ _).mp (tripleChart_equation_class D E t)
  have ha' : (Y.germToFunctionField (tripleOpen D E t)) (a : Γ(Y, _)) =
      (t.2.2.chart.equation : Y.functionField) /
        ((t.1.chart.equation : Y.functionField) * t.2.1.chart.equation) := by
    have := congrArg Units.val ha
    rwa [Units.val_div_eq_div_val, Units.val_mul] at this
  rw [cartierEquationClassHom_eq_iff]
  refine ⟨Units.map (π.appLE (tripleOpen D E t) (π ⁻¹ᵁ tripleOpen D E t) le_rfl).hom.toMonoidHom a,
    ?_⟩
  apply Units.ext
  rw [Units.val_div_eq_div_val, Units.val_mul, pulledEquation_val, pulledEquation_val,
    pulledEquation_val]
  change (X.germToFunctionField (π ⁻¹ᵁ tripleOpen D E t))
      (π.appLE (tripleOpen D E t) _ le_rfl (a : Γ(Y, _))) =
    (functionFieldMap π).hom t.2.2.chart.equation /
      ((functionFieldMap π).hom t.1.chart.equation * (functionFieldMap π).hom t.2.1.chart.equation)
  rw [← map_mul, ← map_div₀, ← ha', ← functionFieldMap_germ_appLE]

/-- **Additivity of the pullback of Cartier divisors**: for `D`, `E`, `D + E` with regular
equations, `π^*(D + E) = π^*D + π^*E`. -/
theorem pullbackDivisor_add (hD : HasRegularCartierEquations Y D)
    (hE : HasRegularCartierEquations Y E) (hDE : HasRegularCartierEquations Y (D + E)) :
    pullbackDivisor π (D + E) hDE = pullbackDivisor π D hD + pullbackDivisor π E hE := by
  apply cartierDivisor_eq_of_restrict_eq X (fun t : TripleChart D E => π ⁻¹ᵁ tripleOpen D E t)
    (triple_cover π D E hD hE hDE)
  intro t
  rw [map_add,
    pullbackDivisor_restrict_le π (D + E) hDE t.2.2 (fun _ hx => tripleOpen_le_sum D E t hx),
    pullbackDivisor_restrict_le π D hD t.1 (fun _ hx => tripleOpen_le_first D E t hx),
    pullbackDivisor_restrict_le π E hE t.2.1 (fun _ hx => tripleOpen_le_second D E t hx),
    ← map_add, ← ofMul_mul]
  exact pulledEquation_sum_class π D E t

/-- The pullback does not depend on the presentation of the divisor. -/
theorem pullbackDivisor_congr {D D' : CartierDivisor Y} (h : D = D')
    (hD : HasRegularCartierEquations Y D) (hD' : HasRegularCartierEquations Y D') :
    pullbackDivisor π D hD = pullbackDivisor π D' hD' := by
  subst h
  rfl

/-! ### Regular equations of sums and multiples -/

/-- The common open of a regular chart of `D` and a regular chart of `E`. -/
abbrev mulOpen (c : RegularCartierEquationChart Y D) (d : RegularCartierEquationChart Y E) :
    Y.Opens :=
  c.chart.openSet ⊓ d.chart.openSet

/-- The product of the two equations represents `D + E` on the common open. -/
theorem mul_represents (c : RegularCartierEquationChart Y D)
    (d : RegularCartierEquationChart Y E) :
    cartierEquationClassHom Y (mulOpen D E c d)
        (Additive.ofMul (c.chart.equation * d.chart.equation)) =
      (cartierDivisorSheaf Y).val.map (homOfLE (show mulOpen D E c d ≤ ⊤ from le_top)).op
        (D + E) := by
  rw [ofMul_mul, map_add, map_add,
    cartierGlobalEquation_restrict Y D (homOfLE (inf_le_left : mulOpen D E c d ≤ _))
      c.chart.equation c.chart.represents,
    cartierGlobalEquation_restrict Y E (homOfLE (inf_le_right : mulOpen D E c d ≤ _))
      d.chart.equation d.chart.represents]

/-- The product equation chart of `D + E`. -/
def chartMul (c : RegularCartierEquationChart Y D) (d : RegularCartierEquationChart Y E) :
    CartierEquationChart Y (D + E) :=
  { openSet := mulOpen D E c d
    nonempty := inferInstance
    equation := c.chart.equation * d.chart.equation
    represents := mul_represents D E c d }

/-- The product of the two regular coefficients, restricted to the common open. -/
def mulCoefficient (c : RegularCartierEquationChart Y D) (d : RegularCartierEquationChart Y E) :
    Γ(Y, mulOpen D E c d) :=
  Y.presheaf.map (homOfLE (inf_le_left : mulOpen D E c d ≤ _)).op c.coefficient *
    Y.presheaf.map (homOfLE (inf_le_right : mulOpen D E c d ≤ _)).op d.coefficient

theorem germ_mulCoefficient (c : RegularCartierEquationChart Y D)
    (d : RegularCartierEquationChart Y E) :
    Y.germToFunctionField (mulOpen D E c d) (mulCoefficient D E c d) =
      ((c.chart.equation * d.chart.equation : Y.functionFieldˣ) : Y.functionField) := by
  change (Y.germToFunctionField (mulOpen D E c d)).hom (_ * _) = _
  rw [map_mul, Units.val_mul]
  exact congrArg₂ (· * ·)
    ((TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE inf_le_left) (genericPoint Y) _ _).trans
      c.germ_eq)
    ((TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE inf_le_right) (genericPoint Y) _ _).trans
      d.germ_eq)

/-- The product of regular charts of `D` and `E` is a regular chart of `D + E` on the common
open. -/
def regularChartMul (c : RegularCartierEquationChart Y D) (d : RegularCartierEquationChart Y E) :
    RegularCartierEquationChart Y (D + E) :=
  { chart := chartMul D E c d
    coefficient := mulCoefficient D E c d
    germ_eq := germ_mulCoefficient D E c d }

theorem hasRegularCartierEquations_add (hD : HasRegularCartierEquations Y D)
    (hE : HasRegularCartierEquations Y E) : HasRegularCartierEquations Y (D + E) := by
  intro y
  obtain ⟨c, hc⟩ := hD y
  obtain ⟨d, hd⟩ := hE y
  exact ⟨regularChartMul D E c d, ⟨hc, hd⟩⟩

/-- The trivial regular chart of the zero divisor. -/
def regularChartZero : RegularCartierEquationChart Y 0 where
  chart :=
    { openSet := ⊤
      nonempty := ⟨⟨genericPoint Y, trivial⟩⟩
      equation := 1
      represents := by rw [ofMul_one, map_zero, map_zero] }
  coefficient := 1
  germ_eq := by rw [map_one, Units.val_one]

theorem hasRegularCartierEquations_zero : HasRegularCartierEquations Y 0 :=
  fun _ => ⟨regularChartZero, trivial⟩

theorem hasRegularCartierEquations_nsmul (hD : HasRegularCartierEquations Y D) :
    ∀ n : ℕ, HasRegularCartierEquations Y (n • D)
  | 0 => by
    rw [zero_nsmul]
    exact hasRegularCartierEquations_zero
  | n + 1 => by
    rw [succ_nsmul]
    exact hasRegularCartierEquations_add _ _ (hasRegularCartierEquations_nsmul hD n) hD

/-- The additivity without the witness for the sum. -/
theorem pullbackDivisor_add' (hD : HasRegularCartierEquations Y D)
    (hE : HasRegularCartierEquations Y E) :
    pullbackDivisor π (D + E) (hasRegularCartierEquations_add D E hD hE) =
      pullbackDivisor π D hD + pullbackDivisor π E hE :=
  pullbackDivisor_add π D E hD hE _

theorem pullbackDivisor_zero (h0 : HasRegularCartierEquations Y 0) :
    pullbackDivisor π (0 : CartierDivisor Y) h0 = 0 := by
  have h := pullbackDivisor_add π 0 0 h0 h0 (hasRegularCartierEquations_add 0 0 h0 h0)
  rw [pullbackDivisor_congr π (add_zero (0 : CartierDivisor Y)) _ h0] at h
  exact left_eq_add.mp h

/-- **The pullback of Cartier divisors commutes with natural multiples.** -/
theorem pullbackDivisor_nsmul (hD : HasRegularCartierEquations Y D) :
    ∀ (n : ℕ) (hn : HasRegularCartierEquations Y (n • D)),
      pullbackDivisor π (n • D) hn = n • pullbackDivisor π D hD
  | 0, hn => by
    rw [pullbackDivisor_congr π (zero_nsmul D) hn hasRegularCartierEquations_zero,
      pullbackDivisor_zero, zero_nsmul]
  | n + 1, hn => by
    rw [pullbackDivisor_congr π (succ_nsmul D n) hn
      (hasRegularCartierEquations_add _ _ (hasRegularCartierEquations_nsmul D hD n) hD),
      pullbackDivisor_add, pullbackDivisor_nsmul hD n (hasRegularCartierEquations_nsmul D hD n),
      succ_nsmul]

/-! ### The pullback as an additive homomorphism -/

/-- The Cartier divisors with regular equations form an additive submonoid. -/
def regularDivisors (S : Scheme.{u}) [IsIntegral S] : AddSubmonoid (CartierDivisor S) where
  carrier := {D | HasRegularCartierEquations S D}
  add_mem' {D E} hD hE := hasRegularCartierEquations_add D E hD hE
  zero_mem' := hasRegularCartierEquations_zero

theorem mem_regularDivisors {S : Scheme.{u}} [IsIntegral S] (D : CartierDivisor S) :
    D ∈ regularDivisors S ↔ HasRegularCartierEquations S D := Iff.rfl

/-- **The pullback of Cartier divisors with regular equations, as an additive homomorphism.** -/
def pullbackDivisorHom : regularDivisors Y →+ CartierDivisor X where
  toFun D := pullbackDivisor π D.1 D.2
  map_zero' := pullbackDivisor_zero π _
  map_add' D E := pullbackDivisor_add π D.1 E.1 D.2 E.2 _

theorem pullbackDivisorHom_apply (D : regularDivisors Y) :
    pullbackDivisorHom π D = pullbackDivisor π D.1 D.2 := rfl

/-- An isomorphism of integral schemes preserves the generic point (an isomorphism is an open
immersion). -/
instance genericPointPreserving_of_isIso (g : X ⟶ Y) [IsIso g] : GenericPointPreserving g :=
  ⟨genericPoint_eq_of_isOpenImmersion g⟩

end KltDP.Geometry.CartierDivisorPullbackAdd
