import KltDP.Examples.FrobeniusStageOneCharts
import KltDP.Geometry.ProjectiveSpaceTupleMorphism

/-!
# The eight `(2,2)`-monomials vanishing at the origin, on the five charts of stage `1`

The blowup `Bl_p(P¹ × P¹)` is embedded in `P⁷` by the bihomogeneous forms of bidegree `(2,2)` vanishing
at `p = ([1:0],[1:0])`: the eight monomials `x_a y_b T_c` with `T_0 = x_0 y_1`, `T_1 = x_1 y_0`,
`T_2 = x_1 y_1` (`monoX`, `monoY`, `monoT`; the ninth monomial `x_0² y_0²` does not vanish at `p`). This is
the composite of `Bl_p ⊂ P¹ × P¹ × P²` (graph of `[x_0 y_1 : x_1 y_0 : x_1 y_1]`) with the eight relevant
Segre coordinates; it is *not* a closed subscheme of `(P¹)³` (a point of `P¹ × P¹` is never the zero
locus of two sections of a line bundle, see the F09 record).

On each affine chart of stage `1` the monomials, divided by the chart's normaliser, are polynomials
in the chart coordinates: the data `ChartTuple` (indices `xi`, `yi` of the product chart the chart lies
over, the pulled-back product coordinates `origU`, `origV`, the normalising `T`-index `ti`, the
`T`-factors `tf`, and the normaliser `e` with `tf τ * e = x-factor * y-factor`). The tuple is
`tuple i = xF (monoX i) * yF (monoY i) * tf (monoT i)`, equal to `1` at the chart's own monomial `ni`
(`tuple_ni`), and `morphism = tupleMorphism 7 planeConstants tuple ni` is the chart's map to `P⁷`.

Generic scaling algebra (for the compatibility of two charts on an overlap, via two ring maps
`α β : k[u][v] →+* S`): `tuple_scale_of_relations` derives `α (tuple i) = α (tuple D'.ni) * β (tuple' i)`
for all `i` from the relations between the pulled-back product coordinates (equal on a common chart,
mutually inverse otherwise) and invertibility of `α e`; the `T`-factor identity is obtained by cancelling
`α e` (`tf_scale_of_isUnit`), and `α e` is a unit as soon as the two charts differ in a product index
(`isUnit_e_of_xi_ne`, `isUnit_e_of_yi_ne`) or `e = 1`. The pair of Rees charts (`e = u` resp. `v`, same
product indices) is handled by `tuple_scale` with its `T`-relation supplied directly.

The five instances: `dataU` (selected Rees chart, `(u, w)`, `v = u w`), `dataV` (second Rees chart,
polynomial model `(v, w')`, `u = w' v`), `data10`, `data01`, `data11` (product charts), collected as
`stageOneData : Fin 5 → ChartTuple k` matching `stageOneChart`; `stageOneData_xi/_yi/_origU/_origV` tie
them to `chartIndex`/`chartBlowdown` of the chart module. No scheme-level compatibility is proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStageOneTuples

open KltDP.Geometry KltDP.Geometry.ProjectiveChart
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusBlowupSmooth
open FrobeniusTowerSecondChart FrobeniusStageOneCharts

variable {k : Type u} [Field k]

/-! ## The eight monomials -/

/-- The `x`-index `a` of the monomial `x_a y_b T_c`. -/
def monoX : Fin 8 → Fin 2 := ![0, 0, 0, 1, 1, 0, 0, 1]

/-- The `y`-index `b` of the monomial `x_a y_b T_c`. -/
def monoY : Fin 8 → Fin 2 := ![0, 0, 0, 0, 0, 1, 1, 1]

/-- The `T`-index `c` of the monomial `x_a y_b T_c`. -/
def monoT : Fin 8 → Fin 3 := ![0, 1, 2, 1, 2, 0, 2, 2]

/-- `T_τ = x_{tX τ} y_{tY τ}`: the `x`-index. -/
def tX : Fin 3 → Fin 2 := ![0, 1, 1]

/-- `T_τ = x_{tX τ} y_{tY τ}`: the `y`-index. -/
def tY : Fin 3 → Fin 2 := ![1, 0, 1]

/-- Data of an affine chart of stage `1` for the monomial tuple. -/
structure ChartTuple (k : Type u) [Field k] where
  /-- the first index of the product chart the chart lies over -/
  xi : Fin 2
  /-- the second index of the product chart the chart lies over -/
  yi : Fin 2
  /-- the pulled-back first product coordinate -/
  origU : planeRing k
  /-- the pulled-back second product coordinate -/
  origV : planeRing k
  /-- the normalising `T`-index -/
  ti : Fin 3
  /-- the chart's own monomial (where the tuple is `1`) -/
  ni : Fin 8
  /-- the normaliser, with `tf τ * e = x-factor * y-factor` -/
  e : planeRing k
  /-- the normalised `T`-coordinates -/
  tf : Fin 3 → planeRing k
  monoX_ni : monoX ni = xi
  monoY_ni : monoY ni = yi
  monoT_ni : monoT ni = ti
  tf_ti : tf ti = 1
  tf_spec : ∀ τ, tf τ * e = (if tX τ = xi then 1 else origU) * (if tY τ = yi then 1 else origV)
  e_dvd_origU : e ∣ origU
  e_dvd_origV : e ∣ origV

namespace ChartTuple

variable (D : ChartTuple k)

/-- The `x`-factor `x_a / x_{xi}`. -/
def xF (a : Fin 2) : planeRing k := if a = D.xi then 1 else D.origU

/-- The `y`-factor `y_b / y_{yi}`. -/
def yF (b : Fin 2) : planeRing k := if b = D.yi then 1 else D.origV

/-- The monomial tuple of the chart. -/
def tuple (i : Fin 8) : planeRing k := D.xF (monoX i) * D.yF (monoY i) * D.tf (monoT i)

theorem xF_xi : D.xF D.xi = 1 := if_pos rfl

theorem yF_yi : D.yF D.yi = 1 := if_pos rfl

theorem tuple_ni : D.tuple D.ni = 1 := by
  rw [tuple, D.monoX_ni, D.monoY_ni, D.monoT_ni, xF_xi, yF_yi, D.tf_ti, mul_one, mul_one]

/-- The chart's morphism to `P⁷`. -/
def morphism : plane k ⟶ projectiveSpace k 7 :=
  tupleMorphism 7 planeConstants D.tuple D.ni D.tuple_ni

theorem morphism_structure : D.morphism ≫ projectiveSpaceToSpec k 7 = planeStructure :=
  tupleMorphism_structure 7 planeConstants D.tuple D.ni D.tuple_ni

/-! ## Scaling algebra for two charts -/

section Scale

variable {S : Type u} [CommRing S] (D' : ChartTuple k) (α β : planeRing k →+* S)

theorem fin_two_eq_of_ne : ∀ a i i' : Fin 2, a ≠ i → i ≠ i' → a = i' := by decide

/-- One-factor scaling from the relation between the two pulled-back coordinates. -/
theorem factor_scale_two (c c' : planeRing k) (i i' a : Fin 2)
    (heq : i = i' → α c = β c') (hmul : i ≠ i' → α c * β c' = 1) :
    α (if a = i then 1 else c) = α (if i' = i then 1 else c) * β (if a = i' then 1 else c') := by
  by_cases hii : i = i'
  · subst hii
    by_cases ha : a = i
    · rw [if_pos ha, if_pos rfl, if_pos ha, map_one, map_one, mul_one]
    · rw [if_neg ha, if_pos rfl, if_neg ha, map_one, one_mul]
      exact heq rfl
  · rw [if_neg (Ne.symm hii)]
    by_cases ha : a = i
    · rw [if_pos ha, if_neg (by rw [ha]; exact hii), map_one]
      exact (hmul hii).symm
    · rw [if_neg ha, if_pos (fin_two_eq_of_ne a i i' ha hii), map_one, mul_one]

theorem xF_scale (heq : D.xi = D'.xi → α D.origU = β D'.origU)
    (hmul : D.xi ≠ D'.xi → α D.origU * β D'.origU = 1) (a : Fin 2) :
    α (D.xF a) = α (D.xF D'.xi) * β (D'.xF a) :=
  factor_scale_two α β D.origU D'.origU D.xi D'.xi a heq hmul

theorem yF_scale (heq : D.yi = D'.yi → α D.origV = β D'.origV)
    (hmul : D.yi ≠ D'.yi → α D.origV * β D'.origV = 1) (b : Fin 2) :
    α (D.yF b) = α (D.yF D'.yi) * β (D'.yF b) :=
  factor_scale_two α β D.origV D'.origV D.yi D'.yi b heq hmul

theorem tf_mul_e (σ : Fin 3) : α (D.tf σ) * α D.e = α (D.xF (tX σ)) * α (D.yF (tY σ)) := by
  rw [← map_mul, D.tf_spec σ, map_mul]
  rfl

/-- The `T`-relation follows from the `x`- and `y`-relations when the normaliser is a unit. -/
theorem tf_scale_of_isUnit (hx : ∀ a, α (D.xF a) = α (D.xF D'.xi) * β (D'.xF a))
    (hy : ∀ b, α (D.yF b) = α (D.yF D'.yi) * β (D'.yF b)) (he : IsUnit (α D.e)) (τ : Fin 3) :
    α (D.tf τ) = α (D.tf D'.ti) * β (D'.tf τ) := by
  apply he.mul_left_cancel
  have hτ : α (D.tf τ) * α D.e =
      (α (D.xF D'.xi) * β (D'.xF (tX τ))) * (α (D.yF D'.yi) * β (D'.yF (tY τ))) := by
    rw [tf_mul_e D α τ, hx (tX τ), hy (tY τ)]
  have hti : α (D.tf D'.ti) * α D.e =
      (α (D.xF D'.xi) * β (D'.xF (tX D'.ti))) * (α (D.yF D'.yi) * β (D'.yF (tY D'.ti))) := by
    rw [tf_mul_e D α D'.ti, hx (tX D'.ti), hy (tY D'.ti)]
  have hτ' : β (D'.tf τ) * β D'.e = β (D'.xF (tX τ)) * β (D'.yF (tY τ)) := tf_mul_e D' β τ
  have hti' : β D'.e = β (D'.xF (tX D'.ti)) * β (D'.yF (tY D'.ti)) := by
    have h := tf_mul_e D' β D'.ti
    rwa [D'.tf_ti, map_one, one_mul] at h
  calc α D.e * α (D.tf τ) = α (D.tf τ) * α D.e := mul_comm _ _
    _ = (α (D.xF D'.xi) * β (D'.xF (tX τ))) * (α (D.yF D'.yi) * β (D'.yF (tY τ))) := hτ
    _ = (α (D.xF D'.xi) * α (D.yF D'.yi)) * (β (D'.tf τ) * β D'.e) := by
        rw [hτ']
        ring
    _ = (α (D.xF D'.xi) * α (D.yF D'.yi)) *
          (β (D'.xF (tX D'.ti)) * β (D'.yF (tY D'.ti))) * β (D'.tf τ) := by
        rw [← hti']
        ring
    _ = α (D.tf D'.ti) * α D.e * β (D'.tf τ) := by
        rw [hti]
        ring
    _ = α D.e * (α (D.tf D'.ti) * β (D'.tf τ)) := by ring

/-- **Scaling of the whole tuple** from the three factor relations. -/
theorem tuple_scale (hx : ∀ a, α (D.xF a) = α (D.xF D'.xi) * β (D'.xF a))
    (hy : ∀ b, α (D.yF b) = α (D.yF D'.yi) * β (D'.yF b))
    (ht : ∀ τ, α (D.tf τ) = α (D.tf D'.ti) * β (D'.tf τ)) (i : Fin 8) :
    α (D.tuple i) = α (D.tuple D'.ni) * β (D'.tuple i) := by
  simp only [tuple, map_mul, D'.monoX_ni, D'.monoY_ni, D'.monoT_ni]
  rw [hx (monoX i), hy (monoY i), ht (monoT i)]
  ring

/-- Scaling of the whole tuple from the coordinate relations and invertibility of the normaliser. -/
theorem tuple_scale_of_relations (hxeq : D.xi = D'.xi → α D.origU = β D'.origU)
    (hxmul : D.xi ≠ D'.xi → α D.origU * β D'.origU = 1)
    (hyeq : D.yi = D'.yi → α D.origV = β D'.origV)
    (hymul : D.yi ≠ D'.yi → α D.origV * β D'.origV = 1) (he : IsUnit (α D.e)) (i : Fin 8) :
    α (D.tuple i) = α (D.tuple D'.ni) * β (D'.tuple i) :=
  tuple_scale D D' α β (xF_scale D D' α β hxeq hxmul) (yF_scale D D' α β hyeq hymul)
    (tf_scale_of_isUnit D D' α β (xF_scale D D' α β hxeq hxmul) (yF_scale D D' α β hyeq hymul) he) i

theorem isUnit_e_of_xi_ne (h : D.xi ≠ D'.xi)
    (hxmul : D.xi ≠ D'.xi → α D.origU * β D'.origU = 1) : IsUnit (α D.e) :=
  isUnit_of_dvd_unit (map_dvd α D.e_dvd_origU) (isUnit_of_mul_eq_one _ _ (hxmul h))

theorem isUnit_e_of_yi_ne (h : D.yi ≠ D'.yi)
    (hymul : D.yi ≠ D'.yi → α D.origV * β D'.origV = 1) : IsUnit (α D.e) :=
  isUnit_of_dvd_unit (map_dvd α D.e_dvd_origV) (isUnit_of_mul_eq_one _ _ (hymul h))

theorem isUnit_e_of_eq_one (h : D.e = 1) : IsUnit (α D.e) := by
  rw [h, map_one]
  exact isUnit_one

end Scale

end ChartTuple

/-! ## The five charts -/

/-- The selected Rees chart: coordinates `(u, w)`, `v = u w`, normaliser `x_0 y_0 T_1 = x_0 x_1 y_0²`. -/
def dataU : ChartTuple k where
  xi := 0
  yi := 0
  origU := uCoord
  origV := uCoord * vCoord
  ti := 1
  ni := 1
  e := uCoord
  tf := ![vCoord, 1, uCoord * vCoord]
  monoX_ni := rfl
  monoY_ni := rfl
  monoT_ni := rfl
  tf_ti := by simp
  tf_spec := by
    intro τ
    fin_cases τ <;> simp [tX, tY] <;> ring
  e_dvd_origU := dvd_refl _
  e_dvd_origV := dvd_mul_right _ _

/-- The second Rees chart in its polynomial model: coordinates `(v, w')`, `u = w' v`, normaliser
`x_0 y_0 T_0 = x_0² y_0 y_1`. -/
def dataV : ChartTuple k where
  xi := 0
  yi := 0
  origU := uCoord * vCoord
  origV := uCoord
  ti := 0
  ni := 0
  e := uCoord
  tf := ![1, vCoord, uCoord * vCoord]
  monoX_ni := rfl
  monoY_ni := rfl
  monoT_ni := rfl
  tf_ti := by simp
  tf_spec := by
    intro τ
    fin_cases τ
    · simp [tX, tY]
    · simp [tX, tY]
      ring
    · simp [tX, tY]
  e_dvd_origU := dvd_mul_right _ _
  e_dvd_origV := dvd_refl _

/-- The product chart `(1,0)`: coordinates `(u', v)`, normaliser `x_1 y_0 T_1 = x_1² y_0²`. -/
def data10 : ChartTuple k where
  xi := 1
  yi := 0
  origU := uCoord
  origV := vCoord
  ti := 1
  ni := 3
  e := 1
  tf := ![uCoord * vCoord, 1, vCoord]
  monoX_ni := rfl
  monoY_ni := rfl
  monoT_ni := rfl
  tf_ti := by simp
  tf_spec := by
    intro τ
    fin_cases τ <;> simp [tX, tY]
  e_dvd_origU := one_dvd _
  e_dvd_origV := one_dvd _

/-- The product chart `(0,1)`: coordinates `(u, v')`, normaliser `x_0 y_1 T_0 = x_0² y_1²`. -/
def data01 : ChartTuple k where
  xi := 0
  yi := 1
  origU := uCoord
  origV := vCoord
  ti := 0
  ni := 5
  e := 1
  tf := ![1, uCoord * vCoord, uCoord]
  monoX_ni := rfl
  monoY_ni := rfl
  monoT_ni := rfl
  tf_ti := by simp
  tf_spec := by
    intro τ
    fin_cases τ <;> simp [tX, tY]
  e_dvd_origU := one_dvd _
  e_dvd_origV := one_dvd _

/-- The product chart `(1,1)`: coordinates `(u', v')`, normaliser `x_1 y_1 T_2 = x_1² y_1²`. -/
def data11 : ChartTuple k where
  xi := 1
  yi := 1
  origU := uCoord
  origV := vCoord
  ti := 2
  ni := 7
  e := 1
  tf := ![uCoord, vCoord, 1]
  monoX_ni := rfl
  monoY_ni := rfl
  monoT_ni := rfl
  tf_ti := by simp
  tf_spec := by
    intro τ
    fin_cases τ <;> simp [tX, tY]
  e_dvd_origU := one_dvd _
  e_dvd_origV := one_dvd _

/-- The chart data of the five charts of stage `1`, in the order of `stageOneChart`. -/
def stageOneData : Fin 5 → ChartTuple k := ![dataU, dataV, data10, data01, data11]

theorem stageOneData_xi (c : Fin 5) : (stageOneData (k := k) c).xi = (chartIndex c).1 := by
  fin_cases c <;> rfl

theorem stageOneData_yi (c : Fin 5) : (stageOneData (k := k) c).yi = (chartIndex c).2 := by
  fin_cases c <;> rfl

theorem stageOneData_origU (c : Fin 5) :
    (stageOneData (k := k) c).origU = chartBlowdown c uCoord := by
  fin_cases c
  · exact chartSubstitution_u.symm
  · exact secondSubstitution_u.symm
  · rfl
  · rfl
  · rfl

theorem stageOneData_origV (c : Fin 5) :
    (stageOneData (k := k) c).origV = chartBlowdown c vCoord := by
  fin_cases c
  · exact chartSubstitution_v.symm
  · exact secondSubstitution_v.symm
  · rfl
  · rfl
  · rfl

/-- The tuple morphism of the `c`-th chart of stage `1`. -/
abbrev chartTupleMorphism (c : Fin 5) : plane k ⟶ projectiveSpace k 7 :=
  (stageOneData (k := k) c).morphism

end KltDP.Examples.FrobeniusStageOneTuples
