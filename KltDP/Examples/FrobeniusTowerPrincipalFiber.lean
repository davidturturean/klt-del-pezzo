import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Geometry.CartierOpenRestriction

/-!
# The pulled-back fibre as a principal Cartier divisor on the whole tower

On an integral charted plane `A`, the polynomials of the selected chart of stage `n` give rational
functions on the whole tower (`chartCoordinate`), nonzero for nonzero polynomials, hence principal
Cartier divisors `chartPrincipal A n a ha` on `(A.stage n).carrier`. The pulled-back fibre equation
`pulledBack A n v` gives the principal divisor `pulledFiberDivisor A n = π^*(v = 0)` on the tower and,
from `pulledBack_vCoord`, the identity of Cartier divisors on the whole tower

`pulledFiberDivisor A n = n • lastCoordinateDivisor A n + strictFiberTowerDivisor A n`

(`pulledFiberDivisor_eq`), where the two terms are the principal divisors of the last chart
coordinates `u`, `v`. Restricted to the selected chart along the accepted `cartierRestrictionHom`
these are the chart divisors of BRIEF8 (`restrict_pulledFiberDivisor : … = stageFiberDivisor n`,
`restrict_lastCoordinateDivisor : … = exceptionalDivisor`, `restrict_strictFiberTowerDivisor : … =
strictFiberDivisor`); restricted to the puncture, the pulled-back fibre divisor is the restriction of
the original fibre divisor `initialFiberDivisor A` of `v = 0` on `A.carrier`, transported along the
accepted complement isomorphism (`restrict_pulledFiberDivisor_puncture`).

This is not yet the decomposition `F̃ + Σ j•C_j + p•P` of BRIEF8 step 2 on the tower: the divisor of the
last coordinate `u` on the whole tower contains, besides the last exceptional curve, the earlier
exceptional curves with their multiplicities; separating them requires the atlas of all Rees charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerPrincipalFiber

open KltDP.Geometry KltDP.Geometry.OpenImmersionRational FrobeniusBlowupContact
  FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageComplement
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusFiberCartierCharts
  FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

theorem planeGerm_injective : Function.Injective (planeGerm (k := k)) := fun _ _ hab =>
  planeSectionHom_injective ((plane k).germToFunctionField_injective ⊤ hab)

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k) [IsIntegral A.carrier] (n : ℕ)

theorem chartCoordinate_injective : Function.Injective (chartCoordinate A n) := fun _ _ hab =>
  planeGerm_injective ((chartFunctionFieldIso A n).symm.commRingCatIsoToRingEquiv.injective hab)

theorem chartCoordinate_ne_zero {a : planeRing k} (ha : a ≠ 0) : chartCoordinate A n a ≠ 0 :=
  fun h => ha (chartCoordinate_injective A n (h.trans (map_zero _).symm))

/-- A nonzero polynomial of the selected chart as a unit of the tower's function field. -/
def chartUnit (a : planeRing k) (ha : a ≠ 0) : (A.stage n).carrier.functionFieldˣ :=
  Units.mk0 _ (chartCoordinate_ne_zero A n ha)

theorem chartUnit_val (a : planeRing k) (ha : a ≠ 0) :
    (chartUnit A n a ha : (A.stage n).carrier.functionField) = chartCoordinate A n a := rfl

theorem chartUnit_mul (a b : planeRing k) (ha : a ≠ 0) (hb : b ≠ 0) :
    chartUnit A n (a * b) (mul_ne_zero ha hb) = chartUnit A n a ha * chartUnit A n b hb := by
  apply Units.ext
  rw [Units.val_mul, chartUnit_val, chartUnit_val, chartUnit_val, map_mul]

theorem chartUnit_pow (a : planeRing k) (ha : a ≠ 0) (m : ℕ) :
    chartUnit A n (a ^ m) (pow_ne_zero m ha) = chartUnit A n a ha ^ m := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, chartUnit_val, chartUnit_val, map_pow]

/-- The principal Cartier divisor on the whole tower of a nonzero polynomial of the selected chart. -/
def chartPrincipal (a : planeRing k) (ha : a ≠ 0) : CartierDivisor (A.stage n).carrier :=
  principalCartierDivisorHom (A.stage n).carrier (Additive.ofMul (chartUnit A n a ha))

theorem chartPrincipal_congr {a b : planeRing k} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a = b) :
    chartPrincipal A n a ha = chartPrincipal A n b hb := by
  subst hab
  rfl

theorem chartPrincipal_mul (a b : planeRing k) (ha : a ≠ 0) (hb : b ≠ 0) :
    chartPrincipal A n (a * b) (mul_ne_zero ha hb) =
      chartPrincipal A n a ha + chartPrincipal A n b hb := by
  rw [chartPrincipal, chartPrincipal, chartPrincipal, chartUnit_mul A n a b ha hb, ← map_add]
  rfl

theorem chartPrincipal_pow (a : planeRing k) (ha : a ≠ 0) (m : ℕ) :
    chartPrincipal A n (a ^ m) (pow_ne_zero m ha) = m • chartPrincipal A n a ha := by
  rw [chartPrincipal, chartPrincipal, chartUnit_pow A n a ha m, ← map_nsmul]
  rfl

/-- The divisor of the last exceptional coordinate `u` on the whole tower. -/
def lastCoordinateDivisor : CartierDivisor (A.stage n).carrier :=
  chartPrincipal A n uCoord FrobeniusFiberCartierCharts.uCoord_ne_zero

/-- The divisor of the last chart coordinate `v` (the strict fibre on the chart) on the whole tower. -/
def strictFiberTowerDivisor : CartierDivisor (A.stage n).carrier :=
  chartPrincipal A n vCoord FrobeniusFiberCartierCharts.vCoord_ne_zero

theorem pulledBack_vCoord_ne_zero : pulledBack A n vCoord ≠ 0 := by
  rw [pulledBack_eq]
  exact chartCoordinate_ne_zero A n (stageFiber_ne_zero n)

/-- The pulled-back total fibre `π^*(v = 0)` as a principal Cartier divisor on the whole tower. -/
def pulledFiberDivisor : CartierDivisor (A.stage n).carrier :=
  principalCartierDivisorHom (A.stage n).carrier
    (Additive.ofMul (Units.mk0 _ (pulledBack_vCoord_ne_zero A n)))

theorem pulledFiberDivisor_eq_chartPrincipal :
    pulledFiberDivisor A n = chartPrincipal A n (stageSubstitution n vCoord) (stageFiber_ne_zero n) := by
  have hu : Units.mk0 _ (pulledBack_vCoord_ne_zero A n) =
      chartUnit A n (stageSubstitution n vCoord) (stageFiber_ne_zero n) :=
    Units.ext (pulledBack_eq A n vCoord)
  rw [pulledFiberDivisor, chartPrincipal, hu]

/-- Step 2 at the level of principal divisors on the whole tower: the pulled-back fibre is `n` times
the divisor of the last coordinate `u` plus the divisor of `v`. -/
theorem pulledFiberDivisor_eq :
    pulledFiberDivisor A n = n • lastCoordinateDivisor A n + strictFiberTowerDivisor A n := by
  rw [pulledFiberDivisor_eq_chartPrincipal, chartPrincipal_congr A n (stageFiber_ne_zero n)
    (mul_ne_zero (pow_ne_zero n FrobeniusFiberCartierCharts.uCoord_ne_zero)
      FrobeniusFiberCartierCharts.vCoord_ne_zero) (stageSubstitution_v n),
    chartPrincipal_mul, chartPrincipal_pow]
  rfl

/-! ## Restriction to the selected chart -/

theorem restrict_chartPrincipal (a : planeRing k) (ha : a ≠ 0) :
    cartierRestrictionHom (A.stage n).chart (chartPrincipal A n a ha) = chartDivisor a ha := by
  rw [chartPrincipal, cartierRestrictionHom_principal, chartDivisor]
  congr 2
  apply Units.ext
  rw [Units.coe_map]
  exact Iso.inv_hom_id_apply (chartFunctionFieldIso A n) (planeGerm a)

theorem restrict_pulledFiberDivisor :
    cartierRestrictionHom (A.stage n).chart (pulledFiberDivisor A n) = stageFiberDivisor n := by
  rw [pulledFiberDivisor_eq_chartPrincipal, restrict_chartPrincipal]
  rfl

theorem restrict_lastCoordinateDivisor :
    cartierRestrictionHom (A.stage n).chart (lastCoordinateDivisor A n) = exceptionalDivisor :=
  restrict_chartPrincipal A n _ _

theorem restrict_strictFiberTowerDivisor :
    cartierRestrictionHom (A.stage n).chart (strictFiberTowerDivisor A n) = strictFiberDivisor :=
  restrict_chartPrincipal A n _ _

/-! ## Restriction to the puncture -/

theorem initialFiber_ne_zero :
    (functionFieldIso A.chart).inv (planeGerm (vCoord (k := k))) ≠ 0 := by
  intro h
  apply FrobeniusFiberCartierCharts.vCoord_ne_zero (k := k)
  apply planeGerm_injective (k := k)
  rw [map_zero]
  apply (functionFieldIso A.chart).symm.commRingCatIsoToRingEquiv.injective
  rw [map_zero]
  exact h

/-- The fibre `v = 0` of the initial chart as a principal Cartier divisor on the initial scheme. -/
def initialFiberDivisor : CartierDivisor A.carrier :=
  principalCartierDivisorHom A.carrier (Additive.ofMul (Units.mk0 _ (initialFiber_ne_zero A)))

theorem towerFunctionFieldIso_inv_comp :
    (towerFunctionFieldIso A n).inv ≫ (functionFieldIso (stagePuncture A n).ι).hom =
      (functionFieldIso (initialPuncture A).ι).hom ≫
        (functionFieldIso (stageComplementIso A n).hom).hom := by
  simp only [towerFunctionFieldIso, Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Over the puncture, the pulled-back fibre divisor is the original fibre divisor, transported along
the accepted complement isomorphism. -/
theorem restrict_pulledFiberDivisor_puncture :
    cartierRestrictionHom (stagePuncture A n).ι (pulledFiberDivisor A n) =
      cartierRestrictionHom (stageComplementIso A n).hom
        (cartierRestrictionHom (initialPuncture A).ι (initialFiberDivisor A)) := by
  rw [pulledFiberDivisor, initialFiberDivisor, cartierRestrictionHom_principal,
    cartierRestrictionHom_principal, cartierRestrictionHom_principal]
  congr 2
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, Units.coe_map]
  exact congrArg (fun φ : A.carrier.functionField ⟶ (stagePuncture A n).toScheme.functionField =>
    φ ((functionFieldIso A.chart).inv (planeGerm vCoord))) (towerFunctionFieldIso_inv_comp A n)

/-- The Picard relation of the principal-divisor identity (formal). -/
theorem pulledFiberDivisor_picard :
    cartierPicardHom (A.stage n).carrier (pulledFiberDivisor A n) =
      n • cartierPicardHom (A.stage n).carrier (lastCoordinateDivisor A n) +
        cartierPicardHom (A.stage n).carrier (strictFiberTowerDivisor A n) := by
  rw [pulledFiberDivisor_eq, map_add, map_nsmul]

end PlaneChartedScheme

end KltDP.Examples.FrobeniusTowerPrincipalFiber

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.OpenImmersionRational FrobeniusGlobalBlowupStages
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusFiberCartierCharts
  FrobeniusTowerFunctionField.PlaneChartedScheme FrobeniusTowerPrincipalFiber.PlaneChartedScheme

/-- Bundle: the pulled-back fibre on the whole tower as a principal Cartier divisor, its identity
`n • div(u) + div(v)`, and its restrictions to the selected chart and to the puncture. -/
theorem f29_tower_principal_fiber {k : Type u} [Field k] (A : PlaneChartedScheme k)
    [IsIntegral A.carrier] (n : ℕ) :
    pulledFiberDivisor A n = n • lastCoordinateDivisor A n + strictFiberTowerDivisor A n ∧
    cartierRestrictionHom (A.stage n).chart (pulledFiberDivisor A n) = stageFiberDivisor n ∧
    cartierRestrictionHom (A.stage n).chart (lastCoordinateDivisor A n) = exceptionalDivisor ∧
    cartierRestrictionHom (A.stage n).chart (strictFiberTowerDivisor A n) = strictFiberDivisor ∧
    cartierRestrictionHom (stagePuncture A n).ι (pulledFiberDivisor A n) =
      cartierRestrictionHom (stageComplementIso A n).hom
        (cartierRestrictionHom (initialPuncture A).ι (initialFiberDivisor A)) :=
  ⟨pulledFiberDivisor_eq A n, restrict_pulledFiberDivisor A n, restrict_lastCoordinateDivisor A n,
    restrict_strictFiberTowerDivisor A n, restrict_pulledFiberDivisor_puncture A n⟩

/-- The translated initial charted plane is integral: its carrier is the projective product. -/
instance translatedInitial_isIntegral {k : Type u} [Field k] (p : ℕ) (a : k) :
    IsIntegral (FrobeniusTranslatedCharts.translatedInitial p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

open FrobeniusTranslatedCharts in
/-- The Frobenius fibre: on the translated initial charted plane `translatedInitial p a` the horizontal
fibre `y = a^p` is `v = 0` of the distinguished chart (BRIEF7, `fiberAdaptedTranslated`), so
`pulledFiberDivisor (translatedInitial p a) n` is `π^*(y = a^p)` on the stage-`n` tower over `(a, a^p)`:
it is `n • div(u) + div(v)` on the whole tower, and over the puncture it is the fibre divisor itself. -/
theorem f29_tower_frobenius_fiber {k : Type u} [Field k] (p : ℕ) (a : k) (n : ℕ) :
    pulledFiberDivisor (translatedInitial p a) n =
      n • lastCoordinateDivisor (translatedInitial p a) n +
        strictFiberTowerDivisor (translatedInitial p a) n ∧
    cartierRestrictionHom (stagePuncture (translatedInitial p a) n).ι
        (pulledFiberDivisor (translatedInitial p a) n) =
      cartierRestrictionHom (stageComplementIso (translatedInitial p a) n).hom
        (cartierRestrictionHom (initialPuncture (translatedInitial p a)).ι
          (initialFiberDivisor (translatedInitial p a))) :=
  ⟨pulledFiberDivisor_eq _ n, restrict_pulledFiberDivisor_puncture _ n⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_tower_principal_fiber_universe_check {k : Type u} [Field k] (A : PlaneChartedScheme k)
    [IsIntegral A.carrier] : True := by
  have _ := f29_tower_principal_fiber.{u} A 0
  trivial

end KltDP.Examples
