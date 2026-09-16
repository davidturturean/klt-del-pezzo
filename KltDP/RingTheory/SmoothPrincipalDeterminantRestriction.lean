import KltDP.RingTheory.SmoothPrincipalConormalDeterminant
import KltDP.LinearAlgebra.ExteriorPowerSemilinearMap

/-!
# The actual determinant adjunction map respects the original ring restriction

For the original algebra map carrying J into J', use its original quotient
map and the pinned maps of Kähler differentials. The original tensor map
commutes with quotient differentials. The equation-normalized determinant
maps therefore commute with this restriction, by their proved wedge formula
and surjectivity of the original quotient differential map.

No determinant or conormal compatibility is assumed. The final result
retains generation, regularity, and smoothness of the two actual charts;
localization can supply the smaller chart's equation conditions separately.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.SmoothPrincipalDeterminantRestriction

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))

/-- The original quotient map induced by the original ambient algebra map. -/
def quotientMap : A ⧸ J →+* A' ⧸ J' :=
  Ideal.quotientMap J' (algebraMap A A') hφ

/-- The explicit quotient map retains the original ambient scalar tower. -/
theorem quotientMapTowerA :
    letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
    IsScalarTower A (A ⧸ J) (A' ⧸ J') := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change Ideal.Quotient.mk J' (algebraMap A A' a) =
    quotientMap A A' J J' hφ (Ideal.Quotient.mk J a)
  exact (Ideal.quotientMap_mk (J := J) (I := J')
    (f := algebraMap A A') (H := hφ) (x := a)).symm

/-- The same original quotient map retains the original base-ring scalar action. -/
theorem quotientMapTowerR :
    letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
    IsScalarTower R (A ⧸ J) (A' ⧸ J') := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change Ideal.Quotient.mk J' (algebraMap R A' r) =
    quotientMap A A' J J' hφ (Ideal.Quotient.mk J (algebraMap R A r))
  rw [quotientMap, Ideal.quotientMap_mk, ← IsScalarTower.algebraMap_apply R A A']

/-- The actual image equation in the original target ideal. -/
def mappedEquation (d : J) : J' :=
  ⟨algebraMap A A' (d : A), hφ d.property⟩

/-- The original map on quotient Kähler modules is semilinear over the original quotient map. -/
def quotientDifferentialMap :
    KaehlerDifferential R (A ⧸ J) →ₛₗ[quotientMap A A' J J' hφ]
      KaehlerDifferential R (A' ⧸ J') := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  let g := KaehlerDifferential.map R R (A ⧸ J) (A' ⧸ J')
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun s m => (g.map_smul s m).trans (algebraMap_smul (A' ⧸ J') s _).symm }

/-- The actual ambient differential map retains the original quotient semilinearity. -/
def ambientTensorMap :
    (A ⧸ J) ⊗[A] KaehlerDifferential R A →ₛₗ[quotientMap A A' J J' hφ]
      (A' ⧸ J') ⊗[A'] KaehlerDifferential R A' := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : Module (A ⧸ J) ((A' ⧸ J') ⊗[A'] KaehlerDifferential R A') :=
    Module.compHom _ (quotientMap A A' J J' hφ)
  letI : IsScalarTower A (A ⧸ J) ((A' ⧸ J') ⊗[A'] KaehlerDifferential R A') := by
    apply IsScalarTower.of_algebraMap_smul
    intro a m
    change quotientMap A A' J J' hφ (Ideal.Quotient.mk J a) • m = a • m
    rw [quotientMap, Ideal.quotientMap_mk]
    exact algebraMap_smul (A' ⧸ J') a m
  let g := (((TensorProduct.mk A' (A' ⧸ J') (KaehlerDifferential R A') 1).restrictScalars A).comp
    (KaehlerDifferential.map R R A A')).liftBaseChange (A ⧸ J)
  exact { toFun := g, map_add' := g.map_add, map_smul' := g.map_smul }

/-- The tensor comparison uses exactly the original quotient map on each coefficient. -/
theorem ambientTensorMap_tmul (s : A ⧸ J) (m : KaehlerDifferential R A) :
    ambientTensorMap R A A' J J' hφ (s ⊗ₜ[A] m) =
      quotientMap A A' J J' hφ s ⊗ₜ[A'] KaehlerDifferential.map R R A A' m := by
  change quotientMap A A' J J' hφ s •
    ((1 : A' ⧸ J') ⊗ₜ[A'] KaehlerDifferential.map R R A A' m) = _
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The original equation differential maps to the differential of the original image equation. -/
theorem ambientTensorMap_equation (d : J) :
    ambientTensorMap R A A' J J' hφ ((1 : A ⧸ J) ⊗ₜ[A] KaehlerDifferential.D R A (d : A)) =
      (1 : A' ⧸ J') ⊗ₜ[A'] KaehlerDifferential.D R A' (mappedEquation A A' J J' hφ d : A') := by
  rw [ambientTensorMap_tmul, map_one, KaehlerDifferential.map_D]
  rfl

private theorem differential_square (m : KaehlerDifferential R A) :
    KaehlerDifferential.map R R A' (A' ⧸ J') (KaehlerDifferential.map R R A A' m) =
      quotientDifferentialMap R A A' J J' hφ
        (KaehlerDifferential.map R R A (A ⧸ J) m) := by
  letI : Algebra (A ⧸ J) (A' ⧸ J') := (quotientMap A A' J J' hφ).toAlgebra
  letI : IsScalarTower A (A ⧸ J) (A' ⧸ J') := quotientMapTowerA A A' J J' hφ
  letI : IsScalarTower R (A ⧸ J) (A' ⧸ J') := quotientMapTowerR R A A' J J' hφ
  change KaehlerDifferential.map R R A' (A' ⧸ J') (KaehlerDifferential.map R R A A' m) =
    KaehlerDifferential.map R R (A ⧸ J) (A' ⧸ J')
      (KaehlerDifferential.map R R A (A ⧸ J) m)
  have hs : ((KaehlerDifferential.map R R A' (A' ⧸ J')).restrictScalars A).comp
        (KaehlerDifferential.map R R A A') =
      ((KaehlerDifferential.map R R (A ⧸ J) (A' ⧸ J')).restrictScalars A).comp
        (KaehlerDifferential.map R R A (A ⧸ J)) := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      quotientDifferentialMap, KaehlerDifferential.map_D]
    change KaehlerDifferential.D R (A' ⧸ J')
        (Ideal.Quotient.mk J' (algebraMap A A' a)) =
      KaehlerDifferential.D R (A' ⧸ J')
        (quotientMap A A' J J' hφ (Ideal.Quotient.mk J a))
    rw [quotientMap, Ideal.quotientMap_mk]
  exact LinearMap.congr_fun hs m

/-- The two original quotient differential routes commute on every ambient tensor. -/
theorem ambientTensorMap_mapBaseChange (m : (A ⧸ J) ⊗[A] KaehlerDifferential R A) :
    KaehlerDifferential.mapBaseChange R A' (A' ⧸ J')
        (ambientTensorMap R A A' J J' hφ m) =
      quotientDifferentialMap R A A' J J' hφ
        (KaehlerDifferential.mapBaseChange R A (A ⧸ J) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s m =>
      rw [ambientTensorMap_tmul, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.mapBaseChange_tmul,
        (quotientDifferentialMap R A A' J J' hφ).map_smulₛₗ,
        differential_square R A A' J J' hφ]
  | add m n hm hn => simp only [map_add, hm, hn]

section Smooth

variable [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')

/-- The produced determinant maps commute with the original ring restriction.
The equality follows from their actual wedge formulas, not a compatibility premise. -/
theorem determinantEquiv_restriction (n : KaehlerDifferential R (A ⧸ J)) :
    KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map (quotientMap A A' J J' hφ) 2
        (ambientTensorMap R A A' J J' hφ)
        (SmoothPrincipalConormalDeterminant.determinantEquiv R A J d hJ hd n) =
      SmoothPrincipalConormalDeterminant.determinantEquiv R A' J'
        (mappedEquation A A' J J' hφ d) hJ' hd'
        (quotientDifferentialMap R A A' J J' hφ n) := by
  obtain ⟨m, rfl⟩ := KaehlerDifferential.mapBaseChange_surjective R A (A ⧸ J)
    (show Function.Surjective (algebraMap A (A ⧸ J)) from Ideal.Quotient.mk_surjective) n
  rw [SmoothPrincipalConormalDeterminant.determinantEquiv_mapBaseChange,
    KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map_ιMulti,
    ← ambientTensorMap_mapBaseChange R A A' J J' hφ,
    SmoothPrincipalConormalDeterminant.determinantEquiv_mapBaseChange]
  congr 1
  funext i
  fin_cases i
  · exact ambientTensorMap_equation R A A' J J' hφ d
  · rfl

end Smooth

end KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
