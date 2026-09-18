import KltDP.Manuscript.S10.CharacteristicTwo
import KltDP.Examples.FrobeniusSquareChartDifferential
import KltDP.Examples.FrobeniusSquareRationalDegree

/-!
# Corollary 10.3 (`cor:inseparable-covers`, manuscript lines 3086–3132):
# failure of the separability arguments in characteristic two

On the characteristic-two surfaces `S_{2,n}` of Theorem 10.2:

* **First failure (the bisection).** The ruling of class `b` restricted to the strict graph `B`
  is, through the union's isomorphism `B ≅ P¹`, the coordinate square map
  `projectivePowerMorphism 2` (`y ↦ y²`); its function-field extension has degree two and is
  purely inseparable, and the square substitution has identically zero differential on both
  coordinate charts (`bisection_inseparable`). So there are no separable ramification points.
* **Second failure (the even set).** For distinct `i ≠ j` the even set `F_i + U_i + F_j + U_j`
  is linearly equivalent to `2(b - P_i - P_j)` in `Pic(S)` (`evenSet_pair`), and the degree-two
  algebra obtained by adjoining a square root `w² = y` of the ruling coordinate (the union's
  `CoverAlgebra RatFunc.X = k(y)[w]/(w² - y)`) is a purely inseparable field extension of
  degree two of `k(y)` (`squareRoot_purelyInseparable`), the manuscript's function-field
  description `z² = y² + y`, `w = z + y`, `w² = y`.

The restriction of the square-root algebra to a disjoint original rational tree (the
"nonreduced double tree") is not in the union and is not formalized here.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Examples KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreProjectiveSevenConfiguration
open KltDP.Examples.FrobeniusMultiCentreGraphFiber
open KltDP.Examples.FrobeniusMultiCentreGraphProjectiveLine
open KltDP.Examples.FrobeniusProjectiveMorphism
open KltDP.Examples.FrobeniusGlobalGraphCompatibility
open KltDP.Examples.FrobeniusActualStrictGraphInseparable
open KltDP.Examples.FrobeniusActualParametrizedGraphInseparable
open KltDP.Examples.FrobeniusSquareRationalMap

universe u

namespace KltDP.Manuscript.S10

section CharacteristicTwo

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwoIC : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

local instance projectiveLineIntegralIC : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- **Corollary 10.3, first failure.** The bisection `B → P¹` (the ruling of class `b` restricted
to the strict graph) is the square map `y ↦ y²` under `B ≅ P¹`; it has function-field degree two,
is purely inseparable, and the square substitution has zero differential (and zero derivative) on
the coordinate charts: there are no separable ramification points. -/
theorem bisection_inseparable :
    (primeCurve n a ha (.inl ()) : Set (surface n a ha).toScheme) =
      Set.range (graphStrictι 2 n a).base ∧
    strictGraphRuling n a =
      (globalGraphIsoProjectiveLine 2 n a).hom ≫ projectivePowerMorphism 2 ∧
    (letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
     letI : Module (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      Algebra.toModule
     Module.finrank (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField = 2) ∧
    (letI : Algebra (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField :=
      (functionFieldMap (strictGraphRuling n a)).hom.toAlgebra
     IsPurelyInseparable (projectiveSpace k 1).functionField (graphStrict 2 n a).functionField) ∧
    (∀ f : Polynomial k,
      KaehlerDifferential.D k (Polynomial k) (polynomialPowerHom 2 f) = 0) ∧
    (∀ f : Polynomial k, Polynomial.derivative (polynomialPowerHom 2 f) = 0) :=
  ⟨rfl,
    (strictGraphRuling_eq_parametrized n a).trans (by rw [parametrizedRuling_eq_square]),
    strictGraphRuling_finrank n a,
    strictGraphRuling_isPurelyInseparable n a,
    fun f => FrobeniusSquareChartDifferential.differential_polynomialPowerHom_two f,
    fun f => FrobeniusSquareChartDifferential.derivative_polynomialPowerHom_two f⟩

/-- **Corollary 10.3, the explicit even set.** For `i ≠ j`,
`F_i + U_i + F_j + U_j ∼ 2 (b - P_i - P_j)` in `Pic(S_{2,n})`. -/
theorem evenSet_pair (i j : Fin n) (hij : i ≠ j) :
    (2 : ℤ) • (multiSecondFiberClass 2 n a -
        exceptionalClass 2 n a i (1 : Fin 2) - exceptionalClass 2 n a j (1 : Fin 2)) =
      cartierPicardHom (surface n a ha).toScheme
        (primeDivisor n a ha (.inr (.inl i)) + primeDivisor n a ha (.inr (.inr i)) +
          primeDivisor n a ha (.inr (.inl j)) + primeDivisor n a ha (.inr (.inr j))) := by
  have h := code_half_class n a ha {i, j} (by rw [Finset.card_pair hij]; exact even_two)
  simp only [Finset.card_pair hij, Finset.sum_pair hij, Nat.reduceDiv, Nat.cast_one,
    one_smul] at h
  simp only [map_add] at h ⊢
  rw [sub_sub, h]
  abel

end CharacteristicTwo

/-! ### The square-root algebra of the ruling coordinate is purely inseparable -/

section SquareRoot

variable (k : Type u) [Field k] [CharP k 2]

/-- **Corollary 10.3, second failure (function-field form).** Adjoining a square root of the
ruling coordinate `y` to `k(y)` — the union's quadratic cover algebra
`CoverAlgebra RatFunc.X = k(y)[w]/(w² - y)`, identified with `k(y)` acting through the square
substitution `squareHom : y ↦ y²` — gives a field extension of degree two which is purely
inseparable; every square lies in the image of the substitution. This is the manuscript's
`z² = y² + y`, `w = z + y`, `w² = y`. -/
theorem squareRoot_purelyInseparable :
    (letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
     letI : Module (RatFunc k) (RatFunc k) := Algebra.toModule
     Module.finrank (RatFunc k) (RatFunc k) = 2) ∧
    (letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
     IsPurelyInseparable (RatFunc k) (RatFunc k)) ∧
    (∀ z : RatFunc k, ∃ a : RatFunc k, squareHom k a = z ^ 2) :=
  ⟨squareHom_finrank k, squareHom_isPurelyInseparable k, squareHom_square_mem_range k⟩

omit [CharP k 2] in
/-- The quadratic cover algebra `k(y)[w]/(w² - y)` is isomorphic, as an algebra over `k(y)`
acting by the square substitution, to `k(y)` itself (the union's `quadraticEquiv`). -/
theorem squareRoot_coverAlgebra_equiv :
    letI : Algebra (RatFunc k) (KltDP.Geometry.QuadraticCover.CoverAlgebra (RatFunc.X : RatFunc k)) :=
      inferInstance
    letI : Algebra (RatFunc k) (RatFunc k) := (squareHom k).toRingHom.toAlgebra
    Nonempty (KltDP.Geometry.QuadraticCover.CoverAlgebra (RatFunc.X : RatFunc k) ≃ₐ[RatFunc k]
      RatFunc k) :=
  ⟨quadraticEquiv k⟩

end SquareRoot

end KltDP.Manuscript.S10

#print axioms KltDP.Manuscript.S10.bisection_inseparable
#print axioms KltDP.Manuscript.S10.evenSet_pair
#print axioms KltDP.Manuscript.S10.squareRoot_purelyInseparable
#print axioms KltDP.Manuscript.S10.squareRoot_coverAlgebra_equiv
