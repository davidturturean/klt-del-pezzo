import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors
import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.CartierSchemePullbackOpenImmersion

/-!
# The actual product swap exchanges the two ruling Cartier divisors

The original pullback symmetry exchanges the two projection morphisms.
Its actual section maps transport the original ruling coordinates, so
its Cartier pullback exchanges their local equations. Equality on the
original two-open ruling cover gives equality of the actual divisors;
the existing Cartier/Picard comparison then gives the Picard equality.
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassSwap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry ProjectiveLineComparison
open KltDP.Geometry.OpenImmersionRational
open KltDP.Examples.FrobeniusProjectivePoints
open KltDP.Examples.FrobeniusGraphPicardClassIntegral
open KltDP.Examples.FrobeniusGraphPicardClassRulingCoordinates
open KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors

variable {k : Type u} [Field k]

local instance : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def productSwapIso : projectiveProduct k ≅ projectiveProduct k :=
  pullbackSymmetry (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

theorem swap_inv_rulingProjection :
    (productSwapIso (k := k)).inv ≫ rulingProjection 1 = rulingProjection 0 := by
  simpa only [productSwapIso, rulingProjection, ↓reduceIte] using
    pullbackSymmetry_inv_comp_snd
      (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)

theorem swap_inv_rulingOpen (i : Fin 2) :
    (productSwapIso (k := k)).inv ⁻¹ᵁ rulingOpen 1 i = rulingOpen 0 i := by
  change (productSwapIso (k := k)).inv ⁻¹ᵁ
    (rulingProjection 1 ⁻¹ᵁ chartOpen k i) =
      rulingProjection 0 ⁻¹ᵁ chartOpen k i
  rw [← Scheme.preimage_comp, swap_inv_rulingProjection]

local instance swap_rulingOpen_nonempty (i : Fin 2) :
    Nonempty ((productSwapIso (k := k)).inv ⁻¹ᵁ rulingOpen 1 i) := by
  rw [swap_inv_rulingOpen]
  infer_instance

private theorem rulingLeft_eq_actual_germ (d : Fin 2) :
    rulingLeft (k := k) d =
      (projectiveProduct k).germToFunctionField (rulingOpen d 0)
        ((rulingProjection d).app (chartOpen k 0) leftCoordinateSection) := by
  exact Scheme.stalkMap_germ_apply (rulingProjection d) (chartOpen k 0)
    (genericPoint (projectiveProduct k)) (rulingGeneric_mem d 0)
    leftCoordinateSection

theorem swap_inv_rulingLeft :
    (functionFieldIso (productSwapIso (k := k)).inv).hom (rulingLeft 1) =
      rulingLeft 0 := by
  rw [rulingLeft_eq_actual_germ 1, functionFieldIso_germ]
  have transport (q : projectiveProduct k ⟶ projectiveSpace k 1)
      [Nonempty (q ⁻¹ᵁ chartOpen k 0)] (hq : q = rulingProjection 0) :
      (projectiveProduct k).germToFunctionField (q ⁻¹ᵁ chartOpen k 0)
        (q.app (chartOpen k 0) leftCoordinateSection) = rulingLeft 0 := by
    subst q
    exact (rulingLeft_eq_actual_germ 0).symm
  letI : Nonempty
      (((productSwapIso (k := k)).inv ≫ rulingProjection 1) ⁻¹ᵁ chartOpen k 0) := by
    rw [swap_inv_rulingProjection]
    exact rulingOpen_nonempty (k := k) 0 0
  change (projectiveProduct k).germToFunctionField
      (((productSwapIso (k := k)).inv ≫ rulingProjection 1) ⁻¹ᵁ chartOpen k 0)
      (((productSwapIso (k := k)).inv ≫ rulingProjection 1).app
        (chartOpen k 0) leftCoordinateSection) = rulingLeft 0
  exact transport _ swap_inv_rulingProjection

theorem swap_inv_rulingCoordinateUnit :
    Units.map (functionFieldIso (productSwapIso (k := k)).inv).hom.hom.toMonoidHom
      (rulingCoordinateUnit 1) = rulingCoordinateUnit 0 := by
  apply Units.ext
  change (functionFieldIso (productSwapIso (k := k)).inv).hom (rulingLeft 1) =
    rulingLeft 0
  exact swap_inv_rulingLeft

theorem swap_inv_rulingEquation (i : Fin 2) :
    Units.map (functionFieldIso (productSwapIso (k := k)).inv).hom.hom.toMonoidHom
      (rulingInfinityEquation 1 i) = rulingInfinityEquation 0 i := by
  by_cases hi : i = 0
  · simp only [rulingInfinityEquation, if_pos hi, map_one]
  · simp only [rulingInfinityEquation, if_neg hi, map_inv,
      swap_inv_rulingCoordinateUnit]

private theorem swap_inv_ruling_local (i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen 0 i ≤ ⊤ from le_top)).op
        (cartierRestrictionHom (productSwapIso (k := k)).inv
          (rulingInfinityDivisor 1)) =
      (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen 0 i ≤ ⊤ from le_top)).op
        (rulingInfinityDivisor 0) := by
  have hr := cartierRestriction_globalEquation_preimage
    (productSwapIso (k := k)).inv (rulingInfinityDivisor 1)
    (rulingOpen 1 i) (rulingInfinityEquation 1 i)
    (rulingInfinityDivisor_restrict 1 i).symm
  have hV := congrArg
    ((cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (swap_inv_rulingOpen (k := k) i).ge).op) hr
  rw [cartierEquationClassHom_restrict,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hV
  change cartierEquationClassHom (projectiveProduct k) (rulingOpen 0 i)
      (Additive.ofMul
        (Units.map (functionFieldIso (productSwapIso (k := k)).inv).hom.hom.toMonoidHom
          (rulingInfinityEquation 1 i))) =
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen 0 i ≤ ⊤ from le_top)).op
      (cartierRestrictionHom (productSwapIso (k := k)).inv
        (rulingInfinityDivisor 1)) at hV
  rw [swap_inv_rulingEquation] at hV
  exact hV.symm.trans (rulingInfinityDivisor_restrict 0 i).symm

theorem swap_inv_rulingInfinityDivisor :
    cartierRestrictionHom (productSwapIso (k := k)).inv (rulingInfinityDivisor 1) =
      rulingInfinityDivisor 0 := by
  apply (cartierDivisorSheaf (projectiveProduct k)).eq_of_locally_eq'
    (rulingOpen 0) ⊤
    (fun i => homOfLE (show rulingOpen 0 i ≤ ⊤ from le_top))
    (rulingOpen_cover (k := k) 0).ge
  exact swap_inv_ruling_local

theorem swap_inv_rulingPicard :
    schemePicardPullbackHom (productSwapIso (k := k)).inv
        (cartierPicardClass (projectiveProduct k) (rulingInfinityDivisor 1)) =
      cartierPicardClass (projectiveProduct k) (rulingInfinityDivisor 0) := by
  rw [schemePicardPullbackHom_cartierPicardClass, swap_inv_rulingInfinityDivisor]

end KltDP.Examples.FrobeniusGraphPicardClassSwap
