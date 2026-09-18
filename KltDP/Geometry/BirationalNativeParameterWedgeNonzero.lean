import KltDP.Geometry.BirationalStalkFunctionFieldTriangle
import KltDP.Geometry.StalkKaehlerGenericRank
import KltDP.Geometry.KaehlerLocalizedFrame
import KltDP.Geometry.KaehlerBasisAlgEquiv
import KltDP.LinearAlgebra.ExteriorPowerScalarMap

/-!
# Nonvanishing of the original pulled parameter wedge

Localize the given native target basis, transport it through the original
birational function-field algebra equivalence, and compare its vectors
using the actual stalk map. A zero original source-stalk wedge would map
to this basis wedge in the function field, contradicting determinant one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace nonZeroDivisors

universe u

namespace KltDP.Geometry.BirationalNativeParameterWedgeNonzero

open IntrinsicNodal

variable {k : Type u} [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (f : S ⟶ Spec (CommRingCat.of k)) (σ : X ⟶ Spec (CommRingCat.of k))
    (π : S ⟶ X) (hπ : π ≫ σ = f) (hbir : IsBirationalScheme π)

include hπ hbir in
/-- For the same parameters whose differentials are the given native target
basis, their literal images under the original stalk map have nonzero wedge. -/
theorem pulled_wedge_ne_zero (y : S)
    (v : Fin 2 → X.presheaf.stalk (π.base y))
    (b : letI := stalkAlgebra σ (π.base y)
      Basis (Fin 2) (X.presheaf.stalk (π.base y))
        (KaehlerDifferential k (X.presheaf.stalk (π.base y))))
    (hb : letI := stalkAlgebra σ (π.base y)
      ∀ i, b i = KaehlerDifferential.D k (X.presheaf.stalk (π.base y)) (v i)) :
    letI := stalkAlgebra f y
    exteriorPower.ιMulti (S.presheaf.stalk y) 2
      (fun i => KaehlerDifferential.D k (S.presheaf.stalk y) (π.stalkMap y (v i))) ≠ 0 := by
  letI := stalkAlgebra σ (π.base y)
  letI := stalkAlgebra f y
  letI := stalkAlgebra σ (genericPoint X)
  letI := stalkAlgebra f (genericPoint S)
  letI := StalkKaehlerGenericRank.stalk_functionField_scalarTower σ (π.base y)
  letI := StalkKaehlerGenericRank.stalk_functionField_scalarTower f y
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let bK := KaehlerLocalizedFrame.localizedFrame k (X.presheaf.stalk (π.base y))
    X.functionField (X.presheaf.stalk (π.base y))⁰ b
  have hbK (i : Fin 2) : bK i = KaehlerDifferential.D k X.functionField
      (algebraMap (X.presheaf.stalk (π.base y)) X.functionField (v i)) := by
    rw [KaehlerLocalizedFrame.localizedFrame_apply, hb i, KaehlerDifferential.map_D]
  let e := BirationalFunctionFieldStalkAlgebra.equiv f σ π hπ hbir
  let bL := KaehlerBasisAlgEquiv.basis e bK
  have hbL (i : Fin 2) : bL i = KaehlerDifferential.D k S.functionField
      (e (algebraMap (X.presheaf.stalk (π.base y)) X.functionField (v i))) :=
    KaehlerBasisAlgEquiv.basis_apply_of_eq_D e bK i _ (hbK i)
  have he (a : X.functionField) : e a = functionFieldMap π a := rfl
  intro hzero
  let T := KltDP.LinearAlgebra.ExteriorPowerScalarMap.map (S.presheaf.stalk y)
    S.functionField 2 (KaehlerDifferential.map k k (S.presheaf.stalk y) S.functionField)
  have hfield : exteriorPower.ιMulti S.functionField 2
      (fun i => KaehlerDifferential.D k S.functionField
        (algebraMap (S.presheaf.stalk y) S.functionField (π.stalkMap y (v i)))) = 0 := by
    calc
      _ = T (exteriorPower.ιMulti (S.presheaf.stalk y) 2
          (fun i => KaehlerDifferential.D k (S.presheaf.stalk y) (π.stalkMap y (v i)))) := by
        simpa only [KaehlerDifferential.map_D] using
          (KltDP.LinearAlgebra.ExteriorPowerScalarMap.map_ιMulti (S.presheaf.stalk y)
            S.functionField 2 (KaehlerDifferential.map k k (S.presheaf.stalk y) S.functionField)
            (fun i => KaehlerDifferential.D k (S.presheaf.stalk y) (π.stalkMap y (v i)))).symm
      _ = 0 := by rw [hzero, map_zero]
  have hvec : (fun i => KaehlerDifferential.D k S.functionField
      (algebraMap (S.presheaf.stalk y) S.functionField (π.stalkMap y (v i)))) = bL := by
    funext i
    rw [hbL i, he]
    exact congrArg (KaehlerDifferential.D k S.functionField)
      (BirationalStalkFunctionFieldTriangle.stalkMap_to_functionField π y (v i))
  rw [hvec] at hfield
  have hdet := congrArg (AffineTopDifferentialFrame.determinantEquiv bL) hfield
  have hone : (1 : S.functionField) = 0 := calc
    1 = AffineTopDifferentialFrame.determinantEquiv bL
        (exteriorPower.ιMulti S.functionField 2 bL) :=
      (AffineTopDifferentialFrame.determinantEquiv_basis_wedge bL).symm
    _ = AffineTopDifferentialFrame.determinantEquiv bL 0 := hdet
    _ = 0 := (AffineTopDifferentialFrame.determinantEquiv bL).map_zero
  exact one_ne_zero hone

end KltDP.Geometry.BirationalNativeParameterWedgeNonzero
