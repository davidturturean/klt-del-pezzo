import KltDP.Geometry.AffineNativeTopDifferentialMap
import KltDP.Examples.FrobeniusBlowupDifferential
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The whole original native map in actual coordinate frames

The original source frame extends along the supplied algebra homomorphism.
For an actual equation `φ a * t = φ b`, the original differential sends the
source coordinate wedge to `φ a` times the target coordinate wedge. Actual
source and target differential bases then determine the entire original map.
No differential or canonical formula is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open KltDP.Examples.FrobeniusBlowupDifferential

universe u

variable (k : Type u) [CommRing k]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable (φ : A →ₐ[k] B) {n : ℕ}

/-- Extend the actual source determinant frame on the literal scalar-extension module. -/
def extendedFrame (β : Basis (Fin n) A (KaehlerDifferential k A)) :
    (ModuleCat.extendScalars φ.toRingHom).obj
        ((differentialModule k A).exteriorPower n) ≃ₗ[B] B := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  exact (LinearEquiv.baseChange A B (⋀[A]^n (KaehlerDifferential k A)) A
    (determinantEquiv β)).trans (TensorProduct.AlgebraTensorModule.rid A B B)

/-- The original scalar-extended basis wedge has frame coordinate one. -/
theorem extendedFrame_wedge (β : Basis (Fin n) A (KaehlerDifferential k A)) :
    extendedFrame k φ β
      ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A n β) = 1 := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  change algebraMap A B (determinantEquiv β (exteriorPower.ιMulti A n β)) * 1 = 1
  rw [determinantEquiv_basis_wedge, map_one, mul_one]

/-- Every element of the original extended module is a multiple of that wedge. -/
theorem extendedFrame_expansion (β : Basis (Fin n) A (KaehlerDifferential k A))
    (ω : (ModuleCat.extendScalars φ.toRingHom).obj
      ((differentialModule k A).exteriorPower n)) :
    extendedFrame k φ β ω •
      ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A n β) = ω := by
  apply (extendedFrame k φ β).injective
  rw [LinearEquiv.map_smul, extendedFrame_wedge, smul_eq_mul, mul_one]

/-- The original product equation gives the actual exceptional wedge factor. -/
theorem map_one_tmul_wedge_of_relation (a b : A) (t : B) (h : φ a * t = φ b) :
    map k φ 2 ((1 : B) ⊗ₜ[A,φ.toRingHom]
      exteriorPower.ιMulti A 2 ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b]) =
    φ a • exteriorPower.ιMulti B 2
      ![KaehlerDifferential.D k B (φ a), KaehlerDifferential.D k B t] := by
  have hw := map_one_tmul_D k φ 2 ![a, b]
  have hs : (fun i : Fin 2 => KaehlerDifferential.D k A (![a, b] i)) =
      ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b] := by
    funext i
    fin_cases i <;> rfl
  have ht : (fun i : Fin 2 => KaehlerDifferential.D k B (φ (![a, b] i))) =
      ![KaehlerDifferential.D k B (φ a), KaehlerDifferential.D k B (φ b)] := by
    funext i
    fin_cases i <;> rfl
  rw [hs, ht] at hw
  refine hw.trans ?_
  rw [← h]
  exact wedgeTwo_derivation_mul (KaehlerDifferential.D k B) (φ a) t

variable (β : Basis (Fin 2) A (KaehlerDifferential k A))
variable (γ : Basis (Fin 2) B (KaehlerDifferential k B))
variable (a b : A) (t : B)
variable (hβ0 : β 0 = KaehlerDifferential.D k A a)
variable (hβ1 : β 1 = KaehlerDifferential.D k A b)
variable (hγ0 : γ 0 = KaehlerDifferential.D k B (φ a))
variable (hγ1 : γ 1 = KaehlerDifferential.D k B t)
variable (hrel : φ a * t = φ b)

include hβ0 hβ1 hγ0 hγ1 hrel in
/-- The actual coordinate bases identify the original wedge image. -/
theorem map_basis_wedge :
    map k φ 2 ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A 2 β) =
      φ a • exteriorPower.ιMulti B 2 γ := by
  have hs : (β : Fin 2 → KaehlerDifferential k A) =
      ![KaehlerDifferential.D k A a, KaehlerDifferential.D k A b] := by
    funext i
    fin_cases i
    · exact hβ0
    · exact hβ1
  have ht : (γ : Fin 2 → KaehlerDifferential k B) =
      ![KaehlerDifferential.D k B (φ a), KaehlerDifferential.D k B t] := by
    funext i
    fin_cases i
    · exact hγ0
    · exact hγ1
  rw [hs, ht]
  exact map_one_tmul_wedge_of_relation k φ a b t hrel

include hβ0 hβ1 hγ0 hγ1 hrel in
/-- The original product equation determines the whole native map in these
actual frames, not only its value on the coordinate wedge. -/
theorem map_frame (ω : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2)) :
    map k φ 2 ω =
      (extendedFrame k φ β ω * φ a) • exteriorPower.ιMulti B 2 γ := by
  calc
    _ = map k φ 2 (extendedFrame k φ β ω •
        ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A 2 β)) :=
      congrArg (map k φ 2) (extendedFrame_expansion k φ β ω).symm
    _ = extendedFrame k φ β ω • map k φ 2
        ((1 : B) ⊗ₜ[A,φ.toRingHom] exteriorPower.ιMulti A 2 β) :=
      (map k φ 2).hom.map_smul _ _
    _ = _ := by
      rw [map_basis_wedge k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel, smul_smul]

/-- The coefficient map is the actual native map followed by the actual target frame. -/
def framedMap : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2) →ₗ[B] B :=
  (determinantEquiv γ).toLinearMap.comp (map k φ 2).hom

include hβ0 hβ1 hγ0 hγ1 hrel in
/-- The coefficient of the whole original map is multiplication by the
original exceptional parameter. -/
theorem framedMap_apply (ω : (ModuleCat.extendScalars φ.toRingHom).obj
    ((differentialModule k A).exteriorPower 2)) :
    framedMap k φ γ ω = extendedFrame k φ β ω * φ a := by
  change determinantEquiv γ (map k φ 2 ω) = _
  rw [map_frame k φ β γ a b t hβ0 hβ1 hγ0 hγ1 hrel,
    LinearEquiv.map_smul (determinantEquiv γ)
      (extendedFrame k φ β ω * φ a) (exteriorPower.ιMulti B 2 γ),
    determinantEquiv_basis_wedge, smul_eq_mul, mul_one]

end KltDP.Geometry.AffineNativeTopDifferential
