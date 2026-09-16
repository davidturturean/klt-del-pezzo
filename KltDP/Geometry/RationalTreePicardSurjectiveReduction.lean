import KltDP.Geometry.RationalTreePicardSurjective

/-!
# Surjectivity of the multidegree map from the coordinate line bundles

BRIEF15, reduction. The multidegree homomorphism `multidegreeHom k X e : X.Pic →* (components →
Multiplicative ℤ)` is surjective as soon as, for every component `C`, some line bundle has component
exponent `1` on `C` and `0` on every other component (`multidegreeHom_surjective_of_coordinate`): its
range is a subgroup containing the coordinate vectors `Pi.mulSingle C (ofAdd 1)`, hence their
integer powers and all their products, i.e. everything (`Finset.univ_prod_mulSingle`). This isolates
the remaining construction of the surjectivity half as the "coordinate" line bundles, one per
component, independently of the node gluing of arbitrary line bundles.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (k : Type u) [Field k] (X : Scheme.{u}) [NoetherianSpace X]
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

open scoped Classical in
/-- The class of a coordinate line bundle is the coordinate vector. -/
theorem multidegreeHom_toPic_eq_mulSingle (C : ↥(irreducibleComponents X)) (L : InvertibleSheaf X)
    (hC : componentExponent k X {C} (e C) L = 1)
    (hD : ∀ D : ↥(irreducibleComponents X), D ≠ C → componentExponent k X {D} (e D) L = 0) :
    multidegreeHom k X e L.toPic =
      (Pi.mulSingle C (Multiplicative.ofAdd (1 : ℤ)) :
        ↥(irreducibleComponents X) → Multiplicative ℤ) := by
  rw [multidegreeHom_toPic]
  funext D
  rw [Pi.mulSingle_apply]
  by_cases h : D = C
  · subst h
    rw [if_pos rfl, hC]
  · rw [if_neg h, hD D h]
    rfl

/-- The multidegree homomorphism is surjective once every component carries a coordinate line
bundle (exponent `1` there, `0` elsewhere). -/
theorem multidegreeHom_surjective_of_coordinate
    (h : ∀ C : ↥(irreducibleComponents X), ∃ L : InvertibleSheaf X,
      componentExponent k X {C} (e C) L = 1 ∧
        ∀ D : ↥(irreducibleComponents X), D ≠ C → componentExponent k X {D} (e D) L = 0) :
    Function.Surjective (multidegreeHom k X e) := by
  classical
  haveI : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  haveI := Fintype.ofFinite ↥(irreducibleComponents X)
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro m _
  rw [← Finset.univ_prod_mulSingle m]
  refine Subgroup.prod_mem _ fun C _ => ?_
  obtain ⟨L, hC, hD⟩ := h C
  have hδ : (Pi.mulSingle C (Multiplicative.ofAdd (1 : ℤ)) :
      ↥(irreducibleComponents X) → Multiplicative ℤ) ∈ (multidegreeHom k X e).range :=
    ⟨L.toPic, multidegreeHom_toPic_eq_mulSingle k X e C L hC hD⟩
  have hpow : (Pi.mulSingle C (m C) : ↥(irreducibleComponents X) → Multiplicative ℤ) =
      (Pi.mulSingle C (Multiplicative.ofAdd (1 : ℤ)) :
        ↥(irreducibleComponents X) → Multiplicative ℤ) ^ (Multiplicative.toAdd (m C)) := by
    funext D
    rw [Pi.pow_apply, Pi.mulSingle_apply, Pi.mulSingle_apply]
    by_cases hDC : D = C
    · rw [if_pos hDC, if_pos hDC, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    · rw [if_neg hDC, if_neg hDC, one_zpow]
  rw [hpow]
  exact Subgroup.zpow_mem _ hδ _

end KltDP.Geometry.RationalTreePicard
