import KltDP.Geometry.TransverseBranchesCotangentQuotient
import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The cotangent space of the ordinary double point model `k⟦x, y⟧ ⧸ (x y)`

BRIEF26 (the completed-stalk nodality interface), algebraic part on the model. Let
`P = k⟦x, y⟧ = MvPowerSeries (Fin 2) k` and `M = P ⧸ (X 0 * X 1)` (the accepted
`ordinaryDoublePointModel k`). This module proves:

* the maximal ideal of `P` is `(X 0, X 1)` (`span_X_eq_maximalIdeal`: a series with vanishing
  constant coefficient is `X 0 · a + X 1 · b`, with `b` the part of the series in `X 1` alone);
* the coefficients of a series in `m_P ^ 2` in degree one vanish (`coeff_single_eq_zero_of_mem_sq`),
  hence the classes of `X 0`, `X 1` form a basis of the cotangent space of `P`
  (`xBasis`, `finrank_cotangentSpace_eq_two`);
* `M` is a local ring (`model_isLocalRing`), the quotient map is local (`mk_isLocalHom`), and by the
  accepted transversal-crossing normal form `transverse_of_crossing_quotient`
  (`(X 0, X 1) = m_P`, `ker (P → M) = (X 0 · X 1)`), **the cotangent space of `M` is two-dimensional
  with the classes of `x̄ = X 0`, `ȳ = X 1` linearly independent** (`model_cotangent`);
* every element of `M` is a constant modulo the maximal ideal (`exists_sub_algebraMap_mem_maximalIdeal`,
  the residue field of the model is `k`).

No `MvPowerSeries` fact beyond coefficient manipulation (`X_dvd_iff`, `coeff_add_monomial_mul`,
`isUnit_iff_constantCoeff`) is used.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.OrdinaryDoublePointModel

open KltDP.Geometry.IntrinsicNodal

variable (k : Type u) [Field k]

/-- The two-variable power series ring `k⟦x, y⟧`. -/
abbrev PS := MvPowerSeries (Fin 2) k

/-! ## The maximal ideal of `k⟦x, y⟧` -/

theorem constantCoeff_eq_zero_of_mem_maximalIdeal {φ : PS k} (h : φ ∈ maximalIdeal (PS k)) :
    MvPowerSeries.constantCoeff (Fin 2) k φ = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not] at h
  exact h

theorem mem_maximalIdeal_of_constantCoeff_eq_zero {φ : PS k}
    (h : MvPowerSeries.constantCoeff (Fin 2) k φ = 0) : φ ∈ maximalIdeal (PS k) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, h]
  exact not_isUnit_zero

theorem X_mem_maximalIdeal (i : Fin 2) : (MvPowerSeries.X i : PS k) ∈ maximalIdeal (PS k) :=
  mem_maximalIdeal_of_constantCoeff_eq_zero k (MvPowerSeries.constantCoeff_X i)

/-- The part of a series involving only `X 1`: the coefficients with `m 0 = 0`. -/
def yPart (φ : PS k) : PS k := fun m => if m 0 = 0 then MvPowerSeries.coeff k m φ else 0

theorem coeff_yPart (φ : PS k) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff k m (yPart k φ) = if m 0 = 0 then MvPowerSeries.coeff k m φ else 0 := rfl

theorem X_dvd_sub_yPart (φ : PS k) : (MvPowerSeries.X 0 : PS k) ∣ φ - yPart k φ := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [map_sub, coeff_yPart, if_pos hm, sub_self]

theorem X_dvd_yPart (φ : PS k) (h : MvPowerSeries.constantCoeff (Fin 2) k φ = 0) :
    (MvPowerSeries.X 1 : PS k) ∣ yPart k φ := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [coeff_yPart]
  split_ifs with h0
  · have hm0 : m = 0 := Finsupp.ext fun i => by
      fin_cases i
      · simpa using h0
      · simpa using hm
    rw [hm0]
    exact h
  · rfl

theorem mem_span_X_of_mem_maximalIdeal {φ : PS k} (h : φ ∈ maximalIdeal (PS k)) :
    φ ∈ Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set (PS k)) := by
  have h0 := constantCoeff_eq_zero_of_mem_maximalIdeal k h
  obtain ⟨a, ha⟩ := X_dvd_sub_yPart k φ
  obtain ⟨b, hb⟩ := X_dvd_yPart k φ h0
  have hφ : φ = MvPowerSeries.X 0 * a + MvPowerSeries.X 1 * b := by
    rw [← ha, ← hb, sub_add_cancel]
  rw [hφ]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- **The maximal ideal of `k⟦x, y⟧` is `(X 0, X 1)`.** -/
theorem span_X_eq_maximalIdeal :
    Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set (PS k)) = maximalIdeal (PS k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro φ (rfl | rfl)
    · exact X_mem_maximalIdeal k 0
    · exact X_mem_maximalIdeal k 1
  · intro φ hφ
    exact mem_span_X_of_mem_maximalIdeal k hφ

/-! ## Degree-one coefficients -/

theorem coeff_single_X_mul (i : Fin 2) (c : PS k) :
    MvPowerSeries.coeff k (Finsupp.single i 1) (MvPowerSeries.X i * c) =
      MvPowerSeries.constantCoeff (Fin 2) k c := by
  have h := MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single i 1) (n := 0) (φ := c) (1 : k)
  rw [add_zero] at h
  rw [MvPowerSeries.X, h, one_mul]
  rfl

theorem coeff_single_X_mul_of_ne {i j : Fin 2} (hij : i ≠ j) (c : PS k) :
    MvPowerSeries.coeff k (Finsupp.single i 1) (MvPowerSeries.X j * c) = 0 :=
  MvPowerSeries.X_dvd_iff.mp (dvd_mul_right _ _) _ (by rw [Finsupp.single_apply, if_neg hij])

/-- The degree-one coefficients of `X 0 · a₀ + X 1 · a₁` are the constant coefficients of the
`aᵢ`. -/
theorem coeff_single_X_mul_add (a₀ a₁ : PS k) (i : Fin 2) :
    MvPowerSeries.coeff k (Finsupp.single i 1) (MvPowerSeries.X 0 * a₀ + MvPowerSeries.X 1 * a₁) =
      MvPowerSeries.constantCoeff (Fin 2) k (![a₀, a₁] i) := by
  fin_cases i
  · show MvPowerSeries.coeff k (Finsupp.single (0 : Fin 2) 1)
        (MvPowerSeries.X 0 * a₀ + MvPowerSeries.X 1 * a₁) =
      MvPowerSeries.constantCoeff (Fin 2) k a₀
    rw [map_add, coeff_single_X_mul, coeff_single_X_mul_of_ne k (by decide : (0 : Fin 2) ≠ 1),
      add_zero]
  · show MvPowerSeries.coeff k (Finsupp.single (1 : Fin 2) 1)
        (MvPowerSeries.X 0 * a₀ + MvPowerSeries.X 1 * a₁) =
      MvPowerSeries.constantCoeff (Fin 2) k a₁
    rw [map_add, coeff_single_X_mul_of_ne k (by decide : (1 : Fin 2) ≠ 0), coeff_single_X_mul,
      zero_add]

/-- A series in `m_P ^ 2` has vanishing coefficients in degree one. -/
theorem coeff_single_eq_zero_of_mem_sq {φ : PS k} (h : φ ∈ maximalIdeal (PS k) ^ 2) (i : Fin 2) :
    MvPowerSeries.coeff k (Finsupp.single i 1) φ = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp (mem_span_X_of_mem_maximalIdeal k ha)
    have hab : a * b = MvPowerSeries.X 0 * (u * b) + MvPowerSeries.X 1 * (v * b) := by
      rw [← huv]
      ring
    have hb0 := constantCoeff_eq_zero_of_mem_maximalIdeal k hb
    rw [hab, coeff_single_X_mul_add]
    fin_cases i
    · show MvPowerSeries.constantCoeff (Fin 2) k (u * b) = 0
      rw [map_mul, hb0, mul_zero]
    · show MvPowerSeries.constantCoeff (Fin 2) k (v * b) = 0
      rw [map_mul, hb0, mul_zero]
  · rw [map_add, hx, hy, add_zero]

/-! ## The cotangent space of `k⟦x, y⟧` -/

/-- The classes of `X 0`, `X 1` in the cotangent space of `k⟦x, y⟧`. -/
def xClass (i : Fin 2) : CotangentSpace (PS k) :=
  (maximalIdeal (PS k)).toCotangent ⟨MvPowerSeries.X i, X_mem_maximalIdeal k i⟩

theorem residue_smul_toCotangent {R : Type u} [CommRing R] [IsLocalRing R] (r : R)
    (w : maximalIdeal R) :
    residue R r • (maximalIdeal R).toCotangent w = (maximalIdeal R).toCotangent (r • w) := by
  first
  | exact Module.Quotient.mk_smul_mk r w
  | rfl

theorem top_le_span_xClass :
    ⊤ ≤ Submodule.span (ResidueField (PS k)) (Set.range (xClass k)) := by
  rintro c -
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := (maximalIdeal (PS k)).toCotangent_surjective c
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp (mem_span_X_of_mem_maximalIdeal k hφ)
  have hc : (maximalIdeal (PS k)).toCotangent ⟨φ, hφ⟩ =
      residue (PS k) u • xClass k 0 + residue (PS k) v • xClass k 1 := by
    rw [xClass, xClass, residue_smul_toCotangent, residue_smul_toCotangent, ← map_add]
    congr 1
    exact Subtype.ext huv.symm
  rw [hc]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem linearIndependent_xClass : LinearIndependent (ResidueField (PS k)) (xClass k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => residue_surjective (R := PS k) (g j)
  have hsum : (∑ j, g j • xClass k j) = (maximalIdeal (PS k)).toCotangent
      (∑ j, a j • (⟨MvPowerSeries.X j, X_mem_maximalIdeal k j⟩ : maximalIdeal (PS k))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, xClass, residue_smul_toCotangent]
  have hval : ((∑ j, a j • (⟨MvPowerSeries.X j, X_mem_maximalIdeal k j⟩ : maximalIdeal (PS k)) :
      maximalIdeal (PS k)) : PS k) = MvPowerSeries.X 0 * a 0 + MvPowerSeries.X 1 * a 1 := by
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_mk,
      smul_eq_mul]
    ring
  rw [hsum, Ideal.toCotangent_eq_zero, hval] at hg
  have hc := coeff_single_eq_zero_of_mem_sq k hg i
  rw [coeff_single_X_mul_add] at hc
  rw [← ha i, residue_eq_zero_iff]
  apply mem_maximalIdeal_of_constantCoeff_eq_zero
  fin_cases i
  · exact hc
  · exact hc

/-- The classes of `X 0`, `X 1` form a basis of the cotangent space of `k⟦x, y⟧`. -/
def xBasis : Basis (Fin 2) (ResidueField (PS k)) (CotangentSpace (PS k)) :=
  Basis.mk (linearIndependent_xClass k) (top_le_span_xClass k)

/-- **The cotangent space of `k⟦x, y⟧` is two-dimensional.** -/
theorem finrank_cotangentSpace_eq_two :
    Module.finrank (ResidueField (PS k)) (CotangentSpace (PS k)) = 2 := by
  rw [Module.finrank_eq_card_basis (xBasis k), Fintype.card_fin]

/-! ## The model `k⟦x, y⟧ ⧸ (x y)` -/

/-- The ideal `(X 0 · X 1)` of `k⟦x, y⟧`. -/
abbrev nodeIdeal : Ideal (PS k) := Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}

theorem nodeIdeal_ne_top : nodeIdeal k ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, MvPowerSeries.isUnit_iff_constantCoeff, map_mul,
    MvPowerSeries.constantCoeff_X, zero_mul]
  exact not_isUnit_zero

theorem model_nontrivial : Nontrivial (ordinaryDoublePointModel k) :=
  Ideal.Quotient.nontrivial (nodeIdeal_ne_top k)

/-- The model is a local ring. -/
instance model_isLocalRing : IsLocalRing (ordinaryDoublePointModel k) :=
  haveI := model_nontrivial k
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (nodeIdeal k)) Ideal.Quotient.mk_surjective

theorem mk_isLocalHom : IsLocalHom (Ideal.Quotient.mk (nodeIdeal k)) :=
  haveI := model_nontrivial k
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- The classes `x̄ = X 0`, `ȳ = X 1` in the maximal ideal of the model. -/
def xBar (i : Fin 2) : maximalIdeal (ordinaryDoublePointModel k) :=
  ⟨Ideal.Quotient.mk (nodeIdeal k) (MvPowerSeries.X i),
    haveI := mk_isLocalHom k
    map_nonunit (Ideal.Quotient.mk (nodeIdeal k)) _ (X_mem_maximalIdeal k i)⟩

theorem xBar_val (i : Fin 2) :
    (xBar k i : ordinaryDoublePointModel k) = Ideal.Quotient.mk (nodeIdeal k) (MvPowerSeries.X i) :=
  rfl

/-- **The cotangent space of `k⟦x, y⟧ ⧸ (x y)` is two-dimensional, with the classes of `x̄`, `ȳ`
linearly independent** (the accepted transversal-crossing normal form applied to
`(X 0, X 1) = m_P`, `ker = (X 0 · X 1)`). -/
theorem model_cotangent :
    Module.finrank (ResidueField (ordinaryDoublePointModel k))
        (CotangentSpace (ordinaryDoublePointModel k)) = 2 ∧
      LinearIndependent (ResidueField (ordinaryDoublePointModel k))
        (fun i : Fin 2 => (maximalIdeal (ordinaryDoublePointModel k)).toCotangent (xBar k i)) := by
  haveI := mk_isLocalHom k
  exact KltDP.Geometry.RationalTreePicard.transverse_of_crossing_quotient
    (Ideal.Quotient.mk (nodeIdeal k)) Ideal.Quotient.mk_surjective
    (finrank_cotangentSpace_eq_two k) (fun i => ⟨MvPowerSeries.X i, X_mem_maximalIdeal k i⟩)
    (span_X_eq_maximalIdeal k) Ideal.mk_ker

theorem finrank_model_cotangentSpace :
    Module.finrank (ResidueField (ordinaryDoublePointModel k))
      (CotangentSpace (ordinaryDoublePointModel k)) = 2 :=
  (model_cotangent k).1

theorem linearIndependent_xBar :
    LinearIndependent (ResidueField (ordinaryDoublePointModel k))
      (fun i : Fin 2 => (maximalIdeal (ordinaryDoublePointModel k)).toCotangent (xBar k i)) :=
  (model_cotangent k).2

/-- `x̄ ȳ = 0` in the model. -/
theorem xBar_mul_xBar :
    (xBar k 0 : ordinaryDoublePointModel k) * xBar k 1 = 0 := by
  rw [xBar_val, xBar_val, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Membership in the maximal ideal of the model is checked on a representative. -/
theorem mk_mem_maximalIdeal_iff (φ : PS k) :
    Ideal.Quotient.mk (nodeIdeal k) φ ∈ maximalIdeal (ordinaryDoublePointModel k) ↔
      φ ∈ maximalIdeal (PS k) := by
  haveI := mk_isLocalHom k
  constructor
  · intro h
    rw [mem_maximalIdeal, mem_nonunits_iff] at h ⊢
    exact fun hu => h (hu.map _)
  · intro h
    exact map_nonunit _ _ h

/-- **The maximal ideal of the model is generated by `x̄`, `ȳ`**: every element of it is
`a x̄ + b ȳ`. -/
theorem exists_eq_mul_xBar_add {z : ordinaryDoublePointModel k}
    (hz : z ∈ maximalIdeal (ordinaryDoublePointModel k)) :
    ∃ a b : ordinaryDoublePointModel k, z = a * xBar k 0 + b * xBar k 1 := by
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp
    (mem_span_X_of_mem_maximalIdeal k ((mk_mem_maximalIdeal_iff k φ).mp hz))
  exact ⟨Ideal.Quotient.mk (nodeIdeal k) u, Ideal.Quotient.mk (nodeIdeal k) v, by
    rw [xBar_val, xBar_val, ← map_mul, ← map_mul, ← map_add, huv]⟩

/-- A constant in the maximal ideal of the model is zero. -/
theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k (ordinaryDoublePointModel k) c ∈ maximalIdeal (ordinaryDoublePointModel k) ↔
      c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k (ordinaryDoublePointModel k)))
  · rintro rfl
    rw [map_zero]
    exact Ideal.zero_mem _

/-! ## The residue field of the model is `k` -/

theorem sub_algebraMap_constantCoeff_mem_maximalIdeal (φ : PS k) :
    φ - algebraMap k (PS k) (MvPowerSeries.constantCoeff (Fin 2) k φ) ∈ maximalIdeal (PS k) := by
  apply mem_maximalIdeal_of_constantCoeff_eq_zero
  rw [map_sub, ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C, sub_self]

/-- Every element of the model is a constant modulo the maximal ideal. -/
theorem exists_sub_algebraMap_mem_maximalIdeal (z : ordinaryDoublePointModel k) :
    ∃ c : k, z - algebraMap k (ordinaryDoublePointModel k) c ∈
      maximalIdeal (ordinaryDoublePointModel k) := by
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨MvPowerSeries.constantCoeff (Fin 2) k φ, ?_⟩
  haveI := mk_isLocalHom k
  have h := map_nonunit (Ideal.Quotient.mk (nodeIdeal k)) _
    (sub_algebraMap_constantCoeff_mem_maximalIdeal k φ)
  rwa [map_sub, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at h

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] :
    Module.finrank (ResidueField (ordinaryDoublePointModel k₀))
      (CotangentSpace (ordinaryDoublePointModel k₀)) = 2 :=
  finrank_model_cotangentSpace k₀

end KltDP.RingTheory.OrdinaryDoublePointModel
