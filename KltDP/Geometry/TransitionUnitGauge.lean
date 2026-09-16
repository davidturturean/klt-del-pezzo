/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

The matching-family coboundary proofs are adapted from
frenzymath/Algebraic-Geometry 9223d85c786394721963a9d642b08d066b72a594,
MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Cohomology/
GluedSheafCongr.lean:42-170. They are upgraded to linearity over the original
section rings and isomorphisms in the actual category X.Modules.
-/
import KltDP.Geometry.TransitionUnitLocalTriviality

/-!
# Actual gauge isomorphisms of cocycle-glued module sheaves

A family of units b_i with b_i g_ij = h_ij b_j gives the actual map of
matching sections s_i ↦ b_i s_i. Its inverse uses b_i⁻¹. These maps are
linear over each original section ring and commute with restrictions,
so they construct an isomorphism in X.Modules. No cocycle law or covering
hypothesis is needed for this gauge isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g h : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (b : ∀ i : ι, Γ(X, U i)ˣ)

/-- The original gauge equation on each double overlap. -/
def IsGauge : Prop :=
  ∀ i j : ι,
    res X (inf_le_left : U i ⊓ U j ≤ U i) (b i) * (g i j : Γ(X, U i ⊓ U j)) =
      (h i j : Γ(X, U i ⊓ U j)) * res X (inf_le_right : U i ⊓ U j ≤ U j) (b j)

/-- The inverse unit family gives the reverse gauge equation. -/
theorem IsGauge.inv (hb : IsGauge X U g h b) :
    IsGauge X U h g (fun i => (b i)⁻¹) := by
  intro i j
  set a := res X (inf_le_left : U i ⊓ U j ≤ U i) (b i : Γ(X, U i)) with ha
  set a' := res X (inf_le_left : U i ⊓ U j ≤ U i)
    (((b i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) with ha'
  set c := res X (inf_le_right : U i ⊓ U j ≤ U j) (b j : Γ(X, U j)) with hc
  set c' := res X (inf_le_right : U i ⊓ U j ≤ U j)
    (((b j)⁻¹ : Γ(X, U j)ˣ) : Γ(X, U j)) with hc'
  have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, Units.inv_mul, map_one]
  have hcc : c * c' = 1 := by rw [hc, hc', ← map_mul, Units.mul_inv, map_one]
  have key : a * (g i j : Γ(X, U i ⊓ U j)) = (h i j : Γ(X, U i ⊓ U j)) * c := hb i j
  calc a' * (h i j : Γ(X, U i ⊓ U j))
      = a' * (h i j : Γ(X, U i ⊓ U j)) * (c * c') := by rw [hcc, mul_one]
    _ = a' * ((h i j : Γ(X, U i ⊓ U j)) * c) * c' := by ring
    _ = a' * (a * (g i j : Γ(X, U i ⊓ U j))) * c' := by rw [key]
    _ = (a' * a) * (g i j : Γ(X, U i ⊓ U j)) * c' := by ring
    _ = (g i j : Γ(X, U i ⊓ U j)) * c' := by rw [haa, one_mul]

/-- Componentwise multiplication by the gauge units preserves matching. -/
theorem gauge_mem (hb : IsGauge X U g h b) {W : X.Opens}
    {s : ∀ i : ι, Γ(X, W ⊓ U i)} (hs : s ∈ sections X U g W) :
    (fun i => res X (inf_le_right : W ⊓ U i ≤ U i) (b i) * s i) ∈
      sections X U h W := by
  intro i j
  have hbase := congrArg (res X (inclCoc X U W i j)) (hb i j)
  have hmatch := (mem_sections_iff X U g W s).mp hs i j
  rw [map_mul, map_mul] at hbase
  rw [map_mul, map_mul]
  simp only [res_res] at hbase hmatch ⊢
  rw [hmatch, ← mul_assoc, hbase, mul_assoc, mul_left_comm]

/-- Gauge transport is linear over the actual original section ring O(W). -/
def gaugeEquiv (hb : IsGauge X U g h b) (W : X.Opens) :
    sections X U g W ≃ₗ[Γ(X, W)] sections X U h W where
  toFun s := ⟨fun i => res X (inf_le_right : W ⊓ U i ≤ U i) (b i) * s.val i,
    gauge_mem X U g h b hb s.property⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    change res X (inf_le_right : W ⊓ U i ≤ U i) (b i : Γ(X, U i)) *
      (s.val i + t.val i) = _
    rw [mul_add]
    rfl
  map_smul' r s := by
    apply Subtype.ext
    funext i
    change res X (inf_le_right : W ⊓ U i ≤ U i) (b i) *
        (res X (inf_le_left : W ⊓ U i ≤ W) r * s.val i) =
      res X (inf_le_left : W ⊓ U i ≤ W) r *
        (res X (inf_le_right : W ⊓ U i ≤ U i) (b i) * s.val i)
    exact mul_left_comm _ _ _
  invFun t := ⟨fun i => res X (inf_le_right : W ⊓ U i ≤ U i)
      (((b i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) * t.val i,
    gauge_mem X U h g (fun i => (b i)⁻¹) (IsGauge.inv X U g h b hb) t.property⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    change res X _ (((b i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) *
      (res X _ (b i : Γ(X, U i)) * s.val i) = s.val i
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  right_inv t := by
    apply Subtype.ext
    funext i
    change res X _ (b i : Γ(X, U i)) *
      (res X _ (((b i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) * t.val i) = t.val i
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

@[simp]
theorem gaugeEquiv_val (hb : IsGauge X U g h b) {W : X.Opens}
    (s : sections X U g W) (i : ι) :
    (gaugeEquiv X U g h b hb W s).val i =
      res X (inf_le_right : W ⊓ U i ≤ U i) (b i) * s.val i := rfl

@[simp]
theorem gaugeEquiv_symm_val (hb : IsGauge X U g h b) {W : X.Opens}
    (s : sections X U h W) (i : ι) :
    ((gaugeEquiv X U g h b hb W).symm s).val i =
      res X (inf_le_right : W ⊓ U i ≤ U i)
        (((b i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) * s.val i := rfl

/-- The gauge map commutes with the actual section restrictions. -/
theorem gaugeEquiv_restrict (hb : IsGauge X U g h b) {V W : X.Opens}
    (hVW : V ≤ W) (s : sections X U g W) :
    gaugeEquiv X U g h b hb V (restrict X U g hVW s) =
      restrict X U h hVW (gaugeEquiv X U g h b hb W s) := by
  apply Subtype.ext
  funext i
  rw [gaugeEquiv_val, restrict_val, restrict_val, gaugeEquiv_val, map_mul]
  simp only [res_res]

/-- The actual isomorphism in X.Modules induced by the original gauge units. -/
def gaugeIso (hb : IsGauge X U g h b) : moduleSheaf X U g ≅ moduleSheaf X U h := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun W => (gaugeEquiv X U g h b hb W.unop).toModuleIso) ?_
  intro V W f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change gaugeEquiv X U g h b hb W.unop (restrict X U g f.unop.le s) =
    restrict X U h f.unop.le (gaugeEquiv X U g h b hb V.unop s)
  exact gaugeEquiv_restrict X U g h b hb f.unop.le s

@[simp]
theorem gaugeIso_hom_app_apply (hb : IsGauge X U g h b)
    (W : X.Opensᵒᵖ) (s : sections X U g W.unop) :
    (gaugeIso X U g h b hb).hom.val.app W s = gaugeEquiv X U g h b hb W.unop s := rfl

@[simp]
theorem gaugeIso_inv_app_apply (hb : IsGauge X U g h b)
    (W : X.Opensᵒᵖ) (s : sections X U h W.unop) :
    (gaugeIso X U g h b hb).inv.val.app W s =
      (gaugeEquiv X U g h b hb W.unop).symm s := rfl

/-- In a chart, the constructed gauge map is multiplication by the original local unit. -/
theorem gaugeEquiv_trivialization (hb : IsGauge X U g h b)
    (hg : IsCocycle X U g) (hh : IsCocycle X U h) (i : ι)
    {W : X.Opens} (hWi : W ≤ U i) (s : sections X U g W) :
    trivialization X U h hh i hWi (gaugeEquiv X U g h b hb W s) =
      res X hWi (b i) * trivialization X U g hg i hWi s := by
  rw [trivialization_apply, gaugeEquiv_val, map_mul, res_res, trivialization_apply]

end KltDP.Geometry.TransitionUnitGluing
