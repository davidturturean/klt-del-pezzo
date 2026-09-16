/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

The section trivialization proofs are adapted from
frenzymath/Algebraic-Geometry9223d85c786394721963a9d642b08d066b72a594,
PicardAlbanese/AlgebraicJacobian/Cohomology/GluedSheaf.lean:287-363.
They are upgraded to linearity over the actual ring O(W) and packaged as
isomorphisms of the project's actual structure-sheaf modules.
-/
import KltDP.Geometry.TransitionUnitSheaf
import KltDP.Geometry.InvertibleSheaf
import KltDP.Compatibility.SheafUnitAutomorphisms

/-!
# Actual local trivializations of the cocycle-glued module sheaf

The cocycle law reconstructs a matching family from any chosen chart
component. The resulting O(W)-linear equivalences commute with restriction,
so they assemble into actual module-sheaf isomorphisms. On a covering family
these constructed isomorphisms give local freeness of rank one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)

/-- A chart component gives a linear equivalence over the original section ring. -/
def trivialization (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    sections X U g W ≃ₗ[Γ(X, W)] Γ(X, W) where
  toFun s := res X (le_inf le_rfl hW) (s.val j)
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    change res X (le_inf le_rfl hW)
      (res X (inf_le_left : W ⊓ U j ≤ W) r * s.val j) =
        r * res X (le_inf le_rfl hW) (s.val j)
    rw [map_mul, res_res, res_self]
  invFun t := ⟨fun i =>
    res X (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U i ≤ U i ⊓ U j)
      (g i j) * res X (inf_le_left : W ⊓ U i ≤ W) t, by
    intro i i'
    have hO : W ⊓ U i ⊓ U i' ≤ U i ⊓ U i' ⊓ U j :=
      le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        ((inf_le_left.trans inf_le_left).trans hW)
    have h := IsCocycle.mul_res_of_le X U g hc (i := i) (j := i') (l := j) hO
    rw [map_mul, map_mul]
    simp only [res_res]
    rw [← h, mul_assoc]⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    have hloc := s.property i j
    have key := congrArg
      (res X (le_inf le_rfl (inf_le_left.trans hW) : W ⊓ U i ≤ W ⊓ U i ⊓ U j)) hloc
    rw [map_mul] at key
    simp only [res_res] at key
    rw [res_self] at key
    change res X (le_inf inf_le_right (inf_le_left.trans hW)) (g i j) *
      res X (inf_le_left : W ⊓ U i ≤ W)
        (res X (le_inf le_rfl hW) (s.val j)) = s.val i
    rw [res_res, ← key]
  right_inv t := by
    change res X (le_inf le_rfl hW)
      (res X (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U j ≤ U j ⊓ U j)
        (g j j) * res X (inf_le_left : W ⊓ U j ≤ W) t) = t
    rw [map_mul, hc.unit_self j, map_one, map_one, one_mul, res_res, res_self]

@[simp]
theorem trivialization_apply (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (s : sections X U g W) :
    trivialization X U g hc j hW s = res X (le_inf le_rfl hW) (s.val j) := rfl

@[simp]
theorem trivialization_symm_val (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (t : Γ(X, W)) (i : ι) :
    ((trivialization X U g hc j hW).symm t).val i =
      res X (le_inf inf_le_right (inf_le_left.trans hW) : W ⊓ U i ≤ U i ⊓ U j)
        (g i j) * res X (inf_le_left : W ⊓ U i ≤ W) t := rfl

/-- The section equivalences commute with the actual restriction maps. -/
theorem trivialization_restrict (j : ι) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ U j)
    (s : sections X U g W) :
    trivialization X U g hc j (h.trans hW) (restrict X U g h s) =
      res X h (trivialization X U g hc j hW s) := by
  rw [trivialization_apply, trivialization_apply, restrict_val]
  simp only [res_res]

/-- On common subopens, the constructed chart maps recover the original cocycle. -/
theorem trivialization_transition (i j : ι) {W : X.Opens}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (s : sections X U g W) :
    trivialization X U g hc i hWi s =
      res X (le_inf hWi hWj : W ≤ U i ⊓ U j) (g i j) *
        trivialization X U g hc j hWj s := by
  have key := congrArg
    (res X (le_inf (le_inf le_rfl hWi) hWj : W ≤ W ⊓ U i ⊓ U j)) (s.property i j)
  rw [map_mul] at key
  simp only [res_res] at key
  rw [trivialization_apply, trivialization_apply]
  exact key

/-- The constructed actual module-sheaf isomorphism over any subopen of a chart. -/
def chartIsoOn (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    (moduleSheaf X U g).over W ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over W) := by
  apply (_root_.SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over W)).preimageIso
  refine _root_.PresheafOfModules.isoMk
    (fun V => (trivialization X U g hc j (V.unop.hom.le.trans hW)).toModuleIso) ?_
  intro V Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change trivialization X U g hc j (Z.unop.hom.le.trans hW)
      (restrict X U g f.unop.left.le s) =
    res X f.unop.left.le
      (trivialization X U g hc j (V.unop.hom.le.trans hW) s)
  exact trivialization_restrict X U g hc j f.unop.left.le (V.unop.hom.le.trans hW) s

@[simp]
theorem chartIsoOn_hom_app_apply (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (V : (Over W)ᵒᵖ) (s : sections X U g V.unop.left) :
    (chartIsoOn X U g hc j hW).hom.val.app V s =
      trivialization X U g hc j (V.unop.hom.le.trans hW) s := rfl

@[simp]
theorem chartIsoOn_inv_app_apply (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (V : (Over W)ᵒᵖ) (s : Γ(X, V.unop.left)) :
    (chartIsoOn X U g hc j hW).inv.val.app V s =
      (trivialization X U g hc j (V.unop.hom.le.trans hW)).symm s := rfl

local instance chartSectionCommRing (V : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.val.obj V) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The actual change of chart is precisely multiplication by the original unit. -/
theorem chartIsoOn_transition (i j : ι) {W : X.Opens}
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    KltDP.SheafOfModules.overUnitSectionUnitsEquivAut X.ringCatSheaf W
        (Units.map (res X (le_inf hWi hWj)).toMonoidHom (g i j)) =
      (chartIsoOn X U g hc j hWj).symm ≪≫ chartIsoOn X U g hc i hWi := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change Γ(X, V.unop.left) at s
  change s * res X (show V.unop.left ≤ W from V.unop.hom.le)
      (res X (le_inf hWi hWj) (g i j)) =
    trivialization X U g hc i (V.unop.hom.le.trans hWi)
      ((trivialization X U g hc j (V.unop.hom.le.trans hWj)).symm s)
  rw [trivialization_transition X U g hc i j
      (V.unop.hom.le.trans hWi) (V.unop.hom.le.trans hWj),
    LinearEquiv.apply_symm_apply]
  calc
    s * res X (show V.unop.left ≤ W from V.unop.hom.le)
        (res X (le_inf hWi hWj) (g i j)) =
      res X (show V.unop.left ≤ W from V.unop.hom.le)
        (res X (le_inf hWi hWj) (g i j)) * s := mul_comm _ _
    _ = res X (show V.unop.left ≤ U i ⊓ U j from
        le_inf (V.unop.hom.le.trans hWi) (V.unop.hom.le.trans hWj))
        (g i j) * s :=
      congrArg (fun a : Γ(X, V.unop.left) => a * s)
        (res_res X (show V.unop.left ≤ W from V.unop.hom.le)
          (le_inf hWi hWj) (g i j))

theorem opens_coversTop (hU : (⨆ i, U i) = ⊤) :
    (Opens.grothendieckTopology X).CoversTop U := by
  intro V x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxU
  exact ⟨V ⊓ U i, homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hxi⟩⟩

/-- The actual chart isomorphisms give a singleton local basis on a cover. -/
def localTrivializations (hU : (⨆ i, U i) = ⊤) :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) (moduleSheaf X U g) where
  I := ι
  X := U
  coversTop := opens_coversTop X U hU
  iso i := _root_.SheafOfModules.freeUniqueIsoUnit
      (R := X.ringCatSheaf.over (U i)) PUnit ≪≫
    (chartIsoOn X U g hc i (le_refl (U i))).symm

include hc in
/-- The constructed glued module is locally free of rank one. -/
theorem moduleSheaf_isInvertible (hU : (⨆ i, U i) = ⊤) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (moduleSheaf X U g) :=
  KltDP.SheafOfModules.LocalTrivializations.isInvertible
    (R := X.ringCatSheaf) (M := moduleSheaf X U g) (localTrivializations X U g hc hU)

/-- The actual invertible sheaf determined by the covering unit cocycle. -/
def invertibleSheaf (hU : (⨆ i, U i) = ⊤) : InvertibleSheaf X :=
  InvertibleSheaf.ofLocalTrivializations (moduleSheaf X U g) (localTrivializations X U g hc hU)

end KltDP.Geometry.TransitionUnitGluing
