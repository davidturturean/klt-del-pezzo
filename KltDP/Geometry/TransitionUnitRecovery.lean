import KltDP.Geometry.TransitionUnitExtraction
import KltDP.Compatibility.SheafIsoOnBasis

/-!
# Recovering an actual module sheaf from its transition units

The map to matching coordinates evaluates the original local
trivializations on restricted sections. On each chart subopen it is
bijective, as comparison with the two chart equivalences shows. The
existing basis criterion then gives an actual isomorphism in X.Modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitExtraction

open TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- Restriction composition for the original sections, using the additive presheaf. -/
private theorem moduleMap_comp {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    (s : M.val.obj (op Z)) :
    M.val.map (homOfLE hVW).op (M.val.map (homOfLE hWZ).op s) =
      M.val.map (homOfLE (hVW.trans hWZ)).op s := by
  have h := CategoryTheory.congr_fun
    (M.val.presheaf.map_comp (homOfLE hWZ).op (homOfLE hVW).op) s
  exact h.symm

/-- Identity restriction for original module sections. -/
private theorem moduleMap_self (W : X.Opens) (s : M.val.obj (op W)) :
    M.val.map (homOfLE (le_refl W)).op s = s := by
  have h := CategoryTheory.congr_fun (M.val.presheaf.map_id (op W)) s
  exact h

/-- Evaluate a restricted chart using the single original composite restriction. -/
private theorem chartEquiv_restrict_twice (i : t.I) {V W Z : X.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) (hWi : W ≤ t.X i)
    (s : M.val.obj (op Z)) :
    res X hVW (chartEquiv X M t i hWi (M.val.map (homOfLE hWZ).op s)) =
      chartEquiv X M t i (hVW.trans hWi)
        (M.val.map (homOfLE (hVW.trans hWZ)).op s) := by
  have hchart := chartEquiv_restrict X M t i hVW hWi
    (M.val.map (homOfLE hWZ).op s)
  have hsections := moduleMap_comp X M hVW hWZ s
  exact hchart.symm.trans
    (congrArg (fun a : M.val.obj (op V) =>
      chartEquiv X M t i (hVW.trans hWi) a) hsections)

/-- Local coordinates of one original section satisfy the extracted matching equations. -/
theorem coordinates_mem (W : X.Opens) (s : M.val.obj (op W)) :
    (fun i => chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : W ⊓ t.X i ≤ W)).op s)) ∈
        sections X t.X (transitionUnits X M t) W := by
  intro i j
  let V : X.Opens := W ⊓ t.X i ⊓ t.X j
  have hVi : V ≤ t.X i := inf_le_left.trans inf_le_right
  have hVj : V ≤ t.X j := inf_le_right
  have hVW : V ≤ W := inf_le_left.trans inf_le_left
  let sV : M.val.obj (op V) := M.val.map (homOfLE hVW).op s
  let c : Γ(X, V) := res X (inclCoc X t.X W i j) (transitionUnits X M t i j)
  have hi : res X (inf_le_left : V ≤ W ⊓ t.X i)
      (chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)
        (M.val.map (homOfLE (inf_le_left : W ⊓ t.X i ≤ W)).op s)) =
      chartEquiv X M t i hVi sV :=
    chartEquiv_restrict_twice X M t i (V := V) (W := W ⊓ t.X i) (Z := W)
      inf_le_left inf_le_left inf_le_right s
  have hj : res X (inclSnd X t.X W i j)
      (chartEquiv X M t j (inf_le_right : W ⊓ t.X j ≤ t.X j)
        (M.val.map (homOfLE (inf_le_left : W ⊓ t.X j ≤ W)).op s)) =
      chartEquiv X M t j hVj sV :=
    chartEquiv_restrict_twice X M t j (V := V) (W := W ⊓ t.X j) (Z := W)
      (inclSnd X t.X W i j)
      inf_le_left inf_le_right s
  have htransition : c * chartEquiv X M t j hVj sV =
      chartEquiv X M t i hVi sV :=
    transitionUnits_mul_chart X M t i j hVi hVj sV
  exact hi.trans (htransition.symm.trans
    (congrArg (fun a : Γ(X, V) => c * a) hj.symm))

/-- The actual O(W)-linear map from sections to their matching coordinates. -/
def coordinateMap (W : X.Opens) :
    M.val.obj (op W) →ₗ[Γ(X, W)] sections X t.X (transitionUnits X M t) W where
  toFun s := ⟨fun i => chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)
      (M.val.map (homOfLE (inf_le_left : W ⊓ t.X i ≤ W)).op s),
    coordinates_mem X M t W s⟩
  map_add' s q := by
    apply Subtype.ext
    funext i
    let V : X.Opens := W ⊓ t.X i
    have hVW : V ≤ W := inf_le_left
    let e : M.val.obj (op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
      chartEquiv X M t i (inf_le_right : V ≤ t.X i)
    have hsections : M.val.map (homOfLE hVW).op (s + q) =
        M.val.map (homOfLE hVW).op s + M.val.map (homOfLE hVW).op q :=
      (M.val.presheaf.map (homOfLE hVW).op).hom.map_add s q
    exact (congrArg (fun a : M.val.obj (op V) => e a) hsections).trans
      (e.map_add (M.val.map (homOfLE hVW).op s) (M.val.map (homOfLE hVW).op q))
  map_smul' r s := by
    apply Subtype.ext
    funext i
    let V : X.Opens := W ⊓ t.X i
    have hVW : V ≤ W := inf_le_left
    let e : M.val.obj (op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
      chartEquiv X M t i (inf_le_right : V ≤ t.X i)
    have hsections : M.val.map (homOfLE hVW).op (r • s) =
        (res X hVW r) • M.val.map (homOfLE hVW).op s :=
      M.val.map_smul (homOfLE hVW).op r s
    have hlinear : e ((res X hVW r) • M.val.map (homOfLE hVW).op s) =
        (res X hVW r) • e (M.val.map (homOfLE hVW).op s) :=
      e.map_smul (res X hVW r) (M.val.map (homOfLE hVW).op s)
    exact (congrArg (fun a : M.val.obj (op V) => e a) hsections).trans
      (hlinear.trans (smul_eq_mul (res X hVW r) (e (M.val.map (homOfLE hVW).op s))))

@[simp]
theorem coordinateMap_val (W : X.Opens) (s : M.val.obj (op W)) (i : t.I) :
    (coordinateMap X M t W s).val i =
      chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)
        (M.val.map (homOfLE (inf_le_left : W ⊓ t.X i ≤ W)).op s) := rfl

/-- Coordinate maps commute with the original restriction maps. -/
theorem coordinateMap_restrict {V W : X.Opens} (hVW : V ≤ W)
    (s : M.val.obj (op W)) :
    coordinateMap X M t V (M.val.map (homOfLE hVW).op s) =
      restrict X t.X (transitionUnits X M t) hVW (coordinateMap X M t W s) := by
  apply Subtype.ext
  funext i
  have hVi : V ⊓ t.X i ≤ t.X i := inf_le_right
  have hleft := congrArg
    (fun a : M.val.obj (op (V ⊓ t.X i)) => chartEquiv X M t i hVi a)
    (moduleMap_comp X M (inf_le_left : V ⊓ t.X i ≤ V) hVW s)
  have hright := chartEquiv_restrict_twice X M t i
    (V := V ⊓ t.X i) (W := W ⊓ t.X i) (Z := W)
    (inf_le_inf_right (t.X i) hVW) (inf_le_left : W ⊓ t.X i ≤ W)
    (inf_le_right : W ⊓ t.X i ≤ t.X i) s
  exact hleft.trans hright.symm

local instance coordinateAdditiveModule (W : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.val.obj W)
      ((additivePresheaf X t.X (transitionUnits X M t)).obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (sections X t.X (transitionUnits X M t) W.unop))

/-- The actual module-sheaf morphism taking original sections to matching coordinates. -/
def coordinateMorphism : M ⟶ moduleSheaf X t.X (transitionUnits X M t) where
  val := {
    app W := ModuleCat.ofHom (coordinateMap X M t W.unop)
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact coordinateMap_restrict X M t f.unop.le s }

/-- Reading one target chart after the coordinate map recovers the original chart map. -/
theorem trivialization_coordinateMap (i : t.I) {W : X.Opens} (hWi : W ≤ t.X i)
    (s : M.val.obj (op W)) :
    trivialization X t.X (transitionUnits X M t) (transitionUnits_isCocycle X M t)
        i hWi (coordinateMap X M t W s) = chartEquiv X M t i hWi s := by
  have hW : W ≤ W ⊓ t.X i := le_inf le_rfl hWi
  have hchart := chartEquiv_restrict_twice X M t i (V := W) (W := W ⊓ t.X i) (Z := W) hW
    (inf_le_left : W ⊓ t.X i ≤ W) (inf_le_right : W ⊓ t.X i ≤ t.X i) s
  exact hchart.trans
    (congrArg (fun a : M.val.obj (op W) => chartEquiv X M t i hWi a)
      (moduleMap_self X M W s))

/-- On an actual chart subopen the coordinate map is bijective. -/
theorem coordinateMap_bijective_on_chart (i : t.I) {W : X.Opens} (hWi : W ≤ t.X i) :
    Function.Bijective (coordinateMap X M t W) := by
  let e : sections X t.X (transitionUnits X M t) W ≃ₗ[Γ(X, W)] Γ(X, W) :=
    trivialization X t.X (transitionUnits X M t)
    (transitionUnits_isCocycle X M t) i hWi
  constructor
  · intro s q h
    apply (chartEquiv X M t i hWi).injective
    exact (trivialization_coordinateMap X M t i hWi s).symm.trans
      ((congrArg (fun a : sections X t.X (transitionUnits X M t) W => e a) h).trans
        (trivialization_coordinateMap X M t i hWi q))
  · intro s
    refine ⟨(chartEquiv X M t i hWi).symm (e s), ?_⟩
    apply e.injective
    exact (trivialization_coordinateMap X M t i hWi
      ((chartEquiv X M t i hWi).symm (e s))).trans
      ((chartEquiv X M t i hWi).apply_symm_apply (e s))

/-- Intersections with the actual trivializing opens form a basis. -/
def chartBasis (p : t.I × X.Opens) : X.Opens := p.2 ⊓ t.X p.1

theorem chartBasis_isBasis : Opens.IsBasis (Set.range (chartBasis X M t)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro W x hx
  have hxU : x ∈ ⨆ i, t.X i := by rw [chartOpens_cover X M t]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  exact ⟨W ⊓ t.X i, ⟨(i, W), rfl⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- The existing basis criterion proves the actual coordinate morphism is an isomorphism. -/
theorem coordinateMorphism_isIso : IsIso (coordinateMorphism X M t) :=
  KltDP.SheafOfModules.isIso_of_bijective_on_basis (B := chartBasis X M t)
    (coordinateMorphism X M t) (chartBasis_isBasis X M t)
    (fun p => coordinateMap_bijective_on_chart X M t p.1
      (inf_le_right : p.2 ⊓ t.X p.1 ≤ t.X p.1))

/-- The original module sheaf is isomorphic to the sheaf glued from its extracted units. -/
def recoveryIso : M ≅ moduleSheaf X t.X (transitionUnits X M t) := by
  letI := coordinateMorphism_isIso X M t
  exact asIso (coordinateMorphism X M t)

@[simp]
theorem recoveryIso_hom_app_val (W : X.Opensᵒᵖ) (s : M.val.obj W) (i : t.I) :
    ((recoveryIso X M t).hom.val.app W s).val i =
      chartEquiv X M t i (inf_le_right : W.unop ⊓ t.X i ≤ t.X i)
        (M.val.map (homOfLE (inf_le_left : W.unop ⊓ t.X i ≤ W.unop)).op s) := rfl

/-- The actual inverse recovers every original inverse-chart restriction. -/
theorem recoveryIso_inv_app_restrict (W : X.Opens)
    (s : sections X t.X (transitionUnits X M t) W) (i : t.I) :
    M.val.map (homOfLE (inf_le_left : W ⊓ t.X i ≤ W)).op
        ((recoveryIso X M t).inv.val.app (op W) s) =
      (chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)).symm (s.val i) := by
  have hsections : (recoveryIso X M t).hom.val.app (op W)
      ((recoveryIso X M t).inv.val.app (op W) s) = s := by
    exact congrArg
      (fun f : moduleSheaf X t.X (transitionUnits X M t) ⟶
          moduleSheaf X t.X (transitionUnits X M t) => f.val.app (op W) s)
      (recoveryIso X M t).inv_hom_id
  have hcoordinate := congrArg
    (fun a : sections X t.X (transitionUnits X M t) W => a.val i) hsections
  have hchart := (recoveryIso_hom_app_val X M t (op W)
    ((recoveryIso X M t).inv.val.app (op W) s) i).symm.trans hcoordinate
  exact (chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)).injective
    (hchart.trans
      ((chartEquiv X M t i (inf_le_right : W ⊓ t.X i ≤ t.X i)).apply_symm_apply
        (s.val i)).symm)

/-- An arbitrary actual invertible sheaf is recovered from its extracted cocycle. -/
def invertibleSheafRecoveryIso (L : InvertibleSheaf X) :
    L.obj ≅ moduleSheaf X L.localTrivializations.X (invertibleSheafUnits X L) :=
  recoveryIso X L.obj L.localTrivializations

end KltDP.Geometry.TransitionUnitExtraction
