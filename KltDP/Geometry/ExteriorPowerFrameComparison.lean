import KltDP.Geometry.SchemeExteriorPower
import KltDP.Geometry.ChartFrameAtlasSheaf
import KltDP.Compatibility.SheafificationOnCover

/-!
# Comparing the actual exterior sheaf with a determinant-frame line

For an actual module sheaf with compatible rank-`n` frames on a covering,
determinant coordinates define a map from its independent exterior presheaf
to the existing transition-glued line. On every subopen of a frame chart,
this map is the ordinary determinant equivalence. Sheafification therefore
gives an isomorphism with the existing glued invertible sheaf.

The frames are used only to construct the comparison and prove local
bijectivity. They do not occur in `SchemeExteriorPower.sheaf`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.AffineTopDifferentialFrame
open KltDP.Geometry.ChartFrameAtlasSheaf
open KltDP.Geometry.TransitionUnitGluing

universe u

namespace KltDP.Geometry.ExteriorPowerFrameComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Determinants

variable {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}
  {P Q : Type u} [AddCommGroup P] [AddCommGroup Q] [Module A P] [Module B Q]
  {n : ℕ}

/-- Determinant naturality for an arbitrary vector family, under a semilinear
map carrying the chosen basis to the chosen basis. -/
theorem det_restrict_vectors (b : Basis (Fin n) A P) (c : Basis (Fin n) B Q)
    (f : P →ₛₗ[φ] Q) (hb : ∀ t, f (b t) = c t) (v : Fin n → P) :
    c.det (fun t => f (v t)) = φ (b.det v) := by
  have h : c.toMatrix (fun t => f (v t)) = φ.mapMatrix (b.toMatrix v) := by
    ext s t
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply]
    exact FrameRestrictionDeterminant.repr_restrict b c f hb (v t) s
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det, h]

/-- Change of basis for the determinant of any vector family. -/
theorem det_change_vectors (b c : Basis (Fin n) A P) (v : Fin n → P) :
    b.det v = b.det c * c.det v := by
  have h := congrArg (fun F : P [⋀^Fin n]→ₗ[A] A => F v)
    ((b.det).eq_smul_basis_det c)
  simpa only [AlternatingMap.smul_apply, smul_eq_mul] using h

end Determinants

variable {X : Scheme.{u}} (M : X.Modules)

local instance sectionCommRing (V : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

/-- The original sections of the module sheaf. -/
abbrev moduleSections (W : X.Opens) : Type u := M.val.obj (op W)

/-- The original module restriction, as a semilinear map over `O(W) → O(V)`. -/
def moduleRestr {V W : X.Opens} (h : V ≤ W) :
    moduleSections M W →ₛₗ[res X h] moduleSections M V where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := _root_.PresheafOfModules.map_smul M.val (homOfLE h).op r x

@[simp]
theorem moduleRestr_self (W : X.Opens) (x : moduleSections M W) :
    moduleRestr M (le_refl W) x = x := by
  change M.val.presheaf.map (𝟙 (op W)) x = x
  rw [M.val.presheaf.map_id]
  rfl

theorem moduleRestr_comp {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    (x : moduleSections M Z) :
    moduleRestr M hVW (moduleRestr M hWZ x) = moduleRestr M (hVW.trans hWZ) x := by
  exact (CategoryTheory.congr_fun
    (M.val.presheaf.map_comp (homOfLE hWZ).op (homOfLE hVW).op) x).symm

variable {ι : Type u} (U : ι → X.Opens) {n : ℕ}
  (frame : ∀ (i : ι) (W : X.Opens), W ≤ U i →
    Basis (Fin n) Γ(X, W) (moduleSections M W))
  (hframe : ∀ (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hW : W ≤ U i) (t : Fin n),
    moduleRestr M hVW (frame i W hW t) = frame i V (hVW.trans hW) t)

/-- Coordinates after actual restriction, packaged as an alternating map over
the original source section ring. -/
def coordinates (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hVi : V ≤ U i) :
    (M.val.obj (op W)).AlternatingMap
      ((ModuleCat.restrictScalars (res X hVW)).obj (ModuleCat.of Γ(X, V) Γ(X, V))) n :=
  ModuleCat.exteriorPower.mk.postcomp
    ((SchemeExteriorPower.presheaf M n).map (homOfLE hVW).op ≫
      (ModuleCat.restrictScalars (res X hVW)).map
        (determinantEquiv (frame i V hVi)).toModuleIso.hom)

@[simp]
theorem coordinates_apply (i : ι) {V W : X.Opens} (hVW : V ≤ W) (hVi : V ≤ U i)
    (v : Fin n → moduleSections M W) :
    coordinates M U frame i hVW hVi v =
      (frame i V hVi).det (fun t => moduleRestr M hVW (v t)) := by
  change determinantEquiv (frame i V hVi)
      ((SchemeExteriorPower.presheaf M n).map (homOfLE hVW).op
        (exteriorPower.ιMulti Γ(X, W) n v)) = _
  exact (congrArg (determinantEquiv (frame i V hVi))
    (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf_map_mk
      X.presheaf M.val n (homOfLE hVW).op v)).trans
        (determinantEquiv_apply_wedge (frame i V hVi)
          (fun t => moduleRestr M hVW (v t)))

include hframe in
/-- Coordinates commute with the original restriction maps. -/
theorem coordinates_restrict (i : ι) {T V W : X.Opens}
    (hTV : T ≤ V) (hVW : V ≤ W) (hVi : V ≤ U i)
    (v : Fin n → moduleSections M W) :
    res X hTV (coordinates M U frame i hVW hVi v) =
      coordinates M U frame i (hTV.trans hVW) (hTV.trans hVi) v := by
  rw [coordinates_apply, coordinates_apply]
  have h := det_restrict_vectors (frame i V hVi) (frame i T (hTV.trans hVi))
    (moduleRestr M hTV) (hframe i hTV hVi)
    (fun t => moduleRestr M hVW (v t))
  simpa only [moduleRestr_comp] using h.symm

include hframe in
/-- Determinant coordinates satisfy the existing matching-family condition. -/
theorem coordinates_matching (W : X.Opens) (v : Fin n → moduleSections M W)
    (i j : ι) :
    res X (inf_le_left : W ⊓ U i ⊓ U j ≤ W ⊓ U i)
        (coordinates M U frame i inf_le_left inf_le_right v) =
      res X (inclCoc X U W i j) (transitionUnit U (moduleSections M) frame i j) *
        res X (inclSnd X U W i j)
          (coordinates M U frame j inf_le_left inf_le_right v) := by
  rw [coordinates_restrict M U frame hframe,
    coordinates_restrict M U frame hframe]
  have hg := chartUnitOn_restrict (U := U) (L := moduleSections M)
    (restr := moduleRestr M) (frame := frame) (hframe := hframe)
    (inclCoc X U W i j) i j inf_le_left inf_le_right
  rw [transitionUnit_eq, ← hg]
  simp only [coordinates_apply, chartUnitOn_val]
  exact det_change_vectors _ _ _

/-- The wedge of a family of actual module sections, expressed in every chart
as matching determinant coordinates. -/
def matchingAlternating (W : X.Opens) :
    (M.val.obj (op W)).AlternatingMap
      ((moduleSheaf X U (transitionUnit U (moduleSections M) frame)).val.obj (op W)) n where
  toFun v := ⟨fun i => coordinates M U frame i inf_le_left inf_le_right v,
    coordinates_matching M U frame hframe W v⟩
  map_update_add' v t x y := by
    apply Subtype.ext
    funext i
    exact (coordinates M U frame i (inf_le_left : W ⊓ U i ≤ W) inf_le_right).map_update_add
      v t x y
  map_update_smul' v t r x := by
    apply Subtype.ext
    funext i
    exact (coordinates M U frame i (inf_le_left : W ⊓ U i ≤ W) inf_le_right).map_update_smul
      v t r x
  map_eq_zero_of_eq' v t s h hts := by
    apply Subtype.ext
    funext i
    exact (coordinates M U frame i (inf_le_left : W ⊓ U i ≤ W) inf_le_right).map_eq_zero_of_eq v h hts

/-- The presheaf comparison into the existing transition-glued sheaf. -/
def toFramePresheaf :
    SchemeExteriorPower.presheaf M n ⟶
      (moduleSheaf X U (transitionUnit U (moduleSections M) frame)).val where
  app W := ModuleCat.exteriorPower.desc (matchingAlternating M U frame hframe W.unop)
  naturality {V W} f := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change ModuleCat.exteriorPower.desc (matchingAlternating M U frame hframe W.unop)
        ((SchemeExteriorPower.presheaf M n).map f (ModuleCat.exteriorPower.mk v)) =
      (moduleSheaf X U (transitionUnit U (moduleSections M) frame)).val.map f
        (ModuleCat.exteriorPower.desc (matchingAlternating M U frame hframe V.unop)
          (ModuleCat.exteriorPower.mk v))
    have hres : (SchemeExteriorPower.presheaf M n).map f
        (ModuleCat.exteriorPower.mk (M := M.val.obj V) v) =
      ModuleCat.exteriorPower.mk (M := M.val.obj W) (fun t => M.val.map f (v t)) :=
      KltDP.Compatibility.ExteriorPowerPresheaf.presheaf_map_mk X.presheaf M.val n f v
    rw [hres, ModuleCat.exteriorPower.desc_mk, ModuleCat.exteriorPower.desc_mk]
    apply Subtype.ext
    funext i
    change coordinates M U frame i (inf_le_left : W.unop ⊓ U i ≤ W.unop)
        inf_le_right (fun t => moduleRestr M f.unop.le (v t)) =
      res X (inf_le_inf_right (U i) f.unop.le)
        (coordinates M U frame i (inf_le_left : V.unop ⊓ U i ≤ V.unop) inf_le_right v)
    rw [coordinates_restrict M U frame hframe]
    simp only [coordinates_apply, moduleRestr_comp]

/-- On every subopen of a chart the comparison is the ordinary determinant
equivalence, after the existing trivialization of the glued line. -/
theorem trivialization_toFrame (j : ι) {W : X.Opens} (hW : W ≤ U j)
    (q : (SchemeExteriorPower.presheaf M n).obj (op W)) :
    trivialization X U (transitionUnit U (moduleSections M) frame)
        (transitionUnit_isCocycle (U := U) (L := moduleSections M)
          (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW
        ((toFramePresheaf M U frame hframe).app (op W) q) =
      determinantEquiv (frame j W hW) q := by
  have heq : (toFramePresheaf M U frame hframe).app (op W) ≫
      (trivialization X U (transitionUnit U (moduleSections M) frame)
        (transitionUnit_isCocycle (U := U) (L := moduleSections M)
          (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW).toModuleIso.hom =
      (determinantEquiv (frame j W hW)).toModuleIso.hom := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change trivialization X U (transitionUnit U (moduleSections M) frame)
        (transitionUnit_isCocycle (U := U) (L := moduleSections M)
          (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW
        (ModuleCat.exteriorPower.desc (matchingAlternating M U frame hframe W)
          (ModuleCat.exteriorPower.mk v)) =
      determinantEquiv (frame j W hW) (exteriorPower.ιMulti Γ(X, W) n v)
    rw [ModuleCat.exteriorPower.desc_mk, determinantEquiv_apply_wedge,
      trivialization_apply]
    change res X (le_inf le_rfl hW)
      (coordinates M U frame j (inf_le_left : W ⊓ U j ≤ W) inf_le_right v) = _
    rw [coordinates_restrict M U frame hframe, coordinates_apply]
    simp only [moduleRestr_self]
  exact CategoryTheory.congr_fun heq q

/-- The actual presheaf comparison is bijective on every subopen of a chart. -/
theorem toFramePresheaf_bijective (j : ι) {W : X.Opens} (hW : W ≤ U j) :
    Function.Bijective ((toFramePresheaf M U frame hframe).app (op W)) := by
  let e := trivialization X U (transitionUnit U (moduleSections M) frame)
    (transitionUnit_isCocycle (U := U) (L := moduleSections M)
      (restr := moduleRestr M) (frame := frame) (hframe := hframe)) j hW
  constructor
  · intro q r h
    apply (determinantEquiv (frame j W hW)).injective
    rw [← trivialization_toFrame M U frame hframe j hW q,
      ← trivialization_toFrame M U frame hframe j hW r, h]
  · intro s
    refine ⟨(determinantEquiv (frame j W hW)).symm (e s), ?_⟩
    apply e.injective
    rw [trivialization_toFrame M U frame hframe j hW,
      LinearEquiv.apply_symm_apply]

/-- The independently defined exterior-power sheaf is isomorphic to the
existing determinant-frame line on the original scheme. -/
def sheafIso (hU : (⨆ i, U i) = ⊤) :
    SchemeExteriorPower.sheaf M n ≅
      (sheafOfFrames U (moduleSections M) (moduleRestr M) frame hframe hU).obj := by
  let g := toFramePresheaf M U frame hframe
  have hg : _root_.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.val) g :=
    _root_.PresheafOfModules.sheafificationW_of_bijective_on_coversTop g U
      (opens_coversTop X U hU)
      (fun i V a => toFramePresheaf_bijective M U frame hframe i a.le)
  letI : IsIso ((_root_.PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.val)).map g) := hg
  exact asIso ((_root_.PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.val)).map g) ≪≫
    _root_.PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
      (moduleSheaf X U (transitionUnit U (moduleSections M) frame))

end KltDP.Geometry.ExteriorPowerFrameComparison
