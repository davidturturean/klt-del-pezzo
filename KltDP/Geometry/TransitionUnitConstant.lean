import KltDP.Geometry.TransitionUnitLocalTriviality
import KltDP.Compatibility.SheafIsoOnBasis

/-!
# Gluing the identity transition cocycle

Restricting an original structure-sheaf section to each chart gives a
matching family for the identity cocycle. This actual linear map commutes
with restrictions and is bijective on every chart subopen. The existing
basis criterion constructs the global unit-sheaf isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- The actual identity unit on every original double overlap. -/
def oneUnits (i j : ι) : Γ(X, U i ⊓ U j)ˣ := 1

/-- Identity transitions satisfy the original normalization and cocycle equations. -/
theorem oneUnits_isCocycle : IsCocycle X U (oneUnits X U) where
  unit_self _ := rfl
  mul_res _ _ _ := by simp only [oneUnits, Units.val_one, map_one, one_mul]

local instance oneCoordinateAdditiveModule (W : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.val.obj W) ((additivePresheaf X U (oneUnits X U)).obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (sections X U (oneUnits X U) W.unop))

/-- Original structure-sheaf restriction gives an actual matching family. -/
def oneCoordinateMap (W : X.Opens) : Γ(X, W) →ₗ[Γ(X, W)] sections X U (oneUnits X U) W where
  toFun s := ⟨fun i => res X (inf_le_left : W ⊓ U i ≤ W) s, by
    intro i j
    change res X _ (res X _ s) = res X _ (1 : Γ(X, U i ⊓ U j)) * res X _ (res X _ s)
    simp only [map_one, one_mul, res_res]⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact map_add _ s t
  map_smul' r s := by
    apply Subtype.ext
    funext i
    exact map_mul (res X (inf_le_left : W ⊓ U i ≤ W)) r s

/-- The actual one-cocycle chart coordinates recover the original section. -/
theorem trivialization_oneCoordinateMap (i : ι) {W : X.Opens} (hWi : W ≤ U i)
    (s : Γ(X, W)) :
    trivialization X U (oneUnits X U) (oneUnits_isCocycle X U) i hWi
      (oneCoordinateMap X U W s) = s := by
  change res X (le_inf le_rfl hWi) (res X (inf_le_left : W ⊓ U i ≤ W) s) = s
  rw [res_res, res_self]

/-- The restriction map to identity matching coordinates is bijective on chart subopens. -/
theorem oneCoordinateMap_bijective_on_chart (i : ι) {W : X.Opens} (hWi : W ≤ U i) :
    Function.Bijective (oneCoordinateMap X U W) := by
  let e := trivialization X U (oneUnits X U) (oneUnits_isCocycle X U) i hWi
  have he : (oneCoordinateMap X U W : Γ(X, W) → sections X U (oneUnits X U) W) = e.symm := by
    funext s
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact trivialization_oneCoordinateMap X U i hWi s
  rw [he]
  exact e.symm.bijective

/-- The actual unit-sheaf morphism given by original chart restrictions. -/
def oneCoordinateMorphism :
    _root_.SheafOfModules.unit X.ringCatSheaf ⟶ moduleSheaf X U (oneUnits X U) where
  val := {
    app W := ModuleCat.ofHom (oneCoordinateMap X U W.unop)
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      funext i
      change res X _ (res X _ s) = res X _ (res X _ s)
      simp only [res_res] }

/-- Covering identity transitions recover the original unit sheaf. -/
theorem oneCoordinateMorphism_isIso (hU : (⨆ i, U i) = ⊤) :
    IsIso (oneCoordinateMorphism X U) := by
  let B : ι × X.Opens → X.Opens := fun p => p.2 ⊓ U p.1
  have hB : Opens.IsBasis (Set.range B) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro W x hx
    have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
    exact ⟨W ⊓ U i, ⟨(i, W), rfl⟩, ⟨hx, hi⟩, inf_le_left⟩
  exact KltDP.SheafOfModules.isIso_of_bijective_on_basis (B := B)
    (oneCoordinateMorphism X U) hB
    (fun p => oneCoordinateMap_bijective_on_chart X U p.1 inf_le_right)

/-- The constructed identity-cocycle gluing isomorphism has the original unit as its source. -/
def unitIsoOne (hU : (⨆ i, U i) = ⊤) :
    _root_.SheafOfModules.unit X.ringCatSheaf ≅ moduleSheaf X U (oneUnits X U) := by
  letI := oneCoordinateMorphism_isIso X U hU
  exact asIso (oneCoordinateMorphism X U)

end KltDP.Geometry.TransitionUnitGluing
