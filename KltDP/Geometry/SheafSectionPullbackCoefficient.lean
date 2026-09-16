import KltDP.Geometry.PrimeCurvePullbackFrameCore
import KltDP.Geometry.RationalTreePicardPulledFrameCoordinate
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Literal pulled sections and local frame coefficients

An arbitrary section is its actual frame coefficient times the frame generator.
The accepted generator comparison and semilinearity therefore identify its
coefficient after the original two pullbacks. If its first pullback is zero,
the original coefficient cannot have a unit germ at any point in the image.
The residue-field specialization applies to the literal adjunction-unit section.

This uses the accepted Over-to-open-subscheme frame comparison unchanged.
No flatness, coherence, integrality, chosen support, or Cartier data is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SheafSectionPullbackCoefficient

open RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

set_option maxHeartbeats 800000 in
/-- The coefficient of the literal double pullback is the original coefficient
through the two actual structural section maps. -/
theorem doublePulled_frame_coefficient (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : M.val.obj (op U)) :
    (pulledChartIso f M U (chartPullbackUnitIsoOf U M e.symm)).hom.val.app
        (op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) (doublePulled f U M s) =
      (f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ U)
        (f.app U (e.hom.val.app (op (Over.mk (𝟙 U))) s)) := by
  let a : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U))) s
  let σ : M.val.obj (op U) := e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))
  let Q : Y.Opens := f ⁻¹ᵁ U
  let τ := pulledChartIso f M U (chartPullbackUnitIsoOf U M e.symm)
  have ha : a • σ = s := by
    calc
      a • σ = e.inv.val.app (op (Over.mk (𝟙 U))) (a • (1 : Γ(X, U))) :=
        ((e.inv.val.app (op (Over.mk (𝟙 U)))).hom.map_smul a (1 : Γ(X, U))).symm
      _ = e.inv.val.app (op (Over.mk (𝟙 U))) a := by rw [smul_eq_mul, mul_one]
      _ = s := overModuleIso_inv_app_hom_app e (op (Over.mk (𝟙 U))) s
  have hσ₀ : (chartPullbackUnitIsoOf U M e.symm).hom.val.app
      (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U σ) = (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) :=
    chartPullbackUnitIsoOf_hom_app_pullbackSection U M e.symm σ rfl
  have hσ : τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M σ) =
      (1 : Γ(Q.toScheme, Q.ι ⁻¹ᵁ Q)) :=
    pulledChartIso_hom_val_app_doublePulled' f U M
      (chartPullbackUnitIsoOf U M e.symm) σ hσ₀
  have hlin : τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M (a • σ)) =
      Q.ι.app Q (f.app U a) •
        τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M σ) := by
    change τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q))
      (pulledSection Q.ι ((schemeModulePullback f).obj M) Q
        (pulledSection f M U (a • σ))) = _
    rw [pulledSection_smul, pulledSection_smul]
    exact (τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q))).hom.map_smul _ _
  change τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M s) = Q.ι.app Q (f.app U a)
  calc
    _ = τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M (a • σ)) :=
      congrArg (fun t => τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M t)) ha.symm
    _ = Q.ι.app Q (f.app U a) •
        τ.hom.val.app (op (Q.ι ⁻¹ᵁ Q)) (doublePulled f U M σ) := hlin
    _ = Q.ι.app Q (f.app U a) := by rw [hσ, smul_eq_mul, mul_one]

/-- A section with zero literal pullback has a nonunit original frame
coefficient at every actual image point in its domain. -/
theorem not_isUnit_germ_of_pulledSection_eq_zero (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : M.val.obj (op U)) (hs : pulledSection f M U s = 0)
    (z : Y) (hz : f.base z ∈ U) :
    ¬ IsUnit (X.presheaf.germ U (f.base z) hz
      (e.hom.val.app (op (Over.mk (𝟙 U))) s)) := by
  let a : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U))) s
  let Q : Y.Opens := f ⁻¹ᵁ U
  have hzQ : z ∈ Q := hz
  let w : Q.toScheme := ⟨z, hzQ⟩
  have hzero : Q.ι.app Q (f.app U a) = 0 := by
    have h := doublePulled_frame_coefficient f M U e s
    have hp : doublePulled f U M s = 0 := by
      change pulledSection Q.ι ((schemeModulePullback f).obj M) Q
        (pulledSection f M U s) = 0
      rw [hs]
      exact map_zero (((schemeModulePullbackPushforwardAdjunction Q.ι).unit.app
        ((schemeModulePullback f).obj M)).val.app (op Q)).hom
    rw [hp, map_zero] at h
    exact h.symm
  intro hu
  have hmem : f.base z ∈ X.basicOpen a := (X.mem_basicOpen a (f.base z) hz).2 hu
  have hpre : w ∈ Q.ι ⁻¹ᵁ (f ⁻¹ᵁ X.basicOpen a) := hmem
  rw [Scheme.preimage_basicOpen, Scheme.preimage_basicOpen, hzero,
    Scheme.basicOpen_zero] at hpre
  exact hpre

/-- The same coefficient obstruction for the restriction of an original global
section; the zero local pullback follows from the actual restriction map. -/
theorem not_isUnit_germ_of_global_pulledSection_eq_zero (f : Y ⟶ X) (M : X.Modules)
    (s : M.val.obj (op (⊤ : X.Opens))) (hs : pulledSection f M ⊤ s = 0)
    (U : X.Opens) (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (z : Y) (hz : f.base z ∈ U) :
    ¬ IsUnit (X.presheaf.germ U (f.base z) hz
      (e.hom.val.app (op (Over.mk (𝟙 U)))
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s))) := by
  apply not_isUnit_germ_of_pulledSection_eq_zero f M U e _ _ z hz
  have h := pulledSection_res f M (le_top : U ≤ ⊤) s
  rw [hs, map_zero] at h
  exact h.symm

/-- Literal vanishing after pullback to the original residue-field point forces
a nonunit coefficient germ in every original local frame at that point. -/
theorem not_isUnit_germ_of_residue_pullback_eq_zero (M : X.Modules)
    (s : M.val.obj (op (⊤ : X.Opens))) (x : X)
    (hs : pulledSection (X.fromSpecResidueField x) M ⊤ s = 0)
    (U : X.Opens) (hx : x ∈ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ¬ IsUnit (X.presheaf.germ U x hx
      (e.hom.val.app (op (Over.mk (𝟙 U)))
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s))) := by
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hz : (X.fromSpecResidueField x).base z ∈ U := by
    simpa only [Scheme.fromSpecResidueField_apply] using hx
  have h := not_isUnit_germ_of_global_pulledSection_eq_zero
    (X.fromSpecResidueField x) M s hs U e z hz
  intro hu
  apply h
  let a : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U)))
    (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)
  apply (X.mem_basicOpen a ((X.fromSpecResidueField x).base z) hz).1
  have hm : x ∈ X.basicOpen a := (X.mem_basicOpen a x hx).2 hu
  simpa only [Scheme.fromSpecResidueField_apply] using hm

end KltDP.Geometry.SheafSectionPullbackCoefficient
