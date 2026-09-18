import KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
import KltDP.Examples.FrobeniusBlowupChartIteration

/-! The original ordered plane coordinates preserve the actual origin ideal. -/

noncomputable section

namespace KltDP.Geometry.PlaneBlowupNativeDifferentialBasis

open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]

/-- The actual polynomial origin kernel is sent to the original two-generator
center ideal by the already constructed ordered coordinate equivalence. -/
theorem planeEquiv_map_originKernel :
    Ideal.map (planeEquiv k).toRingHom
        (RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 => (0 : k))).toRingHom) =
      centerIdeal := by
  let J := RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin 2 => (0 : k))).toRingHom
  have hJ : J.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)
  have hmap : (Ideal.map (planeEquiv k).toRingHom J).IsMaximal :=
    hJ.map_bijective (planeEquiv k).toRingHom (planeEquiv k).bijective
  apply (Ideal.IsMaximal.eq_of_le
    (KltDP.Examples.FrobeniusBlowupChartIteration.centerIdeal_isMaximal (k := k))
    hmap.ne_top ?_).symm
  apply Ideal.span_le.mpr
  intro z hz
  rcases hz with rfl | hz
  · rw [← planeEquiv_X_zero k]
    apply Ideal.mem_map_of_mem
    simp [J, RingHom.mem_ker]
  · rw [Set.mem_singleton_iff] at hz
    subst z
    rw [← planeEquiv_X_one k]
    apply Ideal.mem_map_of_mem
    simp [J, RingHom.mem_ker]

/-- Returning through the same coordinate equivalence recovers that literal
origin kernel, so extension along an actual coordinate map preserves centers. -/
theorem planeEquiv_symm_map_centerIdeal :
    Ideal.map (planeEquiv k).symm.toRingHom (centerIdeal (k := k)) =
      RingHom.ker (MvPolynomial.aeval (fun _ : Fin 2 => (0 : k))).toRingHom := by
  rw [← planeEquiv_map_originKernel k]
  exact Ideal.map_of_equiv (planeEquiv k).toRingEquiv

end KltDP.Geometry.PlaneBlowupNativeDifferentialBasis
