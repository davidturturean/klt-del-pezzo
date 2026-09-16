import KltDP.Geometry.PrimeCurveSubscheme
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Kernels are unchanged by a nonempty open in an integral source

The pin already proves injectivity of restriction maps between nonempty
opens of an integral scheme. Here this gives injectivity for the actual
open-immersion section map, including the empty-target-open case. The
existing ring-kernel composition theorem then identifies the actual
ideal-sheaf kernels before and after restriction. A separate result proves
that the kernel of a quasi-compact morphism from a reduced scheme is
radical, using reducedness of the actual rings of sections.

Newer official Mathlib's scheme-theoretic dominance framework subsumes
these consequences through its larger ideal-sheaf functoriality API.
This adapter uses the exact already pinned section and kernel results,
without porting that additional framework or assuming schematic density.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchematicImageDenseOpen

variable {X Y : Scheme.{u}}

/-- Restriction to a nonempty open of an integral scheme is injective
on every actual section ring, including sections over the empty open. -/
theorem openInclusion_app_injective [IsIntegral X] (U : X.Opens) [Nonempty U]
    (V : X.Opens) : Function.Injective (U.ι.app V) := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    have hUV : ((U.ι ''ᵁ U.ι ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := by
      change (U.ι.base '' (U.ι.base ⁻¹' (V : Set X))).Nonempty
      rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact nonempty_preirreducible_inter V.isOpen U.isOpen
        (by obtain ⟨x⟩ := hV; exact ⟨x.1, x.2⟩)
        (by obtain ⟨x⟩ := (inferInstance : Nonempty U); exact ⟨x.1, x.2⟩)
    letI : Nonempty (U.ι ''ᵁ U.ι ⁻¹ᵁ V : X.Opens) :=
      ⟨⟨hUV.choose, hUV.choose_spec⟩⟩
    rw [Scheme.Opens.ι_app]
    exact map_injective_of_isIntegral X _
  · have hbot : V = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    subst V
    letI : Subsingleton (X.sheaf.val.obj (Opposite.op ⊥)) :=
      CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    intro a b _
    exact Subsingleton.elim a b

/-- Removing a nonempty open complement in the integral source leaves
the actual kernel ideal sheaf unchanged. No quasi-compactness assumption
is required for this identity of the pinned `ofIdeals` constructions. -/
theorem ker_precompose_open [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f : X ⟶ Y) : (U.ι ≫ f).ker = f.ker := by
  unfold Scheme.Hom.ker
  apply congrArg Scheme.IdealSheafData.ofIdeals
  funext V
  rw [Scheme.comp_app, CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective (f.app V).hom
    (openInclusion_app_injective U (f ⁻¹ᵁ V))

/-- A quasi-compact morphism from an actual reduced scheme has a radical
kernel ideal sheaf: nilpotence can be tested in its actual section rings. -/
theorem ker_radical [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  apply Ideal.ext
  intro s
  rw [Ideal.mem_radical_iff, RingHom.mem_ker]
  constructor
  · rintro ⟨n, hn⟩
    have hz : IsNilpotent ((f.app V).hom s) := by
      refine ⟨n, ?_⟩
      simpa only [RingHom.mem_ker, map_pow] using hn
    exact hz.eq_zero
  · intro hs
    exact ⟨1, by simpa only [pow_one, RingHom.mem_ker] using hs⟩

/-- Consequently the existing quotient-glued closed image has its actual
reduced scheme structure, rather than an assumed reduced replacement. -/
theorem image_glued_isReduced [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] :
    IsReduced f.ker.glueData.glued :=
  f.ker.glued_isReduced (ker_radical f)

end KltDP.Geometry.SchematicImageDenseOpen
