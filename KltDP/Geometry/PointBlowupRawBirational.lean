import KltDP.Geometry.PointBlowupTargetIntegral
import KltDP.Geometry.SchemePointBlowupSequenceRestriction
import KltDP.Geometry.BirationalAdapters
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Birationality of the original raw point-blowup morphism

The original center's dimension excludes the generic point. The existing
unchanged-complement theorem supplies the original isomorphism there.
This applies before the target is packaged as a projective surface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- The original raw point-blowup map is birational once its target's
integrality is available from the preceding actual-object producer. -/
theorem IsAt.isBirationalScheme_of_center_dimension
    {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]
    {f : S ⟶ T} {z : T} (h : IsAt f z)
    (hdim : ringKrullDim (T.presheaf.stalk z) = 2) : IsBirationalScheme f := by
  have hz : z ≠ genericPoint T := by
    intro heq
    have hd : ringKrullDim T.functionField = 2 :=
      (congrArg (fun p : T => ringKrullDim (T.presheaf.stalk p)) heq).symm.trans hdim
    rw [ringKrullDim_eq_zero_of_field] at hd
    norm_num at hd
  let U : T.Opens := ⟨({z} : Set T)ᶜ, h.isClosed.isOpen_compl⟩
  letI : Nonempty U.toScheme := ⟨⟨genericPoint T, Ne.symm hz⟩⟩
  letI : IsIso (f ∣_ U) := h.isIso_restrict U (by simp [U])
  exact isBirationalScheme_of_isIso_restrict f U

end KltDP.Geometry.SchemePointBlowup

#print axioms KltDP.Geometry.SchemePointBlowup.IsAt.isBirationalScheme_of_center_dimension
