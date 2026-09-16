import KltDP.Geometry.AmpleNefUnconditional
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.InvertibleSheafTensor
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# Serre ampleness bounds every original restriction degree

Twisting any actual invertible sheaf by sufficiently high powers of an ample
sheaf makes the tensor globally generated. Its original restriction degree
is therefore nonnegative on every actual prime curve. Apply this to a
representative of the inverse Picard class to bound the degree of any
original invertible sheaf by a multiple of the ample degree.

In particular, if an ample sheaf had degree zero on a prime curve, every
invertible sheaf on the surface would have degree zero on that curve. This
is an unconditional intermediate; it does not assume a positive test class
or identify an arbitrary curve with a numerical vector.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AmpleSerreDegreeBound

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance degreeBoundMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

open InvertibleSheafTensor RationalTreePicard
open KltDP.AdmissionProbe.CurveTensorDegreeConsumers

/-- The actual tensor sheaf represents the product of the original Picard classes. -/
theorem tensorInvertibleSheaf_toPic {Y : Scheme.{u}} (L T : InvertibleSheaf Y) :
    (tensorInvertibleSheaf L T).toPic = L.toPic * T.toPic := by
  apply Units.ext
  change ((tensorInvertibleSheaf L T).toPic : Skeleton Y.Modules) =
    (L.toPic : Skeleton Y.Modules) * (T.toPic : Skeleton Y.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Skeleton.toSkeleton_tensorObj L.obj T.obj

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- One Serre bound works simultaneously for every original prime curve. -/
theorem eventually_twisted_restrictionDegree_nonneg (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) (T : InvertibleSheaf X.toScheme) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : X.PrimeCurve,
      0 ≤ (n : ℤ) * C.restrictionDegree L + C.restrictionDegree T := by
  letI := X.isLocallyNoetherian
  obtain ⟨N, hN⟩ := hL T.obj T.isCoherent
  refine ⟨N, fun n hn C => ?_⟩
  obtain ⟨M, hMclass, hMgg⟩ := hN n hn
  have hdeg : 0 ≤ C.restrictionDegree (tensorInvertibleSheaf M T) :=
    AmpleNefUnconditional.globallyGeneratedRestrictionNonneg X
      (tensorInvertibleSheaf M T) hMgg C
  rw [← C.picardRestrictionDegree_toPic (tensorInvertibleSheaf M T),
    tensorInvertibleSheaf_toPic, hMclass, picardRestrictionDegree_mul,
    AmplePositivity.picardRestrictionDegree_pow X C L.toPic n,
    C.picardRestrictionDegree_toPic, C.picardRestrictionDegree_toPic] at hdeg
  exact hdeg

/-- The inverse actual Picard class has the negative original restriction degree. -/
theorem inverseRepresentative_restrictionDegree (C : X.PrimeCurve)
    (T : InvertibleSheaf X.toScheme) :
    C.restrictionDegree (picardRepresentative T.toPic⁻¹) = -C.restrictionDegree T := by
  rw [← C.picardRestrictionDegree_toPic, picardRepresentative_toPic]
  simpa only [one_div, C.picardRestrictionDegree_one,
    C.picardRestrictionDegree_toPic, zero_sub] using
    X.picardRestrictionDegree_div C 1 T.toPic

/-- Every original invertible-sheaf degree is bounded by a sufficiently
high multiple of the ample degree, on all original prime curves at once. -/
theorem eventually_restrictionDegree_le (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) (T : InvertibleSheaf X.toScheme) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : X.PrimeCurve,
      C.restrictionDegree T ≤ (n : ℤ) * C.restrictionDegree L := by
  obtain ⟨N, hN⟩ := eventually_twisted_restrictionDegree_nonneg X L hL
    (picardRepresentative T.toPic⁻¹)
  refine ⟨N, fun n hn C => ?_⟩
  have h := hN n hn C
  rw [inverseRepresentative_restrictionDegree X C T, ← sub_eq_add_neg] at h
  exact sub_nonneg.mp h

/-- Degree zero for an ample sheaf on an original curve would force degree
zero for every actual invertible sheaf on that same curve. -/
theorem restrictionDegree_eq_zero_of_ample_degree_zero (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) (C : X.PrimeCurve)
    (hzero : C.restrictionDegree L = 0) (T : InvertibleSheaf X.toScheme) :
    C.restrictionDegree T = 0 := by
  obtain ⟨N, hN⟩ := eventually_restrictionDegree_le X L hL T
  have hle := hN N le_rfl C
  rw [hzero, mul_zero] at hle
  obtain ⟨N', hN'⟩ := eventually_twisted_restrictionDegree_nonneg X L hL T
  have hge := hN' N' le_rfl C
  rw [hzero, mul_zero, zero_add] at hge
  exact le_antisymm hle hge

/-- The same vanishing conclusion on the actual surface Picard group,
obtained using its proved sheaf representatives. -/
theorem picardRestrictionDegree_eq_zero_of_ample_degree_zero
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) (C : X.PrimeCurve)
    (hzero : C.restrictionDegree L = 0) (p : X.toScheme.Pic) :
    C.picardRestrictionDegree p = 0 := by
  have h := restrictionDegree_eq_zero_of_ample_degree_zero X L hL C hzero
    (picardRepresentative p)
  rwa [← C.picardRestrictionDegree_toPic, picardRepresentative_toPic] at h

end KltDP.Geometry.AmpleSerreDegreeBound
