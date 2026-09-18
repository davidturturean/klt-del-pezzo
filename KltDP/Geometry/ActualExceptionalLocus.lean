import KltDP.Geometry.ActualResolutionExceptionalCount
import KltDP.Geometry.ProperBirationalOffContractedSupport
import KltDP.Geometry.ExceptionalCurveFieldPointFactor
import KltDP.Geometry.ExceptionalCurveOfFieldPointFactor
import KltDP.Geometry.TargetIsomorphismOpen

/-!
# The actual exceptional locus and its original contracted prime curves

For a proper birational map with connected point fibers, the union of all
contracted prime curves contains the entire fiber over every one of its
image points. This rules out silently discarding isolated fiber points.

If the original structure-sheaf pushforward map is an isomorphism, the
existing proper-map inverse theorem identifies this union with the actual
non-isomorphism locus, and its finite image with the target bad set.
Connected fibers and the pushforward isomorphism are conditions on the
original morphism. No exceptional-component partition or image bijection is
assumed. Identification with the singular locus needs minimality and is not
asserted here. No Stein literature axiom is imported to supply connectedness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ActualExceptionalLocus

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- The union of the original prime curves that the original map contracts. -/
def primeSupport : Set S.toScheme :=
  ⋃ C : S.PrimeCurve, ⋃ (_ : IsExceptionalCurve π C), (C : Set S.toScheme)

@[simp] theorem mem_primeSupport (x : S.toScheme) :
    x ∈ primeSupport π ↔ ∃ C : S.PrimeCurve, IsExceptionalCurve π C ∧
      x ∈ (C : Set S.toScheme) := by
  simp only [primeSupport, Set.mem_iUnion, exists_prop]

/-- The actual image of that full union under the original map. -/
def imagePoints : Set X.toScheme := π.base '' primeSupport π

theorem primeCurve_subset_primeSupport (C : S.PrimeCurve)
    (hC : IsExceptionalCurve π C) : (C : Set S.toScheme) ⊆ primeSupport π := by
  intro x hx
  exact (mem_primeSupport π x).mpr ⟨C, hC, hx⟩

/-- Every contracted prime lies in the actual source non-isomorphism locus. -/
theorem primeSupport_subset_exceptionalLocus : primeSupport π ⊆ exceptionalLocus π := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := (mem_primeSupport π x).mp hx
  exact IsExceptionalCurve.subset_exceptionalLocus π hC hxC

variable [IsProper π] (hbir : IsBirationalScheme π)

include hbir in
/-- Finiteness of the actual prime set makes its original union closed. -/
theorem isClosed_primeSupport : IsClosed (primeSupport π) :=
  (exceptionalCurves_finite_of_proper_birational π hbir).isClosed_biUnion
    (fun C _ => C.isClosed)

include hbir in
/-- The original contracted-point set is closed by properness. -/
theorem isClosed_imagePoints : IsClosed (imagePoints π) :=
  π.isClosedMap _ (isClosed_primeSupport π hbir)

include hbir in
/-- Each contracted prime has a singleton image, so the original image
set is finite. This counts image points, not prime curves. -/
theorem imagePoints_finite : (imagePoints π).Finite := by
  have heq : imagePoints π =
      ⋃ C : S.PrimeCurve, ⋃ (_ : IsExceptionalCurve π C),
        π.base '' (C : Set S.toScheme) := by
    simp only [imagePoints, primeSupport, Set.image_iUnion]
  rw [heq]
  exact (exceptionalCurves_finite_of_proper_birational π hbir).biUnion fun C hC => by
    obtain ⟨y, hy⟩ := hC
    rw [hy]
    exact Set.finite_singleton y

/-- The complement of the actual image of all contracted prime curves. -/
def complementOpen : X.toScheme.Opens :=
  ⟨(imagePoints π)ᶜ, (isClosed_imagePoints π hbir).isOpen_compl⟩

variable [IsAlgClosed k]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y}))

include hconnected in
private theorem surjective_of_connectedFibers : Surjective π :=
  ⟨fun y => (hconnected y).nonempty⟩

private theorem factor_prime_subset (C : S.PrimeCurve)
    (hC : ∃ p : Spec (CommRingCat.of k) ⟶ X.toScheme,
      C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ X.structureMorphism = 𝟙 _) :
    (C : Set S.toScheme) ⊆ primeSupport π := by
  obtain ⟨p, hp, _⟩ := hC
  exact primeCurve_subset_primeSupport π C (IsExceptionalCurve.of_fieldPoint_factor π C p hp)

include hbir hπ hconnected in
/-- Every original fiber touching a contracted prime is contained in the
union of contracted primes. The curve through every fiber point is produced
by the existing connected-fiber exhaustion theorem. -/
theorem preimage_image_primeSupport :
    π.base ⁻¹' imagePoints π = primeSupport π := by
  letI : Surjective π := surjective_of_connectedFibers π hconnected
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, hzx⟩
    obtain ⟨C, hC, hzC⟩ := (mem_primeSupport π z).mp hz
    obtain ⟨p, hp, hpk⟩ := hC.exists_fieldPoint_factor π hπ C
    have hzpoint : π.base z = fieldMorphismPoint p :=
      PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor S C π p hp z hzC
    have hxpoint : π.base x = fieldMorphismPoint p := hzx.symm.trans hzpoint
    exact ProperBirationalPointFiber.pointFiber_subset_of_contracted_primes
      S X.structureMorphism π hπ hbir (primeSupport π) (factor_prime_subset π)
      C p hp hpk (hconnected _) hxpoint
  · intro x hx
    exact ⟨x, hx, rfl⟩

variable [IsIso π.c]

include hbir hπ hconnected in
/-- The original map is an isomorphism outside the actual finite image of
its contracted prime curves; no independent inverse or partition is supplied. -/
theorem isIso_complementOpen : IsIso (π ∣_ complementOpen π hbir) := by
  letI : Surjective π := surjective_of_connectedFibers π hconnected
  exact ProperBirationalOffContractedSupport.isIso_restrict S X π hπ hbir
    (primeSupport π) (factor_prime_subset π) hconnected
    (complementOpen π hbir) (fun _ hy => hy)

include hbir hπ hconnected in
/-- The actual target non-isomorphism points are precisely the images of
the original contracted prime curves. No singularity assertion is used. -/
theorem targetNonisomorphismLocus_eq_imagePoints :
    targetNonisomorphismLocus π = imagePoints π := by
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hout
    exact hy ⟨complementOpen π hbir, hout,
      isIso_complementOpen π hbir hπ hconnected⟩
  · rintro y ⟨x, hx, rfl⟩ h
    exact primeSupport_subset_exceptionalLocus π hx h

include hbir hπ hconnected in
/-- The whole original non-isomorphism locus consists exactly of the
original contracted prime curves, with no additional isolated points. -/
theorem exceptionalLocus_eq_primeSupport : exceptionalLocus π = primeSupport π := by
  have heq : exceptionalLocus π = π.base ⁻¹' targetNonisomorphismLocus π := rfl
  rw [heq, targetNonisomorphismLocus_eq_imagePoints π hbir hπ hconnected]
  exact preimage_image_primeSupport π hbir hπ hconnected

end KltDP.Geometry.ActualExceptionalLocus
