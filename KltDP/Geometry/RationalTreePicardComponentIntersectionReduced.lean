/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The open-cover reducedness proof below is adapted from Mathlib.
-/
import KltDP.Geometry.RationalTreePicardComponentIntersectionChart
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Limits

/-!
# Reducedness transported to original component-intersection quotients

The open-cover proof is a bounded port of the proved theorem
`AlgebraicGeometry.IsReduced.of_openCover` in official Mathlib
`110cb7f03dd1c2d9edd957b937f55175c9fc3343`,
AlgebraicGeometry/Properties.lean:133-138 (Apache 2.0, Andrew Yang).
The pin uses `.obj`/`.map` instead of `.X`/`.f`; the local stalk instance
and underlying ring map are explicit. No other newer source is ported.

Its coproduct specialization and the existing actual open chart transfer
reducedness to the quotient by the unchanged original component ideals.
The scheme isomorphism is an explicit premise of ordinary transport.
No intrinsic nodal theorem, field decomposition, or literature axiom is
asserted here. In a future literal nodal-cut application, the isomorphism
must first come from that separately audited input on the original objects.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- Reducedness descends through the actual open-cover stalk maps.
This is the bounded newer-Mathlib proof port described above. -/
theorem IsReduced.of_openCover {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X)
    [∀ i, IsReduced (𝒰.obj i)] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective ((𝒰.map i).stalkMap y).hom
      (asIso ((𝒰.map i).stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

/-- The actual coproduct of reduced schemes is reduced, including an
empty family. No finiteness of the index is required. -/
theorem IsReduced.sigma {ι : Type v} [Small.{u} ι] (Y : ι → Scheme.{u})
    [∀ i, IsReduced (Y i)] : IsReduced (∐ Y) :=
  haveI : ∀ i, IsReduced ((sigmaOpenCover Y).obj i) := fun i =>
    inferInstanceAs (IsReduced (Y i))
  IsReduced.of_openCover (sigmaOpenCover Y)

end AlgebraicGeometry

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens)

/-- Transport from an actual reduced target of the original intersection.
The quotient and its open-immersion map are the already constructed ones. -/
theorem componentIntersectionQuotient_isReduced_of_iso (Y : Scheme.{u}) [IsReduced Y]
    (e : pullback (componentUnionInclusion X S)
      (componentUnionInclusion X Sᶜ) ≅ Y) :
    _root_.IsReduced (Γ(X, U.1) ⧸
      (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)) := by
  apply (affine_isReduced_iff (CommRingCat.of (Γ(X, U.1) ⧸
    (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)))).mp
  change IsReduced (componentIntersectionChart X S U)
  exact isReduced_of_isOpenImmersion
    (componentIntersectionChartToIntersection X S U ≫ e.hom)

/-- An explicit isomorphism to an actual coproduct of reduced schemes
gives reducedness of each original affine sum quotient. -/
theorem componentIntersectionQuotient_isReduced_of_iso_sigma
    {ι : Type v} [Small.{u} ι] (Y : ι → Scheme.{u}) [∀ i, IsReduced (Y i)]
    (e : pullback (componentUnionInclusion X S)
      (componentUnionInclusion X Sᶜ) ≅ ∐ Y) :
    _root_.IsReduced (Γ(X, U.1) ⧸
      (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)) := by
  letI : IsReduced (∐ Y) := IsReduced.sigma Y
  exact componentIntersectionQuotient_isReduced_of_iso X S U (∐ Y) e

/-- Only the fields are needed for this property transport. A future
literature input must separately retain its finite/separable extensions
and the compatibility of the actual decomposition with the base field. -/
theorem componentIntersectionQuotient_isReduced_of_iso_sigma_spec
    {ι : Type v} [Small.{u} ι] (K : ι → Type u) [∀ i, Field (K i)]
    (e : pullback (componentUnionInclusion X S)
      (componentUnionInclusion X Sᶜ) ≅ ∐ fun i => Spec (CommRingCat.of (K i))) :
    _root_.IsReduced (Γ(X, U.1) ⧸
      (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)) := by
  letI : ∀ i, IsReduced (Spec (CommRingCat.of (K i))) := fun i => inferInstance
  exact componentIntersectionQuotient_isReduced_of_iso_sigma X S U
    (fun i => Spec (CommRingCat.of (K i))) e

end KltDP.Geometry.RationalTreePicard
