import KltDP.Geometry.SmoothFieldCharts
import KltDP.Geometry.RegularLocalEquiv
import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Compatibility.StandardSmoothClosedHeight

/-!
# Cotangent bounds at actual closed smooth points

The existing standard-smooth neighborhood and closed-point cotangent
comparison apply without an integrality assumption on the whole source.
The actual affine prime is maximal because the original point is closed.
The canonical localization equivalence then transports the comparison
to its original structure-sheaf stalk and original residue field.

In particular, a smooth scheme of dimension at most one has stalk
cotangent dimension at most one at each closed point. This applies to
the possibly disconnected original branch and root-zero schemes.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
universe u

namespace KltDP.Geometry.SmoothClosedStalkCotangent

private theorem affinePrime_isMaximal_of_closed {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) (x : V) (hx : IsClosed ({(x : Y)} : Set Y)) :
    (hV.primeIdealOf x).asIdeal.IsMaximal := by
  have hpre : IsClosed ((Subtype.val : V → Y) ⁻¹' ({(x : Y)} : Set Y)) :=
    hx.preimage continuous_subtype_val
  have heq : (Subtype.val : V → Y) ⁻¹' ({(x : Y)} : Set Y) = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.ext_iff.symm
  rw [heq] at hpre
  have hclosed := hV.isoSpec.hom.homeomorph.isClosedMap _ hpre
  rw [Set.image_singleton] at hclosed
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (CommRingCat.of k)) [IsSmooth σ]

include σ

/-- The original closed smooth stalk has cotangent dimension at most its ring dimension. -/
theorem cotangent_finrank_le_ringKrullDim (x : Y) (hx : IsClosed ({x} : Set Y)) :
    (Module.finrank (ResidueField (Y.presheaf.stalk x))
      (CotangentSpace (Y.presheaf.stalk x)) : WithBot ℕ∞) ≤
        ringKrullDim (Y.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hsmooth⟩ := isSmooth_field_exists_affine_standardSmooth σ x
  letI := affineSectionsAlgebra σ hV
  obtain ⟨⟨P⟩⟩ := hsmooth
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension k Γ(Y, V) := ⟨P, rfl⟩
  let xv : V := ⟨x, hxV⟩
  let q : Ideal Γ(Y, V) := (hV.primeIdealOf xv).asIdeal
  letI : q.IsMaximal := affinePrime_isMaximal_of_closed hV xv hx
  letI : Algebra Γ(Y, V) (Y.presheaf.stalk x) := Y.presheaf.algebra_section_stalk xv
  letI : IsLocalization.AtPrime (Y.presheaf.stalk x) q := hV.isLocalization_stalk xv
  let e : (Y.presheaf.stalk x) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk x) (Localization.AtPrime q)).toRingEquiv
  have h := KltDP.Compatibility.standardSmooth_closed_cotangent_finrank_le_ringKrullDim
    k Γ(Y, V) P.dimension q
  rw [← cotangent_finrank_eq_of_ringEquiv e, ← ringKrullDim_eq_of_ringEquiv e] at h
  exact h

/-- At every closed point of an actual smooth scheme of dimension at most one,
the original stalk cotangent space has dimension at most one. -/
theorem cotangent_finrank_le_one (hdim : topologicalKrullDim Y ≤ 1)
    (x : Y) (hx : IsClosed ({x} : Set Y)) :
    Module.finrank (ResidueField (Y.presheaf.stalk x))
      (CotangentSpace (Y.presheaf.stalk x)) ≤ 1 := by
  have h := (cotangent_finrank_le_ringKrullDim σ x hx).trans
    ((ringKrullDim_stalk_le_topologicalKrullDim Y x).trans hdim)
  exact_mod_cast h

end KltDP.Geometry.SmoothClosedStalkCotangent

#print axioms KltDP.Geometry.SmoothClosedStalkCotangent.cotangent_finrank_le_ringKrullDim
#print axioms KltDP.Geometry.SmoothClosedStalkCotangent.cotangent_finrank_le_one
