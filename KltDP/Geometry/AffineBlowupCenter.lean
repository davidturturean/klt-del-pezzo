import KltDP.Geometry.AffineBlowupSchemeLift
import KltDP.Geometry.AffineBlowupChartCenter

/-!
# The actual extended center on the blowup

Regular principal equations given in the ring coordinates of an actual
affine open immersion are transported to the sections on its open range.
Consequently the cover-based and intrinsic ideal-sheaf formulations of the
local condition agree. Applied to the proved degree-one Rees chart cover,
this shows that the blowup itself is an admissible test object.

Neither principal generation nor regularity on the blowup is an assumption:
both follow from the existing actual chart equations. No assumption on the
base ring or finiteness of the ideal is added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

section Coordinates

variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- A regular principal equation in affine chart coordinates gives a
regular principal equation for the actual ideal sheaf on the open range. -/
theorem exists_regularGenerator_opensRange
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ Y)
    [IsOpenImmersion j] (d : A)
    (hcenter : Ideal.map (Spec.preimage (j ≫ f)).hom I = Ideal.span {d})
    (hregular : d ∈ nonZeroDivisors A) :
    ∃ e : Γ(Y, j.opensRange),
      (extendedCenter I f).ideal ⟨j.opensRange, isAffineOpen_opensRange j⟩ =
        Ideal.span {e} ∧ e ∈ nonZeroDivisors Γ(Y, j.opensRange) := by
  let U : Y.affineOpens := ⟨j.opensRange, isAffineOpen_opensRange j⟩
  have hrange : Set.range U.2.fromSpec.base = Set.range j.base := by
    rw [U.2.range_fromSpec]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq U.2.fromSpec j hrange
  let ρ := (Spec.preimage e.hom).hom
  have hfac : e.hom ≫ j = U.2.fromSpec :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  have hpre : Spec.preimage (U.2.fromSpec ≫ f) =
      Spec.preimage (j ≫ f) ≫ Spec.preimage e.hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
      ← Category.assoc, hfac]
  have hmap : (Spec.preimage (U.2.fromSpec ≫ f)).hom =
      ρ.comp (Spec.preimage (j ≫ f)).hom :=
    congrArg CommRingCat.Hom.hom hpre
  refine ⟨ρ d, ?_, openImmersionSpecPreimage_mem_nonZeroDivisors e.hom hregular⟩
  change (extendedCenter I f).ideal U = Ideal.span {ρ d}
  rw [extendedCenter_ideal, hmap]
  exact map_comp_eq_span_singleton I _ d hcenter ρ

/-- A genuine affine cover carrying regular principal equations gives the
intrinsic pointwise condition on the existing actual ideal-sheaf carrier. -/
theorem extendedCenterLocallyPrincipalRegular_of_locallyPrincipalRegular
    (hlocal : LocallyPrincipalRegular I f) :
    ExtendedCenterLocallyPrincipalRegular I f := by
  obtain ⟨𝒰, h𝒰⟩ := hlocal
  intro y
  let i := 𝒰.f y
  obtain ⟨d, hcenter, hregular⟩ := h𝒰 i
  refine ⟨⟨(𝒰.map i).opensRange, isAffineOpen_opensRange (𝒰.map i)⟩,
    𝒰.covers y, ?_⟩
  exact exists_regularGenerator_opensRange I f (𝒰.map i) d hcenter hregular

/-- Equivalence of the two literal local ideal-equation formulations. -/
theorem locallyPrincipalRegular_iff_extendedCenter :
    LocallyPrincipalRegular I f ↔ ExtendedCenterLocallyPrincipalRegular I f :=
  ⟨extendedCenterLocallyPrincipalRegular_of_locallyPrincipalRegular I f,
    locallyPrincipalRegular_of_extendedCenter I f⟩

end Coordinates

/-- The actual extended center has regular principal equations on the
degree-one cover of the blowup. Coverage is derived from the Rees algebra. -/
theorem toSpec_locallyPrincipalRegular : LocallyPrincipalRegular I (toSpec I) := by
  refine ⟨degreeOneAffineCover I, fun (a : I) =>
    ⟨chartBaseMap I a (a : R), ?_, chartBaseMap_equation_mem_nonZeroDivisors I a⟩⟩
  change Ideal.map (Spec.preimage (chartι I a ≫ toSpec I)).hom I =
    Ideal.span {chartBaseMap I a (a : R)}
  have hchart : chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
  rw [hchart, Spec.preimage_map]
  exact map_chartBaseMap_ideal I a

/-- The blowup itself is an actual admissible test object: its existing
extended ideal sheaf has regular principal equations near every point. -/
theorem toSpec_extendedCenterLocallyPrincipalRegular :
    ExtendedCenterLocallyPrincipalRegular I (toSpec I) :=
  extendedCenterLocallyPrincipalRegular_of_locallyPrincipalRegular I (toSpec I)
    (toSpec_locallyPrincipalRegular I)

/-- The only endomorphism of the blowup over the affine base is its identity. -/
theorem endomorphism_eq_id (g : scheme I ⟶ scheme I)
    (hg : g ≫ toSpec I = toSpec I) : g = 𝟙 (scheme I) := by
  obtain ⟨l, hl, hunique⟩ := existsUnique_lift_of_locally_principal_regular I (toSpec I)
    (toSpec_locallyPrincipalRegular I)
  exact (hunique g hg).trans (hunique (𝟙 _) (Category.id_comp _)).symm

end KltDP.Geometry.AffineBlowup
