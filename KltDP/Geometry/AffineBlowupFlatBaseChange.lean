import KltDP.Geometry.AffineBlowupOpenBaseChange

/-!
# Actual Rees blowups commute with flat affine base change

The existing flat-ring-map theorem preserves actual nonzerodivisors.
Applying it on an affine refinement of a pulled-back cover shows that
flat precomposition preserves the literal regular-principal center
condition. The previously constructed universal lifts then prove that
the actual blowup of the extended ideal is the actual fiber product.

This extends the proved open-base-change argument without assuming a
base-change comparison or an inverse morphism. It does not identify a
general smooth surface neighborhood with an affine plane, or assert a
smoothness-to-flatness theorem absent from the pinned dependency cone.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowup

universe u

/-- An actual flat map between affine schemes preserves a regular element
under its actual contravariant ring homomorphism. -/
theorem flatSpecPreimage_mem_nonZeroDivisors
    {S T : Type u} [CommRing S] [CommRing T]
    (j : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of S)) [Flat j]
    {r : S} (hr : r ∈ nonZeroDivisors S) :
    (Spec.preimage j).hom r ∈ nonZeroDivisors T := by
  have hj : (Spec.preimage j).hom.Flat := by
    apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)
      (φ := Spec.preimage j)).mp
    rw [Spec.map_preimage]
    infer_instance
  exact KltDP.RingTheory.map_mem_nonZeroDivisors_of_flat _ hj hr

/-- Flat precomposition preserves actual local regular-principal center
equations. The affine cover and its equations are constructed by pullback
and affine refinement; no covering or regularity condition is added. -/
theorem locallyPrincipalRegular_flat_precomp
    {R : Type u} [CommRing R] (I : Ideal R)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (hlocal : LocallyPrincipalRegular I f) (j : X ⟶ Y) [Flat j] :
    LocallyPrincipalRegular I (j ≫ f) := by
  obtain ⟨𝒰, h𝒰⟩ := hlocal
  let 𝒱 := 𝒰.openCover.pullbackCover j
  let 𝒲 := Scheme.OpenCover.affineRefinement 𝒱
  refine ⟨𝒲, ?_⟩
  intro a
  obtain ⟨d, hcenter, hregular⟩ := h𝒰 a.1
  let β : Spec (𝒲.obj a) ⟶ Spec (𝒰.obj a.1) :=
    (𝒱.obj a.1).affineCover.map a.2 ≫ 𝒰.openCover.pullbackHom j a.1
  letI : Flat β := by
    change Flat
      ((𝒱.obj a.1).affineCover.map a.2 ≫ pullback.snd j (𝒰.map a.1))
    infer_instance
  let ρ := (Spec.preimage β).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = β := by
    change Spec.map (Spec.preimage β) = β
    exact Spec.map_preimage β
  have hreg : ρ d ∈ nonZeroDivisors (𝒲.obj a) :=
    flatSpecPreimage_mem_nonZeroDivisors β hregular
  have hfac : 𝒲.map a ≫ j = β ≫ 𝒰.map a.1 := by
    change ((𝒱.obj a.1).affineCover.map a.2 ≫
      pullback.fst j (𝒰.map a.1)) ≫ j =
        ((𝒱.obj a.1).affineCover.map a.2 ≫
          pullback.snd j (𝒰.map a.1)) ≫ 𝒰.map a.1
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have hmap : testChartMap (j ≫ f) 𝒲 a =
      ρ.comp (testChartMap f 𝒰 a.1) := by
    have hc : CommRingCat.ofHom (testChartMap (j ≫ f) 𝒲 a) =
        CommRingCat.ofHom (ρ.comp (testChartMap f 𝒰 a.1)) := by
      apply Spec.map_injective
      rw [testChartMap_toSpec, CommRingCat.ofHom_comp, Spec.map_comp,
        testChartMap_toSpec, hρ]
      rw [← Category.assoc, hfac, Category.assoc]
    exact congrArg CommRingCat.Hom.hom hc
  refine ⟨ρ d, ?_, hreg⟩
  rw [hmap]
  exact map_comp_eq_span_singleton I _ d hcenter ρ

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S)
    [Flat (Spec.map (CommRingCat.ofHom φ))]

/-- The actual pullback of the original blowup remains an admissible test
scheme because its map to the blowup is flat. -/
theorem flatPullback_locallyPrincipalRegular :
    LocallyPrincipalRegular I
      (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ)) ≫ toSpec I) :=
  locallyPrincipalRegular_flat_precomp I (toSpec I) (toSpec_locallyPrincipalRegular I)
    (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ)))

/-- The same pullback is admissible for the extended ideal over the new
base, using the proved equality of the actual chart ring maps. -/
theorem flatPullback_changedCenter_locallyPrincipalRegular :
    LocallyPrincipalRegular (Ideal.map φ I)
      (pullback.snd (toSpec I) (Spec.map (CommRingCat.ofHom φ))) := by
  apply (locallyPrincipalRegular_changeBase_iff I φ _).mpr
  rw [← pullback.condition]
  exact flatPullback_locallyPrincipalRegular I φ

/-- The inverse comparison is the actual universal lift for the extended
center, with its admissibility proved above. -/
def flatBaseChangeFromPullback :
    openBaseChangePullback I φ ⟶ scheme (Ideal.map φ I) :=
  universalLift (Ideal.map φ I) (pullback.snd _ _)
    (flatPullback_changedCenter_locallyPrincipalRegular I φ)

@[simp]
theorem flatBaseChangeFromPullback_toSpec :
    flatBaseChangeFromPullback I φ ≫ toSpec (Ideal.map φ I) = pullback.snd _ _ :=
  universalLift_toSpec _ _ _

/-- The first inverse identity follows from the proved uniqueness of
endomorphisms of the actual blowup over its actual base. -/
theorem flatBaseChange_hom_inv_id :
    openBaseChangeToPullback I φ ≫ flatBaseChangeFromPullback I φ =
      𝟙 (scheme (Ideal.map φ I)) := by
  apply endomorphism_eq_id
  rw [Category.assoc, flatBaseChangeFromPullback_toSpec, openBaseChangeToPullback_snd]

/-- The second inverse identity is proved by actual pullback
extensionality and the existing universal uniqueness theorem. -/
theorem flatBaseChange_inv_hom_id :
    flatBaseChangeFromPullback I φ ≫ openBaseChangeToPullback I φ =
      𝟙 (openBaseChangePullback I φ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, openBaseChangeToPullback_fst, Category.id_comp]
    apply hom_ext_of_locallyPrincipalRegular I _ (flatPullback_locallyPrincipalRegular I φ)
    · rw [Category.assoc, openBaseChangeMap_toSpec, ← Category.assoc,
        flatBaseChangeFromPullback_toSpec]
      exact pullback.condition.symm
    · rfl
  · rw [Category.assoc, openBaseChangeToPullback_snd,
      flatBaseChangeFromPullback_toSpec, Category.id_comp]

/-- The actual Rees blowup of the extended ideal is the actual flat
fiber product of the original blowup, with no finiteness assumption on
the ideal or extra condition on either commutative ring. -/
def flatBaseChangeIso :
    scheme (Ideal.map φ I) ≅ pullback (toSpec I) (Spec.map (CommRingCat.ofHom φ)) where
  hom := openBaseChangeToPullback I φ
  inv := flatBaseChangeFromPullback I φ
  hom_inv_id := flatBaseChange_hom_inv_id I φ
  inv_hom_id := flatBaseChange_inv_hom_id I φ

/-- Its map to the new base is the original blowdown of the extended ideal. -/
@[simp]
theorem flatBaseChangeIso_hom_snd :
    (flatBaseChangeIso I φ).hom ≫ pullback.snd _ _ = toSpec (Ideal.map φ I) :=
  openBaseChangeToPullback_snd I φ

/-- The canonical comparison between the actual blowups is flat, as the
composite of the proved isomorphism with an actual flat base change. -/
instance flatBaseChangeMap_isFlat : Flat (openBaseChangeMap I φ) := by
  rw [← openBaseChangeToPullback_fst I φ]
  change Flat ((flatBaseChangeIso I φ).hom ≫ pullback.fst _ _)
  infer_instance

end BaseChange

end KltDP.Geometry.AffineBlowup
