import KltDP.Geometry.AffineBlowupCenter
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual blowup comparison under affine open base change

The regular-principal center condition is transported through actual open
immersions and through composition of actual affine base maps. The proved
universal mapping property then constructs the comparison of Rees blowups
and the inverse on the actual fiber product. Both inverse identities follow
from the existing uniqueness theorem. No comparison morphism or isomorphism
is assumed in the input.

This supplies the affine-open overlap isomorphism needed to glue local
blowups over a general scheme. The global gluing itself is not asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowup

universe u

section LocalCondition

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))

/-- Precomposing with an actual open immersion preserves the proved local equations. -/
theorem locallyPrincipalRegular_open_precomp
    (hlocal : LocallyPrincipalRegular I f) (j : X ⟶ Y) [IsOpenImmersion j] :
    LocallyPrincipalRegular I (j ≫ f) := by
  obtain ⟨𝒰, h𝒰⟩ := hlocal
  let 𝒱 := 𝒰.openCover.pullbackCover j
  let 𝒲 := Scheme.OpenCover.affineRefinement 𝒱
  refine ⟨𝒲, ?_⟩
  intro a
  obtain ⟨d, hcenter, hregular⟩ := h𝒰 a.1
  let β : Spec (𝒲.obj a) ⟶ Spec (𝒰.obj a.1) :=
    (𝒱.obj a.1).affineCover.map a.2 ≫ 𝒰.openCover.pullbackHom j a.1
  letI : IsOpenImmersion β := by
    change IsOpenImmersion
      ((𝒱.obj a.1).affineCover.map a.2 ≫ pullback.snd j (𝒰.map a.1))
    infer_instance
  let ρ := (Spec.preimage β).hom
  have hρ : Spec.map (CommRingCat.ofHom ρ) = β := by
    change Spec.map (Spec.preimage β) = β
    exact Spec.map_preimage β
  have hreg : ρ d ∈ nonZeroDivisors (𝒲.obj a) :=
    openImmersionSpecPreimage_mem_nonZeroDivisors β hregular
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

/-- A canonical actual lift, chosen from the already proved existence-and-uniqueness theorem. -/
def universalLift (hlocal : LocallyPrincipalRegular I f) : Y ⟶ scheme I :=
  (existsUnique_lift_of_locally_principal_regular I f hlocal).choose

@[simp] theorem universalLift_toSpec (hlocal : LocallyPrincipalRegular I f) :
    universalLift I f hlocal ≫ toSpec I = f :=
  (existsUnique_lift_of_locally_principal_regular I f hlocal).choose_spec.1

theorem universalLift_unique (hlocal : LocallyPrincipalRegular I f)
    (g : Y ⟶ scheme I) (hg : g ≫ toSpec I = f) : g = universalLift I f hlocal :=
  (existsUnique_lift_of_locally_principal_regular I f hlocal).choose_spec.2 g hg

/-- Actual maps over the same admissible test morphism agree. -/
theorem hom_ext_of_locallyPrincipalRegular (hlocal : LocallyPrincipalRegular I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ toSpec I = f) (hh : h ≫ toSpec I = f) : g = h :=
  (universalLift_unique I f hlocal g hg).trans
    (universalLift_unique I f hlocal h hh).symm

end LocalCondition

section ChangeBase

variable {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S)

/-- Compatibility of the actual affine chart ring maps with a change of affine base. -/
theorem testChartMap_changeBase {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of S)) (𝒰 : Scheme.AffineOpenCover.{u} Y) (i : 𝒰.J) :
    testChartMap (g ≫ Spec.map (CommRingCat.ofHom φ)) 𝒰 i =
      (testChartMap g 𝒰 i).comp φ := by
  have hc : CommRingCat.ofHom
      (testChartMap (g ≫ Spec.map (CommRingCat.ofHom φ)) 𝒰 i) =
        CommRingCat.ofHom ((testChartMap g 𝒰 i).comp φ) := by
    apply Spec.map_injective
    rw [testChartMap_toSpec, CommRingCat.ofHom_comp, Spec.map_comp,
      testChartMap_toSpec, Category.assoc]
  exact congrArg CommRingCat.Hom.hom hc

/-- The literal local regular-principal condition agrees for the extended center ideal. -/
theorem locallyPrincipalRegular_changeBase_iff {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of S)) :
    LocallyPrincipalRegular (Ideal.map φ I) g ↔
      LocallyPrincipalRegular I (g ≫ Spec.map (CommRingCat.ofHom φ)) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i => ?_⟩
    obtain ⟨d, hd, hreg⟩ := h𝒰 i
    refine ⟨d, ?_, hreg⟩
    rw [testChartMap_changeBase, ← Ideal.map_map]
    exact hd
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i => ?_⟩
    obtain ⟨d, hd, hreg⟩ := h𝒰 i
    refine ⟨d, ?_, hreg⟩
    rw [Ideal.map_map, ← testChartMap_changeBase]
    exact hd

/-- The changed-base blowup is an actual admissible test scheme over the original base. -/
theorem changedBase_locallyPrincipalRegular :
    LocallyPrincipalRegular I
      (toSpec (Ideal.map φ I) ≫ Spec.map (CommRingCat.ofHom φ)) :=
  (locallyPrincipalRegular_changeBase_iff I φ (toSpec (Ideal.map φ I))).mp
    (toSpec_locallyPrincipalRegular (Ideal.map φ I))

/-- The actual comparison morphism between the two Rees blowups. -/
def openBaseChangeMap : scheme (Ideal.map φ I) ⟶ scheme I :=
  universalLift I (toSpec (Ideal.map φ I) ≫ Spec.map (CommRingCat.ofHom φ))
    (changedBase_locallyPrincipalRegular I φ)

@[simp] theorem openBaseChangeMap_toSpec :
    openBaseChangeMap I φ ≫ toSpec I =
      toSpec (Ideal.map φ I) ≫ Spec.map (CommRingCat.ofHom φ) :=
  universalLift_toSpec I _ _

/-- The actual scheme-theoretic base change of the original Rees blowup. -/
abbrev openBaseChangePullback := pullback (toSpec I) (Spec.map (CommRingCat.ofHom φ))

/-- The canonical comparison to that actual fiber product. -/
def openBaseChangeToPullback : scheme (Ideal.map φ I) ⟶ openBaseChangePullback I φ :=
  pullback.lift (openBaseChangeMap I φ) (toSpec (Ideal.map φ I))
    (openBaseChangeMap_toSpec I φ)

@[simp] theorem openBaseChangeToPullback_fst :
    openBaseChangeToPullback I φ ≫ pullback.fst _ _ = openBaseChangeMap I φ :=
  pullback.lift_fst _ _ _

@[simp] theorem openBaseChangeToPullback_snd :
    openBaseChangeToPullback I φ ≫ pullback.snd _ _ = toSpec (Ideal.map φ I) :=
  pullback.lift_snd _ _ _

variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]

/-- The actual pullback is admissible over the original base, by preservation on open subschemes. -/
theorem openPullback_locallyPrincipalRegular :
    LocallyPrincipalRegular I
      (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ)) ≫ toSpec I) :=
  locallyPrincipalRegular_open_precomp I (toSpec I) (toSpec_locallyPrincipalRegular I)
    (pullback.fst (toSpec I) (Spec.map (CommRingCat.ofHom φ)))

/-- The same actual test object is admissible for the extended ideal on the open base. -/
theorem openPullback_changedCenter_locallyPrincipalRegular :
    LocallyPrincipalRegular (Ideal.map φ I)
      (pullback.snd (toSpec I) (Spec.map (CommRingCat.ofHom φ))) := by
  apply (locallyPrincipalRegular_changeBase_iff I φ _).mpr
  rw [← pullback.condition]
  exact openPullback_locallyPrincipalRegular I φ

/-- The inverse comparison, constructed by the universal lift for the extended center. -/
def openBaseChangeFromPullback : openBaseChangePullback I φ ⟶ scheme (Ideal.map φ I) :=
  universalLift (Ideal.map φ I) (pullback.snd _ _)
    (openPullback_changedCenter_locallyPrincipalRegular I φ)

@[simp] theorem openBaseChangeFromPullback_toSpec :
    openBaseChangeFromPullback I φ ≫ toSpec (Ideal.map φ I) = pullback.snd _ _ :=
  universalLift_toSpec _ _ _

/-- The first inverse identity is forced by uniqueness of endomorphisms over the new base. -/
theorem openBaseChange_hom_inv_id :
    openBaseChangeToPullback I φ ≫ openBaseChangeFromPullback I φ =
      𝟙 (scheme (Ideal.map φ I)) := by
  apply endomorphism_eq_id
  rw [Category.assoc, openBaseChangeFromPullback_toSpec, openBaseChangeToPullback_snd]

/-- The other inverse identity follows from actual pullback extensionality and universal uniqueness. -/
theorem openBaseChange_inv_hom_id :
    openBaseChangeFromPullback I φ ≫ openBaseChangeToPullback I φ =
      𝟙 (openBaseChangePullback I φ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, openBaseChangeToPullback_fst, Category.id_comp]
    apply hom_ext_of_locallyPrincipalRegular I _ (openPullback_locallyPrincipalRegular I φ)
    · rw [Category.assoc, openBaseChangeMap_toSpec, ← Category.assoc,
        openBaseChangeFromPullback_toSpec]
      exact pullback.condition.symm
    · rfl
  · rw [Category.assoc, openBaseChangeToPullback_snd,
      openBaseChangeFromPullback_toSpec, Category.id_comp]

/-- Blowup along the actual extended ideal is isomorphic to actual open base change of the blowup. -/
def openBaseChangeIso : scheme (Ideal.map φ I) ≅ openBaseChangePullback I φ where
  hom := openBaseChangeToPullback I φ
  inv := openBaseChangeFromPullback I φ
  hom_inv_id := openBaseChange_hom_inv_id I φ
  inv_hom_id := openBaseChange_inv_hom_id I φ

/-- The actual comparison is an open immersion, as required for gluing affine blowups. -/
instance openBaseChangeMap_isOpenImmersion : IsOpenImmersion (openBaseChangeMap I φ) := by
  rw [← openBaseChangeToPullback_fst I φ]
  change IsOpenImmersion ((openBaseChangeIso I φ).hom ≫ pullback.fst _ _)
  infer_instance

end ChangeBase

/-- Concrete specialization to restriction along an actual principal affine open. -/
def principalOpenBaseChangeIso {R : Type u} [CommRing R] (I : Ideal R) (r : R) :
    scheme (Ideal.map (algebraMap R (Localization.Away r)) I) ≅
      pullback (toSpec I)
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  exact openBaseChangeIso I (algebraMap R (Localization.Away r))

end KltDP.Geometry.AffineBlowup
