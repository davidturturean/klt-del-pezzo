import KltDP.Geometry.PointBlowupLocalUniqueness
import KltDP.Compatibility.SchemeTwoOpenCoverIso
import Mathlib.RingTheory.Localization.Ideal

/-!
# Independence under principal affine-neighborhood shrinking

For `r` outside the selected maximal ideal, the smaller neighborhood is
the actual principal localization `Spec R[1/r]`. Its point is the actual
extended maximal ideal, whose primality, maximality and contraction are
proved from the pinned localization ideal correspondence. The affine
blowup comparison is the existing map constructed by universal uniqueness.
The unchanged complements are identified over the base, and the two
pieces are then proved to cover the original glued blowup with the actual
overlap. Existing two-open descent supplies the resulting isomorphism.

No comparison map, coverage, maximality of the extended ideal, or gluing
isomorphism is assumed. Comparison for arbitrary non-nested affine
neighborhoods still requires a common-refinement adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

open AffineBlowup

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (r : R) (hr : r ∉ q.asIdeal)

/-- The actual point of the principal localization lying over the selected point. -/
def principalPoint : PrimeSpectrum (Localization.Away r) :=
  ⟨Ideal.map (algebraMap R (Localization.Away r)) q.asIdeal,
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers r)
      (Localization.Away r) q.asIdeal q.isPrime
      ((Ideal.disjoint_powers_iff_not_mem r q.isPrime.isRadical).mpr hr)⟩

theorem principalPoint_comap :
    PrimeSpectrum.comap (algebraMap R (Localization.Away r)) (principalPoint q r hr) = q := by
  apply PrimeSpectrum.ext
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers r)
    (Localization.Away r) q.asIdeal q.isPrime
    ((Ideal.disjoint_powers_iff_not_mem r q.isPrime.isRadical).mpr hr)

instance principalPoint_isMaximal : (principalPoint q r hr).asIdeal.IsMaximal := by
  apply Ideal.isMaximal_def.mpr
  refine ⟨(principalPoint q r hr).isPrime.ne_top, ?_⟩
  intro J hlt
  by_contra hJ
  have hle : q.asIdeal ≤ Ideal.comap (algebraMap R (Localization.Away r)) J :=
    Ideal.map_le_iff_le_comap.mp hlt.le
  have heq := Ideal.IsMaximal.eq_of_le (inferInstance : q.asIdeal.IsMaximal)
    (Ideal.comap_ne_top _ hJ) hle
  have hmap := congrArg (Ideal.map (algebraMap R (Localization.Away r))) heq
  rw [IsLocalization.map_comap (Submonoid.powers r) (Localization.Away r)] at hmap
  exact hlt.ne hmap

/-- The actual smaller affine neighborhood of the same point. -/
def principalNeighborhood : Spec (CommRingCat.of (Localization.Away r)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ j

instance principalNeighborhood_isOpenImmersion : IsOpenImmersion (principalNeighborhood j r) := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  unfold principalNeighborhood
  infer_instance

@[simp] theorem principalNeighborhood_point :
    (principalNeighborhood j r).base (principalPoint q r hr) = j.base q := by
  change j.base (PrimeSpectrum.comap (algebraMap R (Localization.Away r))
    (principalPoint q r hr)) = j.base q
  rw [principalPoint_comap]

include hclosed in
theorem principalPoint_image_closed :
    IsClosed ({(principalNeighborhood j r).base (principalPoint q r hr)} : Set X) := by
  rw [principalNeighborhood_point]
  exact hclosed

/-- The complete glued scheme made with the actual smaller neighborhood. -/
abbrev principalScheme := scheme (principalNeighborhood j r) (principalPoint q r hr)
  (principalPoint_image_closed j q hclosed r hr)

private theorem principalPuncture_eq :
    puncture (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr) = puncture j q hclosed := by
  apply Opens.ext
  simp only [puncture, principalNeighborhood_point]

/-- The two unchanged complements are actually isomorphic over `X`. -/
def principalPunctureIso :
    (puncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)).toScheme ≅
        (puncture j q hclosed).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (puncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)).ι
    (puncture j q hclosed).ι (by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, principalPuncture_eq])

@[simp] theorem principalPunctureIso_hom_ι :
    (principalPunctureIso j q hclosed r hr).hom ≫ (puncture j q hclosed).ι =
      (puncture (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr)).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The actual smaller affine Rees blowup maps to the larger glued scheme. -/
def principalAffineMap : AffineBlowup.scheme (principalPoint q r hr).asIdeal ⟶
    scheme j q hclosed :=
  openBaseChangeMap q.asIdeal (algebraMap R (Localization.Away r)) ≫
    affineBlowupι j q hclosed

instance principalAffineMap_isOpenImmersion :
    IsOpenImmersion (principalAffineMap j q hclosed r hr) := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  unfold principalAffineMap
  infer_instance

@[simp] theorem principalAffineMap_projection :
    principalAffineMap j q hclosed r hr ≫ projection j q hclosed =
      toSpec (principalPoint q r hr).asIdeal ≫ principalNeighborhood j r := by
  rw [principalAffineMap, Category.assoc, affineBlowupι_projection,
    ← Category.assoc, openBaseChangeMap_toSpec, Category.assoc]
  rfl

/-- The actual inclusion of the smaller presentation's unchanged complement. -/
def principalComplementMap :
    (puncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)).toScheme ⟶ scheme j q hclosed :=
  (principalPunctureIso j q hclosed r hr).hom ≫ complementι j q hclosed

instance principalComplementMap_isOpenImmersion :
    IsOpenImmersion (principalComplementMap j q hclosed r hr) := by
  unfold principalComplementMap
  infer_instance

@[simp] theorem principalComplementMap_projection :
    principalComplementMap j q hclosed r hr ≫ projection j q hclosed =
      (puncture (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr)).ι := by
  rw [principalComplementMap, Category.assoc, complementι_projection,
    principalPunctureIso_hom_ι]

theorem principalComplementMap_range :
    Set.range (principalComplementMap j q hclosed r hr).base =
      Set.range (complementι j q hclosed).base := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, rfl⟩
    exact ⟨(principalPunctureIso j q hclosed r hr).hom.base b, rfl⟩
  · rintro x ⟨b, rfl⟩
    refine ⟨(principalPunctureIso j q hclosed r hr).inv.base b, ?_⟩
    change ((principalPunctureIso j q hclosed r hr).inv ≫
      ((principalPunctureIso j q hclosed r hr).hom ≫ complementι j q hclosed)).base b =
        (complementι j q hclosed).base b
    rw [Iso.inv_hom_id_assoc]

/-- The actual overlap maps commute into the original glued blowup. -/
theorem principalOverlap_compatibility :
    (overlapOpen (principalPoint q r hr)).ι ≫ principalAffineMap j q hclosed r hr =
      overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
          (principalPoint_image_closed j q hclosed r hr) ≫
        principalComplementMap j q hclosed r hr := by
  have hbase :
      ((overlapOpen (principalPoint q r hr)).ι ≫ principalAffineMap j q hclosed r hr) ≫
          projection j q hclosed =
        (overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
            (principalPoint_image_closed j q hclosed r hr) ≫
          principalComplementMap j q hclosed r hr) ≫ projection j q hclosed := by
    rw [Category.assoc, Category.assoc, principalAffineMap_projection,
      principalComplementMap_projection]
    exact overlap_base_compatibility (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)
  apply hom_ext_of_range_in_puncture j q hclosed
  · intro w
    rw [hbase, Category.assoc, principalComplementMap_projection]
    rw [← principalPuncture_eq j q hclosed r hr]
    exact ((overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)).base w).2
  · intro w
    rw [Category.assoc, principalComplementMap_projection]
    rw [← principalPuncture_eq j q hclosed r hr]
    exact ((overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr)).base w).2
  · exact hbase

/-- The same overlap is the actual pullback of the two maps into the
original glued blowup; its open range is derived from the base point. -/
def principalOverlapIsPullback :
    IsPullback (overlapOpen (principalPoint q r hr)).ι
      (overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr))
      (principalAffineMap j q hclosed r hr) (principalComplementMap j q hclosed r hr) := by
  apply KltDP.SchemeTwoOpenGluing.isPullback_of_range
    _ _ _ _ (principalOverlap_compatibility j q hclosed r hr)
  rw [Scheme.Opens.range_ι, principalComplementMap_range, range_complementι]
  ext a
  change (toSpec (principalPoint q r hr).asIdeal).base a ∈
      centerComplement (principalPoint q r hr).asIdeal ↔
    (principalAffineMap j q hclosed r hr ≫ projection j q hclosed).base a ≠ j.base q
  rw [principalAffineMap_projection, ← principalNeighborhood_point j q r hr]
  exact (mem_centerComplement_iff_ne (principalPoint q r hr) _).trans
    (not_congr (principalNeighborhood j r).isOpenEmbedding.injective.eq_iff).symm

/-- Every point above the selected center already lies in the smaller
affine blowup piece, by the actual open-base-change pullback. -/
theorem centerFiber_mem_principalAffineMap
    (a : AffineBlowup.scheme q.asIdeal) (ha : (toSpec q.asIdeal).base a = q) :
    (affineBlowupι j q hclosed).base a ∈
      Set.range (principalAffineMap j q hclosed r hr).base := by
  let φ := algebraMap R (Localization.Away r)
  let s := Spec.map (CommRingCat.ofHom φ)
  letI : IsOpenImmersion s := IsOpenImmersion.of_isLocalization r
  have hpoint : (toSpec q.asIdeal).base a ∈ Set.range s.base := by
    refine ⟨principalPoint q r hr, ?_⟩
    change PrimeSpectrum.comap φ (principalPoint q r hr) = (toSpec q.asIdeal).base a
    rw [ha]
    exact principalPoint_comap q r hr
  have hpull : a ∈ Set.range (pullback.fst (toSpec q.asIdeal) s).base := by
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    exact hpoint
  obtain ⟨z, hz⟩ := hpull
  let e := openBaseChangeIso q.asIdeal φ
  refine ⟨e.inv.base z, ?_⟩
  change (e.inv ≫ (openBaseChangeMap q.asIdeal φ ≫ affineBlowupι j q hclosed)).base z =
    (affineBlowupι j q hclosed).base a
  rw [← openBaseChangeToPullback_fst]
  change (e.inv ≫ (e.hom ≫ pullback.fst (toSpec q.asIdeal) s) ≫
    affineBlowupι j q hclosed).base z = (affineBlowupι j q hclosed).base a
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (affineBlowupι j q hclosed).base hz

/-- The smaller affine blowup and unchanged complement actually cover
the original glued blowup. -/
theorem principalPieces_cover (x : scheme j q hclosed) :
    (∃ a : AffineBlowup.scheme (principalPoint q r hr).asIdeal,
      (principalAffineMap j q hclosed r hr).base a = x) ∨
    (∃ b : (puncture (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr)).toScheme,
      (principalComplementMap j q hclosed r hr).base b = x) := by
  rcases pieces_cover j q hclosed x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · by_cases ha : (toSpec q.asIdeal).base a = q
    · exact Or.inl (centerFiber_mem_principalAffineMap j q hclosed r hr a ha)
    · apply Or.inr
      change (affineBlowupι j q hclosed).base a ∈
        Set.range (principalComplementMap j q hclosed r hr).base
      rw [principalComplementMap_range, range_complementι]
      change (affineBlowupι j q hclosed ≫ projection j q hclosed).base a ≠ j.base q
      rw [affineBlowupι_projection]
      exact fun heq => ha (j.isOpenEmbedding.injective heq)
  · apply Or.inr
    change (complementι j q hclosed).base b ∈
      Set.range (principalComplementMap j q hclosed r hr).base
    rw [principalComplementMap_range]
    exact ⟨b, rfl⟩

/-- Shrinking the chosen affine neighborhood to an actual principal open
containing the center gives an actual isomorphism of the glued blowups. -/
def principalNeighborhoodIso : principalScheme j q hclosed r hr ≅ scheme j q hclosed :=
  KltDP.SchemeTwoOpenGluing.isoOfCover (overlapOpen (principalPoint q r hr)).ι
    (overlapToPuncture (principalNeighborhood j r) (principalPoint q r hr)
      (principalPoint_image_closed j q hclosed r hr))
    (principalAffineMap j q hclosed r hr) (principalComplementMap j q hclosed r hr)
    (principalOverlapIsPullback j q hclosed r hr) (principalPieces_cover j q hclosed r hr)

@[simp] theorem principalNeighborhoodIso_affineι :
    affineBlowupι (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr) ≫
      (principalNeighborhoodIso j q hclosed r hr).hom = principalAffineMap j q hclosed r hr :=
  KltDP.SchemeTwoOpenGluing.leftι_toTarget _ _ _ _
    (principalOverlap_compatibility j q hclosed r hr)

@[simp] theorem principalNeighborhoodIso_complementι :
    complementι (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr) ≫
      (principalNeighborhoodIso j q hclosed r hr).hom =
        principalComplementMap j q hclosed r hr :=
  KltDP.SchemeTwoOpenGluing.rightι_toTarget _ _ _ _
    (principalOverlap_compatibility j q hclosed r hr)

/-- The comparison isomorphism lies over the identity of the original scheme. -/
theorem principalNeighborhoodIso_over_base :
    (principalNeighborhoodIso j q hclosed r hr).hom ≫ projection j q hclosed =
      projection (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr) := by
  apply hom_ext (principalNeighborhood j r) (principalPoint q r hr)
    (principalPoint_image_closed j q hclosed r hr)
  · rw [← Category.assoc, principalNeighborhoodIso_affineι,
      principalAffineMap_projection, affineBlowupι_projection]
  · rw [← Category.assoc, principalNeighborhoodIso_complementι,
      principalComplementMap_projection, complementι_projection]

/-- The inverse comparison also lies over the identity of the base. -/
theorem principalNeighborhoodIso_inv_over_base :
    (principalNeighborhoodIso j q hclosed r hr).inv ≫
        projection (principalNeighborhood j r) (principalPoint q r hr)
          (principalPoint_image_closed j q hclosed r hr) = projection j q hclosed := by
  apply (cancel_epi (principalNeighborhoodIso j q hclosed r hr).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, principalNeighborhoodIso_over_base]

/-- The constructed comparison is the unique morphism over the original
base, by the proved endomorphism uniqueness on the smaller glued blowup. -/
theorem principalNeighborhoodIso_unique
    (f : principalScheme j q hclosed r hr ⟶ scheme j q hclosed)
    (hf : f ≫ projection j q hclosed =
      projection (principalNeighborhood j r) (principalPoint q r hr)
        (principalPoint_image_closed j q hclosed r hr)) :
    f = (principalNeighborhoodIso j q hclosed r hr).hom := by
  have h := endomorphism_eq_id (principalNeighborhood j r) (principalPoint q r hr)
    (principalPoint_image_closed j q hclosed r hr)
    (f ≫ (principalNeighborhoodIso j q hclosed r hr).inv) (by
      rw [Category.assoc, principalNeighborhoodIso_inv_over_base, hf])
  apply (cancel_mono (principalNeighborhoodIso j q hclosed r hr).inv).mp
  rw [h, Iso.hom_inv_id]

end KltDP.Geometry.PointBlowupGluing
