import KltDP.Geometry.AffineBlowupCoordinateIso
import KltDP.Geometry.PointBlowupLocalUniqueness
import KltDP.Compatibility.SchemeTwoOpenCoverIso

/-!
# Actual point blowup comparison for isomorphic affine coordinates

An affine coordinate isomorphism over the original scheme, identifying
the selected points, induces an actual isomorphism of the two glued point
blowups. The affine-piece isomorphism is the proved Rees coordinate
comparison; the complement isomorphism comes from equal ranges of actual
open immersions. Their compatibility, overlap and coverage are proved.
There is no assumed blowup comparison or gluing isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

open AffineBlowup

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) [qR.asIdeal.IsMaximal]
    (qS : PrimeSpectrum S) [qS.asIdeal.IsMaximal]
    (hR : IsClosed ({jR.base qR} : Set X)) (hS : IsClosed ({jS.base qS} : Set X))
    (e : Spec (CommRingCat.of S) ≅ Spec (CommRingCat.of R))
    (he : e.hom ≫ jR = jS) (hp : e.hom.base qS = qR)

include he hp in
theorem coordinate_image_point : jS.base qS = jR.base qR := by
  rw [← he]
  change jR.base (e.hom.base qS) = jR.base qR
  rw [hp]

include he hp in
theorem coordinate_puncture_eq : puncture jS qS hS = puncture jR qR hR := by
  apply Opens.ext
  simp only [puncture, coordinate_image_point jR jS qR qS e he hp]

/-- The unchanged open complements coincide over the original scheme. -/
def coordinatePunctureIso : (puncture jS qS hS).toScheme ≅ (puncture jR qR hR).toScheme :=
  IsOpenImmersion.isoOfRangeEq (puncture jS qS hS).ι (puncture jR qR hR).ι (by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι,
      coordinate_puncture_eq jR jS qR qS hR hS e he hp])

@[simp] theorem coordinatePunctureIso_hom_ι :
    (coordinatePunctureIso jR jS qR qS hR hS e he hp).hom ≫ (puncture jR qR hR).ι =
      (puncture jS qS hS).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

def coordinateAffineMap : AffineBlowup.scheme qS.asIdeal ⟶ scheme jR qR hR :=
  (coordinateBlowupIso e qR qS hp).hom ≫ affineBlowupι jR qR hR

instance coordinateAffineMap_isOpenImmersion :
    IsOpenImmersion (coordinateAffineMap jR qR qS hR e hp) := by
  unfold coordinateAffineMap
  infer_instance

include he in
@[simp] theorem coordinateAffineMap_projection :
    coordinateAffineMap jR qR qS hR e hp ≫ projection jR qR hR = toSpec qS.asIdeal ≫ jS := by
  rw [coordinateAffineMap, Category.assoc, affineBlowupι_projection,
    ← Category.assoc, coordinateBlowupIso_hom_toSpec, Category.assoc, he]

def coordinateComplementMap : (puncture jS qS hS).toScheme ⟶ scheme jR qR hR :=
  (coordinatePunctureIso jR jS qR qS hR hS e he hp).hom ≫ complementι jR qR hR

instance coordinateComplementMap_isOpenImmersion :
    IsOpenImmersion (coordinateComplementMap jR jS qR qS hR hS e he hp) := by
  unfold coordinateComplementMap
  infer_instance

@[simp] theorem coordinateComplementMap_projection :
    coordinateComplementMap jR jS qR qS hR hS e he hp ≫ projection jR qR hR =
      (puncture jS qS hS).ι := by
  rw [coordinateComplementMap, Category.assoc, complementι_projection,
    coordinatePunctureIso_hom_ι]

theorem coordinateComplementMap_range :
    Set.range (coordinateComplementMap jR jS qR qS hR hS e he hp).base =
      Set.range (complementι jR qR hR).base := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, rfl⟩
    exact ⟨(coordinatePunctureIso jR jS qR qS hR hS e he hp).hom.base b, rfl⟩
  · rintro x ⟨b, rfl⟩
    refine ⟨(coordinatePunctureIso jR jS qR qS hR hS e he hp).inv.base b, ?_⟩
    change ((coordinatePunctureIso jR jS qR qS hR hS e he hp).inv ≫
      ((coordinatePunctureIso jR jS qR qS hR hS e he hp).hom ≫
        complementι jR qR hR)).base b = (complementι jR qR hR).base b
    rw [Iso.inv_hom_id_assoc]

theorem coordinateOverlap_compatibility :
    (overlapOpen qS).ι ≫ coordinateAffineMap jR qR qS hR e hp =
      overlapToPuncture jS qS hS ≫ coordinateComplementMap jR jS qR qS hR hS e he hp := by
  have hbase : ((overlapOpen qS).ι ≫ coordinateAffineMap jR qR qS hR e hp) ≫
        projection jR qR hR =
      (overlapToPuncture jS qS hS ≫
        coordinateComplementMap jR jS qR qS hR hS e he hp) ≫ projection jR qR hR := by
    rw [Category.assoc, Category.assoc,
      coordinateAffineMap_projection jR jS qR qS hR e he hp,
      coordinateComplementMap_projection]
    exact overlap_base_compatibility jS qS hS
  apply hom_ext_of_range_in_puncture jR qR hR
  · intro w
    rw [hbase, Category.assoc, coordinateComplementMap_projection,
      ← coordinate_puncture_eq jR jS qR qS hR hS e he hp]
    exact ((overlapToPuncture jS qS hS).base w).2
  · intro w
    rw [Category.assoc, coordinateComplementMap_projection,
      ← coordinate_puncture_eq jR jS qR qS hR hS e he hp]
    exact ((overlapToPuncture jS qS hS).base w).2
  · exact hbase

def coordinateOverlapIsPullback :
    IsPullback (overlapOpen qS).ι (overlapToPuncture jS qS hS)
      (coordinateAffineMap jR qR qS hR e hp)
      (coordinateComplementMap jR jS qR qS hR hS e he hp) := by
  apply KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _
    (coordinateOverlap_compatibility jR jS qR qS hR hS e he hp)
  rw [Scheme.Opens.range_ι, coordinateComplementMap_range, range_complementι]
  ext a
  change (toSpec qS.asIdeal).base a ∈ centerComplement qS.asIdeal ↔
    (coordinateAffineMap jR qR qS hR e hp ≫ projection jR qR hR).base a ≠ jR.base qR
  rw [coordinateAffineMap_projection jR jS qR qS hR e he hp,
    ← coordinate_image_point jR jS qR qS e he hp]
  exact (mem_centerComplement_iff_ne qS _).trans (not_congr jS.isOpenEmbedding.injective.eq_iff).symm

theorem coordinatePieces_cover (x : scheme jR qR hR) :
    (∃ a : AffineBlowup.scheme qS.asIdeal,
      (coordinateAffineMap jR qR qS hR e hp).base a = x) ∨
    (∃ b : (puncture jS qS hS).toScheme,
      (coordinateComplementMap jR jS qR qS hR hS e he hp).base b = x) := by
  rcases pieces_cover jR qR hR x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · apply Or.inl
    refine ⟨(coordinateBlowupIso e qR qS hp).inv.base a, ?_⟩
    change ((coordinateBlowupIso e qR qS hp).inv ≫
      ((coordinateBlowupIso e qR qS hp).hom ≫ affineBlowupι jR qR hR)).base a =
        (affineBlowupι jR qR hR).base a
    rw [Iso.inv_hom_id_assoc]
  · apply Or.inr
    change (complementι jR qR hR).base b ∈
      Set.range (coordinateComplementMap jR jS qR qS hR hS e he hp).base
    rw [coordinateComplementMap_range]
    exact ⟨b, rfl⟩

/-- Changing the actual affine coordinates preserves the actual complete
glued point blowup, by an isomorphism constructed from the two open pieces. -/
def coordinateComparisonIso : scheme jS qS hS ≅ scheme jR qR hR :=
  KltDP.SchemeTwoOpenGluing.isoOfCover (overlapOpen qS).ι (overlapToPuncture jS qS hS)
    (coordinateAffineMap jR qR qS hR e hp)
    (coordinateComplementMap jR jS qR qS hR hS e he hp)
    (coordinateOverlapIsPullback jR jS qR qS hR hS e he hp)
    (coordinatePieces_cover jR jS qR qS hR hS e he hp)

/-- The actual coordinate comparison commutes with the projections to `X`. -/
theorem coordinateComparisonIso_over_base :
    (coordinateComparisonIso jR jS qR qS hR hS e he hp).hom ≫ projection jR qR hR =
      projection jS qS hS := by
  apply hom_ext jS qS hS
  · change KltDP.SchemeTwoOpenGluing.leftι _ _ ≫
        (KltDP.SchemeTwoOpenGluing.toTarget _ _ _ _
          (coordinateOverlap_compatibility jR jS qR qS hR hS e he hp) ≫
            projection jR qR hR) = _
    rw [← Category.assoc, KltDP.SchemeTwoOpenGluing.leftι_toTarget,
      coordinateAffineMap_projection jR jS qR qS hR e he hp, affineBlowupι_projection]
  · change KltDP.SchemeTwoOpenGluing.rightι _ _ ≫
        (KltDP.SchemeTwoOpenGluing.toTarget _ _ _ _
          (coordinateOverlap_compatibility jR jS qR qS hR hS e he hp) ≫
            projection jR qR hR) = _
    rw [← Category.assoc, KltDP.SchemeTwoOpenGluing.rightι_toTarget,
      coordinateComplementMap_projection, complementι_projection]

end KltDP.Geometry.PointBlowupGluing
