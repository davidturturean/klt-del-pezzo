import KltDP.Examples.FrobeniusMultiCentreIntegral

/-! # Integrality of the actual pullback of modifications with disjoint support

This abstracts the existing two-open integrality argument so its kernel proof
is checked before substituting the concrete finite and infinity contact towers.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.DisjointModificationPullback

open KltDP.Examples.FrobeniusProjectivePoints
open KltDP.Examples.FrobeniusMultiCentreIntegral
open KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusStageComplement

/-- The original pullback is integral when the factors are integral and each
modification is an isomorphism on one of two covering opens with a common point. -/
theorem isIntegral {k : Type u} [Field k] {S T : Scheme.{u}}
    (f : S ⟶ projectiveProduct k) (g : T ⟶ projectiveProduct k)
    [IsIntegral S] [IsIntegral T]
    (U V : (projectiveProduct k).Opens) (hcover : ∀ x, x ∈ U ∨ x ∈ V)
    [IsIso (g ∣_ U)] [IsIso (f ∣_ V)] [hUV : Nonempty (U ⊓ V : (projectiveProduct k).Opens)] :
    IsIntegral (pullback f g) := by
  letI : IsIso (pullback.snd g U.ι) := isIso_pullback_snd_ι_of_restrict _ _
  letI : IsIso (pullback.snd f V.ι) := isIso_pullback_snd_ι_of_restrict _ _
  let 𝒲 := Scheme.Pullback.openCoverOfBase (twoOpenCover U V hcover) f g
  let c : (U ⊓ V : (projectiveProduct k).Opens) := Classical.choice hUV
  obtain ⟨s', hs'⟩ := (inferInstance : Surjective (f ∣_ V)).surj ⟨c.val, c.property.2⟩
  have hs : f.base s'.1 = c.val := by
    rw [← morphismRestrict_base_coe, hs']
    rfl
  obtain ⟨t', ht'⟩ := (inferInstance : Surjective (g ∣_ U)).surj ⟨c.val, c.property.1⟩
  have ht : g.base t'.1 = c.val := by
    rw [← morphismRestrict_base_coe, ht']
    rfl
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
    s'.1 t'.1 (hs.trans ht.symm)
  have hzU : z ∈ Set.range (𝒲.map ⟨true⟩).base := by
    rw [Scheme.Pullback.openCoverOfBase_map]
    exact mem_range_pieceMap f g U z (by rw [hz₁, hs]; exact c.property.1)
  have hzV : z ∈ Set.range (𝒲.map ⟨false⟩).base := by
    rw [Scheme.Pullback.openCoverOfBase_map]
    exact mem_range_pieceMap f g V z (by rw [hz₁, hs]; exact c.property.2)
  have hpiece : ∀ i, IsIntegral ((𝒲).obj i) := by
    rintro ⟨b⟩
    cases b
    · obtain ⟨y, _⟩ := hzV
      letI : Nonempty ((pullback (pullback.snd (f) (V).ι)
          (pullback.snd (g) (V).ι) : Scheme.{u})) := ⟨y⟩
      exact pieceRight_isIntegral (f) (g) (V)
    · obtain ⟨y, _⟩ := hzU
      letI : Nonempty ((pullback (pullback.snd (f) (U).ι)
          (pullback.snd (g) (U).ι) : Scheme.{u})) := ⟨y⟩
      exact pieceLeft_isIntegral (f) (g) (U)
  change IsIntegral (pullback (f) (g) : Scheme.{u})
  haveI hred : IsReduced (pullback (f) (g) : Scheme.{u}) := by
    haveI : ∀ x : (pullback (f) (g) : Scheme.{u}),
        _root_.IsReduced ((pullback (f) (g) : Scheme.{u}).presheaf.stalk x) := by
      intro x
      obtain ⟨y, hy⟩ := (𝒲).covers x
      haveI := (𝒲).map_prop ((𝒲).f x)
      letI := hpiece ((𝒲).f x)
      rw [← hy]
      exact isReduced_of_injective (((𝒲).map ((𝒲).f x)).stalkMap y).hom
        (asIso (((𝒲).map ((𝒲).f x)).stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk _
  haveI hirr : IrreducibleSpace (pullback (f) (g) : Scheme.{u}) := by
    have hrange : ∀ i, IsIrreducible (Set.range ((𝒲).map i).base) := by
      intro i
      letI := hpiece i
      have h := (IrreducibleSpace.isIrreducible_univ ((𝒲).obj i)).image
        ((𝒲).map i).base ((𝒲).map i).continuous.continuousOn
      simpa only [Set.image_univ] using h
    refine irreducibleSpace_of_two_irreducible_opens (hrange ⟨true⟩) (hrange ⟨false⟩)
      ?_ ?_ ?_ hzU hzV
    · haveI := (𝒲).map_prop ⟨true⟩
      exact ((𝒲).map ⟨true⟩).isOpenEmbedding.isOpen_range
    · haveI := (𝒲).map_prop ⟨false⟩
      exact ((𝒲).map ⟨false⟩).isOpenEmbedding.isOpen_range
    · intro x
      rcases hcover
        ((f).base ((pullback.fst (f) (g)).base x)) with
        hx | hx
      · left
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact mem_range_pieceMap (f) (g) (U) x hx
      · right
        rw [Scheme.Pullback.openCoverOfBase_map]
        exact mem_range_pieceMap (f) (g) (V) x hx
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end KltDP.Geometry.DisjointModificationPullback

#print axioms KltDP.Geometry.DisjointModificationPullback.isIntegral
