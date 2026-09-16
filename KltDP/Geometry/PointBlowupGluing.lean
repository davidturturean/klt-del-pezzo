import KltDP.Compatibility.SchemeTwoOpenGluing
import KltDP.Geometry.AffineBlowupComplement

/-!
# Gluing an actual point blowup to the unchanged complement

An actual affine open neighborhood `j : Spec R → X` and an actual closed
point `q` in it determine the construction. Its image is assumed closed in
`X`, which is required to form the unchanged open complement. The center
is exactly the maximal ideal `q.asIdeal`.

The existing complement isomorphism of the actual Rees blowup determines
the overlap maps. Gluing constructs an actual scheme and its morphism to
`X`. The two open pieces, their coverage and their scheme-theoretic
intersection are conclusions. No desired lifts or gluing conclusions are
included in the hypotheses.

Smoothness, projectivity, global ideal-sheaf universality, independence of
the affine neighborhood, and strict-transform formulas remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

open AffineBlowup

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- The actual complement of the selected closed point in the original scheme. -/
def puncture : X.Opens := ⟨({j.base q} : Set X)ᶜ, hclosed.isOpen_compl⟩

/-- For a maximal center, its affine vanishing locus is exactly the selected point. -/
theorem mem_centerComplement_iff_ne (p : PrimeSpectrum R) :
    p ∈ centerComplement q.asIdeal ↔ p ≠ q := by
  change (¬ (q.asIdeal : Set R) ⊆ p.asIdeal) ↔ p ≠ q
  constructor
  · intro hp heq
    subst p
    exact hp (fun _ => id)
  · intro hp hle
    apply hp
    apply PrimeSpectrum.ext
    exact (Ideal.IsMaximal.eq_of_le (inferInstance : q.asIdeal.IsMaximal)
      p.isPrime.ne_top hle).symm

/-- The actual affine complement maps into the unchanged global complement. -/
theorem affineComplement_range_in_puncture :
    Set.range ((centerComplement q.asIdeal).ι ≫ j).base ⊆
      Set.range (puncture j q hclosed).ι.base := by
  rintro x ⟨p, rfl⟩
  refine ⟨⟨j.base p.1, ?_⟩, rfl⟩
  change j.base p.1 ∉ ({j.base q} : Set X)
  intro heq
  have hpq : p.1 = q := j.isOpenEmbedding.injective (Set.mem_singleton_iff.mp heq)
  exact ((mem_centerComplement_iff_ne q p.1).mp p.2) hpq

/-- The overlap inclusion into the unchanged complement is constructed by the open-immersion lift. -/
def affineComplementToPuncture :
    (centerComplement q.asIdeal).toScheme ⟶ (puncture j q hclosed).toScheme :=
  IsOpenImmersion.lift (puncture j q hclosed).ι ((centerComplement q.asIdeal).ι ≫ j)
    (affineComplement_range_in_puncture j q hclosed)

@[simp] theorem affineComplementToPuncture_fac :
    affineComplementToPuncture j q hclosed ≫ (puncture j q hclosed).ι =
      (centerComplement q.asIdeal).ι ≫ j :=
  IsOpenImmersion.lift_fac _ _ _

instance affineComplementToPuncture_isOpenImmersion :
    IsOpenImmersion (affineComplementToPuncture j q hclosed) := by
  haveI : IsOpenImmersion
      (affineComplementToPuncture j q hclosed ≫ (puncture j q hclosed).ι) := by
    rw [affineComplementToPuncture_fac]
    infer_instance
  exact IsOpenImmersion.of_comp _ (puncture j q hclosed).ι

/-- This inclusion fills exactly the part of the unchanged complement lying in the affine neighborhood. -/
theorem range_affineComplementToPuncture :
    Set.range (affineComplementToPuncture j q hclosed).base =
      {x : (puncture j q hclosed).toScheme | x.1 ∈ Set.range j.base} := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, rfl⟩
    refine ⟨p.1, ?_⟩
    change ((centerComplement q.asIdeal).ι ≫ j).base p =
      (affineComplementToPuncture j q hclosed ≫ (puncture j q hclosed).ι).base p
    rw [affineComplementToPuncture_fac]
  · rintro x ⟨p, hp⟩
    have hmem : p ∈ centerComplement q.asIdeal := by
      apply (mem_centerComplement_iff_ne q p).mpr
      intro heq
      have hx : x.1 ≠ j.base q := x.2
      apply hx
      rw [← hp, heq]
    refine ⟨⟨p, hmem⟩, ?_⟩
    apply (puncture j q hclosed).ι.isOpenEmbedding.injective
    change (affineComplementToPuncture j q hclosed ≫
      (puncture j q hclosed).ι).base ⟨p, hmem⟩ = x.1
    rw [affineComplementToPuncture_fac]
    exact hp

/-- The actual open overlap on the Rees blowup. -/
def overlapOpen : (AffineBlowup.scheme q.asIdeal).Opens :=
  (toSpec q.asIdeal) ⁻¹ᵁ centerComplement q.asIdeal

abbrev overlap := (overlapOpen q).toScheme

/-- The actual overlap map to the unchanged complement, via the proved Rees complement isomorphism. -/
def overlapToPuncture : overlap q ⟶ (puncture j q hclosed).toScheme :=
  (complementIso q.asIdeal).hom ≫ affineComplementToPuncture j q hclosed

instance overlapToPuncture_isOpenImmersion :
    IsOpenImmersion (overlapToPuncture j q hclosed) := by
  unfold overlapToPuncture
  infer_instance

/-- Compatibility of the two maps to the original scheme is derived from the actual complement map. -/
theorem overlap_base_compatibility :
    (overlapOpen q).ι ≫ (toSpec q.asIdeal ≫ j) =
      overlapToPuncture j q hclosed ≫ (puncture j q hclosed).ι := by
  symm
  calc
    _ = (complementIso q.asIdeal).hom ≫ ((centerComplement q.asIdeal).ι ≫ j) := by
      rw [overlapToPuncture, Category.assoc, affineComplementToPuncture_fac]
    _ = ((complementIso q.asIdeal).hom ≫ (centerComplement q.asIdeal).ι) ≫ j :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [complementIso_hom_ι, Category.assoc]
      rfl

/-- The actual scheme obtained by replacing the affine neighborhood by its Rees point blowup. -/
abbrev scheme :=
  KltDP.SchemeTwoOpenGluing.glued (overlapOpen q).ι (overlapToPuncture j q hclosed)

/-- The complete affine-neighborhood blowup is an open subscheme of the new scheme. -/
def affineBlowupι : AffineBlowup.scheme q.asIdeal ⟶ scheme j q hclosed :=
  KltDP.SchemeTwoOpenGluing.leftι (overlapOpen q).ι (overlapToPuncture j q hclosed)

/-- The unchanged complement is an open subscheme of the new scheme. -/
def complementι : (puncture j q hclosed).toScheme ⟶ scheme j q hclosed :=
  KltDP.SchemeTwoOpenGluing.rightι (overlapOpen q).ι (overlapToPuncture j q hclosed)

instance affineBlowupι_isOpenImmersion : IsOpenImmersion (affineBlowupι j q hclosed) := by
  unfold affineBlowupι
  infer_instance

instance complementι_isOpenImmersion : IsOpenImmersion (complementι j q hclosed) := by
  unfold complementι
  infer_instance

/-- The actual global morphism, glued from the affine blowup projection and the unchanged inclusion. -/
def projection : scheme j q hclosed ⟶ X :=
  KltDP.SchemeTwoOpenGluing.toTarget (overlapOpen q).ι (overlapToPuncture j q hclosed)
    (toSpec q.asIdeal ≫ j) (puncture j q hclosed).ι
    (overlap_base_compatibility j q hclosed)

@[simp] theorem affineBlowupι_projection :
    affineBlowupι j q hclosed ≫ projection j q hclosed = toSpec q.asIdeal ≫ j :=
  KltDP.SchemeTwoOpenGluing.leftι_toTarget _ _ _ _ _

@[simp] theorem complementι_projection :
    complementι j q hclosed ≫ projection j q hclosed = (puncture j q hclosed).ι :=
  KltDP.SchemeTwoOpenGluing.rightι_toTarget _ _ _ _ _

/-- The two actual pieces cover the newly constructed scheme. -/
theorem pieces_cover (x : scheme j q hclosed) :
    (∃ a : AffineBlowup.scheme q.asIdeal, (affineBlowupι j q hclosed).base a = x) ∨
      (∃ b : (puncture j q hclosed).toScheme, (complementι j q hclosed).base b = x) :=
  KltDP.SchemeTwoOpenGluing.jointly_surjective _ _ x

/-- The actual scheme-theoretic intersection is exactly the derived overlap. -/
def overlapIsPullback :
    IsPullback (overlapOpen q).ι (overlapToPuncture j q hclosed)
      (affineBlowupι j q hclosed) (complementι j q hclosed) :=
  KltDP.SchemeTwoOpenGluing.overlapIsPullback _ _

/-- Actual maps from the constructed scheme are determined by their restrictions to the two pieces. -/
theorem hom_ext {Y : Scheme.{u}} (f g : scheme j q hclosed ⟶ Y)
    (hA : affineBlowupι j q hclosed ≫ f = affineBlowupι j q hclosed ≫ g)
    (hC : complementι j q hclosed ≫ f = complementι j q hclosed ≫ g) : f = g :=
  KltDP.SchemeTwoOpenGluing.hom_ext _ _ f g hA hC

/-- The unchanged piece is exactly the inverse image of the original point complement. -/
theorem range_complementι :
    Set.range (complementι j q hclosed).base =
      ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed : Set (scheme j q hclosed)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨b, rfl⟩
    change (complementι j q hclosed ≫ projection j q hclosed).base b ∈ puncture j q hclosed
    rw [complementι_projection]
    exact b.2
  · intro x hx
    rcases pieces_cover j q hclosed x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have hbase : j.base ((toSpec q.asIdeal).base a) ∈ puncture j q hclosed := by
        change (affineBlowupι j q hclosed ≫ projection j q hclosed).base a ∈
          puncture j q hclosed at hx
        rw [affineBlowupι_projection] at hx
        exact hx
      have ha : a ∈ overlapOpen q := by
        change (toSpec q.asIdeal).base a ∈ centerComplement q.asIdeal
        apply (mem_centerComplement_iff_ne q _).mpr
        intro heq
        have hne : j.base ((toSpec q.asIdeal).base a) ≠ j.base q := hbase
        exact hne (congrArg j.base heq)
      let w : overlap q := ⟨a, ha⟩
      refine ⟨(overlapToPuncture j q hclosed).base w, ?_⟩
      change (overlapToPuncture j q hclosed ≫ complementι j q hclosed).base w =
        ((overlapOpen q).ι ≫ affineBlowupι j q hclosed).base w
      exact congrArg (fun t => t.base w)
        (KltDP.SchemeTwoOpenGluing.overlap_condition (overlapOpen q).ι
          (overlapToPuncture j q hclosed)).symm
    · exact ⟨b, rfl⟩

/-- The actual global projection is an isomorphism away from the selected point. -/
def punctureIso :
    ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed).toScheme ≅
      (puncture j q hclosed).toScheme :=
  (IsOpenImmersion.isoOfRangeEq (complementι j q hclosed)
    ((projection j q hclosed) ⁻¹ᵁ puncture j q hclosed).ι
      ((range_complementι j q hclosed).trans Subtype.range_coe.symm)).symm

/-- The displayed complement isomorphism uses precisely the restricted global projection. -/
theorem punctureIso_hom :
    (punctureIso j q hclosed).hom = (projection j q hclosed) ∣_ puncture j q hclosed := by
  apply (cancel_mono (puncture j q hclosed).ι).mp
  rw [morphismRestrict_ι]
  dsimp only [punctureIso, Iso.symm_hom]
  rw [← complementι_projection j q hclosed, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_inv_fac]

end KltDP.Geometry.PointBlowupGluing
