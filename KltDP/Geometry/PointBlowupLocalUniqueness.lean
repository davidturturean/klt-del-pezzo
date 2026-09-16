import KltDP.Geometry.PointBlowupGluing
import KltDP.Geometry.AffineBlowupOpenBaseChange

/-!
# Local identification and uniqueness for the actual glued point blowup

The affine Rees blowup is exactly the inverse image of its affine base
neighborhood. Its identification with that open subscheme is constructed
from the two actual open immersions. Maps whose image is off the selected
point are determined by their composite to the base. These facts and the
proved affine blowup uniqueness imply that the only endomorphism of the
glued scheme over the base is the identity.

This is the uniqueness part of neighborhood independence. It does not
assume or construct comparison maps between different neighborhoods.
The source reuses pinned open-immersion lifts and equal-range isomorphisms;
no new general gluing or blowup universal property is postulated.
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

/-- The complete affine Rees piece is precisely the inverse image of the
chosen affine neighborhood under the actual global projection. -/
theorem range_affineBlowupι :
    Set.range (affineBlowupι j q hclosed).base =
      ((projection j q hclosed) ⁻¹ᵁ j.opensRange : Set (scheme j q hclosed)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    change (affineBlowupι j q hclosed ≫ projection j q hclosed).base a ∈
      Set.range j.base
    rw [affineBlowupι_projection]
    exact ⟨(toSpec q.asIdeal).base a, rfl⟩
  · intro x hx
    rcases pieces_cover j q hclosed x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨a, rfl⟩
    · have hb : b.1 ∈ Set.range j.base := by
        change (complementι j q hclosed ≫ projection j q hclosed).base b ∈
          Set.range j.base at hx
        rw [complementι_projection] at hx
        exact hx
      have hb' : b ∈ Set.range (affineComplementToPuncture j q hclosed).base := by
        rw [range_affineComplementToPuncture]
        exact hb
      obtain ⟨p, hp⟩ := hb'
      let w : overlap q := (complementIso q.asIdeal).inv.base p
      have hw : (overlapToPuncture j q hclosed).base w = b := by
        change ((complementIso q.asIdeal).inv ≫
          ((complementIso q.asIdeal).hom ≫
            affineComplementToPuncture j q hclosed)).base p = b
        rw [Iso.inv_hom_id_assoc]
        exact hp
      refine ⟨(overlapOpen q).ι.base w, ?_⟩
      change ((overlapOpen q).ι ≫ affineBlowupι j q hclosed).base w =
        (complementι j q hclosed).base b
      have hOverlap : (overlapOpen q).ι ≫ affineBlowupι j q hclosed =
          overlapToPuncture j q hclosed ≫ complementι j q hclosed :=
        KltDP.SchemeTwoOpenGluing.overlap_condition (overlapOpen q).ι
          (overlapToPuncture j q hclosed)
      rw [hOverlap]
      change (complementι j q hclosed).base
        ((overlapToPuncture j q hclosed).base w) = (complementι j q hclosed).base b
      rw [hw]

/-- The actual affine blowup is canonically identified with this actual
open subscheme of the glued scheme. -/
def affineNeighborhoodIso :
    AffineBlowup.scheme q.asIdeal ≅
      ((projection j q hclosed) ⁻¹ᵁ j.opensRange).toScheme :=
  IsOpenImmersion.isoOfRangeEq (affineBlowupι j q hclosed)
    ((projection j q hclosed) ⁻¹ᵁ j.opensRange).ι
    ((range_affineBlowupι j q hclosed).trans Subtype.range_coe.symm)

@[simp] theorem affineNeighborhoodIso_hom_ι :
    (affineNeighborhoodIso j q hclosed).hom ≫
      ((projection j q hclosed) ⁻¹ᵁ j.opensRange).ι = affineBlowupι j q hclosed :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- A map into the actual glued scheme whose base image lies in the
chosen affine neighborhood factors through the actual affine Rees piece. -/
def affineFactor {Y : Scheme.{u}} (f : Y ⟶ scheme j q hclosed)
    (hf : ∀ y, (f ≫ projection j q hclosed).base y ∈ Set.range j.base) :
    Y ⟶ AffineBlowup.scheme q.asIdeal :=
  IsOpenImmersion.lift (affineBlowupι j q hclosed) f (by
    rintro x ⟨y, rfl⟩
    rw [range_affineBlowupι]
    exact hf y)

@[simp] theorem affineFactor_fac {Y : Scheme.{u}} (f : Y ⟶ scheme j q hclosed)
    (hf : ∀ y, (f ≫ projection j q hclosed).base y ∈ Set.range j.base) :
    affineFactor j q hclosed f hf ≫ affineBlowupι j q hclosed = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization has exactly the prescribed morphism to the affine base. -/
theorem affineFactor_toSpec {Y : Scheme.{u}} (f : Y ⟶ scheme j q hclosed)
    (hf : ∀ y, (f ≫ projection j q hclosed).base y ∈ Set.range j.base)
    (g : Y ⟶ Spec (CommRingCat.of R))
    (hfg : f ≫ projection j q hclosed = g ≫ j) :
    affineFactor j q hclosed f hf ≫ toSpec q.asIdeal = g := by
  apply (cancel_mono j).mp
  rw [Category.assoc, ← affineBlowupι_projection, ← Category.assoc,
    affineFactor_fac, hfg]

/-- Over the puncture the actual projection determines every morphism. -/
theorem hom_ext_of_range_in_puncture {Y : Scheme.{u}}
    (f g : Y ⟶ scheme j q hclosed)
    (hf : ∀ y, (f ≫ projection j q hclosed).base y ∈ puncture j q hclosed)
    (hg : ∀ y, (g ≫ projection j q hclosed).base y ∈ puncture j q hclosed)
    (hbase : f ≫ projection j q hclosed = g ≫ projection j q hclosed) : f = g := by
  have hf' : Set.range f.base ⊆ Set.range (complementι j q hclosed).base := by
    rintro x ⟨y, rfl⟩
    rw [range_complementι]
    exact hf y
  have hg' : Set.range g.base ⊆ Set.range (complementι j q hclosed).base := by
    rintro x ⟨y, rfl⟩
    rw [range_complementι]
    exact hg y
  let f' := IsOpenImmersion.lift (complementι j q hclosed) f hf'
  let g' := IsOpenImmersion.lift (complementι j q hclosed) g hg'
  have hfg : f' = g' := by
    apply (cancel_mono (puncture j q hclosed).ι).mp
    rw [← complementι_projection j q hclosed, ← Category.assoc,
      ← Category.assoc]
    rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, hbase]
  calc
    f = f' ≫ complementι j q hclosed := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = g' ≫ complementι j q hclosed := congrArg (· ≫ complementι j q hclosed) hfg
    _ = g := IsOpenImmersion.lift_fac _ _ _

/-- The actual glued point blowup has no nonidentity endomorphism over its base. -/
theorem endomorphism_eq_id (f : scheme j q hclosed ⟶ scheme j q hclosed)
    (hf : f ≫ projection j q hclosed = projection j q hclosed) :
    f = 𝟙 (scheme j q hclosed) := by
  apply hom_ext j q hclosed
  · have hbase : (affineBlowupι j q hclosed ≫ f) ≫ projection j q hclosed =
        toSpec q.asIdeal ≫ j := by
      rw [Category.assoc, hf, affineBlowupι_projection]
    have hrange : ∀ a,
        ((affineBlowupι j q hclosed ≫ f) ≫ projection j q hclosed).base a ∈
          Set.range j.base := by
      intro a
      rw [hbase]
      exact ⟨(toSpec q.asIdeal).base a, rfl⟩
    let l := affineFactor j q hclosed (affineBlowupι j q hclosed ≫ f) hrange
    have hl : l = 𝟙 (AffineBlowup.scheme q.asIdeal) :=
      AffineBlowup.endomorphism_eq_id q.asIdeal l
        (affineFactor_toSpec j q hclosed _ hrange (toSpec q.asIdeal) hbase)
    rw [Category.comp_id, ← affineFactor_fac j q hclosed _ hrange]
    change l ≫ affineBlowupι j q hclosed = affineBlowupι j q hclosed
    rw [hl, Category.id_comp]
  · rw [Category.comp_id]
    apply hom_ext_of_range_in_puncture j q hclosed
    · intro b
      rw [Category.assoc, hf, complementι_projection]
      exact b.2
    · intro b
      rw [complementι_projection]
      exact b.2
    · rw [Category.assoc, hf]

end KltDP.Geometry.PointBlowupGluing
