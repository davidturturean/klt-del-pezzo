import KltDP.Geometry.PointBlowupGluing
import KltDP.Geometry.AffineBlowupIntegral

/-!
# Integrality of the actual glued point blowup

The actual Rees blowup and unchanged puncture are integral, and their actual
nonempty overlap is dense in the puncture. The proved overlap identity and
coverage therefore make the Rees piece dense in the whole glued scheme.
Reducedness is proved on the two open pieces through their actual stalk maps.

The nonzero-center condition is essential: blowing up the zero ideal of a
field gives an empty scheme. No source-integrality, generic-isomorphism, or
connected-fiber conclusion is supplied as an input. Normality of the base is
not needed for these statements.

Reuse: pinned Mathlib Properties (integrality and reduced stalks),
Irreducible.image/closure, open-set density and continuity of closure images;
the actual two-piece stalk argument already appears in PrimeCurveSubscheme.
No new gluing, localization or birationality foundation is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupGluing

/-- An actual nonempty affine open in an integral scheme has a domain as
its original coordinate ring. The chosen point witnesses nonemptiness. -/
theorem affine_open_chart_isDomain_of_integral
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) : IsDomain R := by
  letI : Nonempty (Spec (CommRingCat.of R)) := ⟨q⟩
  letI : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion j
  exact (affine_isIntegral_iff (CommRingCat.of R)).mp inferInstance

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

include j in
/-- The overlap has an actual point because the center ideal is nonzero. -/
theorem overlap_nonempty (hq : q.asIdeal ≠ ⊥) : Nonempty (overlap q) := by
  letI : IsDomain R := affine_open_chart_isDomain_of_integral j q
  exact AffineBlowup.preimage_centerComplement_nonempty q.asIdeal hq

/-- The actual overlap map supplies a point in the unchanged puncture. -/
theorem puncture_nonempty (hq : q.asIdeal ≠ ⊥) :
    Nonempty (puncture j q hclosed).toScheme :=
  ⟨(overlapToPuncture j q hclosed).base
    (Classical.choice (overlap_nonempty j q hq))⟩

/-- The puncture is integral as an actual nonempty open of the original
integral scheme. Its integrality is not an assumed gluing field. -/
theorem puncture_isIntegral (hq : q.asIdeal ≠ ⊥) :
    IsIntegral (puncture j q hclosed).toScheme := by
  letI : Nonempty (puncture j q hclosed).toScheme := puncture_nonempty j q hclosed hq
  exact isIntegral_of_isOpenImmersion (puncture j q hclosed).ι

/-- Reducedness descends from the two actual reduced open pieces. Each
stalk of the glued scheme injects into the isomorphic stalk of its piece. -/
theorem scheme_isReduced (hq : q.asIdeal ≠ ⊥) :
    IsReduced (scheme j q hclosed) := by
  letI : IsDomain R := affine_open_chart_isDomain_of_integral j q
  letI : IsIntegral (AffineBlowup.scheme q.asIdeal) :=
    AffineBlowup.scheme_isIntegral q.asIdeal hq
  letI : IsIntegral (puncture j q hclosed).toScheme := puncture_isIntegral j q hclosed hq
  haveI : ∀ z : scheme j q hclosed,
      _root_.IsReduced ((scheme j q hclosed).presheaf.stalk z) := by
    intro z
    rcases pieces_cover j q hclosed z with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact isReduced_of_injective ((affineBlowupι j q hclosed).stalkMap a).hom
        (asIso ((affineBlowupι j q hclosed).stalkMap a)).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective ((complementι j q hclosed).stalkMap b).hom
        (asIso ((complementι j q hclosed).stalkMap b)).commRingCatIsoToRingEquiv.injective
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

/-- The actual Rees open is dense in the glued source. The nonempty open
overlap is dense in the integral puncture; coverage and the actual gluing
identity transfer that density to the complete glued scheme. -/
theorem affineBlowupι_dense (hq : q.asIdeal ≠ ⊥) :
    Dense (Set.range (affineBlowupι j q hclosed).base) := by
  letI : IsIntegral (puncture j q hclosed).toScheme := puncture_isIntegral j q hclosed hq
  let w : overlap q := Classical.choice (overlap_nonempty j q hq)
  have hoverlap : Dense (Set.range (overlapToPuncture j q hclosed).base) :=
    (overlapToPuncture j q hclosed).isOpenEmbedding.isOpen_range.dense
      ⟨(overlapToPuncture j q hclosed).base w, ⟨w, rfl⟩⟩
  have hsub : (complementι j q hclosed).base ''
      Set.range (overlapToPuncture j q hclosed).base ⊆
      Set.range (affineBlowupι j q hclosed).base := by
    rintro z ⟨b, ⟨t, rfl⟩, rfl⟩
    refine ⟨(overlapOpen q).ι.base t, ?_⟩
    exact congrArg (fun f : overlap q ⟶ scheme j q hclosed => f.base t)
      (overlapIsPullback j q hclosed).w
  intro z
  rcases pieces_cover j q hclosed z with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact subset_closure ⟨a, rfl⟩
  · exact closure_mono hsub
      (image_closure_subset_closure_image (complementι j q hclosed).continuous
        ⟨b, hoverlap b, rfl⟩)

/-- The dense image of the actual integral Rees piece proves irreducibility
of the whole glued source. -/
theorem scheme_irreducibleSpace (hq : q.asIdeal ≠ ⊥) :
    IrreducibleSpace (scheme j q hclosed) := by
  letI : IsDomain R := affine_open_chart_isDomain_of_integral j q
  letI : IsIntegral (AffineBlowup.scheme q.asIdeal) :=
    AffineBlowup.scheme_isIntegral q.asIdeal hq
  have hirr : IsIrreducible (Set.range (affineBlowupι j q hclosed).base) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (AffineBlowup.scheme q.asIdeal)).image
        (affineBlowupι j q hclosed).base (affineBlowupι j q hclosed).continuous.continuousOn
  have hwhole : IsIrreducible (Set.univ : Set (scheme j q hclosed)) := by
    simpa only [(affineBlowupι_dense j q hclosed hq).closure_eq] using hirr.closure
  exact (irreducibleSpace_def (scheme j q hclosed)).mpr hwhole

/-- Integrality of the constructed point blowup follows from the preceding
actual topology and stalk proofs. -/
theorem scheme_isIntegral (hq : q.asIdeal ≠ ⊥) :
    IsIntegral (scheme j q hclosed) := by
  letI : IsReduced (scheme j q hclosed) := scheme_isReduced j q hclosed hq
  letI : IrreducibleSpace (scheme j q hclosed) := scheme_irreducibleSpace j q hclosed hq
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The original generic point lies in the actual puncture, since that
open subset has a proved point. -/
theorem genericPoint_mem_puncture (hq : q.asIdeal ≠ ⊥) :
    genericPoint X ∈ puncture j q hclosed := by
  let b : (puncture j q hclosed).toScheme :=
    Classical.choice (puncture_nonempty j q hclosed hq)
  exact ((genericPoint_spec X).mem_open_set_iff (puncture j q hclosed).isOpen).mpr
    ⟨b.val, Set.mem_univ _, b.property⟩

/-- The actual projection is an isomorphism over its actual puncture. -/
theorem projection_restrict_puncture_isIso :
    IsIso ((projection j q hclosed) ∣_ puncture j q hclosed) := by
  rw [← punctureIso_hom]
  infer_instance

/-- The actual generic point of the glued integral source maps to the
actual generic point of the original scheme. Both are compared through
the same unchanged open, with its proved composition to the base. -/
theorem projection_genericPoint (hq : q.asIdeal ≠ ⊥) :
    letI : IsIntegral (scheme j q hclosed) := scheme_isIntegral j q hclosed hq
    (projection j q hclosed).base (genericPoint (scheme j q hclosed)) = genericPoint X := by
  letI : IsIntegral (scheme j q hclosed) := scheme_isIntegral j q hclosed hq
  letI : IsIntegral (puncture j q hclosed).toScheme := puncture_isIntegral j q hclosed hq
  have hsource := genericPoint_eq_of_isOpenImmersion (complementι j q hclosed)
  calc
    (projection j q hclosed).base (genericPoint (scheme j q hclosed)) =
        (projection j q hclosed).base
          ((complementι j q hclosed).base (genericPoint (puncture j q hclosed).toScheme)) :=
      congrArg (projection j q hclosed).base hsource.symm
    _ = (puncture j q hclosed).ι.base (genericPoint (puncture j q hclosed).toScheme) :=
      congrArg (fun f : (puncture j q hclosed).toScheme ⟶ X =>
        f.base (genericPoint (puncture j q hclosed).toScheme))
        (complementι_projection j q hclosed)
    _ = genericPoint X := genericPoint_eq_of_isOpenImmersion (puncture j q hclosed).ι

end KltDP.Geometry.PointBlowupGluing
