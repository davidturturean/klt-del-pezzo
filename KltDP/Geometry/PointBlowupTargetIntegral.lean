import KltDP.Geometry.PointBlowupCenterIrreducible
import KltDP.Geometry.PointBlowupTargetRegular
import KltDP.Geometry.SchemePointBlowupSequence
import KltDP.Geometry.MinimalResolutionDebts

/-!
# Integrality of the original raw point-blowup target

The actual center fiber supplies a point over the center, and the unchanged
complement supplies points everywhere else. The original surjective map
therefore transfers irreducibility from its integral source. The original
regular center and source give regular target stalks, hence reducedness.
The target is an arbitrary scheme; integrality is derived, not supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Actual surjectivity includes the center and the unchanged complement. -/
theorem PointBlowupGluing.projection_surjective_of_regular_center
    {R : Type u} [CommRing R] {T : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ T) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set T))
    (hcenter : RegularPoint T (j.base q))
    (hdim : ringKrullDim (T.presheaf.stalk (j.base q)) = 2) :
    Surjective (PointBlowupGluing.projection j q hclosed) := by
  constructor
  intro t
  by_cases ht : t = j.base q
  · obtain ⟨s, hs⟩ := (PointBlowupGluing.pointFiber_isIrreducible
      j q hclosed hcenter hdim).1
    change (PointBlowupGluing.projection j q hclosed).base s = j.base q at hs
    exact ⟨s, hs.trans ht.symm⟩
  · let t' : (PointBlowupGluing.puncture j q hclosed).toScheme := ⟨t, ht⟩
    refine ⟨(PointBlowupGluing.complementι j q hclosed).base t', ?_⟩
    have h := congrArg (fun f : (PointBlowupGluing.puncture j q hclosed).toScheme ⟶ T =>
      f.base t') (PointBlowupGluing.complementι_projection j q hclosed)
    exact h

namespace SchemePointBlowup

/-- Surjectivity for the same original scheme morphism and center. -/
theorem IsAt.surjective_of_regular_center {S T : Scheme.{u}} {f : S ⟶ T} {z : T}
    (h : IsAt f z) (hcenter : RegularPoint T z)
    (hdim : ringKrullDim (T.presheaf.stalk z) = 2) : Surjective f := by
  obtain ⟨c, e, he⟩ := h
  letI : CommRing c.R := c.instCommRing
  letI : IsOpenImmersion c.j := c.instOpenImmersion
  letI : c.q.asIdeal.IsMaximal := c.instMaximal
  have hdim' := (congrArg (fun p : T => ringKrullDim (T.presheaf.stalk p))
    c.base_eq).trans hdim
  letI : Surjective c.projection := PointBlowupGluing.projection_surjective_of_regular_center
    c.j c.q c.isClosed (by simpa only [c.base_eq] using hcenter) hdim'
  rw [← he]
  infer_instance

/-- Regularity of the original raw target, without a surface package. -/
theorem IsAt.target_regular {S T : Scheme.{u}} {f : S ⟶ T} {z : T}
    (h : IsAt f z) (hregular : ∀ s : S, RegularPoint S s)
    (hcenter : RegularPoint T z) : ∀ t : T, RegularPoint T t := by
  obtain ⟨c, e, -⟩ := h
  exact c.target_regular e hregular hcenter

/-- An original integral regular source and regular two-dimensional center
make the arbitrary original target integral. No target irreducibility,
reducedness, normality, or birationality hypothesis is supplied. -/
theorem IsAt.target_isIntegral {S T : Scheme.{u}} [IsIntegral S]
    {f : S ⟶ T} {z : T} (h : IsAt f z)
    (hregular : ∀ s : S, RegularPoint S s) (hcenter : RegularPoint T z)
    (hdim : ringKrullDim (T.presheaf.stalk z) = 2) : IsIntegral T := by
  letI : Surjective f := h.surjective_of_regular_center hcenter hdim
  letI : IrreducibleSpace T := by
    apply (irreducibleSpace_def T).mpr
    change IsIrreducible (Set.univ : Set T)
    rw [← Set.range_eq_univ.mpr f.surjective]
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ S).image f.base f.continuous.continuousOn
  have hnormal := isNormalScheme_of_regularPoint (h.target_regular hregular hcenter)
  letI : ∀ t : T, _root_.IsReduced (T.presheaf.stalk t) := fun t => by
    letI : IsDomain (T.presheaf.stalk t) := (hnormal t).1
    infer_instance
  letI : AlgebraicGeometry.IsReduced T := isReduced_of_isReduced_stalk T
  exact isIntegral_of_irreducibleSpace_of_isReduced T

end SchemePointBlowup
end KltDP.Geometry

#print axioms KltDP.Geometry.SchemePointBlowup.IsAt.surjective_of_regular_center
#print axioms KltDP.Geometry.SchemePointBlowup.IsAt.target_isIntegral
