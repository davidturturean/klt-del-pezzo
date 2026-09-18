import KltDP.Geometry.AffineSmoothLocalizationTransport

/-! Stacks 00TA, the individually stated FIRST cover assertion of Lemma 10.137.9,
 frozen revision a04446e57ec1fbc252a871afcec7752fb2807b14.
 Isolated literal admitted by admission_review/ROOT_CANDIDATE_ADMISSION_DECISION.json.
 This entry authorizes the actual standard-open localization cover only.
 The separate syntomic conclusion is not represented or supplied. -/

universe u
namespace KltDP.Literature.Stacks

axiom smooth_standardSmooth_cover_literal
    (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (hsmooth :
      letI : Algebra R S := φ.toAlgebra
      Algebra.Smooth R S) :
    ∃ T : Set S, Ideal.span T = ⊤ ∧
      ∀ g ∈ T, RingHom.IsStandardSmooth
        ((algebraMap S (Localization.Away g)).comp φ)

end KltDP.Literature.Stacks
#check @KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal
#print axioms KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal
