import KltDP.Geometry.AffineStalkCompletion

/-! Zariski, Ann. Inst. Fourier 2 (1950), Theorem 2, printed page 162.
Closed points of the original integral affine variety; full local-domain
and integral-closedness conclusion for the original maximal-ideal completion.
Isolated admission: admission_review/ROOT_CANDIDATE_ADMISSION_DECISION.json.
The field chosen internally in the published proof adds no premise here. -/

universe u
namespace KltDP.Literature.Zariski

axiom closedPoint_normal_completion_literal
    (k : Type u) [Field k]
    (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    (p : Ideal B) [p.IsMaximal]
    [IsIntegrallyClosed (Localization.AtPrime p)] :
    IsLocalRing
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsDomain
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsIntegrallyClosed
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p))

end KltDP.Literature.Zariski
#check @KltDP.Literature.Zariski.closedPoint_normal_completion_literal
#print axioms KltDP.Literature.Zariski.closedPoint_normal_completion_literal
