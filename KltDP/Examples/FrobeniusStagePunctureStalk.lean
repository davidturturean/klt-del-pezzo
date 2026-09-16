import KltDP.Geometry.RationalTreePicardRestrictStalk
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusGlobalBlowupStages

/-!
# The stalk transport along the stage puncture (BRIEF23, item 1)

Over the complement of the centre the tower projection is an isomorphism (accepted
`toInitial_restrict_isIso`), so its stalk maps there are isomorphisms. The generic half is already
accepted: `RationalTreePicard.isIso_stalkMap_of_isIso_restrict` says that a morphism whose
restriction over an open `V` of the target is an isomorphism has isomorphic stalk maps at the points
over `V`, proved through `morphismRestrict_ι`, `Scheme.stalkMap_comp` and the open-immersion stalk
isomorphisms. What is new here is the specialisation to the tower, the packaging as a ring
equivalence, and — the part the length computations actually need — the transport of the **germ of a
local equation** through it.

* `toInitial_stalkMap_isIso`: at every point of `stagePuncture A n` the stalk map of `A.toInitial n`
  is an isomorphism. The membership `x ∈ stagePuncture A n` *is* the hypothesis
  `(A.toInitial n).base x ∈ initialPuncture A` of the accepted lemma, because the stage puncture is
  by definition that preimage.
* `stagePunctureStalkEquiv`: the resulting ring equivalence from the stalk of the initial scheme at
  the image to the stalk of the stage at the point.
* **`stagePunctureStalkEquiv_germ`**: it sends the germ of a section `s` of `𝒪` near the image to the
  germ of its pullback `(A.toInitial n).app U s` — this is `Scheme.stalkMap_germ_apply`, and it is
  what carries a local equation upstairs.
* `towerStalkEquiv`, `towerStalkEquiv_germ`: the same for the origin contact tower, i.e. the
  composite down to `P¹ × P¹`, since `projectiveContactProjection N` is by definition
  `(projectiveProductInitial).toInitial N`.

Nothing is assumed. The vertical and graph contact lengths (BRIEF23 items 2 and 3) consume this
module; see the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.StagePunctureStalkTransport

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusStageComplement
open FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k] (A : PlaneChartedScheme k) (n : ℕ)

/-- **The tower projection has isomorphic stalk maps at every point of the stage puncture.** -/
theorem toInitial_stalkMap_isIso (x : (A.stage n).carrier) (hx : x ∈ stagePuncture A n) :
    IsIso ((A.toInitial n).stalkMap x) := by
  haveI := toInitial_restrict_isIso A n
  exact isIso_stalkMap_of_isIso_restrict (A.toInitial n) (initialPuncture A) x hx

/-- **The stalk transport along the stage puncture.** -/
def stagePunctureStalkEquiv (x : (A.stage n).carrier) (hx : x ∈ stagePuncture A n) :
    A.carrier.presheaf.stalk ((A.toInitial n).base x) ≃+*
      (A.stage n).carrier.presheaf.stalk x :=
  haveI := toInitial_stalkMap_isIso A n x hx
  (asIso ((A.toInitial n).stalkMap x)).commRingCatIsoToRingEquiv

/-- **The germ of a local equation is carried to the germ of its pullback.** -/
theorem stagePunctureStalkEquiv_germ (x : (A.stage n).carrier) (hx : x ∈ stagePuncture A n)
    (U : A.carrier.Opens) (hU : (A.toInitial n).base x ∈ U) (s : Γ(A.carrier, U)) :
    stagePunctureStalkEquiv A n x hx
        (A.carrier.presheaf.germ U ((A.toInitial n).base x) hU s) =
      (A.stage n).carrier.presheaf.germ ((A.toInitial n) ⁻¹ᵁ U) x hU
        ((A.toInitial n).app U s) := by
  change (A.toInitial n).stalkMap x (A.carrier.presheaf.germ U ((A.toInitial n).base x) hU s) = _
  exact Scheme.stalkMap_germ_apply (A.toInitial n) U x hU s

section Tower

variable (N : ℕ)

/-- **The stalk transport for the origin contact tower**: the composite down to `P¹ × P¹`. -/
def towerStalkEquiv (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N) :
    (FrobeniusProjectivePoints.projectiveProduct k).presheaf.stalk
        ((projectiveContactProjection (k := k) N).base x) ≃+*
      (projectiveContactStage (k := k) N).presheaf.stalk x :=
  stagePunctureStalkEquiv (projectiveProductInitial (k := k)) N x hx

/-- The germ of a local equation on `P¹ × P¹` is carried to the germ of its pullback on the stage. -/
theorem towerStalkEquiv_germ (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (U : (FrobeniusProjectivePoints.projectiveProduct k).Opens)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ U)
    (s : Γ(FrobeniusProjectivePoints.projectiveProduct k, U)) :
    towerStalkEquiv N x hx
        ((FrobeniusProjectivePoints.projectiveProduct k).presheaf.germ U
          ((projectiveContactProjection (k := k) N).base x) hU s) =
      (projectiveContactStage (k := k) N).presheaf.germ
        ((projectiveContactProjection (k := k) N) ⁻¹ᵁ U) x hU
        ((projectiveContactProjection (k := k) N).app U s) :=
  stagePunctureStalkEquiv_germ (projectiveProductInitial (k := k)) N x hx U hU s

end Tower

end KltDP.Examples.StagePunctureStalkTransport

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageComplement
open FrobeniusStageComplement.PlaneChartedScheme StagePunctureStalkTransport

/-- **F29: the stalk transport along the stage puncture**, with the germ of a local equation carried
through it. -/
theorem f29_stage_puncture_stalk_transport (k : Type u) [Field k] (N : ℕ)
    (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N) :
    IsIso ((projectiveContactProjection (k := k) N).stalkMap x) ∧
    ∀ (U : (FrobeniusProjectivePoints.projectiveProduct k).Opens)
      (hU : (projectiveContactProjection (k := k) N).base x ∈ U)
      (s : Γ(FrobeniusProjectivePoints.projectiveProduct k, U)),
      towerStalkEquiv N x hx
          ((FrobeniusProjectivePoints.projectiveProduct k).presheaf.germ U
            ((projectiveContactProjection (k := k) N).base x) hU s) =
        (projectiveContactStage (k := k) N).presheaf.germ
          ((projectiveContactProjection (k := k) N) ⁻¹ᵁ U) x hU
          ((projectiveContactProjection (k := k) N).app U s) :=
  ⟨toInitial_stalkMap_isIso (projectiveProductInitial (k := k)) N x hx,
    fun U hU s => towerStalkEquiv_germ N x hx U hU s⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_stage_puncture_stalk_transport_universe_check (k : Type u) [Field k] (N : ℕ)
    (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N) : True := by
  have _ := f29_stage_puncture_stalk_transport.{u} k N x hx
  trivial

end KltDP.Examples
