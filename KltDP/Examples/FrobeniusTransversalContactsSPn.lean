import KltDP.Examples.FrobeniusNewestTransversality
import KltDP.Examples.FrobeniusIncidenceSPn

/-!
# Transversal contacts on `S_{p,n}`

At the unique point `x_i` of `B ∩ P_i` (resp. `F_i ∩ P_i`, BRIEF10) the tower projection `τ_i` is an
isomorphism on the open neighbourhood `isoPreimage q n a i` (`isoMap` is an open immersion, so its stalk
maps are isomorphisms), and `τ_i x_i` is the contact point `contactPoint q n a i` (resp. the centre point
`fiberPoint q n a i`) of the tower `T_i`, where the newest exceptional curve `P_i` is `u = 0`
(`chart_mem_previousFiber_iff`) and the pulled exceptional equation has contact length one on the
closure (`closure_terminal_exceptional_contact_length`) resp. on the strict fibre
(`fiberClosure_exceptional_contact_length`). The bundle `sPn_transversal_contacts` records exactly these
facts: the contact lengths are computed on the tower's curves at the image points, and `τ_i` is the
local isomorphism carrying `x_i` there (the scheme-level identification of `B` with the tower closure over
the isomorphism open is not part of this module).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusTransversalContactsSPn

open KltDP.Geometry FrobeniusBlowupContact FrobeniusGlobalBlowupStages
  FrobeniusStrictTransformClosure FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusClosureContact
  FrobeniusFiberClosure FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusClosureNewestUnique FrobeniusIncidenceSPn
  FrobeniusNewestTransversality

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The tower projection is a local isomorphism at every point of the isomorphism open. -/
theorem isoMap_stalkMap_isIso (i : Fin n) (y : (isoPreimage q n a i).toScheme) :
    IsIso ((isoMap q n a i).stalkMap y) :=
  inferInstance

/-- A point of `F_i ∩ P_i` maps to the centre point of the strict fibre of `T_i`. -/
theorem fiberStrict_newest_projection (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)) :
    (towerProjection (q + 1) n a i).base x = fiberPoint q n a i := by
  apply fiberClosure_newest_unique (translatedInitial (q + 1) (a i)) q
  · exact fiberStrict_projection_mem_towerStrict q n a i x hx.1
  · have h := hx.2
    rw [exceptionalSupport_eq] at h
    exact h

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- A point of `B ∩ P_i` maps to the contact point of the closure of `T_i`. -/
theorem graphStrict_newest_projection (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit)) :
    (towerProjection (q + 1) n a i).base x = contactPoint q n a i := by
  apply closure_newest_unique (translatedInitial (q + 1) (a i)) q
  · exact graphStrict_projection_mem_towerStrict q n a i x hx.1
  · have h := hx.2
    rw [exceptionalSupport_eq] at h
    exact h

end Graph

end KltDP.Examples.FrobeniusTransversalContactsSPn

namespace KltDP.Examples

open KltDP.Geometry FrobeniusBlowupContact FrobeniusTranslatedCharts FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusClosureContact
  FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreFiberContacts FrobeniusIncidenceSPn
  FrobeniusNewestTransversality FrobeniusTransversalContactsSPn

/-- Bundle: transversal contacts on `S_{p,n}`. For every `i`: `B ∩ P_i` is a single point `x`, lying in
the isomorphism open of `T_i` and mapped by `τ_i` to the contact point of the tower closure, where the
exceptional equation has contact length one; the same for `F_i ∩ P_i` with the centre point of the strict
fibre; and `τ_i` is a local isomorphism (isomorphic stalk maps) on the isomorphism open. -/
theorem sPn_transversal_contacts (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    (∀ i : Fin n, ∃ x, Set.range (graphStrictι (q + 1) n a).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x} ∧ x ∈ isoPreimage q n a i ∧
      (towerProjection (q + 1) n a i).base x = contactPoint q n a i) ∧
    (∀ i : Fin n, Module.length (closureContactStalk (translatedInitial (q + 1) (a i)) (q + 1) 0)
      (closureContactStalk (translatedInitial (q + 1) (a i)) (q + 1) 0 ⧸
        Ideal.span {closureContactGerm (translatedInitial (q + 1) (a i)) q 0 chartU}) = 1) ∧
    (∀ i : Fin n, ∃ x, Set.range (fiberStrictι (q + 1) n a i).base ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit) = {x} ∧ x ∈ isoPreimage q n a i ∧
      (towerProjection (q + 1) n a i).base x = fiberPoint q n a i) ∧
    (∀ i : Fin n, Module.length (fiberContactStalk (translatedInitial (q + 1) (a i)) (q + 1))
      (fiberContactStalk (translatedInitial (q + 1) (a i)) (q + 1) ⧸
        Ideal.span {fiberContactGerm (translatedInitial (q + 1) (a i)) q chartU}) = 1) ∧
    (∀ (i : Fin n) (y : (isoPreimage q n a i).toScheme), IsIso ((isoMap q n a i).stalkMap y)) := by
  refine ⟨fun i => ?_, fun i => closure_terminal_exceptional_contact_length _ q, fun i => ?_,
    fun i => fiberClosure_exceptional_contact_length _ q, fun i y => isoMap_stalkMap_isIso q n a i y⟩
  · obtain ⟨x, hx⟩ := graphStrict_inter_newest_eq_singleton q n a ha i
    have hmem : x ∈ Set.range (graphStrictι (q + 1) n a).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hx]
      exact Set.mem_singleton x
    exact ⟨x, hx, newest_mem_isoPreimage q n a ha i x hmem.2,
      graphStrict_newest_projection q n a i x hmem⟩
  · obtain ⟨x, hx⟩ := fiberStrict_inter_newest_eq_singleton q n a ha i
    have hmem : x ∈ Set.range (fiberStrictι (q + 1) n a i).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hx]
      exact Set.mem_singleton x
    exact ⟨x, hx, newest_mem_isoPreimage q n a ha i x hmem.2,
      fiberStrict_newest_projection q n a i x hmem⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_transversal_contacts_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := sPn_transversal_contacts.{u} k q n a ha
  trivial

end KltDP.Examples
