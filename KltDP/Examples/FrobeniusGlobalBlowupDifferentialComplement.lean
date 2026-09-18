import KltDP.Examples.FrobeniusGlobalBlowupDifferentialAffine
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The actual whole-stage differential is invertible off its exceptional fiber

The original projection on the inverse image of the original puncture is the
already constructed puncture isomorphism followed by the original open
inclusion. The original exterior composition law proves invertibility of the
same pulled next-stage differential, with no new geometric hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupDifferentialComplement

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine

variable {k : Type u} [Field k]

local instance complementOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k)

/-- The actual inverse image of the original punctured scheme. -/
abbrev complementOpen : A.nextScheme.Opens :=
  PointBlowupGluing.exceptionalComplementOpen A.chart (originPoint (k := k)) A.center_closed

/-- The actual projection on this original open is an open immersion. -/
theorem complementProjection_isOpenImmersion :
    IsOpenImmersion ((complementOpen A).ι ≫ A.nextProjection) := by
  change IsOpenImmersion
    (((PointBlowupGluing.projection A.chart (originPoint (k := k)) A.center_closed) ⁻¹ᵁ
      PointBlowupGluing.puncture A.chart (originPoint (k := k)) A.center_closed).ι ≫
        PointBlowupGluing.projection A.chart (originPoint (k := k)) A.center_closed)
  rw [← morphismRestrict_ι, ← PointBlowupGluing.punctureIso_hom]
  infer_instance

/-- The whole original projection differential is invertible on the unchanged complement. -/
theorem complementDifferential_isIso :
    IsIso ((schemeModulePullback (complementOpen A).ι).map (nextDifferentialMap A)) := by
  letI := complementProjection_isOpenImmersion A
  change IsIso ((schemeModulePullback (complementOpen A).ι).map
    (SchemeKaehlerExteriorPullbackTransport.map
      A.structureMap A.nextProjection A.nextStructure rfl 2))
  exact SchemeKaehlerExteriorPullbackTransport.pullback_map_isIso_of_open_comp
    A.structureMap A.nextProjection A.nextStructure rfl 2 (complementOpen A).ι

end KltDP.Examples.FrobeniusGlobalBlowupDifferentialComplement
