import KltDP.Geometry.PartialIsoGraphBirational
import KltDP.Geometry.ProperBirationalSurfacePointBlowupDomination
import KltDP.Geometry.SchemePointBlowupSurfaceSequence
import KltDP.Geometry.SchemePointBlowupSequenceIntegral
import KltDP.Geometry.BirationalSeparatedLeftFactor
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# A common smooth resolution from the actual dense-open isomorphism

The original partial-isomorphism graph has two proper birational projections.
The existing point-blowup domination of its first projection constructs the
common smooth source, whose two original maps are resolutions over the field.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- Birationality over the original field, expressed by an actual dense-open
isomorphism, supplies a common smooth resolution of the original surfaces. -/
theorem exists_common_resolution_of_birationalOver
    {k : Type u} [Field k] [IsAlgClosed k]
    (S T : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]
    (h : Scheme.BirationalOver S.structureMorphism T.structureMorphism) :
    ∃ (Z : NormalProjectiveSurface k) (b : Z.toScheme ⟶ S.toScheme)
        (q : Z.toScheme ⟶ T.toScheme),
      IsResolution Z S b ∧ IsResolution Z T q ∧ IsSmooth Z.structureMorphism ∧
        IsPointBlowupSequence Z S b := by
  letI : IsNoetherian S.toScheme := by
    letI : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
    exact ⟨⟩
  letI : IsProper S.structureMorphism := S.projective.isProper
  letI : IsProper T.structureMorphism := T.projective.isProper
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨G, p, q, hG, h⟩ :=
    exists_proper_birational_graph_of_partialIso
      S.structureMorphism T.structureMorphism φ hφ
  letI := hG
  obtain ⟨hp, hq, hbirp, hbirq, hqp⟩ := h
  letI : IsProper p := hp
  letI : IsProper q := hq
  obtain ⟨Y, b, hb, g, hg⟩ :=
    ProperBirationalSurface.exists_pointBlowup_domination
      S p hbirp S.regularPoints_of_isSmooth
  obtain ⟨U, hU, hpU⟩ := exists_isomorphism_open_of_isBirationalScheme p hbirp
  letI : Nonempty U.toScheme := hU
  have hUmax : U ≤ targetIsomorphismOpen p := fun _ hx => ⟨U, hx, hpU⟩
  have hbU : SchemePointBlowup.SequenceAway S.toScheme (U : Set S.toScheme) Y b :=
    hb.mono hUmax
  letI : IsIntegral Y := hbU.source_isIntegral U
  have hbirb : IsBirationalScheme b := hbU.isBirationalScheme U
  have hbirg : IsBirationalScheme g :=
    isBirationalScheme_left_of_comp_of_isSeparated g p hbirp (by rw [hg]; exact hbirb)
  letI : GenericPointPreserving g := ⟨hbirg.map_genericPoint⟩
  letI : GenericPointPreserving q := ⟨hbirq.map_genericPoint⟩
  have hbirgq : IsBirationalScheme (g ≫ q) :=
    (BirationalComposition.isBirationalScheme_comp_iff g q).mpr ⟨hbirg, hbirq⟩
  let Z : NormalProjectiveSurface k := hbU.sourceSurface S
  have hreg : ∀ y : Z.toScheme, RegularPoint Z.toScheme y := hbU.source_regular S
  have hbk : b ≫ S.structureMorphism = Z.structureMorphism := rfl
  have hqk : (g ≫ q) ≫ T.structureMorphism = Z.structureMorphism := by
    change (g ≫ q) ≫ T.structureMorphism = b ≫ S.structureMorphism
    rw [Category.assoc, hqp, ← Category.assoc, hg]
  exact ⟨Z, b, g ≫ q,
    ⟨hbk, hreg, ⟨hbirb.map_genericPoint, hbirb.isIso_stalkMap_genericPoint⟩⟩,
    ⟨hqk, hreg, ⟨hbirgq.map_genericPoint, hbirgq.isIso_stalkMap_genericPoint⟩⟩,
    hbU.source_isSmooth S, hbU.toSurfaceSequence S⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_common_resolution_of_birationalOver
#print axioms KltDP.Geometry.exists_common_resolution_of_birationalOver
