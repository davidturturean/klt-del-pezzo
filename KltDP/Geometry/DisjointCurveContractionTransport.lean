import KltDP.Geometry.PrimeCurveImageOnIsomorphismOpen
import KltDP.Geometry.ActualContractionMorphismDescent
import KltDP.Geometry.SchemePointBlowupSequenceRestriction

/-!
# Preserve every original curve disjoint from an actual contracted curve

The actual exceptional fiber identifies the isomorphism open containing
all disjoint original curves. Their original closed images, curve-scheme
isomorphisms, self-intersections and pairwise disjointness are derived.
The returned function names actual images under the same original map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

namespace CurveOnIsomorphismOpen

/-- Images of disjoint curves stay disjoint under the actual isomorphism open. -/
theorem imageCurve_disjoint
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    (C D : S.PrimeCurve) (b : S.toScheme ⟶ T.toScheme) [IsProper b]
    (U : T.toScheme.Opens) [IsIso (b ∣_ U)]
    (hC : Set.range C.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme))
    (hD : Set.range D.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme))
    (hCD : Disjoint (C : Set S.toScheme) (D : Set S.toScheme)) :
    Disjoint (imageCurve C b U hC : Set T.toScheme) (imageCurve D b U hD : Set T.toScheme) := by
  apply Set.disjoint_left.mpr
  intro t htC htD
  rw [coe_imageCurve] at htC htD
  obtain ⟨x, hx, hbx⟩ := htC
  obtain ⟨y, hy, hby⟩ := htD
  have hxU : b.base x ∈ U := hC (by rwa [C.range_inclusion])
  have hyU : b.base y ∈ U := hD (by rwa [D.range_inclusion])
  have hxy : x = y := eq_of_isIso_restrict b hxU hyU (hbx.trans hby.symm)
  exact (Set.disjoint_left.mp hCD) (hxy ▸ hx) hy

end CurveOnIsomorphismOpen

set_option maxHeartbeats 800000 in
/-- A single actual contraction transports all disjoint original curves
at once, preserving their actual images, scheme maps and intersection numbers. -/
theorem IsContraction.exists_disjointCurveTransport
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) :
    ∃ F : {C : S.PrimeCurve // Disjoint (C : Set S.toScheme) (E : Set S.toScheme)} → T.PrimeCurve,
      (∀ C, b.base '' (C.val : Set S.toScheme) = (F C : Set T.toScheme) ∧
        ∃ e : (F C).toScheme ≅ C.val.toScheme,
          e.hom ≫ (C.val.inclusion ≫ b) = (F C).inclusion ∧
          e.hom ≫ C.val.toSpec = (F C).toSpec ∧
          (F C).selfIntersectionNumber hb.regular = C.val.selfIntersectionNumber hS) ∧
      (∀ C D, Disjoint (C.val : Set S.toScheme) (D.val : Set S.toScheme) →
        Disjoint (F C : Set T.toScheme) (F D : Set T.toScheme)) := by
  obtain ⟨z, hz, hfiber, hbl⟩ := hb.centerFiber_eq_curve
  let U : T.toScheme.Opens := ⟨({z} : Set T.toScheme)ᶜ, hz.isOpen_compl⟩
  letI : IsIso (b ∣_ U) := hbl.toSchemeIsAt.isIso_restrict U (by simp [U])
  letI : IsProper b := hb.isProper
  have hU (C : {C : S.PrimeCurve // Disjoint (C : Set S.toScheme) (E : Set S.toScheme)}) :
      Set.range C.val.inclusion.base ⊆ ((b ⁻¹ᵁ U : S.toScheme.Opens) : Set S.toScheme) := by
    intro x hx
    rw [C.val.range_inclusion] at hx
    change b.base x ≠ z
    intro hbx
    have hxE : x ∈ (E : Set S.toScheme) := by rw [← hfiber]; exact hbx
    exact (Set.disjoint_left.mp C.property) hx hxE
  let F : {C : S.PrimeCurve //
      Disjoint (C : Set S.toScheme) (E : Set S.toScheme)} → T.PrimeCurve :=
    fun C => CurveOnIsomorphismOpen.imageCurve C.val b U (hU C)
  refine ⟨F, ?_, ?_⟩
  · intro C
    constructor
    · exact (CurveOnIsomorphismOpen.coe_imageCurve C.val b U (hU C)).symm
    · refine ⟨CurveOnIsomorphismOpen.imageCurveSourceIso C.val b U (hU C), ?_, ?_, ?_⟩
      · exact CurveOnIsomorphismOpen.imageCurveSourceIso_hom_map C.val b U (hU C)
      · exact CurveOnIsomorphismOpen.imageCurveSourceIso_over_base C.val b U (hU C)
          hb.over_base
      · exact CurveOnIsomorphismOpen.imageCurve_selfIntersection C.val b U (hU C)
          hS hb.regular hb.over_base
  · intro C D hCD
    exact CurveOnIsomorphismOpen.imageCurve_disjoint C.val D.val b U (hU C) (hU D) hCD

end KltDP.Geometry

#print axioms KltDP.Geometry.IsContraction.exists_disjointCurveTransport
