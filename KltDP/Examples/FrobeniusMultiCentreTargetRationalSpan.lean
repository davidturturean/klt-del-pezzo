import KltDP.Examples.FrobeniusMultiCentreRationalGeneratorSpan
import KltDP.Examples.FrobeniusMultiCentrePicardGeneration

/-!
# The actual target rational Weil class group is spanned by the original line

Original source Picard generation and actual birational class pushforward
surjectivity put every integral target class in the span already proved
for the original generators. The existing positive integral multiple of
each rational divisor then gives the entire original rational Weil class
group. This is a rational Weil-class statement; the original numerical
Picard-rank endpoint requires its separate comparison theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreTargetRationalSpan

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusProjectivityProved
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusMultiCentreSemiampleConstruction
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentrePicardGeneration
open FrobeniusMultiCentrePicardPushforwardSurjective FrobeniusMultiCentreRationalPicardPushforward
open FrobeniusMultiCentreRationalGeneratorSpan InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme) [IsProper π]
    (hbir : IsBirationalScheme π)
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    [Surjective π] [IsIso π.c]
    (hn : 2 < n)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)

include hbir hπ hcriterion hn hconnected hm e in
/-- Every actual integral target class rationalizes into the actual line span. -/
theorem integral_image_mem_span (c : Y.WeilClassGroup) :
    Y.weilClassRationalization c ∈ Submodule.span ℚ
      {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))} := by
  obtain ⟨b, hb⟩ := original_sourcePicardPushforward_surjective q n a ha π hbir c
  obtain ⟨v, hv⟩ := realization_surjective q n a ha b
  have h := realization_image_mem_span q n a ha π hbir
    (hπ := hπ) (hcriterion := hcriterion) (hn := hn) (hconnected := hconnected)
    (A := A) (m := m) (hm := hm) (e := e) v
  have heq : rationalPicardPushforward q n a ha π hbir (realization q n a v) =
      Y.weilClassRationalization c :=
    (congrArg (rationalPicardPushforward q n a ha π hbir) hv).trans
      (congrArg Y.weilClassRationalization hb)
  exact heq ▸ h

include hbir hπ hcriterion hn hconnected hm e in
/-- Denominator clearing upgrades the actual integral-class result to every rational class. -/
theorem rational_class_mem_span (c : Y.RationalWeilClassGroup) :
    c ∈ Submodule.span ℚ
      {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))} := by
  obtain ⟨D, rfl⟩ := Y.rationalPrincipalSubmodule.mkQ_surjective c
  obtain ⟨l, hl, E, hE⟩ := Y.exists_positive_integral_multiple D
  let H : Submodule ℚ Y.RationalWeilClassGroup := Submodule.span ℚ
    {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))}
  change Y.rationalWeilClassMap D ∈ H
  have heq : (l : ℤ) • Y.rationalWeilClassMap D =
      Y.weilClassRationalization (Y.weilClassMap E) := by
    rw [natCast_zsmul, Y.weilClassRationalization_class]
    exact (Y.rationalWeilClassMap.toAddMonoidHom.map_nsmul D l).symm.trans
      (congrArg Y.rationalWeilClassMap hE.symm)
  have hint : Y.weilClassRationalization (Y.weilClassMap E) ∈ H :=
    integral_image_mem_span q n a ha π hbir
      (hπ := hπ) (hcriterion := hcriterion) (hn := hn) (hconnected := hconnected)
      (A := A) (m := m) (hm := hm) (e := e) (Y.weilClassMap E)
  have hz : (l : ℤ) • Y.rationalWeilClassMap D ∈ H := heq.symm ▸ hint
  have hlQ : ((l : ℤ) : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hl))
  apply (H.smul_mem_iff hlQ).mp
  exact (Int.cast_smul_eq_zsmul ℚ (l : ℤ) (Y.rationalWeilClassMap D)).symm ▸ hz

include hbir hπ hcriterion hn hconnected hm e in
/-- Every original target rational Weil class is a scalar of the original line class. -/
theorem rationalWeilClass_eq_smul (c : Y.RationalWeilClassGroup) :
    ∃ t : ℚ, c = t •
      Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (rational_class_mem_span q n a ha π hbir
      (hπ := hπ) (hcriterion := hcriterion) (hn := hn) (hconnected := hconnected)
      (A := A) (m := m) (hm := hm) (e := e) c)
  exact ⟨t, ht.symm⟩

include hbir hπ hcriterion hn hconnected hm e in
/-- The span here is the whole original rational Weil class group. -/
theorem target_line_span_eq_top :
    Submodule.span ℚ
      {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))} = ⊤ := by
  apply top_unique
  intro c _
  exact rational_class_mem_span q n a ha π hbir
    (hπ := hπ) (hcriterion := hcriterion) (hn := hn) (hconnected := hconnected)
    (A := A) (m := m) (hm := hm) (e := e) c

end KltDP.Examples.FrobeniusMultiCentreTargetRationalSpan
