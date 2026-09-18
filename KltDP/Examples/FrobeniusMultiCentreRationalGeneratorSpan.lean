import KltDP.Examples.FrobeniusMultiCentreRationalPicardPushforward
import KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Original source generators map into the actual target line span

The original graph, strict fibre and old exceptional classes have zero
actual rational pushforward. Their original Picard rows identify every
total exceptional image and both ruling images with the rational span
of the original target line. The original pullback-line isomorphism is
used with its positive exponent m. No class vanishing or span statement
is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRationalGeneratorSpan

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusProjectivityProved
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusMultiCentreSemiampleConstruction
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreGraphCartierStrict
open FrobeniusMultiCentreGraphPicardClass FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentrePicardRealization
open FrobeniusMultiCentreRationalPicardPushforward InvertibleSheafSectionPowers

private theorem mem_of_zsmul_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : Submodule ℚ V) {z : ℤ} {x : V} (hz : z ≠ 0) (h : z • x ∈ H) : x ∈ H := by
  apply (H.smul_mem_iff (Int.cast_ne_zero.mpr hz : (z : ℚ) ≠ 0)).mp
  exact (Int.cast_smul_eq_zsmul ℚ z x).symm ▸ h

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

include hπ hcriterion hn hconnected hm e in
/-- Every vector under the original realization maps into the actual target line span. -/
theorem realization_image_mem_span (v : FrobeniusPicard.PicardVector (q + 1) n) :
    rationalPicardPushforward q n a ha π hbir (realization q n a v) ∈
      Submodule.span ℚ
        {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))} := by
  classical
  let F := rationalPicardPushforward q n a ha π hbir
  let H : Submodule ℚ Y.RationalWeilClassGroup := Submodule.span ℚ
    {Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic))}
  change F (realization q n a v) ∈ H
  have hA : Y.weilClassRationalization
      (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) ∈ H :=
    Submodule.subset_span (Set.mem_singleton _)
  have hgraph : F (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 :=
    graph_image_eq_zero q n a ha π hbir (hπ := hπ) (hcriterion := hcriterion)
  have hpower : (m : ℤ) • F (contractingClass q n a ha) =
      Y.weilClassRationalization (Y.picardToWeilClassHom (Additive.ofMul A.toPic)) :=
    power_image_eq q n a ha π hbir (hπ := hπ) (hcriterion := hcriterion)
      hn hconnected A m e
  have hM : F (contractingClass q n a ha) ∈ H :=
    mem_of_zsmul_mem H (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hm)) (hpower.symm ▸ hA)
  have hsecond : F (multiSecondFiberClass (q + 1) n a) ∈ H := by
    have hnZ : (2 : ℤ) < n := by exact_mod_cast hn
    apply mem_of_zsmul_mem H (ne_of_gt (sub_pos.mpr hnZ))
    simpa only [contractingClass, map_add, map_zsmul, hgraph, zero_add] using hM
  have hchain (i : Fin n) (j : Fin q) :
      F (exceptionalClass (q + 1) n a i j.castSucc) =
        F (exceptionalClass (q + 1) n a i j.succ) := by
    have h := congrArg F (chainClass_SPn q n a ha i j)
    have hz := old_exceptional_image_eq_zero q n a ha π hbir
      (hπ := hπ) (hcriterion := hcriterion) i j
    apply sub_eq_zero.mp
    exact (map_sub F _ _).symm.trans (h.symm.trans hz)
  have hconstant (i : Fin n) (j : Fin (q + 1)) :
      F (exceptionalClass (q + 1) n a i j) =
        F (exceptionalClass (q + 1) n a i 0) := by
    refine Fin.induction ?_ (fun j ih => ?_) j
    · rfl
    · exact (hchain i j).symm.trans ih
  have hfiber (i : Fin n) : F (multiSecondFiberClass (q + 1) n a) =
      (q + 1) • F (exceptionalClass (q + 1) n a i 0) := by
    have h := congrArg F (fiberClass_SPn q n a ha i)
    have hz := fiber_image_eq_zero q n a ha π hbir
      (hπ := hπ) (hcriterion := hcriterion) i
    have hdiff : F (multiSecondFiberClass (q + 1) n a) -
        ∑ j : Fin (q + 1), F (exceptionalClass (q + 1) n a i j) = 0 := by
      simpa only [map_sub, map_sum] using h.symm.trans hz
    calc
      F (multiSecondFiberClass (q + 1) n a) =
          ∑ j : Fin (q + 1), F (exceptionalClass (q + 1) n a i j) :=
        sub_eq_zero.mp hdiff
      _ = ∑ _j : Fin (q + 1), F (exceptionalClass (q + 1) n a i 0) :=
        Finset.sum_congr rfl (fun j _ => hconstant i j)
      _ = (q + 1) • F (exceptionalClass (q + 1) n a i 0) := by simp
  have hexceptional (i : Fin n) (j : Fin (q + 1)) :
      F (exceptionalClass (q + 1) n a i j) ∈ H := by
    rw [hconstant i j]
    apply mem_of_zsmul_mem H
      (Int.natCast_ne_zero.mpr (Nat.succ_ne_zero q))
    rw [natCast_zsmul, ← hfiber i]
    exact hsecond
  have hsum : (∑ i : Fin n, ∑ j : Fin (q + 1),
      F (exceptionalClass (q + 1) n a i j)) ∈ H :=
    H.sum_mem (fun i _ => H.sum_mem (fun j _ => hexceptional i j))
  have hfirst : F (multiFirstFiberClass (q + 1) n a) ∈ H := by
    have h := (congrArg F (strictGraphKernelLine_picard_row q n a ha)).symm.trans hgraph
    have hrow : (q + 1) • F (multiFirstFiberClass (q + 1) n a) +
        F (multiSecondFiberClass (q + 1) n a) -
          ∑ i : Fin n, ∑ j : Fin (q + 1),
            F (exceptionalClass (q + 1) n a i j) = 0 := by
      simpa only [map_sub, map_add, map_nsmul, map_sum] using h
    have hfirst_eq : (q + 1) • F (multiFirstFiberClass (q + 1) n a) =
        (∑ i : Fin n, ∑ j : Fin (q + 1), F (exceptionalClass (q + 1) n a i j)) -
          F (multiSecondFiberClass (q + 1) n a) :=
      eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hrow)
    apply mem_of_zsmul_mem H
      (Int.natCast_ne_zero.mpr (Nat.succ_ne_zero q))
    rw [natCast_zsmul, hfirst_eq]
    exact H.sub_mem hsum hsecond
  simp only [realization_apply, map_add, map_zsmul, map_sum]
  exact H.add_mem
    (H.add_mem (H.toAddSubgroup.zsmul_mem hfirst v.1)
      (H.toAddSubgroup.zsmul_mem hsecond v.2.1))
    (H.sum_mem (fun i _ => H.sum_mem (fun j _ =>
      H.toAddSubgroup.zsmul_mem (hexceptional i j) (v.2.2 (i, j)))))

end KltDP.Examples.FrobeniusMultiCentreRationalGeneratorSpan
