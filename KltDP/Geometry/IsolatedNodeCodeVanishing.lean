import KltDP.Geometry.IsolatedNodeVanishing
import KltDP.Codes.IntegralNodeCode

/-!
# The actual binary code of all isolated exceptional nodes vanishes

The code is the kernel of the map from binary words to the original
Picard group modulo its actual subgroup of doubles. Its labels are actual
isolated exceptional prime curves of self-intersection minus two.
The support of a codeword gives the integral half-class already ruled out
by the original-surface no-even theorem.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface UnbranchedExceptionalBlocks ActualExceptionalIncidence

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}

/-- Reduction of the original selected prime classes modulo twice Pic(S). -/
def selectedNodePicardCode (π : S.toScheme ⟶ X.toScheme)
    (hmin : IsMinimalResolution S X π) (N : Finset S.PrimeCurve) :
    Submodule (ZMod 2) (KltDP.Codes.BinaryWord {C : S.PrimeCurve // C ∈ N}) := by
  letI : IsSmooth S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  exact KltDP.Codes.integralNodeCode (fun C : {C : S.PrimeCurve // C ∈ N} =>
    S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1)))

/-- Every original isolated-node selection has the zero binary Picard code. -/
theorem selectedNodePicardCode_eq_bot
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 2 < p)
    (N : Finset S.PrimeCurve) (hiso : IsolatedSelection π N)
    (hN : ∀ C ∈ N, IsExceptionalCurve π C)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2) :
    selectedNodePicardCode π hmin N = ⊥ := by
  classical
  letI : IsSmooth S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  change x ∈ KltDP.Codes.integralNodeCode
    (fun C : {C : S.PrimeCurve // C ∈ N} =>
      S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1))) at hx
  obtain ⟨m, hm⟩ := (KltDP.Codes.mem_integralNodeCode_iff _ x).mp hx
  let J : Finset {C : S.PrimeCurve // C ∈ N} := Finset.univ.filter (fun C => x C ≠ 0)
  let M : Finset S.PrimeCurve := J.image Subtype.val
  have hMN : ∀ C ∈ M, C ∈ N := by
    intro C hC
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hC
    exact D.property
  have hsum : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil M)) =
      ∑ C ∈ J, S.smoothWeilClassPicardEquiv
        (S.weilClassMap (Finsupp.single C.val 1)) := by
    dsimp only [NormalProjectiveSurface.selectedPrimeWeil]
    rw [map_sum, map_sum]
    exact Finset.sum_image (fun a _ b _ h => Subtype.ext h)
  have hM : M = ∅ := isolated_even_selection_eq_empty π hmin hDP hrank p hp M
    (fun C hC => hiso C (hMN C hC))
    (fun C hC => hN C (hMN C hC))
    (fun C hC => hself C (hMN C hC)) ⟨m, by
      rw [hsum]
      simpa only [J, two_zsmul, two_nsmul] using hm.symm⟩
  funext C
  by_contra hC
  have hmem : C.val ∈ M :=
    Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ C, hC⟩, rfl⟩
  simpa only [hM, Finset.not_mem_empty] using hmem

/-- The finite set contains every actual isolated exceptional minus-two prime. -/
def isolatedNodePrimes (π : S.toScheme ⟶ X.toScheme)
    (hmin : IsMinimalResolution S X π) : Finset S.PrimeCurve := by
  classical
  letI : IsProper π := hmin.toIsResolution.isProper
  let F := (exceptionalCurves_finite_of_proper_birational π
    ((isBirational_iff_isBirationalScheme π).mp hmin.toIsResolution.birational)).toFinset
  exact F.filter (fun C => C.selfIntersectionNumber hmin.regular = -2 ∧
    ∀ v : Vertices π, v.val ≠ C → Disjoint (C : Set S.toScheme) (v.val : Set S.toScheme))

theorem mem_isolatedNodePrimes_iff (π : S.toScheme ⟶ X.toScheme)
    (hmin : IsMinimalResolution S X π) (C : S.PrimeCurve) :
    C ∈ isolatedNodePrimes π hmin ↔ IsExceptionalCurve π C ∧
      C.selfIntersectionNumber hmin.regular = -2 ∧
      ∀ v : Vertices π, v.val ≠ C →
        Disjoint (C : Set S.toScheme) (v.val : Set S.toScheme) := by
  classical
  simp only [isolatedNodePrimes, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- Manuscript thm:no-even-nodes, with the literal zero-kernel conclusion
and all isolated original nodes, without a rationality assumption. -/
theorem isolatedNodePicardCode_eq_bot
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 2 < p) :
    selectedNodePicardCode π hmin (isolatedNodePrimes π hmin) = ⊥ := by
  apply selectedNodePicardCode_eq_bot π hmin hDP hrank p hp
  · intro C hC
    exact ((mem_isolatedNodePrimes_iff π hmin C).mp hC).2.2
  · intro C hC
    exact ((mem_isolatedNodePrimes_iff π hmin C).mp hC).1
  · intro C hC
    exact ((mem_isolatedNodePrimes_iff π hmin C).mp hC).2.1

end KltDP.Geometry

#check @KltDP.Geometry.isolatedNodePicardCode_eq_bot
#print axioms KltDP.Geometry.selectedNodePicardCode_eq_bot
#print axioms KltDP.Geometry.isolatedNodePicardCode_eq_bot
