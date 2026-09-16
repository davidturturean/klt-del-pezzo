import KltDP.Examples.FrobeniusGraphPicardClassMixedVanishing
import KltDP.Examples.FrobeniusGraphPicardClassRulingEquations

/-!
# A full original-product cover for the Cartier comparison

The two original diagonal opens, together with the two mixed basic
opens D(1-u^p*v), cover the original product. Each companion open is
nonempty, is disjoint from the original graph, and carries the actual
regular unit represented by the mixed equation. This includes both
mixed points omitted by the diagonal opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassFullCover

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphPicardClassDiagonal FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassMixedBasicOpens
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassMixedSections
open FrobeniusGraphPicardClassMixedVanishing FrobeniusGraphPicardClassRulingEquations

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

def companionOpen (p : ℕ) (i : Fin 2) : (projectiveProduct k).Opens :=
  (projectiveProduct k).basicOpen (mixedAmbientEquation p i)

theorem companionOpen_le_mixed (p : ℕ) (i : Fin 2) :
    companionOpen (k := k) p i ≤ productOpen i (otherIndex i) :=
  (projectiveProduct k).basicOpen_le _

theorem companionOpen_le_complement (p : ℕ) (i : Fin 2) :
    companionOpen (k := k) p i ≤ graphComplement p := by
  intro x hx
  exact fun hg => Set.disjoint_left.mp (mixedEquation_basicOpen_disjoint_graph p i) hx hg

instance companionOpen_nonempty (p : ℕ) (i : Fin 2) : Nonempty (companionOpen (k := k) p i) := by
  let X := projectiveProduct k
  let U : X.Opens := productOpen i (otherIndex i)
  refine ⟨⟨genericPoint X, ?_⟩⟩
  apply (X.mem_basicOpen (mixedAmbientEquation p i) (genericPoint X)
    (genericPoint_mem_nonempty_open X U)).mpr
  change IsUnit (X.germToFunctionField U (mixedAmbientEquation p i))
  rw [mixedAmbientEquation, mixedEquation_polynomial]
  exact isUnit_iff_ne_zero.mpr (mixed_equation_nonzero p i)

/-- Its actual original regular equation restricts to a regular unit. -/
def companionUnit (p : ℕ) (i : Fin 2) : Γ(projectiveProduct k, companionOpen p i)ˣ :=
  ((projectiveProduct k).toRingedSpace.isUnit_res_basicOpen (mixedAmbientEquation p i)).unit

theorem companionUnit_image (p : ℕ) (i : Fin 2) :
    Units.map ((projectiveProduct k).germToFunctionField (companionOpen p i)).hom.toMonoidHom
      (companionUnit (k := k) p i) = mixedFunctionUnit p i := by
  apply Units.ext
  change (projectiveProduct k).germToFunctionField (companionOpen p i)
    (companionUnit (k := k) p i : Γ(projectiveProduct k, companionOpen p i)) = _
  rw [companionUnit, IsUnit.unit_spec]
  change (projectiveProduct k).germToFunctionField (companionOpen p i)
    ((projectiveProduct k).presheaf.map
      (homOfLE (companionOpen_le_mixed (k := k) p i)).op
        (mixedAmbientEquation (k := k) p i)) = _
  calc
    _ = (projectiveProduct k).germToFunctionField
        (productOpen (k := k) i (otherIndex i)) (mixedAmbientEquation (k := k) p i) :=
      (projectiveProduct k).presheaf.germ_res_apply
        (homOfLE (companionOpen_le_mixed (k := k) p i))
        (genericPoint (projectiveProduct k))
        (genericPoint_mem_nonempty_open (projectiveProduct k) (companionOpen (k := k) p i))
        (mixedAmbientEquation (k := k) p i)
    _ = _ := by
      rw [mixedAmbientEquation, mixedEquation_polynomial]
      rfl

def comparisonOpen (p : ℕ) : Fin 2 ⊕ Fin 2 → (projectiveProduct k).Opens
  | .inl i => diagonalOpen i
  | .inr i => companionOpen p i

/-- Every original product point lies in a diagonal or a graph-free companion open. -/
theorem comparisonOpens_cover (p : ℕ) (x : projectiveProduct k) :
    ∃ a : Fin 2 ⊕ Fin 2, x ∈ comparisonOpen (k := k) p a := by
  obtain ⟨i, j, z, rfl⟩ := productCharts_cover x
  by_cases hij : j = i
  · subst j
    refine ⟨.inl i, ?_⟩
    change (productChart i i).base z ∈ diagonalOpen i
    rw [diagonalOpen, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨z, rfl⟩
  · have hj : j = otherIndex i := by
      fin_cases i <;> fin_cases j <;> simp_all [otherIndex]
    subst j
    have hz : z ∈ (Spec (CommRingCat.of (FrobeniusBlowupContact.planeRing k))).basicOpen
        (mixedEquation p) ⊔
      (Spec (CommRingCat.of (FrobeniusBlowupContact.planeRing k))).basicOpen outerSection := by
      rw [mixedBasicOpens_cover]
      trivial
    rcases hz with hh | hv
    · refine ⟨.inr i, ?_⟩
      have h : (productChart i (otherIndex i)).base z ∈ productChart i (otherIndex i) ''ᵁ
          (Spec (CommRingCat.of (FrobeniusBlowupContact.planeRing k))).basicOpen (mixedEquation p) :=
        ⟨z, hh, rfl⟩
      rw [Scheme.image_basicOpen] at h
      exact h
    · refine ⟨.inl i, ?_⟩
      rw [← mixedChart_preimage_diagonal_section (k := k) i] at hv
      change (productChart i (otherIndex i)).base z ∈ diagonalOpen i
      simpa only [diagonalOpen, Scheme.Hom.image_top_eq_opensRange] using hv

theorem comparisonOpens_iSup (p : ℕ) :
    (⨆ a : Fin 2 ⊕ Fin 2, comparisonOpen (k := k) p a) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := comparisonOpens_cover p x
  exact Opens.mem_iSup.mpr ⟨a, ha⟩

end KltDP.Examples.FrobeniusGraphPicardClassFullCover
