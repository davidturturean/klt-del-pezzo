import KltDP.Examples.FrobeniusGraphPicardClassAffine
import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts

/-!
# A cover adapted to the actual closed Frobenius graph

The two diagonal polynomial product charts cover the original graph.
Together with the open complement of that graph they cover the ambient
surface. On each diagonal chart the actual graph base change is the
existing monomial curve, whose regular kernel frame is already proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassDiagonal

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusProductPlaneChart FrobeniusGlobalGraphCompatibility
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassPowerCharts

variable {k : Type u} [Field k]

private theorem diagonal_cone_parameter {W : Scheme.{u}} (p : ℕ) (i : Fin 2)
    (f : W ⟶ Spec (CommRingCat.of (planeRing k)))
    (g : W ⟶ projectiveSpace k 1)
    (h : f ≫ productChart i i = g ≫ projectiveGraphMorphism p) :
    (f ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫ polynomialChartMap k i = g := by
  have he := congrArg (fun q : W ⟶ projectiveProduct k => q ≫ firstProjection) h
  simpa only [Category.assoc, productChart_fst,
    projectiveGraphMorphism_fst, Category.comp_id] using he

/-- Both diagonal graph charts are genuine scheme-theoretic base changes. -/
theorem curveInPlane_diagonal_isPullback (p : ℕ) (i : Fin 2) :
    IsPullback (curveInPlane (k := k) p) (polynomialChartMap k i)
      (productChart i i) (projectiveGraphMorphism p) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (curveInPlane_diagonalChart p i)
    (fun s => s.fst ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap))
    (fun s => ?_) (fun s => diagonal_cone_parameter p i s.fst s.snd s.condition)
    (fun s m hm _ => ?_))
  · apply (cancel_mono (productChart (k := k) i i)).mp
    rw [Category.assoc, curveInPlane_diagonalChart, ← Category.assoc,
      diagonal_cone_parameter p i s.fst s.snd s.condition]
    exact s.condition.symm
  · calc
      m = (m ≫ curveInPlane p) ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap) := by
        rw [Category.assoc, curveInPlane_firstCoordinate, Category.comp_id]
      _ = _ := congrArg (fun q => q ≫ Spec.map (CommRingCat.ofHom firstCoordinateMap)) hm

/-- The graph's original ideal restricts to the monomial ideal at infinity too. -/
theorem graphIdeal_diagonalChart (p : ℕ) (i : Fin 2)
    (U : (Spec (CommRingCat.of (planeRing k))).affineOpens) :
    (curveInPlane p).ker.ideal U =
      ((graphIdeal (k := k) p).ideal
        ⟨productChart i i ''ᵁ U, U.2.image_of_isOpenImmersion _⟩).comap
          ((productChart i i).appIso U).inv.hom :=
  Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (projectiveGraphMorphism p) (curveInPlane p) (polynomialChartMap k i)
    (productChart i i) (curveInPlane_diagonal_isPullback p i) U

/-- Every point of the actual graph is in one of the two diagonal charts. -/
theorem graph_range_diagonal (p : ℕ) (x : projectiveProduct k)
    (hx : x ∈ Set.range (projectiveGraphMorphism (k := k) p).base) :
    ∃ i : Fin 2, x ∈ Set.range (productChart (k := k) i i).base := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨z, hz⟩ := (polynomialAffineCover k).covers q
  let i : Fin 2 := (polynomialAffineCover k).f q
  refine ⟨i, (curveInPlane p).base z, ?_⟩
  calc
    (productChart i i).base ((curveInPlane p).base z) =
        (projectiveGraphMorphism p).base ((polynomialChartMap k i).base z) :=
      congrArg (fun f : Spec (CommRingCat.of (Polynomial k)) ⟶ projectiveProduct k =>
        f.base z) (curveInPlane_diagonalChart p i)
    _ = _ := congrArg (projectiveGraphMorphism p).base hz

/-- The complement is the open complement of the original closed graph. -/
def graphComplement (p : ℕ) : (projectiveProduct k).Opens :=
  ⟨(Set.range (projectiveGraphMorphism (k := k) p).base)ᶜ,
    (projectiveGraphMorphism_isClosed_range p).isOpen_compl⟩

/-- Three actual opens suffice for an atlas of the original graph ideal. -/
def graphAtlasOpen (p : ℕ) : Option (Fin 2) → (projectiveProduct k).Opens
  | none => graphComplement p
  | some i => (productChart i i).opensRange

theorem graphAtlasOpens_cover (p : ℕ) (x : projectiveProduct k) :
    ∃ i : Option (Fin 2), x ∈ graphAtlasOpen (k := k) p i := by
  classical
  by_cases hx : x ∈ Set.range (projectiveGraphMorphism (k := k) p).base
  · obtain ⟨i, hi⟩ := graph_range_diagonal p x hx
    exact ⟨some i, hi⟩
  · exact ⟨none, hx⟩

end KltDP.Examples.FrobeniusGraphPicardClassDiagonal
