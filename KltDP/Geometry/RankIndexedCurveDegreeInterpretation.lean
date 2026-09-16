import KltDP.Geometry.RankIndexedCurveDegree
import KltDP.AdmissionProbe.ProperFiniteRankCohomology

/-!
# Original finite-cohomology interpretation of rank-indexed degree

INACTIVE TEXT. This ordinary adapter depends on the separately selected
finite-rank/coherence sources and the isolated proper-cohomology consumers.
Their admission and native audit remain independent prerequisites. This
file supplies neither a new literature declaration nor a tensor-degree law.

All dimensions use the original structure morphism's scalar action through
`baseFunctor f`. Properness supplies the Noetherian geometry used by the
finite-rank/coherence adapter and the independent vanishing theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.AdmissionProbe.ProperFiniteRankCohomology

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Both original coefficients in degree have finite cohomology, vanish
above one, and compute the displayed degree by their finite dimensions.
This includes rank zero, empty schemes and nonreduced proper schemes. -/
theorem finiteRankDegree_finite_euler_interpretation
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim Y ≤ 1) (E : Y.Modules) (r : ℕ)
    (hE : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) E r) :
    (∀ i, FiniteDimensional k ((baseFunctor f i).obj E)) ∧
      (∀ i, FiniteDimensional k ((baseFunctor f i).obj
        (_root_.SheafOfModules.unit Y.ringCatSheaf))) ∧
      (∀ i, 1 < i → Subsingleton (H E i) ∧
        Subsingleton (H (_root_.SheafOfModules.unit Y.ringCatSheaf) i)) ∧
      finiteRankDegree f hdim E r hE =
        ((cohomologyDimension f E 0 : ℤ) - (cohomologyDimension f E 1 : ℤ)) -
        (r : ℤ) *
          ((cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 0 : ℤ) -
            (cohomologyDimension f (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 : ℤ)) := by
  have hO : KltDP.SheafOfModules.IsLocallyFreeOfRank
      (R := Y.ringCatSheaf) (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 :=
    inferInstance
  obtain ⟨hfiniteE, hvanishE, hχE⟩ :=
    proper_finiteRank_euler_interpretation f hdim E r hE
  obtain ⟨hfiniteO, hvanishO, hχO⟩ :=
    proper_finiteRank_euler_interpretation f hdim
      (_root_.SheafOfModules.unit Y.ringCatSheaf) 1 hO
  refine ⟨hfiniteE, hfiniteO, fun i hi => ⟨hvanishE i hi, hvanishO i hi⟩, ?_⟩
  unfold finiteRankDegree
  rw [hχE, hχO]

end KltDP.Geometry.ModuleCohomology
