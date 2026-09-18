import KltDP.Examples.FrobeniusMultiCentreOldChainGeometry
import KltDP.Geometry.RationalTreePicardChainLastComplement
import KltDP.Geometry.RationalTreePicardIdentificationsOverBase

/-!
# Triviality on the original old exceptional chain

The original exceptional component frames give zero degrees on the selected
components of the accepted full chain. Remove its newest leaf using the proved
inheritance theorem and apply the accepted rational-tree Picard theorem to the
reduced old-only union. All transversality and incidence hypotheses come from
the original exceptional charts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreOldChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
open FrobeniusMultiCentreChainPicard FrobeniusMultiCentreChainTransversal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem componentExponent_zero_of_curve_unit
    {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X]
    {J : Type u} [Fintype J] (c : J → (projectiveSpace k 1 ⟶ X))
    [∀ j, IsClosedImmersion (c j)]
    (hcover : ⋃ j, Set.range (c j).base = Set.univ)
    (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)
    (C : ↥(irreducibleComponents X)) (L : InvertibleSheaf X)
    (hL : Nonempty ((schemeModulePullback
      (c (curveOf X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
        hcover hdistinct C))).obj L.obj ≅
          _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)) :
    componentExponent k X {C} (lineIdentification X c hcover hdistinct C) L = 0 := by
  obtain ⟨t⟩ := hL
  apply (componentExponent_eq_zero_iff k X {C} _ L).mpr
  refine ⟨unitIsoOfPullbackUnitIso (lineIdentification X c hcover hdistinct C) _ ?_⟩
  exact (schemeModulePullbackCompIso (lineIdentification X c hcover hdistinct C).inv
      (componentUnionInclusion X {C})).app L.obj ≪≫
    eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj)
      (lineIdentification_inv_comp X c hcover hdistinct C)) ≪≫ t

private def unitIso_comp_pullback {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)
    (t : (schemeModulePullback f).obj M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePullback (g ≫ f)).obj M ≅ _root_.SheafOfModules.unit Z.ringCatSheaf :=
  ((schemeModulePullbackCompIso g f).app M).symm ≪≫
    (schemeModulePullback g).mapIso t ≪≫ schemeModulePullbackUnitIso g

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

private theorem old_chainCurve_unit (i : Fin n) (j : Fin q)
    (L : InvertibleSheaf (multiSurface (q + 1) n a))
    (hL : Nonempty ((schemeModulePullback (exceptionalCurveι q n a i (Sum.inl j))).obj
      L.obj ≅ _root_.SheafOfModules.unit (exceptionalCurve q n a i (Sum.inl j)).ringCatSheaf)) :
    Nonempty ((schemeModulePullback (FrobeniusMultiCentreChainPicard.chainCurve q n a ha i j.castSucc)).obj
      L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) := by
  obtain ⟨t⟩ := hL
  unfold FrobeniusMultiCentreChainPicard.chainCurve
  rw [chainMember_castSucc]
  exact ⟨unitIso_comp_pullback (exceptionalCurveι q n a i (Sum.inl j))
    (curveIso q n a ha i (Sum.inl j)).inv L.obj t⟩

variable [Fact (q + 1).Prime]

/-- Actual unit frames on the old exceptional components trivialize exactly
the reduced old-only union. The newest component is not among the hypotheses. -/
theorem oldChain_trivial_of_component_units (i : Fin n)
    (L : InvertibleSheaf (multiSurface (q + 1) n a))
    (hL : ∀ j : Fin q, Nonempty ((schemeModulePullback (exceptionalCurveι q n a i (Sum.inl j))).obj
      L.obj ≅ _root_.SheafOfModules.unit (exceptionalCurve q n a i (Sum.inl j)).ringCatSheaf)) :
    Nonempty ((schemeModulePullback (oldChainInclusion q n a ha i)).obj L.obj ≅
      _root_.SheafOfModules.unit (oldChain q n a ha i).ringCatSheaf) := by
  let S := multiSurface (q + 1) n a
  let c := FrobeniusMultiCentreChainPicard.chainCurve q n a ha i
  let X := towerChain q n a ha i
  let hd := chainData q n a ha (singlePoints q n a ha) i
  let cv := CurveChain.curve S q c
  let hc := CurveChain.curve_cover S q c
  let hd' := CurveChain.curve_distinct S q c hd
  let E := towerComponents q n a ha i
  let M := pullbackInvertibleSheaf (towerChainInclusion q n a ha i) L
  have hq : 0 < q := by
    have := (Fact.out : (q + 1).Prime).two_le
    omega
  have ht : HasTransverseComponentBranches X :=
    hasTransverseComponentBranches_of_transversalConfiguration
      (towerChainInclusion q n a ha i)
      (CurveChain.transversalConfiguration S q c hd (towerTransversal q n a ha i))
  obtain ⟨t⟩ := chainLast_complement_trivial_of_degree_zero X q E
    (CurveChain.isChain S q c hd) hq
    (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a)
    (CurveChain.dim S q c) ht (lineIdentification X cv hc hd') M (fun C hC => by
      let r := curveOf X (fun _ => projectiveSpace k 1) cv
        (fun _ => projectiveLine_isIntegral) hc hd' C
      have hrC : E r.down = C := by
        change (curveComponentEquiv X (fun _ => projectiveSpace k 1) cv
          (fun _ => projectiveLine_isIntegral) hc hd') r = C
        exact Equiv.apply_symm_apply _ C
      have hrne : r.down ≠ Fin.last q := fun h => hC (by rw [← hrC, h])
      have hrl : r.down.val < q := by
        have := r.down.isLt
        have hv : r.down.val ≠ q := fun h => hrne (Fin.ext h)
        omega
      let j : Fin q := ⟨r.down.val, hrl⟩
      have hrj : r.down = j.castSucc := Fin.ext rfl
      obtain ⟨u⟩ := old_chainCurve_unit q n a ha i j L (hL j)
      apply componentExponent_zero_of_curve_unit X cv hc hd' C M
      refine ⟨(schemeModulePullbackCompIso (cv r) (towerChainInclusion q n a ha i)).app
          L.obj ≪≫ ?_⟩
      have hmap : cv r ≫ towerChainInclusion q n a ha i = FrobeniusMultiCentreChainPicard.chainCurve q n a ha i j.castSucc := by
        exact (CurveChain.curve_comp S q c r).trans (congrArg c hrj)
      exact eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj) hmap) ≪≫ u)
  exact ⟨((schemeModulePullbackCompIso
    (componentUnionInclusion X ({E (Fin.last q)}ᶜ)) (towerChainInclusion q n a ha i)).app
      L.obj).symm ≪≫ t⟩

/-- Zero degrees, measured on the original projective-line identifications,
give the same actual restriction trivialization on the old chain. -/
theorem oldChain_trivial_of_degree_zero (i : Fin n)
    (L : InvertibleSheaf (multiSurface (q + 1) n a))
    (hL : ∀ j : Fin q, chartExponent k (curveIso q n a ha i (Sum.inl j))
      (pullbackInvertibleSheaf (exceptionalCurveι q n a i (Sum.inl j)) L) = 0) :
    Nonempty ((schemeModulePullback (oldChainInclusion q n a ha i)).obj L.obj ≅
      _root_.SheafOfModules.unit (oldChain q n a ha i).ringCatSheaf) :=
  oldChain_trivial_of_component_units q n a ha i L (fun j =>
    (chartExponent_eq_zero_iff k (curveIso q n a ha i (Sum.inl j))
      (pullbackInvertibleSheaf (exceptionalCurveι q n a i (Sum.inl j)) L)).mp (hL j))

end KltDP.Examples.FrobeniusMultiCentreOldChain
