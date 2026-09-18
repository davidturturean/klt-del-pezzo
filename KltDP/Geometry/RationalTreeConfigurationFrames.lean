import KltDP.Geometry.RationalTreePicardOfConfiguration

/-!
# Triviality of a rational tree from frames on its original curve cover

The existing configuration theorem uses exponents on its canonical reduced
component schemes. Original frames on the covering curves transport through
the proved curve-component isomorphisms and force those exponents to vanish.
No equality of independently selected coordinates is required.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k]
  (Y : Scheme.{u}) [NoetherianSpace Y] [IsLocallyNoetherian Y]
  [AlgebraicGeometry.IsReduced Y]
  {S : Scheme.{u}} (ι : Y ⟶ S) [IsClosedImmersion ι]
  (f : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (hconf : TransversalConfiguration ι)
  (hdim : topologicalKrullDim Y ≤ 1)
  (hTree : (componentPointIncidenceGraph Y).IsTree)
  {J : Type u} [Fintype J]
  (Cv : J → Scheme.{u}) (c : ∀ j, Cv j ⟶ Y) [∀ j, IsClosedImmersion (c j)]
  (hint : ∀ j, IsIntegral (Cv j))
  (hcover : ⋃ j, Set.range (c j).base = Set.univ)
  (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)
  (e : ∀ j, Cv j ≅ projectiveSpace k 1)

include ι f hconf hdim hTree hint hcover hdistinct e

/-- Original unit frames on the rational curves of an actual transversal
tree give a unit frame on that entire original tree. -/
theorem trivial_of_curve_frames_of_configuration (L : InvertibleSheaf Y)
    (hL : ∀ j, Nonempty ((pullbackInvertibleSheaf (c j) L).obj ≅
      _root_.SheafOfModules.unit (Cv j).ringCatSheaf)) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) := by
  classical
  refine KltDP.Manuscript.S02.rationalTreePicard_trivial_of_degree_zero
    Y (ι ≫ f) hdim hTree
    (hasTransverseComponentBranches_of_transversalConfiguration ι hconf)
    (fun D => curveIdentification Y Cv c hint hcover hdistinct D ≪≫
      e (curveOf Y Cv c hint hcover hdistinct D)) L (fun D => ?_)
  rw [componentExponent_eq_zero_iff]
  let t := curveLift Y Cv c hint hcover hdistinct D
  letI : IsIso t := isIso_curveLift Y Cv c hint hcover hdistinct D
  refine ⟨unitIsoOfPullbackUnitIso (asIso t).symm _ ?_⟩
  exact (schemeModulePullbackCompIso t (componentUnionInclusion Y {D})).app L.obj ≪≫
    eqToIso (congrArg (fun g => (schemeModulePullback g).obj L.obj)
      (curveLift_comp Y Cv c hint hcover hdistinct D)) ≪≫
    (hL (curveOf Y Cv c hint hcover hdistinct D)).some

end KltDP.Geometry.RationalTreePicard

#check @KltDP.Geometry.RationalTreePicard.trivial_of_curve_frames_of_configuration
#print axioms KltDP.Geometry.RationalTreePicard.trivial_of_curve_frames_of_configuration
