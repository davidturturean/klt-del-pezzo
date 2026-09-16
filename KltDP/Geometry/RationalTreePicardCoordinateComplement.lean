import KltDP.Geometry.RationalTreePicardCoordinateCocycle
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.ModuleRestrictionPullback

/-!
# The coordinate bundle is trivial on the other components

BRIEF16, step 2. On a tree, two distinct components meet in at most one point
(`inter_subsingleton_of_isTree`, by uniqueness of paths in an acyclic graph). Hence every
component `D ≠ C` lies inside one member of the coordinate cover of `C`
(`exists_range_subset_coordOpens`): inside the complement of `C` if `D` misses `C`, inside the
chart of the node `C ∩ D` otherwise. The glued sheaf has a pullback-form trivialization on each
member of its cover (`chartPullbackIso`, from the accepted over-site chart isomorphism through the
open-subscheme/over-site equivalence and the restriction/pullback comparison), so the pullback of
the coordinate bundle to `Z_D` factors through a trivializing open and is trivial
(`pullbackUnitIsoOfRange`); its component exponent on `D` is `0`
(`componentExponent_coordinateBundle_of_ne`).

Together with `componentExponent_coordinateBundle_self` (which needs the pullback compatibility
`PullbackGluedClass`), this gives the coordinate line bundles of all components and, by the
accepted reduction `multidegreeHom_surjective_of_coordinate`, the surjectivity half of
`lem:tree-picard` conditional on `PullbackGluedClass`
(`multidegreeHom_surjective_of_pullbackGluedClass`, `rationalTreePicard_of_pullbackGluedClass`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open TransitionUnitGluing SchemeModuleRestriction

section TreeLemma

variable {X : Scheme.{u}}

/-- In a tree, two distinct components meet in at most one point. -/
theorem inter_subsingleton_of_isTree (hTree : (componentPointIncidenceGraph X).IsTree)
    {C D : ↥(irreducibleComponents X)} (hCD : C ≠ D) : (C.1 ∩ D.1).Subsingleton := by
  intro q hq q' hq'
  have hqI : q ∈ componentIntersectionPoints X := ⟨C, D, hCD, hq.1, hq.2⟩
  have hqI' : q' ∈ componentIntersectionPoints X := ⟨C, D, hCD, hq'.1, hq'.2⟩
  have h1 : (componentPointIncidenceGraph X).Adj (Sum.inl C) (Sum.inr ⟨q, hqI⟩) := hq.1
  have h2 : (componentPointIncidenceGraph X).Adj (Sum.inr ⟨q, hqI⟩) (Sum.inl D) := hq.2
  have h1' : (componentPointIncidenceGraph X).Adj (Sum.inl C) (Sum.inr ⟨q', hqI'⟩) := hq'.1
  have h2' : (componentPointIncidenceGraph X).Adj (Sum.inr ⟨q', hqI'⟩) (Sum.inl D) := hq'.2
  let p : (componentPointIncidenceGraph X).Walk (Sum.inl C) (Sum.inl D) :=
    SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)
  let p' : (componentPointIncidenceGraph X).Walk (Sum.inl C) (Sum.inl D) :=
    SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2' SimpleGraph.Walk.nil)
  have hp : p.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨⟨SimpleGraph.Walk.IsPath.nil, ?_⟩, ?_⟩
    · simp
    · simp [hCD]
  have hp' : p'.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨⟨SimpleGraph.Walk.IsPath.nil, ?_⟩, ?_⟩
    · simp
    · simp [hCD]
  have heq : (⟨p, hp⟩ : (componentPointIncidenceGraph X).Path (Sum.inl C) (Sum.inl D)) =
      ⟨p', hp'⟩ := hTree.IsAcyclic.path_unique _ _
  have hv := congrArg
    (fun w : (componentPointIncidenceGraph X).Path (Sum.inl C) (Sum.inl D) => w.1.getVert 1) heq
  have hv' : (Sum.inr ⟨q, hqI⟩ :
      ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)) = Sum.inr ⟨q', hqI'⟩ := hv
  exact congrArg Subtype.val (Sum.inr.inj hv')

end TreeLemma

section ChartContainment

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  (C : ↥(irreducibleComponents X)) (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
  (hdim : topologicalKrullDim X ≤ 1)

/-- On a tree, every other component lies inside one member of the coordinate cover of `C`. -/
theorem exists_range_subset_coordOpens (hTree : (componentPointIncidenceGraph X).IsTree)
    {D : ↥(irreducibleComponents X)} (hDC : D ≠ C) :
    ∃ a, Set.range (componentUnionInclusion X {D}).base ⊆ (coordOpens k C e hdim a : Set X) := by
  rw [range_componentUnionInclusion, coe_componentClosedUnion_singleton]
  by_cases hint : ∃ q, q ∈ C.1 ∩ D.1
  · obtain ⟨q, hqC, hqD⟩ := hint
    have hqN : q ∈ nodesOn C := ⟨hqC, (mem_componentClosedUnion X _ q).mpr
      ⟨D, fun h => hDC (Set.mem_singleton_iff.mp h), hqD⟩⟩
    refine ⟨Sum.inr (some ⟨q, hqN⟩), fun x hxD =>
      (mem_coordOpens_some k C e hdim _ x).mpr ⟨?_, ?_⟩⟩
    · rintro ⟨hxN, hxq⟩
      exact hxq (inter_subsingleton_of_isTree hTree hDC.symm ⟨hxN.1, hxD⟩ ⟨hqC, hqD⟩)
    · intro hxK
      have hxC : x ∈ C.1 := lineImage_subset k C e _ hxK
      have hxq : x = q := inter_subsingleton_of_isTree hTree hDC.symm ⟨hxC, hxD⟩ ⟨hqC, hqD⟩
      rw [hxq] at hxK
      exact not_mem_lineImage_nodeChart k C e q hxK
  · refine ⟨Sum.inr none, fun x hxD hxC => hint ⟨x, ?_, hxD⟩⟩
    rw [coe_componentClosedUnion_singleton] at hxC
    exact hxC

end ChartContainment

section ChartTrivialization

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)

/-- The chart trivialization of the glued sheaf, in restriction form. -/
def chartRestrictionIso (i : ι) :
    (restriction (U i).ι).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf :=
  (openToOverFunctor (U i)).preimageIso
    (openToOverRestrictionIso (U i) (moduleSheaf X U g) ≪≫ chartIsoOn X U g hc i le_rfl ≪≫
      openToOverUnitIso (U i))

/-- The chart trivialization of the glued sheaf, in pullback form. -/
def chartPullbackIso (i : ι) :
    (schemeModulePullback (U i).ι).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf :=
  ((restrictionIsoPullback (U i).ι).app (moduleSheaf X U g)).symm ≪≫ chartRestrictionIso U g hc i

/-- The pullback of the glued sheaf along a morphism landing in one chart is trivial. -/
def pullbackUnitIsoOfRange {Y : Scheme.{u}} (φ : Y ⟶ X) (i : ι)
    (hφ : Set.range φ.base ⊆ (U i : Set X)) :
    (schemeModulePullback φ).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  have hrange : Set.range φ.base ⊆ Set.range (U i).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hφ
  eqToIso (congrArg (fun m : Y ⟶ X => (schemeModulePullback m).obj (moduleSheaf X U g))
      (IsOpenImmersion.lift_fac (U i).ι φ hrange).symm) ≪≫
    ((schemeModulePullbackCompIso (IsOpenImmersion.lift (U i).ι φ hrange) (U i).ι).app
      (moduleSheaf X U g)).symm ≪≫
    (schemeModulePullback (IsOpenImmersion.lift (U i).ι φ hrange)).mapIso
      (chartPullbackIso U g hc i) ≪≫
    schemeModulePullbackUnitIso (IsOpenImmersion.lift (U i).ι φ hrange)

end ChartTrivialization

section ComplementExponent

variable (k : Type u) [Field k] {X : Scheme.{u}} [NoetherianSpace X]
  [AlgebraicGeometry.IsReduced X] (C : ↥(irreducibleComponents X))
  (e : componentUnionScheme X {C} ≅ projectiveSpace k 1) (hdim : topologicalKrullDim X ≤ 1)

/-- On a tree, the coordinate bundle of `C` has component exponent `0` on every other
component, for any identification of that component with the projective line. -/
theorem componentExponent_coordinateBundle_of_ne (hTree : (componentPointIncidenceGraph X).IsTree)
    {D : ↥(irreducibleComponents X)} (hDC : D ≠ C)
    (e' : componentUnionScheme X {D} ≅ projectiveSpace k 1) :
    componentExponent k X {D} e' (coordinateBundle k C e hdim) = 0 := by
  rw [componentExponent_eq_zero_iff]
  obtain ⟨a, ha⟩ := exists_range_subset_coordOpens k C e hdim hTree hDC
  exact ⟨pullbackUnitIsoOfRange (coordOpens k C e hdim) (coordUnits k C e hdim)
    (coordUnits_isCocycle k C e hdim) (componentUnionInclusion X {D}) a ha⟩

end ComplementExponent

section Assembly

variable (k : Type u) [Field k] [IsAlgClosed k]
  (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
  (htrans : HasTransverseComponentBranches X)
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

omit [IsAlgClosed k] [IsLocallyNoetherian X] in
include hdim hTree in
/-- Under the pullback compatibility of glued line bundles, every component carries a coordinate
line bundle (exponent `1` there, `0` on every other component). -/
theorem exists_coordinateBundle_of_pullbackGluedClass (hP : PullbackGluedClass.{u})
    (C : ↥(irreducibleComponents X)) :
    ∃ L : InvertibleSheaf X, componentExponent k X {C} (e C) L = 1 ∧
      ∀ D : ↥(irreducibleComponents X), D ≠ C → componentExponent k X {D} (e D) L = 0 :=
  ⟨coordinateBundle k C (e C) hdim, componentExponent_coordinateBundle_self k C (e C) hdim hP,
    fun D hDC => componentExponent_coordinateBundle_of_ne k C (e C) hdim hTree hDC (e D)⟩

omit [IsAlgClosed k] [IsLocallyNoetherian X] in
include hdim hTree in
/-- The multidegree homomorphism is surjective, given the pullback compatibility of glued line
bundles. -/
theorem multidegreeHom_surjective_of_pullbackGluedClass (hP : PullbackGluedClass.{u}) :
    Function.Surjective (multidegreeHom k X e) :=
  multidegreeHom_surjective_of_coordinate k X e
    (exists_coordinateBundle_of_pullbackGluedClass k X hdim hTree e hP)

include f hdim hTree htrans in
/-- The multidegree homomorphism is bijective, given the pullback compatibility of glued line
bundles. -/
theorem multidegreeHom_bijective_of_pullbackGluedClass (hP : PullbackGluedClass.{u}) :
    Function.Bijective (multidegreeHom k X e) :=
  ⟨multidegreeHom_injective_final k X f hdim hTree htrans e,
    multidegreeHom_surjective_of_pullbackGluedClass k X hdim hTree e hP⟩

include f hdim hTree htrans in
/-- `lem:tree-picard` (Picard group of a rational tree), with the exact hypotheses carried here:
`X` is a reduced Noetherian scheme, locally of finite type over an algebraically closed field `k`,
of dimension at most one, with tree component-point incidence graph and transverse branch germs
at the intersection points, and with each irreducible component identified with the projective
line. Then the multidegree map `Pic X → ℤ^{components}` is an isomorphism; the kernel half is
unconditional (`multidegreeHom_injective_final`), the surjectivity half is proved from the
coordinate line bundles `coordinateBundle`, whose exponent on their own component is computed
through the pullback compatibility `PullbackGluedClass` of cocycle-glued line bundles (the only
remaining hypothesis). -/
theorem rationalTreePicard_of_pullbackGluedClass (hP : PullbackGluedClass.{u}) :
    Function.Bijective (multidegreeHom k X e) :=
  multidegreeHom_bijective_of_pullbackGluedClass k X f hdim hTree htrans e hP

end Assembly

end KltDP.Geometry.RationalTreePicard
