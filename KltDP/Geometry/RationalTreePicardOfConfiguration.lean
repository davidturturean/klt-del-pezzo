import KltDP.Geometry.TransverseBranchesOfSurfaceConfiguration
import KltDP.Geometry.RationalTreePicardClosedImmersionLift
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Manuscript.S02.RationalTreePicard

/-!
# The rational-tree Picard lemma for a transversal configuration of projective lines

BRIEF18, tasks 1 (component identification) and 3 (the corollary).

**Components of a configuration.** Let `X` be a Noetherian scheme covered by finitely many
integral curves, given as closed immersions `c j : Cv j ⟶ X` (`j : J`, `J` finite, `Cv j`
integral) whose images cover `X` and are pairwise incomparable (`hdistinct`: an inclusion of images
forces equality of indices). Then the images are exactly the irreducible components of `X`
(`curveRange_mem_irreducibleComponents`, `componentOfCurve_surjective`; the bijection
`curveComponentEquiv : J ≃ irreducibleComponents X`), and the reduced component scheme
`Z_C = componentUnionScheme X {C}` of the lane is isomorphic to the curve: `c j` lifts through the
closed immersion `Z_C ⟶ X` (`curveLift`, by the lane's `liftGluedTo`, since the vanishing ideal of
the image is contained in the kernel of `c j` — `vanishingIdeal_le_ker`, as the kernel of a closed
immersion of a reduced scheme is radical with support the image), and the lift is a surjective
closed immersion into a reduced scheme, hence an isomorphism (`isIso_curveLift`,
`curveIdentification C : Z_C ≅ Cv (curveOf C)`).

**The corollary (`rationalTreePicard_of_configuration`).** For a transversal configuration
`ι : X ⟶ S` (`TransversalConfiguration ι`: regular two-dimensional local rings of `S` at the
crossing points, local equations generating the maximal ideal, no triple points) of projective lines
(`c j : projectiveSpace k 1 ⟶ X`) in a scheme `S` locally of finite type over an algebraically
closed field `k`, with `X` reduced, locally Noetherian, of dimension `≤ 1` and with tree
component-point incidence graph, the multidegree map of `lem:tree-picard` is bijective:
`Pic X ≃* (J → Multiplicative ℤ)` (`picardEquiv_of_configuration`, indexed by the curves), and a
line bundle of degree zero on every curve is trivial (`trivial_of_degree_zero_of_configuration`).
Nodality is derived (`hasTransverseComponentBranches_of_transversalConfiguration`); the
identifications `Z_C ≅ P¹` are the lifted curves. The hypotheses `hdim` (dimension) and `hTree`
(tree incidence graph) are carried as stated on `X`; "smooth projective surface" enters only through
the regularity of the local rings of `S` at the crossing points and the finite-type structure
morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section Lift

variable {X W : Scheme.{u}} (g : W ⟶ X) [IsClosedImmersion g] [AlgebraicGeometry.IsReduced W]

/-- The vanishing ideal of the image of a closed immersion of a reduced scheme is contained in
its kernel (the kernel is radical, with support the closed image). -/
theorem vanishingIdeal_le_ker (K : Closeds X) (hK : (K : Set X) = Set.range g.base) :
    Scheme.IdealSheafData.vanishingIdeal K ≤ g.ker := by
  have hrad : g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support, SchematicImageDenseOpen.ker_radical]
  rw [hrad]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  show (g.ker.support : Set X) ⊆ K
  rw [Scheme.Hom.support_ker, hK]
  exact g.isClosedEmbedding.isClosed_range.closure_subset

end Lift

section Curves

variable (X : Scheme.{u}) [NoetherianSpace X] {J : Type u} [Fintype J]
  (Cv : J → Scheme.{u}) (c : ∀ j, Cv j ⟶ X) [∀ j, IsClosedImmersion (c j)]
  (hint : ∀ j, IsIntegral (Cv j))
  (hcover : ⋃ j, Set.range (c j).base = Set.univ)
  (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)

omit [NoetherianSpace X] [Fintype J] [∀ j, IsClosedImmersion (c j)] in
include hint in
/-- The image of an integral curve is irreducible. -/
theorem curveRange_isIrreducible (j : J) : IsIrreducible (Set.range (c j).base) := by
  haveI : IsIntegral (Cv j) := hint j
  have h := (IrreducibleSpace.isIrreducible_univ (Cv j)).image (c j).base
    (c j).base.hom.continuous.continuousOn
  rwa [Set.image_univ] at h

omit [NoetherianSpace X] [Fintype J] in
theorem curveRange_isClosed (j : J) : IsClosed (Set.range (c j).base) :=
  (c j).isClosedEmbedding.isClosed_range

omit [NoetherianSpace X] in
include hcover in
/-- An irreducible subset of `X` lies in the image of one of the finitely many curves. -/
theorem exists_curveRange_subset_of_isIrreducible (T : Set X) (hT : IsIrreducible T) :
    ∃ j, T ⊆ Set.range (c j).base := by
  classical
  obtain ⟨z, hz, hTz⟩ := isIrreducible_iff_sUnion_isClosed.mp hT
    (Finset.univ.image fun j => Set.range (c j).base)
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      exact curveRange_isClosed X Cv c j)
    (fun x _ => by
      have hx : x ∈ ⋃ j, Set.range (c j).base := by
        rw [hcover]
        exact Set.mem_univ x
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_sUnion.mpr
        ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem (fun j => Set.range (c j).base)
          (Finset.mem_univ j)), hj⟩)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨j, hTz⟩

omit [NoetherianSpace X] in
include hint hcover hdistinct in
/-- The image of each curve is an irreducible component of `X`. -/
theorem curveRange_mem_irreducibleComponents (j : J) :
    Set.range (c j).base ∈ irreducibleComponents X := by
  show Maximal IsIrreducible (Set.range (c j).base)
  refine And.intro (curveRange_isIrreducible X Cv c hint j) (fun T hT hsub => ?_)
  obtain ⟨i, hTi⟩ := exists_curveRange_subset_of_isIrreducible X Cv c hcover T hT
  have hji : j = i := hdistinct j i (hsub.trans hTi)
  rw [hji]
  exact hTi

/-- The irreducible component of `X` given by the `j`-th curve. -/
def componentOfCurve (j : J) : ↥(irreducibleComponents X) :=
  ⟨Set.range (c j).base, curveRange_mem_irreducibleComponents X Cv c hint hcover hdistinct j⟩

omit [NoetherianSpace X] in
theorem componentOfCurve_val (j : J) :
    (componentOfCurve X Cv c hint hcover hdistinct j).1 = Set.range (c j).base := rfl

omit [NoetherianSpace X] in
theorem componentOfCurve_injective : Function.Injective (componentOfCurve X Cv c hint hcover hdistinct) := by
  intro i j hij
  exact hdistinct i j (le_of_eq (congrArg Subtype.val hij))

omit [NoetherianSpace X] in
/-- Every irreducible component of `X` is the image of a curve. -/
theorem componentOfCurve_surjective :
    Function.Surjective (componentOfCurve X Cv c hint hcover hdistinct) := by
  intro C
  have hmax : Maximal IsIrreducible C.1 := C.2
  obtain ⟨j, hCj⟩ := exists_curveRange_subset_of_isIrreducible X Cv c hcover C.1 hmax.1
  refine ⟨j, Subtype.ext ?_⟩
  exact Set.Subset.antisymm (hmax.2 (curveRange_isIrreducible X Cv c hint j) hCj) hCj

/-- The curves are in bijection with the irreducible components of `X`. -/
def curveComponentEquiv : J ≃ ↥(irreducibleComponents X) :=
  Equiv.ofBijective _ ⟨componentOfCurve_injective X Cv c hint hcover hdistinct,
    componentOfCurve_surjective X Cv c hint hcover hdistinct⟩

/-- The curve of a component. -/
def curveOf (C : ↥(irreducibleComponents X)) : J :=
  (curveComponentEquiv X Cv c hint hcover hdistinct).symm C

omit [NoetherianSpace X] in
theorem range_curveOf (C : ↥(irreducibleComponents X)) :
    Set.range (c (curveOf X Cv c hint hcover hdistinct C)).base = C.1 :=
  congrArg Subtype.val ((curveComponentEquiv X Cv c hint hcover hdistinct).apply_symm_apply C)

/-- The vanishing ideal of a component is contained in the kernel of its curve. -/
theorem componentUnionIdeal_le_ker_curve (C : ↥(irreducibleComponents X)) :
    componentUnionIdeal X {C} ≤ (c (curveOf X Cv c hint hcover hdistinct C)).ker := by
  haveI : IsIntegral (Cv (curveOf X Cv c hint hcover hdistinct C)) := hint _
  show Scheme.IdealSheafData.vanishingIdeal (componentClosedUnion X {C}) ≤ _
  apply vanishingIdeal_le_ker
  rw [coe_componentClosedUnion_singleton, range_curveOf]

/-- The lift of the curve of a component through the reduced component scheme `Z_C`. -/
def curveLift (C : ↥(irreducibleComponents X)) : Cv (curveOf X Cv c hint hcover hdistinct C) ⟶
    componentUnionScheme X {C} :=
  liftGluedTo (componentUnionIdeal X {C}) (c (curveOf X Cv c hint hcover hdistinct C))
    (componentUnionIdeal_le_ker_curve X Cv c hint hcover hdistinct C)

theorem curveLift_comp (C : ↥(irreducibleComponents X)) :
    curveLift X Cv c hint hcover hdistinct C ≫ componentUnionInclusion X {C} =
      c (curveOf X Cv c hint hcover hdistinct C) :=
  liftGluedTo_gluedTo _ _ _

/-- The lift is an isomorphism: a surjective closed immersion into the reduced `Z_C`. -/
theorem isIso_curveLift (C : ↥(irreducibleComponents X)) :
    IsIso (curveLift X Cv c hint hcover hdistinct C) := by
  haveI : IsClosedImmersion
      (curveLift X Cv c hint hcover hdistinct C ≫ componentUnionInclusion X {C}) := by
    rw [curveLift_comp]
    infer_instance
  haveI : IsClosedImmersion (curveLift X Cv c hint hcover hdistinct C) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (componentUnionInclusion X {C})
  haveI : Surjective (curveLift X Cv c hint hcover hdistinct C) := ⟨fun z => by
    have hz : (componentUnionInclusion X {C}).base z ∈ C.1 := by
      have := Set.mem_range_self (f := (componentUnionInclusion X {C}).base) z
      rwa [range_componentUnionInclusion, coe_componentClosedUnion_singleton] at this
    rw [← range_curveOf X Cv c hint hcover hdistinct C] at hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨p, (componentUnionInclusion X {C}).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.comp_base_apply, curveLift_comp, hp]⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The identification of the reduced component scheme `Z_C` with its curve. -/
def curveIdentification (C : ↥(irreducibleComponents X)) :
    componentUnionScheme X {C} ≅ Cv (curveOf X Cv c hint hcover hdistinct C) :=
  haveI := isIso_curveLift X Cv c hint hcover hdistinct C
  (asIso (curveLift X Cv c hint hcover hdistinct C)).symm

end Curves

section Corollary

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
  {S : Scheme.{u}} (ι : X ⟶ S) [IsClosedImmersion ι]
  (π : S ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
  (hconf : TransversalConfiguration ι)
  (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
  {J : Type u} [Fintype J] (c : J → (projectiveSpace k 1 ⟶ X)) [∀ j, IsClosedImmersion (c j)]
  (hcover : ⋃ j, Set.range (c j).base = Set.univ)
  (hdistinct : ∀ i j, Set.range (c i).base ⊆ Set.range (c j).base → i = j)

omit [IsAlgClosed k] in
/-- The projective line is integral (the accepted `projectiveSpace_isIntegral`). -/
theorem projectiveLine_isIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The irreducible component of `X` given by the `j`-th line. -/
def lineComponent (j : J) : ↥(irreducibleComponents X) :=
  componentOfCurve X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
    hcover hdistinct j

omit [IsAlgClosed k] [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X] in
theorem lineComponent_val (j : J) :
    (lineComponent X c hcover hdistinct j).1 = Set.range (c j).base := rfl

omit [IsAlgClosed k] [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X] in
/-- Every irreducible component of `X` is one of the lines. -/
theorem lineComponent_surjective : Function.Surjective (lineComponent X c hcover hdistinct) :=
  componentOfCurve_surjective X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
    hcover hdistinct

/-- The identifications of the components of a configuration of projective lines with `P¹`. -/
def lineIdentification (C : ↥(irreducibleComponents X)) :
    componentUnionScheme X {C} ≅ projectiveSpace k 1 :=
  curveIdentification X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
    hcover hdistinct C

include ι π hconf hdim hTree in
/-- **Corollary of Lemma 2.2 for a transversal configuration of projective lines.** The
multidegree map of `X` is bijective. -/
theorem rationalTreePicard_of_configuration :
    Function.Bijective (multidegreeHom k X (lineIdentification X c hcover hdistinct)) :=
  KltDP.Manuscript.S02.rationalTreePicard X (ι ≫ π) hdim hTree
    (hasTransverseComponentBranches_of_transversalConfiguration ι hconf) _

/-- `Pic X ≃* ℤ^{curves}`: the Picard group of a transversal tree of projective lines is free on
the curves. -/
def picardEquiv_of_configuration : X.Pic ≃* (J → Multiplicative ℤ) :=
  (MulEquiv.ofBijective _
    (rationalTreePicard_of_configuration X ι π hconf hdim hTree c hcover hdistinct)).trans
    (MulEquiv.arrowCongr
      (curveComponentEquiv X (fun _ => projectiveSpace k 1) c (fun _ => projectiveLine_isIntegral)
        hcover hdistinct).symm
      (MulEquiv.refl (Multiplicative ℤ)))

include ι π hconf hdim hTree in
/-- The degree-zero clause: a line bundle whose component exponent is zero on every curve is
trivial. -/
theorem trivial_of_degree_zero_of_configuration (L : InvertibleSheaf X)
    (hL : ∀ j : J, componentExponent k X {lineComponent X c hcover hdistinct j}
      (lineIdentification X c hcover hdistinct (lineComponent X c hcover hdistinct j)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  refine KltDP.Manuscript.S02.rationalTreePicard_trivial_of_degree_zero X (ι ≫ π) hdim hTree
    (hasTransverseComponentBranches_of_transversalConfiguration ι hconf)
    (lineIdentification X c hcover hdistinct) L (fun C => ?_)
  obtain ⟨j, rfl⟩ := lineComponent_surjective X c hcover hdistinct C
  exact hL j

/-- Universe check: the corollary at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀]
    [IsLocallyNoetherian X₀] [AlgebraicGeometry.IsReduced X₀] {S₀ : Scheme.{0}} (ι₀ : X₀ ⟶ S₀)
    [IsClosedImmersion ι₀] (π₀ : S₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType π₀]
    (hconf : TransversalConfiguration ι₀) (hdim : topologicalKrullDim X₀ ≤ 1)
    (hTree : (componentPointIncidenceGraph X₀).IsTree) {J₀ : Type} [Fintype J₀]
    (c₀ : J₀ → (projectiveSpace k₀ 1 ⟶ X₀)) [∀ j, IsClosedImmersion (c₀ j)]
    (hcover : ⋃ j, Set.range (c₀ j).base = Set.univ)
    (hdistinct : ∀ i j, Set.range (c₀ i).base ⊆ Set.range (c₀ j).base → i = j) :
    X₀.Pic ≃* (J₀ → Multiplicative ℤ) :=
  picardEquiv_of_configuration X₀ ι₀ π₀ hconf hdim hTree c₀ hcover hdistinct

end Corollary

end KltDP.Geometry.RationalTreePicard
