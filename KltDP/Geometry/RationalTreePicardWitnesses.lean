import KltDP.Geometry.RationalTreePicardDualGraphTransport
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveFiniteType

/-!
# Nonvacuity witnesses for the rational-tree Picard lemma

BRIEF19, task 1 (a): the hypotheses of `KltDP.Manuscript.S02.rationalTreePicard`, in the form of
the configuration corollary `rationalTreePicard_of_configuration`, are satisfied by a single
projective line. Take `X = S = projectiveSpace k 1`, `ι = 𝟙`, the single curve `c () = 𝟙`, and the
structure morphism `projectiveSpaceToSpec k 1` (locally of finite type). `X` is Noetherian,
locally Noetherian and integral (accepted `projectiveSpace_noetherianSpace`,
`projectiveSpace_isLocallyNoetherian`, `projectiveSpace_isIntegral`), of dimension one
(`projectiveSpace_topologicalKrullDim`), with a single irreducible component
(`irreducibleComponents_eq_singleton`) and no intersection point, so the incidence graph has one
vertex and is a tree, and the transversality conditions are vacuous. Hence
`Pic(P¹) ≃* ℤ` (`singleLinePicardEquivInt`, through `singleLinePicardEquiv : Pic ≃* (PUnit → ℤ)`),
and a line bundle of exponent zero on the line is trivial (`singleLine_trivial_of_degree_zero`).
A universe check instantiates the statement at `Scheme.{0}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace SimpleGraph

universe u

namespace KltDP.Geometry.RationalTreePicard

section SingleLine

variable (k : Type u) [Field k] [IsAlgClosed k]

local instance singleLine_noetherianSpace : NoetherianSpace (projectiveSpace k 1) :=
  projectiveSpace_noetherianSpace k 1

local instance singleLine_isLocallyNoetherian : IsLocallyNoetherian (projectiveSpace k 1) :=
  projectiveSpace_isLocallyNoetherian k 1

local instance singleLine_isIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance singleLine_locallyOfFiniteType :
    LocallyOfFiniteType (projectiveSpaceToSpec k 1) :=
  projectiveSpaceToSpec_locallyOfFiniteType k 1

/-- The single curve of the witness: the identity of `P¹`. -/
def singleLineCurve : PUnit.{u + 1} → (projectiveSpace k 1 ⟶ projectiveSpace k 1) := fun _ => 𝟙 _

instance singleLineCurve_isClosedImmersion (j : PUnit.{u + 1}) :
    IsClosedImmersion (singleLineCurve k j) := by
  show IsClosedImmersion (𝟙 _)
  infer_instance

omit [IsAlgClosed k] in
theorem singleLine_cover : ⋃ j : PUnit.{u + 1}, Set.range (singleLineCurve k j).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨PUnit.unit, x, ?_⟩
  simp [singleLineCurve]

omit [IsAlgClosed k] in
theorem singleLine_distinct (i j : PUnit.{u + 1})
    (_ : Set.range (singleLineCurve k i).base ⊆ Set.range (singleLineCurve k j).base) : i = j :=
  Subsingleton.elim _ _

omit [IsAlgClosed k] in
/-- `P¹` has a single irreducible component. -/
theorem singleLine_components_subsingleton :
    Subsingleton ↥(irreducibleComponents (projectiveSpace k 1)) := by
  haveI : IrreducibleSpace (projectiveSpace k 1) := projectiveSpace_irreducibleSpace k 1
  have huniv : ∀ C : ↥(irreducibleComponents (projectiveSpace k 1)),
      (C : Set (projectiveSpace k 1)) = Set.univ := by
    intro C
    have h : (C : Set (projectiveSpace k 1)) ∈
        ({Set.univ} : Set (Set (projectiveSpace k 1))) := by
      rw [← irreducibleComponents_eq_singleton]
      exact C.2
    exact Set.mem_singleton_iff.mp h
  constructor
  intro C D
  exact Subtype.ext ((huniv C).trans (huniv D).symm)

omit [IsAlgClosed k] in
/-- `P¹` has no component intersection points. -/
theorem singleLine_intersectionPoints_isEmpty :
    IsEmpty ↥(componentIntersectionPoints (projectiveSpace k 1)) := by
  haveI := singleLine_components_subsingleton k
  constructor
  rintro ⟨x, C, D, hCD, -, -⟩
  exact hCD (Subsingleton.elim C D)

omit [IsAlgClosed k] in
/-- The incidence graph of `P¹` has one vertex: it is a tree. -/
theorem singleLine_isTree : (componentPointIncidenceGraph (projectiveSpace k 1)).IsTree := by
  haveI := singleLine_components_subsingleton k
  haveI := singleLine_intersectionPoints_isEmpty k
  haveI hsub : Subsingleton (↥(irreducibleComponents (projectiveSpace k 1)) ⊕
      ↥(componentIntersectionPoints (projectiveSpace k 1))) := by
    constructor
    rintro (C | p) (D | q)
    · rw [Subsingleton.elim C D]
    · exact isEmptyElim q
    · exact isEmptyElim p
    · exact isEmptyElim p
  haveI : Nonempty (projectiveSpace k 1) := projectiveSpace_nonempty k 1
  haveI hne : Nonempty (↥(irreducibleComponents (projectiveSpace k 1)) ⊕
      ↥(componentIntersectionPoints (projectiveSpace k 1))) :=
    ⟨Sum.inl ⟨irreducibleComponent (Classical.arbitrary _),
      irreducibleComponent_mem_irreducibleComponents _⟩⟩
  refine ⟨⟨fun v w => ?_⟩, fun v c hc => ?_⟩
  · have hvw := Subsingleton.elim v w
    subst hvw
    exact Reachable.refl v
  · cases c with
    | nil => exact hc.ne_nil rfl
    | cons h p => exact (componentPointIncidenceGraph _).ne_of_adj h (Subsingleton.elim _ _)

omit [IsAlgClosed k] in
/-- With a single component the transversality conditions are vacuous. -/
theorem singleLine_transversalConfiguration :
    TransversalConfiguration (𝟙 (projectiveSpace k 1)) := by
  haveI := singleLine_components_subsingleton k
  exact ⟨fun C D _ _ _ _ _ => Or.inl (Subsingleton.elim C D),
    fun C D hCD => absurd (Subsingleton.elim C D) hCD⟩

omit [IsAlgClosed k] in
theorem singleLine_dim : topologicalKrullDim (projectiveSpace k 1) ≤ 1 := by
  rw [projectiveSpace_topologicalKrullDim, Nat.cast_one]

/-- **Witness (a): the multidegree map of a single projective line is bijective.** -/
theorem singleLine_rationalTreePicard :
    Function.Bijective (multidegreeHom k (projectiveSpace k 1)
      (lineIdentification (projectiveSpace k 1) (singleLineCurve k) (singleLine_cover k)
        (singleLine_distinct k))) :=
  rationalTreePicard_of_configuration (projectiveSpace k 1) (𝟙 _) (projectiveSpaceToSpec k 1)
    (singleLine_transversalConfiguration k) (singleLine_dim k) (singleLine_isTree k)
    (singleLineCurve k) (singleLine_cover k) (singleLine_distinct k)

/-- `Pic(P¹) ≃* ℤ^{Unit}`. -/
def singleLinePicardEquiv : (projectiveSpace k 1).Pic ≃* (PUnit.{u + 1} → Multiplicative ℤ) :=
  picardEquiv_of_configuration (projectiveSpace k 1) (𝟙 _) (projectiveSpaceToSpec k 1)
    (singleLine_transversalConfiguration k) (singleLine_dim k) (singleLine_isTree k)
    (singleLineCurve k) (singleLine_cover k) (singleLine_distinct k)

/-- `Pic(P¹) ≃* ℤ`. -/
def singleLinePicardEquivInt : (projectiveSpace k 1).Pic ≃* Multiplicative ℤ :=
  (singleLinePicardEquiv k).trans (MulEquiv.piUnique fun _ : PUnit.{u + 1} => Multiplicative ℤ)

/-- A line bundle on `P¹` of exponent zero on the line is trivial. -/
theorem singleLine_trivial_of_degree_zero (L : InvertibleSheaf (projectiveSpace k 1))
    (hL : ∀ j : PUnit.{u + 1}, componentExponent k (projectiveSpace k 1)
      {lineComponent (projectiveSpace k 1) (singleLineCurve k) (singleLine_cover k)
        (singleLine_distinct k) j}
      (lineIdentification (projectiveSpace k 1) (singleLineCurve k) (singleLine_cover k)
        (singleLine_distinct k)
        (lineComponent (projectiveSpace k 1) (singleLineCurve k) (singleLine_cover k)
          (singleLine_distinct k) j)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :=
  trivial_of_degree_zero_of_configuration (projectiveSpace k 1) (𝟙 _) (projectiveSpaceToSpec k 1)
    (singleLine_transversalConfiguration k) (singleLine_dim k) (singleLine_isTree k)
    (singleLineCurve k) (singleLine_cover k) (singleLine_distinct k) L hL

/-- Universe check: the witness at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] :
    (projectiveSpace k₀ 1).Pic ≃* Multiplicative ℤ :=
  singleLinePicardEquivInt k₀

end SingleLine

end KltDP.Geometry.RationalTreePicard
