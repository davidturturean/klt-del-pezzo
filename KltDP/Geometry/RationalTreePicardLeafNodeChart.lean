import KltDP.Geometry.RationalTreePicardTransverseNode
import KltDP.Geometry.RationalTreePicardComponentIntersectionFinite
import KltDP.Geometry.RationalTreePicardComponentIntersectionChart
import KltDP.Geometry.RationalTreePicardClosedFrameDescent
import KltDP.Geometry.AffineFiniteType

/-!
# Closed-branch charts at a leaf node of an actual reduced curve

This assembles, on an actual affine chart `U` through a leaf node `q` of an
actual reduced Noetherian curve `X`, the closed-branch data required by the
affine frame descent: the two original component ideals
`I = componentChartIdeal X {C} U` and `J = componentChartIdeal X {C}ᶜ U` of
the leaf component `C` and of the union of the other components.

* `I ⊓ J = ⊥`: the two closed pieces cover `Spec Γ(X, U)` scheme-theoretically
  (from reducedness of `X`, existing `componentChartIdeal_inf_compl`).
* `zeroLocus (I ⊔ J) = {q}`: the pieces meet only at the original leaf point
  (from the finite component-point tree, existing `ComponentLeaf`).
* `I ⊔ J = q.asIdeal`: the intersection is the reduced point, derived from
  first-order transversality of the two original branch germs in the actual
  scheme stalk (existing `nodeIdeal_eq_of_transverse_localization`).

Over an algebraically closed base with locally finite type structure morphism,
the intersection fiber ring `Γ(X, U) ⧸ (I ⊔ J)` is then the ground field, and
the actual intersection chart scheme is `Spec k`. Finally, any original
invertible sheaf on `Spec Γ(X, U)` with actual frames on the two closed pieces
is trivial, by the existing affine closed-frame descent.

Remaining geometric hypotheses (stated, not derived here): the curve has
Krull dimension at most one, its component-point incidence graph is a tree,
and `HasTransverseComponentBranches X` holds. The last is the transverse-germ
form of the nodal hypothesis; deriving it from the intrinsic completed-stalk
normal form `IntrinsicNodal.IsNode` is still open, as are producing the
component frames from degree zero on projective-line components and gluing
the resulting affine trivializations over a global cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- Transverse branch germs at every original point where a component meets
the union of the other components: for every affine chart through the point,
the two original component ideals contain germs whose cotangent classes are
independent in a two-dimensional actual cotangent space. This is the
transverse-germ form of the nodal hypothesis. -/
def HasTransverseComponentBranches : Prop :=
  ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
    q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) →
    ∀ (U : X.affineOpens) (hq : q ∈ U.1),
      ∃ w : Fin 2 → maximalIdeal (X.presheaf.stalk q),
        (w 0 : X.presheaf.stalk q) ∈
            (componentChartIdeal X {C} U).map (X.presheaf.germ U.1 q hq).hom ∧
        (w 1 : X.presheaf.stalk q) ∈
            (componentChartIdeal X ({C}ᶜ) U).map (X.presheaf.germ U.1 q hq).hom ∧
        Module.finrank (ResidueField (X.presheaf.stalk q))
            (CotangentSpace (X.presheaf.stalk q)) = 2 ∧
        LinearIndependent (ResidueField (X.presheaf.stalk q))
            (fun i => (maximalIdeal (X.presheaf.stalk q)).toCotangent (w i))

/-- The closed-branch chart data at a leaf node, for the original component
ideals of the leaf component and of the complementary union on an affine chart
through the node. All three fields are about the original ideals. -/
structure LeafNodeChart (C : ↥(irreducibleComponents X)) (q : X)
    (U : X.affineOpens) (hq : q ∈ U.1) : Prop where
  cover : componentChartIdeal X {C} U ⊓ componentChartIdeal X ({C}ᶜ) U = ⊥
  support : PrimeSpectrum.zeroLocus
      (componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U : Ideal Γ(X, U.1)) =
    {U.2.primeIdealOf ⟨q, hq⟩}
  sup_eq : componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U =
    (U.2.primeIdealOf ⟨q, hq⟩).asIdeal

variable {X}

/-- The intersection quotient of a leaf-node chart is reduced: it is the
quotient by the original prime ideal of the node. -/
theorem LeafNodeChart.isReduced {C : ↥(irreducibleComponents X)} {q : X}
    {U : X.affineOpens} {hq : q ∈ U.1} (h : LeafNodeChart X C q U hq) :
    _root_.IsReduced (Γ(X, U.1) ⧸
      (componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U)) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  rw [h.sup_eq]
  exact (U.2.primeIdealOf ⟨q, hq⟩).isPrime.isRadical

variable (X)

/-- On an actual reduced Noetherian curve whose component-point incidence
graph is a tree, some component is a leaf meeting the others in exactly one
original point, and every affine chart through that point carries the full
closed-branch chart data, given transverse branch germs. -/
theorem exists_leafNodeChart [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    [Nontrivial ↥(irreducibleComponents X)]
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X) :
    ∃ (C : ↥(irreducibleComponents X)) (q : X),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q} ∧
      ∀ (U : X.affineOpens) (hq : q ∈ U.1), LeafNodeChart X C q U hq := by
  obtain ⟨C, q, hcut, hcharts⟩ := exists_component_leaf_chart_support X
    (componentIntersectionPoints_finite X hdim) hTree
  refine ⟨C, q, hcut, fun U hq => ?_⟩
  have hmem : q ∈ C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := by
    rw [hcut]
    exact Set.mem_singleton q
  obtain ⟨w, hw0, hw1, hdim2, hind⟩ := htrans C q hmem.1 hmem.2 U hq
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk q) :=
    X.presheaf.algebra_section_stalk ⟨q, hq⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk q)
      (U.2.primeIdealOf ⟨q, hq⟩).asIdeal := U.2.isLocalization_stalk ⟨q, hq⟩
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing (X.presheaf.stalk q) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨q, hq⟩).asIdeal.primeCompl
      (X.presheaf.stalk q) inferInstance
  exact
    { cover := componentChartIdeal_inf_compl X {C} U
      support := hcharts U hq
      sup_eq := nodeIdeal_eq_of_transverse_localization Γ(X, U.1)
        (componentChartIdeal X {C} U) (componentChartIdeal X ({C}ᶜ) U)
        (U.2.primeIdealOf ⟨q, hq⟩) (hcharts U hq) (X.presheaf.stalk q) w hw0 hw1 hdim2 hind }

section BaseField

variable {X} {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)

/-- The intersection fiber ring of a leaf-node chart is the ground field,
with the algebra structure induced by the actual structure morphism. -/
def LeafNodeChart.nodeFieldEquiv :
    letI := affineSectionsAlgebra f U.2
    (Γ(X, U.1) ⧸ (componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U)) ≃ₐ[k] k := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact reducedNodeFieldEquiv Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support k

/-- The actual intersection chart scheme of the leaf component and the
complementary union is the reduced rational point `Spec k`. -/
def LeafNodeChart.intersectionChartIso :
    componentIntersectionChart X {C} U ≅ Spec (CommRingCat.of k) := by
  letI := affineSectionsAlgebra f U.2
  exact Scheme.Spec.mapIso (h.nodeFieldEquiv f).symm.toRingEquiv.toCommRingCatIso.op

/-- An original invertible sheaf on the leaf-node chart with actual frames on
the two original closed pieces is trivial, by the existing affine descent. -/
def LeafNodeChart.frameUnitIso (L : InvertibleSheaf (Spec (CommRingCat.of Γ(X, U.1))))
    (leftFrame : (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).obj L.obj ≅
      _root_.SheafOfModules.unit
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf)
    (rightFrame : (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).obj L.obj ≅
      _root_.SheafOfModules.unit
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameUnitIso k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame h.cover

end BaseField

end KltDP.Geometry.RationalTreePicard
