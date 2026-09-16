import KltDP.Geometry.RationalTreePicardIntrinsicNode
import KltDP.Geometry.AdicCompletionAlgebraEquiv
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# A geometric node over an algebraically closed field is an original node

The canonical inclusion of an algebraically closed field into its chosen
algebraic closure is an algebra equivalence. Consequently the original
geometric projection is an isomorphism. Its actual stalk map transports
the maximal-ideal completion, and coefficient transport takes the given
geometric ordinary-double-point model back to the original base field.

Every scalar structure below comes from the original structure morphism.
No irreducibility, integrality, reducedness, or splitting assumption is
added. In particular the adapter applies to the possibly reducible nodal
curves in the rational-tree argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.IntrinsicNodal

section OriginalStalkMaps

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

/-- Changing the affine base composes the original stalk coefficient maps. -/
@[reassoc]
theorem baseToStalkMap_Spec_map (f : X ⟶ Spec (CommRingCat.of S))
    (a : R →+* S) (x : X) :
    baseToStalkMap (f ≫ Spec.map (CommRingCat.ofHom a)) x =
      CommRingCat.ofHom a ≫ baseToStalkMap f x := by
  apply Spec.map_injective
  simp only [Spec_map_baseToStalkMap, Spec.map_comp, Category.assoc]

/-- The actual stalk map of a scheme isomorphism, with the original base scalars. -/
def stalkMapAlgEquivOfIsIso (g : X ⟶ Y) [IsIso g]
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    letI := stalkAlgebra f (g.base x)
    letI := stalkAlgebra (g ≫ f) x
    Y.presheaf.stalk (g.base x) ≃ₐ[R] X.presheaf.stalk x := by
  letI := stalkAlgebra f (g.base x)
  letI := stalkAlgebra (g ≫ f) x
  refine { (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  exact congrArg (fun φ : CommRingCat.of R ⟶ X.presheaf.stalk x => φ.hom r)
    (baseToStalkMap_comp g f x).symm

@[simp]
theorem stalkMapAlgEquivOfIsIso_apply (g : X ⟶ Y) [IsIso g]
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X)
    (a : Y.presheaf.stalk (g.base x)) :
    letI := stalkAlgebra f (g.base x)
    letI := stalkAlgebra (g ≫ f) x
    stalkMapAlgEquivOfIsIso g f x a = g.stalkMap x a := rfl

/-- Completion transport extends that same original stalk map. -/
def completedStalkAlgEquivOfIsIso (g : X ⟶ Y) [IsIso g]
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    letI := stalkAlgebra f (g.base x)
    letI := stalkAlgebra (g ≫ f) x
    completedStalk Y (g.base x) ≃ₐ[R] completedStalk X x := by
  letI := stalkAlgebra f (g.base x)
  letI := stalkAlgebra (g ≫ f) x
  exact maximalIdealCompletionAlgEquiv (stalkMapAlgEquivOfIsIso g f x)

@[simp]
theorem completedStalkAlgEquivOfIsIso_of (g : X ⟶ Y) [IsIso g]
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X)
    (a : Y.presheaf.stalk (g.base x)) :
    letI := stalkAlgebra f (g.base x)
    letI := stalkAlgebra (g ≫ f) x
    completedStalkAlgEquivOfIsIso g f x
        (AdicCompletion.of (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) _ a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) _
        (g.stalkMap x a) := by
  letI := stalkAlgebra f (g.base x)
  letI := stalkAlgebra (g ≫ f) x
  exact maximalIdealCompletionAlgEquiv_of (stalkMapAlgEquivOfIsIso g f x) a

end OriginalStalkMaps

section CoefficientTransport

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Power-series coefficient transport induced by the given algebra equivalence. -/
def powerSeriesCoefficientAlgEquiv (e : A ≃ₐ[R] B) :
    MvPowerSeries (Fin 2) A ≃ₐ[R] MvPowerSeries (Fin 2) B where
  __ := MvPowerSeries.mapAlgHom (σ := Fin 2) e.toAlgHom
  invFun := MvPowerSeries.map (Fin 2) e.symm.toRingHom
  left_inv a := by
    ext d
    exact e.symm_apply_apply (MvPowerSeries.coeff A d a)
  right_inv b := by
    ext d
    exact e.apply_symm_apply (MvPowerSeries.coeff B d b)

@[simp]
theorem powerSeriesCoefficientAlgEquiv_X (e : A ≃ₐ[R] B) (i : Fin 2) :
    powerSeriesCoefficientAlgEquiv e (MvPowerSeries.X i) = MvPowerSeries.X i :=
  MvPowerSeries.map_X e.toRingHom i

end CoefficientTransport

/-- The same coefficient equivalence descends through the literal ideal `(XY)`. -/
def ordinaryDoublePointModelAlgEquiv {R k K : Type u} [CommRing R]
    [Field k] [Field K] [Algebra R k] [Algebra R K] (e : k ≃ₐ[R] K) :
    ordinaryDoublePointModel k ≃ₐ[R] ordinaryDoublePointModel K :=
  Ideal.quotientEquivAlg _ _ (powerSeriesCoefficientAlgEquiv e) (by
    simp only [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, map_mul,
      powerSeriesCoefficientAlgEquiv_X])

section AlgebraicallyClosedBase

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The equivalence is the original canonical inclusion, with its original k-action. -/
def canonicalAlgebraicClosureAlgEquiv : k ≃ₐ[k] AlgebraicClosure k :=
  AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

@[simp]
theorem canonicalAlgebraicClosureAlgEquiv_apply (a : k) :
    canonicalAlgebraicClosureAlgEquiv (k := k) a = algebraMap k (AlgebraicClosure k) a :=
  rfl

/-- The original algebraic-closure base morphism is an isomorphism. -/
instance algebraicClosureToSpec_isIso : IsIso (algebraicClosureToSpec (k := k)) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (canonicalAlgebraicClosureAlgEquiv (k := k)).toRingEquiv.toCommRingCatIso.isIso_hom
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  infer_instance

/-- This is the literal projection of the chosen pullback, not a replacement scheme. -/
instance geometricProjection_isIso : IsIso (geometricProjection f) := by
  dsimp only [geometricProjection]
  infer_instance

omit [IsAlgClosed k] in
/-- The two original structure morphisms induce the expected tower on each
chosen geometric stalk. The equality of base maps is proved, not supplied. -/
theorem geometricStalk_scalarTower (y : geometricBaseChange f) :
    letI := stalkAlgebra (geometricStructure f) y
    letI := stalkAlgebra (geometricProjection f ≫ f) y
    IsScalarTower k (AlgebraicClosure k) ((geometricBaseChange f).presheaf.stalk y) := by
  letI := stalkAlgebra (geometricStructure f) y
  letI := stalkAlgebra (geometricProjection f ≫ f) y
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg
    (fun φ : CommRingCat.of k ⟶ (geometricBaseChange f).presheaf.stalk y => φ.hom)
    ((congrArg (fun g => baseToStalkMap g y) (geometricProjection_over f)).trans
      (baseToStalkMap_Spec_map (geometricStructure f)
        (algebraMap k (AlgebraicClosure k)) y))

/-- A geometric ordinary double point gives the ordinary double point on
the original stalk at its actual image, with the original k-structure. -/
theorem isOrdinaryDoublePoint_of_geometric (y : geometricBaseChange f)
    (hclosed : IsClosed ({(geometricProjection f).base y} : Set X))
    (hy : IsOrdinaryDoublePoint (geometricStructure f) y) :
    IsOrdinaryDoublePoint f ((geometricProjection f).base y) := by
  letI := stalkAlgebra (geometricStructure f) y
  letI := stalkAlgebra (geometricProjection f ≫ f) y
  letI := stalkAlgebra f ((geometricProjection f).base y)
  letI : IsScalarTower k (AlgebraicClosure k)
      ((geometricBaseChange f).presheaf.stalk y) := geometricStalk_scalarTower f y
  rcases hy with ⟨_, ⟨e⟩⟩
  refine ⟨hclosed, ⟨?_⟩⟩
  exact (completedStalkAlgEquivOfIsIso (geometricProjection f) f y).trans
    ((e.restrictScalars k).trans
      (ordinaryDoublePointModelAlgEquiv (canonicalAlgebraicClosureAlgEquiv (k := k))).symm)

/-- Geometric nodality specializes to the completed original closed stalk
over an algebraically closed base. No curve irreducibility is required. -/
theorem IsNode.isOrdinaryDoublePoint {x : X} (hx : IsNode f x) :
    IsOrdinaryDoublePoint f x := by
  rcases hx with ⟨hclosed, y, rfl, hy⟩
  exact isOrdinaryDoublePoint_of_geometric f y hclosed hy

end AlgebraicallyClosedBase

end KltDP.Geometry.IntrinsicNodal
