import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# `C·C = −deg_C(conormal line)` for a prime curve carried by a closed immersion (F10)

Let `X` be a normal projective surface over an algebraically closed field, regular at every point,
and let `ι : C ⟶ X` be a closed immersion with reduced source whose range is the prime curve `E`
and whose kernel ideal sheaf `I(C) = ker(O_X → ι_*O_C)` is invertible. Then

* `conormalLine ι hinv` is the invertible sheaf `ι^*I(C) = I/I²` on `C`;
* `selfIntersectionNumber_eq_neg_lineDegree`: `E·E = −deg_E(I/I²)` in the accepted
  `selfIntersectionNumber` of F03, the conormal line being transported to the prime-curve scheme
  along the accepted isomorphism `PrimeCurveInclusionLift.lift E ι`;
* `lineDegree_eq_euler_difference`: the degree on `E` of a line pulled back along an isomorphism
  over `k` is the Euler difference of that line on the other scheme (accepted degree transport).

This is the accepted stage computation
`KltDP.Examples.FrobeniusStageExceptionalSelfIntersection.selfIntersectionNumber_eq_neg_conormal_degree`
made generic: nothing about blowups, plane charts or towers is used. The ingredients are the
accepted `effectiveCartierKernelIso` (`O_X(−D_E) ≅ I(E)`), `kernelIsoOfKerEq`, the identification
of the ideal sheaf of `D_E` with the vanishing ideal of `E`
(`primeCurveCartier_idealData_eq_vanishingIdeal`) and `PrimeCurveInclusionLift`.

No literature statement is used here; the admitted 0AYX additivity enters only through the accepted
`intersectionNumber_neg`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveConormalDegree

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The conormal line `I/I² = ι^*I(C)` of a closed immersion with invertible kernel ideal. -/
def conormalLine {Y C : Scheme.{u}} (ι : C ⟶ Y)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι)) :
    InvertibleSheaf C :=
  pullbackInvertibleSheaf ι ⟨schemeKernelIdeal ι, hinv⟩

theorem conormalLine_obj {Y C : Scheme.{u}} (ι : C ⟶ Y)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι)) :
    (conormalLine ι hinv).obj = schemeConormalSheaf ι := rfl

section Surface

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}

/-- The ideal sheaf of the Cartier divisor `D_E` of the prime curve `E` is the kernel ideal of any
closed immersion with reduced source carrying `E`. -/
theorem primeCurveCartier_ker (hreg : ∀ x : X.Point, RegularPoint X.toScheme x)
    (E : X.PrimeCurve) {C : Scheme.{u}} (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base) :
    (effectiveCartierIdealDataOfRegularEquations X.toScheme (X.primeCurveCartier hreg E)
        (X.primeCurveCartier_hasRegularEquations hreg E)).gluedTo.ker = ι.ker := by
  rw [effectiveCartierIdealDataOfRegularEquations_ker,
    X.primeCurveCartier_idealData_eq_vanishingIdeal hreg E,
    PrimeCurveInclusionLift.ker_eq_vanishingIdeal E ι hE]

/-- `O_X(−D_E) ≅ I(C)`: the negative Cartier module of `E` is the kernel ideal module of `ι`. -/
def negativeCartierKernelIso (hreg : ∀ x : X.Point, RegularPoint X.toScheme x)
    (E : X.PrimeCurve) {C : Scheme.{u}} (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base) :
    cartierDivisorModule X.toScheme (-(X.primeCurveCartier hreg E)) ≅ schemeKernelIdeal ι :=
  effectiveCartierKernelIso X.toScheme (X.primeCurveCartier hreg E)
      (X.primeCurveCartier_hasRegularEquations hreg E) ≪≫
    kernelIsoOfKerEq _ ι (primeCurveCartier_ker hreg E ι hE)

/-- The conormal line transported to the prime-curve scheme of `E`. -/
def curveConormalLine (E : X.PrimeCurve) {C : Scheme.{u}} (ι : C ⟶ X.toScheme)
    [IsClosedImmersion ι] [IsReduced C] (hE : (E : Set X.toScheme) = Set.range ι.base)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal ι)) :
    InvertibleSheaf E.toScheme :=
  pullbackInvertibleSheaf (inv (PrimeCurveInclusionLift.lift E ι hE)) (conormalLine ι hinv)

/-- `E · (−D_E) = deg_E(I/I²)`. -/
theorem intersectionNumber_neg_primeCurveCartier
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (E : X.PrimeCurve) {C : Scheme.{u}}
    (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal ι)) :
    E.intersectionNumber (-(X.primeCurveCartier hreg E)) =
      E.lineDegree (curveConormalLine E ι hE hinv) := by
  unfold PrimeCurve.intersectionNumber
  apply E.lineDegree_eq_of_iso
  refine (schemeModulePullback E.inclusion).mapIso (negativeCartierKernelIso hreg E ι hE) ≪≫ ?_
  rw [PrimeCurveInclusionLift.inclusion_eq_inv_lift E ι hE]
  exact (schemeModulePullbackCompIso (inv (PrimeCurveInclusionLift.lift E ι hE)) ι).symm.app
    (schemeKernelIdeal ι)

/-- **`E·E = −deg_E(I/I²)`** in the accepted `selfIntersectionNumber`. -/
theorem selfIntersectionNumber_eq_neg_lineDegree
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (E : X.PrimeCurve) {C : Scheme.{u}}
    (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal ι)) :
    E.selfIntersectionNumber hreg = -E.lineDegree (curveConormalLine E ι hE hinv) := by
  rw [← intersectionNumber_neg_primeCurveCartier hreg E ι hE hinv,
    PrimeCurve.intersectionNumber_neg, neg_neg]
  rfl

/-- **`E·E = −1` from a conormal line of degree one.** -/
theorem selfIntersectionNumber_eq_neg_one_of_lineDegree_eq_one
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (E : X.PrimeCurve) {C : Scheme.{u}}
    (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal ι))
    (hdeg : E.lineDegree (curveConormalLine E ι hE hinv) = 1) :
    E.selfIntersectionNumber hreg = -1 := by
  rw [selfIntersectionNumber_eq_neg_lineDegree hreg E ι hE hinv, hdeg]

/-- The degree on `E` of a line pulled back along an isomorphism over `k` is the Euler difference
of that line on the other scheme. -/
theorem lineDegree_eq_euler_difference (E : X.PrimeCurve) {G : Scheme.{u}}
    (φ : E.toScheme ⟶ G) [IsIso φ] (g : G ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ g = E.toSpec)
    (L : InvertibleSheaf E.toScheme) (M : InvertibleSheaf G)
    (e : L.obj ≅ (schemeModulePullback φ).obj M.obj) :
    E.lineDegree L =
      eulerCharacteristic g M.obj -
        eulerCharacteristic g (_root_.SheafOfModules.unit G.ringCatSheaf) := by
  rw [← E.picardDegree_toPic L,
    SchemeKernelIdealIsoTransport.toPic_eq_pullback_of_iso φ M L e,
    PrimeCurveDegreeTransport.picardDegree_pullback_iso E φ g hφ M.toPic]
  unfold PrimeCurveDegreeTransport.eulerDegree
  rw [picardEulerValue_toPic, picardEulerValue_one]

/-- The degree on `E` of the conormal line, computed on the carrier `C` with its `k`-structure. -/
theorem lineDegree_curveConormalLine_eq_euler_difference (E : X.PrimeCurve) {C : Scheme.{u}}
    (ι : C ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced C]
    (hE : (E : Set X.toScheme) = Set.range ι.base)
    (hinv : KltDP.SheafOfModules.IsInvertible (R := X.toScheme.ringCatSheaf)
      (schemeKernelIdeal ι)) :
    E.lineDegree (curveConormalLine E ι hE hinv) =
      eulerCharacteristic (ι ≫ X.structureMorphism) (conormalLine ι hinv).obj -
        eulerCharacteristic (ι ≫ X.structureMorphism)
          (_root_.SheafOfModules.unit C.ringCatSheaf) := by
  refine lineDegree_eq_euler_difference E (inv (PrimeCurveInclusionLift.lift E ι hE))
    (ι ≫ X.structureMorphism) ?_ _ (conormalLine ι hinv) (Iso.refl _)
  rw [← Category.assoc, ← PrimeCurveInclusionLift.inclusion_eq_inv_lift E ι hE]
  rfl

end Surface

end KltDP.Geometry.PrimeCurveConormalDegree
