import KltDP.Geometry.CartierRationalPointRestriction
import KltDP.Geometry.ProjectiveStructureSheafHZero
import KltDP.Geometry.ProperInvertibleSectionBasis
import KltDP.Geometry.ModuleCohomologyEuler

/-! A degree-one Cartier point on the original proper integral genus-zero scheme
has exactly two global sections in its original positive Cartier line.
The point, its kernel, and actual H1 vanishing are geometric hypotheses of this helper;
no H0 dimension or global generation is supplied. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CartierRationalPoint

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [hiClosed : IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

include hiClosed hker in
/-- The actual positive Cartier point line has h0=2, by its original exact sequence. -/
theorem cohomologyDimension_eq_two
    (f : X ⟶ Spec (CommRingCat.of k)) [hproper : IsProper f]
    (hi : i ≫ f = 𝟙 _)
    (hH1 : Subsingleton (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1)) :
    cohomologyDimension f (cartierDivisorModule X E) 0 = 2 := by
  let S := EffectiveCartierPositive.sequence X E hE
  let e₁ := EffectiveCartierPositive.firstIsoUnit X E hE
  let e₂ := EffectiveCartierPositive.middleIso X E hE
  let e₃ := quotientIsoPoint E hE i hker
  letI := hH1
  letI : Subsingleton (H S.X₁ 1) :=
    ((zariskiFunctor X 1).mapIso e₁).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
      inferInstance
  letI : FiniteDimensional k ((baseFunctor f 0).obj
      (_root_.SheafOfModules.unit X.ringCatSheaf)) :=
    CompleteLinearSystemSections.cohomology_finiteDimensional f (InvertibleSheaf.trivial X)
  letI : FiniteDimensional k ((baseFunctor f 0).obj (cartierDivisorModule X E)) :=
    CompleteLinearSystemSections.cohomology_finiteDimensional f
      (cartierDivisorInvertibleSheaf X E)
  letI : FiniteDimensional k ((baseFunctor f 0).obj
      (RationalPointPushforward.unitPushforward i)) :=
    RationalPointPushforward.cohomology_finiteDimensional i f hi 0
  letI : FiniteDimensional k ((baseFunctor f 0).obj S.X₁) :=
    ((baseFunctor f 0).mapIso e₁).toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional k ((baseFunctor f 0).obj S.X₂) :=
    ((baseFunctor f 0).mapIso e₂).toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional k ((baseFunctor f 0).obj S.X₃) :=
    ((baseFunctor f 0).mapIso e₃).toLinearEquiv.symm.finiteDimensional
  have h := cohomology_dimension_rank_zero f S (EffectiveCartierPositive.shortExact X E hE)
  rw [connectingRank_eq_zero f S (EffectiveCartierPositive.shortExact X E hE) 0] at h
  rw [cohomologyDimension_eq_of_iso f e₁,
    cohomologyDimension_eq_of_iso f e₂, cohomologyDimension_eq_of_iso f e₃,
    RationalPointPushforward.cohomologyDimension_zero i f hi] at h
  have hunit : cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 = 1 :=
    StructureSheafCohomology.hZero_finrank_one f
  rw [hunit] at h
  omega

#print axioms cohomologyDimension_eq_two

end KltDP.Geometry.CartierRationalPoint
