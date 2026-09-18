import KltDP.Geometry.EffectiveCartierPositiveSequence
import KltDP.Geometry.InvertibleSheafOnField
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.RationalPointPushforwardCohomology

/-! The actual positive Cartier restriction to an actual rational Cartier point.
The point is given by its original closed immersion and original kernel ideal.
The line on that point is proved trivial; no frame or section lift is assumed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.CartierRationalPoint

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance pointMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

/-- The quotient of the original positive sequence is the original point's structure module. -/
def quotientIsoPoint :
    (EffectiveCartierPositive.sequence X E hE).X₃ ≅
      RationalPointPushforward.unitPushforward i := by
  have hk : (effectiveCartierInclusion X E hE).ker = i.ker := by
    rw [hker]
    exact (effectiveCartierIdealDataOfRegularEquations X E hE).ker_gluedTo
  let e := Classical.choice (InvertibleSheafOnField.exists_unitIso k
    (pullbackInvertibleSheaf i (cartierDivisorInvertibleSheaf X E)))
  exact (tensorRight (cartierDivisorModule X E)).mapIso
      (pushforwardUnitIsoOfKerEq (effectiveCartierInclusion X E hE) i hk) ≪≫
    Classical.choice (InvertibleSheaf.exists_pushforwardUnitTensorIso i
      (cartierDivisorInvertibleSheaf X E)) ≪≫
    (schemeModulePushforward i).mapIso e

/-- Restriction of the original positive Cartier line, expressed in the proved point frame. -/
def restriction : cartierDivisorModule X E ⟶ RationalPointPushforward.unitPushforward i :=
  (EffectiveCartierPositive.middleIso X E hE).inv ≫
    (EffectiveCartierPositive.sequence X E hE).g ≫ (quotientIsoPoint E hE i hker).hom

/-- Vanishing H1 of the original structure module lifts every actual point value. -/
theorem sections_surjective
    (hH1 : Subsingleton (ModuleCohomology.H
      (_root_.SheafOfModules.unit X.ringCatSheaf) 1)) :
    Function.Surjective ((restriction E hE i hker).val.app (op (⊤ : X.Opens))) := by
  let S := EffectiveCartierPositive.sequence X E hE
  let e₁ := EffectiveCartierPositive.firstIsoUnit X E hE
  let e₂ := EffectiveCartierPositive.middleIso X E hE
  let e₃ := quotientIsoPoint E hE i hker
  letI := hH1
  letI : Subsingleton (ModuleCohomology.H S.X₁ 1) :=
    ((ModuleCohomology.zariskiFunctor X 1).mapIso e₁).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
      inferInstance
  intro t
  obtain ⟨v, hv⟩ := ModuleCohomology.sections_surjective_of_hOne_zero S
    (EffectiveCartierPositive.shortExact X E hE) (e₃.inv.val.app (op ⊤) t)
  refine ⟨e₂.hom.val.app (op ⊤) v, ?_⟩
  have h₂ := congrArg (fun q : S.X₂ ⟶ S.X₂ => q.val.app (op ⊤) v) e₂.hom_inv_id
  change e₂.inv.val.app (op ⊤) (e₂.hom.val.app (op ⊤) v) = v at h₂
  have h₃ := congrArg
    (fun q : RationalPointPushforward.unitPushforward i ⟶
        RationalPointPushforward.unitPushforward i => q.val.app (op ⊤) t) e₃.inv_hom_id
  change e₃.hom.val.app (op ⊤) (e₃.inv.val.app (op ⊤) t) = t at h₃
  change e₃.hom.val.app (op ⊤)
    (S.g.val.app (op ⊤) (e₂.inv.val.app (op ⊤) (e₂.hom.val.app (op ⊤) v))) = t
  rw [h₂, hv, h₃]

#print axioms quotientIsoPoint
#print axioms sections_surjective

end KltDP.Geometry.CartierRationalPoint
