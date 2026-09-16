import KltDP.Examples.FrobeniusExceptionalPicardExponent

/-!
# The original exceptional normal line and its Picard exponent

The normal sheaf of the actual closed embedding is the existing sheaf of
module-linear local functionals on its actual conormal. The original
evaluation isomorphism proves that its class is the inverse conormal
class. Both sheaves and the original evaluation are then transported
through the existing exceptional-scheme/projective-line isomorphism.

The computed exponent is -1. No Proj twisting-sheaf identification,
divisor degree or self-intersection formula is assumed or asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

local instance structureSections_comm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The actual sheaf of module-linear local functionals, specialized to
the original structure sheaf of a scheme. -/
def schemeDualSheaf {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  KltDP.SheafOfModules.dual X.ringCatSheaf M

/-- For a closed embedding the normal sheaf is the actual dual of the
original conormal, hence Hom(I/I²,O) on the original closed scheme. -/
def schemeNormalSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] : X.Modules :=
  schemeDualSheaf (schemeConormalSheaf f)

/-- Normal sections are actual module-sheaf maps on the original over
site, not a separately specified space of normal directions. -/
def schemeNormalSectionsEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (U : X.Opens) :
    (schemeNormalSheaf f).val.obj (op U) ≃
      ((schemeConormalSheaf f).over U ⟶
        _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := Equiv.refl _

/-- Restriction of normal sections is the original restriction of
local linear functionals, with the existing over-site unit comparison. -/
theorem schemeNormalSectionsEquiv_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] {U V : X.Opens} (h : V ≤ U)
    (s : (schemeNormalSheaf f).val.obj (op U)) :
    schemeNormalSectionsEquiv f V
      ((schemeNormalSheaf f).val.map (homOfLE h).op s) =
      (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).inv.app
          (schemeConormalSheaf f) ≫
        (_root_.SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).map
          (schemeNormalSectionsEquiv f U s) ≫
        (_root_.SheafOfModules.overMapUnitIso X.ringCatSheaf (homOfLE h)).hom := rfl

section DualLine

variable {X : Scheme.{u}}

local instance frobeniusExceptionalNormalDualLineMonoidal : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
local instance : SymmetricCategory X.Modules := Scheme.Modules.symmetricCategory X

/-- The original evaluation against the actual dual is an isomorphism
for an actual locally free rank-one module sheaf. -/
def schemeDualEvaluationIso (L : InvertibleSheaf X) :
    L.obj ⊗ schemeDualSheaf L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  KltDP.SheafOfModules.evaluationIso X.sheaf.val X.ringCatSheaf.cond L.obj

/-- The forward map is exactly the original evaluation morphism. -/
theorem schemeDualEvaluationIso_hom (L : InvertibleSheaf X) :
    (schemeDualEvaluationIso L).hom =
      KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond L.obj := rfl

/-- Original evaluation gives the inverse relation on actual sheaf
isomorphism classes. -/
theorem schemeDualSheaf_class_mul (L : InvertibleSheaf X) :
    toSkeleton L.obj * toSkeleton (schemeDualSheaf L.obj) = (1 : Skeleton X.Modules) := by
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact Quotient.sound ⟨schemeDualEvaluationIso L ≪≫
    (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm⟩

/-- Local invertibility of the actual dual follows from its proved
tensor inverse and the existing tensor-invertible/rank-one equivalence. -/
theorem schemeDualSheaf_isInvertible (L : InvertibleSheaf X) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeDualSheaf L.obj) := by
  apply SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton
  exact isUnit_of_mul_eq_one_right _ _ (schemeDualSheaf_class_mul L)

/-- The original dual module, equipped with its derived rank-one property. -/
def dualInvertibleSheaf (L : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨schemeDualSheaf L.obj, schemeDualSheaf_isInvertible L⟩

/-- The dual's actual Picard class is the inverse of the original class. -/
theorem dualInvertibleSheaf_toPic (L : InvertibleSheaf X) :
    (dualInvertibleSheaf L).toPic = L.toPic⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  change (L.toPic : Skeleton X.Modules) *
    ((dualInvertibleSheaf L).toPic : Skeleton X.Modules) = 1
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact schemeDualSheaf_class_mul L

end DualLine

namespace AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The normal line of the original exceptional closed embedding. -/
def exceptionalNormalLine : InvertibleSheaf (exceptionalScheme I) :=
  dualInvertibleSheaf (exceptionalConormalLine I)

/-- Its module is the normal sheaf of the original exceptional inclusion. -/
theorem exceptionalNormalLine_obj :
    (exceptionalNormalLine I).obj = schemeNormalSheaf (exceptionalι I) := rfl

/-- The actual normal and conormal classes of the original embedding are inverse. -/
theorem exceptionalNormalLine_toPic :
    (exceptionalNormalLine I).toPic = (exceptionalConormalLine I).toPic⁻¹ :=
  dualInvertibleSheaf_toPic (exceptionalConormalLine I)

end AffineBlowup

namespace ProjectiveLinePicardExponent

variable (k : Type u) [Field k]

/-- Inversion in the original Picard group negates its actual exponent. -/
theorem value_inv (p : (projectiveSpace k 1).Pic) :
    value k p⁻¹ = -value k p := by
  have h : (hom k) p⁻¹ = ((hom k) p)⁻¹ :=
    MonoidHom.map_inv (hom k) p
  exact congrArg (fun z : Multiplicative ℤ => z.toAdd) h

end ProjectiveLinePicardExponent

end

end KltDP.Geometry

namespace KltDP.Examples.FrobeniusExceptionalNormal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalLine FrobeniusExceptionalPicardExponent

variable {k : Type u} [Field k]

/-- The original exceptional normal line transported to the original P1
by the same actual isomorphism used for the conormal. -/
def normalLine : InvertibleSheaf (projectiveSpace k 1) :=
  pullbackInvertibleSheaf (exceptionalProjectiveLineIso (k := k)).inv
    (exceptionalNormalLine (centerIdeal (k := k)))

/-- Its underlying module retains the original exceptional embedding. -/
theorem normalLine_obj :
    (normalLine (k := k)).obj =
      (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
        (schemeNormalSheaf (exceptionalι (centerIdeal (k := k)))) := rfl

local instance projectiveModulesMonoidal : MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

/-- The original evaluation, transported through the actual tensor and
unit pullback comparisons along the original exceptional/P1 isomorphism. -/
def conormalNormalEvaluationIso :
    (conormalLine (k := k)).obj ⊗ (normalLine (k := k)).obj ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf :=
  (schemeModulePullbackTensorIso (exceptionalProjectiveLineIso (k := k)).inv
    (exceptionalConormalSheaf (centerIdeal (k := k)))
    (schemeNormalSheaf (exceptionalι (centerIdeal (k := k))))).symm ≪≫
  (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).mapIso
    (schemeDualEvaluationIso (exceptionalConormalLine (centerIdeal (k := k)))) ≪≫
  schemeModulePullbackUnitIso (exceptionalProjectiveLineIso (k := k)).inv

/-- The transported evaluation uses the original evaluation map and
the original comparison isomorphisms, with no chosen tensor inverse. -/
theorem conormalNormalEvaluationIso_hom :
    (conormalNormalEvaluationIso (k := k)).hom =
      (schemeModulePullbackTensorIso (exceptionalProjectiveLineIso (k := k)).inv
        (exceptionalConormalSheaf (centerIdeal (k := k)))
        (schemeNormalSheaf (exceptionalι (centerIdeal (k := k))))).inv ≫
      (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).map
        (KltDP.SheafOfModules.evaluation
          (exceptionalScheme (centerIdeal (k := k))).sheaf.val
          (exceptionalScheme (centerIdeal (k := k))).ringCatSheaf.cond
          (exceptionalConormalSheaf (centerIdeal (k := k)))) ≫
      (schemeModulePullbackUnitIso (exceptionalProjectiveLineIso (k := k)).inv).hom := rfl

/-- The transported original normal class is the inverse of the
transported original conormal class. -/
theorem normalLine_toPic :
    (normalLine (k := k)).toPic = (conormalLine (k := k)).toPic⁻¹ := by
  calc
    (normalLine (k := k)).toPic =
        schemePicardPullbackHom (exceptionalProjectiveLineIso (k := k)).inv
          (exceptionalNormalLine (centerIdeal (k := k))).toPic :=
      (schemePicardPullbackHom_toPic (exceptionalProjectiveLineIso (k := k)).inv
        (exceptionalNormalLine (centerIdeal (k := k)))).symm
    _ = (schemePicardPullbackHom (exceptionalProjectiveLineIso (k := k)).inv
        (exceptionalConormalLine (centerIdeal (k := k))).toPic)⁻¹ := by
      rw [exceptionalNormalLine_toPic, map_inv]
    _ = (conormalLine (k := k)).toPic⁻¹ :=
      congrArg (fun p : (projectiveSpace k 1).Pic => p⁻¹)
        (schemePicardPullbackHom_toPic (exceptionalProjectiveLineIso (k := k)).inv
          (exceptionalConormalLine (centerIdeal (k := k))))

/-- The actual original exceptional normal has Picard exponent -1. -/
theorem normalPicardValue_eq_neg_one :
    ProjectiveLinePicardExponent.value k (normalLine (k := k)).toPic = -1 := by
  rw [normalLine_toPic, ProjectiveLinePicardExponent.value_inv, conormalPicardValue_eq_one]

/-- The standard-chart transition exponent of that same actual normal
line is -1. This does not assert a divisor-degree interpretation. -/
theorem normalExponent_eq_neg_one :
    ProjectiveLineSheafExponent.exponent k (normalLine (k := k)) = -1 := by
  rw [← ProjectiveLinePicardExponent.value_toPic]
  exact normalPicardValue_eq_neg_one

end KltDP.Examples.FrobeniusExceptionalNormal
