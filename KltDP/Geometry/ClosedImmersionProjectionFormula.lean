import KltDP.Geometry.InvertibleTensorExact
import KltDP.Geometry.SchemeModulePullbackTensorNaturality
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeModuleFunctorial

/-!
# The projection formula for tensor-invertible sheaves

For a scheme morphism `f : Y ⟶ X` and a module `L` on `X` with a tensor inverse `L'`
(`L ⊗ L' ≅ 𝟙_`, `L' ⊗ L ≅ 𝟙_`; every invertible sheaf, in particular every `O_X(E)`), the
projection formula

  `f_*N ⊗ L' ≅ f_*(N ⊗ f^*L')`, natural in `N : Y.Modules`,

is the **mate** of the accepted pullback–tensor comparison `f^*(M ⊗ L) ≅ f^*M ⊗ f^*L`
(`schemeModulePullbackTensorIso`, natural in `M`): the functors `(− ⊗ L) ⋙ f^*` and
`f^* ⋙ (− ⊗ f^*L)` are isomorphic, and they are left adjoint to `f_* ⋙ (− ⊗ L')` and to
`(− ⊗ f^*L') ⋙ f_*` respectively (`tensorRightEquivalence` on `X` and on `Y`, composed with the
accepted `schemeModulePullbackPushforwardAdjunction`), so the right adjoints are isomorphic
(`Adjunction.rightAdjointUniq`). In particular `f_*O_Y ⊗ L ≅ f_*(f^*L)`.

No closed-immersion hypothesis is needed; the statement is used for closed immersions in
`KltDP.Geometry.CartierEulerPairingTwisted`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance projectionFormulaMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The chosen tensor unit of `X.Modules` is the structure module (accepted sheafification
counit). -/
def schemeTensorUnitIso (X : Scheme.{u}) :
    𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond

/-- `O_X ⊗ M ≅ M` through the tensor unit comparison and the left unitor. -/
def schemeUnitTensorLeftIso (X : Scheme.{u}) (M : X.Modules) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⊗ M ≅ M :=
  (tensorRight M).mapIso (schemeTensorUnitIso X).symm ≪≫ λ_ M

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback commutes with right tensoring by a fixed module: the accepted comparison
`f^*(M ⊗ L) ≅ f^*M ⊗ f^*L` as a natural isomorphism in `M`. -/
def pullbackTensorRightNatIso (L : X.Modules) :
    tensorRight L ⋙ schemeModulePullback f ≅
      schemeModulePullback f ⋙ tensorRight ((schemeModulePullback f).obj L) :=
  NatIso.ofComponents (fun M => schemeModulePullbackTensorIso f M L) (fun {M N} g => by
    have h := schemeModulePullbackTensorIso_natural f g (𝟙 L)
    rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
    show (schemeModulePullback f).map (g ▷ L) ≫ (schemeModulePullbackTensorIso f N L).hom =
      (schemeModulePullbackTensorIso f M L).hom ≫
        ((schemeModulePullback f).map g ▷ (schemeModulePullback f).obj L)
    exact h)

variable (L L' : X.Modules) (e : L ⊗ L' ≅ 𝟙_ X.Modules) (e' : L' ⊗ L ≅ 𝟙_ X.Modules)

/-- The pulled-back inverse pair: `f^*L ⊗ f^*L' ≅ 𝟙_`. -/
def pullbackInverseIso :
    (schemeModulePullback f).obj L ⊗ (schemeModulePullback f).obj L' ≅ 𝟙_ Y.Modules :=
  (schemeModulePullbackTensorIso f L L').symm ≪≫
    (schemeModulePullback f).mapIso (e ≪≫ schemeTensorUnitIso X) ≪≫
    schemeModulePullbackUnitIso f ≪≫ (schemeTensorUnitIso Y).symm

/-- The pulled-back inverse pair, other side: `f^*L' ⊗ f^*L ≅ 𝟙_`. -/
def pullbackInverseIso' :
    (schemeModulePullback f).obj L' ⊗ (schemeModulePullback f).obj L ≅ 𝟙_ Y.Modules :=
  (schemeModulePullbackTensorIso f L' L).symm ≪≫
    (schemeModulePullback f).mapIso (e' ≪≫ schemeTensorUnitIso X) ≪≫
    schemeModulePullbackUnitIso f ≪≫ (schemeTensorUnitIso Y).symm

/-- **The projection formula** as a natural isomorphism `f_*(−) ⊗ L' ≅ f_*(− ⊗ f^*L')`: the mate
of the pullback–tensor comparison. -/
def projectionFormulaNatIso :
    schemeModulePushforward f ⋙ tensorRight L' ≅
      tensorRight ((schemeModulePullback f).obj L') ⋙ schemeModulePushforward f :=
  Adjunction.rightAdjointUniq
    (((KltDP.Monoidal.tensorRightAdjunction L L' e e').comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoLeft (pullbackTensorRightNatIso f L))
    ((schemeModulePullbackPushforwardAdjunction f).comp
      (KltDP.Monoidal.tensorRightAdjunction _ _ (pullbackInverseIso f L L' e)
        (pullbackInverseIso' f L L' e')))

/-- The projection formula on an object: `f_*N ⊗ L' ≅ f_*(N ⊗ f^*L')`. -/
def projectionFormulaIso (N : Y.Modules) :
    (schemeModulePushforward f).obj N ⊗ L' ≅
      (schemeModulePushforward f).obj (N ⊗ (schemeModulePullback f).obj L') :=
  (projectionFormulaNatIso f L L' e e').app N

/-- **`f_*O_Y ⊗ L ≅ f_*(f^*L)`** for a module `L` with tensor inverse `L'`. -/
def pushforwardUnitTensorIso :
    (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ⊗ L ≅
      (schemeModulePushforward f).obj ((schemeModulePullback f).obj L) :=
  projectionFormulaIso f L' L e' e (_root_.SheafOfModules.unit Y.ringCatSheaf) ≪≫
    (schemeModulePushforward f).mapIso
      (schemeUnitTensorLeftIso Y ((schemeModulePullback f).obj L))

/-- The projection formula for an invertible sheaf `L`: `f_*N ⊗ L ≅ f_*(N ⊗ f^*L)`. -/
theorem InvertibleSheaf.exists_projectionFormulaIso (L : InvertibleSheaf X) (N : Y.Modules) :
    Nonempty ((schemeModulePushforward f).obj N ⊗ L.obj ≅
      (schemeModulePushforward f).obj (N ⊗ (schemeModulePullback f).obj L.obj)) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact ⟨projectionFormulaIso f L' L.obj e' e N⟩

/-- **`f_*O_Y ⊗ L ≅ f_*(f^*L)`** for an invertible sheaf `L`. -/
theorem InvertibleSheaf.exists_pushforwardUnitTensorIso (L : InvertibleSheaf X) :
    Nonempty ((schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ⊗
        L.obj ≅ (schemeModulePushforward f).obj ((schemeModulePullback f).obj L.obj)) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := L.exists_tensorInverse
  exact ⟨pushforwardUnitTensorIso f L.obj L' e e'⟩

end KltDP.Geometry
