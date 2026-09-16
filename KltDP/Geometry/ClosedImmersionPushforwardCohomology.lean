import KltDP.Compatibility.ExactFunctorRightDerived
import KltDP.Compatibility.ClosedEmbeddingPushforwardExact
import KltDP.Compatibility.NatIsoRightDerived
import KltDP.Compatibility.SheafExtRightDerived
import KltDP.Geometry.SchemeAbelianSheafPushforward
import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.CoherentModule
import KltDP.AdmissionProbe.ProperCohomologyConsumers

/-!
# Cohomology of the pushforward along a closed immersion, in every degree

For a closed immersion of schemes `i : Z ⟶ X` and any module `M` on `Z`,

    H^n(X, i_*M) ≅ H^n(Z, M)      for every `n`

(`closedImmersionPushforwardHAddEquiv`), naturally in `M` and compatibly with the global-scalar
actions (`i.appTop`), hence linearly over any base ring `A` with `g : X ⟶ Spec A`
(`closedImmersionPushforwardHBaseRingLinearEquiv`, scalars on `Z` through `i ≫ g`).

Route: `i.base` is a closed embedding (`IsClosedImmersion.base_closed`), so the pushforward of
abelian sheaves `i_*` is exact and preserves injectives (`ClosedEmbeddingPushforwardExact.lean`);
therefore it transports injective resolutions and `Functor.exactRightDerivedIso` identifies
`i_* ⋙ RⁿΓ_X` with `Rⁿ(i_* ⋙ Γ_X)`, which is `RⁿΓ_Z` by the accepted global-sections comparison
`schemeAbelianPushforwardGlobalSectionsIso` and `NatIso.rightDerived`; the accepted
`sheafHRightDerivedIso` converts to the Ext-based `Sheaf.functorH` on both sides. This is the
same chain as the accepted `SchemeIsoCohomology.lean`, with the equivalence replaced by the exact
functor `i_*`. (The accepted tree had the comparison only in degree zero,
`pushforwardHZeroBaseRingLinearEquiv`.)

Consequences over a field `k`: `cohomologyDimension g (i_*M) n = cohomologyDimension (i ≫ g) M n`,
`eulerCharacteristic g (i_*M) = eulerCharacteristic (i ≫ g) M` (**`χ_X(i_*M) = χ_Z(M)`**, no
finiteness needed), vanishing and finite-dimensionality transport, and finiteness of every
`H^n(X, i_*M)` for `M` coherent on `Z` with `i ≫ g` proper (accepted 02O6 consumer on `Z`).

Not proved here: coherence of `i_*M` on `X` (Stacks 01BV literal) for coherent `M`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open KltDP.SheafCochainComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual abelian-sheaf cohomology functors agree under pushforward along a closed
immersion: `i_* ⋙ H^n(X, -) ≅ H^n(Z, -)`. -/
def closedImmersionAbelianSheafCohomologyIso (n : ℕ) :
    schemeAbelianSheafPushforward i ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) n ≅
      Sheaf.functorH (Opens.grothendieckTopology Z) n := by
  letI : HasInjectiveResolutions
      (TopCat.Sheaf AddCommGrp.{u} (Z : TopCat.{u})) :=
    inferInstanceAs (HasInjectiveResolutions
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (Z : TopCat.{u})) AddCommGrp.{u}))
  letI : HasInjectiveResolutions
      (TopCat.Sheaf AddCommGrp.{u} (X : TopCat.{u})) :=
    inferInstanceAs (HasInjectiveResolutions
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (X : TopCat.{u})) AddCommGrp.{u}))
  letI : Functor.Additive
      (C := TopCat.Sheaf AddCommGrp.{u} (Z : TopCat.{u})) (D := AddCommGrp.{u})
      (globalSectionsFunctor (Z : TopCat.{u})) :=
    globalSectionsFunctor_additive (Z : TopCat.{u})
  letI : Functor.Additive
      (C := TopCat.Sheaf AddCommGrp.{u} (X : TopCat.{u})) (D := AddCommGrp.{u})
      (globalSectionsFunctor (X : TopCat.{u})) :=
    globalSectionsFunctor_additive (X : TopCat.{u})
  letI : (schemeAbelianSheafPushforward i).Additive :=
    schemeAbelianSheafPushforward_additive i
  letI : (schemeAbelianSheafPushforward i ⋙
      globalSectionsFunctor (X : TopCat.{u})).Additive := by
    infer_instance
  letI : (schemeAbelianSheafPushforward i).PreservesHomology :=
    KltDP.ClosedEmbeddingPushforward.pushforward_preservesHomology i.base i.isClosedEmbedding
  letI : (schemeAbelianSheafPushforward i).PreservesInjectiveObjects :=
    KltDP.ClosedEmbeddingPushforward.pushforward_preservesInjectiveObjects i.base
  exact isoWhiskerLeft (schemeAbelianSheafPushforward i)
      (sheafHRightDerivedIso (X : TopCat.{u}) n) ≪≫
    Functor.exactRightDerivedIso (schemeAbelianSheafPushforward i)
      (globalSectionsFunctor (X : TopCat.{u})) n ≪≫
    NatIso.rightDerived (schemeAbelianPushforwardGlobalSectionsIso i) n ≪≫
    (sheafHRightDerivedIso (Z : TopCat.{u}) n).symm

namespace ModuleCohomology

/-- The module pushforward along a closed immersion and the cohomology functors:
`i_* ⋙ H^n(X, -) ≅ H^n(Z, -)`. -/
def closedImmersionPushforwardCohomologyIso (n : ℕ) :
    schemeModulePushforward i ⋙ zariskiFunctor X n ≅ zariskiFunctor Z n :=
  (Functor.associator (schemeModulePushforward i)
    (_root_.SheafOfModules.toSheaf X.ringCatSheaf)
    (Sheaf.functorH (Opens.grothendieckTopology X) n)).symm ≪≫
  isoWhiskerRight (schemeModulePushforwardToSheafIso i)
    (Sheaf.functorH (Opens.grothendieckTopology X) n) ≪≫
  Functor.associator (_root_.SheafOfModules.toSheaf Z.ringCatSheaf)
    (schemeAbelianSheafPushforward i)
    (Sheaf.functorH (Opens.grothendieckTopology X) n) ≪≫
  isoWhiskerLeft (_root_.SheafOfModules.toSheaf Z.ringCatSheaf)
    (closedImmersionAbelianSheafCohomologyIso i n)

/-- **`H^n(X, i_*M) ≃+ H^n(Z, M)`** for a closed immersion `i` and every module `M` on `Z`. -/
def closedImmersionPushforwardHAddEquiv (M : Z.Modules) (n : ℕ) :
    H ((schemeModulePushforward i).obj M) n ≃+ H M n :=
  ((closedImmersionPushforwardCohomologyIso i n).app M).addCommGroupIsoToAddEquiv

set_option maxRecDepth 4096 in
/-- The equivalence commutes with every coefficient morphism. -/
theorem closedImmersionPushforwardHAddEquiv_naturality
    {M N : Z.Modules} (f : M ⟶ N) (n : ℕ)
    (x : H ((schemeModulePushforward i).obj M) n) :
    closedImmersionPushforwardHAddEquiv i N n
        ((zariskiFunctor X n).map ((schemeModulePushforward i).map f) x) =
      (zariskiFunctor Z n).map f (closedImmersionPushforwardHAddEquiv i M n x) :=
  ConcreteCategory.congr_hom ((closedImmersionPushforwardCohomologyIso i n).hom.naturality f) x

set_option maxRecDepth 4096 in
/-- Global scalars act through the pullback of the original function along `i`. -/
theorem closedImmersionPushforwardHAddEquiv_smul (M : Z.Modules) (n : ℕ)
    (r : Γ(X, ⊤)) (x : H ((schemeModulePushforward i).obj M) n) :
    letI := globalSectionsCohomologyModule ((schemeModulePushforward i).obj M) n
    letI := globalSectionsCohomologyModule M n
    closedImmersionPushforwardHAddEquiv i M n (r • x) =
      i.appTop r • closedImmersionPushforwardHAddEquiv i M n x := by
  letI := globalSectionsCohomologyModule ((schemeModulePushforward i).obj M) n
  letI := globalSectionsCohomologyModule M n
  change closedImmersionPushforwardHAddEquiv i M n
      ((zariskiFunctor X n).map
        (globalSmulHom ((schemeModulePushforward i).obj M) r) x) =
    (zariskiFunctor Z n).map (globalSmulHom M (i.appTop r))
      (closedImmersionPushforwardHAddEquiv i M n x)
  rw [globalSmulHom_pushforward]
  exact closedImmersionPushforwardHAddEquiv_naturality i (globalSmulHom M (i.appTop r)) n x

variable {A : Type u} [CommRing A]

set_option maxRecDepth 4096 in
/-- **`H^n(X, i_*M) ≃ₗ[A] H^n(Z, M)`** over a base ring `A`, scalars on `Z` through `i ≫ g`. -/
def closedImmersionPushforwardHBaseRingLinearEquiv
    (g : X ⟶ Spec (CommRingCat.of A)) (M : Z.Modules) (n : ℕ) :
    letI := baseRingModule g ((schemeModulePushforward i).obj M) n
    letI := baseRingModule (i ≫ g) M n
    H ((schemeModulePushforward i).obj M) n ≃ₗ[A] H M n := by
  letI := baseRingModule g ((schemeModulePushforward i).obj M) n
  letI := baseRingModule (i ≫ g) M n
  refine { closedImmersionPushforwardHAddEquiv i M n with map_smul' := ?_ }
  intro a x
  change closedImmersionPushforwardHAddEquiv i M n
      ((zariskiFunctor X n).map
        (globalSmulHom ((schemeModulePushforward i).obj M)
          (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) x) =
    (zariskiFunctor Z n).map
      (globalSmulHom M ((i ≫ g).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
      (closedImmersionPushforwardHAddEquiv i M n x)
  rw [globalSmulHom_pushforward]
  simpa only [appTop_baseRingScalar] using
    closedImmersionPushforwardHAddEquiv_naturality i
      (globalSmulHom M (i.appTop
        (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) n x

/-- The linear comparison has the same underlying map as the natural cohomology comparison. -/
theorem closedImmersionPushforwardHBaseRingLinearEquiv_apply
    (g : X ⟶ Spec (CommRingCat.of A)) (M : Z.Modules) (n : ℕ)
    (x : H ((schemeModulePushforward i).obj M) n) :
    letI := baseRingModule g ((schemeModulePushforward i).obj M) n
    letI := baseRingModule (i ≫ g) M n
    closedImmersionPushforwardHBaseRingLinearEquiv i g M n x =
      closedImmersionPushforwardHAddEquiv i M n x := rfl

section Field

variable {k : Type u} [Field k] (g : X ⟶ Spec (CommRingCat.of k))

/-- `dim_k H^n(X, i_*M) = dim_k H^n(Z, M)` in every degree. -/
theorem cohomologyDimension_closedImmersionPushforward (M : Z.Modules) (n : ℕ) :
    cohomologyDimension g ((schemeModulePushforward i).obj M) n =
      cohomologyDimension (i ≫ g) M n := by
  letI := baseRingModule g ((schemeModulePushforward i).obj M) n
  letI := baseRingModule (i ≫ g) M n
  exact (closedImmersionPushforwardHBaseRingLinearEquiv i g M n).finrank_eq

/-- **`χ_X(i_*M) = χ_Z(M)`** for every module `M` on the closed subscheme `Z`. -/
theorem eulerCharacteristic_closedImmersionPushforward (M : Z.Modules) :
    eulerCharacteristic g ((schemeModulePushforward i).obj M) =
      eulerCharacteristic (i ≫ g) M := by
  unfold eulerCharacteristic
  simp only [cohomologyDimension_closedImmersionPushforward]

/-- Vanishing transports from `Z` to `X`. -/
theorem closedImmersionPushforward_H_subsingleton (M : Z.Modules) (n : ℕ)
    [Subsingleton (H M n)] :
    Subsingleton (H ((schemeModulePushforward i).obj M) n) :=
  (closedImmersionPushforwardHAddEquiv i M n).toEquiv.subsingleton_congr.mpr inferInstance

/-- Finite-dimensionality transports from `Z` to `X`. -/
theorem closedImmersionPushforward_finiteDimensional (M : Z.Modules) (n : ℕ)
    [FiniteDimensional k ((baseFunctor (i ≫ g) n).obj M)] :
    FiniteDimensional k ((baseFunctor g n).obj ((schemeModulePushforward i).obj M)) := by
  letI := baseRingModule g ((schemeModulePushforward i).obj M) n
  letI := baseRingModule (i ≫ g) M n
  have hfin : FiniteDimensional k (H M n) :=
    ‹FiniteDimensional k ((baseFunctor (i ≫ g) n).obj M)›
  exact (closedImmersionPushforwardHBaseRingLinearEquiv i g M n).symm.finiteDimensional

/-- Every `H^n(X, i_*M)` is finite dimensional for `M` coherent on `Z` and `Z` proper over `k`
(accepted 02O6 consumer on `Z`). -/
theorem closedImmersionPushforward_baseFunctor_finiteDimensional (M : Z.Modules)
    [IsCoherentModule M] [IsProper (i ≫ g)] (n : ℕ) :
    FiniteDimensional k ((baseFunctor g n).obj ((schemeModulePushforward i).obj M)) := by
  haveI := KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
    (i ≫ g) M n
  exact closedImmersionPushforward_finiteDimensional i g M n

/-- The same with properness of `g` alone: closed immersions are proper and properness composes. -/
theorem closedImmersionPushforward_baseFunctor_finiteDimensional_of_isProper (M : Z.Modules)
    [IsCoherentModule M] [IsProper g] (n : ℕ) :
    FiniteDimensional k ((baseFunctor g n).obj ((schemeModulePushforward i).obj M)) := by
  haveI : IsProper (i ≫ g) := inferInstance
  exact closedImmersionPushforward_baseFunctor_finiteDimensional i g M n

end Field

end ModuleCohomology

end KltDP.Geometry
