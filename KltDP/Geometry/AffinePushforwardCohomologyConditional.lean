import KltDP.Geometry.SchemeAbelianSheafPushforward
import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Compatibility.InvertibleQuasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Original scalar actions in the full affine cohomology comparison

The entire arbitrary-scheme, affine-morphism, quasicoherent-coefficient,
all-degree natural comparison is an explicit hypothesis. No source axiom
or opaque source predicate is introduced. Naturality at the original
coefficient multiplication maps proves compatibility with original global
scalars and every original commutative base ring. The resulting Euler
comparison uses the same native cohomology objects and scalar actions.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (hAffine : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsAffineHom f] (n : ℕ),
    ∃ e : ∀ (M : X.Modules), M.IsQuasicoherent →
      H ((schemeModulePushforward f).obj M) n ≃+ H M n,
      ∀ (M N : X.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
        (φ : M ⟶ N) (x : H ((schemeModulePushforward f).obj M) n),
        e N hN ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
          (zariskiFunctor X n).map φ (e M hM x))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- The additive comparison from the full source family, on the same
original quasicoherent coefficient and in the same cohomological degree. -/
def affinePushforwardHAddEquiv (M : X.Modules) (hM : M.IsQuasicoherent) (n : ℕ) :
    H ((schemeModulePushforward f).obj M) n ≃+ H M n :=
  (hAffine X Y f n).choose M hM

include hAffine

/-- Every original quasicoherent coefficient morphism commutes with the
chosen member of the source's natural comparison family. -/
theorem affinePushforwardHAddEquiv_naturality
    {M N : X.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (φ : M ⟶ N) (n : ℕ) (x : H ((schemeModulePushforward f).obj M) n) :
    affinePushforwardHAddEquiv hAffine f N hN n
        ((zariskiFunctor Y n).map ((schemeModulePushforward f).map φ) x) =
      (zariskiFunctor X n).map φ (affinePushforwardHAddEquiv hAffine f M hM n x) :=
  (hAffine X Y f n).choose_spec M N hM hN φ x

/-- The action of each original target global function is transported by
the original map on global functions, not by an unrelated scalar choice. -/
theorem affinePushforwardHAddEquiv_smul (M : X.Modules) (hM : M.IsQuasicoherent)
    (n : ℕ) (r : Γ(Y, ⊤)) (x : H ((schemeModulePushforward f).obj M) n) :
    letI := globalSectionsCohomologyModule ((schemeModulePushforward f).obj M) n
    letI := globalSectionsCohomologyModule M n
    affinePushforwardHAddEquiv hAffine f M hM n (r • x) =
      f.appTop r • affinePushforwardHAddEquiv hAffine f M hM n x := by
  letI := globalSectionsCohomologyModule ((schemeModulePushforward f).obj M) n
  letI := globalSectionsCohomologyModule M n
  change affinePushforwardHAddEquiv hAffine f M hM n
      ((zariskiFunctor Y n).map
        (globalSmulHom ((schemeModulePushforward f).obj M) r) x) =
    (zariskiFunctor X n).map (globalSmulHom M (f.appTop r))
      (affinePushforwardHAddEquiv hAffine f M hM n x)
  rw [globalSmulHom_pushforward]
  exact affinePushforwardHAddEquiv_naturality hAffine f hM hM
    (globalSmulHom M (f.appTop r)) n x

variable {A : Type u} [CommRing A]

/-- The same comparison is linear over every original commutative base
ring. The source action is induced by the literal composite `f ≫ g`. -/
def affinePushforwardHBaseRingLinearEquiv
    (g : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (hM : M.IsQuasicoherent) (n : ℕ) :
    letI := baseRingModule g ((schemeModulePushforward f).obj M) n
    letI := baseRingModule (f ≫ g) M n
    H ((schemeModulePushforward f).obj M) n ≃ₗ[A] H M n := by
  letI := baseRingModule g ((schemeModulePushforward f).obj M) n
  letI := baseRingModule (f ≫ g) M n
  refine { affinePushforwardHAddEquiv hAffine f M hM n with map_smul' := ?_ }
  intro a x
  change affinePushforwardHAddEquiv hAffine f M hM n
      ((zariskiFunctor Y n).map
        (globalSmulHom ((schemeModulePushforward f).obj M)
          (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) x) =
    (zariskiFunctor X n).map
      (globalSmulHom M ((f ≫ g).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
      (affinePushforwardHAddEquiv hAffine f M hM n x)
  rw [globalSmulHom_pushforward]
  simpa only [appTop_baseRingScalar] using
    affinePushforwardHAddEquiv_naturality hAffine f hM hM
      (globalSmulHom M (f.appTop
        (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) n x

/-- The base-linear map retains the underlying source-family map. -/
theorem affinePushforwardHBaseRingLinearEquiv_apply
    (g : Y ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (hM : M.IsQuasicoherent)
    (n : ℕ) (x : H ((schemeModulePushforward f).obj M) n) :
    letI := baseRingModule g ((schemeModulePushforward f).obj M) n
    letI := baseRingModule (f ≫ g) M n
    affinePushforwardHBaseRingLinearEquiv hAffine f g M hM n x =
      affinePushforwardHAddEquiv hAffine f M hM n x := rfl

section Field

variable {k : Type u} [Field k] (g : Y ⟶ Spec (CommRingCat.of k))

/-- Equality of dimensions for the original base-field cohomology in every degree. -/
theorem cohomologyDimension_affinePushforward (M : X.Modules)
    (hM : M.IsQuasicoherent) (n : ℕ) :
    cohomologyDimension g ((schemeModulePushforward f).obj M) n =
      cohomologyDimension (f ≫ g) M n := by
  letI := baseRingModule g ((schemeModulePushforward f).obj M) n
  letI := baseRingModule (f ≫ g) M n
  exact (affinePushforwardHBaseRingLinearEquiv hAffine f g M hM n).finrank_eq

/-- The original affine pushforward preserves the native Euler value.
No finiteness, properness, separatedness, or dimension restriction is added. -/
theorem eulerCharacteristic_affinePushforward (M : X.Modules) (hM : M.IsQuasicoherent) :
    eulerCharacteristic g ((schemeModulePushforward f).obj M) =
      eulerCharacteristic (f ≫ g) M := by
  unfold eulerCharacteristic
  simp only [cohomologyDimension_affinePushforward hAffine f g M hM]

/-- The requested source-to-target orientation on the actual structure sheaf. -/
theorem eulerCharacteristic_structureSheaf_affine :
    eulerCharacteristic (f ≫ g) (_root_.SheafOfModules.unit X.ringCatSheaf) =
      eulerCharacteristic g
        ((schemeModulePushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) := by
  exact (eulerCharacteristic_affinePushforward hAffine f g
    (_root_.SheafOfModules.unit X.ringCatSheaf) inferInstance).symm

end Field

end KltDP.Geometry.ModuleCohomology

#check @KltDP.Geometry.ModuleCohomology.affinePushforwardHBaseRingLinearEquiv
#check @KltDP.Geometry.ModuleCohomology.eulerCharacteristic_structureSheaf_affine
#print axioms KltDP.Geometry.ModuleCohomology.affinePushforwardHBaseRingLinearEquiv
#print axioms KltDP.Geometry.ModuleCohomology.eulerCharacteristic_affinePushforward
#print axioms KltDP.Geometry.ModuleCohomology.eulerCharacteristic_structureSheaf_affine
