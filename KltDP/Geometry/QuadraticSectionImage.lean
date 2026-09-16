import KltDP.Geometry.QuadraticSectionEvaluationMorphism
import KltDP.Geometry.CoherentFiniteSubobject
import KltDP.Geometry.TensorInvertibleSheaf
import KltDP.Compatibility.SheafSubmodule
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The actual image ideal of the original section evaluation morphism

The image is the categorical kernel of the categorical cokernel of the
original evaluation morphism. Its ideals on opens are the actual component
ranges of this image inclusion. Preservation of kernels, rather than of
cokernels or images, identifies these ideals with the kernels of the actual
quotient-sheaf components. Consequently membership is local and the ideals
form a genuine subsheaf of O, isomorphic over O to the original image.

The original square-root data makes N and its actual sheaf dual invertible.
Finite type descends through the actual image epimorphism. On a locally
Noetherian base the actual image, and its identified ideal subsheaf, are
coherent by the finite-type subobject theorem for the original coherent O.

The literal branch principal ideal maps into this image ideal on every
original affine chart. Equality with that principal ideal still requires
an affine image/exactness comparison; it is not inferred from left exactness
of sections. No global Cartier identification or branch regularity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

universe u

namespace KltDP.Geometry

open KltDP.SheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

local instance sectionImageCommRing (W : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj W) :=
  inferInstanceAs (CommRing (X.presheaf.obj W))

local instance : ∀ W, IsMulCommutative (X.ringCatSheaf.val.obj W) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

variable (N : X.Modules) (b : N.val.obj (op (⊤ : X.Opens)))

/-- The actual abelian image of the original dual-evaluation morphism. -/
abbrev sectionImage : X.Modules := Abelian.image (sectionEvaluationMorphism X N b)

/-- Its actual categorical inclusion into the structure module. -/
abbrev sectionImageι : sectionImage X N b ⟶ _root_.SheafOfModules.unit X.ringCatSheaf :=
  Abelian.image.ι (sectionEvaluationMorphism X N b)

/-- The original evaluation morphism factors through this actual image. -/
@[reassoc]
theorem sectionImage_factorization :
    Abelian.factorThruImage (sectionEvaluationMorphism X N b) ≫
      sectionImageι X N b = sectionEvaluationMorphism X N b :=
  Abelian.image.fac _

/-- The ideals are actual images of sections of the categorical image sheaf. -/
def sectionImageIdeal (W : X.Opens) : Ideal Γ(X, W) :=
  LinearMap.range ((sectionImageι X N b).val.app (op W)).hom

/-- Kernel preservation computes these ideals from the original quotient
sheaf. No sectionwise cokernel formula is used. -/
theorem sectionImageIdeal_eq_ker (W : X.Opens) :
    sectionImageIdeal X N b W =
      LinearMap.ker ((cokernel.π (sectionEvaluationMorphism X N b)).val.app (op W)).hom := by
  let q := cokernel.π (sectionEvaluationMorphism X N b)
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let ev := _root_.SheafOfModules.evaluation X.ringCatSheaf (op W)
  letI : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have h : (S.map ev).Exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (kernelIsKernel q) ev)
  exact h.moduleCat_range_eq_ker

/-- The actual image ideals are stable under the original restrictions. -/
theorem sectionImageIdeal_restrict {V W : X.Opens} (i : V ⟶ W)
    (s : Γ(X, W)) (hs : s ∈ sectionImageIdeal X N b W) :
    X.presheaf.map i.op s ∈ sectionImageIdeal X N b V := by
  obtain ⟨t, rfl⟩ := hs
  refine ⟨(sectionImage X N b).val.map i.op t, ?_⟩
  exact _root_.PresheafOfModules.naturality_apply (sectionImageι X N b).val i.op t

/-- Membership in the original image ideal is local, by separatedness
of the actual quotient sheaf. -/
theorem sectionImageIdeal_of_locally_mem (W : X.Opens) (s : Γ(X, W))
    (hs : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ⟶ W),
      x ∈ V ∧ X.presheaf.map i.op s ∈ sectionImageIdeal X N b V) :
    s ∈ sectionImageIdeal X N b W := by
  rw [sectionImageIdeal_eq_ker]
  change (cokernel.π (sectionEvaluationMorphism X N b)).val.app (op W) s = 0
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (sectionEvaluationMorphism X N b))).cond
  intro x hx
  obtain ⟨V, i, hxV, hV⟩ := hs x hx
  refine ⟨V, i.le, hxV, ?_⟩
  rw [sectionImageIdeal_eq_ker] at hV
  change (cokernel.π (sectionEvaluationMorphism X N b)).val.app (op V)
    (X.presheaf.map i.op s) = 0 at hV
  change (cokernel (sectionEvaluationMorphism X N b)).val.map i.op
      ((cokernel.π (sectionEvaluationMorphism X N b)).val.app (op W) s) =
    (cokernel (sectionEvaluationMorphism X N b)).val.map i.op 0
  rw [map_zero, ← _root_.PresheafOfModules.naturality_apply]
  exact hV

/-- The original image ideals, with their proved restriction stability. -/
def sectionImagePresheafSubmodule :
    (_root_.SheafOfModules.unit X.ringCatSheaf).val.Submodule where
  obj W := sectionImageIdeal X N b W.unop
  map {V W} i := by
    intro s hs
    exact sectionImageIdeal_restrict X N b i.unop s hs

/-- The original image ideals form a genuine subsheaf of O. -/
def sectionImageSubmodule : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule where
  toSubmodule := sectionImagePresheafSubmodule X N b
  isSheaf := by
    intro W s hs
    apply sectionImageIdeal_of_locally_mem X N b W.unop s
    intro x hx
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    exact ⟨V, i, hxV, hi⟩

private theorem sectionImageι_app_injective (W : X.Opensᵒᵖ) :
    Function.Injective ((sectionImageι X N b).val.app W) := by
  apply (ModuleCat.mono_iff_injective _).mp
  change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf W).map
    (kernel.ι (cokernel.π (sectionEvaluationMorphism X N b))))
  infer_instance

/-- The concrete ideal subsheaf is isomorphic to the original categorical
image; its forward components are the original image inclusion with codomain restricted. -/
def sectionImageIsoSubmodule :
    sectionImage X N b ≅ (sectionImageSubmodule X N b).toSheafOfModules := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk (fun W =>
    (LinearEquiv.ofBijective ((sectionImageι X N b).val.app W).hom.rangeRestrict
      ⟨fun a c h => sectionImageι_app_injective X N b W (congrArg Subtype.val h),
        LinearMap.surjective_rangeRestrict _⟩).toModuleIso) ?_
  intro V W i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact _root_.PresheafOfModules.naturality_apply (sectionImageι X N b).val i s

/-- The ideal-sheaf comparison retains the original inclusion into O. -/
@[reassoc]
theorem sectionImageIsoSubmodule_hom_ι :
    (sectionImageIsoSubmodule X N b).hom ≫ (sectionImageSubmodule X N b).ι =
      sectionImageι X N b := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- The original component evaluation image lies in the genuine image ideal. -/
theorem sectionEvaluation_range_le_imageIdeal (W : X.Opens) :
    LinearMap.range ((sectionEvaluationMorphism X N b).val.app (op W)).hom ≤
      sectionImageIdeal X N b W := by
  rintro _ ⟨φ, rfl⟩
  refine ⟨(Abelian.factorThruImage (sectionEvaluationMorphism X N b)).val.app (op W) φ, ?_⟩
  exact congrArg (fun f : dual X.ringCatSheaf N ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf => f.val.app (op W) φ)
    (sectionImage_factorization X N b)

namespace InvertibleQuadraticAtlas

open TransitionUnitGluing TransitionUnitExtraction QuadraticCover

local instance imageMonoidal : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
local instance imageSymmetric : SymmetricCategory X.Modules := Scheme.Modules.symmetricCategory X

variable (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ N)

include L e

/-- The original square-root data derives the rank-one property of N. -/
theorem squareRoot_isInvertible : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) N := by
  let U := L.localTrivializations.X
  let g := invertibleSheafUnits X L
  letI := moduleSheaf_isInvertible X U (productUnits X U g g)
    (productUnits_isCocycle X U g g
      (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_isCocycle X L))
    (invertibleSheafUnits_cover X L)
  exact KltDP.SheafOfModules.IsInvertible.of_iso
    (R := X.ringCatSheaf) (M := moduleSheaf X U (productUnits X U g g)) (N := N)
    (e.symm ≪≫ squareCoordinatesIso X L).symm

/-- The actual dual is rank one by its proved tensor evaluation inverse,
with the original tensor/sheafification comparison. -/
theorem squareRoot_dual_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (dual X.ringCatSheaf N) := by
  letI := squareRoot_isInvertible X N L e
  let ε : SchemeTensorPairing.tensorSheafification (dual X.ringCatSheaf N) N ≅
      SchemeTensorPairing.unitSheaf X :=
    (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
      (dual X.ringCatSheaf N) N).symm ≪≫
      (β_ (dual X.ringCatSheaf N) N) ≪≫
        evaluationIso X.sheaf.val X.ringCatSheaf.cond N
  exact SchemeTensorPairing.isInvertible_of_tensorSheafification_iso_unit ε

/-- Finite type descends through the original image epimorphism. -/
theorem sectionImage_isFiniteType : _root_.SheafOfModules.IsFiniteType (sectionImage X N b) := by
  letI := squareRoot_dual_isInvertible X N L e
  exact _root_.SheafOfModules.isFiniteType_of_epi
    (R := X.ringCatSheaf) (M := dual X.ringCatSheaf N) (N := sectionImage X N b)
    (Abelian.factorThruImage (sectionEvaluationMorphism X N b))

/-- On a locally Noetherian base the actual image is coherent, with the
literal all-open finite-kernel definition used for the structure module. -/
theorem sectionImage_isCoherent [IsLocallyNoetherian X] :
    IsCoherentModule (sectionImage X N b) := by
  letI := sectionImage_isFiniteType X N b L e
  exact IsCoherentModule.of_finiteType_mono (sectionImageι X N b)

/-- The identified actual ideal subsheaf is itself coherent. -/
theorem sectionImageSubmodule_isCoherent [IsLocallyNoetherian X] :
    IsCoherentModule (sectionImageSubmodule X N b).toSheafOfModules := by
  letI := sectionImage_isFiniteType X N b L e
  letI := _root_.SheafOfModules.isFiniteType_of_epi
    (R := X.ringCatSheaf) (M := sectionImage X N b)
    (N := (sectionImageSubmodule X N b).toSheafOfModules)
    (sectionImageIsoSubmodule X N b).hom
  exact IsCoherentModule.of_finiteType_mono (sectionImageSubmodule X N b).ι

/-- Every original affine branch coefficient ideal lies in the actual
image ideal. The opposite inclusion is not inferred from kernel preservation. -/
theorem branchIdeal_le_sectionImageIdeal [X.IsSeparated]
    (i : AffineOpenRefinement.Index X L.localTrivializations.X) :
    branchIdeal ((fromSquareRoot X L N e b).sections i) ≤
      sectionImageIdeal X N b (AffineOpenRefinement.opens X L.localTrivializations.X i) := by
  rw [← sectionEvaluationMorphism_range_eq_branchIdeal X N b L e i]
  exact sectionEvaluation_range_le_imageIdeal X N b _

end InvertibleQuadraticAtlas

end KltDP.Geometry
