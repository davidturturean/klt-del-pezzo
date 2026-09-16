/-
Original project proof using the actual affine basis, original finite
generator maps and pinned free-section correspondence. Released under
Apache 2.0; see docs/reuse_sources/all_open_unit_kernel/sources/LICENSE.
-/
import KltDP.Compatibility.SheafIteratedOverKernel
import KltDP.Geometry.AffineOpenKernelFiniteType
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# All-open finite kernels for the original Noetherian structure sheaf

Every original finite-free-to-unit map on every open of a locally
Noetherian scheme has finite-type kernel. Affine subopens give the actual
cover, their actual kernel generators lift to the original restrictions,
and the existing finite-type locality theorem combines them.

The final statements use the original restricted structure module and
the pinned equivalence between free maps and families of actual compatible
sections. The section family can be empty and need not generate the unit.
No section ring of a nonaffine open is asserted Noetherian. This proves the
all-open kernel condition; no coherence predicate or literature axiom is
introduced here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

/-- All actual affine subopens of the given open, as objects of its
original Over site. -/
def affineSubopensOver (U : X.Opens) (V : {V : X.affineOpens // V.1 ≤ U}) : Over U :=
  Over.mk (homOfLE V.2)

/-- The original affine basis gives a covering in the actual Over topology. -/
theorem affineSubopensOver_coversTop (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).CoversTop (affineSubopensOver U) := by
  intro W
  change Sieve.overEquiv W (Sieve.ofObjects (affineSubopensOver U) W) ∈
    Opens.grothendieckTopology X W.left
  change ∀ x ∈ W.left, ∃ (T : X.Opens) (f : T ⟶ W.left),
    (Sieve.overEquiv W (Sieve.ofObjects (affineSubopensOver U) W)) f ∧ x ∈ T
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hx W.left.2
  let i : {V : X.affineOpens // V.1 ≤ U} := ⟨⟨V, hV⟩, hVW.trans W.hom.le⟩
  let a : affineSubopensOver U i ⟶ W :=
    Over.homMk (homOfLE hVW) (Subsingleton.elim _ _)
  refine ⟨V, homOfLE hVW, ?_, hxV⟩
  change ∃ (T : Over U) (g : T ⟶ W) (h : V ⟶ T.left),
    (Sieve.ofObjects (affineSubopensOver U) W) g ∧ homOfLE hVW = h ≫ g.left
  refine ⟨affineSubopensOver U i, a, 𝟙 _, ⟨i, ⟨𝟙 _⟩⟩, ?_⟩
  change homOfLE hVW = 𝟙 V ≫ homOfLE hVW
  exact Subsingleton.elim _ _

set_option maxHeartbeats 800000 in
/-- The finite-type kernel condition holds on every actual open, by
actual affine restriction and the original finite-generator locality. -/
theorem isFiniteType_kernel_free_to_unit_on_open
    [IsLocallyNoetherian X] (U : X.Opens) (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  haveI (i : {V : X.affineOpens // V.1 ≤ U}) :
      _root_.SheafOfModules.IsFiniteType ((kernel φ).over (affineSubopensOver U i)) := by
    let V := affineSubopensOver U i
    let ψ := _root_.SheafOfModules.overToSingleFreeToUnitMap X.ringCatSheaf V I φ
    obtain ⟨n, p, hp⟩ :=
      exists_finite_free_epi_kernel_on_affineOpen i.1.1 i.1.2 I ψ
    letI : Epi p := hp
    let q : _root_.SheafOfModules.free
        (R := (X.ringCatSheaf.over U).over V) (ULift.{u} (Fin n)) ⟶
        (kernel φ).over V :=
      _root_.SheafOfModules.liftIteratedKernelGenerators
        X.ringCatSheaf V I φ (A := ULift.{u} (Fin n)) p
    letI : Epi q :=
      _root_.SheafOfModules.liftIteratedKernelGenerators_epi
        X.ringCatSheaf V I φ (A := ULift.{u} (Fin n)) p
    letI : HasBinaryProducts (Over V) :=
      CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
        (C := Over U) (B := V)
    exact _root_.SheafOfModules.isFiniteType_of_free_epi
      (R := (X.ringCatSheaf.over U).over V) (M := (kernel φ).over V)
      (I := ULift.{u} (Fin n)) (p := q)
  exact _root_.SheafOfModules.IsFiniteType.of_coversTop (kernel φ)
    (affineSubopensOver U) (affineSubopensOver_coversTop U)

/-- The same statement with the literal original restricted structure
module as target. Its identification uses the actual `unitOverIso`. -/
theorem isFiniteType_kernel_free_to_restricted_unit
    [IsLocallyNoetherian X] (U : X.Opens) (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      (_root_.SheafOfModules.unit X.ringCatSheaf).over U) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  have h := isFiniteType_kernel_free_to_unit_on_open U I
    (φ ≫ (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) U).hom)
  simpa only [_root_.SheafOfModules.unitOverIso, Iso.refl_hom, Category.comp_id] using h

/-- Every finite family of original restricted structure-module sections
has finite-type kernel under the pinned free-map/section equivalence. -/
theorem isFiniteType_kernel_finite_sections_of_restricted_unit
    [IsLocallyNoetherian X] (U : X.Opens) (I : Type u) [Finite I]
    (s : I → ((_root_.SheafOfModules.unit X.ringCatSheaf).over U).sections) :
    _root_.SheafOfModules.IsFiniteType (kernel
      (((_root_.SheafOfModules.unit X.ringCatSheaf).over U).freeHomEquiv.symm s)) :=
  isFiniteType_kernel_free_to_restricted_unit U I
    (((_root_.SheafOfModules.unit X.ringCatSheaf).over U).freeHomEquiv.symm s)

/-- The exact original finite family of functions on `U`, transported
by its genuine restrictions, has finite-type kernel. -/
theorem isFiniteType_kernel_finite_functions
    [IsLocallyNoetherian X] (U : X.Opens) (I : Type u) [Finite I]
    (s : I → Γ(X, U)) :
    _root_.SheafOfModules.IsFiniteType (kernel
      (((_root_.SheafOfModules.unit X.ringCatSheaf).over U).freeHomEquiv.symm
        (fun i => (_root_.SheafOfModules.overSectionsEquiv X.ringCatSheaf
          (_root_.SheafOfModules.unit X.ringCatSheaf) U).symm (s i)))) :=
  isFiniteType_kernel_finite_sections_of_restricted_unit U I _

end KltDP.Geometry
