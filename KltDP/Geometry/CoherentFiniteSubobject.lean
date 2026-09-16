/-
Original project adapters for the pinned local-generator and kernel APIs.
Released under Apache 2.0; see
docs/reuse_sources/literal_coherent_module/sources/mathlib/LICENSE.txt.
The finite-type quotient construction also follows the frozen Apache-licensed
AINTLIB SheafModuleFiniteTypeQuotient source recorded under
docs/reuse_sources/literal_coherent_module/sources/mazur/.
-/
import KltDP.Geometry.CoherentModule
import KltDP.Compatibility.SheafGeneratingSectionsMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Finite-type quotients and finite-type coherent subobjects

An actual epimorphism carries the original finite local generators to the
same cover with the same generator indices. The construction works on
small sites with binary products, including the original Over sites.

For an actual monomorphism into a coherent scheme-module sheaf, the kernel
of every original finite-free map agrees with the kernel of its composite
into the coherent target. Thus a finite-type subobject is coherent in the
literal all-open, finite-section-family sense already defined in the project.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M N : SheafOfModules.{u} R}

/-- Push the original local generators through the original restricted
epimorphism, retaining the actual cover and every generator index. -/
def LocalGeneratorsData.ofEpi (q : M.LocalGeneratorsData) (p : M ⟶ N) [Epi p] :
    N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators k := (q.generators k).ofEpi ((overFunctor R (q.X k)).map p)

/-- The quotient construction retains the literal local generator type. -/
@[simp]
theorem LocalGeneratorsData.ofEpi_generators_I (q : M.LocalGeneratorsData)
    (p : M ⟶ N) [Epi p] (k : q.I) :
    ((q.ofEpi p).generators k).I = (q.generators k).I := rfl

/-- Finite type descends along an actual sheaf epimorphism. No surjectivity
of the map on sections over an arbitrary open is assumed. -/
theorem isFiniteType_of_epi (p : M ⟶ N) [Epi p] [IsFiniteType M] :
    IsFiniteType N := by
  let q := M.localGeneratorsDataOfIsFiniteType
  refine ⟨q.ofEpi p, ?_⟩
  intro k
  change Finite (q.generators k).I
  dsimp only [q]
  infer_instance

end SheafOfModules

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A finite-type actual subobject of a coherent module sheaf is coherent.
The proof tests every finite family on every open, without an epimorphism
condition on its associated free map. -/
theorem IsCoherentModule.of_finiteType_mono (i : M ⟶ N) [Mono i]
    [_root_.SheafOfModules.IsFiniteType M] [IsCoherentModule N] :
    IsCoherentModule M := by
  apply IsCoherentModule.of_kernel_finiteType M
  intro U I hI φ
  let F := _root_.SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsRightAdjoint :=
    inferInstanceAs ((_root_.SheafOfModules.pushforward.{u} (F := Over.forget U)
      (J := (Opens.grothendieckTopology X).over U)
      (K := Opens.grothendieckTopology X)
      (𝟙 (X.ringCatSheaf.over U))).IsRightAdjoint)
  letI : Mono (F.map i) := inferInstance
  letI : _root_.SheafOfModules.IsFiniteType (kernel (φ ≫ F.map i)) :=
    IsCoherentModule.kernel_finiteType N U I (φ ≫ F.map i)
  letI : HasBinaryProducts (Over U) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  exact _root_.SheafOfModules.isFiniteType_of_epi
    (C := Over U) (J := (Opens.grothendieckTopology X).over U)
    (R := X.ringCatSheaf.over U)
    (M := kernel (φ ≫ F.map i)) (N := kernel φ)
    (kernelCompMono φ (F.map i)).hom

end KltDP.Geometry
