/-
Original project adapter for literal coherence and the pinned presentation
predicate. Released under Apache 2.0, retaining the original module sheaves,
free maps, kernel comparisons and Over-site covering data.

The actual cover refinement and presentation transport reuse accepted
SheafFiniteTypeLocality, SheafGeneratingSectionsMap and SheafIteratedOverKernel.
The corresponding official Mathlib presentation bind and the exact newer
sources inspected are recorded in COHERENT_QUASICOHERENT_REUSE.md.
-/
import KltDP.Geometry.CoherentModule
import KltDP.Compatibility.SheafIteratedOverKernel
import KltDP.Compatibility.SheafPresentationMap

/-!
# Literal coherent modules are finitely presented and quasicoherent

Finite local generators come from the original literal coherence predicate.
That same predicate supplies finite-type kernels of their actual finite-free
projections. Finite local kernel generators refine the original cover. The
proved iterated-Over equivalence and original kernel comparison then construct
finite presentations on the flattened original cover.

No Noetherianity, affine model, quasicoherence, finite presentation, localization
or section-extension hypothesis is supplied. This proves the forward implication
from the project's literal coherence predicate; it does not assert its converse
on an arbitrary scheme or construct a Serre-ample sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CoherentQuasicoherent

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- These are the explicit pinned sheafification instances already used by
-- FiniteLocallyFreeCoherent for the same original scheme Over sites.
local instance schemeOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance schemeOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

-- Keep the iterated-site dictionaries behind named proof constants. Their
-- construction is independent of the particular generator and kernel cover.
private theorem iteratedOverWeakSheafify (X : Scheme.{u}) (U : X.Opens) (V : Over U) :
    HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    (((Opens.grothendieckTopology X).over U).over V) AddCommGrp.{u}).isRightAdjoint

local instance iteratedOverWeakSheafifyFamily (X : Scheme.{u}) :
    ∀ (U : X.Opens) (V : Over U),
      HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrp.{u} :=
  iteratedOverWeakSheafify X

private theorem iteratedOverLocallyBijective (X : Scheme.{u}) (U : X.Opens) (V : Over U) :
    (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
      AddCommGrp.{u} := by
  let J := ((Opens.grothendieckTopology X).over U).over V
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over V)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over V)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

local instance iteratedOverLocallyBijectiveFamily (X : Scheme.{u}) :
    ∀ (U : X.Opens) (V : Over U),
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrp.{u} :=
  iteratedOverLocallyBijective X

section AbstractGenerators

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [HasWeakSheafify K AddCommGrp.{u}] [K.WEqualsLocallyBijective AddCommGrp.{u}]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

-- Check the actual mapped family and its epimorphism against an abstract
-- isomorphism. Its concrete kernel comparison is an argument to this proved
-- theorem, so completing the family does not unfold that comparison again.
private theorem exists_finite_generators_of_map_iso
    (F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : _root_.SheafOfModules.unit S ≅ F.obj (_root_.SheafOfModules.unit R))
    {N : _root_.SheafOfModules.{u} R} {P : _root_.SheafOfModules.{u} S}
    (T : N.GeneratingSections) (e : F.obj N ≅ P) (hT : Finite T.I) :
    ∃ G : P.GeneratingSections, Finite G.I := by
  refine ⟨(T.map F η).ofEpi e.hom, ?_⟩
  exact hT

-- Check the kernel/free comparison with abstract modules and functor.
-- Returning a proved existential hides its concrete composite when the
-- presentation transport later uses the actual scheme refinement.
private theorem exists_kernel_iso_of_mapped_generators
    (F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] [F.PreservesZeroMorphisms]
    [PreservesLimitsOfShape WalkingParallelPair F]
    [HasLimitsOfShape WalkingParallelPair (_root_.SheafOfModules.{u} S)]
    (η : _root_.SheafOfModules.unit S ≅ F.obj (_root_.SheafOfModules.unit R))
    {M : _root_.SheafOfModules.{u} R} {N : _root_.SheafOfModules.{u} S}
    (G : M.GeneratingSections) (e : F.obj M ≅ N) :
    Nonempty (F.obj (kernel G.π) ≅ kernel ((G.map F η).ofEpi e.hom).π) := by
  let G' : N.GeneratingSections := (G.map F η).ofEpi e.hom
  let eFree := _root_.SheafOfModules.mapFreeIso F G.I η
  letI : HasKernel (F.map G.π) := hasLimitOfHasLimitsOfShape (parallelPair (F.map G.π) 0)
  letI : HasKernel G'.π := hasLimitOfHasLimitsOfShape (parallelPair G'.π 0)
  refine ⟨PreservesKernel.iso F G.π ≪≫
    kernel.mapIso (F.map G.π) G'.π eFree.symm e ?_⟩
  simp only [G', _root_.SheafOfModules.GeneratingSections.ofEpi_π,
    _root_.SheafOfModules.GeneratingSections.map_π_eq, Iso.symm_hom,
    Category.assoc, eFree, Iso.inv_hom_id_assoc]

end AbstractGenerators

variable {X : Scheme.{u}} (M : X.Modules)

set_option maxHeartbeats 800000 in
/-- Restrict the actual generators and actual kernel generators, then
flatten the nested original Over site with its proved equivalence. -/
private theorem exists_finitePresentationOnRefinement (U : X.Opens)
    (G : (M.over U).GeneratingSections) (V : Over U)
    (T : ((kernel G.π).over V).GeneratingSections)
    (hG : Finite G.I) (hT : Finite T.I) :
    ∃ P : (M.over V.left).Presentation, Finite P.generators.I ∧ Finite P.relations.I := by
  let F := _root_.SheafOfModules.iteratedOverFunctor X.ringCatSheaf V
  let H := _root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf V
  letI : H.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI : H.IsRightAdjoint :=
    _root_.SheafOfModules.overToSingleFunctor_isRightAdjoint X.ringCatSheaf V
  letI : PreservesLimitsOfShape WalkingParallelPair H :=
    (Adjunction.ofIsRightAdjoint H).rightAdjoint_preservesLimits.preservesLimitsOfShape
  letI : HasLimitsOfShape WalkingParallelPair
      (_root_.SheafOfModules.{u} (X.ringCatSheaf.over V.left)) :=
    _root_.SheafOfModules.hasLimitsOfShape.{u}
      (R := X.ringCatSheaf.over V.left) (D := WalkingParallelPair)
  let η := _root_.SheafOfModules.overToSingleUnitIso X.ringCatSheaf V
  let eM := _root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M V
  let G' : (M.over V.left).GeneratingSections := (G.map H η).ofEpi eM.hom
  obtain ⟨eK⟩ := exists_kernel_iso_of_mapped_generators H η G eM
  obtain ⟨S, hS⟩ := exists_finite_generators_of_map_iso F
    (_root_.SheafOfModules.iteratedOverUnitIso X.ringCatSheaf V) T eK hT
  refine ⟨⟨G', S⟩, ?_, hS⟩
  change Finite G.I
  exact hG

set_option maxHeartbeats 800000 in
/-- Assemble the original finite generator cover and the finite-type kernels
of its actual projections. Keep the cover abstract while checking the nested
cover construction, before specializing it to the one supplied by coherence. -/
private theorem isFinitePresentation_of_finiteGeneratorsAndKernels
    (q : M.LocalGeneratorsData) (hq : ∀ i : q.I, Finite (q.generators i).I)
    (hK : ∀ i : q.I,
      _root_.SheafOfModules.IsFiniteType (kernel (q.generators i).π)) :
    M.IsFinitePresentation := by
  letI (i : q.I) : Finite (q.generators i).I := hq i
  letI (i : q.I) : _root_.SheafOfModules.IsFiniteType (kernel (q.generators i).π) :=
    hK i
  -- Instantiate the already proved families at the original cover.
  letI (i : q.I) : ∀ V : Over (q.X i),
      HasWeakSheafify (((Opens.grothendieckTopology X).over (q.X i)).over V)
        AddCommGrp.{u} := iteratedOverWeakSheafify X (q.X i)
  letI (i : q.I) : ∀ V : Over (q.X i),
      (((Opens.grothendieckTopology X).over (q.X i)).over V).WEqualsLocallyBijective
        AddCommGrp.{u} := iteratedOverLocallyBijective X (q.X i)
  have hD : ∀ i : q.I, ∃ D : (kernel (q.generators i).π).LocalGeneratorsData,
      ∀ j : D.I, Finite (D.generators j).I := fun i =>
    _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData
      (M := kernel (q.generators i).π)
  choose D hD using hD
  have hP : ∀ ij : (i : q.I) × (D i).I,
      ∃ P : (M.over ((D ij.1).X ij.2).left).Presentation,
        Finite P.generators.I ∧ Finite P.relations.I := fun ij =>
    exists_finitePresentationOnRefinement M (q.X ij.1) (q.generators ij.1)
      ((D ij.1).X ij.2) ((D ij.1).generators ij.2) (hq ij.1) (hD ij.1 ij.2)
  choose P hP using hP
  let σ : M.QuasicoherentData := {
    I := (i : q.I) × (D i).I
    X := fun ij => ((D ij.1).X ij.2).left
    coversTop := q.coversTop.over (fun i => (D i).coversTop)
    presentation := P }
  refine ⟨σ, ?_⟩
  intro ij
  exact hP ij

set_option maxHeartbeats 800000 in
/-- Literal coherence constructs actual finite presentations on an
actual refinement of the original cover, without Noetherianity. -/
theorem isFinitePresentation_of_isCoherentModule [IsCoherentModule M] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq⟩ :=
    (_root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M))
  exact isFinitePresentation_of_finiteGeneratorsAndKernels M q hq (fun i => by
    letI : Finite (q.generators i).I := hq i
    exact IsCoherentModule.kernel_finiteType M (q.X i) (q.generators i).I
      (q.generators i).π)

/-- Literal coherent original scheme-module sheaves satisfy the pinned
quasicoherent predicate. The actual finite presentations are derived. -/
theorem isQuasicoherent_of_isCoherentModule [IsCoherentModule M] :
    M.IsQuasicoherent := by
  letI : M.IsFinitePresentation := isFinitePresentation_of_isCoherentModule M
  exact ⟨⟨M.quasicoherentDataOfIsFinitePresentation⟩⟩

end KltDP.Geometry.CoherentQuasicoherent
