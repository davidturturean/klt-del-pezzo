/-
Original project proof using the actual affine basis, original rank-one
trivializations and existing kernel/generator comparisons. Released under
Apache 2.0; see
docs/reuse_sources/literal_coherent_module/sources/mathlib/LICENSE.txt.
-/
import KltDP.Geometry.CoherentModule
import KltDP.Compatibility.InvertibleTensorUnit

/-!
# Literal coherence of actual invertible sheaves

On an arbitrary open, restrict the given finite-free map to actual affine
subopens inside the original rank-one charts. The original chart isomorphism
reduces the map to a finite-free-to-unit map on that affine open. Its actual
finite kernel generators lift back through the existing iterated-Over
equivalence. Finite-type locality then proves the original kernel finite
type. No chosen family is required to generate the coefficient sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

set_option maxHeartbeats 800000 in
/-- An actual rank-one atlas on a locally Noetherian scheme proves the
literal all-open finite-kernel condition, hence coherence of the sheaf. -/
theorem isCoherentModule_of_localTrivializations (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M) :
    IsCoherentModule M := by
  letI : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := t.isInvertible
  apply IsCoherentModule.of_kernel_finiteType M
  intro U I hI φ
  let A := (i : t.I) × {V : X.affineOpens // V.1 ≤ U ∧ V.1 ≤ t.X i}
  let V : A → Over U := fun a => Over.mk (homOfLE a.2.2.1)
  have hV : ((Opens.grothendieckTopology X).over U).CoversTop V := by
    intro W
    change Sieve.overEquiv W (Sieve.ofObjects V W) ∈
      Opens.grothendieckTopology X W.left
    change ∀ x ∈ W.left, ∃ (T : X.Opens) (f : T ⟶ W.left),
      (Sieve.overEquiv W (Sieve.ofObjects V W)) f ∧ x ∈ T
    intro x hx
    obtain ⟨T, f, ⟨i, ⟨g⟩⟩, hxT⟩ := t.coversTop W.left x hx
    obtain ⟨_, ⟨P, hP, rfl⟩, hxP, hPT⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open hxT T.2
    let a : A := ⟨i, ⟨⟨P, hP⟩,
      ⟨(hPT.trans f.le).trans W.hom.le, hPT.trans g.le⟩⟩⟩
    let c : V a ⟶ W :=
      Over.homMk (homOfLE (hPT.trans f.le)) (Subsingleton.elim _ _)
    refine ⟨P, homOfLE (hPT.trans f.le), ?_, hxP⟩
    change ∃ (B : Over U) (d : B ⟶ W) (e : P ⟶ B.left),
      (Sieve.ofObjects V W) d ∧ homOfLE (hPT.trans f.le) = e ≫ d.left
    refine ⟨V a, c, 𝟙 _, ⟨a, ⟨𝟙 _⟩⟩, ?_⟩
    exact Subsingleton.elim _ _
  haveI (a : A) : _root_.SheafOfModules.IsFiniteType ((kernel φ).over (V a)) := by
    let F := _root_.SheafOfModules.iteratedOverFunctor X.ringCatSheaf (V a)
    let H := _root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf (V a)
    letI : H.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    letI : H.IsRightAdjoint :=
      _root_.SheafOfModules.overToSingleFunctor_isRightAdjoint X.ringCatSheaf (V a)
    letI : PreservesLimitsOfShape WalkingParallelPair H :=
      (Adjunction.ofIsRightAdjoint H).rightAdjoint_preservesLimits.preservesLimitsOfShape
    letI : HasLimitsOfShape WalkingParallelPair
        (_root_.SheafOfModules.{u} (X.ringCatSheaf.over (V a).left)) :=
      _root_.SheafOfModules.hasLimitsOfShape.{u}
        (R := X.ringCatSheaf.over (V a).left) (D := WalkingParallelPair)
    let e₀ := _root_.SheafOfModules.overToSingleFreeIso X.ringCatSheaf (V a) I
    let e₁ : H.obj (M.over U) ≅
        _root_.SheafOfModules.unit (X.ringCatSheaf.over (V a).left) :=
      _root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M (V a) ≪≫
        t.unitIsoOver a.1 (homOfLE a.2.2.2)
    let ψ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over (V a).left) I ⟶
        _root_.SheafOfModules.unit (X.ringCatSheaf.over (V a).left) :=
      e₀.hom ≫ H.map φ ≫ e₁.hom
    letI : HasKernel ψ := hasLimitOfHasLimitsOfShape (parallelPair ψ 0)
    letI : HasKernel (H.map φ) := hasLimitOfHasLimitsOfShape (parallelPair (H.map φ) 0)
    let eK : F.obj ((kernel φ).over (V a)) ≅ kernel ψ :=
      PreservesKernel.iso H φ ≪≫
        kernel.mapIso (H.map φ) ψ e₀.symm e₁ (by
          simp only [ψ, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
    obtain ⟨n, p, hp⟩ := exists_finite_free_epi_kernel_on_affineOpen
      a.2.1.1 a.2.1.2 I ψ
    letI : Epi p := hp
    let eF := _root_.SheafOfModules.mapFreeIso F (ULift.{u} (Fin n))
      (_root_.SheafOfModules.iteratedOverUnitIso X.ringCatSheaf (V a))
    let p' : _root_.SheafOfModules.free
        (R := (X.ringCatSheaf.over U).over (V a)) (ULift.{u} (Fin n)) ⟶
        (kernel φ).over (V a) :=
      F.preimage (eF.inv ≫ p ≫ eK.inv)
    letI : Epi p' := by
      apply F.epi_of_epi_map
      change Epi (F.map (F.preimage (eF.inv ≫ p ≫ eK.inv)))
      rw [F.map_preimage]
      infer_instance
    letI : HasBinaryProducts (Over (V a)) :=
      CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
        (C := Over U) (B := V a)
    exact _root_.SheafOfModules.isFiniteType_of_free_epi
      (R := (X.ringCatSheaf.over U).over (V a))
      (M := (kernel φ).over (V a)) (I := ULift.{u} (Fin n)) (p := p')
  exact _root_.SheafOfModules.IsFiniteType.of_coversTop (kernel φ) V hV

/-- Actual invertible coefficients are coherent on a locally Noetherian
scheme, by their original rank-one local trivializations. -/
instance isCoherentModule_of_isInvertible (M : X.Modules)
    [KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M] :
    IsCoherentModule M :=
  isCoherentModule_of_localTrivializations M
    (KltDP.SheafOfModules.LocalTrivializations.ofIsInvertible
      (R := X.ringCatSheaf) M)

/-- The original underlying module of an actual invertible sheaf is coherent. -/
theorem InvertibleSheaf.isCoherent (L : InvertibleSheaf X) : IsCoherentModule L.obj :=
  inferInstance

end KltDP.Geometry
