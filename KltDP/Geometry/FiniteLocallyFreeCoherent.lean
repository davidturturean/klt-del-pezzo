import KltDP.Geometry.CoherentModule
import KltDP.Compatibility.ConstantRankSheaf
import KltDP.Compatibility.InvertibleQuasicoherent

/-!
# Coherence from actual finite local bases

On an affine scheme the existing free-to-tilde kernel theorem already handles
arbitrary target modules. Its original finite generators give finite-free
kernel epimorphisms for free-to-free maps. The existing scheme and Over-site
equivalences transport these maps to each actual affine open.

For a module with finite local bases, affine subopens inside those same basis
charts cover every original open. Restricting the original map to these charts
and transporting the actual kernel generators proves the all-open finite-kernel
condition in `IsCoherentModule`. The basis ranks may vary between charts.
No coherence, cohomology or degree conclusion is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace AffineModuleTilde

/-- Expose the actual finite-free epimorphism used by the existing affine
kernel-finiteness proof, for an arbitrary original tilde target. -/
theorem exists_finite_free_epi_kernel_free_to_tilde
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Type u) [Finite I]
    (N : ModuleCat.{u} R)
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶ N.tilde) :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := (Spec (.of R)).ringCatSheaf) (ULift.{u} (Fin n)) ⟶ kernel φ),
      Epi p := by
  letI := finiteFreeModuleMap_kernel_finite R I N φ
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi R (kernel (finiteFreeModuleMap R I N φ))
  letI : Epi p := hp
  exact ⟨n, p ≫ (freeToTildeKernelIso R I N φ).hom, inferInstance⟩

/-- The original free target is the tilde of its original module coproduct.
Only the source basis must be finite for this kernel statement. -/
theorem exists_finite_free_epi_kernel_free_to_free
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I J : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.free J) :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := (Spec (.of R)).ringCatSheaf) (ULift.{u} (Fin n)) ⟶ kernel φ),
      Epi p := by
  let N : ModuleCat.{u} R := ∐ (fun _ : J => ModuleCat.of R R)
  obtain ⟨n, p, hp⟩ := exists_finite_free_epi_kernel_free_to_tilde R I N
    (φ ≫ (freeCoproductIso R J).inv)
  letI : Epi p := hp
  exact ⟨n, p ≫ (kernelCompMono φ (freeCoproductIso R J).inv).hom, inferInstance⟩

end AffineModuleTilde

/-- The existing Spec/open/Over equivalences transport an arbitrary original
free-to-free map and its actual finite kernel generators to an affine open. -/
theorem exists_finite_free_epi_kernel_free_to_free_on_affineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U)
    (I J : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      _root_.SheafOfModules.free J) :
    ∃ (n : ℕ)
      (p : _root_.SheafOfModules.free
        (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶ kernel φ),
      Epi p := by
  let R := Γ(X, U)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let e : Spec (.of R) ≅ U.toScheme := hU.isoSpec.symm
  let F := schemeModulePushforward e.hom ⋙ openToOverFunctor U
  letI : F.IsEquivalence := inferInstanceAs
    ((schemeModulePushforward e.hom ⋙ openToOverFunctor U).IsEquivalence)
  letI : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let a (A : Type u) : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) A ≅
      F.obj (_root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) A) :=
    openToOverFreeIso U A ≪≫ (openToOverFunctor U).mapIso (schemeIsoFreeIso e A)
  let ψ : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I ⟶
      _root_.SheafOfModules.free J :=
    F.preimage ((a I).inv ≫ φ ≫ (a J).hom)
  have hψ : F.map ψ = (a I).inv ≫ φ ≫ (a J).hom := F.map_preimage _
  let eK : F.obj (kernel ψ) ≅ kernel φ :=
    PreservesKernel.iso F ψ ≪≫
      kernel.mapIso (F.map ψ) φ (a I).symm (a J).symm (by
        simp only [Iso.symm_hom, hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  obtain ⟨n, p, hp⟩ :=
    AffineModuleTilde.exists_finite_free_epi_kernel_free_to_free R I J ψ
  letI : Epi p := hp
  exact ⟨n, (a (ULift.{u} (Fin n))).hom ≫ F.map p ≫ eK.hom, inferInstance⟩

-- Use the pinned concrete sheafification adjunction directly on each original
-- open site, so projection elaboration does not rediscover its right adjoint.
local instance schemeOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

-- The companion local-bijectivity instance uses the pinned concrete
-- sheafification comparison and its proved unit-map properties.
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

section LocalBases

variable {X : Scheme.{u}} (M : X.Modules)
  (q : _root_.SheafOfModules.LocalGeneratorsData M) (hq : q.IsLocallyFreeData)
  (hfinite : ∀ i : q.I, Finite (q.generators i).I)

include q hq hfinite

/-- The original finite local bases, with their actual empty relation families,
give the existing finite-presentation predicate. -/
theorem isFinitePresentation_of_finite_localBases : M.IsFinitePresentation := by
  refine ⟨KltDP.SheafOfModules.localBasisQuasicoherentData q hq, fun i => ⟨?_, ?_⟩⟩
  · change Finite (q.generators i).I
    exact hfinite i
  · change Finite (ULift.{u} Empty)
    infer_instance

set_option maxHeartbeats 800000 in
/-- Finite local bases on a locally Noetherian scheme prove the literal
all-open finite-kernel condition for the unchanged coefficient sheaf. -/
theorem isCoherentModule_of_finite_localBases [IsLocallyNoetherian X] :
    IsCoherentModule M := by
  letI : _root_.SheafOfModules.IsFiniteType M := ⟨q, hfinite⟩
  apply IsCoherentModule.of_kernel_finiteType M
  intro U I hI φ
  let A := (i : q.I) × {V : X.affineOpens // V.1 ≤ U ∧ V.1 ≤ q.X i}
  let V : A → Over U := fun a => Over.mk (homOfLE a.2.2.1)
  have hV : ((Opens.grothendieckTopology X).over U).CoversTop V := by
    intro W
    change Sieve.overEquiv W (Sieve.ofObjects V W) ∈ Opens.grothendieckTopology X W.left
    change ∀ x ∈ W.left, ∃ (T : X.Opens) (f : T ⟶ W.left),
      (Sieve.overEquiv W (Sieve.ofObjects V W)) f ∧ x ∈ T
    intro x hx
    obtain ⟨T, f, ⟨i, ⟨g⟩⟩, hxT⟩ := q.coversTop W.left x hx
    obtain ⟨_, ⟨P, hP, rfl⟩, hxP, hPT⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open hxT T.2
    let a : A := ⟨i, ⟨⟨P, hP⟩,
      ⟨(hPT.trans f.le).trans W.hom.le, hPT.trans g.le⟩⟩⟩
    let c : V a ⟶ W := Over.homMk (homOfLE (hPT.trans f.le)) (Subsingleton.elim _ _)
    refine ⟨P, homOfLE (hPT.trans f.le), ?_, hxP⟩
    change ∃ (B : Over U) (d : B ⟶ W) (e : P ⟶ B.left),
      (Sieve.ofObjects V W) d ∧ homOfLE (hPT.trans f.le) = e ≫ d.left
    exact ⟨V a, c, 𝟙 _, ⟨a, ⟨𝟙 _⟩⟩, Subsingleton.elim _ _⟩
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
    let W : Over (q.X a.1) := Over.mk (homOfLE a.2.2.2)
    let G := _root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf W
    letI := hq.isIso a.1
    let eChart : _root_.SheafOfModules.free
        (R := X.ringCatSheaf.over (V a).left) (q.generators a.1).I ≅ M.over (V a).left :=
      _root_.SheafOfModules.overToSingleFreeIso X.ringCatSheaf W (q.generators a.1).I ≪≫
        G.mapIso (asIso (q.generators a.1).π) ≪≫
        _root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M W
    let e₁ : H.obj (M.over U) ≅ _root_.SheafOfModules.free
        (R := X.ringCatSheaf.over (V a).left) (q.generators a.1).I :=
      _root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M (V a) ≪≫ eChart.symm
    let ψ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over (V a).left) I ⟶
        _root_.SheafOfModules.free (q.generators a.1).I :=
      e₀.hom ≫ H.map φ ≫ e₁.hom
    letI : HasKernel ψ := hasLimitOfHasLimitsOfShape (parallelPair ψ 0)
    letI : HasKernel (H.map φ) := hasLimitOfHasLimitsOfShape (parallelPair (H.map φ) 0)
    let eK : F.obj ((kernel φ).over (V a)) ≅ kernel ψ :=
      PreservesKernel.iso H φ ≪≫ kernel.mapIso (H.map φ) ψ e₀.symm e₁ (by
        simp only [ψ, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
    obtain ⟨n, p, hp⟩ := exists_finite_free_epi_kernel_free_to_free_on_affineOpen
      a.2.1.1 a.2.1.2 I (q.generators a.1).I ψ
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

end LocalBases

/-- In particular, the actual constant finite-rank predicate supplies
coherence of its original module on a locally Noetherian scheme. -/
theorem isCoherentModule_of_isLocallyFreeOfRank
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules) {n : ℕ}
    (h : KltDP.SheafOfModules.IsLocallyFreeOfRank M n) : IsCoherentModule M := by
  obtain ⟨q, hq⟩ :
      ∃ q : _root_.SheafOfModules.LocalGeneratorsData M,
        KltDP.SheafOfModules.LocalGeneratorsData.HasConstantRank q n :=
    h.exists_localGeneratorsData
  exact isCoherentModule_of_finite_localBases M q hq.isLocallyFreeData hq.basisFinite

end KltDP.Geometry
