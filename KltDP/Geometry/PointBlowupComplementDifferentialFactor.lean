import KltDP.Geometry.PointBlowupTopDifferential

/-!
# The original differential factor on the unchanged complement

The original center-fiber kernel is framed by one on the actual center
complement. Its tensor inclusion is therefore invertible there. The same
original projection is an isomorphism on this complement, so its original
pulled exterior differential is invertible. Their composite gives the
normalized factor, with no smoothness or frame premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.PointBlowupTopDifferential

open PointBlowupGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance pointComplementModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem scalar_one (Y : Scheme.{u}) :
    schemeScalarEnd (Y := Y) 1 = 𝟙 (_root_.SheafOfModules.unit Y.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : Γ(Y, V.unop) := s
  change s' * Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op 1 = s'
  rw [(Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom.map_one, mul_one]

private theorem structureTensorInclusion_isIso {Y : Scheme.{u}} {I : Y.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf) [IsIso i] (M : Y.Modules) :
    IsIso (schemeStructureTensorInclusion i M) := by
  unfold schemeStructureTensorInclusion
  infer_instance

private theorem isomorphism_factor_comp {C : Type*} [Category C]
    {A B T : C} (a : A ⟶ T) (b : B ⟶ T) [IsIso a] [IsIso b] :
    (asIso a ≪≫ (asIso b).symm).hom ≫ b = a := by simp

variable {k R : Type u} [CommRing k] [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (n : ℕ)

/-- The actual complement frame makes the original pulled kernel inclusion invertible. -/
theorem complementKernelInclusion_isIso :
    IsIso (pulledKernelInclusion (globalCenterFiberι j q hclosed)
      (exceptionalComplementOpen j q hclosed).ι) := by
  haveI : IsIso ((globalCenterFiberComplementFrame j q hclosed).hom ≫
      pulledKernelInclusion (globalCenterFiberι j q hclosed)
        (exceptionalComplementOpen j q hclosed).ι) := by
    rw [globalCenterFiberComplementFrame_inclusion, scalar_one]
    infer_instance
  exact IsIso.of_isIso_comp_left (globalCenterFiberComplementFrame j q hclosed).hom _

/-- Its actual tensor inclusion is invertible on the same original open. -/
theorem complementInclusion_isIso :
    IsIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
      (exceptionalInclusion f j q hclosed n)) := by
  letI : IsIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
      (schemeKernelIdealι (globalCenterFiberι j q hclosed)) ≫
        (schemeModulePullbackUnitIso (exceptionalComplementOpen j q hclosed).ι).hom) :=
    complementKernelInclusion_isIso j q hclosed
  letI : IsIso (schemeStructureTensorInclusion
      ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
          (schemeKernelIdealι (globalCenterFiberι j q hclosed)) ≫
        (schemeModulePullbackUnitIso (exceptionalComplementOpen j q hclosed).ι).hom)
      ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).obj
        (topSheaf f j q hclosed n))) :=
    structureTensorInclusion_isIso _ _
  change IsIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
    (schemeStructureTensorInclusion (schemeKernelIdealι (globalCenterFiberι j q hclosed))
      (topSheaf f j q hclosed n)))
  rw [← schemeModulePullbackTensorIso_inclusion]
  infer_instance

/-- The original projection becomes the original puncture isomorphism here. -/
theorem complementMap_isIso :
    IsIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
      (blowdownMap f j q hclosed n)) := by
  letI : IsOpenImmersion ((exceptionalComplementOpen j q hclosed).ι ≫
      projection j q hclosed) := by
    have he : (exceptionalComplementOpen j q hclosed).ι ≫ projection j q hclosed =
        (punctureIso j q hclosed).hom ≫ (puncture j q hclosed).ι := by
      rw [punctureIso_hom, morphismRestrict_ι]
      rfl
    rw [he]
    infer_instance
  exact SchemeKaehlerExteriorPullbackTransport.pullback_map_isIso_of_open_comp
    f (projection j q hclosed) (projection j q hclosed ≫ f) rfl n
      (exceptionalComplementOpen j q hclosed).ι

/-- The same two original isomorphisms give the actual complementary factor. -/
def complementFactorIso :
    (schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).obj
        ((schemeModulePullback (projection j q hclosed)).obj (sourceSheaf f n)) ≅
      (schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).obj
        (exceptionalTensor f j q hclosed n) := by
  letI := complementMap_isIso f j q hclosed n
  letI := complementInclusion_isIso f j q hclosed n
  exact asIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
    (blowdownMap f j q hclosed n)) ≪≫
      (asIso ((schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
        (exceptionalInclusion f j q hclosed n))).symm

theorem complementFactorIso_comp :
    (complementFactorIso f j q hclosed n).hom ≫
        (schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
          (exceptionalInclusion f j q hclosed n) =
      (schemeModulePullback (exceptionalComplementOpen j q hclosed).ι).map
        (blowdownMap f j q hclosed n) := by
  letI := complementMap_isIso f j q hclosed n
  letI := complementInclusion_isIso f j q hclosed n
  exact isomorphism_factor_comp _ _

end KltDP.Geometry.PointBlowupTopDifferential
