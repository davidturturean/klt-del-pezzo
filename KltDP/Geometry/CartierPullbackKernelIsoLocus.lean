import KltDP.Geometry.CartierPullbackComparison
import KltDP.Geometry.SchemeKernelBaseChangeIsoLocus
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.SchemeKernelGluedIso

/-!
# Cartier pullback and the original kernel over an isomorphism locus

If a regular effective Cartier divisor has the kernel of a given closed
immersion, and a generic-point-preserving map is an isomorphism on an open
containing that closed subscheme, its Cartier pullback has the kernel of
the actual base change. The comparison retains the original inclusions in
the structure sheaf, so equality of embedded ideal data follows.

The proof composes the accepted general Cartier ideal pullback comparison,
the accepted inclusion-compatible isomorphism for equal closed-immersion
kernels, and the accepted base-change comparison over an isomorphism locus.
No flatness, kernel quasicoherence or target ideal equality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.CartierPullbackKernelIsoLocus

open KltDP.Geometry KltDP.Geometry.CartierPullbackComparison
  KltDP.Geometry.SchemeKernelBaseChangeIsoLocus

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance kernelInclusionMono {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono (schemeKernelIdealι f) := by
  unfold schemeKernelIdealι
  infer_instance

/-- A kernel-module isomorphism preserving the original inclusions gives
equality of the embedded kernel ideal data. -/
theorem ker_eq_of_compatibleKernelIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    (e : schemeKernelIdeal f ≅ schemeKernelIdeal g)
    (he : e.hom ≫ schemeKernelIdealι g = schemeKernelIdealι f) : f.ker = g.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply,
    ← schemeKernelIdealι_range_eq_ker f U.1, ← schemeKernelIdealι_range_eq_ker g U.1]
  have hU (t : (schemeKernelIdeal f).val.obj (op U.1)) :
      (schemeKernelIdealι g).val.app (op U.1) (e.hom.val.app (op U.1) t) =
        (schemeKernelIdealι f).val.app (op U.1) t :=
    congrArg (fun α : schemeKernelIdeal f ⟶ _root_.SheafOfModules.unit Z.ringCatSheaf =>
      α.val.app (op U.1) t) he
  have hi (t : (schemeKernelIdeal g).val.obj (op U.1)) :
      e.hom.val.app (op U.1) (e.inv.val.app (op U.1) t) = t :=
    congrArg (fun α : schemeKernelIdeal g ⟶ schemeKernelIdeal g =>
      α.val.app (op U.1) t) e.inv_hom_id
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨e.hom.val.app (op U.1) t, hU t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨e.inv.val.app (op U.1) t, ?_⟩
    exact (hU _).symm.trans (congrArg ((schemeKernelIdealι g).val.app (op U.1)) (hi t))

set_option maxHeartbeats 4000000 in
/-- The accepted general Cartier ideal pullback isomorphism preserves
the original inclusions into the structure sheaf. -/
theorem pullbackKernelIso_inclusion {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Y) [GenericPointPreserving π] (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D) :
    (pullbackKernelIso π D hD).hom ≫ schemeKernelIdealι (pullbackIdealData π D hD).gluedTo =
      pulledKernelInclusion (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π := by
  unfold pullbackKernelIso
  exact schemeModuleMonicFactorIsoOnOpenCover_comp _ _ _ _ _ _

set_option maxHeartbeats 4000000 in
/-- The Cartier pullback has the actual base-change kernel when the
original closed subscheme lies in the map's isomorphism locus. -/
theorem pullbackIdealData_eq_kernel_of_isoLocus {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [GenericPointPreserving π]
    (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)
    (g : Z ⟶ Y) [IsClosedImmersion g] (V : Y.Opens) [IsIso (π ∣_ V)]
    (hgV : Set.range g.base ⊆ (V : Set Y))
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = g.ker) :
    pullbackIdealData π D hD = (pullback.fst π g).ker := by
  letI : IsClosedImmersion (pullback.fst π g) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  let I := effectiveCartierIdealDataOfRegularEquations Y D hD
  let J := pullbackIdealData π D hD
  let eS : schemeKernelIdeal I.gluedTo ≅ schemeKernelIdeal g :=
    kernelIsoOfKerEq I.gluedTo g (I.ker_gluedTo.trans hI)
  have hS : eS.hom ≫ schemeKernelIdealι g = schemeKernelIdealι I.gluedTo :=
    kernelIsoOfKerEq_hom_ι I.gluedTo g (I.ker_gluedTo.trans hI)
  let eP := pullbackKernelIso π D hD
  have hP : eP.hom ≫ schemeKernelIdealι J.gluedTo = pulledKernelInclusion I.gluedTo π :=
    pullbackKernelIso_inclusion π D hD
  let e : schemeKernelIdeal J.gluedTo ≅ schemeKernelIdeal (pullback.fst π g) :=
    eP.symm ≪≫ (schemeModulePullback π).mapIso eS ≪≫ baseChangeKernelIso π g V hgV
  have he : e.hom ≫ schemeKernelIdealι (pullback.fst π g) = schemeKernelIdealι J.gluedTo := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      baseChangeKernelIso_inclusion]
    unfold pulledKernelInclusion
    rw [← Category.assoc ((schemeModulePullback π).map eS.hom), ← Functor.map_comp, hS]
    change eP.inv ≫ pulledKernelInclusion I.gluedTo π = schemeKernelIdealι J.gluedTo
    rw [← hP, Iso.inv_hom_id_assoc]
  exact J.ker_gluedTo.symm.trans
    (ker_eq_of_compatibleKernelIso J.gluedTo (pullback.fst π g) e he)

end KltDP.Geometry.CartierPullbackKernelIsoLocus
