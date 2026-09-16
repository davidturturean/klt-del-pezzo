import KltDP.Geometry.GluedConormalPullbackFrame
import KltDP.Geometry.AffineModuleTildePullbackUnit

/-!
# Equation independence of the original global conormal chart map

The original quotient-chart comparison with the actual global conormal
does not depend on the regular equation used to construct its two frames.
Both frames change by the same original quotient scalar. The scalar
identity follows from the actual structural section map and its proved
quotient-chart normalization.

No transition identity or comparison witness is an input. Compatibility
under different affine opens, and gluing adjunction, remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.GluedConormalEquationIndependence

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The original equation frame on the tilde of the actual cotangent module. -/
def tildeFrame (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    _root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf ≅
      (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent).tilde :=
  (AffineModuleTilde.unitIso (Γ(X, U.1) ⧸ I.ideal U)).symm ≪≫
    AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (Γ(X, U.1) ⧸ I.ideal U))
      (N := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      (gluedAffineCotangentEquiv I U d hI hd)

/-- The original chart structural map sends a coefficient to its quotient section. -/
theorem chart_scalar (r : Γ(X, U.1)) :
    ((I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ U.1).appTop (gluedAffineEquation U r) =
      StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤ (Ideal.Quotient.mk (I.ideal U) r) := by
  let B := Γ(X, U.1) ⧸ I.ideal U
  let e := Scheme.ΓSpecIso (CommRingCat.of B)
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom
      (((I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ U.1).appTop (gluedAffineEquation U r)) =
    e.hom (StructureSheaf.toOpen B ⊤ (Ideal.Quotient.mk (I.ideal U) r))
  calc
    _ = ((I.gluedTo ∣_ U.1).appTop ≫
        (I.gluedRestrictionSectionsIso U).hom) (gluedAffineEquation U r) := rfl
    _ = (U.1.topIso.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))
        (gluedAffineEquation U r) := congrArg
      (fun q => q (gluedAffineEquation U r))
      (I.gluedTo_restrict_appTop_comp_sectionsIso U)
    _ = Ideal.Quotient.mk (I.ideal U) r := by
      change Ideal.Quotient.mk (I.ideal U)
        (U.1.topIso.hom (U.1.topIso.inv r)) = _
      exact congrArg (Ideal.Quotient.mk (I.ideal U))
        (U.1.topIso.commRingCatIsoToRingEquiv.apply_symm_apply r)
    _ = _ := (e.commRingCatIsoToRingEquiv.apply_symm_apply
      (Ideal.Quotient.mk (I.ideal U) r)).symm

/-- The tilde frame sends the original quotient scalar section to its original class. -/
theorem tildeFrame_toOpen (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1))
    (V : (I.glueDataObj U).Opens) (q : Γ(X, U.1) ⧸ I.ideal U) :
    (tildeFrame I U d hI hd).hom.val.app (op V)
        (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) V q) =
      ModuleCat.Tilde.toOpen
        (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) V
        (gluedAffineCotangentEquiv I U d hI hd q) := by
  let B := Γ(X, U.1) ⧸ I.ideal U
  let e := AffineModuleTilde.unitIso B
  have he : e.inv.val.app (op V) (StructureSheaf.toOpen B V q) =
      ModuleCat.Tilde.toOpen (ModuleCat.of B B) V q := by
    calc
      _ = e.inv.val.app (op V)
          (e.hom.val.app (op V) (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V q)) :=
        congrArg (fun s => e.inv.val.app (op V) s)
          (AffineModuleTildePullbackUnit.unitIso_hom_toOpen B V q).symm
      _ = _ := by
        change ((e.hom ≫ e.inv).val.app (op V))
          (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V q) = _
        rw [Iso.hom_inv_id]
        rfl
  change (AffineModuleTilde.map
      (gluedAffineCotangentEquiv I U d hI hd).toModuleIso.hom).val.app (op V)
      (e.inv.val.app (op V) (StructureSheaf.toOpen B V q)) = _
  rw [he]
  exact AffineModuleTilde.map_app_toOpen
    (gluedAffineCotangentEquiv I U d hI hd).toModuleIso.hom V q

/-- The original global chart comparison identifies the two original equation frames. -/
theorem tildeFrame_comparison (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    (tildeFrame I U d hI hd).hom ≫
        (gluedAffineConormalTildePullbackIso I U d hI hd).hom =
      (gluedAffineConormalChartFrameIso I U d hI hd).hom := by
  simp only [tildeFrame, gluedAffineConormalTildePullbackIso,
    gluedAffineConormalTildeIso, gluedAffineConormalChartFrameIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

variable (d e : Γ(X, U.1))
  (hId : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1))
  (hIe : I.ideal U = Ideal.span {e}) (he : e ∈ nonZeroDivisors Γ(X, U.1))

/-- An actual coefficient multiplying the equation multiplies the original tilde frame. -/
theorem tildeFrame_mul (r : Γ(X, U.1)) (her : e = r * d) :
    (tildeFrame I U e hIe he).hom =
      schemeScalarEnd
          (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤
            (Ideal.Quotient.mk (I.ideal U) r)) ≫
        (tildeFrame I U d hId hd).hom := by
  apply ((ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U)
    (I.ideal U).Cotangent).tilde.unitHomEquiv).injective
  apply (schemeModuleSectionsEquivTop _).injective
  change (tildeFrame I U e hIe he).hom.val.app (op ⊤) (1 : Γ(I.glueDataObj U, ⊤)) =
    (tildeFrame I U d hId hd).hom.val.app (op ⊤)
      ((schemeScalarEnd
        (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤
          (Ideal.Quotient.mk (I.ideal U) r))).val.app (op ⊤) (1 : Γ(I.glueDataObj U, ⊤)))
  rw [schemeScalarEnd_appTop, one_mul]
  have h1 : (1 : Γ(I.glueDataObj U, ⊤)) =
      StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤ 1 :=
    (map_one (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤).hom).symm
  rw [h1, tildeFrame_toOpen, tildeFrame_toOpen]
  apply congrArg (ModuleCat.Tilde.toOpen
    (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) ⊤)
  rw [gluedAffineCotangentEquiv_one]
  change (I.ideal U).toCotangent (gluedAffineIdealEquation I U e hIe) =
    KltDP.RingTheory.principalConormalEquiv (I.ideal U)
      (gluedAffineIdealEquation I U d hId) hId.symm hd
      (Ideal.Quotient.mk (I.ideal U) r)
  rw [KltDP.RingTheory.principalConormalEquiv_mk]
  exact congrArg (I.ideal U).toCotangent (Subtype.ext her)

/-- The actual global conormal frame changes by the same original quotient coefficient. -/
theorem chartFrame_mul (r : Γ(X, U.1)) (her : e = r * d) :
    (gluedAffineConormalChartFrameIso I U e hIe he).hom =
      schemeScalarEnd
          (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤
            (Ideal.Quotient.mk (I.ideal U) r)) ≫
        (gluedAffineConormalChartFrameIso I U d hId hd).hom := by
  apply (cancel_mono (gluedAffineConormalChartComparisonIso I U).hom).mp
  rw [Category.assoc, gluedAffineConormalChartFrameIso_comparison,
    gluedAffineConormalChartFrameIso_comparison, ← chart_scalar I U r]
  have hr : gluedAffineEquation U e = gluedAffineEquation U r * gluedAffineEquation U d := by
    rw [her]
    exact U.1.topIso.inv.hom.map_mul r d
  simpa only [hr] using
    pulledConormalGenerator_mul (I.gluedTo ∣_ U.1) (I.glueDataObjIso U).hom
      (gluedAffineEquation U r) (gluedAffineEquation U d)
      (gluedAffineEquation_eq_zero I U d hId)

/-- The actual tilde-to-global-pullback comparison is independent of its regular equation. -/
theorem tildePullbackIso_eq :
    gluedAffineConormalTildePullbackIso I U d hId hd =
      gluedAffineConormalTildePullbackIso I U e hIe he := by
  have hemem : e ∈ Ideal.span {d} := by
    rw [← hId, hIe]
    exact Ideal.subset_span (Set.mem_singleton e)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hemem
  have her : e = r * d := hr.symm
  apply Iso.ext
  apply (cancel_epi (tildeFrame I U e hIe he).hom).mp
  calc
    _ = schemeScalarEnd
          (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤
            (Ideal.Quotient.mk (I.ideal U) r)) ≫
        (tildeFrame I U d hId hd).hom ≫
          (gluedAffineConormalTildePullbackIso I U d hId hd).hom := by
      rw [tildeFrame_mul I U d e hId hd hIe he r her, Category.assoc]
    _ = schemeScalarEnd
          (StructureSheaf.toOpen (Γ(X, U.1) ⧸ I.ideal U) ⊤
            (Ideal.Quotient.mk (I.ideal U) r)) ≫
        (gluedAffineConormalChartFrameIso I U d hId hd).hom := by
      rw [tildeFrame_comparison]
    _ = (gluedAffineConormalChartFrameIso I U e hIe he).hom :=
      (chartFrame_mul I U d e hId hd hIe he r her).symm
    _ = _ := (tildeFrame_comparison I U e hIe he).symm

/-- The original two-open-restriction presentation is equation independent too. -/
theorem tildeIso_eq :
    gluedAffineConormalTildeIso I U d hId hd =
      gluedAffineConormalTildeIso I U e hIe he := by
  apply Iso.ext
  apply (cancel_mono (gluedAffineGlobalConormalPullbackIso I U).hom).mp
  exact congrArg Iso.hom (tildePullbackIso_eq I U d e hId hd hIe he)

end KltDP.Geometry.GluedConormalEquationIndependence
