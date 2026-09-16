import KltDP.Geometry.SheafSectionPullbackCoefficient
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# Support of the effective Cartier divisor of an original section

The accepted effective-Cartier construction preserves its original nonzero
section. Literal residue-field pullback vanishing puts the point in the actual
divisor ideal's support. A unit germ under an actual local functional excludes
the point: its value belongs to the original canonical-section evaluation ideal,
which the accepted comparison identifies with the original regular equation.

The final adapter constructs the divisor and its section-preserving isomorphism.
It assumes the actual section and its two proved local properties, as inputs to
this section-to-divisor adapter. It makes no positivity or ample-existence claim.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.EffectiveCartierSectionSupport

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

/-- Restricting an actual local functional and the original global section
does not change the germ of its value. -/
theorem functional_germ_restriction (M : X.Modules)
    (s : M.val.obj (op (⊤ : X.Opens))) (U V : X.Opens) (hVU : V ≤ U)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (y : X) (hy : y ∈ V) :
    X.presheaf.germ V y hy
        (φ.val.app (op (Over.mk (homOfLE hVU)))
          (M.val.map (homOfLE (le_top : V ≤ ⊤)).op s)) =
      X.presheaf.germ U y (hVU hy)
        (φ.val.app (op (Over.mk (𝟙 U)))
          (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)) := by
  let j : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU) (by simp)
  have hc : M.val.map (homOfLE hVU).op
      (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s) =
        M.val.map (homOfLE (le_top : V ≤ ⊤)).op s :=
    (CategoryTheory.congr_fun (M.val.presheaf.map_comp
      (homOfLE (le_top : U ≤ ⊤)).op (homOfLE hVU).op) s).symm
  have hn : φ.val.app (op (Over.mk (homOfLE hVU)))
      (M.val.map (homOfLE hVU).op
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)) =
      X.presheaf.map (homOfLE hVU).op
        (φ.val.app (op (Over.mk (𝟙 U)))
          (M.val.map (homOfLE (le_top : U ≤ ⊤)).op s)) :=
    _root_.PresheafOfModules.naturality_apply φ.val j.op _
  rw [hc] at hn
  exact (congrArg (fun a : Γ(X, V) => X.presheaf.germ V y hy a) hn).trans
    (X.presheaf.germ_res_apply (homOfLE hVU) y hy _)

variable [IsIntegral X]

/-- A unit germ under any original local functional excludes the point from
the support of the actual effective Cartier ideal. -/
theorem not_mem_support_of_unit_eval (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (U : X.Opens) (y : X) (hyU : y ∈ U)
    (φ : (cartierDivisorModule X E).over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hu : IsUnit (X.presheaf.germ U y hyU
      (φ.val.app (op (Over.mk (𝟙 U)))
        ((cartierDivisorModule X E).val.map (homOfLE (le_top : U ≤ ⊤)).op
          (effectiveCartierSection X E hE))))) :
    y ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
  obtain ⟨c, hyc⟩ := hE y
  let V : X.Opens := U ⊓ c.chart.openSet
  have hyV : y ∈ V := ⟨hyU, hyc⟩
  letI : Nonempty V := ⟨⟨y, hyV⟩⟩
  let d := RegularCartierEquationChart.restrict X E c V inf_le_right
  let ℓ : (cartierDivisorModule X E).val.obj (op V) →ₗ[Γ(X, V)] Γ(X, V) :=
    (φ.val.app (op (Over.mk (homOfLE (inf_le_left : V ≤ U))))).hom
  let b : Γ(X, V) := ℓ ((cartierDivisorModule X E).val.map
    (homOfLE (le_top : V ≤ ⊤)).op (effectiveCartierSection X E hE))
  have hb : b ∈ sectionEvaluationIdeal X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) V := ⟨ℓ, rfl⟩
  have heval : sectionEvaluationIdeal X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) V =
        Ideal.span ({d.coefficient} : Set Γ(X, V)) :=
    effectiveCartierSection_evaluationIdeal X E hE d
  rw [heval] at hb
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hb
  have hbu : IsUnit (X.presheaf.germ V y hyV b) := by
    have hg := functional_germ_restriction X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) U V inf_le_left φ y hyV
    change IsUnit (X.presheaf.germ V y hyV
      (φ.val.app (op (Over.mk (homOfLE (inf_le_left : V ≤ U))))
        ((cartierDivisorModule X E).val.map (homOfLE (le_top : V ≤ ⊤)).op
          (effectiveCartierSection X E hE))))
    rw [hg]
    exact hu
  have hdu : IsUnit (X.presheaf.germ V y hyV d.coefficient) := by
    rw [hr, map_mul] at hbu
    exact isUnit_of_mul_isUnit_left hbu
  intro hmem
  exact (NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
    E hE d y hyV).1 hmem hdu

/-- Literal residue-field pullback vanishing of the original canonical section
puts the point in the actual effective Cartier support. -/
theorem mem_support_of_pulled_canonical_eq_zero (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (x : X)
    (hx : RationalTreePicard.pulledSection (X.fromSpecResidueField x)
      (cartierDivisorModule X E) ⊤ (effectiveCartierSection X E hE) = 0) :
    x ∈ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
  obtain ⟨c, hxc⟩ := hE x
  let U : X.Opens := c.chart.openSet
  letI : Nonempty U := c.chart.nonempty
  let M : X.Modules := cartierDivisorModule X E
  let s : M.val.obj (op U) := M.val.map (homOfLE (le_top : U ≤ ⊤)).op
    (effectiveCartierSection X E hE)
  let τ := cartierEquationOverIso X E U c.chart.equation c.chart.represents
  have hc : τ.inv.val.app (op (Over.mk (𝟙 U))) s = c.coefficient := by
    have h := effectiveCartierSection_frame_eval X E hE c
    have hid : M.val.map (𝟙 U).op s = s :=
      CategoryTheory.congr_fun (M.val.presheaf.map_id (op U)) s
    change τ.inv.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 U).op s) =
      c.coefficient at h
    rw [hid] at h
    exact h
  have hn := SheafSectionPullbackCoefficient.not_isUnit_germ_of_residue_pullback_eq_zero
    M (effectiveCartierSection X E hE) x hx U hxc τ.symm
  change ¬ IsUnit (X.presheaf.germ U x hxc
    (τ.inv.val.app (op (Over.mk (𝟙 U))) s)) at hn
  rw [hc] at hn
  exact (NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ
    E hE c x hxc).2 hn

/-- The original nonzero section determines an actual effective Cartier divisor
through its vanishing point and avoiding a point with unit frame coefficient.
The original section is retained by the returned sheaf isomorphism. -/
theorem exists_effectiveCartier_through_and_avoiding (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) (x y : X)
    (hx : RationalTreePicard.pulledSection (X.fromSpecResidueField x) L.obj ⊤ s = 0)
    (U : X.Opens) (hyU : y ∈ U)
    (e : L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hy : IsUnit (X.presheaf.germ U y hyU
      (e.hom.val.app (op (Over.mk (𝟙 U)))
        (L.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op s)))) :
    ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
      (a : cartierDivisorModule X E ≅ L.obj),
      a.hom.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE) = s ∧
      x ∈ (effectiveCartierIdealDataOfRegularEquations X E hE).support ∧
      y ∉ (effectiveCartierIdealDataOfRegularEquations X E hE).support := by
  obtain ⟨E, hE, a, ha⟩ := exists_effectiveCartier_of_nonzero_section X L s hs
  have hcancel : a.inv.val.app (op (⊤ : X.Opens)) s =
      effectiveCartierSection X E hE := by
    rw [← ha]
    exact congrArg (fun f : cartierDivisorModule X E ⟶ cartierDivisorModule X E =>
      f.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE)) a.hom_inv_id
  have hxE : RationalTreePicard.pulledSection (X.fromSpecResidueField x)
      (cartierDivisorModule X E) ⊤ (effectiveCartierSection X E hE) = 0 := by
    have h := RationalTreePicard.pullback_map_val_app_pulledSection
      (X.fromSpecResidueField x) a.inv ⊤ s
    rw [hx, map_zero, hcancel] at h
    exact h.symm
  let φ : (cartierDivisorModule X E).over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U) :=
    (_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map a.hom ≫ e.hom
  have hyE : IsUnit (X.presheaf.germ U y hyU
      (φ.val.app (op (Over.mk (𝟙 U)))
        ((cartierDivisorModule X E).val.map (homOfLE (le_top : U ≤ ⊤)).op
          (effectiveCartierSection X E hE)))) := by
    have hn := _root_.PresheafOfModules.naturality_apply a.hom.val
      (homOfLE (le_top : U ≤ ⊤)).op (effectiveCartierSection X E hE)
    rw [ha] at hn
    change IsUnit (X.presheaf.germ U y hyU
      (e.hom.val.app (op (Over.mk (𝟙 U)))
        (a.hom.val.app (op U)
          ((cartierDivisorModule X E).val.map (homOfLE (le_top : U ≤ ⊤)).op
            (effectiveCartierSection X E hE)))))
    rw [hn]
    exact hy
  exact ⟨E, hE, a, ha, mem_support_of_pulled_canonical_eq_zero X E hE x hxE,
    not_mem_support_of_unit_eval X E hE U y hyU φ hyE⟩

end KltDP.Geometry.EffectiveCartierSectionSupport
