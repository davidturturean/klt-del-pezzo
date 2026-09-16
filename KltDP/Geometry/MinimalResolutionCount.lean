import KltDP.Literature.ResolutionCountLiterals
import KltDP.Geometry.MinimalResolutionDebts
import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.IntegralSurfacePrimeCurve

/-!
# Minimal resolutions by induction on the number of exceptional curves (F10, E3)

This replaces the global termination hypothesis `ContractionMeasureHypothesis` of E1/E2 by a relative measure:
the number of exceptional prime curves of the current resolution over `X`.

* `NormalProjectiveSurface.PrimeCurve.coe_eq_of_subset_irreducibleCloseds`: a prime curve contained in a proper
  irreducible closed subset equals it (heights in the order of irreducible closed subsets: the subset has height at
  most one, the curve height one).
* `NormalProjectiveSurface.PrimeCurve.finite_setOf_subset`: only finitely many prime curves lie in a proper closed
  subset (finite decomposition into irreducible closed subsets in a Noetherian space).
* `IsResolution.exceptionalCurves_finite`: a resolution has finitely many exceptional prime curves. By Stacks 0BAJ
  (`BirationalIsoOverDenseOpenLiteral`) the resolution is an isomorphism over a dense open `V`, and exceptional curves
  lie in the proper closed complement of `π⁻¹ V` (`IsExceptionalCurve.subset_exceptionalLocus`).
* `IsContraction.ncard_exceptionalCurves_lt`: if `b : S → S'` contracts an exceptional curve `E` of `π = b ≫ π'`,
  then `π'` has fewer exceptional curves. `b` is an isomorphism over the complement of the centre (accepted
  `projection_restrict_puncture_isIso` through the isomorphism of `IsPointBlowupAt`); lifting generic points gives an
  injection of the exceptional curves of `π'` into those of `π` other than `E`. No clause beyond E1's
  `IsContraction` is needed.
* `exists_minimalResolution''`: every normal projective surface over an algebraically closed field has a minimal
  resolution. Hypotheses: Stacks literals only (0BGP, 07QW/07QU, 0C23, 0C5P, 02JX, 0C2N, 0C5J, 0BAJ).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

section Finiteness

/-- A prime curve contained in a proper irreducible closed subset of the surface is that subset. -/
theorem NormalProjectiveSurface.PrimeCurve.coe_eq_of_subset_irreducibleCloseds
    {S : NormalProjectiveSurface k} (C : S.PrimeCurve) (W : IrreducibleCloseds S.toScheme)
    (hCW : (C : Set S.toScheme) ⊆ W) (hW : (W : Set S.toScheme) ≠ Set.univ) :
    (C : Set S.toScheme) = W := by
  by_contra hne
  have hξW : closure ({W.isIrreducible.genericPoint} : Set S.toScheme) = W :=
    W.isIrreducible.closure_genericPoint W.isClosed
  have hξ : W.isIrreducible.genericPoint ≠ _root_.genericPoint S.toScheme := by
    intro h
    apply hW
    rw [← hξW, h]
    exact genericPoint_spec S.toScheme
  have hWle : Order.height W ≤ (1 : ℕ∞) := by
    have h := S.pointClosure_dimension_le_one W.isIrreducible.genericPoint hξ
    have hpc : S.pointClosure W.isIrreducible.genericPoint = W := IrreducibleCloseds.ext hξW
    rw [hpc, KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height] at h
    exact WithBot.coe_le_coe.mp h
  have hC1 : Order.height C.1 = 1 := by
    have h := C.dimension_one
    change topologicalKrullDim (C.1 : Set S.toScheme) = 1 at h
    rw [KltDP.Topology.topologicalKrullDim_irreducibleClosed_eq_height] at h
    exact_mod_cast h
  have hlt : C.1 < W := lt_of_le_of_ne hCW
    (fun h => hne (congrArg (fun Z : IrreducibleCloseds S.toScheme => (Z : Set S.toScheme)) h))
  have h2 := (Order.height_add_one_le hlt).trans hWle
  rw [hC1] at h2
  exact lt_irrefl (1 : ℕ∞)
    (((ENat.lt_add_one_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr le_rfl).trans_le h2)

/-- Only finitely many prime curves lie in a proper closed subset of the surface. -/
theorem NormalProjectiveSurface.PrimeCurve.finite_setOf_subset {S : NormalProjectiveSurface k}
    {Z : Set S.toScheme} (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    {C : S.PrimeCurve | (C : Set S.toScheme) ⊆ Z}.Finite := by
  obtain ⟨T, hTfin, hTclosed, hTirr, hZT⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have hinj : Set.InjOn (fun C : S.PrimeCurve => (C : Set S.toScheme))
      ((fun C : S.PrimeCurve => (C : Set S.toScheme)) ⁻¹' T) :=
    fun C₁ _ C₂ _ h => NormalProjectiveSurface.PrimeCurve.ext h
  refine (hTfin.preimage hinj).subset ?_
  intro C hC
  obtain ⟨T', hT'⟩ := hTfin.exists_finset_coe
  have hcov : (C : Set S.toScheme) ⊆ ⋃₀ (T' : Set (Set S.toScheme)) := by
    rw [hT', ← hZT]
    exact hC
  obtain ⟨t, htT, hCt⟩ := isIrreducible_iff_sUnion_isClosed.mp C.isIrreducible T'
    (fun z hz => hTclosed z (hT' ▸ Finset.mem_coe.mpr hz)) hcov
  have htT' : t ∈ T := hT' ▸ Finset.mem_coe.mpr htT
  have htne : t ≠ Set.univ := by
    intro h
    apply hZne
    apply Set.eq_univ_of_univ_subset
    rw [hZT, ← h]
    exact Set.subset_sUnion_of_mem htT'
  have heq := C.coe_eq_of_subset_irreducibleCloseds ⟨t, hTirr t htT', hTclosed t htT'⟩ hCt htne
  show (C : Set S.toScheme) ∈ T
  rw [heq]
  exact htT'

/-- A resolution has only finitely many exceptional prime curves (Stacks 0BAJ). -/
theorem IsResolution.exceptionalCurves_finite (hV : BirationalIsoOverDenseOpenLiteral k)
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme} (hπ : IsResolution S X π) :
    {C : S.PrimeCurve | IsExceptionalCurve π C}.Finite := by
  obtain ⟨V, hVdense, hViso⟩ := hV.exists_dense_open S X π hπ.over_base hπ.birational
  haveI := hViso
  obtain ⟨y, hy⟩ := hVdense.nonempty
  haveI : Nonempty V.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨s, hs⟩ := preimage_nonempty_of_isIso_restrict π V
  refine (NormalProjectiveSurface.PrimeCurve.finite_setOf_subset
    (Z := ((π ⁻¹ᵁ V : S.toScheme.Opens) : Set S.toScheme)ᶜ)
    (π ⁻¹ᵁ V).isOpen.isClosed_compl ?_).subset ?_
  · intro h
    have hsZ : s ∈ ((π ⁻¹ᵁ V : S.toScheme.Opens) : Set S.toScheme)ᶜ := by
      rw [h]
      exact Set.mem_univ s
    exact hsZ hs
  · intro C hC t ht htV
    exact IsExceptionalCurve.subset_exceptionalLocus π hC ht ⟨V, htV, hViso⟩

end Finiteness

section Count

/-- **The number of exceptional curves drops along a contraction over `X`.** -/
theorem IsContraction.ncard_exceptionalCurves_lt (hV : BirationalIsoOverDenseOpenLiteral k)
    {S S' X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    {π' : S'.toScheme ⟶ X.toScheme} (hπ : IsResolution S X π) (hπ' : IsResolution S' X π')
    {b : S.toScheme ⟶ S'.toScheme} {E : S.PrimeCurve} (hb : IsContraction S S' b E)
    (hfac : b ≫ π' = π) (hE : IsExceptionalCurve π E) :
    {C' : S'.PrimeCurve | IsExceptionalCurve π' C'}.ncard <
      {C : S.PrimeCurve | IsExceptionalCurve π C}.ncard := by
  obtain ⟨x', hx'closed, hEimg, -, hblow⟩ := hb.center
  obtain ⟨c, e, hbe⟩ := hblow.blowup
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  let P : S'.toScheme.Opens := PointBlowupGluing.puncture c.j c.q c.isClosed
  haveI hPiso : IsIso (b ∣_ P) := by
    have hbe' : e.hom ≫ PointBlowupGluing.projection c.j c.q c.isClosed = b := hbe
    haveI : IsIso ((PointBlowupGluing.projection c.j c.q c.isClosed) ∣_ P) :=
      PointBlowupGluing.projection_restrict_puncture_isIso c.j c.q c.isClosed
    rw [← hbe', morphismRestrict_comp]
    infer_instance
  haveI : IsProper b := hb.isProper
  haveI : IsProper π' := hπ'.isProper
  have hlift : ∀ C' : S'.PrimeCurve, ∃ C : S.PrimeCurve,
      b.base C.genericPoint = C'.genericPoint ∧ b.base C.genericPoint ≠ x' := by
    intro C'
    have hη'closed : ¬ IsClosed ({C'.genericPoint} : Set S'.toScheme) :=
      IntegralSurfacePointClosure.curveGenericPoint_not_isClosed S'.toScheme C'
    have hη'ne : C'.genericPoint ≠ x' := by
      intro h
      apply hη'closed
      rw [h]
      exact hx'closed
    have hη'P : C'.genericPoint ∈ P := by
      show C'.genericPoint ∈ ({c.j.base c.q} : Set S'.toScheme)ᶜ
      rw [c.base_eq]
      exact hη'ne
    obtain ⟨t, ht⟩ := (b ∣_ P).homeomorph.surjective ⟨C'.genericPoint, hη'P⟩
    have hbt : b.base t.1 = C'.genericPoint :=
      (morphismRestrict_base_coe b P t).symm.trans (congrArg Subtype.val ht)
    have htclosed : ¬ IsClosed ({t.1} : Set S.toScheme) := by
      intro h
      apply hη'closed
      have himg := b.isClosedMap _ h
      rwa [Set.image_singleton, hbt] at himg
    have htgen : t.1 ≠ genericPoint S.toScheme := by
      intro h
      apply IntegralSurfacePointClosure.curveGenericPoint_ne_genericPoint S'.toScheme
        S'.dimension_two C'
      show C'.genericPoint = genericPoint S'.toScheme
      rw [← hbt, h]
      exact hb.birational.map_genericPoint
    refine ⟨S.primeCurveOfNonclosedPoint t.1 htgen htclosed, ?_, ?_⟩
    · rw [NormalProjectiveSurface.primeCurveOfNonclosedPoint_genericPoint]
      exact hbt
    · rw [NormalProjectiveSurface.primeCurveOfNonclosedPoint_genericPoint, hbt]
      exact hη'ne
  choose f hf using hlift
  have hfin := hπ.exceptionalCurves_finite hV
  have hEmem : E ∈ {C : S.PrimeCurve | IsExceptionalCurve π C} := hE
  calc {C' : S'.PrimeCurve | IsExceptionalCurve π' C'}.ncard
      ≤ ({C : S.PrimeCurve | IsExceptionalCurve π C} \ {E}).ncard := by
        refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hfin.subset Set.diff_subset)
        · intro C' hC'
          obtain ⟨y, hy⟩ := hC'
          have hyclosed : IsClosed ({y} : Set X.toScheme) := by
            have himg := π'.isClosedMap _ C'.isClosed
            rwa [hy] at himg
          have hgy : π.base (f C').genericPoint = y := by
            rw [← hfac, Scheme.comp_base_apply, (hf C').1]
            have hmem : π'.base C'.genericPoint ∈ π'.base '' (C' : Set S'.toScheme) :=
              Set.mem_image_of_mem _ C'.genericPoint_mem
            rw [hy] at hmem
            exact hmem
          have hsub : π.base '' (f C' : Set S.toScheme) ⊆ {y} := by
            rw [← (f C').closure_genericPoint]
            refine (image_closure_subset_closure_image π.continuous).trans ?_
            rw [Set.image_singleton, hgy, hyclosed.closure_eq]
          have himage : π.base '' (f C' : Set S.toScheme) = {y} :=
            ((f C').nonempty.image _).subset_singleton_iff.mp hsub
          have hexc : IsExceptionalCurve π (f C') := by
            show ∃ x : X.Point, π.base '' (f C' : Set S.toScheme) = {x}
            exact ⟨y, himage⟩
          have hneE : f C' ≠ E := by
            intro hfE
            have hmem : (f C').genericPoint ∈ (E : Set S.toScheme) := by
              rw [← hfE]
              exact (f C').genericPoint_mem
            have himgE := Set.mem_image_of_mem b.base hmem
            rw [hEimg] at himgE
            exact (hf C').2 himgE
          exact Set.mem_diff_of_mem hexc (Set.not_mem_singleton_iff.mpr hneE)
        · intro C₁ _ C₂ _ h12
          have hg : C₁.genericPoint = C₂.genericPoint := by
            rw [← (hf C₁).1, ← (hf C₂).1, h12]
          apply NormalProjectiveSurface.PrimeCurve.ext
          rw [← C₁.closure_genericPoint, ← C₂.closure_genericPoint, hg]
    _ < {C : S.PrimeCurve | IsExceptionalCurve π C}.ncard :=
        Set.ncard_diff_singleton_lt_of_mem hEmem hfin

end Count

/-- **Existence of a minimal resolution from Stacks literals only**, by strong induction on the number of
exceptional prime curves of the current resolution. -/
theorem exists_minimalResolution'' [IsAlgClosed k]
    (hL : LipmanModificationLiteral k) (hEx : FiniteTypeExcellentFormalFibresLiteral k)
    (hC : CompletionNormalLiteral.{u}) (hP : RegularProperProjectiveLiteral k)
    (hD : BirationalDimensionLiteral k) (hCa : CastelnuovoContractionLiteral k)
    (hU : ContractionUniversalLiteral k) (hV : BirationalIsoOverDenseOpenLiteral k)
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme), IsMinimalResolution S X π := by
  obtain ⟨S₀, π₀, h₀⟩ := (lipmanResolutionLiteral_of_literals hL hEx hC hP hD).exists_resolution X
    (normalSurface_singularLocus_finite X)
  suffices key : ∀ (n : ℕ) (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsResolution S X π → {C : S.PrimeCurve | IsExceptionalCurve π C}.ncard = n →
        ∃ (S' : NormalProjectiveSurface k) (π' : S'.toScheme ⟶ X.toScheme),
          IsMinimalResolution S' X π' from
    key _ S₀ π₀ h₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S π hπ hn
    by_cases hmin : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → ¬ IsMinusOneCurve hπ.regular C
    · exact ⟨S, π, { toIsResolution := hπ, no_minusOne_curve := hmin }⟩
    · push_neg at hmin
      obtain ⟨E, hE, hE1⟩ := hmin
      obtain ⟨S', b, hb⟩ := hCa.exists_contraction S hπ.regular E hE1
      obtain ⟨π', hfac, hres⟩ := hπ.of_contraction hU hb hE
      refine ih _ ?_ S' π' hres rfl
      rw [← hn]
      exact hb.ncard_exceptionalCurves_lt hV hπ hres hfac hE

end KltDP.Geometry
