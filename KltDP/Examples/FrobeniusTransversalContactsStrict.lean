import KltDP.Examples.FrobeniusStrictImageIso
import KltDP.Examples.FrobeniusTransversalContactsSPn

/-!
# Transversal contacts on the strict transforms themselves

For a point `x` of the strict graph `B` lying over the isomorphism open `V`, the pulled-back point
`restrictPoint x` of `B ×_S V` (BRIEF14 scheme isomorphism `graphRestrictIso`) gives a chain of stalk
isomorphisms: the stalk of `B` at `x` is the stalk of `B ×_S V` (open immersion `pullback.snd`), which is
the stalk of `B_i ×_T isoOpen` (the isomorphism), which is the stalk of the tower closure `B_i` at the
image point (open immersion `pullback.snd`). When `x` is the unique point of `B ∩ P_i` the image point is
the contact point of `B_i` (`graphRestrictPoint_eq_contact`), so the stalk of `B` at `x` is identified with
the accepted `closureContactStalk` (`graphContactStalkEquiv`), the pulled equation of `P_i` becomes an element
of the stalk of `B` (`graphContactGermS`), and its contact length is one on `B` itself
(`graphStrict_contact_length`). The same for the strict fibre (`fiberStrict_contact_length`).
Bundle `sPn_transversal_contacts'`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTransversalContactsStrict

open KltDP.Geometry KltDP.Geometry.SchematicImageOpenBaseChange
  KltDP.Geometry.SchematicImageToImageIso FrobeniusBlowupContact FrobeniusGraphClosed
  FrobeniusStrictTransformClosure FrobeniusFiberClosure FrobeniusTranslatedCharts
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusAdaptedStrictTransform FrobeniusAdaptedFiberTransform FrobeniusClosureContact
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusClosureNewestUnique FrobeniusIncidenceSPn
  FrobeniusNewestTransversality FrobeniusTransversalContactsSPn FrobeniusStrictImageIsoOpen
  FrobeniusStrictImageIso

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-! ## The strict fibre -/

section Fiber

variable (i : Fin n)

theorem fiber_mem_range_snd (x : fiberStrict (q + 1) n a i)
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    x ∈ Set.range (pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)).base := by
  rw [Scheme.Pullback.range_snd]
  change (fiberStrictι (q + 1) n a i).base x ∈ Set.range (isoPreimage q n a i).ι.base
  rw [Scheme.Opens.range_ι]
  exact hx

/-- The point of `F_i ×_S V` over a point of `F_i` lying over `V`. -/
def fiberRestrictPoint (x : fiberStrict (q + 1) n a i)
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) : fiberRestrict q n a i :=
  Classical.choose (fiber_mem_range_snd q n a i x hx)

theorem fiberRestrictPoint_snd (x : fiberStrict (q + 1) n a i)
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    (pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)).base
      (fiberRestrictPoint q n a i x hx) = x :=
  Classical.choose_spec (fiber_mem_range_snd q n a i x hx)

/-- The image point on the tower strict fibre. -/
def fiberTowerPoint (x' : fiberRestrict q n a i) :
    liftedFiberClosure (translatedInitial (q + 1) (a i)) (q + 1) :=
  (pullback.snd (isoMap q n a i) (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))).base
    ((fiberRestrictIso q n a i).hom.base x')

theorem fiberClosureInclusion_fiberTowerPoint (x' : fiberRestrict q n a i) :
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base (fiberTowerPoint q n a i x') =
      (towerProjection (q + 1) n a i).base
        ((fiberStrictι (q + 1) n a i).base
          ((pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)).base x')) := by
  have h1 := congrArg (fun h => h.base ((fiberRestrictIso q n a i).hom.base x'))
    (pullback.condition (f := isoMap q n a i)
      (g := fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)))
  simp only [Scheme.comp_base_apply] at h1
  have h2 := congrArg (fun h => h.base x') (fiberRestrictIso_hom_fst q n a i)
  simp only [Scheme.comp_base_apply] at h2
  have h3 := congrArg (fun h => h.base x')
    (pullback.condition (f := (isoPreimage q n a i).ι) (g := fiberStrictι (q + 1) n a i))
  simp only [Scheme.comp_base_apply] at h3
  change (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base
    ((pullback.snd (isoMap q n a i) (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))).base
      ((fiberRestrictIso q n a i).hom.base x')) = _
  rw [← h1, h2, isoMap_base, ← Scheme.Opens.ι_base_apply, h3]

/-- The stalk of `F_i` at a point over `V` is the stalk of the tower strict fibre at the image point. -/
def fiberStalkEquiv (x' : fiberRestrict q n a i) :
    (fiberStrict (q + 1) n a i).presheaf.stalk
        ((pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)).base x') ≃+*
      (liftedFiberClosure (translatedInitial (q + 1) (a i)) (q + 1)).presheaf.stalk
        (fiberTowerPoint q n a i x') :=
  (asIso ((pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)).stalkMap x') ≪≫
    (asIso ((fiberRestrictIso q n a i).hom.stalkMap x')).symm ≪≫
      (asIso ((pullback.snd (isoMap q n a i)
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))).stalkMap
          ((fiberRestrictIso q n a i).hom.base x'))).symm).commRingCatIsoToRingEquiv

/-- Over the single point of `F_i ∩ P_i`, the image point is the centre point of the tower strict
fibre. -/
theorem fiberTowerPoint_eq_contact (x : fiberStrict (q + 1) n a i)
    (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    fiberTowerPoint q n a i (fiberRestrictPoint q n a i x hx) =
      fiberContactPoint (translatedInitial (q + 1) (a i)) (q + 1) := by
  apply Scheme.IdealSheafData.gluedTo_injective
    (liftedFiberClosureIdeal (translatedInitial (q + 1) (a i)) (q + 1))
  change (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base _ =
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base _
  rw [fiberClosureInclusion_fiberTowerPoint, fiberRestrictPoint_snd]
  exact fiberStrict_newest_projection q n a i _ ⟨⟨x, rfl⟩, hP⟩

/-- The stalk of `F_i` at the point of `F_i ∩ P_i`, identified with the accepted contact stalk. -/
def fiberContactStalkEquivS (x : fiberStrict (q + 1) n a i)
    (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    (fiberStrict (q + 1) n a i).presheaf.stalk x ≃+*
      fiberContactStalk (translatedInitial (q + 1) (a i)) (q + 1) :=
  ((fiberStrict (q + 1) n a i).presheaf.stalkCongr
      (Inseparable.of_eq (fiberRestrictPoint_snd q n a i x hx).symm)).commRingCatIsoToRingEquiv.trans
    ((fiberStalkEquiv q n a i (fiberRestrictPoint q n a i x hx)).trans
      ((liftedFiberClosure (translatedInitial (q + 1) (a i)) (q + 1)).presheaf.stalkCongr
        (Inseparable.of_eq (fiberTowerPoint_eq_contact q n a i x hP hx))).commRingCatIsoToRingEquiv)

/-- The pulled equation of `P_i` as an element of the stalk of `F_i`. -/
def fiberContactGermS (x : fiberStrict (q + 1) n a i)
    (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    (fiberStrict (q + 1) n a i).presheaf.stalk x :=
  (fiberContactStalkEquivS q n a i x hP hx).symm
    (fiberContactGerm (translatedInitial (q + 1) (a i)) q chartU)

/-- **`F_i ⋔ P_i` on `S_{p,n}`**: the pulled equation of `P_i` has contact length one on the stalk of
`F_i` at its point of `F_i ∩ P_i`. -/
theorem fiberStrict_contact_length (x : fiberStrict (q + 1) n a i)
    (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i) :
    Module.length ((fiberStrict (q + 1) n a i).presheaf.stalk x)
      ((fiberStrict (q + 1) n a i).presheaf.stalk x ⧸
        Ideal.span {fiberContactGermS q n a i x hP hx}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (fiberContactStalkEquivS q n a i x hP hx), fiberContactGermS, RingEquiv.apply_symm_apply]
  exact fiberClosure_exceptional_contact_length (translatedInitial (q + 1) (a i)) q

end Fiber

/-! ## The strict graph -/

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)] (i : Fin n)

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
theorem graph_mem_range_snd (x : graphStrict (q + 1) n a)
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    x ∈ Set.range (pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).base := by
  rw [Scheme.Pullback.range_snd]
  change (graphStrictι (q + 1) n a).base x ∈ Set.range (isoPreimage q n a i).ι.base
  rw [Scheme.Opens.range_ι]
  exact hx

/-- The point of `B ×_S V` over a point of `B` lying over `V`. -/
def graphRestrictPoint (x : graphStrict (q + 1) n a)
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) : graphRestrict q n a i :=
  Classical.choose (graph_mem_range_snd q n a i x hx)

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
theorem graphRestrictPoint_snd (x : graphStrict (q + 1) n a)
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    (pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).base
      (graphRestrictPoint q n a i x hx) = x :=
  Classical.choose_spec (graph_mem_range_snd q n a i x hx)

/-- The image point on the tower closure. -/
def graphTowerPoint (x' : graphRestrict q n a i) :
    liftedGraphClosure (translatedInitial (q + 1) (a i)) (q + 1) 0 :=
  (pullback.snd (isoMap q n a i) (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)).base
    ((graphRestrictIso q n a i).hom.base x')

theorem closureInclusion_graphTowerPoint (x' : graphRestrict q n a i) :
    (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base (graphTowerPoint q n a i x') =
      (towerProjection (q + 1) n a i).base
        ((graphStrictι (q + 1) n a).base
          ((pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).base x')) := by
  have h1 := congrArg (fun h => h.base ((graphRestrictIso q n a i).hom.base x'))
    (pullback.condition (f := isoMap q n a i)
      (g := closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0))
  simp only [Scheme.comp_base_apply] at h1
  have h2 := congrArg (fun h => h.base x') (graphRestrictIso_hom_fst q n a i)
  simp only [Scheme.comp_base_apply] at h2
  have h3 := congrArg (fun h => h.base x')
    (pullback.condition (f := (isoPreimage q n a i).ι) (g := graphStrictι (q + 1) n a))
  simp only [Scheme.comp_base_apply] at h3
  change (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base
    ((pullback.snd (isoMap q n a i) (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)).base
      ((graphRestrictIso q n a i).hom.base x')) = _
  rw [← h1, h2, isoMap_base, ← Scheme.Opens.ι_base_apply, h3]

/-- The stalk of `B` at a point over `V` is the stalk of the tower closure at the image point. -/
def graphStalkEquiv (x' : graphRestrict q n a i) :
    (graphStrict (q + 1) n a).presheaf.stalk
        ((pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).base x') ≃+*
      (liftedGraphClosure (translatedInitial (q + 1) (a i)) (q + 1) 0).presheaf.stalk
        (graphTowerPoint q n a i x') :=
  (asIso ((pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)).stalkMap x') ≪≫
    (asIso ((graphRestrictIso q n a i).hom.stalkMap x')).symm ≪≫
      (asIso ((pullback.snd (isoMap q n a i)
        (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)).stalkMap
          ((graphRestrictIso q n a i).hom.base x'))).symm).commRingCatIsoToRingEquiv

/-- Over the single point of `B ∩ P_i`, the image point is the contact point of the tower closure. -/
theorem graphTowerPoint_eq_contact (x : graphStrict (q + 1) n a)
    (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    graphTowerPoint q n a i (graphRestrictPoint q n a i x hx) =
      closureContactPoint (translatedInitial (q + 1) (a i)) (q + 1) 0 := by
  apply Scheme.IdealSheafData.gluedTo_injective
    (liftedGraphClosureIdeal (translatedInitial (q + 1) (a i)) (q + 1) 0)
  change (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base _ =
    (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0).base _
  rw [closureInclusion_graphTowerPoint, graphRestrictPoint_snd]
  exact graphStrict_newest_projection q n a i _ ⟨⟨x, rfl⟩, hP⟩

/-- The stalk of `B` at the point of `B ∩ P_i`, identified with the accepted contact stalk. -/
def graphContactStalkEquivS (x : graphStrict (q + 1) n a)
    (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    (graphStrict (q + 1) n a).presheaf.stalk x ≃+*
      closureContactStalk (translatedInitial (q + 1) (a i)) (q + 1) 0 :=
  ((graphStrict (q + 1) n a).presheaf.stalkCongr
      (Inseparable.of_eq (graphRestrictPoint_snd q n a i x hx).symm)).commRingCatIsoToRingEquiv.trans
    ((graphStalkEquiv q n a i (graphRestrictPoint q n a i x hx)).trans
      ((liftedGraphClosure (translatedInitial (q + 1) (a i)) (q + 1) 0).presheaf.stalkCongr
        (Inseparable.of_eq (graphTowerPoint_eq_contact q n a i x hP hx))).commRingCatIsoToRingEquiv)

/-- The pulled equation of `P_i` as an element of the stalk of `B`. -/
def graphContactGermS (x : graphStrict (q + 1) n a)
    (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    (graphStrict (q + 1) n a).presheaf.stalk x :=
  (graphContactStalkEquivS q n a i x hP hx).symm
    (closureContactGerm (translatedInitial (q + 1) (a i)) q 0 chartU)

/-- **`B ⋔ P_i` on `S_{p,n}`**: the pulled equation of `P_i` has contact length one on the stalk of `B`
at its point of `B ∩ P_i`. -/
theorem graphStrict_contact_length (x : graphStrict (q + 1) n a)
    (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
    (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i) :
    Module.length ((graphStrict (q + 1) n a).presheaf.stalk x)
      ((graphStrict (q + 1) n a).presheaf.stalk x ⧸
        Ideal.span {graphContactGermS q n a i x hP hx}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (graphContactStalkEquivS q n a i x hP hx), graphContactGermS, RingEquiv.apply_symm_apply]
  exact closure_terminal_exceptional_contact_length (translatedInitial (q + 1) (a i)) q

end Graph

end KltDP.Examples.FrobeniusTransversalContactsStrict

namespace KltDP.Examples

open KltDP.Geometry FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphNewest FrobeniusIncidenceSPn FrobeniusTransversalContactsStrict

/-- Bundle: on `S_{p,n}` itself, for every `i`, `B ∩ P_i` is a single point of `B` at which the pulled
equation of `P_i` has contact length one on the stalk of `B`, and likewise for `F_i ∩ P_i` on the stalk
of `F_i`. -/
theorem sPn_transversal_contacts' (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) :
    (∀ i : Fin n, ∃ (x : graphStrict (q + 1) n a)
      (hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
      (hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i),
      Set.range (graphStrictι (q + 1) n a).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) = {(graphStrictι (q + 1) n a).base x} ∧
      Module.length ((graphStrict (q + 1) n a).presheaf.stalk x)
        ((graphStrict (q + 1) n a).presheaf.stalk x ⧸
          Ideal.span {graphContactGermS q n a i x hP hx}) = 1) ∧
    (∀ i : Fin n, ∃ (x : fiberStrict (q + 1) n a i)
      (hP : (fiberStrictι (q + 1) n a i).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit))
      (hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i),
      Set.range (fiberStrictι (q + 1) n a i).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) = {(fiberStrictι (q + 1) n a i).base x} ∧
      Module.length ((fiberStrict (q + 1) n a i).presheaf.stalk x)
        ((fiberStrict (q + 1) n a i).presheaf.stalk x ⧸
          Ideal.span {fiberContactGermS q n a i x hP hx}) = 1) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨y, hy⟩ := graphStrict_inter_newest_eq_singleton q n a ha i
    have hmem : y ∈ Set.range (graphStrictι (q + 1) n a).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hy]
      exact Set.mem_singleton y
    obtain ⟨x, hxy⟩ := hmem.1
    have hP : (graphStrictι (q + 1) n a).base x ∈ exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hxy]
      exact hmem.2
    have hx : (graphStrictι (q + 1) n a).base x ∈ isoPreimage q n a i :=
      newest_mem_isoPreimage q n a ha i _ hP
    exact ⟨x, hP, hx, by rw [hxy]; exact hy, graphStrict_contact_length q n a i x hP hx⟩
  · obtain ⟨y, hy⟩ := fiberStrict_inter_newest_eq_singleton q n a ha i
    have hmem : y ∈ Set.range (fiberStrictι (q + 1) n a i).base ∩
        exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hy]
      exact Set.mem_singleton y
    obtain ⟨x, hxy⟩ := hmem.1
    have hP : (fiberStrictι (q + 1) n a i).base x ∈
        exceptionalSupport q n a i (Sum.inr PUnit.unit) := by
      rw [hxy]
      exact hmem.2
    have hx : (fiberStrictι (q + 1) n a i).base x ∈ isoPreimage q n a i :=
      newest_mem_isoPreimage q n a ha i _ hP
    exact ⟨x, hP, hx, by rw [hxy]; exact hy, fiberStrict_contact_length q n a i x hP hx⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_transversal_contacts'_universe_check (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := sPn_transversal_contacts'.{u} k q n a ha
  trivial

end KltDP.Examples
