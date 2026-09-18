import KltDP.Geometry.DisjointCurveContractionTransport
import KltDP.Literature.ResolutionLiterals

/-!
# Successive blowdowns of an actual finite disjoint minus-one family

Induction contracts one original curve, transports every disjoint curve
through the actual puncture isomorphism, and repeats on the actual target.
The existing point-blowup sequence retains the literal composite. Every
original family member is contracted, while all original curves disjoint
from the family retain their curve schemes and self-intersections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- The finite sequence uses only ordinary single-curve contraction existence.
No finite-family contraction or transport property is assumed. -/
theorem exists_contract_disjoint_fin
    {k : Type u} [Field k] [IsAlgClosed k]
    (hCa : KltDP.Literature.Stacks.CastelnuovoContractionLiteral k) (n : ℕ) :
    ∀ (S : NormalProjectiveSurface k)
      (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (C : Fin n → S.PrimeCurve),
      (∀ i, IsMinusOneCurve hS (C i)) →
      Pairwise (fun i j => Disjoint (C i : Set S.toScheme) (C j : Set S.toScheme)) →
      ∃ (T : NormalProjectiveSurface k)
        (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (f : S.toScheme ⟶ T.toScheme),
        IsPointBlowupSequence S T f ∧ (∀ i, IsExceptionalCurve f (C i)) ∧
        ∀ D : S.PrimeCurve, (∀ i, Disjoint (D : Set S.toScheme) (C i : Set S.toScheme)) →
          ∃ D' : T.PrimeCurve, f.base '' (D : Set S.toScheme) = (D' : Set T.toScheme) ∧
            ∃ e : D'.toScheme ≅ D.toScheme,
              e.hom ≫ (D.inclusion ≫ f) = D'.inclusion ∧
              e.hom ≫ D.toSpec = D'.toSpec ∧
              D'.selfIntersectionNumber hT = D.selfIntersectionNumber hS := by
  induction n with
  | zero =>
      intro S hS C hminus hpair
      refine ⟨S, hS, 𝟙 S.toScheme, .of_isIso _ inferInstance (by simp), ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro D hD
        refine ⟨D, ?_, Iso.refl _, ?_, ?_, rfl⟩ <;> simp
  | succ n ih =>
      intro S hS C hminus hpair
      obtain ⟨S', b, hb⟩ := hCa.exists_contraction S hS (C 0) (hminus 0)
      obtain ⟨F, hF, hFdis⟩ := hb.exists_disjointCurveTransport hS
      let tail (i : Fin n) :
          {D : S.PrimeCurve // Disjoint (D : Set S.toScheme) (C 0 : Set S.toScheme)} :=
        ⟨C i.succ, @hpair i.succ 0 (Fin.succ_ne_zero i)⟩
      let C' : Fin n → S'.PrimeCurve := fun i => F (tail i)
      have hminus' (i : Fin n) : IsMinusOneCurve hb.regular (C' i) := by
        obtain ⟨-, e, he, hover, hsquare⟩ := hF (tail i)
        obtain ⟨eP, heP⟩ := (hminus i.succ).isoProjectiveLine
        refine ⟨⟨e ≪≫ eP, ?_⟩, ?_⟩
        · rw [Iso.trans_hom, Category.assoc, heP, hover]
        · exact hsquare.trans (hminus i.succ).selfIntersection
      have hpair' : Pairwise (fun i j =>
          Disjoint (C' i : Set S'.toScheme) (C' j : Set S'.toScheme)) := by
        intro i j hij
        exact hFdis (tail i) (tail j)
          (@hpair i.succ j.succ (fun h => hij (Fin.succ_inj.mp h)))
      obtain ⟨T, hT, g, hseq, hcontract, hpreserve⟩ :=
        ih S' hb.regular C' hminus' hpair'
      obtain ⟨z, hz, hzero, hdim, hbl⟩ := hb.center
      refine ⟨T, hT, b ≫ g, .step b g z hbl hseq, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · refine ⟨g.base z, ?_⟩
          change (g.base ∘ b.base) '' (C 0 : Set S.toScheme) = {g.base z}
          simpa only [Set.image_image, Set.image_singleton, Function.comp_def] using
            congrArg (fun A : Set S'.toScheme => g.base '' A) hzero
        · obtain ⟨t, ht⟩ := hcontract j
          refine ⟨t, ?_⟩
          change (g.base ∘ b.base) '' (C j.succ : Set S.toScheme) = {t}
          have hh := (congrArg (fun A : Set S'.toScheme => g.base '' A)
            (hF (tail j)).1).trans ht
          simpa only [Set.image_image, Function.comp_def] using hh
      · intro D hD
        let d : {D : S.PrimeCurve //
            Disjoint (D : Set S.toScheme) (C 0 : Set S.toScheme)} := ⟨D, hD 0⟩
        obtain ⟨himD, eD, hmapD, hbaseD, hsquareD⟩ := hF d
        have hD' : ∀ i, Disjoint (F d : Set S'.toScheme) (C' i : Set S'.toScheme) :=
          fun i => hFdis d (tail i) (hD i.succ)
        obtain ⟨D', himD', eD', hmapD', hbaseD', hsquareD'⟩ := hpreserve (F d) hD'
        refine ⟨D', ?_, eD' ≪≫ eD, ?_, ?_, hsquareD'.trans hsquareD⟩
        · change (g.base ∘ b.base) '' (D : Set S.toScheme) = (D' : Set T.toScheme)
          have hh := (congrArg (fun A : Set S'.toScheme => g.base '' A) himD).trans himD'
          simpa only [Set.image_image, Function.comp_def] using hh
        · calc
            (eD' ≪≫ eD).hom ≫ (D.inclusion ≫ (b ≫ g)) =
                eD'.hom ≫ ((eD.hom ≫ (D.inclusion ≫ b)) ≫ g) := by
              simp only [Iso.trans_hom, Category.assoc]
            _ = eD'.hom ≫ ((F d).inclusion ≫ g) := by rw [hmapD]
            _ = D'.inclusion := hmapD'
        · rw [Iso.trans_hom, Category.assoc, hbaseD, hbaseD']

/-- Arbitrary finite indexing retains the original family under the original composite. -/
theorem exists_contract_disjoint_family
    {k : Type u} [Field k] [IsAlgClosed k]
    (hCa : KltDP.Literature.Stacks.CastelnuovoContractionLiteral k)
    {ι : Type*} [Finite ι] (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (C : ι → S.PrimeCurve)
    (hminus : ∀ i, IsMinusOneCurve hS (C i))
    (hpair : Pairwise (fun i j => Disjoint (C i : Set S.toScheme) (C j : Set S.toScheme))) :
    ∃ (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (f : S.toScheme ⟶ T.toScheme),
      IsPointBlowupSequence S T f ∧ (∀ i, IsExceptionalCurve f (C i)) ∧
      ∀ D : S.PrimeCurve, (∀ i, Disjoint (D : Set S.toScheme) (C i : Set S.toScheme)) →
        ∃ D' : T.PrimeCurve, f.base '' (D : Set S.toScheme) = (D' : Set T.toScheme) ∧
          ∃ e : D'.toScheme ≅ D.toScheme,
            e.hom ≫ (D.inclusion ≫ f) = D'.inclusion ∧
            e.hom ≫ D.toSpec = D'.toSpec ∧
            D'.selfIntersectionNumber hT = D.selfIntersectionNumber hS := by
  classical
  letI := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have hp : Pairwise (fun i j =>
      Disjoint (C (e.symm i) : Set S.toScheme) (C (e.symm j) : Set S.toScheme)) :=
    fun i j hij => @hpair _ _ (fun h => hij (e.symm.injective h))
  obtain ⟨T, hT, f, hseq, hcontract, hpreserve⟩ :=
    exists_contract_disjoint_fin hCa (Fintype.card ι) S hS (fun j => C (e.symm j))
      (fun j => hminus (e.symm j)) hp
  refine ⟨T, hT, f, hseq, ?_, ?_⟩
  · intro i
    simpa only [Equiv.symm_apply_apply] using hcontract (e i)
  · intro D hD
    exact hpreserve D (fun j => hD (e.symm j))

end KltDP.Geometry

#print axioms KltDP.Geometry.exists_contract_disjoint_family
