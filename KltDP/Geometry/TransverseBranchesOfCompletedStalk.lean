import KltDP.RingTheory.CotangentOfNodalCompletion
import KltDP.Geometry.RationalTreePicardLeafNodeChart
import KltDP.Geometry.Surface

/-!
# Transverse component branches from the completed-stalk node model

BRIEF26 (Task 2 of BRIEF18), scheme-level part. Let `X` be a Noetherian, locally Noetherian scheme
with structure map `f : X ⟶ Spec k`, and `q` a point whose completed local ring is the ordinary
double point model, `e : Ô_{X, q} ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)` (an explicit `k`-algebra isomorphism with
the accepted `ordinaryDoublePointModel k`, with the scalars of `stalkAlgebra f q`).

* **`finrank_cotangentSpace_eq_two_of_completedStalk`** (unconditional): the cotangent space of
  `O_{X, q}` is two-dimensional, by the ring-theoretic `NodalCompletion.finrank_cotangentSpace_eq_two`
  (the stalk is Noetherian: the accepted `isNoetherianRing_stalk_of_isLocallyNoetherian`).
* **`hasTransverseComponentBranches_of_completedStalk_of_branchGerms`**: `X` has transverse
  component branches (the nodality hypothesis of `lem:tree-picard`) provided at every point `q` where a
  component `C` meets the other components there are **branch germs** (`BranchGermsAt`): germs
  `w 0`, `w 1` of the stalk ideals of `C` and of `Z_{Cᶜ}` whose completions are multiples of `x̄`, `ȳ`
  and which are not in `m_q ^ 2`. Their cotangent classes are independent
  (`NodalCompletion.linearIndependent_of_model`).

**What is not proved here** (recorded in `LEMMA22_PROGRESS.md`, Task 26): that the branch germs
exist, i.e. that the completed branch ideals `(I_C)_q Ô` and `(I_{Cᶜ})_q Ô` are exactly `(x̄)` and
`(ȳ)`; the unconditional export `hasTransverseComponentBranches_of_completedStalk` is therefore
still open. The intended argument (`(I_C)_q · (I_{Cᶜ})_q = 0` in the reduced stalk, so the two
completed ideals annihilate each other and lie in `(x̄)`, `(ȳ)` by the fibre-product description
`k⟦x, y⟧ ⧸ (x y) ≅ k⟦x⟧ ×_k k⟦y⟧`; a nonzerodivisor argument through the flatness of the completion
then forces `(I_C)_q ⊄ m_q ^ 2`) needs the model's ideal theory and the flatness transport, listed
there with the exact sublemmas.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

open KltDP.Geometry.IntrinsicNodal KltDP.RingTheory.OrdinaryDoublePointModel

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of k))

omit [NoetherianSpace X] in
/-- **The cotangent space at a point with nodal completed stalk is two-dimensional.** -/
theorem finrank_cotangentSpace_eq_two_of_completedStalk (q : X)
    (e : letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k) :
    Module.finrank (ResidueField (X.presheaf.stalk q)) (CotangentSpace (X.presheaf.stalk q)) = 2 := by
  letI := stalkAlgebra f q
  haveI : IsNoetherianRing (X.presheaf.stalk q) :=
    KltDP.Geometry.isNoetherianRing_stalk_of_isLocallyNoetherian X q
  exact KltDP.RingTheory.NodalCompletion.finrank_cotangentSpace_eq_two e

/-- **Branch germs in completed-stalk form** at a point `q` of the component `C`, on the affine chart
`U`: germs `w 0`, `w 1` of the maximal ideal lying in the stalk ideals of `C` and of `Z_{Cᶜ}`, whose
completions are multiples of `x̄`, `ȳ` under `e`, and which are not in `m_q ^ 2`. -/
def BranchGermsAt (C : ↥(irreducibleComponents X)) (q : X) (U : X.affineOpens) (hq : q ∈ U.1)
    (e : letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k) : Prop :=
  letI := stalkAlgebra f q
  ∃ w : Fin 2 → maximalIdeal (X.presheaf.stalk q),
    (w 0 : X.presheaf.stalk q) ∈
        (componentChartIdeal X {C} U).map (X.presheaf.germ U.1 q hq).hom ∧
    (w 1 : X.presheaf.stalk q) ∈
        (componentChartIdeal X ({C}ᶜ) U).map (X.presheaf.germ U.1 q hq).hom ∧
    ∀ i, (∃ u : ordinaryDoublePointModel k,
        e (algebraMap (X.presheaf.stalk q) (completedStalk X q) (w i : X.presheaf.stalk q)) =
          u * xBar k i) ∧
      (w i : X.presheaf.stalk q) ∉ maximalIdeal (X.presheaf.stalk q) ^ 2

/-- **Transverse component branches from completed-stalk nodes with branch germs.** -/
theorem hasTransverseComponentBranches_of_completedStalk_of_branchGerms
    (e : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) →
      (letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k))
    (hbr : ∀ (C : ↥(irreducibleComponents X)) (q : X) (hqC : q ∈ C.1)
      (hqCc : q ∈ (componentClosedUnion X ({C}ᶜ) : Set X)) (U : X.affineOpens) (hq : q ∈ U.1),
      BranchGermsAt X f C q U hq (e C q hqC hqCc)) :
    HasTransverseComponentBranches X := by
  intro C q hqC hqCc U hq
  letI := stalkAlgebra f q
  haveI : IsNoetherianRing (X.presheaf.stalk q) :=
    KltDP.Geometry.isNoetherianRing_stalk_of_isLocallyNoetherian X q
  obtain ⟨w, hw0, hw1, hw⟩ := hbr C q hqC hqCc U hq
  refine ⟨w, hw0, hw1, KltDP.RingTheory.NodalCompletion.finrank_cotangentSpace_eq_two (e C q hqC hqCc), ?_⟩
  choose c hc hcw using fun i => KltDP.RingTheory.NodalCompletion.exists_const_of_mem_span (e C q hqC hqCc) (w i) i
    (hw i).1.choose (hw i).1.choose_spec (hw i).2
  exact KltDP.RingTheory.NodalCompletion.linearIndependent_of_model (e C q hqC hqCc) w c hc hcw

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀] [IsLocallyNoetherian X₀]
    (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (q : X₀)
    (e : letI := stalkAlgebra f₀ q; completedStalk X₀ q ≃ₐ[k₀] ordinaryDoublePointModel k₀) :
    Module.finrank (ResidueField (X₀.presheaf.stalk q)) (CotangentSpace (X₀.presheaf.stalk q)) = 2 :=
  finrank_cotangentSpace_eq_two_of_completedStalk X₀ f₀ q e

end KltDP.Geometry.RationalTreePicard
