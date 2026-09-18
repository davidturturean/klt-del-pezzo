import KltDP.Geometry.SurfaceBirationalGraphDominationInput
import KltDP.Geometry.ProperBirationalSurfacePointBlowupDomination
import KltDP.Geometry.SchemePointBlowupSequenceRestriction

/-!
# Point-blowup domination of the original correspondence over X

The separately audited 0AHI use site is applied to the actual proper graph
projection. Composing its factor with the actual graph extension gives the
map to the original model over the original X. The sequence avoids the
original partial map's domain. Its actual inverse on that domain recovers
the original partial map, by cancellation through the graph restriction.

The output source is an actual scheme with an actual point-blowup sequence.
Normality, regularity, and projectivity of that source are not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SurfaceBirationalPointBlowupDomination

/-- Uniqueness of an actual section over an open where the original map is an iso. -/
private theorem section_eq_of_isIso_restrict {G T : Scheme.{u}}
    (p : G ⟶ T) (U : T.Opens) [IsIso (p ∣_ U)]
    (a b : U.toScheme ⟶ G) (ha : a ≫ p = U.ι) (hb : b ≫ p = U.ι) : a = b := by
  let P := isPullback_morphismRestrict p U
  let a' := P.lift (𝟙 _) a (by simpa only [Category.id_comp] using ha.symm)
  let b' := P.lift (𝟙 _) b (by simpa only [Category.id_comp] using hb.symm)
  have hab : a' = b' := by
    apply (cancel_mono (p ∣_ U)).mp
    exact (P.lift_fst _ _ _).trans (P.lift_fst _ _ _).symm
  calc
    a = a' ≫ (p ⁻¹ᵁ U).ι := (P.lift_snd _ _ _).symm
    _ = b' ≫ (p ⁻¹ᵁ U).ι := congrArg (fun z => z ≫ (p ⁻¹ᵁ U).ι) hab
    _ = b := P.lift_snd _ _ _

open SurfaceBirationalGraphDominationInput

variable {k : Type u} [Field k] [IsAlgClosed k] (T : NormalProjectiveSurface k)
  {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
  (t : T.toScheme ⟶ X) (v : V ⟶ X) [IsProper v]
  (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)

/-- The actual original correspondence is dominated by point blowups over X,
avoiding its original domain and agreeing there as actual scheme morphisms. -/
theorem exists_domination_of_regular (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme) (q : Z ⟶ V),
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) Z b ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ Z,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  obtain ⟨Z, b, hb, g, hg⟩ :=
    ProperBirationalSurface.exists_pointBlowup_domination T (projection T t v ht hv)
      (projection_isBirationalScheme T t v ht hv) hreg
  have hbU : SchemePointBlowup.SequenceAway T.toScheme
      ((representative T t v ht hv).domain : Set T.toScheme) Z b :=
    hb.mono (originalDomain_le_targetIsomorphismOpen T t v ht hv)
  letI : IsIso (b ∣_ (representative T t v ht hv).domain) :=
    SchemePointBlowup.SequenceAway.isIso_restrict _ hbU
  let q : Z ⟶ V := g ≫ extension T t v ht hv
  have hq : q ≫ v = b ≫ t := by
    dsimp only [q]
    rw [Category.assoc, extension_comp, ← Category.assoc, hg]
  let j : (representative T t v ht hv).domain.toScheme ⟶ Z :=
    inv (b ∣_ (representative T t v ht hv).domain) ≫
      (b ⁻¹ᵁ (representative T t v ht hv).domain).ι
  have hj : j ≫ b = (representative T t v ht hv).domain.ι := by
    dsimp only [j]
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  letI := projection_restrict_originalDomain_isIso T t v ht hv
  have hjg : j ≫ g = domainLift T t v ht hv := by
    apply section_eq_of_isIso_restrict (projection T t v ht hv)
      (representative T t v ht hv).domain
    · rw [Category.assoc, hg]
      exact hj
    · exact domainLift_projection T t v ht hv
  have hjq : j ≫ q = (representative T t v ht hv).hom := by
    dsimp only [q]
    rw [← Category.assoc, hjg, domainLift_extension]
  exact ⟨Z, b, q, hbU, inferInstance, hq, j, hj, hjq⟩

/-- Smoothness of the original normal surface supplies regularity, retaining
the same original partial map and the same over-X conclusion. -/
theorem exists_domination_of_smooth [IsSmooth T.structureMorphism] :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme) (q : Z ⟶ V),
      SchemePointBlowup.SequenceAway T.toScheme
        ((representative T t v ht hv).domain : Set T.toScheme) Z b ∧
      IsIso (b ∣_ (representative T t v ht hv).domain) ∧
      q ≫ v = b ≫ t ∧
      ∃ j : (representative T t v ht hv).domain.toScheme ⟶ Z,
        j ≫ b = (representative T t v ht hv).domain.ι ∧
        j ≫ q = (representative T t v ht hv).hom := by
  apply exists_domination_of_regular T t v ht hv
  exact SmoothFieldRegularPoints.regularPoint_of_isSmooth_of_isNormalScheme
    T.structureMorphism T.normal (fun x => inferInstance) T.dimension_two.le

end KltDP.Geometry.SurfaceBirationalPointBlowupDomination
