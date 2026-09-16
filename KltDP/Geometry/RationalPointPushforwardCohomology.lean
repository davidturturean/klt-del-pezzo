import KltDP.Geometry.RationalPointIdealExact
import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Compatibility.GrothendieckVanishing.FlasqueVanishing

/-!
# Cohomology of the actual pushforward of a rational point

The coefficient module is the original pushforward of the unit on `Spec k`.
Its restriction maps are surjective because every section on an open of
the one-point source extends globally. The existing ordinary flasque
vanishing theorem therefore applies to its actual Ext-based cohomology.

For a section of the original structure morphism, the existing H0 comparison
followed by `ΓSpecIso` is linear for the original base-field action. This
proves finite-dimensionality in every degree, vanishing above degree zero,
and Euler characteristic one. No closed-immersion hypothesis is needed,
and no comparison with a replacement skyscraper or cohomology is assumed.

Reuse and source correspondence:
`docs/reuse_sources/rational_point_skyscraper_cohomology/`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalPointPushforward

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section OnePointSource

variable {S X : Scheme.{u}}

/-- The literal pushforward of the source structure module. -/
abbrev unitPushforward (i : S ⟶ X) : X.Modules :=
  (schemeModulePushforward i).obj (_root_.SheafOfModules.unit S.ringCatSheaf)

/-- Every restriction on a scheme with at most one point is surjective. -/
theorem restriction_surjective (S : Scheme.{u}) [Subsingleton S]
    {U V : S.Opens} (j : U ⟶ V) :
    Function.Surjective (S.presheaf.map j.op) := by
  intro s
  obtain ⟨t, ht⟩ := RationalPointIdeal.topRestriction_surjective S U s
  refine ⟨S.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op t, ?_⟩
  calc
    S.presheaf.map j.op
        (S.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op t) =
        S.presheaf.map ((homOfLE (show V ≤ ⊤ from le_top)).op ≫ j.op) t :=
      (ConcreteCategory.congr_hom
        (S.presheaf.map_comp (homOfLE (show V ≤ ⊤ from le_top)).op j.op) t).symm
    _ = S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t := by
      exact congrArg (fun a : op (⊤ : S.Opens) ⟶ op U => S.presheaf.map a t)
        (Subsingleton.elim _ _)
    _ = s := ht

/-- The underlying additive sheaf of the actual pushforward is flasque. -/
theorem unitPushforward_isFlasque (i : S ⟶ X) [Subsingleton S] :
    IsFlasqueSheaf
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (unitPushforward i)) := by
  intro U V j
  apply (AddCommGrp.epi_iff_surjective _).mpr
  change Function.Surjective
    (S.presheaf.map ((Opens.map i.base).map j).op)
  exact restriction_surjective S ((Opens.map i.base).map j)

/-- Positive-degree ordinary cohomology vanishes for the original module. -/
theorem cohomology_succ_subsingleton (i : S ⟶ X) [Subsingleton S] (n : ℕ) :
    Subsingleton (ModuleCohomology.H (unitPushforward i) (n + 1)) :=
  sheafH_subsingleton_of_flasque (X : TopCat.{u})
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (unitPushforward i))
    (unitPushforward_isFlasque i) n

/-- The same actual cohomology has vanishing bound zero. -/
theorem cohomology_subsingleton_of_pos (i : S ⟶ X) [Subsingleton S]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (ModuleCohomology.H (unitPushforward i) n) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact cohomology_succ_subsingleton i n

end OnePointSource

section RationalSection

open ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- On the point, the original base scalar is the usual affine scalar. -/
theorem appTop_baseScalar (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) (r : k) :
    i.appTop (baseFieldToGlobalSections f r) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv r := by
  have h : f.appTop ≫ i.appTop = 𝟙 (Γ(Spec (CommRingCat.of k), ⊤)) := by
    rw [← Scheme.comp_appTop, hi, Scheme.id_appTop]
  exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)

/-- Actual global sections identify with the field for the original action. -/
def sectionsLinearEquiv (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) :
    letI := baseSectionsModule f (unitPushforward i)
    sections (unitPushforward i) ≃ₗ[k] k := by
  letI := baseSectionsModule f (unitPushforward i)
  refine
    { (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := ?_ }
  intro r s
  change Γ(Spec (CommRingCat.of k), ⊤) at s
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (i.appTop (baseFieldToGlobalSections f r) * s) =
    r * (Scheme.ΓSpecIso (CommRingCat.of k)).hom s
  rw [appTop_baseScalar i f hi r, map_mul,
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply]

/-- The original Ext-based H0, with its original base action, is the field. -/
def hZeroLinearEquiv (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) :
    letI := baseModule f (unitPushforward i) 0
    H (unitPushforward i) 0 ≃ₗ[k] k := by
  letI := baseModule f (unitPushforward i) 0
  letI := baseSectionsModule f (unitPushforward i)
  exact (hZeroBaseLinearEquivSections f (unitPushforward i)).trans
    (sectionsLinearEquiv i f hi)

/-- This comparison evaluates the existing H0 section through `ΓSpecIso`. -/
theorem hZeroLinearEquiv_apply (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _)
    (x : H (unitPushforward i) 0) :
    hZeroLinearEquiv i f hi x = (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (hZeroEquivGlobalSections (unitPushforward i) x) := rfl

/-- Every actual cohomology group is finite-dimensional for that same field. -/
theorem cohomology_finiteDimensional (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) (n : ℕ) :
    FiniteDimensional k ((baseFunctor f n).obj (unitPushforward i)) := by
  cases n with
  | zero =>
      letI := baseModule f (unitPushforward i) 0
      exact Module.Finite.equiv (hZeroLinearEquiv i f hi).symm
  | succ n =>
      letI := baseModule f (unitPushforward i) (n + 1)
      letI : Subsingleton ((baseFunctor f (n + 1)).obj (unitPushforward i)) :=
        cohomology_succ_subsingleton i n
      exact Module.Finite.of_surjective
        (0 : k →ₗ[k] H (unitPushforward i) (n + 1))
        (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- The actual H0 dimension is one. -/
theorem cohomologyDimension_zero (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) :
    cohomologyDimension f (unitPushforward i) 0 = 1 := by
  letI := baseModule f (unitPushforward i) 0
  exact (hZeroLinearEquiv i f hi).finrank_eq.trans (Module.finrank_self k)

/-- The dimensions in positive degrees are zero. -/
theorem cohomologyDimension_succ (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    cohomologyDimension f (unitPushforward i) (n + 1) = 0 := by
  letI := cohomology_succ_subsingleton i n
  exact cohomologyDimension_eq_zero_of_subsingleton f (unitPushforward i) (n + 1)

/-- The ordinary finite-dimensional, bounded cohomology has Euler value one. -/
theorem eulerCharacteristic_eq_one (i : Spec (CommRingCat.of k) ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hi : i ≫ f = 𝟙 _) :
    eulerCharacteristic f (unitPushforward i) = 1 := by
  rw [eulerCharacteristic_eq_truncatedEuler f (unitPushforward i) 0
    (cohomology_subsingleton_of_pos i)]
  simp only [truncatedEuler, zero_add, Finset.sum_range_one,
    pow_zero, one_mul, cohomologyDimension_zero i f hi, Nat.cast_one]

end RationalSection

end KltDP.Geometry.RationalPointPushforward
