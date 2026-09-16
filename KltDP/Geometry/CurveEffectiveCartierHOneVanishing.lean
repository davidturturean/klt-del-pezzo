import KltDP.Geometry.CurveEffectiveCartierSequence
import KltDP.Geometry.SchemeDisjointCoverSections
import KltDP.Compatibility.GrothendieckVanishing.FlasqueVanishing

/-!
# Vanishing of the higher cohomology of `i_*O_E` for a finite scheme with closed points

On a scheme `S` with finitely many points, all closed, the topology is discrete, so every open
`U ≤ V` has an open complement `W = V \ U` in `V`; the sheaf condition for the disjoint cover
`{U, W}` of `V` makes every restriction `Γ(S, V) → Γ(S, U)` surjective. Hence the pushforward of
the structure module along any morphism `i : S → X` is a flasque sheaf of abelian groups on `X`,
and its cohomology vanishes in positive degrees (accepted `sheafH_subsingleton_of_flasque`).

Applied to the closed immersion of the zero scheme `E` of an effective Cartier divisor, this is the
input `hone : H¹(C, i_*O_E) = 0` of `lineDegree_neg_cartier_of_sequence`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section DisjointRestriction

variable (Z : Scheme.{u})

/-- Gluing over a two-element cover with disjoint members. -/
theorem exists_glue_bool (F : Bool → Z.Opens) (hbot : F false ⊓ F true = ⊥) (V : Z.Opens)
    (hle : ∀ b, F b ≤ V) (hcover : V ≤ iSup F) (sf : ∀ b, Γ(Z, F b)) :
    ∃ t : Γ(Z, V), ∀ b, Z.presheaf.map (homOfLE (hle b)).op t = sf b := by
  have hbot' : ∀ i j : Bool, i ≠ j → F i ⊓ F j = ⊥ := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact hbot
    · exact (inf_comm (F true) (F false)).trans hbot
    · exact absurd rfl hij
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.val F sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Subsingleton.elim (Opens.infLELeft (F i) (F i)) (Opens.infLERight (F i) (F i))]
    · exact @Subsingleton.elim _ (sections_subsingleton_of_eq_bot Z (hbot' i j hij)) _ _
  obtain ⟨t, ht, -⟩ :=
    Z.sheaf.existsUnique_gluing' F V (fun b => homOfLE (hle b)) hcover sf hcompat
  exact ⟨t, ht⟩

/-- The two-element family `{W, U}` indexed by `Bool`. -/
def boolFamily (U W : Z.Opens) : Bool → Z.Opens := fun b => Bool.rec W U b

theorem boolFamily_false (U W : Z.Opens) : boolFamily Z U W false = W := rfl

theorem boolFamily_true (U W : Z.Opens) : boolFamily Z U W true = U := rfl

/-- Sections over the two-element family. -/
def boolSections {U W : Z.Opens} (sU : Γ(Z, U)) (sW : Γ(Z, W)) :
    ∀ b : Bool, Γ(Z, boolFamily Z U W b) :=
  fun b => Bool.rec (motive := fun b => Γ(Z, boolFamily Z U W b)) sW sU b

theorem boolSections_true {U W : Z.Opens} (sU : Γ(Z, U)) (sW : Γ(Z, W)) :
    boolSections Z sU sW true = sU := rfl

/-- Gluing over the disjoint cover `{U, W}` of `V`: restriction from `V` to `U` is surjective. -/
theorem restriction_surjective_of_disjoint_cover {U V W : Z.Opens}
    (hUW : U ⊓ W = ⊥) (hU : U ≤ V) (hW : W ≤ V) (hV : V ≤ U ⊔ W) (j : U ⟶ V) :
    Function.Surjective (Z.presheaf.map j.op) := by
  intro s
  have hbot : boolFamily Z U W false ⊓ boolFamily Z U W true = ⊥ := by
    rw [boolFamily_false, boolFamily_true, inf_comm]
    exact hUW
  have hle : ∀ b : Bool, boolFamily Z U W b ≤ V := by
    intro b
    cases b
    · rw [boolFamily_false]
      exact hW
    · rw [boolFamily_true]
      exact hU
  have hcover : V ≤ iSup (boolFamily Z U W) := by
    intro x hx
    refine Opens.mem_iSup.mpr ?_
    by_cases hxU : x ∈ U
    · exact ⟨true, by rw [boolFamily_true]; exact hxU⟩
    · have hx' : x ∈ ((U ⊔ W : Z.Opens) : Set Z) := hV hx
      rw [Opens.coe_sup] at hx'
      rcases hx' with hx' | hx'
      · exact absurd hx' hxU
      · exact ⟨false, by rw [boolFamily_false]; exact hx'⟩
  obtain ⟨t, ht⟩ := exists_glue_bool Z (boolFamily Z U W) hbot V hle hcover
    (boolSections Z s (1 : Γ(Z, W)))
  refine ⟨t, ?_⟩
  have ht' := ht true
  rw [boolSections_true] at ht'
  exact (congrArg (fun a : op V ⟶ op U => Z.presheaf.map a t)
    (Subsingleton.elim j.op (homOfLE (hle true)).op)).trans ht'

end DisjointRestriction

section FiniteScheme

variable (S : Scheme.{u})

/-- On a finite scheme with closed points every restriction map is surjective. -/
theorem restriction_surjective_of_finite_of_isClosed_singleton [Finite S]
    (hT1 : ∀ x : S, IsClosed ({x} : Set S)) {U V : S.Opens} (j : U ⟶ V) :
    Function.Surjective (S.presheaf.map j.op) := by
  haveI : DiscreteTopology S := DiscreteTopology.of_finite_of_isClosed_singleton hT1
  obtain ⟨W, hW⟩ : ∃ W : S.Opens, (W : Set S) = (V : Set S) \ (U : Set S) :=
    ⟨⟨(V : Set S) \ (U : Set S), isOpen_discrete _⟩, rfl⟩
  have hUW : U ⊓ W = ⊥ := by
    apply Opens.ext
    rw [Opens.coe_inf, Opens.coe_bot, hW]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and,
      not_not]
    intro hxU _
    exact hxU
  have hWV : W ≤ V := by
    intro x hx
    rw [hW] at hx
    exact hx.1
  have hV : V ≤ U ⊔ W := by
    intro x hx
    rw [Opens.coe_sup]
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      rw [hW]
      exact ⟨hx, hxU⟩
  exact restriction_surjective_of_disjoint_cover S hUW j.le hWV hV j

variable {S} {X : Scheme.{u}}

/-- The pushforward of the structure module of a finite scheme with closed points is flasque. -/
theorem pushforwardUnit_isFlasque_of_finite (i : S ⟶ X) [Finite S]
    (hT1 : ∀ x : S, IsClosed ({x} : Set S)) :
    IsFlasqueSheaf ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((schemeModulePushforward i).obj (_root_.SheafOfModules.unit S.ringCatSheaf))) := by
  intro U V j
  apply (AddCommGrp.epi_iff_surjective _).mpr
  change Function.Surjective (S.presheaf.map ((Opens.map i.base).map j).op)
  exact restriction_surjective_of_finite_of_isClosed_singleton S hT1 ((Opens.map i.base).map j)

/-- **Positive-degree cohomology of `i_*O_S` vanishes** for a finite scheme `S` with closed points. -/
theorem pushforwardUnit_cohomology_succ_subsingleton (i : S ⟶ X) [Finite S]
    (hT1 : ∀ x : S, IsClosed ({x} : Set S)) (n : ℕ) :
    Subsingleton (ModuleCohomology.H
      ((schemeModulePushforward i).obj (_root_.SheafOfModules.unit S.ringCatSheaf)) (n + 1)) :=
  sheafH_subsingleton_of_flasque (X : TopCat.{u})
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj
      ((schemeModulePushforward i).obj (_root_.SheafOfModules.unit S.ringCatSheaf)))
    (pushforwardUnit_isFlasque_of_finite i hT1) n

end FiniteScheme

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (E : CartierDivisor C.toScheme) (hE : HasRegularCartierEquations C.toScheme E)

/-- `H¹(C, i_*O_E) = 0` once the zero scheme `E` is finite with closed points. -/
theorem divisorStructurePushforward_hOne_subsingleton [Finite (effectiveCartierScheme C.toScheme E hE)]
    (hT1 : ∀ x : effectiveCartierScheme C.toScheme E hE, IsClosed ({x} : Set _)) :
    Subsingleton (H (C.divisorStructurePushforward E hE) 1) :=
  pushforwardUnit_cohomology_succ_subsingleton (effectiveCartierInclusion C.toScheme E hE) hT1 0

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
