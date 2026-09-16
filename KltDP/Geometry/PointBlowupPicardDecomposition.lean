import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.RationalTreePicardMultidegree

/-!
# The Picard group of a point blowup: the formal decomposition `Pic T ≃ Pic S × ker(res_{T ∖ E})`

BRIEF29, task 3 (F09, step (0) of `laneA1/F09_PICARD_PLAN.md`). For the accepted glued point blowup
`σ = projection j q hclosed : T ⟶ X` of the closed point `x = j.base q`, with `V = puncture j q hclosed`
(`X ∖ {x}`) and `W = σ⁻¹ V` (`T ∖ E`, the accepted `exceptionalComplementOpen`):

* `ι_W ≫ σ = punctureIso.hom ≫ ι_V` (`complementOpen_ι_projection`), so restriction to `W` of a pulled-back
  class is the restriction to `V` transported along the accepted isomorphism `W ≅ V`
  (`restrictComplement_pullback`);
* hence, **whenever restriction `Pic X → Pic V` is bijective** (F09 step (i), taken here as the hypothesis
  `hres`), `ρ := res_V⁻¹ ∘ (punctureIso^*)⁻¹ ∘ res_W` is a retraction of `σ^*` (`retraction_pullback`), and
  a retraction of a homomorphism of commutative groups splits the group (`splitEquiv`):
  **`picardDecomposition hres : T.Pic ≃* X.Pic × ↥(retraction j q hclosed hres).ker`**, with
  `picardDecomposition_apply_fst` (first component `ρ`), `picardDecomposition_symm_apply`
  (`(a, c) ↦ σ^* a * c`) and `ker_retraction : ρ.ker = (restrictComplement j q hclosed).ker`
  (the kernel is the group of classes trivial on `T ∖ E`);
* the class of the exceptional ideal sheaf `O_T(−E)` (accepted `globalCenterFiberIdealLine`) lies in the
  kernel, by the accepted trivialisation `globalCenterFiberComplementFrame` on `T ∖ E`
  (`exceptionalIdealClass_mem_ker`).

The identification of the kernel with `ℤ · [E]` (steps (iii), (iv) of the plan) and the bijectivity of
`Pic X → Pic (X ∖ {x})` for a regular surface (step (i)) are not proved here; the module reduces
`Pic T ≃ Pic S × ℤ` to them. Everything is stated for the accepted general point blowup (any base scheme
`X`, any affine neighbourhood `j`, any closed point with maximal `q`); no surface, regularity or
projectivity hypothesis enters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupPicard

/-! ## A retraction splits a commutative group -/

section Split

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- A homomorphism `s : H →* G` with a retraction `ρ` (`ρ ∘ s = id`) splits `G` as `H × ker ρ`:
`g ↦ (ρ g, g · s (ρ g)⁻¹)`, with inverse `(a, c) ↦ s a · c`. -/
def splitEquiv (s : H →* G) (ρ : G →* H) (hρ : ∀ a, ρ (s a) = a) : G ≃* H × ρ.ker where
  toFun g := (ρ g, ⟨g * (s (ρ g))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, mul_inv_cancel]⟩)
  invFun p := s p.1 * p.2
  left_inv g := by
    show s (ρ g) * (g * (s (ρ g))⁻¹) = g
    rw [mul_comm g, ← mul_assoc, mul_inv_cancel, one_mul]
  right_inv p := by
    obtain ⟨a, c, hc⟩ := p
    have hc' : ρ c = 1 := hc
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show ρ (s a * c) = a
      rw [map_mul, hρ, hc', mul_one]
    · show s a * c * (s (ρ (s a * c)))⁻¹ = c
      rw [map_mul, hρ, hc', mul_one, mul_comm (s a) c, mul_assoc, mul_inv_cancel, mul_one]
  map_mul' g g' := by
    refine Prod.ext (map_mul ρ g g') (Subtype.ext ?_)
    show g * g' * (s (ρ (g * g')))⁻¹ = g * (s (ρ g))⁻¹ * (g' * (s (ρ g'))⁻¹)
    rw [map_mul, map_mul, mul_inv, mul_mul_mul_comm]

theorem splitEquiv_apply_fst (s : H →* G) (ρ : G →* H) (hρ : ∀ a, ρ (s a) = a) (g : G) :
    (splitEquiv s ρ hρ g).1 = ρ g := rfl

theorem splitEquiv_symm_apply (s : H →* G) (ρ : G →* H) (hρ : ∀ a, ρ (s a) = a)
    (p : H × ρ.ker) : (splitEquiv s ρ hρ).symm p = s p.1 * p.2 := rfl

end Split

/-! ## Pullback along an isomorphism of schemes -/

/-- Pullback of Picard classes along an isomorphism of schemes, as a group isomorphism. -/
def pullbackEquivOfIso {Y Z : Scheme.{u}} (g : Y ≅ Z) : Z.Pic ≃* Y.Pic where
  toFun := schemePicardPullbackHom g.hom
  invFun := schemePicardPullbackHom g.inv
  left_inv c := by
    rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp, Iso.inv_hom_id,
      schemePicardPullbackHom_id, MonoidHom.id_apply]
  right_inv c := by
    rw [← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp, Iso.hom_inv_id,
      schemePicardPullbackHom_id, MonoidHom.id_apply]
  map_mul' := map_mul _

theorem pullbackEquivOfIso_apply {Y Z : Scheme.{u}} (g : Y ≅ Z) (c : Z.Pic) :
    pullbackEquivOfIso g c = schemePicardPullbackHom g.hom c := rfl

/-! ## The point blowup -/

open KltDP.Geometry.PointBlowupGluing AffineBlowup

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))

/-- Pullback of Picard classes along the blowdown `σ : T ⟶ X`. -/
def pullbackHom : X.Pic →* (scheme j q hclosed).Pic :=
  schemePicardPullbackHom (projection j q hclosed)

/-- Restriction of Picard classes of `X` to the puncture `X ∖ {x}`. -/
def restrictPuncture : X.Pic →* (puncture j q hclosed).toScheme.Pic :=
  schemePicardPullbackHom (puncture j q hclosed).ι

/-- Restriction of Picard classes of the blowup to the complement `T ∖ E = σ⁻¹(X ∖ {x})`. -/
def restrictComplement :
    (scheme j q hclosed).Pic →* (projection j q hclosed ⁻¹ᵁ puncture j q hclosed).toScheme.Pic :=
  schemePicardPullbackHom (projection j q hclosed ⁻¹ᵁ puncture j q hclosed).ι

/-- The complement `T ∖ E` maps to the puncture through the accepted isomorphism. -/
theorem complementOpen_ι_projection :
    (projection j q hclosed ⁻¹ᵁ puncture j q hclosed).ι ≫ projection j q hclosed =
      (punctureIso j q hclosed).hom ≫ (puncture j q hclosed).ι := by
  rw [punctureIso_hom, morphismRestrict_ι]

/-- Restricting a pulled-back class to `T ∖ E` is restricting to `X ∖ {x}` and transporting along
`T ∖ E ≅ X ∖ {x}`. -/
theorem restrictComplement_pullback (c : X.Pic) :
    restrictComplement j q hclosed (pullbackHom j q hclosed c) =
      pullbackEquivOfIso (punctureIso j q hclosed) (restrictPuncture j q hclosed c) := by
  rw [restrictComplement, pullbackHom, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
    complementOpen_ι_projection, schemePicardPullbackHom_comp, MonoidHom.comp_apply,
    pullbackEquivOfIso_apply, restrictPuncture]

variable (hres : Function.Bijective (restrictPuncture j q hclosed))

/-- The retraction `Pic T → Pic X` of `σ^*`: restrict to `T ∖ E`, transport to `X ∖ {x}`, and extend
across `x` by the (hypothetical) bijectivity of the restriction `Pic X → Pic (X ∖ {x})`. -/
def retraction : (scheme j q hclosed).Pic →* X.Pic :=
  (MulEquiv.ofBijective (restrictPuncture j q hclosed) hres).symm.toMonoidHom.comp
    ((pullbackEquivOfIso (punctureIso j q hclosed)).symm.toMonoidHom.comp
      (restrictComplement j q hclosed))

theorem retraction_pullback (c : X.Pic) :
    retraction j q hclosed hres (pullbackHom j q hclosed c) = c := by
  rw [retraction, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, restrictComplement_pullback, MulEquiv.symm_apply_apply]
  exact (MulEquiv.ofBijective (restrictPuncture j q hclosed) hres).symm_apply_apply c

theorem retraction_eq_one_of_mem_ker {c : (scheme j q hclosed).Pic}
    (hc : c ∈ (restrictComplement j q hclosed).ker) : retraction j q hclosed hres c = 1 := by
  rw [MonoidHom.mem_ker] at hc
  rw [retraction, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, hc, map_one, map_one]

/-- **The formal Picard decomposition of a point blowup**: if restriction `Pic X → Pic (X ∖ {x})` is
bijective, then `Pic T ≃* Pic X × ker (Pic T → Pic (T ∖ E))`, the first component being the retraction
of `σ^*` and the inverse `(a, c) ↦ σ^* a · c`. -/
def picardDecomposition :
    (scheme j q hclosed).Pic ≃* X.Pic × ↥(retraction j q hclosed hres).ker :=
  splitEquiv (pullbackHom j q hclosed) (retraction j q hclosed hres)
    (retraction_pullback j q hclosed hres)

theorem picardDecomposition_apply_fst (c : (scheme j q hclosed).Pic) :
    (picardDecomposition j q hclosed hres c).1 = retraction j q hclosed hres c := rfl

theorem picardDecomposition_symm_apply (p : X.Pic × ↥(retraction j q hclosed hres).ker) :
    (picardDecomposition j q hclosed hres).symm p = pullbackHom j q hclosed p.1 * p.2 := rfl

/-- The kernel of the retraction is the kernel of restriction to `T ∖ E`. -/
theorem ker_retraction :
    (retraction j q hclosed hres).ker = (restrictComplement j q hclosed).ker := by
  ext c
  constructor
  · intro hc
    rw [MonoidHom.mem_ker] at hc ⊢
    have h := congrArg (MulEquiv.ofBijective (restrictPuncture j q hclosed) hres) hc
    rw [retraction, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at h
    have h' := congrArg (pullbackEquivOfIso (punctureIso j q hclosed)) h
    rwa [MulEquiv.apply_symm_apply, map_one] at h'
  · exact retraction_eq_one_of_mem_ker j q hclosed hres

/-! ## The exceptional class lies in the kernel -/

open SchemeModuleRestriction in
/-- The class of the exceptional ideal sheaf `O_T(−E)` restricts trivially to `T ∖ E`. -/
theorem exceptionalIdealClass_mem_ker :
    (globalCenterFiberIdealLine j q hclosed).toPic ∈ (restrictComplement j q hclosed).ker := by
  rw [MonoidHom.mem_ker, restrictComplement, schemePicardPullbackHom_toPic,
    KltDP.Geometry.RationalTreePicard.toPic_eq_one_iff_iso_unit]
  exact ⟨(globalCenterFiberComplementFrame j q hclosed).symm⟩

/-- Universe check at universe `0`. -/
example {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} (j₀ : Spec (CommRingCat.of R₀) ⟶ X₀)
    [IsOpenImmersion j₀] (q₀ : PrimeSpectrum R₀) [q₀.asIdeal.IsMaximal]
    (hclosed₀ : IsClosed ({j₀.base q₀} : Set X₀))
    (hres₀ : Function.Bijective (restrictPuncture j₀ q₀ hclosed₀)) :
    (scheme j₀ q₀ hclosed₀).Pic ≃* X₀.Pic × ↥(retraction j₀ q₀ hclosed₀ hres₀).ker :=
  picardDecomposition j₀ q₀ hclosed₀ hres₀

end KltDP.Geometry.PointBlowupPicard
