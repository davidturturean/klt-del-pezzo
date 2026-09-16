import KltDP.Geometry.ExtendAcrossClosedPoint
import KltDP.Geometry.CartierClassOpenRestriction
import KltDP.Geometry.CartierEquationUnits
import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.PointBlowupGluing

/-!
# Cartier divisors and Picard classes trivial off a point with a two-dimensional factorial stalk

BRIEF30, task 3 (F09 step (i), injectivity half). `S` is an integral scheme, `x` a point whose stalk is a
unique factorisation domain of Krull dimension two, and `V` an open containing every point other than `x`
(e.g. `S ∖ {x}` for a closed point). Divisors are the accepted `CartierDivisor S` (global sections of the
Cartier divisor sheaf), restriction to `V` is the accepted `cartierRestrictionHom V.ι`, Picard classes and
their restriction are the accepted `cartierPicardClass` and `schemePicardPullbackHom V.ι`.

* `cartierEquationClassHom_eq_zero_of_eq_zero_off`: a local equation on an affine neighbourhood `U` of `x`
  which is a unit on an open containing `U ∖ {x}` is a unit on `U` (`ExtendAcrossClosedPoint.exists_unit_extension`
  applied to the unit and its inverse).
* `eq_zero_of_map_eq_zero` (sheaf form): a Cartier divisor whose section-restriction to `V` vanishes is zero.
* `cartierEquationClassHom_image_preimage_eq_zero`, `map_eq_zero_of_cartierRestrictionHom_eq_zero`: vanishing
  of the restriction `cartierRestrictionHom f E` along an open immersion `f` gives vanishing of the section
  restriction of `E` to the image of `f` (units are moved along `f.appIso` and the accepted `functionFieldIso`).
* **`eq_zero_of_cartierRestrictionHom_eq_zero`, `cartierRestrictionHom_injective`**: restriction
  `CartierDivisor S → CartierDivisor V` is injective.
* **`cartierPicardClass_eq_one_of_pullback_eq_one`, `schemePicardPullbackHom_injective`**: restriction of
  Picard classes `Pic S → Pic V` is injective. This uses the accepted `cartierPicardClass_surjective` (every
  Picard class of an integral scheme is the class of a Cartier divisor, `CartierPicardComparison`) and the
  accepted kernel description `cartierPicardClass_eq_one_iff`; no surface hypothesis enters.
* Closed-point forms: `schemePicardPullbackHom_compl_injective` (`V = {x}ᶜ`), and
  `puncture_schemePicardPullbackHom_injective` for the accepted point-blowup puncture
  `PointBlowupGluing.puncture j q hclosed` — the injectivity half of the hypothesis `hres` of
  `PointBlowupPicard.picardDecomposition` (where `restrictPuncture j q hclosed` is by definition
  `schemePicardPullbackHom (puncture j q hclosed).ι`).

Not proved here: surjectivity of `Pic S → Pic V` (extension of line bundles across `x`), the other half
of `hres`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierSupportedAtPoint

open KltDP.Geometry.OpenImmersionRational

local instance (T : Scheme.{u}) [IsIntegral T] (y : T) : IsDomain (T.presheaf.stalk y) :=
  ExtendAcrossClosedPoint.stalk_isDomain T y

variable {S : Scheme.{u}} [IsIntegral S]

/-- Restrictions of sections of the Cartier divisor sheaf compose. -/
theorem cartierDivisorSheaf_map_map {U V W : S.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (D : (cartierDivisorSheaf S).val.obj (op U)) :
    (cartierDivisorSheaf S).val.map (homOfLE h₂).op
        ((cartierDivisorSheaf S).val.map (homOfLE h₁).op D) =
      (cartierDivisorSheaf S).val.map (homOfLE (h₂.trans h₁)).op D := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ## Local equations across the point -/

/-- A local equation on an affine neighbourhood `U` of `x` whose class vanishes on an open containing
`U ∖ {x}` has vanishing class on `U`. -/
theorem cartierEquationClassHom_eq_zero_of_eq_zero_off {U : S.Opens} (hU : IsAffineOpen U)
    [Nonempty U] {x : S} (hxU : x ∈ U) [UniqueFactorizationMonoid (S.presheaf.stalk x)]
    (hdim : ringKrullDim (S.presheaf.stalk x) = 2) {W : S.Opens} [Nonempty W]
    (hW : ∀ y ∈ U, y ≠ x → y ∈ W) (f : S.functionFieldˣ)
    (hf : cartierEquationClassHom S W (Additive.ofMul f) = 0) :
    cartierEquationClassHom S U (Additive.ofMul f) = 0 := by
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_zero_iff S W f).mp hf
  obtain ⟨b, hb⟩ := ExtendAcrossClosedPoint.exists_unit_extension hU hxU hdim hW a
  exact (cartierEquationClassHom_eq_zero_iff S U f).mpr ⟨b, hb.trans ha⟩

/-- **A Cartier divisor trivial off `x` is trivial** (section form): if the restriction of `D` to an open
`V` containing every point other than `x` vanishes, then `D = 0`. -/
theorem eq_zero_of_map_eq_zero {x : S} [UniqueFactorizationMonoid (S.presheaf.stalk x)]
    (hdim : ringKrullDim (S.presheaf.stalk x) = 2) {V : S.Opens} (hV : ∀ y, y ≠ x → y ∈ V)
    (D : CartierDivisor S)
    (hD : (cartierDivisorSheaf S).val.map (homOfLE (le_top : V ≤ ⊤)).op D = 0) : D = 0 := by
  obtain ⟨V', i, hxV', f, hf⟩ := exists_local_cartier_equation S ⊤ D x trivial
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV'⟩ :=
    (isBasis_affine_open S).exists_subset_of_mem_open hxV' V'.isOpen
  have hU' : IsAffineOpen U := hU
  haveI : Nonempty V' := ⟨⟨x, hxV'⟩⟩
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE le_top := Subsingleton.elim _ _
  subst hi
  have hUV'' : U ≤ V' := hUV'
  have hDU : (cartierDivisorSheaf S).val.map (homOfLE (le_top : U ≤ ⊤)).op D =
      cartierEquationClassHom S U (Additive.ofMul f) := by
    rw [← cartierEquationClassHom_restrict S hUV'' f, hf, cartierDivisorSheaf_map_map]
  have hW : ∀ y ∈ U, y ≠ x → y ∈ U ⊓ V := fun y hyU hyx => Opens.mem_inf.mpr ⟨hyU, hV y hyx⟩
  haveI : Nonempty (U ⊓ V : S.Opens) :=
    ExtendAcrossClosedPoint.nonempty_of_forall_ne hU' hxU hdim hW
  have hUV : cartierEquationClassHom S (U ⊓ V) (Additive.ofMul f) = 0 := by
    rw [← cartierEquationClassHom_restrict S (inf_le_left : U ⊓ V ≤ U) f, ← hDU,
      cartierDivisorSheaf_map_map,
      ← cartierDivisorSheaf_map_map (le_top : V ≤ ⊤) (inf_le_right : U ⊓ V ≤ V), hD, map_zero]
  have hU0 := cartierEquationClassHom_eq_zero_of_eq_zero_off hU' hxU hdim hW f hUV
  refine (cartierDivisorSheaf S).eq_of_locally_eq₂ (homOfLE (le_top : U ≤ ⊤))
    (homOfLE (le_top : V ≤ ⊤)) ?_ D 0 ?_ ?_
  · intro y _
    by_cases hyx : y = x
    · subst hyx
      exact (le_sup_left : U ≤ U ⊔ V) hxU
    · exact (le_sup_right : V ≤ U ⊔ V) (hV y hyx)
  · rw [hDU, hU0, map_zero]
  · rw [hD, map_zero]

/-! ## From `cartierRestrictionHom` to section restriction -/

/-- If the restriction of `E` along an open immersion `φ` vanishes, a local equation of `E` on `W` is a
unit on `φ(φ⁻¹ W)`. -/
theorem cartierEquationClassHom_image_preimage_eq_zero {Y : Scheme.{u}} [IsIntegral Y] (φ : Y ⟶ S)
    [IsOpenImmersion φ] (E : CartierDivisor S) (hE : cartierRestrictionHom φ E = 0)
    (W : S.Opens) [Nonempty W] [Nonempty (φ ⁻¹ᵁ W)] (g : S.functionFieldˣ)
    (hg : cartierEquationClassHom S W (Additive.ofMul g) =
      (cartierDivisorSheaf S).val.map (homOfLE (le_top : W ≤ ⊤)).op E) :
    letI := nonempty_image φ (φ ⁻¹ᵁ W)
    cartierEquationClassHom S (φ ''ᵁ (φ ⁻¹ᵁ W)) (Additive.ofMul g) = 0 := by
  letI := nonempty_image φ (φ ⁻¹ᵁ W)
  have h := cartierRestriction_globalEquation_preimage φ E W g hg
  rw [hE, map_zero] at h
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_zero_iff Y (φ ⁻¹ᵁ W) _).mp h
  refine (cartierEquationClassHom_eq_zero_iff S (φ ''ᵁ (φ ⁻¹ᵁ W)) g).mpr
    ⟨Units.map (φ.appIso (φ ⁻¹ᵁ W)).inv.hom.toMonoidHom a, ?_⟩
  apply Units.ext
  apply (functionFieldIso φ).hom.hom.injective
  change (functionFieldIso φ).hom (S.germToFunctionField (φ ''ᵁ (φ ⁻¹ᵁ W))
      ((φ.appIso (φ ⁻¹ᵁ W)).inv (a : Γ(Y, φ ⁻¹ᵁ W)))) =
    (functionFieldIso φ).hom (g : S.functionField)
  rw [functionFieldIso_image_germ, Iso.inv_hom_id_apply]
  exact congrArg Units.val ha

/-- If `cartierRestrictionHom V.ι E = 0`, the section restriction of `E` to `V` vanishes. -/
theorem map_eq_zero_of_cartierRestrictionHom_eq_zero {V : S.Opens} [Nonempty V]
    (E : CartierDivisor S) (hE : cartierRestrictionHom V.ι E = 0) :
    (cartierDivisorSheaf S).val.map (homOfLE (le_top : V ≤ ⊤)).op E = 0 := by
  choose V' i hzV' g hg using fun z : V => exists_local_cartier_equation S ⊤ E z.1 trivial
  refine (cartierDivisorSheaf S).eq_of_locally_eq' (fun z : V => V.ι ''ᵁ (V.ι ⁻¹ᵁ V' z)) V
    (fun z => homOfLE (V.ι_image_le _)) ?_ _ 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, (Scheme.Hom.map_mem_image_iff V.ι
      (U := V.ι ⁻¹ᵁ V' ⟨y, hy⟩) (x := ⟨y, hy⟩)).mpr (hzV' ⟨y, hy⟩)⟩
  · intro z
    haveI : Nonempty (V' z) := ⟨⟨z.1, hzV' z⟩⟩
    haveI : Nonempty (V.ι ⁻¹ᵁ V' z) := ⟨⟨z, hzV' z⟩⟩
    letI := nonempty_image V.ι (V.ι ⁻¹ᵁ V' z)
    have hi : i z = homOfLE le_top := Subsingleton.elim _ _
    have hgz := hg z
    rw [hi] at hgz
    have h0 := cartierEquationClassHom_image_preimage_eq_zero V.ι E hE (V' z) (g z) hgz
    have hle : V.ι ''ᵁ (V.ι ⁻¹ᵁ V' z) ≤ V' z :=
      (V.ι.image_preimage_eq_opensRange_inter (V' z)).le.trans inf_le_right
    rw [map_zero, cartierDivisorSheaf_map_map, ← h0,
      ← cartierEquationClassHom_restrict S hle (g z), hgz, cartierDivisorSheaf_map_map]

/-! ## Injectivity of restriction off the point -/

variable {x : S} [UniqueFactorizationMonoid (S.presheaf.stalk x)]
  (hdim : ringKrullDim (S.presheaf.stalk x) = 2)

include hdim

omit [IsIntegral S] [UniqueFactorizationMonoid (S.presheaf.stalk x)] in
/-- An open containing every point other than `x` is nonempty. -/
theorem nonempty_of_forall_ne {V : S.Opens} (hV : ∀ y, y ≠ x → y ∈ V) : Nonempty V := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open S).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  exact ExtendAcrossClosedPoint.nonempty_of_forall_ne hU' hxU hdim fun y _ hyx => hV y hyx

/-- **A Cartier divisor whose restriction off `x` is trivial is trivial.** -/
theorem eq_zero_of_cartierRestrictionHom_eq_zero {V : S.Opens} [Nonempty V]
    (hV : ∀ y, y ≠ x → y ∈ V) (D : CartierDivisor S) (hD : cartierRestrictionHom V.ι D = 0) :
    D = 0 :=
  eq_zero_of_map_eq_zero hdim hV D (map_eq_zero_of_cartierRestrictionHom_eq_zero D hD)

/-- **Restriction of Cartier divisors off `x` is injective.** -/
theorem cartierRestrictionHom_injective {V : S.Opens} [Nonempty V] (hV : ∀ y, y ≠ x → y ∈ V) :
    Function.Injective (cartierRestrictionHom V.ι) := by
  rw [injective_iff_map_eq_zero]
  exact eq_zero_of_cartierRestrictionHom_eq_zero hdim hV

/-- A Picard class of a Cartier divisor which becomes trivial off `x` is trivial. -/
theorem cartierPicardClass_eq_one_of_pullback_eq_one {V : S.Opens} (hV : ∀ y, y ≠ x → y ∈ V)
    (D : CartierDivisor S) (hD : schemePicardPullbackHom V.ι (cartierPicardClass S D) = 1) :
    cartierPicardClass S D = 1 := by
  haveI : Nonempty V := nonempty_of_forall_ne hdim hV
  rw [schemePicardPullbackHom_cartierPicardClass] at hD
  obtain ⟨g', hg'⟩ := (cartierPicardClass_eq_one_iff V.toScheme _).mp hD
  let g : S.functionFieldˣ := Units.map (functionFieldIso V.ι).inv.hom.toMonoidHom g'
  have hg : Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom g = g' := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (functionFieldIso V.ι) (g' : V.toScheme.functionField)
  have h0 : D - principalCartierDivisorHom S (Additive.ofMul g) = 0 := by
    apply eq_zero_of_cartierRestrictionHom_eq_zero hdim hV
    rw [map_sub, cartierRestrictionHom_principal, hg, hg', sub_self]
  rw [sub_eq_zero.mp h0]
  exact cartierPicardClass_principal S g

/-- **Restriction of Picard classes off `x` is injective**, `Pic S → Pic V`. -/
theorem schemePicardPullbackHom_injective {V : S.Opens} (hV : ∀ y, y ≠ x → y ∈ V) :
    Function.Injective (schemePicardPullbackHom V.ι) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective S c
  exact cartierPicardClass_eq_one_of_pullback_eq_one hdim hV D hc

/-- Closed-point form: `Pic S → Pic (S ∖ {x})` is injective. -/
theorem schemePicardPullbackHom_compl_injective (hclosed : IsClosed ({x} : Set S)) :
    Function.Injective
      (schemePicardPullbackHom (Scheme.Opens.ι (⟨({x} : Set S)ᶜ, hclosed.isOpen_compl⟩ : S.Opens))) :=
  schemePicardPullbackHom_injective hdim fun _ hyx => hyx

end KltDP.Geometry.CartierSupportedAtPoint

namespace KltDP.Geometry.CartierSupportedAtPoint

open KltDP.Geometry.PointBlowupGluing

local instance (T : Scheme.{u}) [IsIntegral T] (y : T) : IsDomain (T.presheaf.stalk y) :=
  ExtendAcrossClosedPoint.stalk_isDomain T y

/-- For the accepted point-blowup data, restriction of Picard classes to the puncture
`puncture j q hclosed = X ∖ {j.base q}` is injective when `X` is integral and the stalk at `j.base q` is a
two-dimensional UFD (the injectivity half of `hres` in `PointBlowupPicard.picardDecomposition`). -/
theorem puncture_schemePicardPullbackHom_injective {R : Type u} [CommRing R] {X : Scheme.{u}}
    [IsIntegral X] (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (q : PrimeSpectrum R)
    [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set X))
    [UniqueFactorizationMonoid (X.presheaf.stalk (j.base q))]
    (hdim : ringKrullDim (X.presheaf.stalk (j.base q)) = 2) :
    Function.Injective (schemePicardPullbackHom (puncture j q hclosed).ι) :=
  schemePicardPullbackHom_injective hdim fun _ hyx => hyx

end KltDP.Geometry.CartierSupportedAtPoint
