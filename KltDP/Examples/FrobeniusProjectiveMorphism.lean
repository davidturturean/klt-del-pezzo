import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Geometry.ProjectiveSpaceNormal
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Coordinate-power maps for projective Frobenius

The coefficient homomorphism in every polynomial substitution below is `C`.
Thus scalars in `k` are fixed; these are coordinate-power maps over `k`,
not the absolute Frobenius on a coefficient field.

The affine component is compatible with the actual graph parameterization
from `FrobeniusProjectivePoints`. The homogeneous-localization component
adapts the quotient construction of pinned Mathlib's
`HomogeneousLocalization.map` to the degree scaling `d ↦ p*d`.
That construction is Copyright (c) 2022 Jujian Zhang, Eric Wieser,
released under Apache 2.0; the project retains the license text in
`docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusProjectiveMorphism

open KltDP.Geometry ProjectiveChart FrobeniusProjectivePoints

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The affine coordinate is raised to `p`; all coefficients are fixed. -/
def affinePowerHom (p : ℕ) : affineRing k 1 →+* affineRing k 1 :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun _ : Fin 1 => (MvPolynomial.X 0 : affineRing k 1) ^ p)

@[simp] theorem affinePowerHom_C (p : ℕ) (r : k) :
    affinePowerHom p (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [affinePowerHom]

@[simp] theorem affinePowerHom_X (p : ℕ) :
    affinePowerHom (k := k) p (MvPolynomial.X 0) = MvPolynomial.X 0 ^ p := by
  simp [affinePowerHom]

theorem affinePowerHom_one : affinePowerHom (k := k) 1 = RingHom.id (affineRing k 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affinePowerHom]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [affinePowerHom]

theorem parameterMap_one : parameterMap (k := k) 1 = dehomogenize k 1 := by
  change (affinePowerHom 1).comp (dehomogenize k 1) = dehomogenize k 1
  rw [affinePowerHom_one]
  rfl

/-- The actual affine-line scheme endomorphism induced by coordinate powering. -/
def affinePowerMorphism (p : ℕ) :
    Spec (CommRingCat.of (affineRing k 1)) ⟶ Spec (CommRingCat.of (affineRing k 1)) :=
  Spec.map (CommRingCat.ofHom (affinePowerHom p))

theorem affinePowerMorphism_over_base (p : ℕ) :
    affinePowerMorphism (k := k) p ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1)) := by
  have h : CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1) ≫
      CommRingCat.ofHom (affinePowerHom p) =
      CommRingCat.ofHom (MvPolynomial.C : k →+* affineRing k 1) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact affinePowerHom_C p r
  rw [affinePowerMorphism, ← Spec.map_comp, h]

/-- The new affine endomorphism gives exactly the existing projective-chart map. -/
theorem affinePowerMorphism_comp_chart (p : ℕ) :
    affinePowerMorphism (k := k) p ≫ parameterMorphism 1 = parameterMorphism p := by
  have h : CommRingCat.ofHom (parameterMap (k := k) 1) ≫
      CommRingCat.ofHom (affinePowerHom p) = CommRingCat.ofHom (parameterMap p) := by
    rw [parameterMap_one]
    rfl
  rw [affinePowerMorphism, parameterMorphism, parameterMorphism,
    ← Category.assoc, ← Spec.map_comp, h]

/-- Evaluation of the actual affine endomorphism agrees with scalar coordinate powering. -/
theorem affinePowerMorphism_evaluation (p : ℕ) (a : k) :
    Spec.map (CommRingCat.ofHom (parameterEvaluation a)) ≫ affinePowerMorphism p =
      Spec.map (CommRingCat.ofHom (parameterEvaluation (a ^ p))) := by
  have h : (parameterEvaluation a).comp (affinePowerHom p) =
      parameterEvaluation (a ^ p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [parameterEvaluation, affinePowerHom]
    · intro i
      simp [parameterEvaluation, affinePowerHom]
  rw [affinePowerMorphism, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

/-- The actual affine graph has the existing chart as first projection. -/
theorem affineGraphMorphism_fst (p : ℕ) :
    affineGraphMorphism (k := k) p ≫
        pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      parameterMorphism 1 :=
  pullback.lift_fst _ _ _

/-- Its second projection is the affine power endomorphism followed by that same chart. -/
theorem affineGraphMorphism_snd (p : ℕ) :
    affineGraphMorphism (k := k) p ≫
        pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      affinePowerMorphism p ≫ parameterMorphism 1 := by
  rw [affinePowerMorphism_comp_chart]
  exact pullback.lift_snd _ _ _

/-- Coordinate powering on the homogeneous polynomial ring fixes coefficients. -/
def homogeneousPowerHom (p : ℕ) : homogeneousRing k 1 →+* homogeneousRing k 1 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i ^ p)

@[simp] theorem homogeneousPowerHom_C (p : ℕ) (r : k) :
    homogeneousPowerHom p (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [homogeneousPowerHom]

@[simp] theorem homogeneousPowerHom_X (p : ℕ) (i : Fin 2) :
    homogeneousPowerHom (k := k) p (MvPolynomial.X i) = MvPolynomial.X i ^ p := by
  simp [homogeneousPowerHom]

/-- A homogeneous polynomial of degree `d` is sent to degree `p*d`. -/
theorem homogeneousPowerHom_mem (p d : ℕ) (a : homogeneousRing k 1)
    (ha : a ∈ grading k 1 d) :
    homogeneousPowerHom p a ∈ grading k 1 (p * d) :=
  (show a.IsHomogeneous d from ha).eval₂ MvPolynomial.C
    (fun i => MvPolynomial.X i ^ p)
    (fun r => MvPolynomial.isHomogeneous_C _ r)
    (fun i => MvPolynomial.isHomogeneous_X_pow i p)

section HomogeneousLocalization

variable (p : ℕ) (P : Submonoid (homogeneousRing k 1))
  (hP : P ≤ P.comap (homogeneousPowerHom p))

private def powerLocalizationFun :
    HomogeneousLocalization (grading k 1) P → HomogeneousLocalization (grading k 1) P :=
  Quotient.map'
    (fun x => ⟨p * x.deg,
      ⟨homogeneousPowerHom p x.num, homogeneousPowerHom_mem p _ _ x.num.2⟩,
      ⟨homogeneousPowerHom p x.den, homogeneousPowerHom_mem p _ _ x.den.2⟩,
      hP x.den_mem⟩)
    (fun x y (e : x.embedding = y.embedding) => by
      apply_fun IsLocalization.map (Localization P) (homogeneousPowerHom p) hP at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e)

private theorem powerLocalizationFun_val
    (x : HomogeneousLocalization (grading k 1) P) :
    (powerLocalizationFun p P hP x).val =
      IsLocalization.map (Localization P) (homogeneousPowerHom p) hP x.val := by
  obtain ⟨a, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [powerLocalizationFun, Quotient.map'_mk'', HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']

/-- Coordinate powering on a homogeneous localization, with the degree scaling
carried in actual numerator/denominator representatives. -/
def powerLocalizationMap :
    HomogeneousLocalization (grading k 1) P →+* HomogeneousLocalization (grading k 1) P where
  toFun := powerLocalizationFun p P hP
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [powerLocalizationFun_val, HomogeneousLocalization.val_zero, map_zero]
  map_one' := by
    apply HomogeneousLocalization.val_injective
    simp only [powerLocalizationFun_val, HomogeneousLocalization.val_one, map_one]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [powerLocalizationFun_val, HomogeneousLocalization.val_add, map_add]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [powerLocalizationFun_val, HomogeneousLocalization.val_mul, map_mul]

theorem powerLocalizationMap_val (x : HomogeneousLocalization (grading k 1) P) :
    (powerLocalizationMap p P hP x).val =
      IsLocalization.map (Localization P) (homogeneousPowerHom p) hP x.val :=
  powerLocalizationFun_val p P hP x

end HomogeneousLocalization

/-- If a homogeneous denominator is sent to its `p`th power, its powers form
a preserved denominator monoid. -/
theorem powers_le_comap_homogeneousPowerHom (p : ℕ) (f : homogeneousRing k 1)
    (hf : homogeneousPowerHom p f = f ^ p) :
    Submonoid.powers f ≤ (Submonoid.powers f).comap (homogeneousPowerHom p) := by
  rintro a ⟨m, rfl⟩
  change homogeneousPowerHom p (f ^ m) ∈ Submonoid.powers f
  rw [map_pow, hf, ← pow_mul]
  exact ⟨p * m, rfl⟩

/-- The actual degree-zero localization endomorphism on a projective chart. -/
def chartPowerMap (p : ℕ) (f : homogeneousRing k 1)
    (hf : homogeneousPowerHom p f = f ^ p) :
    HomogeneousLocalization.Away (grading k 1) f →+*
      HomogeneousLocalization.Away (grading k 1) f :=
  powerLocalizationMap p (Submonoid.powers f)
    (powers_le_comap_homogeneousPowerHom p f hf)

/-- The coordinate-power maps commute with the actual projective-chart
transition ring maps. This follows from uniqueness of localization lifts. -/
theorem chartPowerMap_awayMap (p : ℕ) {f g x : homogeneousRing k 1}
    {d : ℕ} (hg : g ∈ grading k 1 d) (hx : x = f * g)
    (hf : homogeneousPowerHom p f = f ^ p)
    (hxp : homogeneousPowerHom p x = x ^ p) :
    (HomogeneousLocalization.awayMap (grading k 1) hg hx).comp (chartPowerMap p f hf) =
      (chartPowerMap p x hxp).comp
        (HomogeneousLocalization.awayMap (grading k 1) hg hx) := by
  let θ : Localization.Away f →+* Localization.Away x :=
    Localization.awayLift (algebraMap (homogeneousRing k 1) (Localization.Away x)) f
      (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩)
        (IsLocalization.Away.algebraMap_isUnit x))
  have hθ : θ.comp
      (IsLocalization.map (Localization.Away f) (homogeneousPowerHom p)
        (powers_le_comap_homogeneousPowerHom p f hf)) =
      (IsLocalization.map (Localization.Away x) (homogeneousPowerHom p)
        (powers_le_comap_homogeneousPowerHom p x hxp)).comp θ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, θ,
      Localization.awayLift, IsLocalization.Away.lift_eq]
  apply RingHom.ext
  intro z
  apply HomogeneousLocalization.val_injective
  simpa only [RingHom.comp_apply, HomogeneousLocalization.val_awayMap,
    chartPowerMap, powerLocalizationMap_val, θ] using RingHom.congr_fun hθ z.val

/-- The same compatibility after applying `Spec` and the actual chart immersions. -/
theorem chartPowerMorphism_overlap (p : ℕ) {f g x : homogeneousRing k 1}
    (hf : f ∈ grading k 1 1) (hg : g ∈ grading k 1 1) (hx : x = f * g)
    (hfp : homogeneousPowerHom p f = f ^ p)
    (hxp : homogeneousPowerHom p x = x ^ p) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading k 1) hg hx)) ≫
        (Spec.map (CommRingCat.ofHom (chartPowerMap p f hfp)) ≫
          Proj.awayι (grading k 1) f hf Nat.zero_lt_one) =
      Spec.map (CommRingCat.ofHom (chartPowerMap p x hxp)) ≫
        Proj.awayι (grading k 1) x
          (hx ▸ SetLike.mul_mem_graded hf hg) (by decide) := by
  have h : CommRingCat.ofHom (chartPowerMap p f hfp) ≫
      CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading k 1) hg hx) =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap (grading k 1) hg hx) ≫
        CommRingCat.ofHom (chartPowerMap p x hxp) :=
    CommRingCat.hom_ext (chartPowerMap_awayMap p hg hx hfp hxp)
  rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]

/-- The coordinate-power morphism on each member of the actual standard cover. -/
def localProjectivePower (p : ℕ) (i : Fin 2) :
    (standardAffineCover k 1).openCover.obj i ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom
    (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i))) ≫
      (standardAffineCover k 1).map i

/-- The chart maps agree on their genuine scheme pullbacks. -/
theorem localProjectivePower_compatible (p : ℕ) (i j : Fin 2) :
    pullback.fst ((standardAffineCover k 1).map i) ((standardAffineCover k 1).map j) ≫
        localProjectivePower p i =
      pullback.snd ((standardAffineCover k 1).map i) ((standardAffineCover k 1).map j) ≫
        localProjectivePower p j := by
  let f : homogeneousRing k 1 := MvPolynomial.X i
  let g : homogeneousRing k 1 := MvPolynomial.X j
  let hf : f ∈ grading k 1 1 := MvPolynomial.isHomogeneous_X k i
  let hg : g ∈ grading k 1 1 := MvPolynomial.isHomogeneous_X k j
  let e := Proj.pullbackAwayιIso (grading k 1) hf Nat.zero_lt_one hg Nat.zero_lt_one
    (show f * g = f * g from rfl)
  have hfg : homogeneousPowerHom p (f * g) = (f * g) ^ p := by
    simp only [map_mul, f, g, homogeneousPowerHom_X, mul_pow]
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (pullback.fst (Proj.awayι (grading k 1) f hf Nat.zero_lt_one)
      (Proj.awayι (grading k 1) g hg Nat.zero_lt_one) ≫
        (Spec.map (CommRingCat.ofHom (chartPowerMap p f (homogeneousPowerHom_X p i))) ≫
          Proj.awayι (grading k 1) f hf Nat.zero_lt_one)) =
    e.inv ≫ (pullback.snd (Proj.awayι (grading k 1) f hf Nat.zero_lt_one)
      (Proj.awayι (grading k 1) g hg Nat.zero_lt_one) ≫
        (Spec.map (CommRingCat.ofHom (chartPowerMap p g (homogeneousPowerHom_X p j))) ≫
          Proj.awayι (grading k 1) g hg Nat.zero_lt_one))
  rw [← Category.assoc e.inv, ← Category.assoc e.inv]
  rw [Proj.pullbackAwayιIso_inv_fst, Proj.pullbackAwayιIso_inv_snd]
  exact (chartPowerMorphism_overlap p hf hg rfl (homogeneousPowerHom_X p i) hfg).trans
    (chartPowerMorphism_overlap p hg hf (mul_comm f g) (homogeneousPowerHom_X p j) hfg).symm

/-- The same two standard charts, with indices lifted to the universe required
by the pinned scheme-gluing API. All chart objects and maps are unchanged. -/
private def projectivePowerCover : Scheme.OpenCover.{u} (projectiveSpace k 1) where
  J := ULift.{u} (Fin 2)
  obj i := (standardAffineCover k 1).openCover.obj i.down
  map i := (standardAffineCover k 1).map i.down
  f x := ⟨(standardAffineCover k 1).f x⟩
  covers x := (standardAffineCover k 1).covers x

/-- The global coordinate-power self-morphism of the actual projective line,
obtained by gluing the proved compatible maps on its standard affine cover. -/
def projectivePowerMorphism (p : ℕ) : projectiveSpace k 1 ⟶ projectiveSpace k 1 :=
  (projectivePowerCover (k := k)).glueMorphisms
    (fun i => localProjectivePower p i.down)
    (fun i j => localProjectivePower_compatible p i.down j.down)

/-- On every actual chart the global map is the coordinate-power map constructed above. -/
theorem chart_projectivePowerMorphism (p : ℕ) (i : Fin 2) :
    (standardAffineCover k 1).map i ≫ projectivePowerMorphism p =
      localProjectivePower p i :=
  (projectivePowerCover (k := k)).ι_glueMorphisms _ _ (ULift.up i)

/-- The constants in any actual homogeneous chart. -/
def chartConstants (f : homogeneousRing k 1) :
    k →+* HomogeneousLocalization.Away (grading k 1) f :=
  (HomogeneousLocalization.fromZeroRingHom (grading k 1) (Submonoid.powers f)).comp
    (projectiveSpaceConstants k 1)

theorem chartPowerMap_constants (p : ℕ) (f : homogeneousRing k 1)
    (hf : homogeneousPowerHom p f = f ^ p) (r : k) :
    chartPowerMap p f hf (chartConstants f r) = chartConstants f r := by
  apply HomogeneousLocalization.val_injective
  rw [chartPowerMap, powerLocalizationMap_val]
  change IsLocalization.map (Localization.Away f) (homogeneousPowerHom p)
      (powers_le_comap_homogeneousPowerHom p f hf)
      (Localization.mk (MvPolynomial.C r) ⟨1, one_mem _⟩) =
    Localization.mk (MvPolynomial.C r) ⟨1, one_mem _⟩
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk', homogeneousPowerHom_C, map_one]

theorem awayι_over_base {f : homogeneousRing k 1} (hf : f ∈ grading k 1 1) :
    Proj.awayι (grading k 1) f hf Nat.zero_lt_one ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (chartConstants f)) := by
  rw [projectiveSpaceToSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The global map preserves the specified structure morphism to `Spec k`. -/
theorem projectivePowerMorphism_over_base (p : ℕ) :
    projectivePowerMorphism (k := k) p ≫ projectiveSpaceToSpec k 1 =
      projectiveSpaceToSpec k 1 := by
  apply (projectivePowerCover (k := k)).hom_ext
  rintro ⟨i⟩
  change (standardAffineCover k 1).map i ≫
      (projectivePowerMorphism p ≫ projectiveSpaceToSpec k 1) =
    (standardAffineCover k 1).map i ≫ projectiveSpaceToSpec k 1
  rw [← Category.assoc, chart_projectivePowerMorphism]
  change (Spec.map (CommRingCat.ofHom
      (chartPowerMap p (MvPolynomial.X i) (homogeneousPowerHom_X p i))) ≫
        Proj.awayι (grading k 1) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one) ≫ projectiveSpaceToSpec k 1 =
    Proj.awayι (grading k 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one ≫ projectiveSpaceToSpec k 1
  rw [Category.assoc, awayι_over_base, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact chartPowerMap_constants p _ (homogeneousPowerHom_X p i) r

/-- On the first chart the actual coordinate fraction is sent to its `p`th power. -/
theorem chartPowerMap_ratio (p : ℕ) :
    chartPowerMap p (coordinate k 1) (homogeneousPowerHom_X p 0) (ratio k 1 0) =
      ratio k 1 0 ^ p := by
  apply HomogeneousLocalization.val_injective
  rw [chartPowerMap, powerLocalizationMap_val, HomogeneousLocalization.val_pow]
  simp only [ratio, HomogeneousLocalization.Away.val_mk, pow_one,
    Localization.mk_eq_mk', IsLocalization.map_mk', coordinate,
    homogeneousPowerHom_X, ← IsLocalization.mk'_pow]
  apply congrArg (IsLocalization.mk' (ambientLocalization k 1)
    ((MvPolynomial.X (Fin.succ (0 : Fin 1)) : homogeneousRing k 1) ^ p))
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]

/-- The homogeneous-localization map dehomogenizes to the original affine substitution. -/
theorem dehomogenize_comp_chartPowerMap (p : ℕ) :
    (dehomogenize k 1).comp
        (chartPowerMap p (coordinate k 1) (homogeneousPowerHom_X p 0)) =
      parameterMap p := by
  have h : ((dehomogenize k 1).comp
      (chartPowerMap p (coordinate k 1) (homogeneousPowerHom_X p 0))).comp
        (homogenizeRatios k 1) = affinePowerHom p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, homogenizeRatios, MvPolynomial.eval₂Hom_C]
      rw [show constants k 1 r = chartConstants (coordinate k 1) r from rfl,
        chartPowerMap_constants]
      exact (dehomogenize_constants k 1 r).trans (affinePowerHom_C p r).symm
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [RingHom.comp_apply, homogenizeRatios, MvPolynomial.eval₂Hom_X']
      rw [chartPowerMap_ratio, map_pow, dehomogenize_ratio, affinePowerHom_X]
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun h (dehomogenize k 1 z)
  simpa only [RingHom.comp_apply, homogenizeRatios_dehomogenize] using hz

/-- The global morphism has exactly the affine action used in the manuscript construction. -/
theorem parameterMorphism_projectivePowerMorphism (p : ℕ) :
    parameterMorphism (k := k) 1 ≫ projectivePowerMorphism p = parameterMorphism p := by
  have hc : chartMorphism k 1 ≫ projectivePowerMorphism p =
      Spec.map (CommRingCat.ofHom
        (chartPowerMap p (coordinate k 1) (homogeneousPowerHom_X p 0))) ≫ chartMorphism k 1 :=
    chart_projectivePowerMorphism p 0
  have hr : CommRingCat.ofHom
      (chartPowerMap p (coordinate k 1) (homogeneousPowerHom_X p 0)) ≫
        CommRingCat.ofHom (dehomogenize k 1) = CommRingCat.ofHom (parameterMap p) :=
    CommRingCat.hom_ext (dehomogenize_comp_chartPowerMap p)
  rw [parameterMorphism, parameterMap_one, Category.assoc, hc,
    ← Category.assoc, ← Spec.map_comp, hr]
  rfl

/-- The actual graph morphism of the global coordinate-power map over `k`. -/
def projectiveGraphMorphism (p : ℕ) : projectiveSpace k 1 ⟶ projectiveProduct k :=
  pullback.lift (𝟙 (projectiveSpace k 1)) (projectivePowerMorphism p)
    (by rw [Category.id_comp, projectivePowerMorphism_over_base])

/-- The previously constructed affine graph is the restriction of the global graph morphism. -/
theorem parameterMorphism_projectiveGraphMorphism (p : ℕ) :
    parameterMorphism (k := k) 1 ≫ projectiveGraphMorphism p = affineGraphMorphism p := by
  apply pullback.hom_ext
  · simp only [projectiveGraphMorphism, Category.assoc, pullback.lift_fst,
      Category.comp_id, affineGraphMorphism_fst]
  · simp only [projectiveGraphMorphism, Category.assoc, pullback.lift_snd,
      parameterMorphism_projectivePowerMorphism, affineGraphMorphism_snd,
      affinePowerMorphism_comp_chart]

end KltDP.Examples.FrobeniusProjectiveMorphism
