import KltDP.Geometry.PointClosureCurve
import KltDP.Geometry.ProjectivePlane

/-!
# Prime curves from closed immersions of irreducible curves

Two constructors of `PrimeCurve`s of a `NormalProjectiveSurface` from a closed immersion
`ι : C ⟶ X` of a scheme `C`:

* `primeCurveOfIsoProjectiveLine`: when `C ≅ P¹_k`, the range has dimension one by homeomorphism
  transport (the accepted `exceptionalPrimeCurve` pattern), and `C` is integral through the
  isomorphism;
* `primeCurve`: when `C` is irreducible, the range is not the whole surface and `C` has two
  distinct points, the range is the closure of the image of the generic point of `C`
  (`range_eq_closure_genericPoint`), which is neither the generic point of the surface nor a closed
  point, so the accepted `pointClosure_dimension_eq_one` gives dimension one.

The second constructor needs no isomorphism with `P¹` and is used for the strict transforms of
the graph and of the fibre in the Frobenius towers, whose identification with `P¹` is not accepted.
Also: two distinct points of `Spec k[t]` (`exists_pair_ne_polynomialSpec`), two distinct points of
the basic open `D(t)` (`exists_pair_ne_basicOpen_X`), and injectivity of a morphism from
injectivity of a composite (`injective_of_comp`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PrimeCurveOfClosedImmersion

open KltDP.Geometry

section Generic

variable {k : Type u} [Field k]

/-- Injectivity of `f` on points from injectivity of a composite `f ≫ g`. -/
theorem injective_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Function.Injective (f ≫ g).base) : Function.Injective f.base := by
  intro a b hab
  apply h
  simp only [Scheme.comp_base_apply, hab]

/-- Two distinct points of the affine line `Spec k[t]`: the generic point and the origin. -/
theorem exists_pair_ne_polynomialSpec (k : Type u) [Field k] :
    ∃ x y : Spec (CommRingCat.of (Polynomial k)), x ≠ y := by
  let x : PrimeSpectrum (Polynomial k) := ⟨⊥, Ideal.bot_prime⟩
  let y : PrimeSpectrum (Polynomial k) :=
    ⟨Ideal.span {Polynomial.X},
      (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  have hxy : x ≠ y := by
    intro h
    have hX : (Polynomial.X : Polynomial k) ∈ y.asIdeal := Ideal.mem_span_singleton_self _
    rw [← h] at hX
    exact Polynomial.X_ne_zero (Ideal.mem_bot.mp hX)
  exact ⟨x, y, hxy⟩

/-- Two distinct points of the basic open `D(t) ⊆ Spec k[t]`: the generic point and `t = 1`. -/
theorem exists_pair_ne_basicOpen_X (k : Type u) [Field k] :
    ∃ x y : Spec (CommRingCat.of (Polynomial k)),
      x ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) ∧
      y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) ∧ x ≠ y := by
  let x : PrimeSpectrum (Polynomial k) := ⟨⊥, Ideal.bot_prime⟩
  let y : PrimeSpectrum (Polynomial k) :=
    ⟨Ideal.span {Polynomial.X - Polynomial.C 1},
      (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero 1)).mpr (Polynomial.prime_X_sub_C 1)⟩
  have hx : x ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact fun h => Polynomial.X_ne_zero (Ideal.mem_bot.mp h)
  have hy : y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro h
    have h' : Polynomial.X - Polynomial.C (1 : k) ∣ Polynomial.X := Ideal.mem_span_singleton.mp h
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_X] at h'
    exact one_ne_zero h'
  have hxy : x ≠ y := by
    intro h
    have hX : Polynomial.X - Polynomial.C (1 : k) ∈ y.asIdeal := Ideal.mem_span_singleton_self _
    rw [← h] at hX
    exact Polynomial.X_sub_C_ne_zero 1 (Ideal.mem_bot.mp hX)
  exact ⟨x, y, hx, hy, hxy⟩

/-- The range of a closed immersion of a scheme isomorphic to `P¹` has dimension one. -/
theorem range_topologicalKrullDim_of_iso {C Y : Scheme.{u}} (ι : C ⟶ Y) [IsClosedImmersion ι]
    (e : C ≅ projectiveSpace k 1) : topologicalKrullDim (Set.range ι.base) = 1 := by
  calc
    topologicalKrullDim (Set.range ι.base) = topologicalKrullDim C :=
      (IsHomeomorph.topologicalKrullDim_eq _
        ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
    _ = topologicalKrullDim (projectiveSpace k 1) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph
    _ = ((1 : ℕ) : WithBot ℕ∞) := projectiveSpace_topologicalKrullDim k 1
    _ = 1 := Nat.cast_one

/-- A scheme isomorphic to `P¹` is integral. -/
theorem isIntegral_of_iso_projectiveLine {C : Scheme.{u}} (e : C ≅ projectiveSpace k 1) :
    IsIntegral C := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  haveI : Nonempty C := ⟨e.inv.base (projectiveSpace_nonempty k 1).some⟩
  exact isIntegral_of_isOpenImmersion e.hom

end Generic

section Surface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)
variable {C : Scheme.{u}} (ι : C ⟶ X.toScheme) [IsClosedImmersion ι]

/-- The range of a closed immersion is closed. -/
theorem range_isClosed : IsClosed (Set.range ι.base) := ι.isClosedEmbedding.isClosed_range

section Irreducible

variable [IrreducibleSpace C]

omit [IsClosedImmersion ι] in
/-- The range of a closed immersion of an irreducible scheme is irreducible. -/
theorem range_isIrreducible : IsIrreducible (Set.range ι.base) := by
  have h := (IrreducibleSpace.isIrreducible_univ C).image ι.base ι.continuous.continuousOn
  simpa only [Set.image_univ] using h

/-- The range is the closure of the image of the generic point. -/
theorem range_eq_closure_genericPoint :
    Set.range ι.base = closure ({ι.base (genericPoint C)} : Set X.toScheme) := by
  rw [← Set.image_univ, ← (genericPoint_spec C).def, ← ι.isClosedEmbedding.closure_image_eq,
    Set.image_singleton]

/-- If the range is not the whole surface, the image of the generic point is not the generic
point of the surface. -/
theorem genericPoint_image_ne (hne : Set.range ι.base ≠ Set.univ) :
    ι.base (genericPoint C) ≠ genericPoint X.toScheme := by
  intro h
  apply hne
  rw [range_eq_closure_genericPoint X ι, h]
  exact (genericPoint_spec X.toScheme).def

/-- If `C` has two distinct points, the image of the generic point is not closed. -/
theorem genericPoint_image_not_isClosed (hnt : ∃ x y : C, x ≠ y) :
    ¬ IsClosed ({ι.base (genericPoint C)} : Set X.toScheme) := by
  intro h
  obtain ⟨x, y, hxy⟩ := hnt
  have hrange : Set.range ι.base = {ι.base (genericPoint C)} := by
    rw [range_eq_closure_genericPoint X ι, h.closure_eq]
  have hx : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
  have hy : ι.base y ∈ Set.range ι.base := ⟨y, rfl⟩
  rw [hrange, Set.mem_singleton_iff] at hx hy
  exact hxy (ι.isClosedEmbedding.injective (hx.trans hy.symm))

/-- **Dimension one of the range** from the accepted point-closure dimension. -/
theorem range_topologicalKrullDim (hne : Set.range ι.base ≠ Set.univ) (hnt : ∃ x y : C, x ≠ y) :
    topologicalKrullDim (Set.range ι.base) = 1 := by
  have h := X.pointClosure_dimension_eq_one (ι.base (genericPoint C))
    (genericPoint_image_ne X ι hne) (genericPoint_image_not_isClosed X ι hnt)
  change topologicalKrullDim (closure ({ι.base (genericPoint C)} : Set X.toScheme)) = 1 at h
  rw [← range_eq_closure_genericPoint X ι] at h
  exact h

/-- **A closed irreducible curve with two distinct points, not filling the surface, is a prime
curve.** -/
def primeCurve (hne : Set.range ι.base ≠ Set.univ) (hnt : ∃ x y : C, x ≠ y) : X.PrimeCurve :=
  ⟨⟨Set.range ι.base, range_isIrreducible X ι, range_isClosed X ι⟩,
    range_topologicalKrullDim X ι hne hnt⟩

@[simp] theorem coe_primeCurve (hne : Set.range ι.base ≠ Set.univ) (hnt : ∃ x y : C, x ≠ y) :
    (primeCurve X ι hne hnt : Set X.toScheme) = Set.range ι.base := rfl

end Irreducible

/-- **A closed immersion of a scheme isomorphic to `P¹` is a prime curve.** -/
def primeCurveOfIsoProjectiveLine (e : C ≅ projectiveSpace k 1) : X.PrimeCurve :=
  letI : IsIntegral C := isIntegral_of_iso_projectiveLine e
  ⟨⟨Set.range ι.base, range_isIrreducible X ι, range_isClosed X ι⟩,
    range_topologicalKrullDim_of_iso ι e⟩

@[simp] theorem coe_primeCurveOfIsoProjectiveLine (e : C ≅ projectiveSpace k 1) :
    (primeCurveOfIsoProjectiveLine X ι e : Set X.toScheme) = Set.range ι.base := rfl

end Surface

end KltDP.Geometry.PrimeCurveOfClosedImmersion
