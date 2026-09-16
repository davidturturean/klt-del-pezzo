import KltDP.Geometry.SmoothEtaleCoordinates

/-!
# Translation of actual étale coordinates to the origin

The polynomial automorphism below sends each variable to that variable
minus a specified scalar. Composing an actual coordinate map with this
automorphism centers its value under an actual algebra character.

The character identity gives a commuting diagram of actual Spec maps.
It does not identify the entire inverse-image fiber with the chosen point.
All constructions use the pinned polynomial evaluation and algebra
equivalence APIs; no newer library declaration is imported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace KltDP.Geometry.EtaleCoordinates

universe u v w

/-- Translation by minus the given scalar coordinates, with the opposite
translation as its actual inverse. -/
def polynomialTranslation {k : Type u} [CommRing k] {ι : Type v} (a : ι → k) :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i ↦ X i - C (a i))
    (MvPolynomial.aeval fun i ↦ X i + C (a i))
    (by
      ext i
      simp [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq])
    (by
      ext i
      simp [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq])

@[simp] theorem polynomialTranslation_X
    {k : Type u} [CommRing k] {ι : Type v} (a : ι → k) (i : ι) :
    polynomialTranslation a (X i) = X i - C (a i) := by
  change MvPolynomial.aeval (fun j ↦ X j - C (a j)) (X i) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem polynomialTranslation_C
    {k : Type u} [CommRing k] {ι : Type v} (a : ι → k) (r : k) :
    polynomialTranslation a (C r) = C r := by
  change MvPolynomial.aeval (fun j ↦ X j - C (a j)) (C r) = _
  exact MvPolynomial.aeval_C _ _

@[simp] theorem polynomialTranslation_symm_X
    {k : Type u} [CommRing k] {ι : Type v} (a : ι → k) (i : ι) :
    (polynomialTranslation a).symm (X i) = X i + C (a i) := by
  change MvPolynomial.aeval (fun j ↦ X j + C (a j)) (X i) = _
  exact MvPolynomial.aeval_X _ _

/-- The translated coordinate map uses the values of the original
coordinates under the given algebra character. -/
def centeredCoordinateMap
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) :
    MvPolynomial (Fin n) k →ₐ[k] S :=
  g.comp (polynomialTranslation (fun i ↦ χ (g (X i)))).toAlgHom

@[simp] theorem centeredCoordinateMap_X
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) (i : Fin n) :
    centeredCoordinateMap g χ (X i) =
      g (X i) - algebraMap k S (χ (g (X i))) := by
  change g (polynomialTranslation (fun j ↦ χ (g (X j))) (X i)) = _
  rw [polynomialTranslation_X, map_sub]
  congr 1
  exact g.commutes _

/-- Every translated coordinate has value zero under the actual character. -/
theorem character_comp_centeredCoordinateMap
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) :
    χ.comp (centeredCoordinateMap g χ) =
      MvPolynomial.aeval (fun _ : Fin n ↦ (0 : k)) := by
  ext i
  simp [AlgHom.comp_apply, centeredCoordinateMap_X]

/-- Translation preserves the actual scalar factorization. -/
theorem centeredCoordinateMap_comp_C
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) :
    (centeredCoordinateMap g χ).toRingHom.comp MvPolynomial.C = algebraMap k S :=
  (centeredCoordinateMap g χ).comp_algebraMap

/-- Composing with the polynomial automorphism preserves relative
dimension-zero standard smoothness of the actual coordinate ring map. -/
theorem centeredCoordinateMap_standardSmoothZero
    {k : Type u} {S : Type v} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k)
    (hg : g.toRingHom.IsStandardSmoothOfRelativeDimension 0) :
    (centeredCoordinateMap g χ).toRingHom.IsStandardSmoothOfRelativeDimension 0 := by
  exact hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
    (polynomialTranslation (fun i ↦ χ (g (X i)))).toRingEquiv)

/-- Standard-smooth coordinates can be chosen to vanish under the given
actual character, while retaining their dimension-zero coordinate map. -/
theorem exists_centered_standardSmoothZero_coordinates
    (n : ℕ) (k : Type u) (S : Type v) [CommRing k] [CommRing S] [Algebra k S]
    [Algebra.IsStandardSmoothOfRelativeDimension n k S] (χ : S →ₐ[k] k) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k] S,
      g.toRingHom.IsStandardSmoothOfRelativeDimension 0 ∧
      χ.comp g = MvPolynomial.aeval (fun _ : Fin n ↦ (0 : k)) := by
  obtain ⟨g, hg⟩ :=
    KltDP.StandardSmoothCoordinates.exists_standardSmoothZero_mvPolynomial n k S
  exact ⟨centeredCoordinateMap g χ, centeredCoordinateMap_standardSmoothZero g χ hg,
    character_comp_centeredCoordinateMap g χ⟩

/-- The translated map of actual affine schemes is étale. -/
theorem centeredCoordinateMap_isEtale
    {k S : Type u} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k)
    (hg : g.toRingHom.IsStandardSmoothOfRelativeDimension 0) :
    IsEtale (Spec.map (CommRingCat.ofHom (centeredCoordinateMap g χ).toRingHom)) :=
  KltDP.Geometry.isEtale_spec_map_of_standardSmoothZero _
    (centeredCoordinateMap_standardSmoothZero g χ hg)

/-- The actual character diagram after translation. Over a field, its
source is the rational point defined by the character and its target
is the origin defined by evaluation of every variable at zero. -/
theorem character_centeredCoordinateMap_spec_identity
    {k S : Type u} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) :
    Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (centeredCoordinateMap g χ).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (fun _ : Fin n ↦ (0 : k))).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h : MvPolynomial (Fin n) k →ₐ[k] k ↦
    Spec.map (CommRingCat.ofHom h.toRingHom))
      (character_comp_centeredCoordinateMap g χ)

end KltDP.Geometry.EtaleCoordinates
