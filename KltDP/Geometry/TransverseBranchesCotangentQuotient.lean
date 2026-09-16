import KltDP.Geometry.RegularLocalParameterQuotient
import KltDP.Geometry.RationalTreePicardCotangentTransport

/-!
# Cotangent data of a transversal-crossing quotient

BRIEF18, task 1 (algebraic part). Let `φ : R →+* T` be a surjective local homomorphism of local
rings.

* If `RingHom.ker φ ≤ m_R ^ 2`, the semilinear cotangent map `cotangentSemilinearMap φ` of the
  accepted `RegularLocalParameterQuotient` is injective (`cotangentSemilinearMap_injective`), hence
  bijective, and it transports a family with independent cotangent classes in a two-dimensional
  cotangent space of `R` to such a family in `T` (`cotangent_transfer_of_surjective`; the
  isomorphism case is the lane's `cotangent_transfer`).
* Two generators `f, g` of the maximal ideal of a local ring with two-dimensional cotangent space
  have independent cotangent classes (`linearIndependent_toCotangent_of_span_pair_eq`).
* The transversal-crossing normal form: if `(f, g) = m_R`, `RingHom.ker φ = (f g)` and
  `dim m_R/m_R² = 2`, then the cotangent space of `T` is two-dimensional and the classes of
  `φ f`, `φ g` are independent (`transverse_of_crossing_quotient`).
* A regular local ring of Krull dimension two has a two-dimensional cotangent space
  (`finrank_cotangentSpace_eq_two_of_regularLocal`, from the project's `RegularLocal` predicate).

Everything is proved; no geometric hypothesis enters here.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.Geometry.RationalTreePicard

open KltDP.Geometry.RegularLocalParameterQuotient

section Quotient

variable {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
  (φ : R →+* T) [IsLocalHom φ]

/-- If the kernel of a surjective local homomorphism lies in the square of the maximal ideal,
the induced map of cotangent spaces is injective. -/
theorem cotangentSemilinearMap_injective (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ (maximalIdeal R) ^ 2) :
    Function.Injective (cotangentSemilinearMap φ) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  have hmem := (cotangent_map_zero_iff φ hφ a).mp hv
  rw [sup_eq_left.mpr hker] at hmem
  exact (Ideal.toCotangent_eq_zero _ a).mpr hmem

/-- The residue-field isomorphism induced by a surjective local homomorphism. -/
def residueFieldEquivOfSurjective (hφ : Function.Surjective φ) :
    ResidueField R ≃+* ResidueField T :=
  RingEquiv.ofBijective (ResidueField.map φ) (residueField_map_bijective φ hφ)

theorem residueFieldEquivOfSurjective_apply (hφ : Function.Surjective φ) (c : ResidueField R) :
    residueFieldEquivOfSurjective φ hφ c = ResidueField.map φ c := rfl

/-- The cotangent map evaluated on the class of a maximal-ideal element. -/
theorem cotangentSemilinearMap_toCotangent (a : maximalIdeal R) :
    cotangentSemilinearMap φ ((maximalIdeal R).toCotangent a) =
      (maximalIdeal T).toCotangent ⟨φ a, map_nonunit φ a a.2⟩ :=
  localCotangentMap_toCotangent φ a

/-- Transport of the transverse data along a surjective local homomorphism whose kernel lies in
the square of the maximal ideal: a family in the maximal ideal with independent cotangent classes
spanning a two-dimensional cotangent space maps to such a family. -/
theorem cotangent_transfer_of_surjective (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ (maximalIdeal R) ^ 2)
    (h2 : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (w : Fin 2 → maximalIdeal R)
    (hind : LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (w i))) :
    Module.finrank (ResidueField T) (CotangentSpace T) = 2 ∧
      LinearIndependent (ResidueField T) (fun i => (maximalIdeal T).toCotangent
        ⟨φ (w i), map_nonunit φ (w i) (w i).2⟩) := by
  have hcomp : (fun i => (maximalIdeal T).toCotangent ⟨φ (w i), map_nonunit φ (w i) (w i).2⟩) =
      (cotangentSemilinearMap φ) ∘ (fun i => (maximalIdeal R).toCotangent (w i)) := by
    funext i
    exact (cotangentSemilinearMap_toCotangent φ (w i)).symm
  have hinj := cotangentSemilinearMap_injective φ hφ hker
  have hsurj := cotangentSemilinearMap_surjective φ hφ
  let ε := residueFieldEquivOfSurjective φ hφ
  have hindT : LinearIndependent (ResidueField T) (fun i => (maximalIdeal T).toCotangent
      ⟨φ (w i), map_nonunit φ (w i) (w i).2⟩) := by
    rw [hcomp]
    exact hind.map_of_injective_injective ε.symm (cotangentSemilinearMap φ).toAddMonoidHom
      (fun r hr => by rw [← ε.apply_symm_apply r, hr, map_zero])
      (fun m hm => hinj (by rw [map_zero]; exact hm))
      (fun r m => by
        change cotangentSemilinearMap φ (ε.symm r • m) = r • cotangentSemilinearMap φ m
        rw [(cotangentSemilinearMap φ).map_smulₛₗ]
        rw [show ResidueField.map φ (ε.symm r) = r from ε.apply_symm_apply r])
  refine ⟨?_, hindT⟩
  haveI : RingHomSurjective (ResidueField.map φ) := ⟨(residueField_map_bijective φ hφ).2⟩
  let b : Basis (Fin 2) (ResidueField R) (CotangentSpace R) :=
    basisOfLinearIndependentOfCardEqFinrank hind (by rw [h2, Fintype.card_fin])
  have hb : Set.range b = Set.range (fun i => (maximalIdeal R).toCotangent (w i)) := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hspan : ⊤ ≤ Submodule.span (ResidueField T) (Set.range (fun i =>
      (maximalIdeal T).toCotangent ⟨φ (w i), map_nonunit φ (w i) (w i).2⟩)) := by
    rw [hcomp, Set.range_comp, ← Submodule.map_span (cotangentSemilinearMap φ), ← hb, b.span_eq,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr hsurj).ge
  exact (Module.finrank_eq_card_basis (Basis.mk hindT hspan)).trans (Fintype.card_fin 2)

omit [IsLocalRing T] [IsLocalHom φ] in
/-- The kernel `(f g)` with `f, g` in the maximal ideal lies in the square of the maximal
ideal. -/
theorem ker_le_sq_of_eq_span_mul {f g : R} (hf : f ∈ maximalIdeal R) (hg : g ∈ maximalIdeal R)
    (hker : RingHom.ker φ = Ideal.span {f * g}) : RingHom.ker φ ≤ (maximalIdeal R) ^ 2 := by
  rw [hker, Ideal.span_singleton_le_iff_mem, pow_two]
  exact Ideal.mul_mem_mul hf hg

end Quotient

section Generators

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Two generators of the maximal ideal of a local ring with two-dimensional cotangent space have
linearly independent cotangent classes. -/
theorem linearIndependent_toCotangent_of_span_pair_eq
    (h2 : Module.finrank (ResidueField R) (CotangentSpace R) = 2) (w : Fin 2 → maximalIdeal R)
    (hspan : Ideal.span {(w 0 : R), (w 1 : R)} = maximalIdeal R) :
    LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (w i)) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by rw [h2, Fintype.card_fin])
  intro v _
  obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  have hx : (x : R) ∈ Ideal.span {(w 0 : R), (w 1 : R)} := by
    rw [hspan]
    exact x.2
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hx
  have hxe : x = a • w 0 + b • w 1 := by
    apply Subtype.ext
    change (x : R) = a * (w 0 : R) + b * (w 1 : R)
    exact hab.symm
  rw [hxe, map_add, map_smul, map_smul]
  exact Submodule.add_mem _
    (Submodule.smul_of_tower_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_of_tower_mem _ b (Submodule.subset_span ⟨1, rfl⟩))

/-- A regular local ring of Krull dimension two has a two-dimensional cotangent space. -/
theorem finrank_cotangentSpace_eq_two_of_regularLocal (hR : RegularLocal R)
    (hdim : ringKrullDim R = 2) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 2 := by
  have h := hR.2
  rw [hdim] at h
  exact_mod_cast h.symm

end Generators

section Crossing

variable {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
  (φ : R →+* T) [IsLocalHom φ]

/-- The transversal-crossing normal form: for a surjective local homomorphism `φ : R →+* T` with
kernel `(f g)`, where `f, g` generate the maximal ideal of `R` and the cotangent space of `R` is
two-dimensional, the cotangent space of `T` is two-dimensional and the cotangent classes of
`φ f`, `φ g` are linearly independent. -/
theorem transverse_of_crossing_quotient (hφ : Function.Surjective φ)
    (h2 : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (w : Fin 2 → maximalIdeal R)
    (hspan : Ideal.span {(w 0 : R), (w 1 : R)} = maximalIdeal R)
    (hker : RingHom.ker φ = Ideal.span {(w 0 : R) * (w 1 : R)}) :
    Module.finrank (ResidueField T) (CotangentSpace T) = 2 ∧
      LinearIndependent (ResidueField T) (fun i => (maximalIdeal T).toCotangent
        ⟨φ (w i), map_nonunit φ (w i) (w i).2⟩) :=
  cotangent_transfer_of_surjective φ hφ (ker_le_sq_of_eq_span_mul φ (w 0).2 (w 1).2 hker) h2 w
    (linearIndependent_toCotangent_of_span_pair_eq h2 w hspan)

end Crossing

end KltDP.Geometry.RationalTreePicard
