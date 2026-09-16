import KltDP.Geometry.SingularPoints
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Regularity under isomorphisms of actual local rings

A local ring map induces a map on the actual quotient `m/m²`. For a ring
isomorphism the induced cotangent maps are inverse, and they are semilinear
over the induced residue-field isomorphism. This proves equality of cotangent
dimensions without changing either module's scalar action. Noetherianity and
Krull dimension then transport regularity across the given ring isomorphism.
-/

noncomputable section

open IsLocalRing AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

section CotangentMaps

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- The actual map on maximal-ideal cotangent spaces induced by a local ring
homomorphism. It is initially bundled as a `ℤ`-linear map; the stronger scalar
compatibility with the source and residue fields is proved below. -/
def localCotangentMap (f : R →+* S) [IsLocalHom f] :
    CotangentSpace R →ₗ[ℤ] CotangentSpace S :=
  Ideal.mapCotangent (R := ℤ) (maximalIdeal R) (maximalIdeal S) f.toIntAlgHom
    (fun a ha ↦ map_nonunit f a ha)

@[simp]
theorem localCotangentMap_toCotangent (f : R →+* S) [IsLocalHom f]
    (a : maximalIdeal R) :
    localCotangentMap f ((maximalIdeal R).toCotangent a) =
      (maximalIdeal S).toCotangent ⟨f a, map_nonunit f a a.2⟩ := rfl

/-- Ring scalars commute with the quotient map under the original ring
homomorphism, not an arbitrarily installed algebra structure. -/
theorem localCotangentMap_smul (f : R →+* S) [IsLocalHom f]
    (r : R) (x : CotangentSpace R) :
    localCotangentMap f (r • x) = f r • localCotangentMap f x := by
  obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rw [← (maximalIdeal R).toCotangent.map_smul r a,
    localCotangentMap_toCotangent, localCotangentMap_toCotangent,
    ← (maximalIdeal S).toCotangent.map_smul]
  congr 1
  apply Subtype.ext
  exact f.map_mul r a

/-- The cotangent map of a ring isomorphism is inverted by the map of its
inverse; equality is checked on genuine maximal-ideal representatives. -/
theorem localCotangentMap_symm_apply (e : R ≃+* S) (x : CotangentSpace R) :
    localCotangentMap (e.symm : S →+* R) (localCotangentMap (e : R →+* S) x) = x := by
  obtain ⟨a, rfl⟩ := (maximalIdeal R).toCotangent_surjective x
  rw [localCotangentMap_toCotangent, localCotangentMap_toCotangent]
  congr 1
  apply Subtype.ext
  exact e.symm_apply_apply a

theorem localCotangentMap_apply_symm (e : R ≃+* S) (x : CotangentSpace S) :
    localCotangentMap (e : R →+* S) (localCotangentMap (e.symm : S →+* R) x) = x := by
  obtain ⟨a, rfl⟩ := (maximalIdeal S).toCotangent_surjective x
  rw [localCotangentMap_toCotangent, localCotangentMap_toCotangent]
  congr 1
  apply Subtype.ext
  exact e.apply_symm_apply a

/-- The underlying additive equivalence of the actual cotangent spaces. -/
def localCotangentAddEquiv (e : R ≃+* S) : CotangentSpace R ≃+ CotangentSpace S where
  toFun := localCotangentMap (e : R →+* S)
  invFun := localCotangentMap (e.symm : S →+* R)
  left_inv := localCotangentMap_symm_apply e
  right_inv := localCotangentMap_apply_symm e
  map_add' := (localCotangentMap (e : R →+* S)).map_add

/-- The induced cotangent equivalence is semilinear over the induced
isomorphism of actual residue fields. -/
theorem localCotangentAddEquiv_smul (e : R ≃+* S)
    (c : ResidueField R) (x : CotangentSpace R) :
    localCotangentAddEquiv e (c • x) =
      ResidueField.mapEquiv e c • localCotangentAddEquiv e x := by
  obtain ⟨r, rfl⟩ := residue_surjective c
  change localCotangentMap (e : R →+* S) (residue R r • x) =
    ResidueField.map (e : R →+* S) (residue R r) • localCotangentMap (e : R →+* S) x
  rw [ResidueField.map_residue]
  change localCotangentMap (e : R →+* S) ((algebraMap R (ResidueField R) r) • x) =
    (algebraMap S (ResidueField S) (e r)) • localCotangentMap (e : R →+* S) x
  rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
  exact localCotangentMap_smul (e : R →+* S) r x

/-- Cotangent dimension is invariant under an actual local-ring isomorphism.
The proof compares the original residue-field module structures directly. -/
theorem cotangent_finrank_eq_of_ringEquiv (e : R ≃+* S) :
    Module.finrank (ResidueField R) (CotangentSpace R) =
      Module.finrank (ResidueField S) (CotangentSpace S) := by
  simpa only [Module.finrank] using congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (ResidueField.mapEquiv e) (localCotangentAddEquiv e)
      (ResidueField.mapEquiv e).bijective (localCotangentAddEquiv_smul e))

/-- Regularity transports across the given isomorphism, using Noetherianity,
Krull dimension, and the proved cotangent-space transport separately. -/
theorem regularLocal_of_ringEquiv (e : R ≃+* S) (hR : RegularLocal R) :
    RegularLocal S := by
  letI : IsNoetherianRing R := hR.1
  refine ⟨isNoetherianRing_of_ringEquiv R e, ?_⟩
  calc
    ringKrullDim S = ringKrullDim R := (ringKrullDim_eq_of_ringEquiv e).symm
    _ = (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := hR.2
    _ = (Module.finrank (ResidueField S) (CotangentSpace S) : WithBot ℕ∞) :=
      congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞)) (cotangent_finrank_eq_of_ringEquiv e)

/-- Invariance of the project's regular-local predicate under an actual
ring isomorphism of local commutative rings. -/
theorem regularLocal_iff_of_ringEquiv (e : R ≃+* S) :
    RegularLocal R ↔ RegularLocal S :=
  ⟨regularLocal_of_ringEquiv e, regularLocal_of_ringEquiv e.symm⟩

end CotangentMaps

/-- An open immersion identifies the actual local rings at corresponding
points, so regularity is unchanged on an affine or other open neighborhood. -/
theorem regularPoint_iff_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    RegularPoint X x ↔ RegularPoint Y (f.base x) :=
  (regularLocal_iff_of_ringEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

/-- The regular locus restricts to an open subscheme as the inverse image of
the original regular locus. This is a compatibility theorem, not an assertion
that either locus is open. -/
theorem regularLocus_preimage_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    regularLocus X = f.base ⁻¹' regularLocus Y := by
  ext x
  exact regularPoint_iff_of_isOpenImmersion f x

/-- Singular points likewise restrict along actual open immersions. -/
theorem singularLocus_preimage_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    singularLocus X = f.base ⁻¹' singularLocus Y := by
  ext x
  exact not_congr (regularPoint_iff_of_isOpenImmersion f x)

end KltDP.Geometry
