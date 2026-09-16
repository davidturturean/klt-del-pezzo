import KltDP.Geometry.RationalTreePicardRestrictStalk

/-!
# Transport of cotangent data along an isomorphism of local rings

BRIEF13, part (ii). For a ring isomorphism `e : R ≃+* S` of local rings: the maximal ideals
correspond (`mem_maximalIdeal_map_iff`), the induced additive map of cotangent spaces
`cotangentMap e` (an instance of `Ideal.mapCotangent` over `ℤ`) is semilinear over
`IsLocalRing.ResidueField.mapEquiv e` (`cotangentMap_smul`, `cotangentSemilinear`), bijective
(`cotangentMap_injective`, `cotangentMap_surjective`), and therefore transports the transverse
data: a family in the maximal ideal with independent cotangent classes in a two-dimensional
cotangent space maps to such a family (`cotangent_transfer`).
-/

noncomputable section

open IsLocalRing

namespace KltDP.Geometry.RationalTreePicard

section CotangentTransport

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)

/-- A ring isomorphism of local rings preserves and reflects the maximal ideal. -/
theorem mem_maximalIdeal_map_iff (x : R) : e x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  constructor
  · intro h hx
    exact h (hx.map e)
  · intro h hex
    apply h
    have := hex.map e.symm
    rwa [e.symm_apply_apply] at this

theorem maximalIdeal_map_eq : Ideal.map e (maximalIdeal R) = maximalIdeal S := by
  rw [← Ideal.comap_symm]
  ext s
  rw [Ideal.mem_comap]
  exact mem_maximalIdeal_map_iff e.symm s

/-- The additive map of cotangent spaces induced by a ring isomorphism of local rings. -/
def cotangentMap : CotangentSpace R →ₗ[ℤ] CotangentSpace S :=
  Ideal.mapCotangent (maximalIdeal R) (maximalIdeal S) (e : R →+* S).toIntAlgHom
    (fun x hx => (mem_maximalIdeal_map_iff e x).mpr hx)

theorem cotangentMap_toCotangent (x : maximalIdeal R) :
    cotangentMap e ((maximalIdeal R).toCotangent x) =
      (maximalIdeal S).toCotangent ⟨e x, (mem_maximalIdeal_map_iff e x).mpr x.2⟩ :=
  rfl

theorem isLocalHom_toRingHom : IsLocalHom (e : R →+* S) :=
  IsLocalHom.of_surjective _ e.surjective

/-- The induced map is semilinear over the isomorphism of residue fields. -/
theorem cotangentMap_smul (a : ResidueField R) (v : CotangentSpace R) :
    cotangentMap e (a • v) = ResidueField.mapEquiv e a • cotangentMap e v := by
  haveI := isLocalHom_toRingHom e
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  have h1 : (Ideal.Quotient.mk (maximalIdeal R) r) • (maximalIdeal R).toCotangent y =
      (maximalIdeal R).toCotangent (r • y) := by
    rw [map_smul]
    rfl
  have h2 : ResidueField.mapEquiv e (Ideal.Quotient.mk (maximalIdeal R) r) =
      Ideal.Quotient.mk (maximalIdeal S) (e r) :=
    ResidueField.map_residue (e : R →+* S) r
  rw [h1, cotangentMap_toCotangent, h2, cotangentMap_toCotangent]
  have h3 : (Ideal.Quotient.mk (maximalIdeal S) (e r)) •
      (maximalIdeal S).toCotangent ⟨e y, (mem_maximalIdeal_map_iff e y).mpr y.2⟩ =
      (maximalIdeal S).toCotangent (e r • ⟨e y, (mem_maximalIdeal_map_iff e y).mpr y.2⟩) := by
    rw [map_smul]
    rfl
  rw [h3]
  congr 1
  ext
  simp [smul_eq_mul]

theorem cotangentMap_injective : Function.Injective (cotangentMap e) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨y, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  rw [cotangentMap_toCotangent, Ideal.toCotangent_eq_zero] at hv
  rw [Ideal.toCotangent_eq_zero]
  have hsq : (maximalIdeal S) ^ 2 = Ideal.map e ((maximalIdeal R) ^ 2) := by
    rw [Ideal.map_pow, maximalIdeal_map_eq]
  rw [hsq, ← Ideal.comap_symm, Ideal.mem_comap] at hv
  simpa using hv

theorem cotangentMap_surjective : Function.Surjective (cotangentMap e) := by
  intro v
  obtain ⟨⟨s, hs⟩, rfl⟩ := (maximalIdeal S).toCotangent_surjective v
  refine ⟨(maximalIdeal R).toCotangent ⟨e.symm s, (mem_maximalIdeal_map_iff e.symm s).mpr hs⟩, ?_⟩
  rw [cotangentMap_toCotangent]
  congr 1
  ext
  simp

/-- The induced map as a semilinear map over the residue-field isomorphism. -/
def cotangentSemilinear :
    CotangentSpace R →ₛₗ[(ResidueField.mapEquiv e : ResidueField R →+* ResidueField S)]
      CotangentSpace S where
  toFun := cotangentMap e
  map_add' := map_add _
  map_smul' := cotangentMap_smul e

/-- Transport of the transverse data: a family in the maximal ideal with independent cotangent
classes spanning a two-dimensional cotangent space maps to such a family. -/
theorem cotangent_transfer (h2 : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (w : Fin 2 → maximalIdeal R)
    (hind : LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (w i))) :
    Module.finrank (ResidueField S) (CotangentSpace S) = 2 ∧
      LinearIndependent (ResidueField S) (fun i => (maximalIdeal S).toCotangent
        ⟨e (w i), (mem_maximalIdeal_map_iff e (w i)).mpr (w i).2⟩) := by
  have hcomp : (fun i => (maximalIdeal S).toCotangent
      ⟨e (w i), (mem_maximalIdeal_map_iff e (w i)).mpr (w i).2⟩) =
      (cotangentSemilinear e) ∘ (fun i => (maximalIdeal R).toCotangent (w i)) := by
    funext i
    exact (cotangentMap_toCotangent e (w i)).symm
  have hindS : LinearIndependent (ResidueField S) (fun i => (maximalIdeal S).toCotangent
      ⟨e (w i), (mem_maximalIdeal_map_iff e (w i)).mpr (w i).2⟩) := by
    rw [hcomp]
    have := hind.map_of_injective_injective (ResidueField.mapEquiv e).symm
      (cotangentSemilinear e).toAddMonoidHom
      (fun r hr => by rw [← (ResidueField.mapEquiv e).apply_symm_apply r, hr, map_zero])
      (fun m hm => cotangentMap_injective e (by rw [map_zero]; exact hm))
      (fun r m => by
        change cotangentMap e ((ResidueField.mapEquiv e).symm r • m) = r • cotangentMap e m
        rw [cotangentMap_smul, RingEquiv.apply_symm_apply])
    exact this
  refine ⟨?_, hindS⟩
  haveI : RingHomSurjective (ResidueField.mapEquiv e : ResidueField R →+* ResidueField S) :=
    ⟨(ResidueField.mapEquiv e).surjective⟩
  let b : Basis (Fin 2) (ResidueField R) (CotangentSpace R) :=
    basisOfLinearIndependentOfCardEqFinrank hind (by rw [h2, Fintype.card_fin])
  have hb : Set.range b = Set.range (fun i => (maximalIdeal R).toCotangent (w i)) := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hspan : ⊤ ≤ Submodule.span (ResidueField S) (Set.range (fun i => (maximalIdeal S).toCotangent
      ⟨e (w i), (mem_maximalIdeal_map_iff e (w i)).mpr (w i).2⟩)) := by
    have hsurj : Function.Surjective (cotangentSemilinear e) := cotangentMap_surjective e
    rw [hcomp, Set.range_comp, ← Submodule.map_span (cotangentSemilinear e), ← hb, b.span_eq,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr hsurj).ge
  exact (Module.finrank_eq_card_basis (Basis.mk hindS hspan)).trans (Fintype.card_fin 2)

end CotangentTransport

end KltDP.Geometry.RationalTreePicard
