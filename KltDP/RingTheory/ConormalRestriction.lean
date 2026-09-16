import KltDP.RingTheory.RegularPrincipalConormal

/-!
# Actual conormal maps and principal coordinates

The existing ideal cotangent map is semilinear over the actual induced
map of quotient rings. This module proves that scalar compatibility and
functoriality, then describes the map in regular principal coordinates.
No localization or flatness assumption is needed for the map itself.
-/

noncomputable section

namespace KltDP.RingTheory

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (J : Ideal A) (K : Ideal B) (φ : A →+* B) (hφ : J ≤ K.comap φ)

/-- The pinned cotangent map, retaining its underlying integer linearity. -/
def conormalMapInt : J.Cotangent →ₗ[ℤ] K.Cotangent :=
  Ideal.mapCotangent (R := ℤ) J K φ.toIntAlgHom hφ

/-- The representative formula uses the original ring homomorphism. -/
@[simp]
theorem conormalMapInt_toCotangent (x : J) :
    conormalMapInt J K φ hφ (J.toCotangent x) =
      K.toCotangent ⟨φ (x : A), hφ x.property⟩ := rfl

/-- Compatibility with the canonical quotient-ring scalar actions. -/
theorem conormalMapInt_quotient_smul (q : A ⧸ J) (v : J.Cotangent) :
    conormalMapInt J K φ hφ (q • v) =
      Ideal.quotientMap K φ hφ q • conormalMapInt J K φ hφ v := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective v
  change K.toCotangent ⟨φ (r * (x : A)), _⟩ =
    K.toCotangent ⟨φ r * φ (x : A), _⟩
  exact congrArg K.toCotangent (Subtype.ext (φ.map_mul r (x : A)))

/-- The actual conormal restriction map, semilinear over the actual
quotient-ring map. This upgrades the pinned map without changing its values. -/
def conormalMap : J.Cotangent →ₛₗ[Ideal.quotientMap K φ hφ] K.Cotangent where
  toFun := conormalMapInt J K φ hφ
  map_add' := (conormalMapInt J K φ hφ).map_add
  map_smul' := conormalMapInt_quotient_smul J K φ hφ

/-- The semilinear map has the same actual representative formula. -/
@[simp]
theorem conormalMap_toCotangent (x : J) :
    conormalMap J K φ hφ (J.toCotangent x) =
      K.toCotangent ⟨φ (x : A), hφ x.property⟩ := rfl

/-- The conormal restriction for the identity ring map is the identity. -/
theorem conormalMap_id (v : J.Cotangent) :
    conormalMap J J (RingHom.id A) (fun _ h => h) v = v := by
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective v
  rfl

/-- The quotient-ring maps compose as the original ring maps do. -/
theorem conormalQuotientMap_comp (L : Ideal C) (ψ : B →+* C)
    (hψ : K ≤ L.comap ψ) (q : A ⧸ J) :
    Ideal.quotientMap L ψ hψ (Ideal.quotientMap K φ hφ q) =
      Ideal.quotientMap L (ψ.comp φ) (fun _ hx => hψ (hφ hx)) q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

/-- Actual conormal restrictions compose; the proof is on actual ideal
representatives, so no choice of principal coordinates enters it. -/
theorem conormalMap_comp (L : Ideal C) (ψ : B →+* C)
    (hψ : K ≤ L.comap ψ) (v : J.Cotangent) :
    conormalMap K L ψ hψ (conormalMap J K φ hφ v) =
      conormalMap J L (ψ.comp φ) (fun _ hx => hψ (hφ hx)) v := by
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective v
  rfl

/-- A scalar change of defining equation gives precisely that scalar
in conormal coordinates. Principality and regularity are unnecessary for
this map identity; they are used only to turn the coordinates into equivalences. -/
theorem conormalMap_principalConormalMap (d : J) (e : K) (t : B)
    (he : φ (d : A) = t * (e : B)) (q : A ⧸ J) :
    conormalMap J K φ hφ (principalConormalMap J d q) =
      principalConormalMap K e (Ideal.quotientMap K φ hφ q * Ideal.Quotient.mk K t) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [principalConormalMap_mk, conormalMap_toCotangent, Ideal.quotientMap_mk,
    ← map_mul, principalConormalMap_mk]
  apply congrArg K.toCotangent
  apply Subtype.ext
  change φ (r * (d : A)) = (φ r * t) * (e : B)
  rw [map_mul, he, mul_assoc]

/-- The same identity expressed using the proved regular principal
equivalences of source and target conormal modules. -/
theorem conormalMap_principalConormalEquiv
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (e : K) (hK : Ideal.span {(e : B)} = K) (he : (e : B) ∈ nonZeroDivisors B)
    (t : B) (ht : φ (d : A) = t * (e : B)) (q : A ⧸ J) :
    conormalMap J K φ hφ (principalConormalEquiv J d hJ hd q) =
      principalConormalEquiv K e hK he
        (Ideal.quotientMap K φ hφ q * Ideal.Quotient.mk K t) :=
  conormalMap_principalConormalMap J K φ hφ d e t ht q

/-- Inverse principal coordinates give the same quotient scalar. -/
theorem principalConormalEquiv_symm_conormalMap
    (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
    (e : K) (hK : Ideal.span {(e : B)} = K) (he : (e : B) ∈ nonZeroDivisors B)
    (t : B) (ht : φ (d : A) = t * (e : B)) (q : A ⧸ J) :
    (principalConormalEquiv K e hK he).symm
      (conormalMap J K φ hφ (principalConormalEquiv J d hJ hd q)) =
        Ideal.quotientMap K φ hφ q * Ideal.Quotient.mk K t := by
  rw [conormalMap_principalConormalEquiv J K φ hφ d hJ hd e hK he t ht,
    LinearEquiv.symm_apply_apply]

end KltDP.RingTheory
