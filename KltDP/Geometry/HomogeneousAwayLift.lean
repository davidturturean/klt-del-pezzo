import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Ring homomorphisms out of a homogeneous localization `A_{(f)}`

Two ring maps out of the pinned `HomogeneousLocalization.Away 𝒜 f` are equal as soon as they agree
on every fraction `Away.mk 𝒜 hf n a ha = a / f ^ n` (pinned `Away.mk_surjective`); and a ring map
`g : A →+* P` with `g f * v = 1` induces `lift 𝒜 g v hv : Away 𝒜 f →+* P`, `a / f ^ n ↦ g a * v ^ n`
(the pinned `Localization.awayLift` restricted along the inclusion into the ordinary localization,
the construction of the accepted `ProjectiveChart.dehomogenize`). Constants of degree zero are sent
to their image under `g`.

These are the tools with which chart-by-chart morphisms into `Proj 𝒜` are defined and compared on
overlaps; no scheme is mentioned here.
-/

noncomputable section

namespace KltDP.Geometry.HomogeneousAway

variable {R A P : Type*} [CommRing R] [CommRing A] [CommRing P] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A}

/-- Two ring maps out of `A_{(f)}` agreeing on every fraction `a / f ^ n` are equal. -/
theorem ringHom_ext {d : ℕ} (hf : f ∈ 𝒜 d)
    {φ ψ : HomogeneousLocalization.Away 𝒜 f →+* P}
    (h : ∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)),
      φ (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
        ψ (HomogeneousLocalization.Away.mk 𝒜 hf n a ha)) : φ = ψ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  exact h n a ha

/-- The ring map `A_{(f)} →+* P` induced by `g : A →+* P` with `g f * v = 1`. -/
def lift (g : A →+* P) (v : P) (hv : g f * v = 1) :
    HomogeneousLocalization.Away 𝒜 f →+* P :=
  (Localization.awayLift g f (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

/-- The lift sends the fraction `a / f ^ n` to `g a * v ^ n`. -/
theorem lift_mk {d : ℕ} (hf : f ∈ 𝒜 d) (g : A →+* P) (v : P) (hv : g f * v = 1)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    lift 𝒜 g v hv (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) = g a * v ^ n := by
  change Localization.awayLift g f (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
    (Localization.mk a ⟨f ^ n, n, rfl⟩) = _
  exact Localization.awayLift_mk g f a v hv n

/-- The lift sends a degree-zero constant to its image under `g`. -/
theorem lift_fromZeroRingHom (g : A →+* P) (v : P) (hv : g f * v = 1) (a : 𝒜 0) :
    lift 𝒜 g v hv (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      g a := by
  change Localization.awayLift g f (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
    (Localization.mk (a : A) 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.Away.lift_eq f (isUnit_iff_exists_inv.mpr ⟨v, hv⟩) (a : A)

end KltDP.Geometry.HomogeneousAway
