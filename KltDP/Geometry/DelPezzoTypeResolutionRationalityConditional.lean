import KltDP.Geometry.DelPezzoType
import KltDP.Geometry.ResolutionRationality
import KltDP.Geometry.SurfaceEulerStructureSheaf
import KltDP.Geometry.GeneralMinimalResolutionExistence

/-!
# Conditional whole-surface rationality for original minimal resolutions

The explicit hypothesis below is the complete scope and all conclusions
of Bernasconi Lemma 5.1 in the frozen accepted postprint: every algebraically
closed field of positive characteristic and every surface of del Pezzo
type, with its arbitrary effective rational boundary. No source declaration
or admission is introduced. Final journal collation remains unverified.

The source theorem is applied to X. Ordinary transport then proves
rationality of the whole original resolution source S over the same field.
Vanishing and Euler characteristic below remain statements about X.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

variable
  (hBernasconi : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p], 0 < p →
    ∀ (X : NormalProjectiveSurface k), IsDelPezzoType X →
      Scheme.BirationalOver X.structureMorphism
        (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ∧
      (∀ i : ℕ, 0 < i → Subsingleton
        (ModuleCohomology.H
          (StructureSheafCohomology.structureSheaf X.toScheme) i)) ∧
      ModuleCohomology.eulerCharacteristic X.structureMorphism
        (StructureSheafCohomology.structureSheaf X.toScheme) = 1)

variable {k : Type u} [Field k] [IsAlgClosed k]
  (p : ℕ) [CharP k p] (hp : 0 < p)
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

include hBernasconi p hp

/-- Retain every source conclusion on X and transport rationality through the original π. -/
theorem IsResolution.delPezzoType_conclusions_conditional
    (hπ : IsResolution S X π) (hX : IsDelPezzoType X) :
    Scheme.BirationalOver S.structureMorphism
        (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ∧
      Scheme.BirationalOver X.structureMorphism
        (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) ∧
      (∀ i : ℕ, 0 < i → Subsingleton
        (ModuleCohomology.H
          (StructureSheafCohomology.structureSheaf X.toScheme) i)) ∧
      ModuleCohomology.eulerCharacteristic X.structureMorphism
        (StructureSheafCohomology.structureSheaf X.toScheme) = 1 := by
  obtain ⟨hXrat, hH, hχ⟩ := hBernasconi k p hp X hX
  exact ⟨hπ.birationalOver_affinePlane hXrat, hXrat, hH, hχ⟩

/-- Boundary zero is derived from the original intrinsic klt del Pezzo predicate. -/
theorem IsMinimalResolution.kltDelPezzo_rationality_conditional
    (hmin : IsMinimalResolution S X π) (hX : IsKltDelPezzo X) :
    Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  (hmin.toIsResolution.delPezzoType_conclusions_conditional hBernasconi p hp
    (isDelPezzoType_of_isKltDelPezzo X hX)).1

/-- One original canonical representative occurs in both discrepancies and ampleness. -/
theorem IsMinimalResolution.rationality_of_klt_ample_multiple_conditional
    (hmin : IsMinimalResolution S X π) (KX : X.WeilDivisor)
    (hklt : IsKltWithCanonicalDivisor X KX)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : NormalProjectiveSurface.rationalizeWeilDivisor X (X.cartierToWeilHom A) =
      n • (-NormalProjectiveSurface.rationalizeWeilDivisor X KX))
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  (hmin.toIsResolution.delPezzoType_conclusions_conditional hBernasconi p hp
    (isDelPezzoType_of_klt_ample_multiple X KX hklt n hn A hA hample)).1

/-- Construct a minimal resolution of X and prove its whole source rational, conditionally. -/
theorem exists_rational_minimalResolution_of_delPezzoType_conditional
    (X : NormalProjectiveSurface k) (hX : IsDelPezzoType X) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π ∧
        Scheme.BirationalOver S.structureMorphism
          (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  exact ⟨S, π, hmin,
    (hmin.toIsResolution.delPezzoType_conclusions_conditional hBernasconi p hp hX).1⟩

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.delPezzoType_conclusions_conditional
#check @KltDP.Geometry.IsMinimalResolution.kltDelPezzo_rationality_conditional
#print axioms KltDP.Geometry.IsResolution.delPezzoType_conclusions_conditional
#print axioms KltDP.Geometry.IsMinimalResolution.kltDelPezzo_rationality_conditional
#print axioms KltDP.Geometry.IsMinimalResolution.rationality_of_klt_ample_multiple_conditional
#print axioms KltDP.Geometry.exists_rational_minimalResolution_of_delPezzoType_conditional
