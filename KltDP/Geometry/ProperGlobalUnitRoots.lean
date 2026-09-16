import KltDP.Geometry.ProperGlobalSectionsConstants
import KltDP.Geometry.SplitQuadraticNaturality

/-!
# Compatible roots of actual global branch units

For an integral, universally closed, locally finite-type scheme over an
algebraically closed field, the original scalar map identifies the global
section ring with the field. Consequently an actual global unit has a unit
root of every positive order. Restricting one such global root to the actual
affine charts gives roots that agree under coefficient restriction maps.

This supplies root existence after a branch line bundle has been trivialized.
It does not prove that a degree-zero line bundle on a rational component or
tree is trivial, nor that a branch section of a nontrivial line bundle is a
global function. Root existence here is valid in every characteristic; the
quadratic splitting still separately requires invertibility of two.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace KltDP.Geometry.ProperGlobalUnitRoots

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f]

/-- A root can be chosen as a unit of the original base field. -/
theorem exists_scalar_unit_pow (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ r : kˣ, (Units.map (baseFieldToGlobalSections f).toMonoidHom r) ^ n = b := by
  obtain ⟨c, hc⟩ := (baseFieldToGlobalSections_bijective f).surjective (b : Γ(X, ⊤))
  have hc0 : c ≠ 0 := by
    intro h
    apply b.ne_zero
    simpa only [h, map_zero] using hc.symm
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hd0 : d ≠ 0 := by
    intro h
    apply hc0
    simpa only [h, zero_pow hn.ne'] using hd.symm
  refine ⟨Units.mk0 d hd0, ?_⟩
  apply Units.ext
  change (baseFieldToGlobalSections f d) ^ n = (b : Γ(X, ⊤))
  rw [← map_pow, hd, hc]

/-- The chosen field unit; all later chart roots use this single choice. -/
def scalarUnitRoot (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n) : kˣ :=
  (exists_scalar_unit_pow f b n hn).choose

/-- The root as an actual invertible global section. -/
def globalUnitRoot (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n) : Γ(X, ⊤)ˣ :=
  Units.map (baseFieldToGlobalSections f).toMonoidHom (scalarUnitRoot f b n hn)

@[simp]
theorem globalUnitRoot_pow (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n) :
    (globalUnitRoot f b n hn) ^ n = b :=
  (exists_scalar_unit_pow f b n hn).choose_spec

end KltDP.Geometry.ProperGlobalUnitRoots

namespace KltDP.Geometry.ProperGlobalUnitRoots

variable {X : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction of actual global sections to the coefficient ring of an affine chart. -/
def affineRestriction (g : Spec (.of R) ⟶ X) : Γ(X, ⊤) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp g.appTop.hom

/-- This restriction is induced by the original morphisms, with the canonical
identification of sections of an affine spectrum with its ring. -/
theorem affineRestriction_naturality (r : R →+* S)
    (gR : Spec (.of R) ⟶ X) (gS : Spec (.of S) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom r) ≫ gR = gS) :
    r.comp (affineRestriction gR) = affineRestriction gS := by
  have h : gS.appTop ≫ (Scheme.ΓSpecIso (.of S)).hom =
      gR.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom r := by
    rw [← hg, Scheme.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  exact (congrArg (fun t : Γ(X, ⊤) ⟶ CommRingCat.of S => t.hom) h).symm

/-- The actual restriction of an invertible global section is an invertible chart section. -/
def affineUnit (g : Spec (.of R) ⟶ X) (b : Γ(X, ⊤)ˣ) : Rˣ :=
  Units.map (affineRestriction g).toMonoidHom b

theorem affineUnit_naturality (r : R →+* S)
    (gR : Spec (.of R) ⟶ X) (gS : Spec (.of S) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom r) ≫ gR = gS) (b : Γ(X, ⊤)ˣ) :
    Units.map r.toMonoidHom (affineUnit gR b) = affineUnit gS b := by
  apply Units.ext
  change r (affineRestriction gR (b : Γ(X, ⊤))) =
    affineRestriction gS (b : Γ(X, ⊤))
  exact RingHom.congr_fun (affineRestriction_naturality r gR gS hg) b

end KltDP.Geometry.ProperGlobalUnitRoots

namespace KltDP.Geometry.ProperGlobalUnitRoots

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    [UniversallyClosed f] [LocallyOfFiniteType f]
    {R S : Type u} [CommRing R] [CommRing S]

include f in
/-- Invertibility of two in the original field gives the actual chart-ring
hypothesis required by quadratic splitting. -/
theorem affine_two_isUnit (h2 : IsUnit (2 : k)) (g : Spec (.of R) ⟶ X) :
    IsUnit (2 : R) := by
  have h := h2.map ((affineRestriction g).comp (baseFieldToGlobalSections f))
  simpa only [map_ofNat] using h

/-- A chart root obtained by restricting the single global root. -/
def affineRoot (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (g : Spec (.of R) ⟶ X) : Rˣ :=
  affineUnit g (globalUnitRoot f b n hn)

@[simp]
theorem affineRoot_pow (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (g : Spec (.of R) ⟶ X) :
    (affineRoot f b n hn g) ^ n = affineUnit g b := by
  change (Units.map (affineRestriction g).toMonoidHom (globalUnitRoot f b n hn)) ^ n =
    Units.map (affineRestriction g).toMonoidHom b
  rw [← map_pow, globalUnitRoot_pow]

/-- The exact root compatibility required by `splitQuadraticMap` and its gluing adapters. -/
theorem affineRoot_restriction (b : Γ(X, ⊤)ˣ) (n : ℕ) (hn : 0 < n)
    (r : R →+* S) (gR : Spec (.of R) ⟶ X) (gS : Spec (.of S) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom r) ≫ gR = gS) :
    r (affineRoot f b n hn gR : R) = (affineRoot f b n hn gS : S) :=
  congrArg Units.val (affineUnit_naturality r gR gS hg (globalUnitRoot f b n hn))

/-- The original local branch equation equals the square-root presentation
used by the actual split quadratic quotient. -/
theorem affineBranchPolynomial_eq (b : Γ(X, ⊤)ˣ) (g : Spec (.of R) ⟶ X) :
    (Polynomial.X ^ 2 - C (affineUnit g b : R) : R[X]) =
      splitQuadraticPolynomial (affineRoot f b 2 (by decide) g) := by
  have h := congrArg Units.val (affineRoot_pow f b 2 (by decide) g)
  change (affineRoot f b 2 (by decide) g : R) ^ 2 = (affineUnit g b : R) at h
  simp only [splitQuadraticPolynomial, h]

end KltDP.Geometry.ProperGlobalUnitRoots
