import KltDP.Geometry.ProperGlobalSectionsFinite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Global sections over a finite disjoint open cover

For a scheme `Z` and a family of pairwise disjoint opens `V i` covering `Z`, the
restriction maps identify `Γ(Z, ⊤)` with the product `∏ i, Γ(Z, V i)`: injectivity
is locality of the structure sheaf, surjectivity is gluing (the compatibility
condition is vacuous because sections over the empty open form a terminal ring).

Given a base ring homomorphism `φ : k →+* Γ(Z, ⊤)` from a field, the product
identification is `k`-linear for the actions through `φ` and restriction, and the
`k`-dimension of `Γ(Z, ⊤)` is the sum of the `k`-dimensions of the `Γ(Z, V i)`.
This is the finite-product decomposition used for zero-dimensional closed
subschemes; the choice of a disjoint cover separating the points is not made here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (Z : Scheme.{u}) {ι : Type u} (V : ι → Z.Opens)

/-- Restriction of global sections to each member of a family of opens. -/
def restrictionPi : Γ(Z, ⊤) →+* (∀ i, Γ(Z, V i)) :=
  Pi.ringHom fun i => (Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom

@[simp]
theorem restrictionPi_apply (s : Γ(Z, ⊤)) (i : ι) :
    restrictionPi Z V s i = Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s := rfl

/-- Sections over the empty open form a subsingleton ring. -/
theorem sections_subsingleton_of_eq_bot {W : Z.Opens} (hW : W = ⊥) : Subsingleton Γ(Z, W) :=
  CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hW)

/-- Locality: a global section is determined by its restrictions to a cover. -/
theorem restrictionPi_injective (hcover : (⨆ i, V i) = ⊤) :
    Function.Injective (restrictionPi Z V) := by
  intro s t hst
  apply Z.sheaf.eq_of_locally_eq' V ⊤ (fun i => homOfLE le_top) hcover.ge
  intro i
  exact congrFun hst i

/-- Gluing: over a pairwise disjoint cover every family of sections glues. -/
theorem restrictionPi_surjective (hcover : (⨆ i, V i) = ⊤)
    (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥) :
    Function.Surjective (restrictionPi Z V) := by
  intro sf
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.val V sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Subsingleton.elim (Opens.infLELeft (V i) (V i)) (Opens.infLERight (V i) (V i))]
    · exact @Subsingleton.elim _ (sections_subsingleton_of_eq_bot Z (hdisj hij)) _ _
  obtain ⟨s, hs, -⟩ :=
    Z.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcover.ge sf hcompat
  exact ⟨s, funext hs⟩

/-- Global sections over a finite disjoint open cover: the product ring isomorphism. -/
def sectionsPiRingEquiv (hcover : (⨆ i, V i) = ⊤)
    (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥) :
    Γ(Z, ⊤) ≃+* (∀ i, Γ(Z, V i)) :=
  RingEquiv.ofBijective (restrictionPi Z V)
    ⟨restrictionPi_injective Z V hcover, restrictionPi_surjective Z V hcover hdisj⟩

@[simp]
theorem sectionsPiRingEquiv_apply (hcover : (⨆ i, V i) = ⊤)
    (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥) (s : Γ(Z, ⊤)) (i : ι) :
    sectionsPiRingEquiv Z V hcover hdisj s i =
      Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s := rfl

section Base

variable {k : Type u} [Field k] (φ : k →+* Γ(Z, ⊤))

/-- The base action on sections over `W` through `φ` and restriction. -/
abbrev sectionsBaseModule (W : Z.Opens) : Module k Γ(Z, W) :=
  Module.compHom Γ(Z, W) ((Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp φ)

/-- The product identification is `k`-linear. -/
def sectionsPiLinearEquiv (hcover : (⨆ i, V i) = ⊤)
    (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥) :
    letI := Module.compHom Γ(Z, ⊤) φ
    letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z φ (V i)
    Γ(Z, ⊤) ≃ₗ[k] (∀ i, Γ(Z, V i)) := by
  letI := Module.compHom Γ(Z, ⊤) φ
  letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z φ (V i)
  refine (sectionsPiRingEquiv Z V hcover hdisj).toAddEquiv.toLinearEquiv ?_
  intro r s
  funext i
  change Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (φ r * s) =
    Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (φ r) *
      Z.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s
  exact map_mul _ _ _

/-- The `k`-dimension of global sections is the sum over a finite disjoint cover. -/
theorem finrank_sections_eq_sum [Fintype ι] (hcover : (⨆ i, V i) = ⊤)
    (hdisj : Pairwise fun i j => V i ⊓ V j = ⊥)
    (hfin : letI := Module.compHom Γ(Z, ⊤) φ; Module.Finite k Γ(Z, ⊤)) :
    letI := Module.compHom Γ(Z, ⊤) φ
    letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z φ (V i)
    Module.finrank k Γ(Z, ⊤) = ∑ i, Module.finrank k Γ(Z, V i) := by
  letI := Module.compHom Γ(Z, ⊤) φ
  letI : ∀ i, Module k Γ(Z, V i) := fun i => sectionsBaseModule Z φ (V i)
  haveI := hfin
  have e := sectionsPiLinearEquiv Z V φ hcover hdisj
  haveI : ∀ i, Module.Finite k Γ(Z, V i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp e.toLinearMap)
      ((Function.surjective_eval i).comp e.surjective)
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end Base

end KltDP.Geometry
