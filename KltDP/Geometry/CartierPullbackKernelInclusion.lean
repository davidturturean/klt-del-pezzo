import KltDP.Geometry.CartierPullbackComparison
import KltDP.Geometry.SchemeKernelGluedIso

/-!
# Normalization and monicity of the original pulled Cartier ideal inclusion

The existing `pullbackKernelIso` is the original monic factor glued from
regular Cartier charts. Its inclusion formula is an instance of the existing
public gluing formula, and identifies the original pulled kernel inclusion
with an isomorphism followed by the original pulled divisor's kernel inclusion.
Consequently that original pulled inclusion is a monomorphism.

The existing kernel/glued-kernel isomorphism also retains the original
inclusion. Pulling this formula transfers monicity to an actual morphism
whose kernel ideal data is that of the regular effective Cartier divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace KltDP.Geometry

private theorem eqToIso_inclusion {C : Type u} [Category.{v} C]
    {A : Type w} (K : A → C) {Q : C} (i : ∀ a, K a ⟶ Q)
    {a b : A} (h : a = b) (p : K a = K b) :
    (eqToIso p).hom ≫ i b = i a := by
  rw [Subsingleton.elim p (congrArg K h)]
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

private theorem originalIso_inclusion {C : Type u} [Category.{v} C]
    {M N N' Q : C} (e : M ≅ N') (e₀ : M ≅ N) (t : N ≅ N')
    (j : N' ⟶ Q) (j₀ : N ⟶ Q) (a : M ⟶ Q)
    (he : e = e₀ ≪≫ t) (ht : t.hom ≫ j = j₀) (ha : e₀.hom ≫ j₀ = a) :
    e.hom ≫ j = a := by
  rw [he, Iso.trans_hom, Category.assoc, ht, ha]

variable {X Y Z : Scheme.{u}}

private def kernelIdealGluedIso_factorization (g : Z ⟶ Y) [QuasiCompact g]
    [(schemeKernelIdeal g).IsQuasicoherent] :=
  (rfl : kernelIdealGluedIso g =
    monicImageGluedKernelIso (schemeKernelIdealι g) ≪≫ eqToIso _)

private def kernelIdealGluedIso_inclusion_proof (g : Z ⟶ Y) [QuasiCompact g]
    [(schemeKernelIdeal g).IsQuasicoherent] :=
  originalIso_inclusion
    (kernelIdealGluedIso g) (monicImageGluedKernelIso (schemeKernelIdealι g)) _
    (schemeKernelIdealι g.ker.gluedTo) _ (schemeKernelIdealι g)
    (kernelIdealGluedIso_factorization g)
    (eqToIso_inclusion (fun I : Y.IdealSheafData => schemeKernelIdeal I.gluedTo)
      (fun I => schemeKernelIdealι I.gluedTo) (ofMorphism_schemeKernelIdealι g) _)
    (monicImageGluedKernelIso_inclusion (schemeKernelIdealι g))

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The existing kernel/glued-kernel isomorphism preserves the original
inclusion into the structure module:
`(kernelIdealGluedIso g).hom ≫ schemeKernelIdealι g.ker.gluedTo = schemeKernelIdealι g`.
The transparent inferred proposition retains the original maps and their
computed sheaf-instance proofs. -/
theorem kernelIdealGluedIso_inclusion (g : Z ⟶ Y) [QuasiCompact g]
    [(schemeKernelIdeal g).IsQuasicoherent] :
    statementOf (kernelIdealGluedIso_inclusion_proof g) :=
  kernelIdealGluedIso_inclusion_proof g

/-- Actual pullback retains the original kernel/glued-kernel normalization,
including the prescribed comparison with the structure module. -/
theorem pulledKernelIdealGluedIso_inclusion (g : Z ⟶ Y) [QuasiCompact g]
    [(schemeKernelIdeal g).IsQuasicoherent] (π : X ⟶ Y) :
    (schemeModulePullback π).map (kernelIdealGluedIso g).hom ≫
        pulledKernelInclusion g.ker.gluedTo π = pulledKernelInclusion g π := by
  let F := schemeModulePullback π
  let e := kernelIdealGluedIso g
  let i := schemeKernelIdealι g.ker.gluedTo
  let t := (schemeModulePullbackUnitIso π).hom
  have h := congrArg (fun a => F.map a ≫ t) (kernelIdealGluedIso_inclusion g)
  exact (Category.assoc (F.map e.hom) (F.map i) t).symm.trans
    ((congrArg (fun a => a ≫ t) (F.map_comp e.hom i).symm).trans h)

end KltDP.Geometry

namespace KltDP.Geometry.CartierPullbackComparison

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackIdeal

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y)
  [GenericPointPreserving π] (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)

/-- The existing Cartier pullback isomorphism preserves the original ideal
inclusions and the existing normalization of the structure module. -/
@[reassoc] theorem pullbackKernelIso_comp :
    (pullbackKernelIso π D hD).hom ≫
        schemeKernelIdealι (pullbackIdealData π D hD).gluedTo =
      pulledKernelInclusion
        (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π := by
  letI : Mono (schemeKernelIdealι (pullbackIdealData π D hD).gluedTo) := by
    unfold schemeKernelIdealι
    infer_instance
  unfold pullbackKernelIso
  apply schemeModuleMonicFactorIsoOnOpenCover_comp

/-- Pulling the original ideal inclusion of a regular effective Cartier divisor
along a generic-point-preserving morphism of integral schemes remains monic. -/
theorem pulledKernelInclusion_mono_of_regularCartier :
    Mono (pulledKernelInclusion
      (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π) := by
  letI : Mono (schemeKernelIdealι (pullbackIdealData π D hD).gluedTo) := by
    unfold schemeKernelIdealι
    infer_instance
  rw [← pullbackKernelIso_comp π D hD]
  infer_instance

/-- The original pulled inclusion of an actual morphism is monic when its
kernel ideal data is that of the regular effective Cartier divisor. -/
theorem pulledKernelInclusion_mono_of_regularCartier_kernel {Z : Scheme.{u}}
    (g : Z ⟶ Y) [QuasiCompact g] [(schemeKernelIdeal g).IsQuasicoherent]
    (hI : effectiveCartierIdealDataOfRegularEquations Y D hD = g.ker) :
    Mono (pulledKernelInclusion g π) := by
  letI : Mono (pulledKernelInclusion g.ker.gluedTo π) := by
    rw [← hI]
    exact pulledKernelInclusion_mono_of_regularCartier π D hD
  rw [← pulledKernelIdealGluedIso_inclusion g π]
  infer_instance

end KltDP.Geometry.CartierPullbackComparison
