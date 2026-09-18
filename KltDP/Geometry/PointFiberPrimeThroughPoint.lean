import KltDP.Geometry.ConnectedPointFiberComponents
import KltDP.Geometry.PointClosureCurve

/-!
The nontrivial irreducible closed subsets produced inside an original
connected point fiber are actual prime curves of the original surface.
The accepted point-closure dimension theorem supplies dimension one.
Surjectivity onto a nontrivial target rules out a fiber filling the whole
surface; no dimension, curve-cover, or fiber-exhaustion premise is used.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.ConnectedPointFiberComponents

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original nontrivial proper irreducible closed carrier is a prime
curve, using the existing dimension theorem for its actual generic point. -/
def primeCurveOfProperNontrivialClosed (Z : IrreducibleCloseds X.toScheme)
    (hnt : (Z : Set X.toScheme).Nontrivial) (hne : (Z : Set X.toScheme) ≠ Set.univ) :
    X.PrimeCurve := by
  let z : X.toScheme := Z.isIrreducible.genericPoint
  have hclosure : closure ({z} : Set X.toScheme) = (Z : Set X.toScheme) :=
    Z.isIrreducible.closure_genericPoint Z.isClosed
  have hgeneric : z ≠ genericPoint X.toScheme := by
    intro h
    apply hne
    rw [← hclosure, h, genericPoint_closure]
  have hclosed : ¬ IsClosed ({z} : Set X.toScheme) := by
    intro hz
    have hsing : (Z : Set X.toScheme) = {z} := by
      rw [← hclosure, hz.closure_eq]
    exact Set.subsingleton_singleton.not_nontrivial (hsing ▸ hnt)
  refine ⟨Z, ?_⟩
  have hd := X.pointClosure_dimension_eq_one z hgeneric hclosed
  change topologicalKrullDim (closure ({z} : Set X.toScheme)) = 1 at hd
  rwa [hclosure] at hd

@[simp] theorem coe_primeCurveOfProperNontrivialClosed
    (Z : IrreducibleCloseds X.toScheme) (hnt : (Z : Set X.toScheme).Nontrivial)
    (hne : (Z : Set X.toScheme) ≠ Set.univ) :
    (primeCurveOfProperNontrivialClosed X Z hnt hne : Set X.toScheme) = Z := rfl

/-- A point fiber of a surjective map to a nontrivial target cannot fill
the original source. -/
theorem pointFiber_ne_univ {Y : Scheme.{u}} [Nontrivial Y]
    (f : X.toScheme ⟶ Y) [Surjective f] (y : Y) :
    f.base ⁻¹' {y} ≠ Set.univ := by
  intro hfull
  obtain ⟨z, hzy⟩ := exists_ne y
  obtain ⟨x, hx⟩ := (inferInstance : Surjective f).surj z
  have hxy : x ∈ f.base ⁻¹' {y} := by
    rw [hfull]
    exact Set.mem_univ x
  exact hzy (hx.symm.trans hxy)

/-- Every point of a connected closed fiber containing a contracted
prime lies on an actual original prime contained in that same fiber. -/
theorem exists_primeCurve_through_point {Y : Scheme.{u}} [Nontrivial Y]
    (f : X.toScheme ⟶ Y) [Surjective f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) (hconnected : IsConnected (f.base ⁻¹' {y}))
    (C : X.PrimeCurve) (hC : ∀ z ∈ (C : Set X.toScheme), f.base z = y)
    (x : X.toScheme) (hx : f.base x = y) :
    ∃ B : X.PrimeCurve, x ∈ (B : Set X.toScheme) ∧
      ∀ z ∈ (B : Set X.toScheme), f.base z = y := by
  obtain ⟨Z, hxZ, hnt, hZfiber⟩ :=
    exists_irreducibleClosed_in_pointFiber X f y hy hconnected C hC x hx
  have hne : (Z : Set X.toScheme) ≠ Set.univ := by
    intro hZ
    apply pointFiber_ne_univ X f y
    exact Set.Subset.antisymm (Set.subset_univ _) (hZ ▸ hZfiber)
  exact ⟨primeCurveOfProperNontrivialClosed X Z hnt hne, hxZ,
    fun z hz => hZfiber hz⟩

end KltDP.Geometry.ConnectedPointFiberComponents
