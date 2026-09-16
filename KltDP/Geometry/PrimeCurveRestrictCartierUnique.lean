import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# The restricted Cartier divisor is characterised by its chart equations

`restrictCartier D hD hC` was obtained by gluing (a `choose` from `exists_restrictCartier`). The
sheaf of Cartier divisors is separated, so the glued divisor is the *unique* Cartier divisor on `C`
whose restriction to every pulled-back generic chart `i⁻¹U_c` is the class of the restricted
equation `i^*f_c` (`restrictCartier_eq_of_forall_chart`, `eq_restrictCartier_iff`). This removes the
dependence on the choice and is the tool for computing `restrictCartier` on sums.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

include hD in
/-- The pulled-back generic charts cover the curve. -/
theorem top_le_iSup_chartPreimage :
    (⊤ : C.toScheme.Opens) ≤ iSup (fun c : C.GenericChart D => C.chartPreimage D c.1) := by
  intro y _
  obtain ⟨c, hyc⟩ := C.exists_genericChart D hD y
  exact Opens.mem_iSup.mpr ⟨c, hyc⟩

/-- **Uniqueness of the restriction**: a Cartier divisor on `C` whose restriction to every
pulled-back generic chart is the class of the restricted equation is `D|_C`. -/
theorem restrictCartier_eq_of_forall_chart (E : CartierDivisor C.toScheme)
    (hE : ∀ c : C.GenericChart D,
      letI : Nonempty (C.chartPreimage D c.1) :=
        ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
      (cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op E =
        cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
          (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC))) :
    E = C.restrictCartier D hD hC :=
  (cartierDivisorSheaf C.toScheme).eq_of_locally_eq'
    (fun c : C.GenericChart D => C.chartPreimage D c.1) ⊤
    (fun c => homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top))
    (C.top_le_iSup_chartPreimage D hD) E (C.restrictCartier D hD hC)
    (fun c => (hE c).trans (C.restrictCartier_spec D hD hC c).symm)

/-- **Characterisation of `D|_C` without choice**: `E = D|_C` iff `E` restricts on every
pulled-back generic chart to the class of the restricted equation. -/
theorem eq_restrictCartier_iff (E : CartierDivisor C.toScheme) :
    E = C.restrictCartier D hD hC ↔
      ∀ c : C.GenericChart D,
        letI : Nonempty (C.chartPreimage D c.1) :=
          ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D c.1 c.2⟩⟩
        (cartierDivisorSheaf C.toScheme).val.map
            (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op E =
          cartierEquationClassHom C.toScheme (C.chartPreimage D c.1)
            (Additive.ofMul (C.restrictedEquation D hD c.1 c.2 hC)) := by
  constructor
  · intro h c
    rw [h]
    exact C.restrictCartier_spec D hD hC c
  · intro h
    exact C.restrictCartier_eq_of_forall_chart D hD hC E h

include hD in
/-- Two Cartier divisors on the curve agreeing on a cover indexed by generic charts of `D` are
equal (the separatedness used above, in the form needed for sums). -/
theorem cartierDivisor_eq_of_forall_chartPreimage (E E' : CartierDivisor C.toScheme)
    (h : ∀ c : C.GenericChart D,
      (cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op E =
        (cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top)).op E') :
    E = E' :=
  (cartierDivisorSheaf C.toScheme).eq_of_locally_eq'
    (fun c : C.GenericChart D => C.chartPreimage D c.1) ⊤
    (fun c => homOfLE (show C.chartPreimage D c.1 ≤ ⊤ from le_top))
    (C.top_le_iSup_chartPreimage D hD) E E' h

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
