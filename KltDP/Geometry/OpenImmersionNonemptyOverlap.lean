import KltDP.Geometry.OpenImmersionFunctionFieldFunctorial

/-!
# An original nonempty open overlap for two integral open immersions

The open is the literal inverse image of the other original open range.
Generic points derive nonemptiness; the original lift supplies its map
and triangle. The overlap is not required to contain a specified point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenImmersionRational

/-- Two original nonempty integral open neighborhoods have an actual
nonempty open overlap, expressed as an open of the first source. -/
theorem exists_nonempty_open_overlap
    {V W₁ W₂ : Scheme.{u}} [IsIntegral V] [IsIntegral W₁] [IsIntegral W₂]
    (i₁ : W₁ ⟶ V) (i₂ : W₂ ⟶ V)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] :
    ∃ (Z : W₁.Opens) (hne : Nonempty Z.toScheme) (j : Z.toScheme ⟶ W₂),
      IsOpenImmersion j ∧ Z.ι ≫ i₁ = j ≫ i₂ := by
  let Z : W₁.Opens := i₁ ⁻¹ᵁ i₂.opensRange
  letI : Nonempty i₂.opensRange := ⟨⟨i₂.base (genericPoint W₂),
    ⟨genericPoint W₂, rfl⟩⟩⟩
  letI : Nonempty Z := preimage_nonempty i₁ i₂.opensRange
  letI : Nonempty Z.toScheme := ⟨Classical.choice (inferInstance : Nonempty Z)⟩
  have hrange : Set.range (Z.ι ≫ i₁).base ⊆ Set.range i₂.base := by
    rintro _ ⟨y, rfl⟩
    exact y.property
  let j : Z.toScheme ⟶ W₂ := IsOpenImmersion.lift i₂ (Z.ι ≫ i₁) hrange
  have htriangle : j ≫ i₂ = Z.ι ≫ i₁ :=
    IsOpenImmersion.lift_fac i₂ (Z.ι ≫ i₁) hrange
  letI : IsOpenImmersion (j ≫ i₂) := by
    rw [htriangle]
    infer_instance
  letI : IsOpenImmersion j := IsOpenImmersion.of_comp j i₂
  exact ⟨Z, inferInstance, j, inferInstance, htriangle.symm⟩

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.exists_nonempty_open_overlap
#print axioms KltDP.Geometry.OpenImmersionRational.exists_nonempty_open_overlap
