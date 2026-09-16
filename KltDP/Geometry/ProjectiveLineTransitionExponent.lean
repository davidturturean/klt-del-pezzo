import KltDP.Geometry.ProjectiveLineTransitionUnits

/-!
# The exponent of an actual projective-line overlap unit

The pinned Laurent degree distinguishes the exponent in the proved unit
normal form. It therefore supplies a well-defined integer exponent,
additive under multiplication. On the actual projective-line overlap,
restrictions of chart units have exponent zero, so changes of the two
chart frames preserve the exponent.

The exponent is an invariant of actual section units here. It is not
identified with the degree of a divisor or a Picard class in this file.
The existing bounded pin/current/external library search is recorded in
audit/literature_candidates/node_cover_inputs/laurent_unit_library_candidates.md.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.ProjectiveLineTransitionExponent

open ProjectiveLineComparison ProjectiveLineSections ProjectiveLineTransitionUnits

variable (k : Type u) [Field k]

/-- A unit has an actual scalar-monomial expression, with the exponent first. -/
theorem exists_unit_monomial (s : (LaurentPolynomial k)ˣ) :
    ∃ n : ℤ, ∃ c : kˣ,
      (s : LaurentPolynomial k) = LaurentPolynomial.C (c : k) * LaurentPolynomial.T n := by
  obtain ⟨c, hc, n, hn⟩ := exists_scalar_mul_T_of_isUnit k (s : LaurentPolynomial k) s.isUnit
  obtain ⟨c, rfl⟩ := hc
  exact ⟨n, c, hn⟩

/-- The integer exponent of the original Laurent unit. -/
def unitExponent (s : (LaurentPolynomial k)ˣ) : ℤ :=
  Classical.choose (exists_unit_monomial k s)

theorem unitExponent_spec (s : (LaurentPolynomial k)ˣ) :
    ∃ c : kˣ, (s : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (unitExponent k s) :=
  Classical.choose_spec (exists_unit_monomial k s)

/-- Laurent degree proves uniqueness of the selected exponent. -/
theorem unitExponent_eq_of_monomial (s : (LaurentPolynomial k)ˣ) (c : kˣ) (n : ℤ)
    (h : (s : LaurentPolynomial k) = LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    unitExponent k s = n := by
  obtain ⟨d, hd⟩ := unitExponent_spec k s
  have he := congrArg LaurentPolynomial.degree (hd.symm.trans h)
  apply WithBot.coe_injective
  simpa only [LaurentPolynomial.degree_C_mul_T _ _ (Units.ne_zero d),
    LaurentPolynomial.degree_C_mul_T _ _ (Units.ne_zero c)] using he

@[simp]
theorem unitExponent_one : unitExponent k 1 = 0 := by
  apply unitExponent_eq_of_monomial k 1 1 0
  simp only [Units.val_one, map_one, LaurentPolynomial.T_zero, one_mul]

/-- Multiplication of the original units adds their unique exponents. -/
theorem unitExponent_mul (s t : (LaurentPolynomial k)ˣ) :
    unitExponent k (s * t) = unitExponent k s + unitExponent k t := by
  obtain ⟨c, hc⟩ := unitExponent_spec k s
  obtain ⟨d, hd⟩ := unitExponent_spec k t
  apply unitExponent_eq_of_monomial k (s * t) (c * d) _
  rw [Units.val_mul, hc, hd, Units.val_mul, map_mul, LaurentPolynomial.T_add]
  ring

@[simp]
theorem unitExponent_inv (s : (LaurentPolynomial k)ˣ) :
    unitExponent k s⁻¹ = -unitExponent k s := by
  have h := unitExponent_mul k s s⁻¹
  rw [mul_inv_cancel, unitExponent_one] at h
  omega

/-- Zero exponent means that the actual Laurent unit is an actual nonzero constant. -/
theorem unitExponent_eq_zero_iff (s : (LaurentPolynomial k)ˣ) :
    unitExponent k s = 0 ↔ ∃ c : kˣ,
      (s : LaurentPolynomial k) = LaurentPolynomial.C (c : k) := by
  constructor
  · intro hs
    obtain ⟨c, hc⟩ := unitExponent_spec k s
    exact ⟨c, by simpa only [hs, LaurentPolynomial.T_zero, mul_one] using hc⟩
  · rintro ⟨c, hc⟩
    apply unitExponent_eq_of_monomial k s c 0
    simpa only [LaurentPolynomial.T_zero, mul_one] using hc

/-- The square of a unit has twice its exponent. -/
theorem unitExponent_sq (s : (LaurentPolynomial k)ˣ) :
    unitExponent k (s ^ 2) = 2 * unitExponent k s := by
  rw [pow_two, unitExponent_mul]
  ring

/-- The coordinate unit of the original structure-sheaf overlap. -/
def overlapLaurentUnit (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ) :
    (LaurentPolynomial k)ˣ :=
  Units.map (overlapSectionsEquiv k).toRingHom.toMonoidHom s

/-- The exponent of the actual overlap section, through the original Laurent coordinates. -/
def overlapExponent (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ) : ℤ :=
  unitExponent k (overlapLaurentUnit k s)

@[simp]
theorem overlapExponent_one : overlapExponent k 1 = 0 := by
  change unitExponent k ((Units.map (overlapSectionsEquiv k).toRingHom.toMonoidHom) 1) = 0
  rw [map_one, unitExponent_one]

theorem overlapExponent_mul (s t : Γ(projectiveSpace k 1, overlapOpen k)ˣ) :
    overlapExponent k (s * t) = overlapExponent k s + overlapExponent k t := by
  change unitExponent k ((Units.map (overlapSectionsEquiv k).toRingHom.toMonoidHom) (s * t)) =
    unitExponent k (overlapLaurentUnit k s) + unitExponent k (overlapLaurentUnit k t)
  rw [map_mul, unitExponent_mul]
  rfl

@[simp]
theorem overlapExponent_inv (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ) :
    overlapExponent k s⁻¹ = -overlapExponent k s := by
  change unitExponent k ((Units.map (overlapSectionsEquiv k).toRingHom.toMonoidHom) s⁻¹) =
    -unitExponent k (overlapLaurentUnit k s)
  rw [map_inv, unitExponent_inv]
  rfl

/-- A unit restricted from the actual first chart has exponent zero. -/
@[simp]
theorem overlapExponent_restrictLeft (s : Γ(projectiveSpace k 1, chartOpen k 0)ˣ) :
    overlapExponent k (Units.map (restrictLeft k).toMonoidHom s) = 0 := by
  obtain ⟨c, hc⟩ := left_chart_unit_constant k s
  apply unitExponent_eq_of_monomial k _ c 0
  change overlapSectionsEquiv k (restrictLeft k (s : Γ(projectiveSpace k 1, chartOpen k 0))) = _
  rw [overlapSectionsEquiv_restrictLeft, hc, Polynomial.toLaurent_C,
    LaurentPolynomial.T_zero, mul_one]

/-- A unit restricted from the actual second chart also has exponent zero. -/
@[simp]
theorem overlapExponent_restrictRight (s : Γ(projectiveSpace k 1, chartOpen k 1)ˣ) :
    overlapExponent k (Units.map (restrictRight k).toMonoidHom s) = 0 := by
  obtain ⟨c, hc⟩ := right_chart_unit_constant k s
  apply unitExponent_eq_of_monomial k _ c 0
  change overlapSectionsEquiv k (restrictRight k (s : Γ(projectiveSpace k 1, chartOpen k 1))) = _
  rw [overlapSectionsEquiv_restrictRight, hc, Polynomial.aeval_C,
    ← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.T_zero, mul_one]

/-- Changing the two actual chart frames preserves the original overlap exponent. -/
theorem overlapExponent_gauge
    (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ)
    (a : Γ(projectiveSpace k 1, chartOpen k 0)ˣ)
    (b : Γ(projectiveSpace k 1, chartOpen k 1)ˣ) :
    overlapExponent k
      (Units.map (restrictLeft k).toMonoidHom a * s *
        (Units.map (restrictRight k).toMonoidHom b)⁻¹) = overlapExponent k s := by
  rw [overlapExponent_mul, overlapExponent_mul, overlapExponent_restrictLeft,
    overlapExponent_inv, overlapExponent_restrictRight]
  simp only [zero_add, neg_zero, add_zero]

end KltDP.Geometry.ProjectiveLineTransitionExponent
