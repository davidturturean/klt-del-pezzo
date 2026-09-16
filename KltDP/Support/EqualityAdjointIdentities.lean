import KltDP.Support.EqualityContactCert

/-!
# The five adjoint identities of Proposition A.2 as integral class arithmetic

Manuscript `source/manuscript.tex` lines 3263–3335 (`prop:equality-adjoints`),
proof sentence "Substitution of the proved curve classes and
`K_S = -2a - 2b + Σ E_{ij}` gives all five adjoint identities." Support
obligation `U-EQUALITY-UNIQUE` (lines 3289–3302) needs these identities before
its uniqueness clause.

Classes live in the integral basis `a, b, E_{i1}, E_{i2}, E_{i3}` (`i = 0, 1, ∞`),
encoded as `Fin 11 → ℤ` with coordinates `0 = a`, `1 = b`, `2 + 3i + j = E_{i,j+1}`.
The geometric classes of Proposition 10.1 at `p = 3` are `B = 3a + b - Σ E_{ij}`,
`F_i = b - Σ_j E_{ij}`, `U_i = E_{i1} - E_{i2}`, `V_i = E_{i2} - E_{i3}`,
`K_S = -2a - 2b + Σ E_{ij}`; the thirteen exterior classes `P_i, T_i, Θ, Q_i, W_i`
are the integral classes of the accepted contact patterns
(`KltDP.Support.integralClass` applied to `KltDP.EqualityContacts.P` etc.).
The intersection form is `a·b = 1`, `a² = b² = 0`, `E_{ij}·E_{kl} = -δ`.

Proved here, by kernel decision on these explicit vectors: the five identities
of Proposition A.2, `Z² = -1` and `K·Z = -1` for all thirteen exterior classes,
and the explicit coordinates of the thirteen classes.

Not proved here: that these vectors are the Picard classes of the actual
curves on `S_{3,3}` (F09, F28, F29, F34), the linear equivalences as actual
divisors, and the uniqueness of the effective representatives.
-/

namespace KltDP.Support

open KltDP.EqualityContacts

/-- Integral class vectors in the basis `a, b, E_{01}, E_{02}, E_{03}, E_{11}, …, E_{∞3}`. -/
abbrev ClassVec := Fin 11 → ℤ

/-- The class vector of a `ClassVector`. -/
def toVec (x : ClassVector) : ClassVec :=
  ![x.a, x.b, x.e01, x.e02, x.e03, x.e11, x.e12, x.e13, x.eInf1, x.eInf2, x.eInf3]

/-- The intersection form: `a·b = 1`, `a² = b² = 0`, `E_{ij}·E_{kl} = -δ_{ik}δ_{jl}`. -/
def form (x y : ClassVec) : ℤ :=
  x 0 * y 1 + x 1 * y 0 - ∑ t : Fin 11, if 2 ≤ (t : ℕ) then x t * y t else 0

/-- `B = 3a + b - Σ E_{ij}`. -/
def Bcls : ClassVec := ![3, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- `F_i = b - Σ_j E_{ij}`. -/
def Fcls (i : Fin 3) : ClassVec := fun t =>
  if (t : ℕ) = 1 then 1
  else if 2 + 3 * (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) < 5 + 3 * (i : ℕ) then -1 else 0

/-- `U_i = C_{i1} = E_{i1} - E_{i2}`. -/
def Ucls (i : Fin 3) : ClassVec := fun t =>
  if (t : ℕ) = 2 + 3 * (i : ℕ) then 1 else if (t : ℕ) = 3 + 3 * (i : ℕ) then -1 else 0

/-- `V_i = C_{i2} = E_{i2} - E_{i3}`. -/
def Vcls (i : Fin 3) : ClassVec := fun t =>
  if (t : ℕ) = 3 + 3 * (i : ℕ) then 1 else if (t : ℕ) = 4 + 3 * (i : ℕ) then -1 else 0

/-- `K_S = -2a - 2b + Σ E_{ij}`. -/
def Kcls : ClassVec := ![-2, -2, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The exterior classes from the accepted contact patterns. -/
def Pcls (i : Fin 3) : ClassVec := toVec (integralClass (KltDP.EqualityContacts.P i))
def Tcls (i : Fin 3) : ClassVec := toVec (integralClass (KltDP.EqualityContacts.T i))
def thetaCls : ClassVec := toVec (integralClass KltDP.EqualityContacts.theta)
def Qcls (i : Fin 3) : ClassVec := toVec (integralClass (KltDP.EqualityContacts.Q i))
def Wcls (i : Fin 3) : ClassVec := toVec (integralClass (KltDP.EqualityContacts.W i))

/-- Explicit coordinates of the branch-`0` representatives. -/
theorem exterior_classes_explicit :
    Pcls 0 = ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] ∧
    Tcls 0 = ![1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    thetaCls = ![1, 1, -1, 0, 0, -1, 0, 0, -1, 0, 0] ∧
    Qcls 0 = ![2, 1, -1, 0, 0, -1, -1, 0, -1, -1, 0] ∧
    Wcls 0 = ![3, 2, -1, -1, -1, -2, -1, 0, -2, -1, 0] := by
  decide

/-- Identity 1: `K + V_i + B + F_i + 2P_i = T_i`. -/
theorem adjoint_identity_one :
    ∀ i : Fin 3, Kcls + Vcls i + Bcls + Fcls i + (Pcls i + Pcls i) = Tcls i := by
  decide

/-- Identity 2: `K + U_i + F_j + F_k + 2T_i = P_i` for `{i, j, k} = {0, 1, ∞}`. -/
theorem adjoint_identity_two :
    ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls i + Fcls j + Fcls k + (Tcls i + Tcls i) = Pcls i := by
  decide

/-- Identity 3: `K + Σ U_i + 2Θ = Σ P_i`. -/
theorem adjoint_identity_three :
    Kcls + Ucls 0 + Ucls 1 + Ucls 2 + (thetaCls + thetaCls) = Pcls 0 + Pcls 1 + Pcls 2 := by
  decide

/-- Identity 4: `K + U_i + V_j + V_k + 2Q_i = P_i + T_j + T_k`. -/
theorem adjoint_identity_four :
    ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls i + Vcls j + Vcls k + (Qcls i + Qcls i) = Pcls i + Tcls j + Tcls k := by
  decide

/-- Identity 5: `K + U_j + V_j + W_i = P_k + T_k` for `j ≠ i` and `k` the third index. -/
theorem adjoint_identity_five :
    ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls j + Vcls j + Wcls i = Pcls k + Tcls k := by
  decide

/-- All thirteen exterior classes have square `-1` and `K·Z = -1`. -/
theorem exterior_classes_minus_one :
    (∀ i, form (Pcls i) (Pcls i) = -1 ∧ form Kcls (Pcls i) = -1) ∧
    (∀ i, form (Tcls i) (Tcls i) = -1 ∧ form Kcls (Tcls i) = -1) ∧
    (form thetaCls thetaCls = -1 ∧ form Kcls thetaCls = -1) ∧
    (∀ i, form (Qcls i) (Qcls i) = -1 ∧ form Kcls (Qcls i) = -1) ∧
    (∀ i, form (Wcls i) (Wcls i) = -1 ∧ form Kcls (Wcls i) = -1) := by
  decide

/-- The displayed geometric classes: `B² = -3`, `F_i² = -3`, `U_i² = V_i² = -2`,
`U_i·V_i = 1`, `K² = -1`. -/
theorem displayed_classes_squares :
    form Bcls Bcls = -3 ∧ (∀ i, form (Fcls i) (Fcls i) = -3) ∧
    (∀ i, form (Ucls i) (Ucls i) = -2 ∧ form (Vcls i) (Vcls i) = -2 ∧ form (Ucls i) (Vcls i) = 1) ∧
    form Kcls Kcls = -1 := by
  decide


/-- "Each right side consists of pairwise disjoint `(-1)`-curves": the classes occurring
on the right-hand sides pair to zero, `P_i·P_j = P_i·T_j = T_i·T_j = 0` for `i ≠ j` and
`P_k·T_k = 0`. -/
theorem right_hand_sides_pairwise_disjoint :
    (∀ i j : Fin 3, i ≠ j → form (Pcls i) (Pcls j) = 0) ∧
    (∀ i j : Fin 3, i ≠ j → form (Pcls i) (Tcls j) = 0) ∧
    (∀ i j : Fin 3, i ≠ j → form (Tcls i) (Tcls j) = 0) ∧
    (∀ k : Fin 3, form (Pcls k) (Tcls k) = 0) := by
  decide

/-- Degrees against `L = (1/3)(B + b)`, cleared of denominators: `3 L·Z = B·Z + b·Z` equals
`1` for `P_i, T_i`, `2` for `Θ, Q_i` and `3` for `W_i` (the shortest-curve rows). -/
def bCls : ClassVec := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem three_L_degrees :
    (∀ i, form Bcls (Pcls i) + form bCls (Pcls i) = 1) ∧
    (∀ i, form Bcls (Tcls i) + form bCls (Tcls i) = 1) ∧
    (form Bcls thetaCls + form bCls thetaCls = 2) ∧
    (∀ i, form Bcls (Qcls i) + form bCls (Qcls i) = 2) ∧
    (∀ i, form Bcls (Wcls i) + form bCls (Wcls i) = 3) := by
  decide

/-- **Proposition A.2, class-arithmetic clause.** -/
theorem equality_adjoint_identities :
    (∀ i : Fin 3, Kcls + Vcls i + Bcls + Fcls i + (Pcls i + Pcls i) = Tcls i) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls i + Fcls j + Fcls k + (Tcls i + Tcls i) = Pcls i) ∧
    (Kcls + Ucls 0 + Ucls 1 + Ucls 2 + (thetaCls + thetaCls) = Pcls 0 + Pcls 1 + Pcls 2) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls i + Vcls j + Vcls k + (Qcls i + Qcls i) = Pcls i + Tcls j + Tcls k) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kcls + Ucls j + Vcls j + Wcls i = Pcls k + Tcls k) :=
  ⟨adjoint_identity_one, adjoint_identity_two, adjoint_identity_three,
    adjoint_identity_four, adjoint_identity_five⟩

end KltDP.Support
