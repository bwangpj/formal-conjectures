/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.NumberTheory.Hecke.GeneralLinearGroup
public import Mathlib.Data.Complex.Basic
public import FormalConjecturesForMathlib.NumberTheory.Hecke.Operator
public import FormalConjecturesForMathlib.NumberTheory.Hecke.Satake

@[expose] public section

/-!
# The spherical Hecke operators `T i`

The Hecke operators of `GL n` attached to the double cosets of the diagonal matrices
`diag (ϖ, …, ϖ, 1, …, 1)`. Their eigenvalues on a spherical vector are the coefficients of the
Hecke polynomial, whose roots are the Satake parameters.

Since `GL n R` is a Hecke subgroup of `GL n F` by
`Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup`, these operators exist with no extra
hypotheses.
-/

open scoped Pointwise

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- The diagonal element of `GL n F` with `u` in the positions in `s` and `1` elsewhere. -/
def diagOn (u : Fˣ) (s : Finset n) : GL n F where
  val := Matrix.diagonal fun j => if j ∈ s then (u : F) else 1
  inv := Matrix.diagonal fun j => if j ∈ s then ((u⁻¹ : Fˣ) : F) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    split <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    split <;> simp

@[simp]
theorem coe_diagOn (u : Fˣ) (s : Finset n) :
    (diagOn u s : Matrix n n F) = Matrix.diagonal fun j => if j ∈ s then (u : F) else 1 := rfl

@[simp]
theorem diagOn_empty (u : Fˣ) : diagOn u (∅ : Finset n) = 1 := by
  ext i j
  simp [diagOn, Matrix.diagonal, Matrix.one_apply]

section Operators

variable {R : Type*} [CommRing R] [IsDomain R] [Algebra R F] [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL n F) V)

/-- The **spherical Hecke operator** attached to `diag (ϖ, …, ϖ, 1, …, 1)`, with `ϖ` in the
positions in `s`, acting on the `GL n R`-invariants. -/
noncomputable def sphericalHeckeOperator
    (hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})) (u : Fˣ) (s : Finset n) :
    ρ.subgroupInvariants (integralSubgroup n R F) →ₗ[ℂ]
      ρ.subgroupInvariants (integralSubgroup n R F) :=
  Representation.heckeOperator ρ _ (isHeckePair_integralSubgroup hfin) (diagOn u s)

end Operators

section Eigenvectors

/-! ### Spherical eigenvectors and their Satake parameters

Indexing the operators needs an order on the coordinates, so this section fixes `n = Fin m`. -/

variable {m : ℕ} {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin m) F) V)

/-- The first `i` coordinates. -/
def initSeg (m i : ℕ) : Finset (Fin m) := {j | (j : ℕ) < i}

@[simp]
theorem initSeg_zero : initSeg m 0 = ∅ := by simp [initSeg]

/-- The spherical Hecke operator `T i`, at the double coset of
`diag (ϖ, …, ϖ, 1, …, 1)` with `i` entries equal to `ϖ`. -/
noncomputable def T (hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})) (ϖ : Fˣ) (i : ℕ) :
    ρ.subgroupInvariants (integralSubgroup (Fin m) R F) →ₗ[ℂ]
      ρ.subgroupInvariants (integralSubgroup (Fin m) R F) :=
  sphericalHeckeOperator ρ hfin ϖ (initSeg m i)

/-- `T 0` is the identity: its double coset is that of `1`. -/
@[simp]
theorem T_zero (hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})) (ϖ : Fˣ) :
    T ρ hfin ϖ 0 = LinearMap.id := by
  rw [T, sphericalHeckeOperator, initSeg_zero, diagOn_empty]
  exact Representation.heckeOperator_one ρ _ _

/-- `v` is a spherical Hecke eigenvector with system of eigenvalues `a`. -/
structure IsSphericalEigenvector (hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a}))
    (ϖ : Fˣ) (v : ρ.subgroupInvariants (integralSubgroup (Fin m) R F))
    (a : Fin (m + 1) → ℂ) : Prop where
  /-- An eigenvector is nonzero. -/
  ne_zero : v ≠ 0
  /-- `T i` acts by the scalar `a i`. -/
  eigen : ∀ i : Fin (m + 1), T ρ hfin ϖ (i : ℕ) v = a i • v

variable {ρ}

/-- The eigenvalue of `T 0` is `1`, so the eigenvalue system is automatically normalised and
`Satake.heckePolynomial` is monic. -/
theorem IsSphericalEigenvector.eigenvalue_zero
    {hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})} {ϖ : Fˣ}
    {v : ρ.subgroupInvariants (integralSubgroup (Fin m) R F)} {a : Fin (m + 1) → ℂ}
    (h : IsSphericalEigenvector ρ hfin ϖ v a) : a 0 = 1 := by
  have h0 := h.eigen 0
  rw [show ((0 : Fin (m + 1)) : ℕ) = 0 from rfl, T_zero] at h0
  have : (1 - a 0) • v = 0 := by
    rw [sub_smul, one_smul, h0.symm]
    simp
  rcases smul_eq_zero.mp this with h1 | h1
  · linear_combination (norm := ring_nf) -(sub_eq_zero.mp h1)
  · exact absurd h1 h.ne_zero

/-- The **Satake parameters** of a spherical Hecke eigenvector: the roots of the Hecke
polynomial built from its eigenvalues. There are exactly `m` of them, with multiplicity, by
`Satake.card_satakeParameters` together with `IsSphericalEigenvector.eigenvalue_zero`. -/
noncomputable def IsSphericalEigenvector.satakeParameters (p : ℕ)
    {hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})} {ϖ : Fˣ}
    {v : ρ.subgroupInvariants (integralSubgroup (Fin m) R F)} {a : Fin (m + 1) → ℂ}
    (_h : IsSphericalEigenvector ρ hfin ϖ v a) : Multiset ℂ :=
  Satake.satakeParameters p a

theorem IsSphericalEigenvector.card_satakeParameters (p : ℕ)
    {hfin : ∀ a : R, a ≠ 0 → Finite (R ⧸ Ideal.span {a})} {ϖ : Fˣ}
    {v : ρ.subgroupInvariants (integralSubgroup (Fin m) R F)} {a : Fin (m + 1) → ℂ}
    (h : IsSphericalEigenvector ρ hfin ϖ v a) :
    Multiset.card (h.satakeParameters p) = m :=
  Satake.card_satakeParameters h.eigenvalue_zero

end Eigenvectors

end Matrix.GeneralLinearGroup
