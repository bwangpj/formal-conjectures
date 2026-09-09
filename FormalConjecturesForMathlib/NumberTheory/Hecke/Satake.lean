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

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
# Satake parameters

The Satake parameters of an unramified Hecke eigensystem for `GL n` at a prime `p`: the
multiset of roots of the Hecke polynomial

`∑ i, (-1) ^ i * p ^ (i.choose 2) * a i * X ^ (n - i)`,

whose coefficients are the eigenvalues `a i` of the Hecke operators `T (p, i)` attached to the
double cosets of `diag (ϖ, …, ϖ, 1, …, 1)` with `i` entries `ϖ`, normalised so that `a 0 = 1`.

Defining the parameters this way — as the roots of the Hecke polynomial — rather than through
the Satake isomorphism `ℋ (GL n F, GL n 𝒪) ≃ ℂ[X₁^±, …, Xₙ^±] ^ (Sₙ)` is deliberate. The
isomorphism is a theorem about a general reductive group, and stating it needs the dual group
and root datum, none of which Mathlib has; the roots of the Hecke polynomial are elementary and
are exactly what the local factor

`L (s, π, p) ⁻¹ = ∏ j, (1 - α j * p ^ (-s))`

of an automorphic `L`-function is built from, which is all that is needed to state the global
Langlands correspondence. The Satake isomorphism is then the statement that this parametrisation
is a bijection onto unramified representations, which is a theorem for later rather than part of
the definition.

## Main declarations

* `heckePolynomial`: the Hecke polynomial of an eigensystem.
* `satakeParameters`: its roots, with multiplicity.

*References:*
 - I. Satake, *Theory of spherical functions on reductive algebraic groups over p-adic fields*,
   Publ. Math. IHÉS 18 (1963), 5-69
 - [J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300
   (2024)](https://sites.duke.edu/jgetz/files/2022/04/Graduate_Text.pdf), §7
-/

open Polynomial

namespace Satake

variable {n : ℕ}

/-- The **Hecke polynomial** of an eigensystem `a` at `p`: the degree `n` polynomial whose
coefficients are the Hecke eigenvalues, normalised by the powers of `p` that make its roots the
Satake parameters. -/
noncomputable def heckePolynomial (p : ℕ) (a : Fin (n + 1) → ℂ) : ℂ[X] :=
  ∑ i : Fin (n + 1), C ((-1) ^ (i : ℕ) * (p : ℂ) ^ (i : ℕ).choose 2 * a i) * X ^ (n - (i : ℕ))

theorem natDegree_heckePolynomial_le (p : ℕ) (a : Fin (n + 1) → ℂ) :
    (heckePolynomial p a).natDegree ≤ n :=
  natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (natDegree_C_mul_le _ _).trans ((natDegree_X_pow _).le.trans (Nat.sub_le _ _))

@[simp]
theorem coeff_heckePolynomial_natDegree (p : ℕ) (a : Fin (n + 1) → ℂ) :
    (heckePolynomial p a).coeff n = a 0 := by
  rw [heckePolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro i _ hi
    have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have : n - (i : ℕ) ≠ n := by
      have := i.is_lt
      omega
    rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm this), mul_zero]
  · simp

/-- The Hecke polynomial of a normalised eigensystem is monic of degree `n`. -/
theorem monic_heckePolynomial {p : ℕ} {a : Fin (n + 1) → ℂ} (ha : a 0 = 1) :
    (heckePolynomial p a).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_heckePolynomial_le p a)
    (by rw [coeff_heckePolynomial_natDegree, ha])

theorem natDegree_heckePolynomial {p : ℕ} {a : Fin (n + 1) → ℂ} (ha : a 0 = 1) :
    (heckePolynomial p a).natDegree = n :=
  le_antisymm (natDegree_heckePolynomial_le p a)
    (le_natDegree_of_ne_zero (by
      rw [coeff_heckePolynomial_natDegree, ha]; exact one_ne_zero))

/-- The **Satake parameters** of an eigensystem: the roots of its Hecke polynomial, with
multiplicity. -/
noncomputable def satakeParameters (p : ℕ) (a : Fin (n + 1) → ℂ) : Multiset ℂ :=
  (heckePolynomial p a).roots

/-- There are `n` Satake parameters, counted with multiplicity: `ℂ` is algebraically closed. -/
theorem card_satakeParameters {p : ℕ} {a : Fin (n + 1) → ℂ} (ha : a 0 = 1) :
    Multiset.card (satakeParameters p a) = n := by
  rw [satakeParameters,
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)),
    natDegree_heckePolynomial ha]

end Satake
