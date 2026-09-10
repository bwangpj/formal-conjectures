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
public import Mathlib.Data.Sym.Card

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
* `satakeParameters`: its roots, with multiplicity, nonzero by
  `zero_notMem_satakeParameters` and so a semisimple conjugacy class in `GL n ℂ`.
* `tensorTransfer`, `symPowTransfer`, `extPowTransfer`: the effect on Satake parameters of the
  tensor product, the symmetric power and the exterior power, three instances of the transfer
  in the fifth question of Langlands.

## Functoriality

Question 5 of Langlands asks, for quasi-split `G` and `G'` over a global field and a complex
analytic homomorphism of `L`-groups over the Galois group, whether an automorphic `π'` on `G'`
transfers to an automorphic `π` on `G` whose local components correspond under the induced local
homomorphisms. For general linear groups the transfer is visible entirely on Satake parameters:
the dual group of `GL n` is `GL n ℂ`, in which a semisimple conjugacy class is exactly an
unordered tuple of nonzero complex numbers, so an `L`-homomorphism acts as a map of multisets
and no `L`-group need be constructed. `tensorTransfer`, `symPowTransfer` and `extPowTransfer` are three standard
instances.

Langlands notes there that the case `G' = {1}`, `G = GL(1)` of the fourth and fifth questions is
the Artin reciprocity law, so reciprocity is a special case of Question 5 rather than a separate
conjecture.

*References:*
 - R. P. Langlands, *Problems in the theory of automorphic forms*, in Lectures in Modern
   Analysis and Applications III, Lecture Notes in Math. 170, Springer (1970), 18-61;
   Question 5 is global functoriality.
   https://publications.ias.edu/sites/default/files/problems-in-the-theory-of-automorphic-forms.pdf
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

/-- The Hecke polynomial of an eigensystem over an arbitrary commutative ring, with `q` the
residue cardinality.

Every power of `q` appearing here is a nonnegative integer power, so this is the *arithmetic*
normalisation of Clozel and Gross rather than the one induced by the Satake isomorphism itself,
which is twisted by half the sum of the positive roots and so involves a square root of `q`.
Being integral, it transports along an arbitrary ring homomorphism
(`heckePolynomialOver_map`), which is what comparing Hecke eigenvalues with Frobenius
characteristic polynomials over a `p`-adic field requires. -/
noncomputable def heckePolynomialOver {R : Type*} [CommRing R] (q : ℕ) (a : Fin (n + 1) → R) :
    R[X] :=
  ∑ i : Fin (n + 1), C ((-1) ^ (i : ℕ) * (q : R) ^ (i : ℕ).choose 2 * a i) * X ^ (n - (i : ℕ))

/-- Over `ℂ` the two agree, so the exponents of `heckePolynomial` are exactly the arithmetic
ones. -/
theorem heckePolynomial_eq_heckePolynomialOver (p : ℕ) (a : Fin (n + 1) → ℂ) :
    heckePolynomial p a = heckePolynomialOver p a := rfl

/-- The arithmetically normalised Hecke polynomial transports along a ring homomorphism. -/
theorem heckePolynomialOver_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ)
    (a : Fin (n + 1) → R) :
    (heckePolynomialOver q a).map φ = heckePolynomialOver q (fun i => φ (a i)) := by
  simp [heckePolynomialOver, Polynomial.map_sum]

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

@[simp]
theorem coeff_zero_heckePolynomial (p : ℕ) (a : Fin (n + 1) → ℂ) :
    (heckePolynomial p a).coeff 0 = (-1) ^ n * (p : ℂ) ^ n.choose 2 * a (Fin.last n) := by
  rw [heckePolynomial, finsetSum_coeff, Finset.sum_eq_single (Fin.last n)]
  · simp only [Fin.val_last, Nat.sub_self, pow_zero, mul_one, coeff_C_zero]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ n := fun h => hi (Fin.ext (by simpa using h))
    have hne : n - (i : ℕ) ≠ 0 := by have := i.is_lt; omega
    rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hne), mul_zero]
  · simp

/-- The Satake parameters are nonzero, so the multiset really is a semisimple conjugacy class
in `GL n ℂ`. The hypothesis on the top eigenvalue holds for a spherical eigenvector, the
corresponding Hecke operator being at a central and hence invertible element. -/
theorem zero_notMem_satakeParameters {p : ℕ} {a : Fin (n + 1) → ℂ} (ha : a 0 = 1)
    (hp : (p : ℂ) ≠ 0) (hlast : a (Fin.last n) ≠ 0) : (0 : ℂ) ∉ satakeParameters p a := by
  intro hmem
  rw [satakeParameters, mem_roots (monic_heckePolynomial ha).ne_zero] at hmem
  have h0 : (heckePolynomial p a).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact hmem
  rw [coeff_zero_heckePolynomial] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    · exact absurd h' (pow_ne_zero _ hp)
  · exact hlast h

/-! ### Transfer of Satake parameters

For `GL n` the dual group is `GL n ℂ`, and a semisimple conjugacy class in `GL n ℂ` is exactly
an unordered `n`-tuple of nonzero complex numbers, which is exactly a multiset of Satake
parameters. So an `L`-homomorphism between general linear groups acts on Satake parameters as
an explicit operation on multisets, and the fifth question of Langlands can be stated for these
groups without constructing `L`-groups at all. -/

/-- Transfer of Satake parameters along the tensor product `GL n ℂ × GL m ℂ → GL (n * m) ℂ`:
the Rankin-Selberg case. -/
def tensorTransfer (α β : Multiset ℂ) : Multiset ℂ := α.bind fun x => β.map (x * ·)

@[simp]
theorem card_tensorTransfer (α β : Multiset ℂ) :
    Multiset.card (tensorTransfer α β) = Multiset.card α * Multiset.card β := by
  simp [tensorTransfer, Multiset.card_bind]

theorem zero_notMem_tensorTransfer {α β : Multiset ℂ} (hα : (0 : ℂ) ∉ α) (hβ : (0 : ℂ) ∉ β) :
    (0 : ℂ) ∉ tensorTransfer α β := by
  intro hmem
  rw [tensorTransfer, Multiset.mem_bind] at hmem
  obtain ⟨x, hx, hmem'⟩ := hmem
  rw [Multiset.mem_map] at hmem'
  obtain ⟨y, hy, hxy⟩ := hmem'
  rcases mul_eq_zero.mp hxy with h | h
  · exact hα (h ▸ hx)
  · exact hβ (h ▸ hy)

/-- Transfer of Satake parameters along the `k`-th symmetric power `GL 2 ℂ → GL (k + 1) ℂ`. -/
def symPowTransfer (k : ℕ) (α β : ℂ) : Multiset ℂ :=
  (Multiset.range (k + 1)).map fun i => α ^ i * β ^ (k - i)

@[simp]
theorem card_symPowTransfer (k : ℕ) (α β : ℂ) :
    Multiset.card (symPowTransfer k α β) = k + 1 := by
  simp [symPowTransfer]

theorem zero_notMem_symPowTransfer {k : ℕ} {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (0 : ℂ) ∉ symPowTransfer k α β := by
  intro hmem
  rw [symPowTransfer, Multiset.mem_map] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  rcases mul_eq_zero.mp hi with h | h
  · exact absurd h (pow_ne_zero _ hα)
  · exact absurd h (pow_ne_zero _ hβ)

/-- Reflecting `{0, …, n}` about its midpoint permutes it. -/
theorem _root_.Multiset.range_map_sub (n : ℕ) :
    (Multiset.range (n + 1)).map (fun i => n - i) = Multiset.range (n + 1) := by
  have h : (List.range (n + 1)).map (fun i => n - i) = (List.range (n + 1)).reverse := by
    rw [List.range_eq_range', List.reverse_range', ← List.range_eq_range']
    congr 1
    funext i
    omega
  calc (Multiset.range (n + 1)).map (fun i => n - i)
      = ↑((List.range (n + 1)).map fun i => n - i) := by rw [Multiset.range, Multiset.map_coe]
    _ = ↑((List.range (n + 1)).reverse) := by rw [h]
    _ = Multiset.range (n + 1) := Multiset.coe_reverse _

/-- The symmetric power transfer does not depend on the ordering of the two parameters:
reindexing `i ↦ k - i` swaps the roles of `α` and `β`. So it is well defined on the
*unordered* pair of Satake parameters of an eigenform on `GL 2`, as a transfer of semisimple
conjugacy classes should be. -/
theorem symPowTransfer_comm (k : ℕ) (α β : ℂ) :
    symPowTransfer k α β = symPowTransfer k β α := by
  rw [symPowTransfer, symPowTransfer]
  conv_rhs => rw [← Multiset.range_map_sub k, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hki : k - (k - i) = i := by omega
  simp only [Function.comp_apply, hki]
  ring

/-- Transfer of Satake parameters along the `k`-th symmetric power
`GL m ℂ → GL ((m + k - 1).choose k) ℂ`, the parameters given as an indexed family
`α : Fin m → ℂ`: the monomials of degree `k` in the parameters, one for each unordered
`k`-tuple of indices. By `symPowTransferFamily_comp_perm` the result depends only on the
multiset of parameters, so this is well defined on semisimple conjugacy classes; for `m = 2`
it is the transfer of `symPowTransfer`. -/
noncomputable def symPowTransferFamily {m : ℕ} (k : ℕ) (α : Fin m → ℂ) : Multiset ℂ :=
  (Finset.univ : Finset (Sym (Fin m) k)).val.map fun s : Sym (Fin m) k =>
    ((s : Multiset (Fin m)).map α).prod

/-- The `k`-th symmetric power of `GL m` lands in `GL ((m + k - 1).choose k)`: there are
`multichoose m k` monomials of degree `k` in `m` variables. -/
@[simp]
theorem card_symPowTransferFamily {m : ℕ} (k : ℕ) (α : Fin m → ℂ) :
    Multiset.card (symPowTransferFamily k α) = (m + k - 1).choose k := by
  rw [symPowTransferFamily, Multiset.card_map, ← Finset.card_def, Finset.card_univ,
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem zero_notMem_symPowTransferFamily {m k : ℕ} {α : Fin m → ℂ} (hα : ∀ j, α j ≠ 0) :
    (0 : ℂ) ∉ symPowTransferFamily k α := by
  intro hmem
  rw [symPowTransferFamily, Multiset.mem_map] at hmem
  obtain ⟨s, -, hs⟩ := hmem
  refine Multiset.prod_ne_zero ?_ hs
  intro h0
  rw [Multiset.mem_map] at h0
  obtain ⟨j, -, hj⟩ := h0
  exact hα j hj

/-- The symmetric power transfer depends only on the *multiset* of parameters: reindexing
the family by a permutation leaves it unchanged, since it just permutes the monomials. -/
theorem symPowTransferFamily_comp_perm {m k : ℕ} (α : Fin m → ℂ) (σ : Equiv.Perm (Fin m)) :
    symPowTransferFamily k (α ∘ σ) = symPowTransferFamily k α := by
  rw [symPowTransferFamily, symPowTransferFamily]
  have he : ((Finset.univ : Finset (Sym (Fin m) k)).val.map (Sym.equivCongr σ))
      = (Finset.univ : Finset (Sym (Fin m) k)).val := by
    have h := congrArg Finset.val (Finset.map_univ_equiv (Sym.equivCongr σ (n := k)))
    rw [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  conv_rhs => rw [← he, Multiset.map_map]
  refine Multiset.map_congr rfl fun s _ => ?_
  show ((s : Multiset (Fin m)).map (α ∘ σ)).prod
    = (((Sym.map σ s : Sym (Fin m) k) : Multiset (Fin m)).map α).prod
  rw [Sym.coe_map, Multiset.map_map]

/-- Transfer of Satake parameters along the `k`-th exterior power
`GL n ℂ → GL (n.choose k) ℂ`: the products of the parameters over the `k`-element
sub-multisets. -/
def extPowTransfer (k : ℕ) (α : Multiset ℂ) : Multiset ℂ :=
  (α.powersetCard k).map Multiset.prod

@[simp]
theorem card_extPowTransfer (k : ℕ) (α : Multiset ℂ) :
    Multiset.card (extPowTransfer k α) = (Multiset.card α).choose k := by
  simp [extPowTransfer]

theorem zero_notMem_extPowTransfer {k : ℕ} {α : Multiset ℂ} (hα : (0 : ℂ) ∉ α) :
    (0 : ℂ) ∉ extPowTransfer k α := by
  intro hmem
  rw [extPowTransfer, Multiset.mem_map] at hmem
  obtain ⟨s, hs, hprod⟩ := hmem
  have hsub : s ≤ α := (Multiset.mem_powersetCard.mp hs).1
  exact Multiset.prod_ne_zero (fun h => hα (Multiset.mem_of_le hsub h)) hprod

/-- The top exterior power is the determinant: `Λ ^ n` of an `n`-tuple of parameters is the
single product of them all. -/
theorem extPowTransfer_card (α : Multiset ℂ) :
    extPowTransfer (Multiset.card α) α = {α.prod} := by
  rw [extPowTransfer, Multiset.powersetCard_self, Multiset.map_singleton]

end Satake
