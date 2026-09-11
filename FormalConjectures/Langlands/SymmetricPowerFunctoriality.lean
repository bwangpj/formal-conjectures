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

import FormalConjecturesUtil

/-!
# Symmetric power functoriality for `GL m` over `ℚ`

An instance of Langlands' functoriality conjecture (Question 5 of [La70]), for the symmetric
power `Sym^k : GL m ℂ → GL N ℂ`, `N = (m + k - 1).choose k`, of the dual group of `GL m`:
every automorphic eigenform `f` for `GL m / ℚ` should transfer to an automorphic eigenform `g`
for `GL N / ℚ` whose local parameters are the `k`-th symmetric powers of those of `f`:

* at all but finitely many primes, the Satake parameters of `g` are the degree `k` monomials
  in the Satake parameters of `f` (`Satake.symPowTransferFamily`);
* at the archimedean place, the Harish-Chandra parameter of `g` consists of the `k`-fold sums,
  with repetition, of the entries of that of `f` (`symPowWeightFamily`).

The two clauses are the same combinatorics — indexed by the unordered `k`-tuples
`Sym (Fin m) k`, with `N` entries, the rank of the target group — with products in one and
sums in the other: an `L`-homomorphism multiplies Satake parameters and adds the archimedean
parameters, which are their exponents.

The statement is at the level of eigenforms, not automorphic representations: an automorphic
eigenform (`IsAutomorphicEigenform`) is a Borel-Jacquet automorphic form which, at all but
finitely many primes, is unramified and a simultaneous eigenvector of the spherical Hecke
operators, its Satake parameters being the roots of the Hecke polynomial of its eigensystem.
Quantifying over all eigensystems and infinitesimal characters is unambiguous because both are
unique (`HasHeckeEigensystemAt.unique`, `HasInfinitesimalCharacter.unique`), and both
transfers depend only on the unordered family of parameters
(`Satake.symPowTransferFamily_comp_perm`, `symPowWeightFamily_comp_perm`).

## The archimedean exponents

The transfer rule is additive on *Harish-Chandra* parameters — highest weights shifted by
`ρ` — not on unshifted highest weights. For `m = 2` the two agree, so `GL 2` checks cannot
detect the difference, but they diverge from `m = 3` on: for `ν = (10, 0, -10)` and `k = 2`
the correct parameter is `{20, 10, 0, 0, -10, -20}`, while transferring the unshifted weight
and adding `ρ_6` gives `{41/2, 21/2, 1/2, -1/2, -21/2, -41/2}`.

Sanity checks: for `f` a holomorphic modular form of weight `w`, with parameter
`((w - 1)/2, -(w - 1)/2)`, the clause gives `Sym^2` the parameter `{w - 1, 0, -(w - 1)}` of
the Gelbart-Jacquet symmetric square; `k = 1` is the identity, and `k = 0` transfers to `GL 1`
with the empty-sum parameter `{0}`.

## Caveats

Only the infinitesimal character is matched at infinity — not the full archimedean
`L`-parameter, which also carries discrete data (the minimal `K`-type; discrete versus
principal series for `m = 2`) — and nothing is asked at the ramified primes, which would need
local Langlands. Moreover the archimedean clause is only as sharp as the Verma parametrisation
of characters of `Z(𝔤)` used by `HasHarishChandraParameter`; its completeness and faithfulness
up to the Weyl group are the Harish-Chandra isomorphism, not available in Mathlib. See the
implementation notes of `FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.Algebraic`.

No cuspidality is imposed (condition (e) of Borel-Jacquet is not formalised) and no
algebraicity: functoriality is conjectured for all automorphic forms, including non-algebraic
ones such as generic Maass forms. Algebraicity is an independent axis over the same
infrastructure; see `FormalConjectures.Langlands.ClozelAlgebraicity`.

## Status

For `m = 2` — where `Sym^k` lands in `GL (k + 1)` — and `f` coming from a holomorphic modular
form, this is a theorem of Newton-Thorne [NT21a], [NT21b] for all `k`, after Gelbart-Jacquet
(`k = 2`) and Kim-Shahidi and Kim (`k = 3, 4`). For Maass forms and for `m ≥ 3` it is open,
and central: the symmetric power `L`-functions it controls imply, among other things, the
Ramanujan-Petersson and Sato-Tate conjectures.

## References

- [La70] R. P. Langlands, *Problems in the theory of automorphic forms*, in Lectures in
  Modern Analysis and Applications III, Lecture Notes in Math. 170, Springer (1970), 18-61.
  https://publications.ias.edu/sites/default/files/problems-in-the-theory-of-automorphic-forms.pdf
- [NT21a] J. Newton, J. A. Thorne, *Symmetric power functoriality for holomorphic modular
  forms*, Publ. Math. IHÉS 134 (2021), 1-116. https://doi.org/10.1007/s10240-021-00324-0
- [NT21b] J. Newton, J. A. Thorne, *Symmetric power functoriality for holomorphic modular
  forms, II*, Publ. Math. IHÉS 134 (2021), 117-152.
  https://doi.org/10.1007/s10240-021-00318-y
- [Wikipedia](https://en.wikipedia.org/wiki/Langlands_program)
-/

namespace SymmetricPowerFunctoriality

open Matrix.GeneralLinearGroup

/-- `Sym^k` of a nontrivial group is nontrivial: `(m + k - 1).choose k ≠ 0` when `m ≠ 0`. -/
local instance {m k : ℕ} [NeZero m] : NeZero ((m + k - 1).choose k) :=
  ⟨(Nat.choose_pos (by have := NeZero.pos m; omega)).ne'⟩

/-- **Symmetric power functoriality** for `GL m` over `ℚ`: every automorphic eigenform `f` for
`GL m` admits, for each `k`, an automorphic eigenform `g` for `GL ((m + k - 1).choose k)` whose
local parameters are the `k`-th symmetric power of those of `f`. At all but finitely many
primes the Satake parameters of `g` are the degree `k` monomials in the Satake parameters
`α 0, …, α (m - 1)` of `f`, and at the archimedean place the Harish-Chandra parameter of `g` is
the multiset of `k`-fold sums of that of `f`.

Open in general; for `m = 2` and `f` coming from a holomorphic modular form it is a theorem of
Newton-Thorne. -/
@[category research open, AMS 11]
theorem symmetric_power_functoriality (k m : ℕ) [NeZero m] (f : automorphicForms (Fin m))
    (hf : IsAutomorphicEigenform f) :
    ∃ g : automorphicForms (Fin ((m + k - 1).choose k)), IsAutomorphicEigenform g ∧
      (∃ S : Finset Nat.Primes, ∀ p ∉ S, ∀ (a : Fin (m + 1) → ℂ)
        (b : Fin ((m + k - 1).choose k + 1) → ℂ),
        HasHeckeEigensystemAt p f a → HasHeckeEigensystemAt p g b →
          ∃ α : Fin m → ℂ,
            Satake.satakeParameters (p : ℕ) a = Finset.univ.val.map α ∧
              Satake.satakeParameters (p : ℕ) b = Satake.symPowTransferFamily k α) ∧
      ∀ (χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ) (ν : Fin m → ℂ),
        HasInfinitesimalCharacter f χ → HasHarishChandraParameter χ ν →
          ∃ (χ' : ↥(centerUniversalEnveloping (Fin ((m + k - 1).choose k))) →ₐ[ℂ] ℂ)
            (ν' : Fin ((m + k - 1).choose k) → ℂ),
            HasInfinitesimalCharacter g χ' ∧ HasHarishChandraParameter χ' ν' ∧
              Finset.univ.val.map ν' = symPowWeightFamily k ν := by
  sorry

/-- **Symmetric power functoriality**, at the finite places only: the transfer exists and
matches Satake parameters at all but finitely many primes, with nothing asked at infinity.
The weaker half of `symmetric_power_functoriality`. -/
@[category research open, AMS 11]
theorem symmetric_power_functoriality.variants.finite_places (k m : ℕ) [NeZero m]
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) :
    ∃ g : automorphicForms (Fin ((m + k - 1).choose k)), IsAutomorphicEigenform g ∧
      ∃ S : Finset Nat.Primes, ∀ p ∉ S, ∀ (a : Fin (m + 1) → ℂ)
        (b : Fin ((m + k - 1).choose k + 1) → ℂ),
        HasHeckeEigensystemAt p f a → HasHeckeEigensystemAt p g b →
          ∃ α : Fin m → ℂ,
            Satake.satakeParameters (p : ℕ) a = Finset.univ.val.map α ∧
              Satake.satakeParameters (p : ℕ) b = Satake.symPowTransferFamily k α := by
  sorry

/-- **Symmetric power functoriality** for `GL 2` over `ℚ`: the case `m = 2`, where the
`k`-th symmetric power lands in `GL (k + 1)` and the transfer of the parameters `{α, β}` is
`{α^i * β^(k-i) | 0 ≤ i ≤ k}`. A theorem of Newton-Thorne for `f` coming from a holomorphic
modular form; open for general `f` (in particular for Maass forms). Stated at the finite
places only. -/
@[category research open, AMS 11]
theorem symmetric_power_functoriality.variants.gl_two (k : ℕ)
    (f : automorphicForms (Fin 2)) (hf : IsAutomorphicEigenform f) :
    ∃ g : automorphicForms (Fin (k + 1)), IsAutomorphicEigenform g ∧
      ∃ S : Finset Nat.Primes, ∀ p ∉ S, ∀ (a : Fin (2 + 1) → ℂ) (b : Fin (k + 1 + 1) → ℂ),
        HasHeckeEigensystemAt p f a → HasHeckeEigensystemAt p g b →
          ∃ α β : ℂ,
            Satake.satakeParameters (p : ℕ) a = {α, β} ∧
              Satake.satakeParameters (p : ℕ) b = Satake.symPowTransfer k α β := by
  sorry

end SymmetricPowerFunctoriality
