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

An instance of Langlands' functoriality conjecture (the fifth question of [La70]), for the
symmetric power representations `Sym^k : GL m ℂ → GL ((m + k - 1).choose k) ℂ` of the dual
group of `GL m`: every automorphic eigenform `f` for `GL m / ℚ` should transfer to an
automorphic eigenform `g` for `GL ((m + k - 1).choose k) / ℚ` whose Satake parameters at all
but finitely many primes are the `k`-th symmetric power of those of `f` — if `f` has
parameters `{α 0, …, α (m-1)}` at `p`, then `g` has the degree `k` monomials in the `α j` as
parameters at `p`, one for each unordered `k`-tuple of indices
(`Satake.symPowTransferFamily`).

The statement here is deliberately at the level of eigenforms rather than automorphic
representations: an automorphic eigenform (`IsAutomorphicEigenform`) is an automorphic form
in the sense of Borel-Jacquet which, at all but finitely many primes, is unramified and a
simultaneous eigenvector of the spherical Hecke operators `T_{p,i}`, and its Satake
parameters at such a prime are the roots of the Hecke polynomial of its eigensystem. The
eigensystem at each prime is unique (`HasHeckeEigensystemAt.unique`), so quantifying over
all eigensystems of `f` and `g` pins down the parameters, and the transfer depends only on
the unordered family of parameters by `Satake.symPowTransferFamily_comp_perm` (for `m = 2`,
`Satake.symPowTransfer_comm`). No cuspidality is imposed on either side.

For `m = 2` the symmetric power lands in `GL (k + 1)`, and for `f` coming from a
holomorphic modular form the conjecture is a theorem of Newton and Thorne [NT21a], [NT21b],
for all `k`; before that, the cases `k = 2, 3, 4` were known through the work of
Gelbart-Jacquet, Kim-Shahidi and Kim. For general automorphic eigenforms on `GL 2` (in
particular for Maass forms), and for general `m`, it is open, and it is a central open
instance of functoriality: the symmetric power `L`-functions it controls imply, among other
things, the Ramanujan-Petersson and Sato-Tate conjectures.

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

/-- **Symmetric power functoriality** for `GL m` over `ℚ`, on Satake parameters: every
automorphic eigenform `f` for `GL m` admits, for each `k`, an automorphic eigenform `g` for
`GL ((m + k - 1).choose k)` such that at all but finitely many primes the Satake parameters
of `g` are the degree `k` monomials in the Satake parameters `α 0, …, α (m - 1)` of `f`.
Open in general; for `m = 2` and `f` coming from a holomorphic modular form it is a theorem
of Newton-Thorne. -/
@[category research open, AMS 11]
theorem symmetric_power_functoriality (k m : ℕ) [NeZero m] (f : automorphicForms (Fin m))
    (hf : IsAutomorphicEigenform f) :
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
modular form; open for general `f` (in particular for Maass forms). -/
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
