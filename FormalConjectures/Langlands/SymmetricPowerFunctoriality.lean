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
automorphic eigenform `g` for `GL ((m + k - 1).choose k) / ℚ` whose local parameters are the
`k`-th symmetric power of those of `f`.

Question 5 asks for matching at *every* place, and the statement below has one clause for the
finite places and one for the archimedean place.

* At all but finitely many primes, the Satake parameters of `g` are the `k`-th symmetric power
  of those of `f`: if `f` has parameters `{α 0, …, α (m-1)}` at `p`, then `g` has the degree
  `k` monomials in the `α j` as parameters at `p`, one for each unordered `k`-tuple of indices
  (`Satake.symPowTransferFamily`).
* At the archimedean place, the Harish-Chandra parameter of `g` is the `k`-th symmetric power
  of that of `f`: the sums of `k` of the `ν j` with repetition (`symPowWeightFamily`).

An `L`-homomorphism multiplies Satake parameters and adds archimedean parameters, the latter
being the exponents of the former, which is why the two clauses use the same combinatorics with
products in one and sums in the other. Both transfers are indexed by the unordered `k`-tuples
`Sym (Fin m) k` and both have `(m + k - 1).choose k` entries, the rank of the target group.

The statement is deliberately at the level of eigenforms rather than automorphic
representations: an automorphic eigenform (`IsAutomorphicEigenform`) is an automorphic form in
the sense of Borel-Jacquet which, at all but finitely many primes, is unramified and a
simultaneous eigenvector of the spherical Hecke operators `T_{p,i}`, and its Satake parameters
at such a prime are the roots of the Hecke polynomial of its eigensystem. The eigensystem at
each prime is unique (`HasHeckeEigensystemAt.unique`) and so is the infinitesimal character
(`HasInfinitesimalCharacter.unique`), so quantifying over all of them pins down the parameters;
each transfer depends only on the unordered family of parameters, by
`Satake.symPowTransferFamily_comp_perm` and `symPowWeightFamily_comp_perm`.

## Archimedean sanity check

The exponents are the place a statement like this is most likely to be silently false, so:
for `m = 2` and `f` a holomorphic modular form of weight `w`, the Harish-Chandra parameter is
`((w - 1) / 2, -(w - 1) / 2)`, and the clause above gives `Sym ^ 2` the parameter
`{w - 1, 0, -(w - 1)}`, which is the Gelbart-Jacquet symmetric square, of motivic weight
`2 (w - 1)`. At the other end, `k = 0` transfers to `GL 1` with parameter `{0}`, the empty sum,
and `k = 1` is the identity.

The shift by `ρ` is essential: the rule is additive on Harish-Chandra parameters, not on
unshifted highest weights. For `m = 2` the two happen to agree, since
`Sym ^ k (lam + ρ_2) = Sym ^ k lam + ρ_(k+1)` there, so the `GL 2` check above does not detect
the shift. They diverge from `m = 3` on: for `m = 3`, `k = 2` and `ν = (10, 0, -10)` the
correct answer is `{20, 10, 0, 0, -10, -20}`, while transferring the unshifted weight and
adding `ρ_6` gives `{41/2, 21/2, 1/2, -1/2, -21/2, -41/2}`.

## What is not matched

Only the *infinitesimal character* is matched at infinity, not the full archimedean
`L`-parameter, which also carries discrete data such as the minimal `K`-type and, for `m = 2`,
whether the component at infinity is a discrete series or a principal series. So the
archimedean clause is a strengthening towards Question 5 rather than the whole of it. Nothing
is asked at the finitely many ramified primes either, which would need local Langlands.

The archimedean clause is only as sharp as the Verma parametrisation of characters of `Z(𝔤)`
that `HasHarishChandraParameter` uses. That every character is of this form, and that the
parametrisation is faithful up to the Weyl group, are the content of the Harish-Chandra
isomorphism, which needs the Poincaré-Birkhoff-Witt theorem and is not available in Mathlib;
so neither fact is proved here. See the implementation notes of
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.Algebraic`.

No cuspidality is imposed on either side: condition (e) in the Borel-Jacquet definition is not
formalised, since it needs Haar integration over `N(ℚ) \ N(𝔸)`. Nor is algebraicity, and it
would be wrong to impose it: functoriality is conjectured for all automorphic forms, including
the non-algebraic ones such as a generic Maass form. See
`FormalConjectures.Langlands.ClozelAlgebraicity` for the algebraicity conjecture, which is an
independent axis over the same infrastructure.

## Status

For `m = 2` the symmetric power lands in `GL (k + 1)`, and for `f` coming from a holomorphic
modular form the conjecture is a theorem of Newton and Thorne [NT21a], [NT21b], for all `k`;
before that, the cases `k = 2, 3, 4` were known through the work of Gelbart-Jacquet,
Kim-Shahidi and Kim. For general automorphic eigenforms on `GL 2` (in particular for Maass
forms), and for general `m`, it is open, and it is a central open instance of functoriality:
the symmetric power `L`-functions it controls imply, among other things, the
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
