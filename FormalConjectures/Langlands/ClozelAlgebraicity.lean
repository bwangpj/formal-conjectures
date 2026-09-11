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
# The Clozel-Buzzard-Gee algebraicity conjecture for `GL m` over `ℚ`

An algebraic automorphic form should be arithmetic. Precisely: if `f` is an automorphic
eigenform for `GL m / ℚ` which is L-algebraic, meaning that the centre of the universal
enveloping algebra of `𝔤𝔩 m ℂ` acts on `f` through a character with integral Harish-Chandra
parameter (`IsLAlgebraic`), then there is a *single* number field `E` such that at almost
every prime the L-normalised Satake parameters of `f` lie in `E`.

This is the first half of the conjectural picture relating automorphic forms to Galois
representations: it is what turns the complex numbers produced by Hecke operators into
elements of a number field, so that one can then ask for a compatible system of `p`-adic
Galois representations with those Frobenius characteristic polynomials. Stated on its own it
mentions no Galois representations at all, which is why it can be formalised today.

## The field `E`, and why it is in the statement

`[BG14]` Definition 3.1.3 asks for one number field `E` that works at almost all places, not
merely that each eigenvalue be an algebraic number. The uniformity is the content, not
packaging. L-arithmetic and C-arithmetic differ only by the factor `p ^ (i * (m - 1) / 2)`,
which is an algebraic number but does not lie in a fixed `E`; so if one weakens the conclusion
to "each eigenvalue is algebraic", the L- and C-versions of the conjecture become the same
assertion and neither `[BG14]` Conjecture 3.1.5 nor 3.1.6 is being stated. The statements
below therefore all carry `E`.

## Normalisation, and why the conclusions carry a half-power of `p`

`Satake.heckePolynomial` is the *arithmetic* normalisation of Clozel and Gross: its
coefficients are `p ^ (i.choose 2) * a i`, involving only nonnegative integer powers of `p`.
That normalisation is the one that pairs with C-algebraicity, which is why
`FormalConjectures.Langlands.WeakReciprocity` takes `IsCAlgebraic`. The L-normalised Satake
parameters are the arithmetic ones divided by `p ^ ((m - 1) / 2)`, so an L-arithmeticity
statement about a form whose eigenvalues are recorded arithmetically must divide by that
half-power.

That half-power is `Complex.cpow`, `p ^ z = exp (log p * z)` for the principal `Complex.log`.
No branch is being chosen: `p` is a positive real, so its principal logarithm is `Real.log p`
and `p ^ (k / 2)` is the positive real number `(√p) ^ k`, which is the number `[BG14]` write.
For `m = 1` the exponent is `0` and the half-power is `1`, the two normalisations agreeing
there.

## Cuspidality

Clozel states the conjecture for cuspidal automorphic representations. Neither cuspidality nor
automorphic representations are available here: condition (e) in the Borel-Jacquet definition,
that the constant term along every unipotent radical vanishes, is not formalised, since it
needs Haar integration over `N(ℚ) \ N(𝔸)`. So the statements below quantify over all
L-algebraic automorphic eigenforms, cuspidal or not, and are in that respect formally stronger
than Clozel's conjecture. The same caveat applies to
`FormalConjectures.Langlands.SymmetricPowerFunctoriality`.

## Status

Known when the Harish-Chandra parameter is regular, that is when the `ν i` are distinct: such
a form is cohomological (`[Clo90]` Lemme 3.14, a regular algebraic representation of `GL m` is
cohomological after a quadratic twist; `[BG14]` §7.2 for the converse direction), and the
Hecke eigenvalues of a cohomological form are eigenvalues of Hecke correspondences acting on
the rational cohomology of a locally symmetric space, hence lie in a number field. In `[BG14]`
terms this is §3.3, where the conjecture is proved for a cuspidal representation of `GL 2 / ℚ`
which is discrete series at infinity. The conjecture is open in general, the smallest open case
being that of weight `0` Maass forms on `GL 2`, where the parameter is as singular as possible
(`[BG14]` §3.1: for `GL 2 / ℚ` with principal series at infinity, both directions are open).
Regularity is not formalised here, so the statements below are the unrestricted ones.

A weight `0` Maass form has Harish-Chandra parameter `(0, 0)`, so it is L-algebraic and, `ρ`
being `(1 / 2, -1 / 2)` for `m = 2`, *not* C-algebraic: for even `m` the two conditions are
disjoint. This is the reason the file is organised around `IsLAlgebraic`: its running example,
and the smallest open case, is an L-algebraic form.

## Relation to the reference statements

`[BG14]` splits the conjecture into an archimedean condition and a finite-place condition:
*L-algebraic* (Definition 3.1.1, our `IsLAlgebraic`) and *C-algebraic* (Definition 3.1.2, our
`IsCAlgebraic`) constrain `π` at the infinite places, while *L-arithmetic* (Definition 3.1.3)
and *C-arithmetic* (Definition 3.1.4) ask for a single number field `E` such that at almost
every finite place `v` the Satake parameter of `π_v` is defined over `E`, respectively `π_v`
itself is defined over `E` (the two senses of "defined over `E`" being Definition 2.2.2(ii)
and (i)). Conjecture 3.1.5 asserts L-arithmetic ⟺ L-algebraic and Conjecture 3.1.6 asserts
C-arithmetic ⟺ C-algebraic.

The statements below are the "algebraic implies arithmetic" direction of those conjectures.
At an unramified place, where all of them are asserted, `π_v` is determined by its Satake
parameter, so Definition 2.2.2(i)'s condition that `π_v ^ σ ≅ π_v` for every
`σ ∈ Aut(ℂ / E)` says the arithmetically normalised eigenvalues are `σ`-fixed, hence in `E`;
that is what `variants.c_algebraic` says. The converse direction, arithmetic implies algebraic,
is a transcendence statement and is not formalised at all.

## References

- [Clo90] L. Clozel, *Motifs et formes automorphes: applications du principe de
  fonctorialité*, in Automorphic Forms, Shimura Varieties, and `L`-functions I, Perspect.
  Math. 10 (1990), 77-159. Clozel calls a representation of `GL n` *algébrique* when it is
  C-algebraic and isobaric (`[BG14]` §8.1); Conjectures 3.7 and 4.5 attach Galois
  representations to such a representation, Proposition 3.1(iii) deduces arithmeticity of the
  local data from that, and Lemme 3.14 is the regular case discussed under Status. Clozel is,
  per `[BG14]` §3.1, the first to have raised these conjectures explicitly, for `G = GL n`.
- [BG14] K. Buzzard, T. Gee, *The conjectural connections between automorphic representations
  and Galois representations*, in Automorphic Forms and Galois Representations I, LMS Lecture
  Note Series 414 (2014), 135-187; Definitions 2.2.2, 3.1.1-3.1.4 and Conjectures 3.1.5,
  3.1.6, as described above. https://arxiv.org/abs/1009.0785
- [Ta04] R. Taylor, *Galois representations*, Ann. Fac. Sci. Toulouse Math. (6) 13 (2004),
  73-119; Conjecture 3.4, whose first assertion, that each `rec_p(π_p)` can be defined over
  `ℚ̄`, is this conjecture for a cuspidal representation whose infinitesimal character `H` is
  a multiset of *integers*, that is for an L-algebraic form.
  https://www.numdam.org/item/AFST_2004_6_13_1_73_0/
- [Sar02] P. Sarnak, *Maass cusp forms with integer coefficients*, in A Panorama of Number
  Theory, Cambridge Univ. Press (2002), 121-127; the converse direction for `GL 2 / ℚ`.
- [Bru03] F. Brumley, *Maass cusp forms with quadratic integer coefficients*, Int. Math. Res.
  Not. (2003), no. 18, 983-997; the same converse over certain quadratic fields.
- [Wal81] M. Waldschmidt, *Transcendance et exponentielles en plusieurs variables*, Invent.
  Math. 63 (1981), 97-127; the converse direction for `GL 1`.
- [Wikipedia](https://en.wikipedia.org/wiki/Langlands_program)
-/

namespace ClozelAlgebraicity

open Matrix.GeneralLinearGroup

/-- **The algebraicity conjecture**, `[BG14]` Conjecture 3.1.5 in the direction L-algebraic
implies L-arithmetic: an L-algebraic automorphic eigenform for `GL m / ℚ` admits a single
number field `E` containing its L-normalised Hecke eigenvalues at almost every prime.

Here `a i` is the arithmetically normalised eigenvalue, the `i`-th coefficient of
`Satake.heckePolynomial` up to the rational factor `p ^ (i.choose 2)`; the L-normalisation
divides the `i`-th one by `p ^ (i * (m - 1) / 2)`. See the *Normalisation* section above for
that half-power, and *The field `E`* for why the conclusion is not merely that the eigenvalues
are algebraic.

Known for regular Harish-Chandra parameters, where the form is cohomological; open in general,
the smallest open case being weight `0` Maass forms on `GL 2`. -/
@[category research open, AMS 11]
theorem clozel_algebraicity (m : ℕ) [NeZero m] (f : automorphicForms (Fin m))
    (hf : IsAutomorphicEigenform f) (hL : IsLAlgebraic f) :
    ∃ E : IntermediateField ℚ ℂ, FiniteDimensional ℚ E ∧ ∃ S : Finset Nat.Primes,
      ∀ p ∉ S, ∀ a : Fin (m + 1) → ℂ, HasHeckeEigensystemAt p f a →
        ∀ i : Fin (m + 1),
          a i / ((p : ℕ) : ℂ) ^ (((((i : ℕ) * (m - 1) : ℕ) : ℂ)) / 2) ∈ E := by
  sorry

/-- **The algebraicity conjecture, on Satake parameters**: at almost every prime the
L-normalised Satake parameters of an L-algebraic automorphic eigenform lie in one number
field `E`.

Equivalent to `clozel_algebraicity`, the parameters being the roots of the Hecke polynomial,
whose coefficients are the eigenvalues up to integer powers of `p`. This is the form closest to
`[BG14]` Definition 3.1.3, whose local condition is Definition 2.2.2(ii), that the Satake
parameter be defined over `E`, which for `GL m` is by Lemma 2.2.6 the condition that the Satake
conjugacy class contain an element of `GL m E`. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.satake_parameters (m : ℕ) [NeZero m]
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) (hL : IsLAlgebraic f) :
    ∃ E : IntermediateField ℚ ℂ, FiniteDimensional ℚ E ∧ ∃ S : Finset Nat.Primes,
      ∀ p ∉ S, ∀ a : Fin (m + 1) → ℂ, HasHeckeEigensystemAt p f a →
        ∀ α ∈ Satake.satakeParameters (p : ℕ) a,
          α / ((p : ℕ) : ℂ) ^ ((((m - 1 : ℕ) : ℂ)) / 2) ∈ E := by
  sorry

/-- **The algebraicity conjecture, C-algebraic version**, `[BG14]` Conjecture 3.1.6 in the
direction C-algebraic implies C-arithmetic: for a C-algebraic form the *arithmetically*
normalised eigenvalues themselves lie in a single number field, with no half-power of `p`.

This is the version that pairs with `Satake.heckePolynomial`, hence with
`FormalConjectures.Langlands.WeakReciprocity`, whose hypothesis is likewise `IsCAlgebraic`.
It is a genuinely different assertion from `clozel_algebraicity`, not a restatement: for even
`m` the two hypotheses are disjoint, and the two conclusions differ by `p ^ (i * (m - 1) / 2)`,
which is not in `E`. The twist `f ↦ f * |det| ^ ((m - 1) / 2)` carries C-algebraic forms to
L-algebraic ones and would relate the two, but is an operation on automorphic forms that is not
formalised.

The local condition of `[BG14]` Definition 3.1.4 is Definition 2.2.2(i), that `π_v` be defined
over `E`; at an unramified place `π_v` is determined by its Satake parameter, so that condition
is exactly membership of the eigenvalues in `E`. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.c_algebraic (m : ℕ) [NeZero m]
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f) :
    ∃ E : IntermediateField ℚ ℂ, FiniteDimensional ℚ E ∧ ∃ S : Finset Nat.Primes,
      ∀ p ∉ S, ∀ a : Fin (m + 1) → ℂ, HasHeckeEigensystemAt p f a →
        ∀ i : Fin (m + 1), a i ∈ E := by
  sorry

end ClozelAlgebraicity
