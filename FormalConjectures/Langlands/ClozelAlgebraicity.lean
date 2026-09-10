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
# Clozel's algebraicity conjecture for `GL m` over `ℚ`

An algebraic automorphic form should have algebraic Hecke eigenvalues. Precisely: if `f` is an
automorphic eigenform for `GL m / ℚ` which is C-algebraic, meaning that the centre of the
universal enveloping algebra of `𝔤𝔩 m ℂ` acts on `f` through the character attached to an
integral weight (`IsCAlgebraic`), then at every prime where `f` is unramified its system of
spherical Hecke eigenvalues consists of algebraic numbers, and so do its Satake parameters.

This is the first half of the conjectural picture relating automorphic forms to Galois
representations: it is what turns the complex numbers produced by Hecke operators into
elements of a number field, so that one can then ask for a compatible system of `p`-adic
Galois representations with those Frobenius characteristic polynomials. Stated on its own it
mentions no Galois representations at all, which is why it can be formalised today.

## Normalisation

The conjecture is usually stated for the *normalised* Satake parameters, and the normalisation
differs between the C-algebraic and L-algebraic conventions: the Hecke polynomial has
coefficients `p ^ (i.choose 2) * a i` in the first (which is the convention of
`Satake.heckePolynomial`, so the parameters here are the C-normalised ones) and
`p ^ (- i * (m - i) / 2) * a i` in the second. The two differ by the factor
`p ^ (i * (m - 1) / 2)`, a rational power of `p`, which is a nonzero algebraic number. So
algebraicity of the eigenvalues, of the C-normalised parameters and of the L-normalised
parameters are all the same assertion, and the statement below is stated for the raw
eigenvalues `a i`.

For the same reason the C-algebraic and L-algebraic versions of the conjecture carry the same
content. The twist `f ↦ f * |det| ^ ((m - 1) / 2)` carries C-algebraic forms to L-algebraic
ones and multiplies the eigenvalues by rational powers of `p`, so each version follows from the
other. Both hypotheses are formalised, `IsCAlgebraic` asking for an integral highest weight and
`IsLAlgebraic` for an integral Harish-Chandra parameter, and both versions of the conjecture
are stated, since the twist relating them is an operation on automorphic forms that is not
formalised. This insensitivity to the normalisation is special to algebraicity; a statement
about Frobenius characteristic polynomials would have to commit to one convention, and would
take `IsLAlgebraic`.

## Cuspidality

Clozel states the conjecture for cuspidal automorphic representations. Neither cuspidality nor
automorphic representations are available here: condition (e) in the Borel-Jacquet definition,
that the constant term along every unipotent radical vanishes, is not formalised, since it
needs Haar integration over `N(ℚ) \ N(𝔸)`. So the statement below quantifies over all
C-algebraic automorphic eigenforms, cuspidal or not, and is in that respect formally stronger
than Clozel's conjecture. The same caveat applies to
`FormalConjectures.Langlands.SymmetricPowerFunctoriality`.

## Status

Known when the weight is regular, that is when the `lam i` are distinct: such forms are
cohomological, and their Hecke eigenvalues are eigenvalues of Hecke correspondences acting on
the rational cohomology of a locally symmetric space, hence algebraic. The conjecture is open
in general, the smallest open case being that of weight `0` Maass forms on `GL 2`, where the
weight is as singular as possible. Regularity is not formalised here, so the statements below
are the unrestricted ones.

## References

- [Cl90] L. Clozel, *Motifs et formes automorphes: applications du principe de fonctorialité*,
  in Automorphic Forms, Shimura Varieties, and `L`-functions I, Perspect. Math. 10 (1990),
  77-159; Définition 1.8 for algebraicity and Conjecture 2.1 for the conjecture.
- [BG14] K. Buzzard, T. Gee, *The conjectural connections between automorphic representations
  and Galois representations*, in Automorphic Forms and Galois Representations I, LMS Lecture
  Note Series 414 (2014), 135-187. https://arxiv.org/abs/1009.0785
- [Wikipedia](https://en.wikipedia.org/wiki/Langlands_program)
-/

namespace ClozelAlgebraicity

open Matrix.GeneralLinearGroup

/-- **Clozel's algebraicity conjecture** for `GL m` over `ℚ`: the spherical Hecke eigenvalues
of a C-algebraic automorphic eigenform are algebraic numbers.

Known for regular weights, where the form is cohomological; open in general, the smallest open
case being weight `0` Maass forms on `GL 2`. -/
@[category research open, AMS 11]
theorem clozel_algebraicity (m : ℕ) [NeZero m] (f : automorphicForms (Fin m))
    (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f) (p : Nat.Primes)
    (a : Fin (m + 1) → ℂ) (ha : HasHeckeEigensystemAt p f a) (i : Fin (m + 1)) :
    IsAlgebraic ℚ (a i) := by
  sorry

/-- **Clozel's algebraicity conjecture**, on Satake parameters: at every unramified prime the
Satake parameters of a C-algebraic automorphic eigenform are algebraic numbers.

Equivalent to `clozel_algebraicity`, the parameters being the roots of the Hecke polynomial,
whose coefficients are the eigenvalues up to integer powers of `p`. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.satake_parameters (m : ℕ) [NeZero m]
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f)
    (p : Nat.Primes) (a : Fin (m + 1) → ℂ) (ha : HasHeckeEigensystemAt p f a) (α : ℂ)
    (hα : α ∈ Satake.satakeParameters (p : ℕ) a) :
    IsAlgebraic ℚ α := by
  sorry

/-- **Clozel's algebraicity conjecture**, L-algebraic version: the spherical Hecke eigenvalues
of an L-algebraic automorphic eigenform are algebraic numbers.

Carries the same content as `clozel_algebraicity`. The twist `f ↦ f * |det| ^ ((m - 1) / 2)`
carries C-algebraic forms to L-algebraic ones and multiplies the eigenvalues by rational powers
of `p`, so each version follows from the other; that twist is not formalised, so the two are
stated separately. L-algebraic is the hypothesis under which the parameters should match
Frobenius characteristic polynomials with no further twist, so this is the version reciprocity
builds on. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.l_algebraic (m : ℕ) [NeZero m]
    (f : automorphicForms (Fin m)) (hf : IsAutomorphicEigenform f) (hL : IsLAlgebraic f)
    (p : Nat.Primes) (a : Fin (m + 1) → ℂ) (ha : HasHeckeEigensystemAt p f a)
    (i : Fin (m + 1)) :
    IsAlgebraic ℚ (a i) := by
  sorry

/-- **Clozel's algebraicity conjecture** for `GL 1` over `ℚ`: the values of an algebraic Hecke
character are algebraic numbers. Here the C- and L-algebraic hypotheses coincide, `ρ` being
zero (`isCAlgebraic_iff_isLAlgebraic_one`).

This is the classical case: an algebraic Hecke character of `ℚ` is a Dirichlet character times
an integer power of the norm, so its values at `p` are a root of unity times a power of `p`.
It is stated here as an instance of the general conjecture rather than proved, the
classification of Hecke characters not being available. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.gl_one (f : automorphicForms (Fin 1))
    (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f) (p : Nat.Primes)
    (a : Fin (1 + 1) → ℂ) (ha : HasHeckeEigensystemAt p f a) (i : Fin (1 + 1)) :
    IsAlgebraic ℚ (a i) := by
  sorry

/-- **Clozel's algebraicity conjecture** for `GL 2` over `ℚ`: the case `m = 2`, where the two
Satake parameters at an unramified prime `p` are the roots of `X ^ 2 - a 1 * X + p * a 2`.
The open case is that of Maass forms, whose weight is singular. -/
@[category research open, AMS 11]
theorem clozel_algebraicity.variants.gl_two (f : automorphicForms (Fin 2))
    (hf : IsAutomorphicEigenform f) (hC : IsCAlgebraic f) (p : Nat.Primes)
    (a : Fin (2 + 1) → ℂ) (ha : HasHeckeEigensystemAt p f a) (i : Fin (2 + 1)) :
    IsAlgebraic ℚ (a i) := by
  sorry

end ClozelAlgebraicity
