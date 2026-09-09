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
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

/-!
# The `p`-adic spherical Hecke pair

`GL n ℤ_[p]` is a Hecke subgroup of `GL n ℚ_[p]`. This is the case of
`Matrix.GeneralLinearGroup.isHeckePair_integralSubgroup` in which the spherical Hecke algebra
and its Satake parameters live, so it is what makes those definitions concrete rather than
hypothetical.

The one thing to check is that the residue rings of `ℤ_[p]` are finite. Every nonzero `a` is
associated to a power of `p`, since `ℤ_[p]` is a discrete valuation ring, and
`ℤ_[p] ⧸ (p ^ n) ≃ ZMod (p ^ n)`.
-/

open Matrix

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The residue rings of `ℤ_[p]` are finite. -/
theorem finite_quotient_span_singleton {a : ℤ_[p]} (ha : a ≠ 0) :
    Finite (ℤ_[p] ⧸ Ideal.span {a}) := by
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
    (PadicInt.irreducible_p (p := p))
  have hspan : Ideal.span {a} = Ideal.span {(p : ℤ_[p]) ^ n} :=
    Ideal.span_singleton_eq_span_singleton.mpr hn
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  rw [hspan, ← PadicInt.ker_toZModPow n]
  exact Finite.of_equiv _ (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow n))).symm.toEquiv

end PadicInt

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]

/-- **`GL n ℤ_[p]` is a Hecke subgroup of `GL n ℚ_[p]`**, so the spherical Hecke operators and
Satake parameters exist for it with no further hypotheses. -/
theorem isHeckePair_integralSubgroup_padic :
    Subgroup.IsHeckePair (integralSubgroup n ℤ_[p] ℚ_[p]) :=
  isHeckePair_integralSubgroup fun _ ha => PadicInt.finite_quotient_span_singleton ha

end Matrix.GeneralLinearGroup
