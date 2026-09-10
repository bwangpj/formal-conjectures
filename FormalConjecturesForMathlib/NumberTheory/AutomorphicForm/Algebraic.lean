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

public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.Eigenform

@[expose] public section

/-!
# Algebraic automorphic forms

Clozel's notion of an **algebraic** automorphic form for `GL m / ℚ`, at the level of a single
form rather than of an automorphic representation. An automorphic form in the sense of
Borel-Jacquet satisfies condition (c), that the centre `Z(𝔤)` of the universal enveloping
algebra of `𝔤𝔩 m ℂ` annihilates it through an ideal of finite codimension. Here we ask for the
stronger condition that `Z(𝔤)` act by a *character* `χ`, the **infinitesimal character** of
the form, and then that `χ` be one of the characters cut out by an integral weight.

## The algebraicity condition

Clozel's condition is that the infinitesimal character be integral. Rather than parametrise
characters of `Z(𝔤)` through the Harish-Chandra isomorphism, which needs the
Poincaré-Birkhoff-Witt theorem and is not available in Mathlib, we use the equivalent
formulation: `χ` is the character by which `Z(𝔤)` acts on the highest weight vector `v_λ` of
the Verma module `M(λ)` of integral highest weight `λ`. Since `v_λ` generates `M(λ)` and `z`
is central, that is the single condition

`z - χ z ∈ Ann (v_λ) = U(𝔤) 𝔫⁺ + ∑_h U(𝔤) (h - λ h)`,

which is `vermaAnnihilator` below. This is literally Clozel's definition, extended to singular
weights, so weight `0` Maass forms are covered. Nothing has to be proved to state it; what PBW
would buy is the agreement of this parametrisation with the usual one.

## Main declarations

All in the namespace `Matrix.GeneralLinearGroup`:

* `IsStrictlyUpper` and `diagWeight`: the raising subalgebra `𝔫⁺` of `𝔤𝔩 m ℂ`, and the linear
  functional on the diagonal Cartan subalgebra `𝔥` attached to a weight.
* `vermaAnnihilator`: the left ideal of `U(𝔤𝔩 m ℂ)` annihilating the highest weight vector of
  the Verma module of highest weight `lam`.
* `HasHighestWeight` and `HasHarishChandraParameter`: a character of the centre is the one
  attached to the weight `lam`, respectively to the shifted weight `ν = lam + ρ`. Neither
  determines the weight: only its orbit under the Weyl group `S m`.
* `symPowWeightFamily`: the effect of the `k`-th symmetric power on a Harish-Chandra
  parameter, the additive analogue of `Satake.symPowTransferFamily`. This is the archimedean
  half of Langlands functoriality; see
  `FormalConjectures.Langlands.SymmetricPowerFunctoriality`.
* `archSlices`: the family of archimedean slices `y ↦ f (x, y)` of an automorphic form, the
  object that `Z(𝔤)` acts on in condition (c).
* `HasInfinitesimalCharacter`: `Z(𝔤)` acts on every archimedean slice by the scalar `χ z`. It
  is unique for a nonzero form (`HasInfinitesimalCharacter.unique`) and it implies condition
  (c) (`HasInfinitesimalCharacter.isZFinite`).
* `IsCAlgebraic` and `IsLAlgebraic`: the form has an infinitesimal character whose highest
  weight, respectively whose Harish-Chandra parameter, is integral. The two differ by the
  shift `ρ`, so they agree for `GL 1` (`isCAlgebraic_iff_isLAlgebraic_one`) and in general are
  exchanged by a twist; `isCAlgebraic_iff` and `isLAlgebraic_iff` state each in the other's
  parametrisation.

## Implementation notes

`IsCAlgebraic` is not exercised on an example here. The natural sanity check, that the constant
function `1` is C-algebraic with `lam = 0`, amounts to identifying `constantsCharacter` with
the character of the trivial representation, and that identification is exactly the
Harish-Chandra computation which needs PBW. The two properties of `HasInfinitesimalCharacter`
that are proved, uniqueness and condition (c), are what pin the definition down without it.

Both algebraicity conditions are defined, and neither is proved to be exchanged by the twist
`f ↦ f * |det| ^ ((m - 1) / 2)`: that twist is an operation on automorphic forms which is not
formalised, so the relation between `IsCAlgebraic` and `IsLAlgebraic` is recorded only through
their weight parametrisations. For the algebraicity conjecture the distinction does not matter,
its conclusion being insensitive to the normalisation; for reciprocity it does, and there
`IsLAlgebraic` is the right hypothesis. See
`FormalConjectures.Langlands.ClozelAlgebraicity`.

*References:*
 - L. Clozel, *Motifs et formes automorphes: applications du principe de fonctorialité*, in
   Automorphic Forms, Shimura Varieties, and `L`-functions I, Perspect. Math. 10 (1990),
   77-159; Définition 1.8 and Conjecture 2.1.
 - K. Buzzard and T. Gee, *The conjectural connections between automorphic representations and
   Galois representations*, in Automorphic Forms and Galois Representations I, LMS Lecture Note
   Series 414 (2014), 135-187. https://arxiv.org/abs/1009.0785
-/

namespace Matrix.GeneralLinearGroup

open AutomorphicForm

open scoped IsDedekindDomain.FiniteAdeleRing

variable {m : ℕ}

/-! ### The raising subalgebra and the weights of the diagonal Cartan subalgebra -/

/-- `X : 𝔤𝔩 m ℂ` is **strictly upper triangular**. These matrices form the raising subalgebra
`𝔫⁺` of `𝔤𝔩 m ℂ`, with respect to the diagonal Cartan subalgebra and the standard order on the
coordinates. -/
def IsStrictlyUpper (X : Matrix (Fin m) (Fin m) ℂ) : Prop := ∀ i j, j ≤ i → X i j = 0

@[simp]
lemma isStrictlyUpper_zero : IsStrictlyUpper (0 : Matrix (Fin m) (Fin m) ℂ) := by
  simp [IsStrictlyUpper]

/-- The value at the diagonal matrix `diagonal d` of the linear functional on the diagonal
Cartan subalgebra `𝔥` of `𝔤𝔩 m ℂ` attached to the weight `lam`. In coordinates
`lam (diagonal d) = ∑ i, d i * lam i`, so the weight `lam` is read off as the tuple of its
values on the standard basis of `𝔥`. -/
def diagWeight (lam : Fin m → ℂ) (d : Fin m → ℂ) : ℂ := ∑ i, d i * lam i

@[simp]
lemma diagWeight_zero (lam : Fin m → ℂ) : diagWeight lam 0 = 0 := by simp [diagWeight]

/-! ### The annihilator of a highest weight vector -/

/-- The image of the raising subalgebra `𝔫⁺` in `U(𝔤𝔩 m ℂ)`. -/
noncomputable def raisingSet (m : ℕ) : Set (universalEnveloping (Fin m)) :=
  {u | ∃ X : Matrix (Fin m) (Fin m) ℂ, IsStrictlyUpper X ∧ u = UniversalEnvelopingAlgebra.ι ℂ X}

/-- The elements `h - lam h` of `U(𝔤𝔩 m ℂ)`, for `h` in the diagonal Cartan subalgebra `𝔥`.
Together with `raisingSet` these generate the annihilator of the highest weight vector of the
Verma module of highest weight `lam`. -/
noncomputable def cartanShiftSet (lam : Fin m → ℂ) : Set (universalEnveloping (Fin m)) :=
  {u | ∃ d : Fin m → ℂ, u = UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d)
    - algebraMap ℂ (universalEnveloping (Fin m)) (diagWeight lam d)}

/-- The left ideal `U(𝔤) 𝔫⁺ + ∑_h U(𝔤) (h - lam h)` of `U(𝔤𝔩 m ℂ)`, the annihilator of the
highest weight vector `v_lam` of the Verma module `M (lam)` of highest weight `lam`.

An element `z` of the centre acts on `v_lam` by a scalar `c` exactly when `z - c` lies in this
left ideal, and then, `v_lam` generating `M (lam)` and `z` being central, `z` acts by `c` on
all of `M (lam)`. This is how `IsCAlgebraic` names a character of the centre without the
Harish-Chandra isomorphism. -/
noncomputable def vermaAnnihilator (lam : Fin m → ℂ) :
    Submodule ℂ (universalEnveloping (Fin m)) :=
  Submodule.span ℂ
    {u | ∃ v : universalEnveloping (Fin m), ∃ w ∈ raisingSet m ∪ cartanShiftSet lam, u = v * w}

lemma mul_mem_vermaAnnihilator {lam : Fin m → ℂ} (v : universalEnveloping (Fin m))
    {w : universalEnveloping (Fin m)} (hw : w ∈ raisingSet m ∪ cartanShiftSet lam) :
    v * w ∈ vermaAnnihilator lam :=
  Submodule.subset_span ⟨v, w, hw, rfl⟩

/-- The raising subalgebra annihilates the highest weight vector. -/
lemma ι_mem_vermaAnnihilator_of_isStrictlyUpper {lam : Fin m → ℂ}
    {X : Matrix (Fin m) (Fin m) ℂ} (hX : IsStrictlyUpper X) :
    UniversalEnvelopingAlgebra.ι ℂ X ∈ vermaAnnihilator lam := by
  have h := mul_mem_vermaAnnihilator (lam := lam) 1 (Or.inl ⟨X, hX, rfl⟩)
  simpa using h

/-- The Cartan subalgebra acts on the highest weight vector through the weight. -/
lemma diagonal_sub_mem_vermaAnnihilator (lam : Fin m → ℂ) (d : Fin m → ℂ) :
    UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d)
      - algebraMap ℂ (universalEnveloping (Fin m)) (diagWeight lam d)
      ∈ vermaAnnihilator lam := by
  have h := mul_mem_vermaAnnihilator (lam := lam) 1 (Or.inr ⟨d, rfl⟩)
  simpa using h

/-! ### Highest weights and Harish-Chandra parameters -/

/-- `χ` is the character by which the centre of `U(𝔤𝔩 m ℂ)` acts on the highest weight vector
of the Verma module of highest weight `lam`.

This does not determine `lam`: two weights give the same character exactly when their
Harish-Chandra parameters `lam + ρ` are in the same orbit of the Weyl group `S m`. Statements
about the weight of a form therefore quantify over all weights it has, the way statements
about Satake parameters use a multiset. -/
def HasHighestWeight (χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ)
    (lam : Fin m → ℂ) : Prop :=
  ∀ z : ↥(centerUniversalEnveloping (Fin m)),
    (z : universalEnveloping (Fin m)) - algebraMap ℂ (universalEnveloping (Fin m)) (χ z)
      ∈ vermaAnnihilator lam

/-- Half the sum of the positive roots of `GL m`, as a weight:
`ρ = ((m - 1) / 2, (m - 3) / 2, …, -(m - 1) / 2)`, so `ρ i = (m - 1) / 2 - i`. Its entries are
half-integers for `m` even. -/
noncomputable def rho (m : ℕ) : Fin m → ℂ := fun i => ((m : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- `χ` is the infinitesimal character whose **Harish-Chandra parameter** is `ν`, that is the
character of highest weight `ν - ρ`.

The Harish-Chandra parameter is the shifted weight, and it is the parameter on which
functoriality acts additively: an `L`-homomorphism multiplies Satake parameters and adds
Harish-Chandra parameters, the latter being exponents of the former. Like the highest weight
it is determined only up to the Weyl group. -/
def HasHarishChandraParameter
    (χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ) (ν : Fin m → ℂ) : Prop :=
  HasHighestWeight χ (ν - rho m)

/-- The Harish-Chandra parameter of the character of highest weight `lam` is `lam + ρ`. -/
theorem hasHarishChandraParameter_add_rho
    {χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ} {lam : Fin m → ℂ} :
    HasHarishChandraParameter χ (lam + rho m) ↔ HasHighestWeight χ lam := by
  have h : lam + rho m - rho m = lam := add_sub_cancel_right lam (rho m)
  unfold HasHarishChandraParameter
  rw [h]

/-! ### The archimedean symmetric power transfer

The effect of the `k`-th symmetric power on Harish-Chandra parameters. It is the additive
analogue of `Satake.symPowTransferFamily`, which is the same construction with products in
place of sums: an `L`-homomorphism acts on Satake parameters by multiplying them and on
archimedean parameters by adding them, the archimedean parameters being the exponents.

The two land in the same rank, `(m + k - 1).choose k`, indexed the same way by the unordered
`k`-tuples `Sym (Fin m) k`, which is the consistency check that they describe one and the same
transfer `GL m → GL ((m + k - 1).choose k)`.
-/

/-- Transfer of Harish-Chandra parameters along the `k`-th symmetric power
`GL m ℂ → GL ((m + k - 1).choose k) ℂ`, the parameter given as an indexed family
`ν : Fin m → ℂ`: the sums of `k` of the `ν j` with repetition, one for each unordered
`k`-tuple of indices. The additive analogue of `Satake.symPowTransferFamily`. -/
noncomputable def symPowWeightFamily {m : ℕ} (k : ℕ) (ν : Fin m → ℂ) : Multiset ℂ :=
  (Finset.univ : Finset (Sym (Fin m) k)).val.map fun s : Sym (Fin m) k =>
    ((s : Multiset (Fin m)).map ν).sum

/-- The archimedean transfer has the rank of the target group, matching
`Satake.card_symPowTransferFamily`. -/
@[simp]
theorem card_symPowWeightFamily {m : ℕ} (k : ℕ) (ν : Fin m → ℂ) :
    Multiset.card (symPowWeightFamily k ν) = (m + k - 1).choose k := by
  rw [symPowWeightFamily, Multiset.card_map, ← Finset.card_def, Finset.card_univ,
    Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The archimedean transfer depends only on the *multiset* of parameters: reindexing the
family by a permutation just permutes the sums. This is what makes it well defined on a
Harish-Chandra parameter, which is only given up to the Weyl group. -/
theorem symPowWeightFamily_comp_perm {m k : ℕ} (ν : Fin m → ℂ) (σ : Equiv.Perm (Fin m)) :
    symPowWeightFamily k (ν ∘ σ) = symPowWeightFamily k ν := by
  rw [symPowWeightFamily, symPowWeightFamily]
  have he : ((Finset.univ : Finset (Sym (Fin m) k)).val.map (Sym.equivCongr σ))
      = (Finset.univ : Finset (Sym (Fin m) k)).val := by
    have h := congrArg Finset.val (Finset.map_univ_equiv (Sym.equivCongr σ (n := k)))
    rw [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  conv_rhs => rw [← he, Multiset.map_map]
  refine Multiset.map_congr rfl fun s _ => ?_
  show ((s : Multiset (Fin m)).map (ν ∘ σ)).sum
    = (((Sym.map σ s : Sym (Fin m) k) : Multiset (Fin m)).map ν).sum
  rw [Sym.coe_map, Multiset.map_map]

/-! ### The infinitesimal character of an automorphic form -/

variable [NeZero m]

/-- The family of archimedean slices `y ↦ f (x, y)` of an automorphic form, indexed by the
finite-adelic variable `x`. This is the object on which the centre of the universal enveloping
algebra acts in condition (c) of the Borel-Jacquet definition. -/
noncomputable def archSlices (f : automorphicForms (Fin m)) :
    GL (Fin m) 𝔸ᶠ[ℤ, ℚ] → smoothGL (Fin m) :=
  fun x => ⟨fun y => (f : GL (Fin m) 𝔸ᶠ[ℤ, ℚ] × GL (Fin m) ℝ → ℂ) (x, y),
    f.2.smooth.smoothOnGL x⟩

@[simp]
lemma archSlices_apply_apply (f : automorphicForms (Fin m)) (x : GL (Fin m) 𝔸ᶠ[ℤ, ℚ])
    (y : GL (Fin m) ℝ) :
    ((archSlices f x : smoothGL (Fin m)) : GL (Fin m) ℝ → ℂ) y =
      (f : GL (Fin m) 𝔸ᶠ[ℤ, ℚ] × GL (Fin m) ℝ → ℂ) (x, y) := rfl

/-- `f` has **infinitesimal character `χ`**: the centre of the universal enveloping algebra of
`𝔤𝔩 m ℂ` acts on the archimedean slices of `f`, by left invariant differential operators,
through the character `χ`.

This is a strengthening of condition (c) in the Borel-Jacquet definition of an automorphic
form, which only asks that some ideal of finite codimension annihilate `f`
(`HasInfinitesimalCharacter.isZFinite`). Every automorphic representation contains vectors
with an infinitesimal character, so nothing of interest is excluded by asking for one. -/
def HasInfinitesimalCharacter (f : automorphicForms (Fin m))
    (χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ) : Prop :=
  ∀ z : ↥(centerUniversalEnveloping (Fin m)), z • archSlices f = χ z • archSlices f

namespace HasInfinitesimalCharacter

variable {f : automorphicForms (Fin m)}
  {χ χ' : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ}

/-- Having an infinitesimal character implies condition (c): the kernel of the character is an
ideal of finite codimension annihilating the form. -/
theorem isZFinite (h : HasInfinitesimalCharacter f χ) :
    IsZFinite ℂ ↥(centerUniversalEnveloping (Fin m)) (archSlices f) :=
  IsZFinite.of_forall_smul_eq_algHom_smul χ h

/-- The infinitesimal character of a nonzero form is unique. This is what makes the
algebraicity condition `IsCAlgebraic` a condition on the form. -/
theorem unique (hf : f ≠ 0) (h : HasInfinitesimalCharacter f χ)
    (h' : HasInfinitesimalCharacter f χ') : χ = χ' := by
  have hval : (f : GL (Fin m) 𝔸ᶠ[ℤ, ℚ] × GL (Fin m) ℝ → ℂ) ≠ 0 :=
    fun hz => hf (ZeroMemClass.coe_eq_zero.mp hz)
  obtain ⟨⟨x₁, x₂⟩, hx⟩ := Function.ne_iff.mp hval
  ext z
  -- the two eigenvalue equations agree, so compare them where `f` does not vanish
  have h1 := (h z).symm.trans (h' z)
  have h2 := congrFun h1 x₁
  rw [Pi.smul_apply, Pi.smul_apply] at h2
  have h3 := congrArg (fun φ : smoothGL (Fin m) => (φ : GL (Fin m) ℝ → ℂ) x₂) h2
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, archSlices_apply_apply] at h3
  exact mul_right_cancel₀ hx h3

end HasInfinitesimalCharacter

/-! ### C-algebraic forms -/

/-- `f` is **C-algebraic** in the sense of Clozel: it has an infinitesimal character `χ`, and
`χ` is the character by which the centre acts on the highest weight vector of the Verma module
of some *integral* highest weight `lam : Fin m → ℤ`.

Integrality of the weight is the whole content; the Verma module formulation is a way of naming
the character attached to `lam` without the Harish-Chandra isomorphism. Singular weights are
allowed, so this covers weight `0` Maass forms. -/
def IsCAlgebraic (f : automorphicForms (Fin m)) : Prop :=
  ∃ χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ, HasInfinitesimalCharacter f χ ∧
    ∃ lam : Fin m → ℤ, HasHighestWeight χ (fun i => (lam i : ℂ))

/-- A C-algebraic form has an infinitesimal character, hence satisfies condition (c). -/
theorem IsCAlgebraic.isZFinite {f : automorphicForms (Fin m)} (h : IsCAlgebraic f) :
    IsZFinite ℂ ↥(centerUniversalEnveloping (Fin m)) (archSlices f) := by
  obtain ⟨χ, hχ, -⟩ := h
  exact hχ.isZFinite

/-- `f` is **C-algebraic** exactly when its Harish-Chandra parameter lies in `ρ + ℤ ^ m`. This
is the shifted form of the condition, and the one to compare with `IsLAlgebraic`. -/
theorem isCAlgebraic_iff {f : automorphicForms (Fin m)} :
    IsCAlgebraic f ↔ ∃ χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ,
      HasInfinitesimalCharacter f χ ∧ ∃ lam : Fin m → ℤ,
        HasHarishChandraParameter χ ((fun i => (lam i : ℂ)) + rho m) := by
  refine exists_congr fun χ => and_congr_right fun _ => exists_congr fun lam => ?_
  exact hasHarishChandraParameter_add_rho.symm

/-- `f` is **L-algebraic** in the sense of Buzzard-Gee: it has an infinitesimal character whose
Harish-Chandra parameter is *integral*.

Equivalently the highest weight lies in `-ρ + ℤ ^ m`, so for `m` even an L-algebraic form is
never C-algebraic and conversely, while for `m` odd both conditions can hold of the same form,
consistently, since the twist relating them exists in both directions. L-algebraic is the
condition under which the Satake parameters should match Frobenius characteristic polynomials
without a further twist, which is why it, rather than `IsCAlgebraic`, is the hypothesis of the
reciprocity conjecture. The two are related by `f ↦ f * |det| ^ ((m - 1) / 2)`. -/
def IsLAlgebraic (f : automorphicForms (Fin m)) : Prop :=
  ∃ χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ, HasInfinitesimalCharacter f χ ∧
    ∃ ν : Fin m → ℤ, HasHarishChandraParameter χ (fun i => (ν i : ℂ))

/-- An L-algebraic form has an infinitesimal character, hence satisfies condition (c). -/
theorem IsLAlgebraic.isZFinite {f : automorphicForms (Fin m)} (h : IsLAlgebraic f) :
    IsZFinite ℂ ↥(centerUniversalEnveloping (Fin m)) (archSlices f) := by
  obtain ⟨χ, hχ, -⟩ := h
  exact hχ.isZFinite

/-- `f` is **L-algebraic** exactly when its highest weight lies in `-ρ + ℤ ^ m`. -/
theorem isLAlgebraic_iff {f : automorphicForms (Fin m)} :
    IsLAlgebraic f ↔ ∃ χ : ↥(centerUniversalEnveloping (Fin m)) →ₐ[ℂ] ℂ,
      HasInfinitesimalCharacter f χ ∧ ∃ ν : Fin m → ℤ,
        HasHighestWeight χ ((fun i => (ν i : ℂ)) - rho m) := by
  refine exists_congr fun χ => and_congr_right fun _ => exists_congr fun ν => ?_
  rfl

/-- For `GL 1` the two conditions agree: `ρ = 0`, so the shift relating them is trivial. -/
theorem isCAlgebraic_iff_isLAlgebraic_one {f : automorphicForms (Fin 1)} :
    IsCAlgebraic f ↔ IsLAlgebraic f := by
  have hrho : rho 1 = 0 := by
    funext i
    simp [rho]
  refine exists_congr fun χ => and_congr_right fun _ => exists_congr fun lam => ?_
  rw [HasHarishChandraParameter, hrho, sub_zero]

end Matrix.GeneralLinearGroup
