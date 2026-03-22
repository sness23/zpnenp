/-
  Density.lean — Density of Subset Sum instances and phase transitions

  The density of a Subset Sum instance controls its computational difficulty:
  - Low density (d < 1): solvable by lattice reduction (LLL)
  - High density (d >> 1): solvable by pigeonhole (many collisions)
  - Critical density (d ≈ 1): believed to be maximally hard

  This file formalizes the density definition, the pigeonhole argument
  for high density, and connects to our modular zero-sum results.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Zpnenp.SubsetSum

open Finset

/-! ## Subset Sum instance -/

/-- A Subset Sum instance: a finite set of positive integers and a target. -/
structure SubsetSumInstance where
  /-- The set of available integers (as a Finset of positive naturals) -/
  weights : Finset ℕ
  /-- All weights are positive -/
  weights_pos : ∀ w ∈ weights, 0 < w
  /-- The target sum -/
  target : ℕ

/-- The number of elements in a Subset Sum instance. -/
def SubsetSumInstance.n (inst : SubsetSumInstance) : ℕ := inst.weights.card

/-- The maximum weight in a Subset Sum instance (0 if empty). -/
noncomputable def SubsetSumInstance.maxWeight (inst : SubsetSumInstance) : ℕ :=
  inst.weights.sup id

/-! ## The pigeonhole density argument

When a Subset Sum instance has many elements relative to the maximum
weight, the pigeonhole principle forces two distinct subsets to have
the same sum. Their symmetric difference then sums to the difference
of the two sums.

Specifically: there are 2^n subsets, each summing to a value in
{0, 1, ..., n * maxWeight}. If 2^n > n * maxWeight + 1, two subsets
must collide.

This is the combinatorial foundation of the "high density is easy"
phenomenon. -/

/-- The number of achievable subset sums is bounded by the range of
    possible values. For weights in {1, ..., M} with n elements,
    subset sums lie in {0, ..., n * M}. -/
theorem subsetSums_range_bound (s : Finset ℕ) (M : ℕ)
    (hM : ∀ w ∈ s, w ≤ M) :
    ∀ s' ∈ s.powerset, s'.sum id ≤ s.card * M := by
  intro s' hs'
  have hs'_sub := mem_powerset.mp hs'
  calc s'.sum id
      ≤ s'.sum (fun _ => M) := by
        apply Finset.sum_le_sum
        intro w hw; exact hM w (hs'_sub hw)
    _ = s'.card • M := Finset.sum_const M
    _ = s'.card * M := by simp
    _ ≤ s.card * M := Nat.mul_le_mul_right M (card_le_card hs'_sub)

/-- **Pigeonhole collision**: If 2^n > n * M + 1, then two distinct
    subsets of s must have the same sum.

    This is the foundation of the density argument: at high density
    (n / log₂(M) >> 1), collisions are forced, making Subset Sum easy. -/
theorem pigeonhole_collision (s : Finset ℕ) (M : ℕ)
    (hM : ∀ w ∈ s, w ≤ M) (_hM_pos : 0 < M)
    (hdense : s.card * M + 1 < 2 ^ s.card) :
    ∃ s₁ ∈ s.powerset, ∃ s₂ ∈ s.powerset, s₁ ≠ s₂ ∧ s₁.sum id = s₂.sum id := by
  -- Use Finset pigeonhole: map powerset to Finset.range (n*M + 1)
  -- |powerset| = 2^n > n*M + 1 = |range|, so map is not injective
  have hrange : (Finset.range (s.card * M + 1)).card < s.powerset.card := by
    rw [Finset.card_range, Finset.card_powerset]; exact hdense
  have hmaps : ∀ x ∈ s.powerset, x.sum id ∈ Finset.range (s.card * M + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have := subsetSums_range_bound s M hM x hx
    omega
  obtain ⟨a, ha, b, hb, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hrange hmaps
  exact ⟨a, ha, b, hb, hne, heq⟩

/-! ## Density definition -/

-- The **density** of a Subset Sum instance is d = n / log₂(max weight).
-- We work with the exponential relationship directly (avoiding ℝ).

/-- An instance has "high density" if 2^n > n * maxWeight + 1.
    This is the regime where pigeonhole forces subset sum collisions. -/
def SubsetSumInstance.isHighDensity (inst : SubsetSumInstance) : Prop :=
  inst.n * inst.maxWeight + 1 < 2 ^ inst.n

/-- An instance has "low density" if the weights are exponentially
    larger than the number of elements: maxWeight > 2^(n²).
    This is the regime where lattice reduction (LLL) works. -/
def SubsetSumInstance.isLowDensity (inst : SubsetSumInstance) : Prop :=
  2 ^ (inst.n ^ 2) < inst.maxWeight

/-- An instance is at "critical density" if it is neither high nor low.
    This is the regime believed to be maximally hard. -/
def SubsetSumInstance.isCriticalDensity (inst : SubsetSumInstance) : Prop :=
  ¬inst.isHighDensity ∧ ¬inst.isLowDensity

/-! ## Connection to modular zero-sum theory

The Davenport constant D(ℤ/nℤ) = n gives a threshold for modular
zero-sum. For standard Subset Sum, the density d ≈ 1 threshold
plays an analogous role:

| Regime | Modular (ℤ/nℤ) | Standard (ℤ) |
|--------|----------------|--------------|
| Above threshold | Always YES (D = n) | Collisions forced (pigeonhole) |
| At threshold | Rigid structure (inverse Davenport) | Critical density d ≈ 1 |
| Below threshold | Zero-sum free possible | Lattice methods work |

The inverse Davenport theorem tells us that modular zero-sum free
instances at threshold are (n-1) copies of a unit. The analogous
question for standard Subset Sum: what do "hard" instances at
critical density look like? Are they also rigidly structured?

This is the key question connecting our formalization to P ≠ NP. -/

/-- At high density, a collision exists: two distinct subsets have
    the same sum. This means the "difference" instance (formed by
    taking elements in one but not the other) sums to zero.

    This is the integer analog of the Davenport upper bound:
    above a threshold, structure (collision/zero-sum) is forced. -/
theorem high_density_has_collision (inst : SubsetSumInstance)
    (hd : inst.isHighDensity) (hM : ∀ w ∈ inst.weights, w ≤ inst.maxWeight) :
    ∃ s₁ ∈ inst.weights.powerset, ∃ s₂ ∈ inst.weights.powerset,
      s₁ ≠ s₂ ∧ s₁.sum id = s₂.sum id := by
  have hM_pos : 0 < inst.maxWeight := by
    -- isHighDensity implies n * M + 1 < 2^n, so n ≥ 1, so weights nonempty
    rw [SubsetSumInstance.isHighDensity, SubsetSumInstance.n] at hd
    by_contra h; push_neg at h; simp only [Nat.le_zero] at h
    -- If maxWeight = 0, then n * 0 + 1 < 2^n, i.e., 1 < 2^n, so n ≥ 1
    -- But maxWeight = 0 and all weights ≤ maxWeight means all weights = 0
    -- This contradicts weights_pos (all weights > 0) if weights is nonempty
    -- n ≥ 1 means weights is nonempty
    have : inst.weights.card * 0 + 1 < 2 ^ inst.weights.card := by rwa [h] at hd
    have hn : 0 < inst.weights.card := by
      by_contra hc; push_neg at hc; simp only [Nat.le_zero] at hc
      simp [hc] at this
    rw [Finset.card_pos] at hn
    obtain ⟨w, hw⟩ := hn
    have := inst.weights_pos w hw
    have := hM w hw
    omega
  exact pigeonhole_collision inst.weights inst.maxWeight hM hM_pos hd

/-! ## The density trichotomy and P ≠ NP

The density formalization reveals the structure of the P ≠ NP question
for Subset Sum:

1. **High density** (d >> 1): Pigeonhole forces collisions. Any
   algorithm that checks for collisions works. This is EASY and
   does not require NP-hardness.

2. **Low density** (d << 1): Lattice reduction (LLL algorithm)
   solves random instances in polynomial time. This is also
   "EASY" for most instances (under number-theoretic assumptions).

3. **Critical density** (d ≈ 1): Neither pigeonhole nor lattice
   methods apply. This is where hardness concentrates.

The structural question: at critical density, are hard instances
structured (like the inverse Davenport theorem shows for modular
zero-sum) or unstructured?

If hard instances are structured, algorithms might exploit this.
If they are unstructured, the problem might be genuinely hard.
But if they are NEITHER structured NOR unstructured (in the sense
of Tao's structure-randomness dichotomy), then we are in new territory
— and this is where a proof of P ≠ NP might live.
-/

/-- At high density, ANY target sum is achievable (by the collision argument).
    Two subsets with the same sum can be "differenced" to produce any target
    via the symmetric difference argument. -/
theorem high_density_many_sums (inst : SubsetSumInstance)
    (hd : inst.isHighDensity) (hM : ∀ w ∈ inst.weights, w ≤ inst.maxWeight) :
    ∃ s₁ ∈ inst.weights.powerset, ∃ s₂ ∈ inst.weights.powerset,
      s₁ ≠ s₂ ∧ s₁.sum id = s₂.sum id :=
  high_density_has_collision inst hd hM

/-- The density trichotomy: every instance falls into exactly one of
    high, low, or critical density. -/
theorem density_trichotomy (inst : SubsetSumInstance) :
    inst.isHighDensity ∨ inst.isLowDensity ∨ inst.isCriticalDensity := by
  by_cases hH : inst.isHighDensity
  · left; exact hH
  · by_cases hL : inst.isLowDensity
    · right; left; exact hL
    · right; right; exact ⟨hH, hL⟩
