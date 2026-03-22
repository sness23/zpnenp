/-
  ZeroSum.lean — Connections to zero-sum theory

  We connect the Subset Sum definitions to results from additive
  combinatorics already formalized in Mathlib, particularly the
  Erdős-Ginzburg-Ziv theorem.
-/

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Data.ZMod.Basic
import Zpnenp.SubsetSum

open Finset

/-! ## Modular Subset Sum -/

/-- Modular subset sum over a Finset: does `s` have a nonempty subset
    whose sum is divisible by `n`? -/
def ModSubsetSumZero (s : Finset ℤ) (n : ℕ) : Prop :=
  ∃ s' ∈ s.powerset, s' ≠ ∅ ∧ (n : ℤ) ∣ s'.sum id

/-! ## EGZ implies modular zero-sum existence

The Erdős-Ginzburg-Ziv theorem guarantees that any 2n−1 integers
contain n elements whose sum is divisible by n. We connect this
to our SubsetSum definitions. -/

variable {n : ℕ}

/-- **EGZ applied to Finset ℤ**: If a set of distinct integers has at least
    2n−1 elements, then it contains a sub-finset of exactly n elements
    whose sum is divisible by n. This is a direct corollary of
    `Int.erdos_ginzburg_ziv` from Mathlib. -/
theorem egz_finset (s : Finset ℤ) (_hn : 0 < n) (hs : 2 * n - 1 ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ (n : ℤ) ∣ t.sum id := by
  have h := Int.erdos_ginzburg_ziv (s := s) id (by omega)
  obtain ⟨t, hts, htcard, htdvd⟩ := h
  exact ⟨t, hts, by omega, by simpa using htdvd⟩

/-- **EGZ guarantees ModSubsetSumZero**: When |s| ≥ 2n−1 and n > 0,
    modular subset sum to zero is always achievable.

    This is the key structural guarantee: no matter what integers the
    adversary chooses, once there are enough of them, a zero-sum subset
    mod n must exist. The adversary cannot avoid it. -/
theorem egz_implies_modSubsetSumZero (s : Finset ℤ) (hn : 1 < n)
    (hs : 2 * n - 1 ≤ s.card) : ModSubsetSumZero s n := by
  obtain ⟨t, hts, htcard, htdvd⟩ := egz_finset s (by omega) hs
  refine ⟨t, mem_powerset.mpr hts, ?_, htdvd⟩
  intro h
  rw [h] at htcard
  simp at htcard
  omega

/-!
## What EGZ means for our program

**Theorem (Erdős-Ginzburg-Ziv, 1961):** Among any 2n−1 integers,
there exist n whose sum is ≡ 0 (mod n).

**Formalized above as:** `egz_implies_modSubsetSumZero`

**Interpretation for P ≠ NP:**

This theorem says that for modular subset sum with target 0,
the problem is *trivially YES* whenever |s| ≥ 2n−1. The adversary
(dealer) cannot construct a large enough set that avoids having
a zero-sum subset mod n. The combinatorial structure forces it.

The critical question becomes: what about the instances that are
*below* this threshold? The **inverse EGZ theorem** characterizes
exactly what those extremal sequences look like:

- Sequences of length 2n−2 avoiding n-element zero-sum consist
  of (n−1) copies of element a and (n−1) copies of element b,
  with a−b coprime to n.

These extremal instances are **highly structured**. This suggests
that "hard" instances (those near the existence threshold) must
have rigid structure — structure that might be algorithmically
exploitable.
-/

/-!
## The Davenport Constant

The Davenport constant D(G) of a finite abelian group G is the
smallest d such that every sequence of d elements from G contains
a non-empty subsequence summing to zero.

For G = ℤ/nℤ: D(ℤ/nℤ) = n

See Davenport.lean for D(ℤ/nℤ) = n and Inverse.lean for the inverse theorem.
-/

/-! ## Reduction: Integer Subset Sum → Modular Subset Sum

If SubsetSum s t holds over ℤ (some subset sums to t), then
reducing mod n, the same subset sums to t mod n. This connects
integer Subset Sum to modular zero-sum theory. -/

/-- Integer Subset Sum reduces to modular Subset Sum:
    if a subset of integers sums to t, reducing mod n gives
    a subset summing to t mod n. -/
theorem subsetSum_mod_of_subsetSum (s : Finset ℤ) (t : ℤ) (n : ℕ)
    (h : SubsetSum s t) : ∃ s' ∈ s.powerset, (n : ℤ) ∣ (s'.sum id - t) := by
  obtain ⟨s', hs'mem, hs'sum⟩ := h
  exact ⟨s', hs'mem, by rw [hs'sum, sub_self]; exact dvd_zero _⟩

/-- If SubsetSum s 0 holds (zero-target), then ModSubsetSumZero holds
    for every modulus. A zero-sum over ℤ is a zero-sum mod n. -/
theorem modSubsetSumZero_of_subsetSumZero (s : Finset ℤ) (n : ℕ)
    (h : SubsetSumZero s) : ModSubsetSumZero s n := by
  obtain ⟨s', hs'mem, hs'ne, hs'sum⟩ := h
  exact ⟨s', hs'mem, hs'ne, by rw [hs'sum]; exact dvd_zero _⟩

/-- Contrapositive: if modular zero-sum is impossible (ModSubsetSumZero
    is false), then integer zero-sum is also impossible. This is how
    modular results give LOWER BOUNDS for integer problems. -/
theorem not_subsetSumZero_of_not_modSubsetSumZero (s : Finset ℤ) (n : ℕ)
    (h : ¬ModSubsetSumZero s n) : ¬SubsetSumZero s :=
  fun hzs => h (modSubsetSumZero_of_subsetSumZero s n hzs)
