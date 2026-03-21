/-
  Structural.lean — Structural properties of subset sums

  We formalize properties connecting the structure of a set of integers
  to its subset sum behavior, drawing on additive combinatorics.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Zpnenp.SubsetSum

open Finset

/-! ## Counting subset sums -/

/-- The number of achievable subset sums is at most 2^|s|,
    since there are 2^|s| subsets. -/
theorem card_subsetSums_le (s : Finset ℤ) :
    (subsetSums s).card ≤ 2 ^ s.card := by
  calc (subsetSums s).card
      ≤ s.powerset.card := card_image_le
    _ = 2 ^ s.card := card_powerset s

/-!
## The Density Argument (Informal)

When the integers in s are bounded by some maximum value M,
there are only 2M+1 possible sum values in [-M*n, M*n].
But there are 2^n subsets. When 2^n > 2*M*n + 1, by pigeonhole,
two distinct subsets must have the same sum, meaning their
symmetric difference sums to zero.

This is the basis of the Lagarias-Odlyzko density argument:
at "high density" (n / log₂(max aᵢ) >> 1), Subset Sum instances
are trivially YES because collisions are forced.

At "low density" (n / log₂(max aᵢ) << 1), lattice reduction (LLL)
solves the problem efficiently.

The "hard core" is the intermediate density regime d ≈ 1.

TODO: Formalize the pigeonhole density argument
TODO: Formalize the density definition d = n / log₂(max aᵢ)
-/

/-! ## Structure of Hard Instances

From inverse zero-sum theory, the "hardest" instances (those that
maximally avoid having zero-sum subsets) are HIGHLY STRUCTURED:
- Zero-sum-free sequences of maximal length in ℤ/nℤ consist of
  (n-1) copies of a single element coprime to n
- Near-extremal sequences are supported on very few group elements

From Freiman's theorem, if the set of achievable subset sums is
small (|subsetSums(s)| ≤ K|s|), then s must be contained in a
generalized arithmetic progression of bounded dimension.

These structural results constrain what "hard" instances look like,
potentially limiting the adversary's ability to construct inputs
that defeat polynomial-time algorithms.
-/

/-! ## The Density-Structure Connection

The density of a Subset Sum instance (n / log₂(max weight)) determines
which structural regime the instance falls into:

**High density** (d >> 1): Many elements relative to weight range.
The pigeonhole principle forces subset sum collisions (proved in
Density.lean: `pigeonhole_collision`). The set of achievable sums
covers most of the range. Structurally: the sumset A+A is very large
relative to A (the "growing" case from Freiman.lean).

**Low density** (d << 1): Few elements relative to weight range.
Lattice reduction methods (LLL algorithm) can find solutions.
Structurally: the elements are sparse, so the sumset grows slowly.

**Critical density** (d ≈ 1): The boundary between high and low density.
This is where neither pigeonhole nor lattice methods directly apply.
Structurally: this is the regime where the Freiman dichotomy
(growing vs. structured) is most relevant.

The key insight: at critical density, the sum-product phenomenon
(from SumProduct.lean) creates a TENSION — the adversary cannot
simultaneously make the additive structure (sumset) and the
multiplicative structure (choice vectors in {0,1}^n) both "small."
-/

/-- The achievable subset sums always include 0 (from the empty subset).
    Combined with the singletons, we get |subsetSums s| ≥ |s| + 1
    when all elements are nonzero. -/
theorem card_subsetSums_ge (s : Finset ℤ) (hs : ∀ x ∈ s, x ≠ 0) :
    s.card + 1 ≤ (subsetSums s).card := by
  have h0 : (0 : ℤ) ∈ subsetSums s := by
    simp only [subsetSums, mem_image, mem_powerset]
    exact ⟨∅, empty_subset _, by simp⟩
  have h_sing : ∀ x ∈ s, x ∈ subsetSums s := by
    intro x hx; simp only [subsetSums, mem_image, mem_powerset]
    exact ⟨{x}, singleton_subset_iff.mpr hx, by simp⟩
  have h_disj : (0 : ℤ) ∉ s := fun h0s => hs 0 h0s rfl
  have hsub : insert (0 : ℤ) s ⊆ subsetSums s := by
    intro x hx; rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact h0
    · exact h_sing x hx
  calc s.card + 1 = (insert (0 : ℤ) s).card := (Finset.card_insert_of_notMem h_disj).symm
    _ ≤ (subsetSums s).card := card_le_card hsub

/-- For a nonempty set of nonzero integers, the subset sums strictly
    outnumber the elements. This is the "growth" phenomenon:
    the empty-subset sum 0 provides a new achievable value. -/
theorem subsetSums_growth (s : Finset ℤ) (_hs_ne : s.Nonempty)
    (hs_nz : ∀ x ∈ s, x ≠ 0) :
    s.card < (subsetSums s).card := by
  have := card_subsetSums_ge s hs_nz; omega

/-! ## Hard Core Characterization

Combining the density analysis with the structural theory:

1. **High density**: |subsetSums s| is large (close to the full range).
   By `pigeonhole_collision` (Density.lean), collisions exist, making
   the problem "easy" for collision-based algorithms.

2. **Low density**: Elements are sparse. Lattice methods work.

3. **Critical density with growing sumset**: |A+A| > |A|, so by
   Cauchy-Davenport / iterated sumset growth (Freiman.lean),
   the achievable sums cover a large fraction of the target range.
   Random/birthday-paradox algorithms are effective.

4. **Critical density with small sumset**: |A+A| ≤ K|A|, so by
   Freiman's theorem, A sits inside a generalized arithmetic
   progression. This rigid structure enables specialized algorithms
   (lattice reduction in the progression's coordinates).

5. **Critical density with large product set**: |A·A| is large
   (from sum-product theorem, SumProduct.lean). The multiplicative
   growth creates many distinct subset sums through the interaction
   of additive and multiplicative structure.

**The adversary's dilemma**: Cases 1-5 cover all possibilities.
In each case, some algorithmic approach has structural leverage.
The P ≠ NP question reduces to: is this structural leverage
sufficient for POLYNOMIAL-TIME algorithms in ALL cases?

This is precisely the gap identified in our formalization:
the structural theory constrains WHAT hard instances look like,
but does not (yet) show that the structure enables polynomial-time
solutions.
-/
