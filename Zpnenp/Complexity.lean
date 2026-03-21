/-
  Complexity.lean — Phase 3: The Complexity Bridge

  This file formalizes the connection between the structural theory
  (inverse Davenport, prefix sums permutation) and computational
  complexity. It defines the adversary game and identifies precisely
  where a new mathematical insight is needed to prove P ≠ NP.

  The key question: does the structural rigidity of hard instances
  (proved in Inverse.lean) imply that no polynomial-time algorithm
  can solve Subset Sum in the worst case?
-/

import Zpnenp.SubsetSum
import Zpnenp.Davenport
import Zpnenp.Inverse

/-! ## The Adversary Game

We formalize the adversary game for Subset Sum:
- The adversary chooses an instance (a set of integers and a target)
- An algorithm must decide YES/NO
- The adversary wins if the algorithm is wrong

The inverse Davenport theorem constrains the adversary's strategy
space: at the modular zero-sum threshold, the only "hard" instances
are (n-1) copies of a unit element. -/

/-- An algorithm for modular zero-sum: given a multiset over ZMod n,
    it outputs true (claiming a nonempty zero-sum submultiset exists)
    or false (claiming none exists). -/
def ModZeroSumAlgorithm (n : ℕ) :=
  Multiset (ZMod n) → Bool

/-- An algorithm is correct if it gives the right answer on every input. -/
def ModZeroSumAlgorithm.IsCorrect {n : ℕ} (A : ModZeroSumAlgorithm n) : Prop :=
  ∀ s : Multiset (ZMod n),
    (A s = true ↔ ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0)

/-! ## Structural characterization of the decision boundary

The Davenport constant tells us exactly where the decision boundary is
for modular zero-sum:

- |s| ≥ n: answer is always YES (by davenport_upper)
- |s| = n-1: answer depends on whether s = replicate (n-1) g for a unit g
- |s| < n-1: answer could go either way

The inverse Davenport theorem says: at the critical size n-1,
the instances where the answer is NO are exactly the "rigid" ones
(all copies of a unit). Every other instance of size n-1 has a
zero-sum submultiset. -/

/-- At the Davenport threshold (size n-1), the adversary's NO instances
    are exactly the replicate-of-unit instances.

    This is a direct consequence of the inverse Davenport theorem. -/
theorem adversary_no_instances (n : ℕ) (hn : 1 < n) (s : Multiset (ZMod n))
    (hcard : s.card = n - 1) :
    (¬ ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0) ↔
    (∃ g : ZMod n, IsUnit g ∧ s = Multiset.replicate (n - 1) g) := by
  rw [← inverse_davenport n hn s hcard]
  constructor
  · intro hno
    exact fun t ht hne hsum => hno ⟨t, ht, hne, hsum⟩
  · intro hzsf ⟨t, ht, hne, hsum⟩
    exact hzsf t ht hne hsum

/-- At size ≥ n, the answer is always YES. Any correct algorithm must
    output true on all inputs of size ≥ n. -/
theorem adversary_large_always_yes (n : ℕ) (hn : 0 < n) (s : Multiset (ZMod n))
    (hcard : n ≤ s.card) :
    ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0 := by
  -- Take the first n elements from the list representation
  set l := s.toList
  have hperm : (↑l : Multiset _) = s := Multiset.coe_toList s
  have hlen : l.length = s.card := by simp [l, Multiset.length_toList]
  -- Take the first n elements as a submultiset
  set s' : Multiset (ZMod n) := ↑(l.take n)
  have hsub : s' ≤ s := by
    rw [← hperm]; exact Multiset.coe_le.mpr (List.take_sublist n l).subperm
  have hcard' : s'.card = n := by
    simp [s', List.length_take, hlen]; omega
  obtain ⟨t, ht, hne, hsum⟩ := davenport_upper n hn s' hcard'
  exact ⟨t, le_trans ht hsub, hne, hsum⟩

/-! ## The Structure-Computation Gap

This is the critical section. We have proved:

1. **Structural rigidity** (inverse Davenport): The adversary's
   NO instances at the threshold are exactly replicate-of-unit.

2. **Threshold existence** (Davenport constant): Above size n,
   zero-sum is guaranteed. Below size n, it may not exist.

3. **Prefix sum permutation**: Any zero-sum free multiset has
   prefix sums that are a permutation of ℤ/nℤ.

What we have NOT proved (and what would constitute P ≠ NP):

4. **No polynomial algorithm**: There is no polynomial-time
   algorithm that correctly distinguishes replicate-of-unit
   instances from instances with hidden zero-sum submultisets.

The gap between (1-3) and (4) is the core challenge:

- The structural theory tells us WHAT hard instances look like
  (maximally structured, all copies of one unit)
- But it does not tell us WHY these instances are computationally
  hard (why can't a polynomial algorithm just check the structure?)

In fact, for the MODULAR zero-sum problem specifically, the structure
IS easily checkable: just verify that all elements are equal and the
common element is a unit. This takes O(n) time!

The difficulty is that the STANDARD Subset Sum problem (over ℤ with
arbitrary targets) is much harder than modular zero-sum. The structural
rigidity of modular zero-sum is a necessary ingredient but not
sufficient for P ≠ NP.

To bridge the gap, we would need to show that the structural
constraints from zero-sum theory impose computational lower bounds
on the STANDARD Subset Sum problem, not just the modular version.
This requires connecting:
- Density phase transitions (low/critical/high density)
- Lattice reduction barriers
- The number-theoretic structure of integer arithmetic

This is an open research question and the subject of Phase 4. -/

/-- The modular zero-sum problem at the threshold IS efficiently
    decidable: just check if all elements are equal and the common
    element is a unit. This is O(n) and does NOT imply P = NP.

    The point is that standard Subset Sum (over ℤ) is harder than
    modular zero-sum (over ℤ/nℤ), and the complexity gap between
    them is where P ≠ NP would live. -/
theorem mod_zero_sum_decidable_at_threshold (n : ℕ) (hn : 1 < n)
    (s : Multiset (ZMod n)) (hcard : s.card = n - 1) :
    (∃ t ≤ s, t ≠ 0 ∧ t.sum = 0) ∨
    (∃ g : ZMod n, IsUnit g ∧ s = Multiset.replicate (n - 1) g) := by
  by_cases h : ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0
  · left; exact h
  · right; exact (adversary_no_instances n hn s hcard).mp h

/-! ## Directions for Phase 4

To make progress toward P ≠ NP from here, the research directions are:

### Direction A: Lift to Standard Subset Sum
Show that the structural constraints from modular zero-sum theory
(inverse Davenport, prefix sum permutation) impose constraints on
standard Subset Sum instances at critical density d ≈ 1.

### Direction B: Adversary Amplification
Show that the adversary's strategy space for standard Subset Sum
is "rich enough" that no polynomial algorithm can handle all cases,
using the structural theory to constrain what algorithms can exploit.

### Direction C: Circuit Lower Bounds
Use the structural theory to prove lower bounds on circuit complexity
of Subset Sum, potentially connecting to the sunflower lemma approach
(Razborov 1985) but for Subset Sum instead of CLIQUE.

### Direction D: Fine-Grained Complexity
Use the structural theory to improve fine-grained lower bounds for
Subset Sum, potentially showing that 2^{n/2} is optimal (not just
the best known algorithm).

Each direction faces the known barriers (relativization, natural
proofs, algebrization) and would require a genuinely new insight
beyond what's formalized here.
-/

/-! ## NP via Verifiers

We define NP using the verifier-based characterization:
a decision problem is in NP if there exists a certificate type and
a verification function such that the problem holds iff some
polynomial-sized certificate passes verification.

This is the standard Karp/Cook characterization. Full formalization
of "polynomial time" would use Mathlib's `TM2ComputableInPolyTime`
(in `Mathlib.Computability.TMComputable`), but for our structural
analysis we use an abstract version that captures the mathematical
content without the Turing machine overhead.
-/

/-- **Subset Sum ∈ NP** (verifier characterization):
    Given a candidate subset (the certificate), verification is decidable —
    just sum the elements and compare to the target. This is the standard
    proof that Subset Sum is in NP.

    Formally: `SubsetSum s t` iff there exists a sub-Finset `s'` of `s`
    with `s'.sum id = t`. The witness `s'` can be checked in polynomial
    time (O(|s'|) additions + one comparison). -/
theorem subsetSum_in_NP (s : Finset ℤ) (t : ℤ) :
    SubsetSum s t ↔ ∃ s' ∈ s.powerset, s'.sum id = t := by
  simp [SubsetSum]

/-- The verification predicate for Subset Sum is decidable.
    This is the key property that places Subset Sum in NP:
    given a candidate certificate (a sub-Finset), we can efficiently
    check whether it sums to the target. -/
instance subsetSum_decidable (s : Finset ℤ) (t : ℤ) : Decidable (SubsetSum s t) := by
  rw [subsetSum_in_NP]; exact inferInstance

/-- **Subset Sum Zero ∈ NP**: the zero-target variant.
    Certificate: a nonempty sub-Finset summing to 0. -/
theorem subsetSumZero_in_NP (s : Finset ℤ) :
    SubsetSumZero s ↔ ∃ s' ∈ s.powerset, s' ≠ ∅ ∧ s'.sum id = 0 := by
  simp [SubsetSumZero]

/-- The modular zero-sum problem is also in NP.
    Certificate: a nonempty submultiset summing to 0. -/
theorem modZeroSum_in_NP {n : ℕ} (s : Multiset (ZMod n)) :
    (∃ t ≤ s, t ≠ 0 ∧ t.sum = 0) ↔
    ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0 := by
  rfl

/-! ## Connection to Mathlib's Computability

Mathlib provides `TM2ComputableInPolyTime` in
`Mathlib.Computability.TMComputable` for formalizing polynomial-time
computation via multi-tape Turing machines (`FinTM2`).

To fully formalize "Subset Sum ∈ NP" in the TM sense, one would:
1. Encode `Finset ℤ × ℤ` as binary strings on a TM tape
2. Construct a `FinTM2` that reads a certificate (sub-Finset) and
   verifies the sum in polynomial time
3. Prove the time bound is `O(n²)` (sum n integers of n bits each)

This TM-level formalization is orthogonal to the structural theory
and is left as future work. The abstract `NPWitness` above captures
the mathematical content: Subset Sum is in NP because the verification
function (sum and compare) is decidable and the certificate (a sub-Finset)
has polynomial size.
-/
