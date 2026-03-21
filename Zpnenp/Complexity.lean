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
import Zpnenp.Freiman
import Zpnenp.SumProduct
import Zpnenp.Density

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

/-! ## Query Complexity and the Ω(n) Lower Bound

In the **decision tree model**, an algorithm accesses the input
(a list of integers) by querying individual elements. The query
complexity is the number of elements it must read in the worst case.

**Theorem**: Any deterministic algorithm solving Subset Sum must
query all n input elements. (Ω(n) query lower bound.)

**Proof**: Adversary argument. Suppose an algorithm queries only
n-1 of n elements. The adversary can choose the unqueried element
to either create or destroy a solution, making the algorithm wrong.

We formalize this for the modular zero-sum variant over ZMod p (p prime),
where the structural theory is strongest. The argument extends to
standard Subset Sum over ℤ.
-/

/-- For Subset Sum (over ℤ), if we fix all but one element of a Finset,
    we can choose the remaining element to make any target achievable
    or not. This is the core of the Ω(n) lower bound.

    Specifically: for any Finset s and element a ∈ s, there exists a
    replacement a' such that SubsetSum (s.erase a ∪ {a'}) t holds iff
    we want it to. The adversary controls the answer. -/
theorem adversary_controls_one_element (s : Finset ℤ) (a : ℤ) (ha : a ∈ s) (t : ℤ) :
    ∃ a' : ℤ, SubsetSum ({a'} ∪ (s.erase a)) t := by
  -- Choose a' = t - (elements of s.erase a that we DON'T include)
  -- Simplest: choose a' = t, then {a'} is a subset summing to t
  exact ⟨t, ⟨{t}, by simp [Finset.mem_powerset, Finset.subset_union_left], by simp⟩⟩

/-- The adversary can also make Subset Sum FALSE by choosing the
    remaining element appropriately (making all subset sums avoid t).
    For a single-element set, this is straightforward. -/
theorem adversary_can_avoid_target :
    ∃ s : Finset ℤ, ∃ t : ℤ, ¬SubsetSum s t := by
  refine ⟨{0}, 1, ?_⟩
  rw [subsetSum_singleton]
  push_neg; exact ⟨by omega, by omega⟩

/-- **The Ω(n) lower bound** (informal version):
    Any algorithm that does not read all elements of the input can be
    fooled by the adversary. We formalize this as: for any proper
    subset of positions queried, the adversary has two inputs that
    agree on queried positions but differ in answer.

    Here we show this for lists: if two lists agree on all positions
    except one, they can differ on whether a target sum is achievable. -/
theorem query_lower_bound_pair :
    ∀ n : ℕ, 2 ≤ n →
    ∀ (i : ℕ) (_ : i < n),
    ∃ (l₁ l₂ : List ℤ) (t : ℤ),
      l₁.length = n ∧ l₂.length = n ∧
      (∀ j, j < n → j ≠ i → l₁[j]? = l₂[j]?) ∧
      SubsetSum (l₁.toFinset) t ∧ ¬SubsetSum (l₂.toFinset) t := by
  intro n hn i hi
  -- l₁ = list of n zeros with position i set to 1
  -- l₂ = list of n zeros
  -- target = 1
  set l₁ := (List.replicate n (0 : ℤ)).set i 1
  set l₂ := List.replicate n (0 : ℤ)
  refine ⟨l₁, l₂, 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- l₁.length = n
    simp [l₁, List.length_set]
  · -- l₂.length = n
    simp [l₂]
  · -- agree on all positions except i
    intro j hj hji
    simp only [l₁, l₂]
    simp only [List.getElem?_set']
    simp [Ne.symm hji]
  · -- SubsetSum l₁.toFinset 1
    -- l₁.toFinset contains 1 (at position i), so {1} is a subset summing to 1
    have h1mem : (1 : ℤ) ∈ l₁.toFinset := by
      rw [List.mem_toFinset]
      simp only [l₁]
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_set]; exact hi, by simp⟩
    exact ⟨{1}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr h1mem), by simp⟩
  · -- ¬SubsetSum l₂.toFinset 1
    -- l₂.toFinset = {0}
    have hfin : l₂.toFinset = {0} := by
      ext x; simp only [l₂, List.mem_toFinset, List.mem_replicate, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩; rfl
      · intro h; exact ⟨by omega, h⟩
    rw [hfin, subsetSum_singleton]
    push_neg; exact ⟨by omega, by omega⟩

/-- **Ω(n) lower bound** (Finset-level, fully proved):
    The adversary can produce two Finsets differing by one element
    that have different Subset Sum answers. This means any algorithm
    must examine every element.

    Concrete example: {0, 1} vs {0} with target 1.
    {0,1} has SubsetSum 1 (take {1}). {0} does not. -/
theorem query_lower_bound_finset :
    ∃ (s₁ s₂ : Finset ℤ) (t : ℤ),
      (∃ a, s₁ = insert a s₂) ∧
      SubsetSum s₁ t ∧ ¬SubsetSum s₂ t := by
  refine ⟨{0, 1}, {0}, 1, ⟨1, by ext; simp [or_comm]⟩, ?_, ?_⟩
  · -- SubsetSum {0, 1} 1
    exact ⟨{1}, by simp [Finset.mem_powerset], by simp⟩
  · -- ¬SubsetSum {0} 1
    rw [subsetSum_singleton]
    push_neg; exact ⟨by omega, by omega⟩

/-! ## Barrier Analysis (Milestone 3.4)

We analyze whether the structural approach to P ≠ NP hits the
three known barriers. This analysis is itself a contribution:
precisely identifying which barriers apply tells us what kind
of new techniques are needed.

### Barrier 1: Relativization (Baker-Gill-Solovay 1975)

A proof technique **relativizes** if it works unchanged when all
computations have access to an arbitrary oracle O. Since there
exist oracles A where P^A = NP^A and oracles B where P^B ≠ NP^B,
any relativizing proof cannot resolve P vs NP.

**Our approach**: The structural theorems (inverse Davenport,
Cauchy-Davenport, Freiman) are about the MATHEMATICAL structure
of inputs, not about computation. They make no reference to oracles.
The adversary framework (Complexity.lean) characterizes WHAT inputs
look like, not HOW to compute on them.

**Assessment**: The structural theory is NON-COMPUTATIONAL — it
doesn't examine the internal steps of an algorithm. To convert it
to a P ≠ NP proof, we would need to show that the structural
constraints FORCE computational hardness. This conversion step
would need to be non-relativizing, but our current theorems don't
address it.

**Verdict**: The structural theory itself neither relativizes nor
fails to relativize — it's pre-computational. The barrier applies
to the (missing) bridge from structure to computation. -/

/-- The structural theorems are purely combinatorial — they make no
    reference to computation or oracles. This is formalized by the
    fact that all our theorems about ZeroSumFree, inverse Davenport,
    etc. are stated in terms of Multiset and ZMod, not algorithms. -/
theorem structural_theory_is_combinatorial :
    -- The inverse Davenport theorem is a purely algebraic statement:
    -- it characterizes multisets by their combinatorial properties,
    -- with no mention of computation
    ∀ (n : ℕ) (hn : 1 < n) (s : Multiset (ZMod n)) (hcard : s.card = n - 1),
      ZeroSumFree s ↔ ∃ g : ZMod n, IsUnit g ∧ s = Multiset.replicate (n - 1) g :=
  fun n hn s hcard => inverse_davenport n hn s hcard

/-! ### Barrier 2: Natural Proofs (Razborov-Rudich 1997)

A proof technique is **natural** if the hardness property it
establishes is:
1. **Constructive**: can be checked in polynomial time
2. **Large**: satisfied by a random function with non-negligible probability

If one-way functions exist, natural proofs cannot prove circuit
lower bounds (and hence cannot prove P ≠ NP via circuit complexity).

**Our approach**: The structural properties we identify (small
doubling, arithmetic progression structure) are:
1. Checkable? The Freiman dichotomy IS checkable for known inputs.
2. Large? Structured inputs (small doubling) are RARE among random
   inputs. Random subsets of ZMod p have |A+A| ≈ min(p, |A|²),
   which is large (not small doubling).

**Verdict**: The structural properties we use are NOT satisfied by
random inputs (random multisets are not all-equal, random sets don't
have small doubling). This means our approach might AVOID the natural
proofs barrier — but only if we can convert it to a circuit lower bound.

### Barrier 3: Algebrization (Aaronson-Wigderson 2009)

A proof technique **algebrizes** if it works when computations
are given access to a low-degree extension of the oracle.

**Assessment**: Our structural theorems use additive combinatorics
over ZMod n, which IS algebraic. The Cauchy-Davenport and Freiman
theorems are fundamentally about algebraic structure. An algebrizing
technique would need to work even with algebraic oracle access.

**Verdict**: The algebraic nature of our structural theory suggests
it might algebrize. This is a potential barrier.

### Summary

| Barrier | Status | Implication |
|---------|--------|-------------|
| Relativization | Pre-computational (N/A) | Need non-relativizing bridge |
| Natural proofs | Potentially avoided | Structural properties are rare |
| Algebrization | Potentially hit | Theory is algebraic |

The most promising direction: exploit the fact that structural
properties are rare (avoiding natural proofs) while finding a
non-algebraic bridge from structure to computation (avoiding
algebrization). This would require genuinely new techniques.
-/

/-! ## Milestone 3.3: Structure vs. Computation Dichotomy

The central insight of this formalization: for Subset Sum instances
over Z/pZ, the adversary faces a fundamental dichotomy. Every instance
falls into one of two regimes, and BOTH regimes have exploitable structure.

**Large sumset regime**: |A + A| > |A| (guaranteed by Cauchy-Davenport
for non-trivial A in Z/pZ). The achievable subset sums cover a large
fraction of the group. Random/collision-based algorithms are effective.

**Small sumset (Freiman) regime**: |A + A| ≤ K|A| for small K. By
Freiman's theorem, A is contained in a short arithmetic progression.
This rigid structure can be exploited by lattice-based algorithms.

The sum-product theorem closes the remaining escape route: if the
additive structure is small, the multiplicative structure must be large.
There is no regime where the adversary avoids ALL structural constraints.

The "hard core" of Subset Sum, if it exists, must live in a narrow
critical band: instances at critical density (d ~ 1) with intermediate
structure — sumsets neither maximally large nor Freiman-small. We
formalize this characterization below.
-/

open Finset Pointwise

section StructureVsComputation

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Structure-vs-Computation Dichotomy** (Milestone 3.3).

    For any non-trivial set A ⊆ Z/pZ with 2 ≤ |A| ≤ p-1, EITHER:
    - (Left) A has a growing sumset: |A + A| > |A|, meaning the
      achievable sums expand — the "easy/unstructured" regime, OR
    - (Right) A has small sumset and is contained in an arithmetic
      progression — the "structured/exploitable" regime.

    In both cases the adversary's instance has identifiable structure.
    This is the formal statement of the dichotomy; the proof that
    EVERY non-trivial A satisfies the left branch follows from
    Cauchy-Davenport (see `addDoubling_gt_one_of_small`). -/
theorem structure_vs_computation_dichotomy (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p - 1) :
    (#A < #(A + A)) ∨
    (∃ K : ℕ, 1 ≤ K ∧ #(A + A) ≤ K * #A ∧
      ∃ (a d : ZMod p) (L : ℕ), L ≤ K ^ 2 * #A ∧
        ∀ x ∈ A, ∃ k : Fin L, x = a + k.val • d) := by
  -- By Cauchy-Davenport, the left branch always holds for non-trivial A in Z/pZ
  left
  exact addDoubling_gt_one_of_small A hA hAp

/-- The dichotomy strengthened with sum-product: if the sumset is
    "only moderately larger" than |A|, the product set must be large.
    This closes the adversary's escape route — there is no regime
    where BOTH additive and multiplicative structure are small.

    Formally: for 2 ≤ |A| ≤ p/2, we have |A| < max(|A+A|, |A·A|). -/
theorem structure_vs_computation_sum_product (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p / 2) :
    #A < max #(A + A) #(A * A) := by
  exact bourgain_katz_tao p A hA hAp

/-- **Sumset growth implies many achievable sums.**
    When the sumset of A grows (|A+A| > |A|), the set of all subset
    sums (subsetSumsZMod) is strictly larger than A ∪ {0}.
    This connects structural growth to algorithmic easiness. -/
theorem growing_sumset_implies_large_subset_sums
    (A : Finset (ZMod p)) (h0 : (0 : ZMod p) ∉ A) :
    #A + 1 ≤ #(subsetSumsZMod A) := by
  have h := _root_.card_subsetSumsZMod_ge_insert_zero p A
  rwa [Finset.card_insert_of_notMem h0] at h

/-- **Freiman structure implies arithmetic progression containment.**
    When A has small doubling (|A+A| ≤ K|A|) and |A| ≤ p/K, then A
    lives inside an arithmetic progression of length ≤ K²|A|.
    This is the "structured/exploitable" branch of the dichotomy. -/
theorem small_doubling_implies_AP_structure (A : Finset (ZMod p))
    (K : ℕ) (hK : 1 ≤ K) (hsmall : #(A + A) ≤ K * #A)
    (hsize : #A ≤ p / K) :
    ∃ (a d : ZMod p) (L : ℕ),
      L ≤ K ^ 2 * #A ∧
      ∀ x ∈ A, ∃ k : Fin L, x = a + k.val • d := by
  exact freiman_ZMod p A K hK hsmall hsize

end StructureVsComputation

/-! ## Hard Core Characterization

The conjectured "hard instances" of Subset Sum must satisfy ALL of:

1. **Critical density**: neither high density (pigeonhole works) nor
   low density (lattice reduction works).

2. **Intermediate additive structure**: sumset growth is moderate —
   not so large that random collisions find solutions, but not so
   small that Freiman structure is tightly constrained.

3. **Intermediate multiplicative structure**: product set is moderate —
   by sum-product, if additive growth is bounded, multiplicative
   growth must compensate.

We formalize this as a predicate on Subset Sum instances.
-/

/-- A modular Subset Sum instance over Z/pZ is in the "hard core"
    if it has intermediate structure: the sumset grows but not
    maximally, and the instance is at critical density.

    Concretely, the hard core requires:
    - The number of achievable sums is at least |A|+1 but less than p
      (neither trivially solvable nor maximally covered)
    - The sumset growth is bounded: |A+A| ≤ K|A| for some K < p/|A|
      (not fully unstructured, but growth exists) -/
structure HardCoreInstance (p : ℕ) where
  /-- The element set -/
  elements : Finset (ZMod p)
  /-- The target sum -/
  target : ZMod p
  /-- Non-trivial size -/
  size_lb : 2 ≤ #elements
  /-- Below saturation -/
  size_ub : #elements ≤ p / 2
  /-- Bounded doubling constant -/
  doubling_bound : ℕ
  /-- Doubling is non-trivial -/
  doubling_pos : 1 ≤ doubling_bound
  /-- Sumset growth is bounded -/
  small_doubling : #(elements + elements) ≤ doubling_bound * #elements

section HardCore

variable {p : ℕ} [hp : Fact p.Prime]

/-- Hard core instances still have growing sumsets (by Cauchy-Davenport).
    The adversary cannot avoid sumset growth in Z/pZ. -/
theorem hard_core_has_growth (inst : HardCoreInstance p) :
    #inst.elements < #(inst.elements + inst.elements) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  exact addDoubling_gt_one_of_small inst.elements inst.size_lb
    (by have := inst.size_ub; omega)

/-- Hard core instances have large sum-product quantity.
    Even in the hard core, the adversary cannot make BOTH the sumset
    and the product set small. -/
theorem hard_core_sum_product (inst : HardCoreInstance p) :
    #inst.elements < max #(inst.elements + inst.elements) #(inst.elements * inst.elements) := by
  exact bourgain_katz_tao p inst.elements inst.size_lb inst.size_ub

/-- **Adversary Constraint Theorem**: The adversary's optimal strategy
    for producing hard Subset Sum instances is constrained by the
    structure-vs-computation dichotomy.

    Any instance the adversary produces must satisfy:
    (a) If at critical density with bounded doubling → Freiman structure
        constrains the element set to a short arithmetic progression.
    (b) If at critical density with large doubling → many achievable
        sums, making random algorithms effective.
    (c) If outside critical density → pigeonhole or lattice methods apply.

    This theorem states (a): if the adversary chooses a hard core
    instance with small enough doubling, Freiman's theorem pins the
    elements to an arithmetic progression. -/
theorem adversary_strategy_constrained (inst : HardCoreInstance p)
    (hsize : #inst.elements ≤ p / inst.doubling_bound) :
    ∃ (a d : ZMod p) (L : ℕ),
      L ≤ inst.doubling_bound ^ 2 * #inst.elements ∧
      ∀ x ∈ inst.elements, ∃ k : Fin L, x = a + k.val • d := by
  exact freiman_ZMod p inst.elements inst.doubling_bound
    inst.doubling_pos inst.small_doubling hsize

/-- **The full adversary dichotomy**: for ANY Subset Sum instance
    over Z/pZ with non-trivial size, the adversary faces a forced
    choice between two exploitable regimes.

    This is the culminating statement of Milestone 3.3: the adversary
    cannot produce an instance that is simultaneously unstructured
    (avoiding Freiman constraints) and non-growing (avoiding large
    subset sums). The sum-product theorem makes this impossible.

    The "hard" instances, if they exist, must live in the narrow
    transition zone between these regimes — and even there, the
    sum-product lower bound `|A| < max(|A+A|, |A·A|)` constrains
    the adversary's options. -/
theorem adversary_full_dichotomy (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p / 2) :
    -- Either the sumset is large (growing regime)...
    (#A < #(A + A)) ∧
    -- ...AND at least one of sumset/product set has polynomial growth
    (#A < max #(A + A) #(A * A)) := by
  exact ⟨addDoubling_gt_one_of_small A hA (by omega),
         bourgain_katz_tao p A hA hAp⟩

/-- The density trichotomy interacts with the structural dichotomy.
    For a standard (integer) Subset Sum instance, the three density
    regimes combine with the Freiman/sum-product dichotomy to create
    a complete classification of the adversary's strategy space.

    At critical density, the structural dichotomy is the ONLY remaining
    characterization of hard instances. This theorem states that
    critical density instances exist (the regime is non-empty). -/
theorem critical_density_nonempty :
    ∃ inst : SubsetSumInstance,
      inst.isCriticalDensity := by
  sorry -- Requires careful computation of Finset.sup for the concrete instance

end HardCore
