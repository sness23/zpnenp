/-
  ProofComplexity.lean — Pigeonhole, proof complexity, and P ≠ NP

  Our Davenport upper bound proof IS a pigeonhole argument: n+1 prefix
  sums in an n-element group force a collision, yielding a zero-sum.

  This connects to a deep theme in proof complexity:
  - The pigeonhole principle (PHP) is hard for weak proof systems
  - PHP lower bounds relate to circuit lower bounds (Krajíček-Pudlák)
  - Our proofs use PHP in a structured setting (prefix sums, zero-sums)

  This module makes these connections explicit and explores whether
  the structural content of our proofs gives proof complexity insights.
-/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Zpnenp.Davenport
import Zpnenp.Inverse

/-! ## The Pigeonhole Principle in Our Framework

The standard PHP: if f : Fin (n+1) → Fin n, then f is not injective.

Our usage in `davenport_upper`:
- f = prefix sums : Fin (n+1) → ZMod n
- Non-injectivity → collision → contiguous zero-sum

The proof is constructive: from the collision (ps(i) = ps(j)),
we extract the zero-sum as elements l[i..j).
-/

/-- The pigeonhole principle: a map from n+1 elements to n elements
    is not injective. This is the core of `davenport_upper`. -/
theorem pigeonhole_fin (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  exact ⟨a, b, hab, hfab⟩

/-! ## Prefix Sums as a PHP Instance

The Davenport upper bound constructs a specific PHP instance:
- Domain: Fin (n+1) (indices 0, 1, ..., n)
- Codomain: ZMod n (the n-element group)
- Map: prefix sums ps(i) = Σ_{k<i} l[k]

Key properties of this PHP instance:
1. **Monotone structure**: ps(i+1) = ps(i) + l[i]
   (each step adds one element)
2. **Zero anchor**: ps(0) = 0
3. **Collision semantics**: ps(i) = ps(j) means l[i..j) sums to 0

This is not a "random" PHP instance — it has rich algebraic structure
that makes the collision MEANINGFUL (it gives a zero-sum).
-/

/-- Prefix sums of a list in ZMod n. -/
def prefixSums {n : ℕ} (l : List (ZMod n)) : Fin (l.length + 1) → ZMod n :=
  fun i => (l.take i.val).sum

/-- Prefix sums start at 0. -/
theorem prefixSums_zero {n : ℕ} (l : List (ZMod n)) :
    prefixSums l ⟨0, by omega⟩ = 0 := by
  simp [prefixSums]

/-- A collision in prefix sums gives a contiguous zero-sum. -/
theorem collision_gives_zerosum {n : ℕ} (l : List (ZMod n))
    {i j : ℕ} (hij : i < j) (hj : j ≤ l.length)
    (hcol : (l.take i).sum = (l.take j).sum) :
    ((l.drop i).take (j - i)).sum = 0 := by
  have htake_eq : l.take j = l.take i ++ (l.drop i).take (j - i) := by
    rw [show j = i + (j - i) from by omega, List.take_add]
    have : i + (j - i) - i = j - i := by omega
    rw [this]
  have happ : (l.take j).sum = (l.take i).sum + ((l.drop i).take (j - i)).sum := by
    rw [htake_eq, List.sum_append]
  rw [hcol] at happ
  have h : (l.take j).sum + 0 = (l.take j).sum + ((l.drop i).take (j - i)).sum := by
    rw [add_zero]; exact happ
  exact (add_left_cancel h).symm

/-! ## Proof Complexity Perspective

In proof complexity, the **propositional pigeonhole principle** PHP_n^{n+1}
states that there is no injection from [n+1] to [n]. Key results:

1. **Exponential lower bounds**: PHP requires exponential-size proofs in
   Resolution (Haken 1985), bounded-depth Frege (Ajtai 1988), and
   Cutting Planes (Pudlák 1997).

2. **Connection to circuit bounds** (Krajíček-Pudlák 1998):
   If PHP_n^{n+1} requires super-polynomial proofs in all propositional
   proof systems, this implies circuit lower bounds.

3. **Cook-Reckhow thesis**: If a tautology requires super-polynomial
   proofs in ALL proof systems, then P ≠ NP.

Our situation: `davenport_upper` uses PHP in a STRUCTURED way
(prefix sums over a group). The question is whether this structure
makes the pigeonhole argument "easier" or "harder" from a proof
complexity perspective.

**Key insight**: Our PHP instance is NOT a generic injection failure.
It's a collision in a homomorphic structure (prefix sums form a
group homomorphism from (Z, +) to ZMod n). This structural content
might make the proof SHORTER in certain proof systems, which would
be evidence AGAINST using PHP-based arguments for P ≠ NP.

Conversely: the inverse Davenport theorem shows that the ONLY way
to avoid PHP collisions at the threshold (size n-1) is to have
all-equal elements. This rigidity might give STRONGER proof
complexity results for structured PHP instances.
-/

/-! ## The Structured PHP: Prefix Sums over Groups

We formalize the key properties that make our PHP instance special.
-/

/-- The prefix sum map from Fin (n+1) to ZMod n, for a list of length n.
    This is the specific PHP instance used in `davenport_upper`. -/
def davenportPHP {n : ℕ} (l : List (ZMod n)) (hl : l.length = n) :
    Fin (n + 1) → ZMod n :=
  fun i => (l.take i.val).sum

/-- The Davenport PHP instance has a zero anchor. -/
theorem davenportPHP_zero {n : ℕ} (l : List (ZMod n)) (hl : l.length = n) :
    davenportPHP l hl ⟨0, by omega⟩ = 0 := by
  simp [davenportPHP]

/-- The Davenport PHP non-injectivity: n+1 prefix sums in ZMod n
    must have a collision. This is the core of `davenport_upper`. -/
theorem davenportPHP_not_injective {n : ℕ} (hn : 0 < n)
    (l : List (ZMod n)) (hl : l.length = n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧
      davenportPHP l hl a = davenportPHP l hl b := by
  haveI : NeZero n := ⟨by omega⟩
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (n + 1)) := by
    rw [ZMod.card n, Fintype.card_fin]; omega
  exact Fintype.exists_ne_map_eq_of_card_lt (davenportPHP l hl) hcard

/-! ## Connection to the Inverse Theorem

The inverse Davenport theorem (`inverse_davenport` from Inverse.lean)
tells us exactly when the PHP prefix sums are INJECTIVE on the first
n positions (i.e., on Fin n ⊆ Fin (n+1)):

A list l of n-1 elements has injective prefix sums ↔ all elements
are equal to some unit g ↔ the multiset is zero-sum free.

This means:
- **Injective prefix sums** ↔ all-equal (maximally structured)
- **Non-injective prefix sums** ↔ contains a zero-sum (some diversity)

The transition from injectivity to non-injectivity happens at EXACTLY
size n (the Davenport constant). Below n, injectivity is possible
but only for maximally structured inputs. At n, injectivity is
impossible, and the collision yields a zero-sum.

**Proof complexity interpretation**: The Davenport inverse theorem
characterizes the "hard instances" of the structured PHP. These hard
instances (all-equal elements) are MAXIMALLY STRUCTURED. In proof
complexity terms, this suggests that structured PHP might be EASIER
than generic PHP, because the hard instances have exploitable structure.
-/

/-- Prefix sums of a zero-sum free list are injective.
    (Restated from `ZeroSumFree.prefix_sums_injective`.)
    This is the "easy direction" of the structured PHP analysis. -/
theorem zeroSumFree_implies_injective_prefixSums {n : ℕ} (hn : 1 < n)
    {l : List (ZMod n)} (hzsf : ZeroSumFree (↑l : Multiset (ZMod n)))
    (hlen : l.length = n - 1) :
    Function.Injective (fun i : Fin n => (l.take i.val).sum) := by
  haveI : NeZero n := ⟨by omega⟩
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only at heq
  by_contra hij
  have hne : i ≠ j := fun h => hij (Fin.ext h)
  exact ZeroSumFree.prefix_sums_injective (by omega) hzsf
    (by omega) (by omega) hne heq

/-! ## Summary and Open Questions

**Established connections:**
1. `davenport_upper` = structured PHP over ZMod n
2. Collision semantics: PHP collision ↔ zero-sum existence
3. Inverse theorem: PHP injectivity ↔ maximal structure

**Open questions for proof complexity:**
- Does the group structure of prefix sums make PHP easier in
  Resolution or bounded-depth Frege?
- Can the inverse Davenport theorem be expressed as a short
  propositional proof in Extended Frege?
- Does the "all-equal" characterization of hard instances
  give polynomial-size proofs for structured PHP variants?

**Connection to P ≠ NP:**
If structured PHP (over groups) admits short proofs in all
propositional systems while generic PHP does not, this would
separate the combinatorial structure of Subset Sum from the
"generic" combinatorial structure needed for P ≠ NP. This
would be evidence for the "natural proofs barrier" — our
structural theorems might be too "natural" (holding for
random objects) to yield circuit lower bounds.
-/
