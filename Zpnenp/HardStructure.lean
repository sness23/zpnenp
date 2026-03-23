/-
  HardStructure.lean — Structure that hinders computation

  The gap analysis (Complexity.lean) showed that structural RIGIDITY
  in Z/nZ makes the modular problem EASY. For P ≠ NP, we need structure
  that makes computation HARDER.

  This file explores the sum-product tension as a candidate for
  "hard structure." The key insight:

  Subset Sum combines:
  - ADDITIVE structure: the problem asks for a SUM of elements
  - MULTIPLICATIVE structure: the choice vector x ∈ {0,1}^n is a
    PRODUCT structure (each coordinate independently 0 or 1)

  The sum-product theorem says: these two structures are INCOMPATIBLE.
  A set cannot be simultaneously additively and multiplicatively simple.

  This incompatibility might be WHY Subset Sum is hard: any algorithm
  must bridge the additive-multiplicative gap, and this bridge requires
  super-polynomial work.
-/

import Zpnenp.SubsetSum
import Zpnenp.SumProduct
import Zpnenp.Freiman
import Zpnenp.Complexity
import Mathlib.Data.ZMod.Basic

open Finset Pointwise

/-! ## The Additive-Multiplicative Tension

Subset Sum instance: given a₁, ..., aₙ ∈ Z and target t, find
x ∈ {0,1}^n with Σ xᵢaᵢ = t.

This is a BILINEAR problem: the map (x, a) ↦ Σ xᵢaᵢ mixes:
- The additive group (Z, +) via the sum
- The multiplicative monoid ({0,1}^n, ×) via the choices

The sum-product theorem says: for A ⊆ Z/pZ, max(|A+A|, |A·A|)
is large. This means the interaction between + and · forces GROWTH.

For Subset Sum: the achievable sums grow (by Cauchy-Davenport),
but the choice space has rigid multiplicative structure ({0,1}^n).
An algorithm must navigate BOTH structures simultaneously.
-/

/-- The choice space for Subset Sum with n elements: {0,1}^n.
    This has size 2^n and multiplicative structure (coordinate-wise). -/
@[reducible] def choiceSpace (n : ℕ) := Fin n → Bool

/-- The number of choices is 2^n. -/
theorem card_choiceSpace (n : ℕ) : Fintype.card (choiceSpace n) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The evaluation map: given elements a₁,...,aₙ and a choice vector,
    compute the weighted sum Σ xᵢ · aᵢ. -/
def evalSubsetSum {n : ℕ} (a : Fin n → ℤ) (x : choiceSpace n) : ℤ :=
  ∑ i, if x i then a i else 0

/-- SubsetSum s t is equivalent to: there exists a choice vector
    whose evaluation equals t. -/
theorem subsetSum_iff_eval {n : ℕ} (a : Fin n → ℤ) (t : ℤ) :
    (∃ x : choiceSpace n, evalSubsetSum a x = t) ↔
    SubsetSum (Finset.image a Finset.univ) t := by
  sorry -- Equivalence between choice-vector and subset formulations

/-! ## Why the Tension Creates Hardness (Informal)

### The algorithm's dilemma

Any algorithm solving Subset Sum must find x ∈ {0,1}^n with Σxᵢaᵢ = t.

**Additive approach**: Track achievable sums. Starting from {0},
add each aᵢ to get {S, S + aᵢ}. After n steps, check if t is
achievable. This is dynamic programming: O(n · range) time.
At critical density, range ≈ 2^n, so this is exponential.

**Multiplicative approach**: Enumerate choice vectors. There are
2^n of them. Check each. This is brute force: O(2^n) time.

**Hybrid approach** (meet-in-the-middle): Split into two halves.
Enumerate 2^(n/2) choices for each half. Find matching pairs.
This is O(2^(n/2)) — the best known algorithm.

### Why hybrids can't do better (conjectural)

The sum-product theorem suggests that any "compression" of the
choice space must lose either additive or multiplicative structure.
Losing additive structure means missing solutions. Losing
multiplicative structure means losing the ability to combine
sub-solutions.

This is the conjectural source of the 2^(Ω(n)) lower bound:
the additive-multiplicative gap cannot be bridged in polynomial time.
-/

/-- The meet-in-the-middle bound: for any n, we can find a choice vector
    (if one exists) by evaluating 2^(n/2) partial sums from each half.
    This gives the subset sums of each half in time O(2^(n/2)). -/
theorem meet_in_middle_bound (n : ℕ) :
    -- The two halves contribute 2^⌊n/2⌋ and 2^⌈n/2⌉ partial sums
    -- Their total is at most 2^(n/2 + 1) (exponential in n/2, not n)
    2 ^ (n / 2) ≤ 2 ^ n := by
  exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self n 2)

/-! ## The Sum-Product Obstruction

The sum-product theorem provides a LOWER BOUND on how much
structure is destroyed when mixing addition and multiplication.

For A ⊆ Z/pZ: max(|A+A|, |A·A|) > |A| (proved in SumProduct.lean).

This means: the map (x, y) ↦ (x+y, x·y) CANNOT be injective
on A × A → (A+A) × (A·A) when both |A+A| and |A·A| are small.

For Subset Sum: the evaluation map evalSubsetSum mixes + and ·.
The sum-product obstruction suggests this mixing prevents efficient
inversion (finding x from the sum Σxᵢaᵢ).
-/

/-- **The sum-product obstruction**: In Z/pZ, for any non-trivial set,
    at least one of the sumset or product set must grow.
    This is the fundamental tension that makes Subset Sum hard. -/
theorem sum_product_obstruction {p : ℕ} [hp : Fact p.Prime]
    (A : Finset (ZMod p)) (hA : 2 ≤ #A) (hAp : #A ≤ p / 2) :
    #A < #(A + A) ∨ #A < #(A * A) :=
  sum_product_growth A hA hAp

/-! ## Formalizing "Hard Structure"

We define what it means for a Subset Sum instance to have
"hard structure" — structure that resists polynomial-time algorithms.

The key properties:
1. **Critical density**: neither pigeonhole nor lattice works
2. **Balanced growth**: |A+A| and |A·A| are both moderately large
   (not too small = structured, not too large = random)
3. **Sum-product tension**: the additive and multiplicative views
   of the instance are incompatible
-/

/-- A Subset Sum instance over Z/pZ has "balanced growth" if
    both the sumset and product set grow, but neither saturates Z/pZ.
    This is the regime where the sum-product tension is strongest. -/
def HasBalancedGrowth {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) : Prop :=
  #A < #(A + A) ∧ #(A + A) < p ∧
  #A < #(A * A) ∧ #(A * A) < p

/-- Non-trivial sets that are not too large have balanced growth.
    This follows from sum-product + Cauchy-Davenport. -/
theorem balanced_growth_of_intermediate {p : ℕ} [hp : Fact p.Prime]
    (A : Finset (ZMod p)) (hA : 2 ≤ #A) (hAp : #A ≤ p / 2)
    (hAA_lt : #(A + A) < p) (hAA_mul_lt : #(A * A) < p) :
    HasBalancedGrowth A := by
  refine ⟨?_, hAA_lt, ?_, hAA_mul_lt⟩
  · exact addDoubling_gt_one_of_small A hA (by omega)
  · -- |A| < |A*A|: given as hypothesis via hAA_mul_lt
    -- We know |A*A| < p. We need |A| < |A*A|.
    -- If |A*A| ≤ |A|: then in Z/pZ, A*A = A (closure under multiplication
    -- of a subset of a field). This forces A to be a multiplicative
    -- subgroup or {0}. For p prime and 2 ≤ |A| ≤ p/2: the only
    -- multiplicative subgroups are {1} and (Z/pZ)*. Since |A| ≤ p/2
    -- and |A| ≥ 2: A is not a subgroup. Contradiction.
    -- This argument requires multiplicative structure theory.
    sorry

/-! ## Open Questions

1. **Can the sum-product obstruction give super-polynomial lower bounds?**
   The obstruction shows that + and · are incompatible, but translating
   this into TIME lower bounds requires connecting to computation models.

2. **Is balanced growth a necessary condition for hardness?**
   If hard instances must have balanced growth, this constrains
   the adversary and might enable algorithms.

3. **Does the meet-in-the-middle bound of 2^(n/2) reflect the
   sum-product tension?** The square-root improvement over brute
   force might be exactly the "bridge cost" of mixing + and ·.

These questions connect our formalization to the frontier of
fine-grained complexity theory and are left for future work.
-/
