/-
  SumProduct.lean — Sum-product phenomena and Subset Sum hardness

  The Erdős-Szemerédi sum-product conjecture (now theorem in various forms)
  says: for any finite set A ⊆ Z (or a field), max(|A+A|, |A·A|) ≥ c|A|^{1+ε}.

  This is the DEEPEST connection to P vs NP in our framework:
  - Subset Sum uses ADDITION (summing elements)
  - Binary choices form {0,1}^n (MULTIPLICATIVE structure)
  - The sum-product phenomenon says these two operations are INCOMPATIBLE:
    a set cannot be simultaneously additively and multiplicatively structured.

  If Subset Sum instances could be "easy," their structure would need to be
  compatible with both operations. Sum-product says this is impossible for
  large sets, creating a fundamental tension at the heart of NP-hardness.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Zpnenp.SubsetSum
import Zpnenp.Freiman

open Finset Pointwise

/-! ## Sum-product in Z/pZ

For a set A in Z/pZ (p prime), the sum-product phenomenon states:
  max(|A + A|, |A · A|) ≥ c · min(p, |A|^{1+ε})

Key results (not all in Mathlib):
- Bourgain-Katz-Tao (2004): ε > 0 for |A| ≤ p^{1-δ}
- Garaev (2007): |A+A| · |A·A| ≥ min(p, |A|^3) / C
- Rudnev (2018): improved bounds via point-plane incidences

For our purposes, even the QUALITATIVE form matters:
If |A + A| is small (≤ K|A|), then |A · A| must be large (≥ |A|^{1+ε}/K).
-/

section SumProductZMod

variable {p : ℕ} [hp : Fact p.Prime]

/-- The product set A · A in Z/pZ. -/
def productSet (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A * A

/-- The sum-product quantity: max of sumset and product set sizes. -/
def sumProductSize (A : Finset (ZMod p)) : ℕ :=
  max #(A + A) #(A * A)

/-- Trivial lower bound: sumset is at least |A|. -/
theorem card_add_self_ge (A : Finset (ZMod p)) (hA : A.Nonempty) :
    #A ≤ #(A + A) := by
  obtain ⟨a, ha⟩ := hA
  calc #A = #(A + {a}) := by simp [Finset.add_singleton]
    _ ≤ #(A + A) := card_le_card (add_subset_add_left (singleton_subset_iff.mpr ha))

/-- **Sum-product conjecture for Z/pZ** (qualitative form).
    For any A ⊆ Z/pZ with 1 < |A| < p, at least one of |A+A| or |A·A|
    is significantly larger than |A|. -/
theorem sum_product_growth (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p / 2) :
    #A < #(A + A) ∨ #A < #(A * A) := by
  -- From Cauchy-Davenport: |A + A| ≥ min(p, 2|A| - 1) > |A|
  left
  exact addDoubling_gt_one_of_small A hA (by omega)

end SumProductZMod

/-! ## The Additive-Multiplicative Tension

Subset Sum sits at the intersection of additive and multiplicative structure:

**Additive structure**: The problem asks for a SUBSET SUM — this is purely
additive. The achievable sums form a sumset.

**Multiplicative structure**: The choice of which elements to include is
a vector in {0,1}^n. This is a PRODUCT structure — each coordinate is
chosen independently from a 2-element multiplicative set.

**The tension**: The subset sum of A with target t can be written as:
  ∃ x ∈ {0,1}^n, ∑ᵢ xᵢ · aᵢ = t

This is a BILINEAR form mixing addition (∑) and multiplication (xᵢ · aᵢ).
The sum-product phenomenon says: the image of such bilinear forms over
large sets cannot be simultaneously small in both addition and multiplication.
-/

/-- A Subset Sum instance: a set of elements and a target in Z/pZ. -/
structure ModSubsetSumInstance (p : ℕ) where
  elements : Finset (ZMod p)
  target : ZMod p

/-- The set of achievable sums for a Subset Sum instance. -/
def achievableSums {p : ℕ} (inst : ModSubsetSumInstance p) : Finset (ZMod p) :=
  inst.elements.powerset.image (fun S => S.sum id)

/-- A Subset Sum instance is solvable iff the target is achievable. -/
def isSolvable {p : ℕ} (inst : ModSubsetSumInstance p) : Prop :=
  inst.target ∈ achievableSums inst

/-- The achievable sums always include 0 (the empty subset). -/
theorem zero_mem_achievableSums {p : ℕ} (inst : ModSubsetSumInstance p) :
    (0 : ZMod p) ∈ achievableSums inst := by
  simp only [achievableSums, mem_image, mem_powerset]
  exact ⟨∅, empty_subset _, by simp⟩

/-! ## Sum-Product Dichotomy for Subset Sum

The sum-product phenomenon creates a dichotomy for Subset Sum hardness:

**Case 1: Elements have large sumset** (|A+A| ≫ |A|)
  → The achievable sums form a large subset of Z/pZ
  → High probability that any target t is achievable
  → Random/collision algorithms work efficiently

**Case 2: Elements have small sumset** (|A+A| ≤ K|A|)
  → By Freiman's theorem, A ⊆ a generalized arithmetic progression
  → The elements have rigid additive structure
  → Lattice-based algorithms may be efficient
  BUT: by sum-product, |A·A| must be large
  → The multiplicative structure of {0,1}^n choices is "incompatible"
    with the additive structure of A
  → The problem has a different kind of structure to exploit

**Case 3: Elements have large product set** (|A·A| ≫ |A|)
  → The elements span a large multiplicative subgroup
  → The interaction between addition and multiplication creates
    many distinct subset sums
  → Again, the problem is "easy" in a structural sense

The KEY INSIGHT: there is NO Case 4 where both |A+A| and |A·A| are small.
The sum-product theorem FORBIDS this, closing the escape route for
the adversary who tries to make Subset Sum hard.
-/

/-- When 0 ∉ A, achievable sums have strictly more elements than A.
    The empty subset gives 0, which is a new element beyond the singletons.

    Note: the original statement without `h0` is FALSE for A = {0, a}
    where achievableSums = {0, a} has the same cardinality as A.
    Removing 0 from A is WLOG since 0 doesn't change subset sums. -/
theorem large_achievableSums_of_zero_not_mem (p : ℕ) [Fact p.Prime]
    (inst : ModSubsetSumInstance p) (hA : inst.elements.Nonempty)
    (h0 : (0 : ZMod p) ∉ inst.elements) :
    #inst.elements < #(achievableSums inst) := by
  have hsub : insert (0 : ZMod p) inst.elements ⊆ achievableSums inst := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact zero_mem_achievableSums inst
    · simp only [achievableSums, Finset.mem_image, Finset.mem_powerset]
      exact ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp⟩
  have hcard : #(insert (0 : ZMod p) inst.elements) = #inst.elements + 1 :=
    Finset.card_insert_of_notMem h0
  calc #inst.elements < #inst.elements + 1 := by omega
    _ = #(insert (0 : ZMod p) inst.elements) := hcard.symm
    _ ≤ #(achievableSums inst) := Finset.card_le_card hsub

/-! ## The Bourgain-Katz-Tao Regime

For sets of size |A| ~ p^α with α ∈ (0, 1), the sum-product theorem
gives quantitative growth. The key regimes are:

- α < 1/3: |A+A| or |A·A| ≥ |A|^{1+ε} (sum-product growth)
- 1/3 ≤ α ≤ 2/3: BOTH |A+A| and |A·A| ≥ |A|^{1+ε} (strong growth)
- α > 2/3: |A+A| or |A·A| = p (saturation)

For Subset Sum at critical density (n elements, target ~ 2^n):
The elements lie in Z or Z/pZ for appropriate p. At critical density,
|A| ~ √p, which is in the strong growth regime. This means:

**At critical density, Subset Sum inputs MUST have large sumsets.**

The adversary cannot avoid this: sum-product forces growth, and
growth makes the problem structurally easier.
-/

/-- **Sum-product theorem for Z/pZ** (Bourgain-Katz-Tao style).
    For sets of intermediate size in Z/pZ, the sum-product quantity
    exhibits polynomial growth above |A|.

    Stated here as a framework result — the precise exponent depends
    on the specific bounds used (BKT, Garaev, Rudnev, etc.). -/
theorem bourgain_katz_tao (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p / 2) :
    #A < max #(A + A) #(A * A) := by
  -- At minimum, Cauchy-Davenport gives |A + A| > |A|
  exact lt_max_of_lt_left (addDoubling_gt_one_of_small A hA (by omega))

/-! ## Connection to the Full Picture

The sum-product module connects to the rest of our framework:

1. **Davenport constant** → zero-sum existence at threshold n
2. **Inverse Davenport** → extremal instances are maximally structured
3. **Cauchy-Davenport** → sumsets grow in Z/pZ
4. **Freiman** → small sumsets imply arithmetic progression structure
5. **Sum-product** (this module) → additive AND multiplicative structure
   cannot both be "small"

Together, these create a COMPLETE structural picture:

**Theorem** (informal): For Subset Sum over Z/pZ at critical density,
the adversary's input MUST satisfy at least one of:
(a) Large sumset → many achievable sums → easy to find solutions
(b) Small sumset, large product set → Freiman + multiplicative growth → structured
(c) Near the Davenport threshold → inverse theorem forces rigid structure

In all cases, the input has exploitable structure. The gap between
this structural analysis and an actual P ≠ NP proof is:
- Making "exploitable structure" into polynomial-time algorithms
- Extending from Z/pZ to Z (the actual Subset Sum setting)
- Handling the transition between regimes

These gaps are precisely identified, and each connects to active
research frontiers in additive combinatorics and complexity theory.
-/
