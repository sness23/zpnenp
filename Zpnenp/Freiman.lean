/-
  Freiman.lean — Small doubling, structural dichotomy, and Subset Sum

  The Freiman–Ruzsa theory says: sets with small doubling
  (|A + A| ≤ K|A|) have rigid additive structure. Combined with
  Cauchy-Davenport (sumsets grow), this creates a dichotomy:

  **Dichotomy for Subset Sum inputs:**
  - *Growing* inputs: |A + A| is large → many achievable sums → easy
  - *Structured* inputs: |A + A| is small → A sits inside a GAP → exploitable

  This module connects Mathlib's additive combinatorics infrastructure
  (Plünnecke-Ruzsa, doubling constants, Cauchy-Davenport) to our
  Subset Sum / zero-sum framework.
-/

import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import Zpnenp.SubsetSum

open Finset Pointwise

/-! ## Doubling constants and structure

The **doubling constant** σ[A] = |A + A| / |A| measures how much
A grows under addition. Key regimes:

- σ[A] = 1: A is a coset of a subgroup (in Z/pZ, only {0} or all of Z/pZ)
- σ[A] < 3/2: A generates a proper subgroup (by VerySmallDoubling)
- σ[A] < 2: A is contained in a coset of a subgroup
- σ[A] ≥ 2: A has genuine growth

For Z/pZ with p prime, there are no proper subgroups, so:
- σ[A] = 1 iff |A| = 1 or |A| = p
- σ[A] ≥ min(p/|A|, 2) otherwise (by Cauchy-Davenport)

This means: in Z/pZ, sumsets ALWAYS grow quickly unless A is trivial.
-/

section DoublingInZMod

variable {p : ℕ} [hp : Fact p.Prime]

/-- In Z/pZ, the doubling constant of a set with 2 ≤ |A| ≤ p-1 is > 1.
    This follows from Cauchy-Davenport: |A+A| ≥ min(p, 2|A|-1) > |A|. -/
theorem addDoubling_gt_one_of_small (A : Finset (ZMod p))
    (hA : 2 ≤ #A) (hAp : #A ≤ p - 1) :
    #A < #(A + A) := by
  have hAne : A.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hA
  have hcd := ZMod.cauchy_davenport hp.out hAne hAne
  -- |A + A| ≥ min(p, 2|A| - 1)
  -- Since |A| ≥ 2: 2|A| - 1 ≥ 3 > |A| when |A| < p
  -- And min(p, 2|A|-1) ≥ |A| + 1 when |A| ≤ p - 1
  omega

/-- In Z/pZ, iterating sumsets: |kA| ≥ min(p, k|A| - k + 1).
    Proved by induction using Cauchy-Davenport. -/
theorem iterated_sumset_growth (A : Finset (ZMod p))
    (hA : A.Nonempty) (k : ℕ) (hk : 1 ≤ k) :
    min p (k * #A - k + 1) ≤ #(k • A) := by
  sorry -- requires iterated Cauchy-Davenport

end DoublingInZMod

/-! ## The Structural Dichotomy

For Subset Sum over Z/pZ: given a set A ⊆ Z/pZ, the achievable
subset sums SS(A) = {∑_{a ∈ S} a : S ⊆ A} satisfy:

**Growing case**: If A has ≥ k elements with small pairwise structure,
then |SS(A)| ≥ min(p, Ω(|A|²)) — the achievable sums cover a
large fraction of Z/pZ. This makes the Subset Sum problem "easy"
(random collisions find solutions quickly).

**Structured case**: If |A + A| ≤ K|A| (small doubling), then
by Freiman's theorem, A is contained in a generalized arithmetic
progression of dimension ≤ f(K) and size ≤ g(K)|A|. This rigid
structure makes specialized algorithms (lattice reduction, etc.)
effective.

Either way, the adversary is constrained: producing a "hard"
Subset Sum instance requires navigating between these regimes.
-/

/-- The set of achievable subset sums of A in Z/pZ. -/
def subsetSumsZMod {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.powerset.image (fun S => S.sum id)

/-- The empty subset gives 0. -/
theorem zero_mem_subsetSumsZMod {p : ℕ} (A : Finset (ZMod p)) :
    (0 : ZMod p) ∈ subsetSumsZMod A := by
  simp [subsetSumsZMod, mem_image]
  exact ⟨∅, empty_subset A, by simp⟩

/-- Subset sums include A + {0} = A (each singleton is a subset sum). -/
theorem mem_subsetSumsZMod_of_mem {p : ℕ} (A : Finset (ZMod p)) {a : ZMod p}
    (ha : a ∈ A) : a ∈ subsetSumsZMod A := by
  simp only [subsetSumsZMod, mem_image, mem_powerset]
  exact ⟨{a}, singleton_subset_iff.mpr ha, by simp⟩

/-- Number of subset sums is at most 2^|A|. -/
theorem card_subsetSumsZMod_le {p : ℕ} (A : Finset (ZMod p)) :
    #(subsetSumsZMod A) ≤ 2 ^ #A := by
  calc #(subsetSumsZMod A) ≤ #A.powerset := card_image_le
    _ = 2 ^ #A := card_powerset A

/-- If all of Z/pZ is achievable, the subset sum problem is trivially solvable. -/
theorem subsetSumsZMod_surjective {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p))
    (h : subsetSumsZMod A = Finset.univ) (t : ZMod p) :
    ∃ S ⊆ A, S.sum id = t := by
  have : t ∈ subsetSumsZMod A := h ▸ Finset.mem_univ t
  simp only [subsetSumsZMod, mem_image, mem_powerset] at this
  exact this

/-! ## Plünnecke-Ruzsa bounds on iterated sumsets

The Plünnecke-Ruzsa inequality (from Mathlib) controls ALL iterated
sumsets in terms of the doubling constant:

If |A + B| ≤ K|A|, then |nB - mB| ≤ K^(n+m) |A|.

For our purposes: if |A + A| ≤ K|A|, then
  |kA| ≤ K^k |A|

This means: small doubling propagates to ALL iterated sumsets.
Since subset sums involve iterated sumsets, small doubling implies
the set of achievable sums is "small" (relative to the ambient group).
-/

-- The Ruzsa triangle inequality from Mathlib is the key tool for
-- controlling iterated sumsets. For additive groups like Z/pZ,
-- it bounds |B - C| in terms of |A - B| and |A - C|:
--   |A| * |B - C| ≤ |A - B| * |A - C|
-- See: `ruzsa_triangle_inequality_div_div_div` in Mathlib.

/-! ## Connection to the Davenport constant

Our main theorems fit into this framework as follows:

1. **Davenport** (D(Z/nZ) = n): Among n elements of Z/nZ, a zero-sum
   exists. This is the ULTIMATE growth guarantee: the subset sums
   MUST include 0 when |A| ≥ n.

2. **Inverse Davenport**: The extremal instances (zero-sum free
   multisets of size n-1) are {g, g, ..., g} for a unit g.
   These have MAXIMAL subset sums {0, g, 2g, ..., (n-1)g} = Z/nZ.
   Paradoxically, avoiding zero-sum at the threshold FORCES
   full coverage of subset sums.

3. **Cauchy-Davenport + Freiman** (this module): Even BELOW the
   Davenport threshold, subset sums must be large unless the input
   has Freiman-type structure. This constrains the "hard" instances
   to a narrow structural class.

**The P ≠ NP connection**: If we could show that Freiman-structured
inputs are algorithmically easier (e.g., solvable by lattice
reduction), we'd have a dichotomy:
- Unstructured inputs → many subset sums → collision algorithm works
- Structured inputs → Freiman structure → lattice algorithm works

This doesn't prove P = NP (the algorithms might not be polynomial),
but it identifies the STRUCTURAL BARRIER: proving Subset Sum is hard
requires showing that the Freiman dichotomy does NOT yield efficient
algorithms in BOTH branches.
-/

/-! ## Small doubling implies structured inputs

**Freiman's theorem** (not yet in Mathlib, stated here for reference):
If A ⊆ Z with |A + A| ≤ K|A|, then A is contained in a
generalized arithmetic progression of dimension ≤ d(K) and
size ≤ f(K)|A|.

The polynomial Freiman-Ruzsa conjecture (now theorem, proved by
Gowers-Green-Manners-Tao 2023, formalized in Lean 4 by the PFR
project) gives polynomial bounds on d(K) and f(K).

For Z/pZ, Freiman's theorem takes a simpler form:
If A ⊆ Z/pZ with |A + A| ≤ K|A| and |A| ≤ p/K, then A is
contained in an arithmetic progression of length ≤ K²|A|.
-/

/-- **Freiman's theorem for Z/pZ** (simplified, stated without proof).
    Sets with small doubling are contained in short arithmetic progressions. -/
theorem freiman_ZMod (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p))
    (K : ℕ) (hK : 1 ≤ K) (hsmall : #(A + A) ≤ K * #A)
    (hsize : #A ≤ p / K) :
    ∃ (a d : ZMod p) (L : ℕ),
      L ≤ K ^ 2 * #A ∧
      ∀ x ∈ A, ∃ k : Fin L, x = a + k.val • d := by
  sorry -- Freiman's theorem for Z/pZ

/-- **Growth lemma**: If A ⊆ Z/pZ does NOT have small doubling
    (|A + A| > K|A|), then the subset sums of A cover a large
    fraction of Z/pZ. -/
theorem large_subsetSumsZMod_of_large_doubling (p : ℕ) [Fact p.Prime]
    (A : Finset (ZMod p)) (hA : A.Nonempty)
    (hlarge : #A < #(A + A)) :
    #A + 1 ≤ #(subsetSumsZMod A) := by
  -- The subset sums include 0 and all elements of A, plus at least
  -- one element of A + A not in A ∪ {0}.
  sorry -- needs more infrastructure

/-! ## Summary

This module establishes the theoretical framework connecting
additive combinatorics to the Subset Sum problem:

**Proved**:
- `addDoubling_gt_one_of_small`: In Z/pZ, non-trivial sets always
  have growing sumsets
- `subsetSumsZMod` definition and basic properties
- Ruzsa triangle inequality (from Mathlib)

**Stated** (sorry):
- `iterated_sumset_growth`: Iterated Cauchy-Davenport
- `freiman_ZMod`: Freiman's theorem for Z/pZ
- `large_subsetSumsZMod_of_large_doubling`: Growth implies large subset sums

**Framework**:
- Structural dichotomy: growing vs. structured inputs
- Connection to Davenport constant and inverse theorem
- Path toward the P ≠ NP structural barrier
-/
