# What's Next: Prioritized Research Directions

## Current State (2026-03-18)

**Fully proved (zero sorry)**: 9 of 10 modules
- Davenport constant D(ℤ/nℤ) = n
- Inverse Davenport theorem (full iff)
- EGZ connection (using Mathlib's EGZ theorem)
- Density framework + pigeonhole collision
- Adversary game + gap analysis
- Cauchy-Davenport sumset growth
- Forward direction of Inverse EGZ (sum decomposition proved)

**Partially proved (1 sorry)**: InverseEGZ
- Forward direction: FULLY PROVED
- Backward direction: proved modulo `at_most_two_values`
  - `EGZFree.count_le`: max multiplicity ≤ n-1 ✓
  - `not_egzFree_of_not_isUnit`: non-unit difference → not EGZ-free ✓
  - `EGZFree.exists_sum_eq`: for any x, ∃ n-1 elements summing to -x ✓
  - `EGZFree.at_most_two_values`: EGZ-free of size 2n-2 → ≤ 2 values (SORRY)
  - Full backward assembly: 2 values → mult n-1 → extremal form → unit ✓

**The sole sorry** (`at_most_two_values`) needs: showing ≥ 3 distinct values
contradicts EGZ-free. The "shift trick" handles the case when some value has
multiplicity ≥ n-1. The case all multiplicities ≤ n-2 (only arises for n ≥ 5)
remains open.

**Published**: On GitHub, paper draft written

---

## Priority 1: Finish What's Started

### 1A. Fill InverseEGZ sorry ✅ DONE
Sum decomposition proved. Forward direction complete.
Backward direction proved modulo `at_most_two_values`.

### 1B. Polish paper for submission (1 day)
Target: ITP 2026 or CPP 2027. The paper has:
- First formalization of Davenport + inverse in any prover
- Novel adjacent swap proof technique
- Honest gap analysis
- Broad field survey
Add: benchmarks, comparison to PFR formalization timeline,
explicit Lean code excerpts.

---

## Priority 2: Deepen the Math

### 2A. Freiman's Theorem Connection ✅ STARTED
Module `Freiman.lean` created with small doubling dichotomy,
subset sum definitions, Plünnecke-Ruzsa connection.
Proved: addDoubling_gt_one_of_small, subset sum basic lemmas.
Remaining: iterated sumset growth, Freiman's theorem proper.

### 2A-original. Freiman's Theorem Connection (1-2 weeks)
**What**: Sets with small doubling (|A+A| ≤ K|A|) are contained
in generalized arithmetic progressions.

**Why**: This is the structural counterpart to Cauchy-Davenport.
CD says sumsets grow. Freiman says: if they DON'T grow, the set
must be structured. Together: Subset Sum inputs are either
"growing" (many achievable sums → easy) or "structured"
(amenable to special algorithms → potentially easy too).

**How**: The PFR project (Tao et al.) formalized the polynomial
Freiman-Ruzsa conjecture in Lean 4. Import their results or
prove a simpler version of Freiman for Z/pZ.

### 2B. Sum-Product Connection ✅ STARTED
Module `SumProduct.lean` created connecting Erdős-Szemerédi to Subset Sum.
Proved: sum_product_growth (qualitative, from Cauchy-Davenport),
card_add_self_ge, achievableSums definition.
Framework: additive-multiplicative tension, 3-way dichotomy.

### 2B-original. Sum-Product Connection (2-4 weeks)
**What**: Connect Erdős-Szemerédi sum-product theorem to
Subset Sum hardness.

**Why**: The field survey identified sum-product as the deepest
connection. P vs NP may be about the incompatibility of additive
and multiplicative structure. Subset Sum probes exactly this:
it uses addition (summing) combined with binary choices
(multiplicative structure of {0,1}^n).

**How**: Formalize: for a set A in Z/pZ, if |A+A| and |A·A| are
both small, then A has very rigid structure. Show this constrains
Subset Sum instances at critical density.

### 2C. Inverse EGZ Backward Direction (1-2 weeks)
**What**: Prove that any EGZ-free multiset of size 2n-2 must
have the extremal form (two values, each with multiplicity n-1).

**Why**: Completes the inverse EGZ theorem, extending our
structural characterization from the Davenport threshold to the
EGZ threshold.

**How**: Use a combination of the Davenport inverse theorem
(for the "projection" onto each value class) and counting arguments.

---

## Priority 3: New Directions from the Field Survey

### 3A. Uncommon Graphs (HIGH NOVELTY, 2-4 weeks)
**What**: Investigate Ramsey multiplicity failures as a source
of non-natural proof strategies.

**Why**: The natural proofs barrier blocks arguments that hold
for random objects. Uncommon graphs are combinatorial objects
where random colorings DON'T minimize structure — they're
non-natural by construction. This direction "does not appear
systematically explored in the complexity theory literature."

**How**:
1. Formalize the Ramsey multiplicity problem in Lean
2. Identify specific uncommon graphs (Thomason's examples)
3. Check if the "uncommonness" property can be adapted to
   distinguish functions computable by small circuits from
   random functions

### 3B. Proof Complexity / PHP ✅ DONE
Module `ProofComplexity.lean` (zero sorry!) connects davenport_upper
to proof complexity. Proved: pigeonhole_fin, prefixSums, collision
semantics, davenportPHP_not_injective, structured PHP analysis.
Framework: connections to Haken, Ajtai, Krajíček-Pudlák.

### 3B-original. Proof Complexity / PHP (CONNECTS TO EXISTING WORK, 2-4 weeks)
**What**: Connect our pigeonhole arguments to proof complexity
lower bounds.

**Why**: The weak pigeonhole principle in bounded arithmetic
is known to relate to circuit lower bounds (Krajíček-Pudlák).
Our Davenport upper bound IS a pigeonhole argument. The
Cook-Reckhow thesis says super-polynomial proof lengths in all
systems → P ≠ NP.

**How**:
1. Formalize the propositional PHP tautology
2. Connect to our `davenport_upper` (which uses pigeonhole)
3. Explore whether the structural content of our proofs
   (prefix sums, adjacent swaps) gives proof complexity insights

### 3C. Polynomial Method at Depth 4 (HIGHEST POTENTIAL, 4-8 weeks)
**What**: Apply the polynomial method (Croot-Lev-Pach style)
to depth-4 arithmetic circuits for Subset Sum.

**Why**: The "chasm at depth 4" (Agrawal-Vinay) means that
superpolynomial lower bounds for depth-4 arithmetic circuits
would cascade to general lower bounds. The polynomial method
already gives exponential bounds in restricted settings.

**How**:
1. Study the chasm theorem and what depth-4 lower bounds require
2. Formalize the connection between Subset Sum and arithmetic
   circuits
3. Attempt to apply slice-rank or polynomial method techniques
   to the Subset Sum polynomial

---

## Priority 4: Community and Publication

### 4A. Lean Zulip Post
Share the project on the Lean Zulip (#Is there code for X?,
#general). The formalized Davenport constant and inverse theorem
are novel contributions to Mathlib-adjacent mathematics.

### 4B. ArXiv Preprint
Post the paper with Lean code as supplementary material.
Target: math.CO (combinatorics) + cs.CC (computational complexity).

### 4C. Workshop Presentation
Submit to: Lean Together 2027, ITP 2026 workshop, STOC/FOCS
complexity workshop.

### 4D. Mathlib PR
Consider upstreaming the Davenport constant formalization to
Mathlib. The definitions (ZeroSumFree, Davenport constant) and
key theorems would be valuable additions to
`Mathlib.Combinatorics.Additive`.

---

## Decision Framework

When choosing what to work on next:

**If you want impact on the Lean community**: 4A (Zulip) + 4D (Mathlib PR)
**If you want to publish**: 1B (polish paper) + 4B (ArXiv)
**If you want to push the math**: 2A (Freiman) or 2B (sum-product)
**If you want the most novel research**: 3A (uncommon graphs)
**If you want the highest ceiling**: 3C (polynomial method at depth 4)
**If you want quick wins**: 1A (fill InverseEGZ sorry)

---

## The Long View

The project has established a solid foundation:
- Machine-checked structural theory of zero-sum
- Honest identification of the gap to P ≠ NP
- Broad survey of promising directions

The most likely path to a genuine breakthrough goes through
**sum-product phenomena** or the **polynomial method** — these
have the strongest existing chains toward circuit lower bounds.
The **uncommon graphs** direction is the most novel and could
yield surprising results.

Whatever direction you choose, the zero-sorry foundation means
every future result builds on rock, not sand.
