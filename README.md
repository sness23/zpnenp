# zpnenp: Zero-Sum Problems and P != NP

A Lean 4 investigation into whether structural results from additive
combinatorics — particularly zero-sum theory — can illuminate the
P vs NP problem through the Subset Sum problem.

**Status**: All theorems machine-checked. Zero `sorry` declarations.
Builds clean against Lean 4.28.0 + Mathlib v4.28.0.

---

## The Big Idea in 60 Seconds

The **Subset Sum** problem asks: given a set of integers, does some
subset sum to a target? It's one of the original NP-complete problems.

**Zero-sum theory** (a branch of additive combinatorics) studies exactly
when subsets with prescribed sums MUST exist. The **Davenport constant**
D(Z/nZ) = n tells us: with n elements in Z/nZ, a zero-sum subset is
*guaranteed* — no matter what the adversary chooses.

The **inverse Davenport theorem** goes further: the *only* instances at
the threshold that avoid zero-sum are (n-1) copies of a single unit
element. The adversary's "hardest" instances are **maximally structured**.

We formalize all of this in Lean 4 and ask: can this structural rigidity
tell us something about computational hardness?

---

## Table of Contents

- [The Mathematical Story](#the-mathematical-story)
- [What We Proved](#what-we-proved)
- [The Honest Gap](#the-honest-gap)
- [Project Structure](#project-structure)
- [Building the Project](#building-the-project)
- [Documentation](#documentation)
- [The Adversary Game](#the-adversary-game)
- [The Density Phase Transition](#the-density-phase-transition)
- [The Three Barriers](#the-three-barriers)
- [Where Could the Answer Come From?](#where-could-the-answer-come-from)
- [FAQ](#faq)

---

## The Mathematical Story

### Act 1: The Davenport Constant

Consider a bag of numbers from Z/nZ (integers mod n). How many numbers
do you need before a zero-sum subset is GUARANTEED to exist?

**Answer**: Exactly n. This is the Davenport constant D(Z/nZ) = n.

**Proof of the upper bound** (n is enough): Take any n numbers.
Compute the prefix sums s_0 = 0, s_1 = a_1, s_2 = a_1 + a_2, etc.
That's n+1 values in Z/nZ (which has n elements). By the
**pigeonhole principle**, two prefix sums must be equal: s_i = s_j.
The elements between them sum to zero.

**Proof of the lower bound** (n-1 is not enough): Take n-1 copies of 1.
Any k-element subset sums to k, and 1 <= k <= n-1 means k != 0 mod n.

Both directions are formalized in [`Zpnenp/Davenport.lean`](Zpnenp/Davenport.lean).

### Act 2: The Inverse Theorem

The Davenport constant tells us the *threshold*. The inverse theorem
tells us what happens *at* the threshold:

**Theorem**: A multiset of n-1 elements in Z/nZ is zero-sum free
**if and only if** it's (n-1) copies of a single unit element.

This means the adversary's optimal strategy is completely determined.
No mixing of elements. No clever constructions. Just copies of one
number that generates the group.

The proof uses a beautiful **adjacent swap argument**:

1. For any zero-sum free multiset, the prefix sums of ANY ordering
   form a **permutation of Z/nZ** (n distinct values in an n-element set).

2. Swapping two adjacent elements changes exactly ONE prefix sum.

3. Both orderings must give permutations. Two permutations of the same
   set that agree on n-1 of n positions must agree on all n.

4. Therefore the two swapped elements are equal. Since any pair can be
   made adjacent, ALL elements are equal.

Formalized in [`Zpnenp/Inverse.lean`](Zpnenp/Inverse.lean).

### Act 3: The Density Phase Transition

Standard Subset Sum (over Z, not Z/nZ) has a **phase transition**
based on the density d = n / log_2(max weight):

| Density | Difficulty | Method |
|---------|-----------|--------|
| d >> 1 (high) | Easy | Pigeonhole forces collisions |
| d << 1 (low) | Easy | Lattice reduction (LLL) |
| d ~ 1 (critical) | **Hard** | Neither method works |

We formalize the pigeonhole collision theorem: if 2^n > n*M + 1,
two distinct subsets must have the same sum. This is the integer
analog of the Davenport upper bound.

Formalized in [`Zpnenp/Density.lean`](Zpnenp/Density.lean).

### Act 4: The Complexity Bridge

We formalize the adversary game for modular zero-sum and prove:

- **At the threshold** (size n-1): the adversary's NO instances are
  exactly replicate-of-unit (by the inverse Davenport theorem).
- **Above the threshold** (size >= n): the answer is always YES.
- **The threshold is decidable in O(n)**: just check if all elements
  are equal and the common element is a unit.

Formalized in [`Zpnenp/Complexity.lean`](Zpnenp/Complexity.lean).

---

## What We Proved

Every theorem below is machine-checked in Lean 4 with zero `sorry`:

### Core Definitions
| Declaration | File | Description |
|-------------|------|-------------|
| `SubsetSum` | SubsetSum.lean | The Subset Sum decision problem |
| `SubsetSumZero` | SubsetSum.lean | Zero-sum variant |
| `subsetSums` | SubsetSum.lean | Set of all achievable subset sums |
| `ZeroSumFree` | Davenport.lean | No nonempty submultiset sums to zero |
| `ModSubsetSumZero` | ZeroSum.lean | Modular zero-sum |
| `SubsetSumInstance` | Density.lean | Structured instance type |

### Theorems
| Theorem | File | Statement |
|---------|------|-----------|
| `subsetSum_zero` | SubsetSum.lean | SubsetSum s 0 always holds |
| `subsetSum_mono` | SubsetSum.lean | Monotone in the set |
| `subsetSum_singleton` | SubsetSum.lean | SubsetSum {a} t iff t=0 or t=a |
| `card_subsetSums_le` | Structural.lean | At most 2^n achievable sums |
| `egz_finset` | ZeroSum.lean | EGZ applied to Finset Z |
| `egz_implies_modSubsetSumZero` | ZeroSum.lean | EGZ implies modular zero-sum |
| `multiset_sum_replicate` | Davenport.lean | Sum of k copies = k * a |
| `zeroSumFree_replicate_one` | Davenport.lean | D(Z/nZ) >= n |
| `davenport_upper` | Davenport.lean | D(Z/nZ) <= n (pigeonhole) |
| `davenport_ZMod` | Davenport.lean | D(Z/nZ) = n |
| `zeroSumFree_replicate_unit` | Inverse.lean | Forward direction (any unit) |
| `prefix_sums_injective` | Inverse.lean | Prefix sums are distinct |
| `prefix_sums_surjective` | Inverse.lean | Prefix sums cover Z/nZ |
| `injective_agree_of_agree_except` | Inverse.lean | Bijections agreeing on n-1 inputs agree |
| `ZeroSumFree.all_eq` | Inverse.lean | All elements of max ZSF are equal |
| `isUnit_of_replicate_zeroSumFree` | Inverse.lean | Common element is a unit |
| `inverse_davenport` | Inverse.lean | **Full inverse theorem (iff)** |
| `adversary_no_instances` | Complexity.lean | NO instances = replicate-of-unit |
| `adversary_large_always_yes` | Complexity.lean | Size >= n implies YES |
| `mod_zero_sum_decidable_at_threshold` | Complexity.lean | Threshold is decidable |
| `subsetSums_range_bound` | Density.lean | Subset sums bounded by n*M |
| `pigeonhole_collision` | Density.lean | High density forces collisions |
| `high_density_has_collision` | Density.lean | Applied to instances |

---

## The Honest Gap

We are transparent about what our results do and do not imply.

**What we proved**: The modular zero-sum problem at the Davenport
threshold is O(n)-decidable. The adversary's extremal instances are
maximally structured.

**What we did NOT prove**: P != NP.

**Why not**: Our structural results are about Z/nZ (modular arithmetic),
which is SIMPLER than standard Subset Sum over Z. The modular problem's
structural rigidity (inverse Davenport) makes it EASY to decide, not hard.

**The real gap**: Standard Subset Sum at critical density d ~ 1 is where
hardness lives. Bridging from modular structure to integer hardness
requires new ideas beyond current zero-sum theory.

**This is documented in the code itself** — see the extensive comments
in [`Zpnenp/Complexity.lean`](Zpnenp/Complexity.lean).

---

## Project Structure

```
zpnenp/
├── README.md                  # This file
├── THESIS.md                  # Thesis statement and big picture
├── ROADMAP.md                 # 24-week research plan
├── lakefile.toml              # Lean build configuration
├── lean-toolchain             # Lean version (4.28.0)
│
├── Zpnenp/                    # Lean 4 source (1005 lines, 0 sorry)
│   ├── Basic.lean             # Root module
│   ├── SubsetSum.lean         # Core definitions
│   ├── ZeroSum.lean           # EGZ connection
│   ├── Structural.lean        # Counting bounds
│   ├── Davenport.lean         # D(Z/nZ) = n
│   ├── Inverse.lean           # Inverse Davenport theorem
│   ├── Complexity.lean        # Adversary game, gap analysis
│   └── Density.lean           # Phase transitions, pigeonhole
│
├── docs/                      # Documentation
│   ├── 01-OVERVIEW.md         # Project overview
│   ├── 02-MATH-BACKGROUND.md  # Zero-sum theory, additive combinatorics
│   ├── 03-BARRIERS.md         # Three barriers to P != NP
│   ├── 04-LEAN-STATUS.md      # Formalization status
│   ├── 05-LITERATURE.md       # Literature survey with tables
│   ├── 06-FIELD-SURVEY.md     # Broad survey of adjacent fields
│   ├── 07-TUTORIAL-ZERO-SUM.md  # Tutorial: zero-sum theory
│   ├── 08-TUTORIAL-LEAN.md    # Tutorial: reading Lean proofs
│   └── 09-TUTORIAL-PNP.md     # Tutorial: P vs NP for beginners
│
├── paper/
│   └── paper.md               # Draft paper
│
└── blueprint/                 # LaTeX blueprint (leanblueprint)
    ├── src/content.tex        # Dependency graph
    └── ...
```

---

## Building the Project

### Prerequisites

- [Lean 4](https://lean-lang.org/) (installed via [elan](https://github.com/leanprover/elan))
- Git

### Build

```bash
git clone <repo-url>
cd zpnenp
lake build
```

If it compiles with no errors and no warnings containing `sorry`,
every theorem is machine-checked and valid.

### Verify zero sorry

```bash
grep -rn "sorry" Zpnenp/ | grep -v "^.*:.*--.*sorry"
# Should produce no output
```

---

## Documentation

### Start Here

If you're new to this project, read in this order:

1. **[Tutorial: P vs NP](docs/09-TUTORIAL-PNP.md)** — What is P vs NP
   and why does it matter? No math background needed.

2. **[Tutorial: Zero-Sum Theory](docs/07-TUTORIAL-ZERO-SUM.md)** — The
   mathematics behind this project, from basic examples to key theorems.

3. **[Tutorial: Reading Lean Proofs](docs/08-TUTORIAL-LEAN.md)** — How
   to read the formalized proofs, even if you've never used Lean.

### Deep Dives

4. **[Math Background](docs/02-MATH-BACKGROUND.md)** — Detailed coverage
   of zero-sum theory, additive combinatorics, and extremal set theory.

5. **[Barriers](docs/03-BARRIERS.md)** — The three barriers to proving
   P != NP and how our approach relates.

6. **[Field Survey](docs/06-FIELD-SURVEY.md)** — Broad survey of fields
   that might contain a hidden resolution of P vs NP.

7. **[Literature](docs/05-LITERATURE.md)** — Complete reference tables.

### Project Management

8. **[Thesis](THESIS.md)** — The thesis statement and argument structure.
9. **[Roadmap](ROADMAP.md)** — 24-week research plan with milestones.
10. **[Lean Status](docs/04-LEAN-STATUS.md)** — What's formalized, what's next.
11. **[Overview](docs/01-OVERVIEW.md)** — Repository structure and goals.

---

## The Adversary Game

Think of Subset Sum as a betting game:

```
    DEALER (adversary)              YOU (algorithm)
    ┌─────────────────┐            ┌────────────────┐
    │ Picks integers  │            │ Must say YES   │
    │ and a target    │───────────>│ or NO          │
    │                 │            │                │
    │ Tries to make   │            │ Tries to be    │
    │ you wrong       │            │ always right   │
    └─────────────────┘            └────────────────┘
```

The dealer can change ONE number and completely alter the landscape.
Your dynamic programming table? Invalidated. Your lattice reduction?
Broken. Your meet-in-the-middle split? Ruined.

**P != NP** means: no matter how clever you are, the dealer can
always find an instance you can't solve in polynomial time.

**Our results** constrain the dealer's strategy: at the modular
threshold, the dealer's optimal move is maximally structured
(all copies of one unit). The question is whether this structural
rigidity extends to standard Subset Sum.

---

## The Density Phase Transition

```
    EASY              HARD              EASY
    (lattice)         (???)             (pigeonhole)
    ◄─────────────────┼─────────────────►
    d << 1            d ~ 1             d >> 1

    density = n / log₂(max weight)
```

- **Low density**: Weights are exponentially large. The lattice
  structure (LLL algorithm) finds solutions in polynomial time.

- **High density**: Many elements, small weights. By pigeonhole,
  2^n subsets can't all have different sums when there are only
  n*M possible values. Collisions are forced.

- **Critical density**: The "Goldilocks zone." Neither lattice
  methods nor pigeonhole apply. This is where NP-hardness lives.

Our `pigeonhole_collision` theorem formalizes the high-density
case. The critical density regime remains the frontier.

---

## The Three Barriers

Any proof of P != NP must evade three known barriers:

### 1. Relativization (Baker-Gill-Solovay, 1975)

There exist "oracles" A and B such that P^A = NP^A but P^B != NP^B.
So any proof that works relative to ALL oracles can't resolve P vs NP.

**Our approach**: Uses internal arithmetic structure of Z/nZ
(not just black-box input-output behavior). Potentially non-relativizing.

### 2. Natural Proofs (Razborov-Rudich, 1997)

If one-way functions exist, you can't prove circuit lower bounds using
properties that (a) hold for random functions and (b) are efficiently
testable.

**Our approach**: The inverse Davenport theorem is specific to Subset Sum
(not a generic property of random functions). Potentially non-natural.

### 3. Algebrization (Aaronson-Wigderson, 2009)

Even arithmetic techniques (like IP = PSPACE) can't resolve P vs NP.

**Our approach**: This is the least clear barrier for our methods.

See [docs/03-BARRIERS.md](docs/03-BARRIERS.md) for full analysis.

---

## Where Could the Answer Come From?

Our [field survey](docs/06-FIELD-SURVEY.md) examined five broad areas:

### Most Promising Directions

1. **Sum-product phenomena**: P vs NP may be about the fundamental
   incompatibility of additive and multiplicative structure.
   The chain: sum-product -> extractors -> PRGs -> circuit lower bounds
   almost reaches P != NP.

2. **Uncommon graphs**: Ramsey multiplicity failures give properties
   that FAIL for random objects — potentially evading the natural proofs
   barrier. This direction appears underexplored.

3. **Proof complexity**: Super-polynomial proof lengths in ALL proof
   systems would prove P != NP (Cook-Reckhow thesis). The pigeonhole
   principle in bounded arithmetic connects to circuit lower bounds.

4. **The polynomial method at depth 4**: The "chasm at depth 4" means
   depth-4 arithmetic circuit lower bounds cascade to general lower
   bounds. The Croot-Lev-Pach polynomial method already gives
   exponential bounds in restricted settings.

---

## FAQ

### Is this a proof of P != NP?

**No.** This is a formalization of structural results from zero-sum
theory connected to Subset Sum complexity, with an honest analysis
of the gap between what we proved and what P != NP requires.

### What IS proved?

The Davenport constant D(Z/nZ) = n and its inverse theorem, fully
machine-checked in Lean 4. The density phase transition framework
for Subset Sum. The adversary game for modular zero-sum.

### Is anything new mathematically?

The mathematics (Davenport constant, inverse theorem) is known.
The contributions are: (1) first formalization in any theorem prover,
(2) the adjacent swap proof technique for the inverse theorem,
(3) the explicit connection to Subset Sum complexity with honest
gap analysis, (4) the broad field survey identifying underexplored
directions.

### Why Lean 4?

Machine-checked proofs eliminate hand-waving. For a problem as
important as P vs NP, every step must be rigorous. The Lean 4 +
Mathlib ecosystem has key results already formalized (EGZ theorem,
Sauer-Shelah, Plunnecke-Ruzsa) and has demonstrated success on
deep mathematical formalizations (PFR conjecture, Liquid Tensor).

### Why Subset Sum?

It's NP-complete, has a natural "adversary game" interpretation,
connects directly to additive combinatorics (a deep mathematical
field), and has a rich density-based phase transition that mirrors
physics.

### Can I contribute?

Yes! The most impactful contributions would be:
- Formalizing the Cauchy-Davenport theorem
- Formalizing the inverse EGZ theorem
- Exploring the "uncommon graphs" direction
- Connecting sum-product phenomena to Subset Sum
- Improving the leanblueprint dependency graph

### How do I learn more?

Start with the tutorials:
- [P vs NP for beginners](docs/09-TUTORIAL-PNP.md)
- [Zero-sum theory](docs/07-TUTORIAL-ZERO-SUM.md)
- [Reading Lean proofs](docs/08-TUTORIAL-LEAN.md)

Then read the [thesis statement](THESIS.md) and [roadmap](ROADMAP.md).

---

## Acknowledgments

This project builds on:
- [Mathlib](https://github.com/leanprover-community/mathlib4) —
  the Lean 4 mathematics library
- [Yaël Dillies](https://github.com/YaelDillies/LeanCamCombi) —
  formalization of the EGZ theorem in Mathlib
- The additive combinatorics community, especially the work of
  Erdos, Ginzburg, Ziv, Olson, Gao, Geroldinger, and Grynkiewicz

---

## License

[Apache 2.0](LICENSE)
