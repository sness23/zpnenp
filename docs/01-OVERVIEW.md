# Project Overview: zpnenp

**Goal**: Investigate whether results from Extremal Set Theory and Zero-Sum Theory already contain the structural insights needed to prove P ≠ NP, via the Subset Sum problem, formalized in Lean 4.

**Name**: zpnenp = "Zero-sum Problems → NP ≠ P" (or "ℤ P≠NP")

## The Big Idea

Combinatorialists in Extremal Set Theory and Additive Combinatorics have developed a deep structural theory about when subsets with prescribed sums must exist, what "hard" instances look like, and how sumset sizes grow. These results are so natural to the community that their implications for computational complexity may be hiding in plain sight — like fish who don't notice water.

We aim to:
1. Systematically formalize these structural results in Lean 4
2. Build a rigorous bridge to computational complexity
3. Determine whether these structural constraints imply that no polynomial-time algorithm can solve Subset Sum in the worst case

## The Adversarial Dealer Argument

The core intuition, expressed as a game:

1. A **dealer** presents you with a set of integers and a target
2. You must bet: does some subset sum to the target?
3. The dealer can change **one number** and completely alter the computational landscape — your dynamic programming table, meet-in-the-middle splits, lattice reduction — all invalidated
4. A perfect adversary with NP-oracle knowledge can always find modifications that defeat any fixed polynomial-time strategy

**Formal version**: For every polynomial-time algorithm A, there exists an input instance x such that A(x) gives the wrong answer for the Subset Sum decision problem.

## Current Status

- **Lean 4 project**: initialized with Mathlib, building cleanly
- **Formalized**: SubsetSum definition, basic properties, EGZ connection
- **Phase**: 1 of 4 (Foundations)

## Repository Structure

```
zpnenp/
├── THESIS.md              # Thesis statement and big picture
├── ROADMAP.md             # 24-week plan with milestones
├── docs/                  # Detailed documentation
│   ├── 01-OVERVIEW.md     # This file
│   ├── 02-MATH-BACKGROUND.md
│   ├── 03-BARRIERS.md
│   ├── 04-LEAN-STATUS.md
│   └── 05-LITERATURE.md
├── Zpnenp/                # Lean 4 source
│   ├── Basic.lean         # Root module
│   ├── SubsetSum.lean     # Core definitions
│   ├── ZeroSum.lean       # EGZ connection
│   └── Structural.lean    # Structural properties
├── lakefile.toml           # Lean build config
└── lean-toolchain          # Lean version
```
