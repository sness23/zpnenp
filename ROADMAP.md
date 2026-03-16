# Roadmap: From Extremal Combinatorics to P ≠ NP

## Overview

This roadmap is structured in four phases, each building on the last. The formalization uses Lean 4 + Mathlib with the **leanblueprint** approach (LaTeX blueprint + dependency graph + linked Lean code).

---

## Phase 1: Foundations (Weeks 1–4)

**Goal**: Define Subset Sum in Lean, connect to existing Mathlib infrastructure, and formalize the basic objects of zero-sum theory.

### Milestone 1.1: Project Setup
- [ ] Initialize Lean 4 project with Mathlib dependency (`lake init zpnenp math`)
- [ ] Set up leanblueprint (`pip install leanblueprint`, template from [LeanProject](https://github.com/leanprover-community/LeanProject))
- [ ] Create initial blueprint LaTeX document with dependency graph
- [ ] CI pipeline: `lake build` + `leanblueprint all` on push

### Milestone 1.2: Subset Sum in Lean
- [ ] Define `SubsetSum` as a decision problem over `Finset Int`
  ```lean
  def SubsetSum (s : Finset Int) (t : Int) : Prop :=
    ∃ s' : Finset Int, s' ⊆ s ∧ s'.sum id = t
  ```
- [ ] Define `SubsetSumZero` (target = 0) as the natural zero-sum variant
- [ ] Prove basic properties: monotonicity (larger sets have more achievable sums), empty set case, singleton case
- [ ] Define modular variant `SubsetSumMod` over `ZMod n`

### Milestone 1.3: Connect to Existing Mathlib
- [ ] Import and verify `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv`
- [ ] State the connection: EGZ implies `SubsetSumMod` is trivially true for sets of size ≥ 2n−1
- [ ] Import `Mathlib.Combinatorics.SetFamily.Shatter` (Sauer-Shelah)
- [ ] Import `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

### Milestone 1.4: Davenport Constant
- [ ] Define Davenport constant D(G) for finite abelian groups
- [ ] Prove D(ℤ/nℤ) = n (Olson's result for cyclic groups)
- [ ] State the implication: |S| ≥ D(G) ⟹ `SubsetSumZero` over G is YES
- [ ] Begin formalization of D(G) for products of cyclic groups

---

## Phase 2: Structural Theory (Weeks 5–10)

**Goal**: Formalize the inverse theorems that characterize *what hard instances look like* and the sumset bounds that constrain solution spaces.

### Milestone 2.1: Inverse Zero-Sum Theorems
- [ ] Formalize the characterization of zero-sum-free sequences of maximal length in ℤ/nℤ
  - These are sequences of (n−1) copies of a single element coprime to n
- [ ] Formalize the inverse EGZ: characterize sequences of length 2n−2 in ℤ/nℤ without an n-element zero-sum subsequence
  - These consist of (n−1) copies of element a and (n−1) copies of element b, with a−b coprime to n
- [ ] **Key insight to formalize**: Extremal (hardest) instances are *highly structured*, not random

### Milestone 2.2: Sumset Bounds
- [ ] Formalize Cauchy-Davenport theorem: |A + B| ≥ min(p, |A| + |B| − 1) in ℤ/pℤ
- [ ] Leverage existing Plünnecke-Ruzsa from Mathlib for sumset growth bounds
- [ ] Formalize the iterated sumset bound: the set of all subset sums of n elements in ℤ/pℤ has size min(p, 1 + n(n+1)/2)
- [ ] State Kneser's theorem (may already be partially in Mathlib via additive combinatorics modules)

### Milestone 2.3: Density and Phase Transitions
- [ ] Define density of a Subset Sum instance: d = n / log₂(max aᵢ)
- [ ] Formalize the Lagarias-Odlyzko density argument: at low density (d < 1/n), random instances are solvable
- [ ] State the pigeonhole threshold: at high density (d >> 1), solutions are guaranteed
- [ ] Characterize the critical density d ≈ 1 regime as the hardness frontier

### Milestone 2.4: Freiman's Theorem Connection
- [ ] State Freiman's theorem: |A + A| ≤ K|A| ⟹ A ⊆ generalized arithmetic progression
- [ ] Leverage PFR project results if available in Mathlib (Polynomial Freiman-Ruzsa)
- [ ] Connect: sets with few distinct subset sums must have arithmetic structure
- [ ] Formalize: structured inputs are algorithmically easier (qualitative statement)

---

## Phase 3: Complexity Bridge (Weeks 11–18)

**Goal**: Build the formal bridge between combinatorial structure theorems and computational complexity. This is the novel and most speculative phase.

### Milestone 3.1: Complexity Definitions
- [ ] Import or adapt P, NP, polynomial-time reduction definitions from [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
- [ ] Define Subset Sum as a formal language (decision problem over binary strings)
- [ ] Prove Subset Sum ∈ NP (the verifier is just: check the subset, sum it, compare)

### Milestone 3.2: The Adversary Framework
- [ ] Formalize the "adversary game" for Subset Sum:
  - An adversary chooses an instance (S, t)
  - An algorithm A outputs YES/NO in poly-time
  - The adversary wins if A is wrong
- [ ] Connect to query complexity: formalize decision tree model for Subset Sum
- [ ] Prove the trivial Ω(n) query lower bound (must read all inputs)
- [ ] **Open question**: Can the adversary framework + structural theorems yield super-polynomial bounds?

### Milestone 3.3: Structure vs. Computation
- [ ] Formalize the key dichotomy:
  - **Structured instances** (small doubling, arithmetic progressions): solvable by Freiman-type exploitation
  - **Unstructured instances** (random-looking): solvable by density/lattice methods
  - **Critical-density instances with intermediate structure**: ??? — the conjectured hard core
- [ ] Attempt to formalize: for any poly-time algorithm A, the adversary can find instances in the "hard core" that A gets wrong
- [ ] **This is where the proof would live or fail** — explore rigorously whether the structural theory actually implies computational hardness

### Milestone 3.4: Barrier Analysis
- [ ] Verify that the approach is non-relativizing: does it examine internal structure of computation (not just input-output)?
- [ ] Verify non-naturality: is the hardness property specific to Subset Sum (not a large-fraction property of all functions)?
- [ ] Verify non-algebrization: does the argument go beyond algebraic oracle queries?
- [ ] If any barrier is hit: document it precisely, as this itself is a publishable insight

---

## Phase 4: Synthesis and Publication (Weeks 19–24)

**Goal**: Either (a) complete the proof, (b) identify exactly where it fails and what additional insight is needed, or (c) produce publishable partial results.

### Milestone 4.1: Proof Assembly
- [ ] If Phase 3 succeeds: assemble the full proof in Lean with blueprint
- [ ] Machine-check every step
- [ ] Generate the dependency graph showing the complete proof structure
- [ ] Write the human-readable paper from the blueprint

### Milestone 4.2: Partial Results (if full proof eludes us)
Publishable outcomes even if P ≠ NP is not proved:
- [ ] First Lean formalization of Davenport constants and inverse zero-sum theorems
- [ ] First formal connection between zero-sum theory and Subset Sum complexity
- [ ] New structural characterization of "hard core" Subset Sum instances
- [ ] Barrier analysis: precise identification of what additional techniques are needed
- [ ] Open problems for the combinatorics and complexity communities

### Milestone 4.3: Community Engagement
- [ ] Submit blueprint to Lean Zulip for community review
- [ ] Present at relevant venues (STOC/FOCS workshop, Lean Together, ITP)
- [ ] ArXiv preprint with Lean code as supplementary material
- [ ] If successful: submit to Clay Mathematics Institute

---

## Key Dependencies (Blueprint Graph)

```
                    ┌─────────────────┐
                    │   P ≠ NP Proof   │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
    ┌─────────▼──────┐ ┌────▼─────┐ ┌──────▼──────┐
    │  Adversary     │ │ Barrier  │ │  Structure  │
    │  Framework     │ │ Analysis │ │  vs Compute │
    └─────────┬──────┘ └────┬─────┘ └──────┬──────┘
              │              │              │
    ┌─────────▼──────────────▼──────────────▼──────┐
    │              Complexity Bridge                │
    │     (P, NP definitions + SubsetSum ∈ NP)     │
    └──────────────────────┬───────────────────────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
  ┌──────▼──────┐  ┌──────▼──────┐  ┌───────▼──────┐
  │  Inverse    │  │   Sumset    │  │   Density    │
  │  Zero-Sum   │  │   Bounds    │  │   Phase      │
  │  Theorems   │  │  (Kneser,   │  │  Transitions │
  │             │  │   C-D, PfR) │  │              │
  └──────┬──────┘  └──────┬──────┘  └───────┬──────┘
         │                │                 │
  ┌──────▼────────────────▼─────────────────▼──────┐
  │               Foundations                       │
  │  SubsetSum def, Davenport const, EGZ import     │
  └────────────────────────────────────────────────┘
```

---

## Tools and Infrastructure

| Tool | Purpose |
|------|---------|
| [Lean 4](https://lean-lang.org/) | Theorem prover |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Mathematics library |
| [leanblueprint](https://github.com/PatrickMassot/leanblueprint) | LaTeX → dependency graph → linked Lean code |
| [LeanProject template](https://github.com/leanprover-community/LeanProject) | Project skeleton |
| [LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) | P, NP, reduction definitions |
| [LeanCamCombi](https://github.com/YaelDillies/LeanCamCombi) | Extremal combinatorics formalizations |

---

## Key Literature

### Zero-Sum Theory
- Erdős, Ginzburg, Ziv (1961) — The 2n−1 theorem
- Olson (1969) — Davenport constant for ℤ/pℤ, D(ℤ_p) = p
- Gao (1996) — Generalization of EGZ to all finite abelian groups
- Geroldinger, Halter-Koch (2006) — *Non-Unique Factorizations* (monograph on zero-sum theory)
- Grynkiewicz (2013) — *Structural Additive Theory* (comprehensive reference)

### Additive Combinatorics
- Freiman (1966) — Sets with small doubling live in GAPs
- Kneser (1953) — Sumset lower bounds in abelian groups
- Plünnecke (1970), Ruzsa (1989) — Sumset growth inequalities
- Balog-Szemerédi (1994), Gowers (1998) — Additive structure from many additive quadruples
- Tao, Green (2005+) — Modern additive combinatorics program

### Subset Sum Algorithms and Complexity
- Horowitz, Sahni (1974) — Meet-in-the-middle, O(2^{n/2})
- Lagarias, Odlyzko (1985) — Lattice reduction for low-density instances
- Impagliazzo, Naor (1996) — Average-case hardness from OWFs
- Bringmann (2017) — Õ(T) pseudo-polynomial algorithm
- Becker, Coron, Joux (2011) — O(2^{0.291n}) for random instances

### Barriers
- Baker, Gill, Solovay (1975) — Relativization
- Razborov, Rudich (1997) — Natural proofs
- Aaronson, Wigderson (2009) — Algebrization

### Lean Formalization Precedents
- Liquid Tensor Experiment — Scholze's challenge, completed in Lean
- PFR Project (Tao, 2023) — Polynomial Freiman-Ruzsa in Lean, ~3 weeks
- LeanCamCombi (Dillies) — Szemerédi Regularity Lemma in Lean

---

## Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| The argument hits a known barrier | High | Phase 3.4 barrier analysis; knowing *which* barrier is itself valuable |
| Structural theorems don't imply computational lower bounds | High | The gap between "existence of hard instances" and "no poly-time algorithm" is real; inverse theorems tell us *what* hard instances look like but not *why* they're computationally hard |
| Lean formalization bottleneck | Medium | Blueprint approach + community collaboration; start with what's already in Mathlib |
| Key results missing from Mathlib | Medium | Formalize them — this is independently publishable |
| Someone else proves P ≠ NP first | Very low | Enjoy the champagne |

## Success Criteria

**Full success**: Machine-checked proof of P ≠ NP via Subset Sum + extremal combinatorics. Millennium Prize. $1M. Glory.

**Partial success (still excellent)**:
- Novel formalized connection between zero-sum theory and computational complexity
- First Lean formalization of inverse zero-sum theorems
- Precise characterization of what additional insight is needed beyond current extremal combinatorics
- Publishable paper at ITP, STOC/FOCS workshop, or specialized journal
- A roadmap that others can build on
