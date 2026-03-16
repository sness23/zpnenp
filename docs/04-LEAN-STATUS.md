# Lean Formalization Status

## Project Setup

- **Lean version**: 4.28.0
- **Mathlib**: v4.28.0
- **Build status**: Clean (all 1867 modules)
- **Blueprint**: Not yet set up (planned)

## What We've Formalized

### `Zpnenp/SubsetSum.lean` — Core Definitions

| Declaration | Type | Status |
|-------------|------|--------|
| `SubsetSum s t` | `def` | Defined: ∃ s' ∈ s.powerset, s'.sum id = t |
| `SubsetSumZero s` | `def` | Defined: ∃ nonempty s' ⊆ s, s'.sum id = 0 |
| `subsetSums s` | `def` | Defined: s.powerset.image (sum id) |
| `subsetSum_zero` | `theorem` | Proved: SubsetSum s 0 always holds |
| `subsetSum_mono` | `theorem` | Proved: s ⊆ t → SubsetSum s target → SubsetSum t target |
| `subsetSum_singleton` | `theorem` | Proved: SubsetSum {a} t ↔ t = 0 ∨ t = a |
| `mem_subsetSums` | `theorem` | Proved: t ∈ subsetSums s ↔ SubsetSum s t |

### `Zpnenp/ZeroSum.lean` — EGZ Connection

| Declaration | Type | Status |
|-------------|------|--------|
| `ModSubsetSumZero s n` | `def` | Defined: ∃ nonempty s' ⊆ s, n ∣ s'.sum id |
| `egz_finset` | `theorem` | Proved: |s| ≥ 2n−1 → ∃ t ⊆ s, |t| = n ∧ n ∣ t.sum id |
| `egz_implies_modSubsetSumZero` | `theorem` | Proved: |s| ≥ 2n−1 ∧ n > 1 → ModSubsetSumZero s n |

### `Zpnenp/Structural.lean` — Counting

| Declaration | Type | Status |
|-------------|------|--------|
| `card_subsetSums_le` | `theorem` | Proved: |subsetSums s| ≤ 2^|s| |

## What's Available in Mathlib

Already formalized results we can import and use:

| Result | Mathlib Location |
|--------|-----------------|
| Erdős-Ginzburg-Ziv theorem | `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv` |
| Sauer-Shelah / VC dimension | `Mathlib.Combinatorics.SetFamily.Shatter` |
| Plünnecke-Ruzsa inequality | `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` |
| Additive energy | `Mathlib.Combinatorics.Additive.Energy` |
| Finset operations | `Mathlib.Data.Finset.*` |
| ZMod arithmetic | `Mathlib.Data.ZMod.*` |
| Turing machines | `Mathlib.Computability.TuringMachine` |
| Polynomial-time | `Mathlib.Computability.TMComputable` |

## What Needs Formalization (TODOs)

### Phase 1 (Current)
- [ ] Davenport constant D(G) definition
- [ ] D(ℤ/nℤ) = n proof
- [ ] Olson's theorem (2√p bound for zero-sum in ℤ/pℤ)
- [ ] leanblueprint setup

### Phase 2
- [ ] Inverse zero-sum: characterize zero-sum-free sequences of maximal length
- [ ] Inverse EGZ: characterize sequences of length 2n−2 without n-element zero-sum
- [ ] Cauchy-Davenport theorem
- [ ] Subset sum density definition
- [ ] Pigeonhole density argument

### Phase 3
- [ ] Import P, NP definitions from LeanMillenniumPrizeProblems
- [ ] Subset Sum ∈ NP (verifier)
- [ ] Adversary game formalization
- [ ] Structure vs. computation dichotomy
- [ ] Barrier analysis

### Phase 4
- [ ] Proof assembly (if Phase 3 succeeds)
- [ ] Paper from blueprint
- [ ] Community review

## External Lean Projects to Leverage

| Project | What It Provides | URL |
|---------|-----------------|-----|
| LeanMillenniumPrizeProblems | P, NP, reduction definitions | github.com/lean-dojo/LeanMillenniumPrizeProblems |
| LeanCamCombi | Extremal combinatorics (Szemerédi Regularity Lemma) | github.com/YaelDillies/LeanCamCombi |
| PFR Project | Polynomial Freiman-Ruzsa (additive combinatorics) | github.com/teorth/pfr |
| leanblueprint | LaTeX → dependency graph tooling | github.com/PatrickMassot/leanblueprint |
| LeanProject template | Blueprint project skeleton | github.com/leanprover-community/LeanProject |

## Lean Code Architecture

```
SubsetSum.lean
    ↓ (imported by)
ZeroSum.lean ←── Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
    ↓
Structural.lean ←── Mathlib.Combinatorics.Additive.PluenneckeRuzsa (planned)
    ↓
Basic.lean (root)
```

Future modules:
- `Davenport.lean` — Davenport constant
- `Inverse.lean` — Inverse zero-sum theorems
- `Density.lean` — Phase transitions and density arguments
- `Complexity.lean` — P, NP bridge
- `Adversary.lean` — Adversary game formalization
