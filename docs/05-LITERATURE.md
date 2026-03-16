# Literature Survey

## Zero-Sum Theory

| Paper | Authors | Year | Key Result | Relevance |
|-------|---------|------|------------|-----------|
| "A combinatorial problem on finite abelian groups" | Erdős, Ginzburg, Ziv | 1961 | 2n−1 integers contain n with sum ≡ 0 (mod n) | Foundation: structural guarantee for modular subset sum |
| "A combinatorial problem on finite abelian groups II" | Olson | 1969 | D(ℤ/pℤ) = p; 2√p bound for variable-length zero-sum | Tighter thresholds for prime moduli |
| Generalization of EGZ | Gao | 1996 | n + D(G) − 1 elements guarantee length-n zero-sum | Unified EGZ for all finite abelian groups |
| *Non-Unique Factorizations* | Geroldinger, Halter-Koch | 2006 | Comprehensive monograph on zero-sum theory | Reference for Davenport constant, inverse results |
| *Structural Additive Theory* | Grynkiewicz | 2013 | Modern treatment of zero-sum and additive combinatorics | Primary reference for inverse zero-sum theorems |
| Weighted EGZ | Grynkiewicz | 2005 | Extension to weighted sums | Generalization direction |
| Kemnitz conjecture (confirmed) | Reiher | 2007 | Multi-dimensional EGZ: 4p−3 points in ℤ/pℤ² | Higher-dimensional generalization |

## Additive Combinatorics

| Paper | Authors | Year | Key Result | Relevance |
|-------|---------|------|------------|-----------|
| *Foundations of a Structural Theory of Set Addition* | Freiman | 1966 | Small doubling → GAP structure | Structured inputs are exploitable |
| Sumset lower bounds | Kneser | 1953 | |A+B| ≥ |A+H| + |B+H| − |H| | Constrains how few subset sums exist |
| Sumset estimates | Plünnecke | 1970 | Sumset growth bounds | Already in Mathlib |
| Sumset estimates via graph theory | Ruzsa | 1989 | Plünnecke-Ruzsa inequality | Already in Mathlib |
| Balog-Szemerédi | Balog, Szemerédi | 1994 | Many additive quadruples → structured subset | Bridge between weak and strong structure |
| Quantitative Balog-Szemerédi | Gowers | 1998 | Polynomial bounds for BSz | Effective version |
| Polynomial Freiman-Ruzsa | Gowers, Green, Manners, Tao | 2023 | PFR conjecture proved | Formalized in Lean (~3 weeks) |

## Subset Sum Algorithms

| Paper | Authors | Year | Key Result | Relevance |
|-------|---------|------|------------|-----------|
| Meet-in-the-middle | Horowitz, Sahni | 1974 | O(2^{n/2}) time | Best worst-case exponent (still) |
| Space-efficient MITM | Schroeppel, Shamir | 1981 | O(2^{n/2}) time, O(2^{n/4}) space | Same time, much less space |
| Lattice reduction for low-density | Lagarias, Odlyzko | 1985 | Poly-time for d < 1/n via LLL | Low-density instances are easy |
| Improved density threshold | Coster, Joux, LaMacchia, Odlyzko, Schnorr, Stern | 1992 | Threshold improved to d < 0.94 | Larger easy regime |
| Average-case hardness from OWFs | Impagliazzo, Naor | 1996 | Subset Sum hard on average ↔ OWFs exist | Cryptographic foundation |
| Representation technique | Howgrave-Graham, Joux | 2010 | O(2^{0.337n}) for random instances | Below 2^{n/2} for average case |
| Improved representations | Becker, Coron, Joux | 2011 | O(2^{0.291n}) for random instances | Best known for random case |
| Dense subset sum hardness | Austrin, Kaski, Koivisto, Nederlof | 2016 | Dense case may be hardest | Critical density = hardness frontier |
| Near-linear pseudo-polynomial | Bringmann | 2017 | Õ(T) randomized algorithm | Best pseudo-polynomial |
| Deterministic pseudo-polynomial | Koiliaris, Xu | 2019 | Õ(√n · T) deterministic | Best deterministic pseudo-polynomial |

## Barrier Results

| Paper | Authors | Year | Key Result | Impact |
|-------|---------|------|------------|--------|
| Relativizations of P =? NP | Baker, Gill, Solovay | 1975 | P vs NP has different answers under different oracles | Rules out relativizing proofs |
| Natural proofs | Razborov, Rudich | 1997 | Constructive + largeness + OWFs → no circuit lower bounds | Rules out natural combinatorial proofs |
| Algebrization | Aaronson, Wigderson | 2009 | Arithmetization techniques also blocked | Rules out IP=PSPACE-style proofs |
| IP = PSPACE | Shamir | 1990 | Non-relativizing result | Shows barriers can be overcome |
| NEXP ⊄ ACC⁰ | Williams | 2011 | Algorithm → circuit lower bound | Circumvents natural proofs barrier |
| Geometric Complexity Theory | Mulmuley, Sohoni | 2001 | Algebraic geometry approach | Potentially avoids all three barriers |

## Extremal Set Theory

| Paper | Authors | Year | Key Result | Relevance |
|-------|---------|------|------------|-----------|
| Sunflower lemma | Erdős, Rado | 1960 | Large uniform families contain sunflowers | Circuit lower bounds tool |
| Improved sunflower | Alweiss, Lovett, Wu, Zhang | 2020 | Near-optimal sunflower bounds | Major improvement |
| Sauer-Shelah lemma | Sauer; Shelah | 1972 | VC-dim d → |F| ≤ O(nᵈ) | Bounds solution space complexity |
| Monotone circuit lower bounds | Razborov | 1985 | Exp lower bounds for CLIQUE | Used sunflower lemma for complexity |
| *Extremal Combinatorics* | Jukna | 2001 | Textbook connecting extremal comb to CS | Key reference for our bridge |

## Lean Formalization Precedents

| Project | Team | Year | What Was Formalized | Timeline |
|---------|------|------|--------------------|----|
| Liquid Tensor Experiment | Lean community | 2022 | Scholze's liquid vector space theorem | ~1 year |
| PFR | Tao + community | 2023 | Polynomial Freiman-Ruzsa conjecture | ~3 weeks |
| LeanCamCombi | Dillies + Mehta | 2022+ | Szemerédi Regularity Lemma, Roth's theorem | Ongoing |
| Sphere eversion | van Doorn et al. | 2023 | Sphere eversion via h-principle | ~2 years |

## Key References for Next Steps

### Immediate (Phase 1)
1. Geroldinger & Halter-Koch, *Non-Unique Factorizations* — for Davenport constant formalization
2. Grynkiewicz, *Structural Additive Theory* — for inverse zero-sum theorems
3. Mathlib source: `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv` — understand proof structure

### Medium-term (Phase 2-3)
4. Jukna, *Extremal Combinatorics with Applications in Computer Science* — bridge between combinatorics and complexity
5. Austrin et al., "Dense Subset Sum May Be the Hardest" — understand hardness landscape
6. Aaronson-Wigderson, "Algebrization" — understand what techniques survive
7. LeanMillenniumPrizeProblems repo — import complexity definitions
