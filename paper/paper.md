# Formalized Zero-Sum Theory and the Subset Sum Complexity Landscape: A Lean 4 Investigation

## Abstract

We present a complete Lean 4 formalization of the Davenport constant for cyclic groups and its inverse theorem, connecting these results from additive combinatorics to the computational complexity of the Subset Sum problem. Our formalization establishes D(Z/nZ) = n via a pigeonhole argument on prefix sums, proves the full inverse Davenport theorem (characterizing maximal zero-sum free sequences as copies of a single unit element), and formalizes the density-based phase transition framework for Subset Sum hardness. All results are machine-checked with zero `sorry` declarations. We identify the precise gap between the structural rigidity of extremal zero-sum instances and the computational hardness of Subset Sum, documenting four research directions that could bridge this gap toward resolving P vs NP.

**Keywords**: Subset Sum, Davenport constant, zero-sum theory, Lean 4, formalization, additive combinatorics, computational complexity

## 1. Introduction

The Subset Sum problem — given a set of integers, does some subset sum to a target? — is one of the earliest known NP-complete problems. Despite decades of research, the precise boundary between tractable and intractable instances remains poorly understood. Meanwhile, the field of additive combinatorics has developed a deep structural theory about when subsets with prescribed sums must exist, culminating in results like the Erdos-Ginzburg-Ziv theorem and the Davenport constant.

We investigate whether these structural results, when formalized rigorously, reveal connections to computational complexity that informal reasoning might miss. Our contributions are:

1. **A complete Lean 4 formalization** of the Davenport constant D(Z/nZ) = n, including both the pigeonhole upper bound and the lower bound witness.

2. **The first formalization of the inverse Davenport theorem**: maximal zero-sum free sequences in Z/nZ are exactly (n-1) copies of a unit element. This required a novel "adjacent swap" argument formalized via the lemma that two bijections agreeing on n-1 of n inputs must agree everywhere.

3. **A formalized density framework** connecting the modular zero-sum threshold to the standard Subset Sum phase transition, with the pigeonhole collision theorem establishing that high-density instances are always solvable.

4. **An honest gap analysis** identifying precisely where the structural theory falls short of proving P != NP, with four concrete research directions informed by a broad survey of adjacent fields.

All proofs compile with zero `sorry` declarations against Lean 4.28.0 and Mathlib v4.28.0.

## 2. Background

### 2.1 The Davenport Constant

The Davenport constant D(G) of a finite abelian group G is the smallest integer d such that every sequence of d elements from G contains a nonempty subsequence summing to zero.

**Theorem (Olson, 1969)**: D(Z/nZ) = n.

The upper bound follows from the pigeonhole principle applied to prefix sums: n+1 prefix sums in a group of order n must include a collision. The lower bound is witnessed by (n-1) copies of any unit element.

### 2.2 The Inverse Davenport Theorem

The inverse theorem characterizes the *extremal* sequences — those of maximal length without a zero-sum subsequence:

**Theorem**: A multiset of size n-1 in Z/nZ is zero-sum free if and only if it consists of (n-1) copies of a single unit element g (i.e., gcd(g, n) = 1).

This is the structural result that matters for our program: the adversary's "hardest" instances are maximally rigid, not random.

### 2.3 Subset Sum Density

The density of a Subset Sum instance with n elements and maximum weight M is d = n / log_2(M). The problem exhibits a phase transition:

- **High density** (d >> 1): Pigeonhole forces collisions; the problem is easy.
- **Low density** (d << 1): Lattice reduction (LLL) solves random instances.
- **Critical density** (d ~ 1): Neither method applies; hardness concentrates here.

### 2.4 The Erdos-Ginzburg-Ziv Theorem

**Theorem (EGZ, 1961)**: Among any 2n-1 integers, there exist n whose sum is divisible by n.

This is formalized in Mathlib via Chevalley-Warning. We connect it to our Subset Sum definitions.

## 3. Formalization in Lean 4

### 3.1 Architecture

The formalization consists of seven modules totaling approximately 700 lines of Lean 4:

| Module | Lines | Content |
|--------|-------|---------|
| `SubsetSum.lean` | ~60 | Core definitions, basic properties |
| `ZeroSum.lean` | ~50 | EGZ connection, modular zero-sum |
| `Structural.lean` | ~40 | Counting bounds |
| `Davenport.lean` | ~160 | D(Z/nZ) = n, both bounds |
| `Inverse.lean` | ~250 | Full inverse theorem |
| `Complexity.lean` | ~130 | Adversary game, gap analysis |
| `Density.lean` | ~170 | Density definitions, pigeonhole collision |

All modules build against Lean 4.28.0 with Mathlib v4.28.0.

### 3.2 Key Definitions

```lean
-- The Subset Sum decision problem
def SubsetSum (s : Finset Z) (t : Z) : Prop :=
  exists s' in s.powerset, s'.sum id = t

-- Zero-sum free multisets
def ZeroSumFree {G : Type*} [AddCommMonoid G] (s : Multiset G) : Prop :=
  forall t <= s, t != 0 -> t.sum != 0
```

### 3.3 The Davenport Constant: D(Z/nZ) = n

**Upper bound** (`davenport_upper`): Given a multiset of n elements in ZMod n, we convert to a list, define the prefix sum function Fin(n+1) -> ZMod n, apply `Fintype.exists_ne_map_eq_of_card_lt` (pigeonhole), extract the contiguous zero-sum slice, and show it is a nonempty submultiset.

The proof required establishing the list identity `l.take j = l.take i ++ (l.drop i).take (j-i)` via `List.take_add`.

**Lower bound** (`zeroSumFree_replicate_one`): The multiset of (n-1) copies of 1 is zero-sum free because any k-element submultiset sums to k in ZMod n, and 1 <= k <= n-1 implies n does not divide k.

### 3.4 The Inverse Theorem

The proof of the full inverse Davenport theorem required three key lemmas:

**Lemma 1** (`prefix_sums_injective`): Prefix sums of a zero-sum free list are all distinct. Proof: if two prefix sums coincide, the elements between them form a nonempty zero-sum submultiset.

**Lemma 2** (`prefix_sums_surjective`): For a zero-sum free list of length n-1, the n prefix sums form a bijection Fin n -> ZMod n. Proof: by `Fintype.bijective_iff_injective_and_card`, an injective map between finite sets of equal size is bijective.

**Lemma 3** (`injective_agree_of_agree_except`): Two injective functions from Fin n to an n-element type that agree on all but one input must agree everywhere. Proof: by contradiction — if they disagree at position k, then the value g(k) must equal f(j) for some j != k (by surjectivity of f), but f(j) = g(j) (by agreement), giving g(k) = g(j), contradicting injectivity of g.

**The main theorem** (`all_eq`): Any two elements a, b of a maximal zero-sum free multiset are equal. Proof: construct lists [a, b, ...rest] and [b, a, ...rest] representing the same multiset. Both yield prefix sum bijections. These bijections agree at all positions except 1 (where they give a and b respectively, since a+b = b+a). By Lemma 3, a = b.

**The unit property** (`isUnit_of_replicate_zeroSumFree`): If (n-1) copies of g are zero-sum free, then g is a unit. Proof: the prefix sums {0, g, 2g, ..., (n-1)g} are a permutation of ZMod n, so some k*g = 1, making g a unit.

### 3.5 Density and Pigeonhole

We formalize the pigeonhole collision theorem: if 2^n > n*M + 1 (high density), then two distinct subsets of any n-element set with weights in {1,...,M} must have the same sum. The proof uses `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` with the range bound `subsetSums_range_bound`.

## 4. The Structure-Computation Gap

### 4.1 What We Proved

Our formalization establishes:

1. **Modular zero-sum at the Davenport threshold is completely characterized**: the adversary's NO instances are exactly replicate-of-unit (proved: `adversary_no_instances`).

2. **Above the threshold, the answer is always YES** (proved: `adversary_large_always_yes`).

3. **The threshold decision problem is O(n)-decidable**: just check if all elements are equal and the common element is a unit.

### 4.2 What We Did NOT Prove

The modular zero-sum problem at the Davenport threshold is efficiently decidable. This does NOT imply P = NP. Standard Subset Sum (over Z with arbitrary targets) is harder than modular zero-sum (over Z/nZ).

The gap between our structural results and P != NP requires bridging from modular to integer arithmetic, through the density phase transition at d ~ 1.

### 4.3 Research Directions

A broad survey of adjacent fields (Ramsey theory, probabilistic combinatorics, algebra, logic, physics) identified four promising directions:

**Direction A: Sum-product phenomena.** The incompatibility of additive and multiplicative structure (Erdos-Szemeredi sum-product theorem) connects to extractors and pseudorandomness. The chain sum-product -> extractors -> PRGs -> circuit lower bounds almost reaches P != NP.

**Direction B: Uncommon graphs.** Ramsey multiplicity failures (graphs where random colorings don't minimize monochromatic copies) give properties that are non-natural in the Razborov-Rudich sense — potentially evading the strongest known barrier to proving P != NP.

**Direction C: Proof complexity.** The weak pigeonhole principle in bounded arithmetic connects to circuit lower bounds. Our pigeonhole-based proofs (Davenport upper bound, density collision) are in the same spirit as proof complexity lower bounds.

**Direction D: The polynomial method at depth 4.** The "chasm at depth 4" (Agrawal-Vinay) means that depth-4 arithmetic circuit lower bounds would cascade to general lower bounds. The polynomial method (Croot-Lev-Pach) already gives exponential bounds in restricted settings.

## 5. Related Work

### 5.1 Formalized Additive Combinatorics

The Polynomial Freiman-Ruzsa conjecture was formalized in Lean 4 by Tao et al. (2023) in approximately three weeks using the leanblueprint approach. Mathlib contains formalizations of the EGZ theorem (Dillies), Sauer-Shelah lemma, and Plunnecke-Ruzsa inequality.

### 5.2 Formalized Complexity Theory

The LeanMillenniumPrizeProblems project formalizes P, NP, and polynomial-time reductions using Mathlib's TM2 model. Mathlib's computability library includes Turing machines and the halting problem but does not yet contain P and NP definitions in its main branch.

### 5.3 The Davenport Constant

The Davenport constant has been extensively studied (Geroldinger-Halter-Koch 2006, Grynkiewicz 2013). To our knowledge, this is the first complete formalization of D(Z/nZ) = n and the inverse Davenport theorem in any theorem prover.

## 6. Conclusion

We have presented a complete, zero-sorry Lean 4 formalization connecting zero-sum theory to Subset Sum complexity. The formalization proves the Davenport constant and its inverse theorem, establishes the density phase transition framework, and honestly identifies the gap between structural rigidity and computational hardness.

The inverse Davenport theorem — that the adversary's extremal instances are maximally structured — is a striking constraint on the hardness landscape. Whether this structural rigidity can be leveraged to prove computational lower bounds remains an open question at the frontier of mathematics.

The project is open-source at [repository URL] and builds against Lean 4.28.0 with Mathlib v4.28.0.

## References

- Austrin, Kaski, Koivisto, Nederlof (2016). Dense Subset Sum May Be the Hardest. STACS.
- Baker, Gill, Solovay (1975). Relativizations of the P =? NP Question. SIAM J. Comput.
- Becker, Coron, Joux (2011). Improved Generic Algorithms for Hard Knapsacks. EUROCRYPT.
- Bringmann (2017). A Near-Linear Pseudopolynomial Time Algorithm for Subset Sum. SODA.
- Dillies, Mehta (2022). Formalising Szemeredi's Regularity Lemma in Lean. ITP.
- Erdos, Ginzburg, Ziv (1961). Theorem in the Additive Number Theory. Bull. Res. Council Israel.
- Gao (1996). A Combinatorial Problem on Finite Abelian Groups. J. Number Theory.
- Geroldinger, Halter-Koch (2006). Non-Unique Factorizations. Chapman & Hall/CRC.
- Grynkiewicz (2013). Structural Additive Theory. Springer.
- Horowitz, Sahni (1974). Computing Partitions with Applications to the Knapsack Problem. JACM.
- Impagliazzo, Naor (1996). Efficient Cryptographic Schemes Provably as Secure as Subset Sum. J. Cryptology.
- Lagarias, Odlyzko (1985). Solving Low-Density Subset Sum Problems. JACM.
- Olson (1969). A Combinatorial Problem on Finite Abelian Groups I. J. Number Theory.
- Razborov, Rudich (1997). Natural Proofs. JCSS.
- Tao et al. (2023). A Formal Proof of the Polynomial Freiman-Ruzsa Conjecture. arXiv.
