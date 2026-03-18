# Tutorial: P vs NP for Beginners

This tutorial explains the P vs NP problem and how our project
connects to it.

## The Million-Dollar Question

The **P vs NP problem** is one of seven Millennium Prize Problems,
each worth $1,000,000. It asks:

> Is it always easy to CHECK a solution as it is to FIND one?

More precisely: if you can verify a solution quickly, can you also
find a solution quickly?

## P: Problems You Can SOLVE Quickly

**P** (Polynomial time) is the class of problems a computer can
solve efficiently — in time proportional to some polynomial of the
input size (like n^2, n^3, etc.).

Examples:
- **Sorting** a list of n numbers: O(n log n)
- **Shortest path** in a graph: O(n^2) or better
- **Multiplication** of two n-digit numbers: O(n^2) or better
- **Is this number prime?**: O(n^6) (AKS algorithm)

## NP: Problems You Can CHECK Quickly

**NP** (Nondeterministic Polynomial time) is the class of problems
where, given a proposed solution, you can VERIFY it's correct in
polynomial time.

Examples:
- **Subset Sum**: "Does some subset of {3, 7, 1, 8, 2} sum to 11?"
  - Hard to solve (try all 2^5 = 32 subsets?)
  - Easy to check: "{3, 8} sums to 11? Let me add: 3 + 8 = 11. Yes!"

- **Sudoku**: Hard to solve, but easy to check if a filled grid is valid.

- **Factoring** (decision version): "Does 15 have a factor between 2 and 7?"
  - Easy to check: "Is 3 a factor? 15/3 = 5. Yes!"

## The Question: P = NP or P != NP?

Every problem in P is also in NP (if you can solve it, you can
certainly check solutions). The question is: does NP contain
problems that are NOT in P?

```
         ┌────────────────────┐
         │        NP          │
         │  ┌──────────────┐  │
         │  │      P       │  │
         │  │   (easy to   │  │
         │  │    solve)    │  │
         │  └──────────────┘  │
         │                    │
         │  Subset Sum?       │
         │  SAT? Traveling    │
         │  Salesman?         │
         └────────────────────┘
```

- **If P = NP**: Everything easy to check is also easy to solve.
  Cryptography breaks. Optimization becomes trivial. Mathematics
  becomes (in some sense) mechanical.

- **If P != NP**: Some problems are fundamentally harder to solve
  than to check. This is what almost everyone believes.

## NP-Completeness: The Hardest Problems in NP

In 1971, Stephen Cook proved that **SAT** (Boolean satisfiability)
is "NP-complete" — it's the hardest problem in NP. If you can solve
SAT efficiently, you can solve EVERYTHING in NP efficiently.

Soon after, Richard Karp showed that many other problems are also
NP-complete, including:
- **Subset Sum**
- **Traveling Salesman**
- **Graph Coloring**
- **Knapsack**

These problems are all "equivalent" — solving any one of them
efficiently would solve all of them.

## Why Subset Sum?

We focus on Subset Sum because:

1. **It's simple to state**: Does some subset of integers sum to a target?
2. **It connects to number theory**: Subset Sum is about adding integers,
   which connects to additive combinatorics — a deep mathematical field.
3. **It has a rich structure**: The "density" of an instance controls its
   difficulty, creating a phase transition that mirrors physics.
4. **The adversary game is intuitive**: Think of it as a bet — the dealer
   picks numbers, you guess if a subset sums to the target.

## The Adversary Game

Imagine Subset Sum as a game:

1. **The Dealer** (adversary) picks a set of integers and a target.
2. **You** must say YES (some subset sums to the target) or NO.
3. If you're right, you win. If wrong, you lose.

**The P vs NP question becomes**: Is there a strategy that lets you
ALWAYS win in polynomial time?

The dealer's goal is to construct instances that defeat ANY strategy
you might use. Our project studies what the dealer's optimal strategy
looks like.

## What Our Project Proves

### The Davenport constant constrains the dealer

For the MODULAR version (working mod n instead of over integers):

- **With n or more numbers**: The dealer CANNOT avoid a zero-sum subset.
  You always win by saying YES. (Our theorem: `davenport_upper`)

- **With n-1 numbers**: The dealer CAN avoid zero-sum, but ONLY by
  using all copies of one element. (Our theorem: `inverse_davenport`)

### The density phase transition

For STANDARD Subset Sum (over integers):

- **High density** (many numbers, small values): Pigeonhole forces
  collisions. You win by looking for matching sums. (Our theorem:
  `pigeonhole_collision`)

- **Low density** (few numbers, huge values): Lattice algorithms win.

- **Critical density** (balanced): Neither method works. THIS is where
  P vs NP lives.

## The Gap: Why We Haven't Proved P != NP (Yet)

Our structural results are about the MODULAR problem (Z/nZ), which
turns out to be efficiently decidable at the Davenport threshold.
The STANDARD problem (over Z) is harder.

The gap between modular and standard Subset Sum is where the
million-dollar answer hides. Our project:

1. Identifies this gap precisely
2. Documents four research directions to bridge it
3. Provides a complete, machine-checked foundation to build on

## The Three Barriers

Three famous results explain why proving P != NP is so hard:

### 1. Relativization (Baker-Gill-Solovay, 1975)
Simple diagonalization arguments (the most common proof technique
in computability theory) can't work, because there exist "oracles"
that make P = NP true and others that make it false.

### 2. Natural Proofs (Razborov-Rudich, 1997)
Combinatorial arguments that apply to RANDOM functions can't work
(if cryptography is possible), because such arguments can't
distinguish truly random functions from pseudorandom ones computed
by small circuits.

### 3. Algebrization (Aaronson-Wigderson, 2009)
Even arithmetic/algebraic techniques (like the ones that proved
IP = PSPACE) can't resolve P vs NP.

Any proof of P != NP must somehow evade ALL THREE barriers.

## Where Could the Answer Come From?

Our field survey ([docs/06-FIELD-SURVEY.md](06-FIELD-SURVEY.md))
identifies several promising directions:

1. **Sum-product phenomena**: The incompatibility of addition and
   multiplication might constrain computation.

2. **Uncommon graphs**: Certain Ramsey-theoretic properties that
   FAIL for random objects might evade the natural proofs barrier.

3. **Proof complexity**: Lower bounds on proof lengths connect to
   circuit lower bounds.

4. **The polynomial method**: Already gives exponential bounds in
   restricted settings.

## Further Reading

- [P vs NP on Clay Mathematics Institute](https://www.claymath.org/millennium-problems/p-vs-np-problem)
- Scott Aaronson, "P vs NP" survey (2016)
- Sipser, "Introduction to the Theory of Computation" (textbook)
- Arora and Barak, "Computational Complexity: A Modern Approach" (textbook)
- Lance Fortnow, "The Golden Ticket: P, NP, and the Search for the Impossible" (popular book)
