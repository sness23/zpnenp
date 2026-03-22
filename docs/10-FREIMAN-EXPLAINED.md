# Freiman's Theorem: A Simplified Explanation

## The One-Sentence Version

**If a set of numbers doesn't grow much when you add it to itself,
the set must have a simple, pattern-like structure.**

## The Setup

Take a set A of numbers in Z/pZ (integers mod a prime p).
The **sumset** A + A is the set of all pairwise sums:

```
A + A = { a + b : a in A, b in A }
```

How big can A + A be?

- **Maximum**: |A + A| can be as large as min(p, |A|^2) — every
  pair gives a different sum.
- **Minimum**: |A + A| >= min(p, 2|A| - 1) — this is the
  **Cauchy-Davenport theorem** (proved in Mathlib).

The **doubling constant** K measures how much A grows:

```
K = |A + A| / |A|
```

- K = 1: A doesn't grow at all. Only possible if A is trivial
  (size 0 or 1) or A = all of Z/pZ.
- K close to 1: A grows very little — it must be structured.
- K close to |A|: A grows maximally — it's "spread out."

## What Freiman Says

**Theorem** (Freiman, 1966, simplified for Z/pZ):
If K is small (|A + A| <= K|A|) and A is not too large
(|A| <= p/K), then A is contained in an **arithmetic progression**:

```
A ⊆ { a, a+d, a+2d, ..., a+(L-1)d }
```

where L <= K^2 |A|.

In other words: **small doubling forces arithmetic structure.**

## Why This Matters for P != NP

For the Subset Sum problem, the set of achievable sums depends on
the **structure** of the input set A. Freiman's theorem creates a
**dichotomy**:

1. **Growing case** (K large): |A + A| >> |A|, so there are many
   achievable sums. The problem is "easy" because random collisions
   find solutions.

2. **Structured case** (K small): A sits inside an AP. This rigid
   structure can potentially be exploited by specialized algorithms
   (lattice reduction in the AP's coordinates).

Either way, the adversary is constrained. This is formalized in
`Complexity.lean` as `structure_vs_computation_dichotomy`.

## The Proof Idea (for Z/pZ)

### Key Insight: Z/pZ Has No Subgroups

For a prime p, Z/pZ has **no proper nontrivial subgroups**. The only
subgroups are {0} and all of Z/pZ. This makes the Z/pZ case simpler
(but also different) from the general case.

### Step 1: Ruzsa Covering

**Ruzsa's Covering Lemma** (in Mathlib as `Finset.ruzsa_covering_mul`):
If |A + A| <= K|A|, there exists a small set F ⊆ A with |F| <= K such
that A is covered by F + (A - A):

```
A ⊆ F + (A - A)    with |F| <= K
```

This says: A can be covered by K "translates" of the difference set A - A.

### Step 2: Plünnecke-Ruzsa

The **Plünnecke-Ruzsa inequality** (in Mathlib) bounds the difference set:

```
|A - A| <= K^2 |A|
```

So A - A has bounded size.

### Step 3: AP Structure in Z/pZ

In Z/pZ (p prime), every set generates an arithmetic progression
structure. The difference set A - A = {a - b : a, b in A} determines
the "spread" of A. When |A - A| is small relative to p, A must be
concentrated in a short arithmetic progression.

The formal argument uses:
- Cauchy-Davenport for growth bounds
- The fact that Z/pZ is a field (every nonzero element is invertible)
- The covering from Step 1 to localize A

### Step 4: Combine

From Steps 1-3: A is covered by K translates of a set of size
<= K^2 |A|. In Z/pZ, this union of translates can be embedded in an
AP of length <= K^2 |A| (using the field structure).

## Available Mathlib Infrastructure

| Component | Mathlib Location | Status |
|-----------|-----------------|--------|
| Cauchy-Davenport | `ZMod.cauchy_davenport` | Available |
| Plünnecke-Ruzsa | `PluenneckeRuzsa.lean` | Available |
| Ruzsa Covering | `RuzsaCovering.lean` | Available |
| Doubling Constants | `DoublingConst.lean` | Available |
| Very Small Doubling | `VerySmallDoubling.lean` | Available |
| Freiman Homomorphisms | `FreimanHom.lean` | Available |
| **Freiman's Theorem** | — | **Not in Mathlib** |

The theorem itself is NOT in Mathlib. All the ingredients are there,
but assembling them into the full proof is the remaining work.

## Remaining Sorry

Our `freiman_ZMod` in `Freiman.lean` states the theorem and is used
by `small_doubling_implies_AP_structure` in `Complexity.lean`. Proving
it would close one of the two remaining sorries in the project.

## References

- Freiman, G.A. (1966). *Foundations of a Structural Theory of Set Addition*
- Ruzsa, I.Z. (1999). "An analog of Freiman's theorem in groups"
- Green, B. and Ruzsa, I.Z. (2007). "Freiman's theorem in an arbitrary abelian group"
- Tao, T. and Vu, V. (2006). *Additive Combinatorics*, Chapter 5
