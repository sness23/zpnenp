# Tutorial: Zero-Sum Theory for Beginners

This tutorial explains the mathematics behind the zpnenp project,
assuming no prior knowledge of additive combinatorics. We'll build
up from simple examples to the key theorems.

## What is a "Zero-Sum" Problem?

Imagine you have a bag of numbers. You want to know: can you pick
some of them (at least one) so they add up to zero?

**Example 1**: Bag = {3, -1, -2}
- Pick {3, -1, -2}: sum = 3 + (-1) + (-2) = 0. YES!

**Example 2**: Bag = {1, 2, 4}
- {1} = 1, {2} = 2, {4} = 4, {1,2} = 3, {1,4} = 5, {2,4} = 6, {1,2,4} = 7
- None sum to zero. NO.

This is essentially the **Subset Sum** problem (with target 0),
one of the most fundamental problems in computer science.

## Modular Arithmetic: Clock Math

Now imagine we're working "mod n" — on a clock with n hours.
In **Z/nZ** (read "Z mod n Z"), numbers wrap around:
- In Z/6Z: 4 + 3 = 7 = 1 (mod 6)
- In Z/5Z: 3 + 4 = 7 = 2 (mod 5)

Zero-sum mod n means: can you pick some numbers that add up to
a multiple of n?

**Example**: In Z/5Z with bag {2, 3, 4}:
- {2, 3} = 5 = 0 (mod 5). YES!

## The Pigeonhole Principle

The **pigeonhole principle** says: if you have n+1 pigeons and
n holes, at least two pigeons share a hole.

This simple idea is surprisingly powerful. It's the key to
understanding WHEN zero-sum subsets must exist.

## The Davenport Constant: When Must Zero-Sum Exist?

**Question**: How many numbers do you need from Z/nZ before a
zero-sum subset is GUARANTEED to exist — no matter what numbers
the adversary chooses?

**Answer**: Exactly n. This number is called the **Davenport
constant** D(Z/nZ).

### Why n is enough (upper bound)

Take any n numbers a_1, ..., a_n from Z/nZ. Compute the
**prefix sums**:

```
s_0 = 0
s_1 = a_1
s_2 = a_1 + a_2
s_3 = a_1 + a_2 + a_3
...
s_n = a_1 + a_2 + ... + a_n
```

That's n+1 values (s_0 through s_n), all living in Z/nZ which
has only n elements. By **pigeonhole**, two must be equal:
s_i = s_j for some i < j.

Then: a_{i+1} + a_{i+2} + ... + a_j = s_j - s_i = 0.

That's a nonempty subset summing to zero!

### Why n-1 is not enough (lower bound)

Take the bag {1, 1, 1, ..., 1} with n-1 copies of 1.

Any nonempty subset has k copies of 1 (for 1 <= k <= n-1),
summing to k. Since 1 <= k <= n-1, we have k != 0 mod n.

So no nonempty subset sums to zero. The adversary wins with n-1!

### Together: D(Z/nZ) = n

- n elements: zero-sum guaranteed (pigeonhole)
- n-1 elements: adversary can avoid zero-sum (all-ones bag)

## The Inverse Theorem: What Do "Hard" Instances Look Like?

The Davenport constant tells us the THRESHOLD. The **inverse
theorem** tells us what happens AT the threshold.

**Theorem**: The ONLY bags of n-1 elements in Z/nZ that avoid
zero-sum are bags where ALL elements are the same, and that
element is a "unit" (coprime to n).

In other words: the adversary's best strategy is to use ALL
copies of a single element. Any mixing of different elements
at size n-1 will create a zero-sum subset.

### Why this matters

This is a **structural rigidity** result. The adversary has
no freedom — the "hardest" instances are maximally structured.

- With n-1 copies of 1: zero-sum free (all subsets sum to 1, 2, ..., n-1)
- With n-1 copies of 2 (if gcd(2,n)=1): also zero-sum free
- With n-2 copies of 1 and 1 copy of 2: might have zero-sum!
- Any mixture: the structure forces a zero-sum to appear

### The proof idea: adjacent swap

Here's the elegant argument:

1. Take any ordering of the n-1 elements. The n prefix sums
   are all distinct (we proved this — if two were equal,
   there'd be a zero-sum). Since there are n prefix sums in
   Z/nZ (which has n elements), they hit EVERY element.

2. Now take two adjacent elements a and b in the ordering,
   and swap them. The new ordering has the SAME prefix sums
   except at one position.

3. Both orderings give permutations of Z/nZ as prefix sums.
   Two permutations that agree at n-1 out of n positions must
   agree at all n positions.

4. Therefore a = b. Since any two elements can be made adjacent,
   ALL elements are equal.

## The Erdos-Ginzburg-Ziv Theorem

**Theorem (EGZ, 1961)**: Among any 2n-1 integers, there exist
n whose sum is divisible by n.

This is a stronger result than the Davenport constant — it
guarantees not just any zero-sum subset, but one of SIZE exactly n.

The EGZ theorem is already formalized in Mathlib (by Yaël Dillies),
proved via the Chevalley-Warning theorem. Our project connects it
to Subset Sum definitions.

## From Modular to Integer: The Density Phase Transition

The modular zero-sum problem (over Z/nZ) is simpler than the
standard Subset Sum problem (over Z with a target). The connection
goes through **density**.

The **density** of a Subset Sum instance is:

```
d = (number of elements) / log_2(maximum weight)
```

This measures how many elements you have relative to the size
of the numbers.

### High density (d >> 1): EASY

Many elements, small numbers. By pigeonhole, two subsets must
have the same sum (there are 2^n subsets but only about n*M
possible sum values). The difference of these subsets gives
a zero-sum.

### Low density (d << 1): EASY (for a different reason)

Few elements, huge numbers. Lattice reduction algorithms (LLL)
can exploit the sparse structure to find solutions in polynomial
time.

### Critical density (d ~ 1): HARD

This is the "Goldilocks zone" where neither method works. This
is where computational hardness concentrates, and where a proof
of P != NP would need to operate.

## The Big Picture

```
STRUCTURAL THEORY          COMPUTATIONAL THEORY
(what must exist)          (what algorithms can find)

Zero-sum theory            Subset Sum algorithms
Davenport constant         Pigeonhole (high density)
Inverse theorem            Lattice reduction (low density)
EGZ theorem                ??? (critical density)
                                   |
                                   v
                           This gap is P vs NP
```

Our project formalizes the left column in Lean 4 and connects
it to the right column. The gap between them is the million-dollar
question.

## Next: The Barriers

Why hasn't anyone proved P != NP yet? There are three known
barriers that block most proof techniques. See
[docs/03-BARRIERS.md](03-BARRIERS.md) for the full story.
