# Tutorial: Reading the Lean 4 Proofs

This tutorial helps you read the formalized proofs in this project,
even if you've never used Lean before.

## What is Lean 4?

Lean 4 is a **theorem prover** — a programming language where you
write mathematical proofs that a computer checks for correctness.
If the code compiles, the proof is valid. No bugs, no hand-waving,
no "the reader can easily verify."

**Mathlib** is a library of 100,000+ formalized mathematics theorems
in Lean 4, maintained by the community.

## The Basic Structure of a Lean File

```lean
-- This is a comment

/-- This is a documentation comment (docstring) -/

-- Import other files
import Mathlib.Data.ZMod.Basic

-- Open a namespace (so we don't have to write Multiset.card etc.)
open Multiset

-- Define something
def MyDefinition (x : Nat) : Nat := x + 1

-- State and prove a theorem
theorem my_theorem (n : Nat) (h : 0 < n) : n + 1 > 0 := by
  omega
```

## Reading Definitions

Our core definition:

```lean
def SubsetSum (s : Finset Z) (t : Z) : Prop :=
  exists s' in s.powerset, s'.sum id = t
```

Reading this:
- `def SubsetSum` — we're defining something called SubsetSum
- `(s : Finset Z)` — s is a finite set of integers
- `(t : Z)` — t is an integer (the target)
- `: Prop` — the result is a proposition (true/false statement)
- `exists s' in s.powerset` — there exists a subset s' of s
- `s'.sum id = t` — whose sum equals t

## Reading Proofs

Lean proofs use **tactics** — commands that transform the goal
step by step until it's solved. Here's a simple example:

```lean
theorem subsetSum_zero (s : Finset Z) : SubsetSum s 0 := by
  exact ⟨empty, mem_powerset.mpr (empty_subset s), sum_empty⟩
```

Reading this:
- `theorem subsetSum_zero` — we're proving SubsetSum s 0
- `by` — start tactic mode
- `exact ⟨..⟩` — provide the witness directly
  - The witness is the empty set
  - `mem_powerset.mpr (empty_subset s)` — empty set is in the powerset
  - `sum_empty` — sum of empty set is 0

## Common Tactics

| Tactic | What it does |
|--------|-------------|
| `intro h` | Introduce a hypothesis |
| `exact e` | Provide the exact proof term |
| `by_contra h` | Assume the negation for contradiction |
| `rw [lemma]` | Rewrite using an equation |
| `simp` | Simplify using known lemmas |
| `omega` | Solve linear arithmetic goals |
| `calc` | Chain of equalities/inequalities |
| `obtain ⟨x, hx⟩ := h` | Destructure an existential |
| `rcases` | Pattern match on a hypothesis |
| `apply f` | Apply a function/lemma |
| `sorry` | Skip a proof (NOT allowed in final code) |

## Reading the Davenport Upper Bound

Here's the key proof, annotated:

```lean
theorem davenport_upper (n : Nat) (hn : 0 < n)
    (s : Multiset (ZMod n)) (hs : s.card = n) :
    exists t <= s, t != 0 /\ t.sum = 0 := by
```

This says: given n > 0 and a multiset s of n elements in Z/nZ,
there exists a nonempty submultiset t of s summing to 0.

```lean
  haveI : NeZero n := ...  -- n is nonzero (needed for ZMod)
  set l := s.toList        -- convert multiset to a list
```

Now define prefix sums:

```lean
  let ps : Fin (n + 1) -> ZMod n := fun i => (l.take i.val).sum
```

This maps index i to the sum of the first i elements. There are
n+1 such values (i = 0, 1, ..., n) living in Z/nZ (which has n
elements).

```lean
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (n + 1)) := ...
  obtain ⟨a, b, hab, hps⟩ := Fintype.exists_ne_map_eq_of_card_lt ps hcard
```

Pigeonhole! Since n+1 > n, two prefix sums must be equal.
We get indices a != b with ps(a) = ps(b).

The rest extracts the contiguous slice between a and b,
shows it sums to 0, and shows it's a submultiset of s.

## Reading the Inverse Theorem

The adjacent swap argument:

```lean
theorem ZeroSumFree.all_eq ... {a b : ZMod n} (ha : a in s) (hb : b in s) :
    a = b := by
  by_contra hab    -- assume a != b
```

We construct two lists `[a, b, ...rest]` and `[b, a, ...rest]`
that both represent the same multiset s:

```lean
  set l1 : List (ZMod n) := a :: b :: rl
  set l2 : List (ZMod n) := b :: a :: rl
```

Both give bijective prefix sum functions:

```lean
  have hinj1 : Function.Injective ps1 := ...
  have hinj2 : Function.Injective ps2 := ...
```

They agree everywhere except position 1:

```lean
  have hps_agree : forall i, i != 1 -> ps1 i = ps2 i := by
    -- position 0: both are 0
    -- position >= 2: a+b+... = b+a+... by commutativity
```

By the general lemma (two bijections agreeing on n-1 inputs
agree everywhere):

```lean
  have h1 := injective_agree_of_agree_except hinj1 hinj2 ... hps_agree
  -- h1 says: ps1(1) = ps2(1), i.e., a = b
  exact hab h1  -- contradiction!
```

## Key Types

| Type | What it is |
|------|-----------|
| `Nat` (or `N`) | Natural numbers 0, 1, 2, ... |
| `Int` (or `Z`) | Integers ..., -1, 0, 1, ... |
| `ZMod n` | Integers mod n (the group Z/nZ) |
| `Finset A` | Finite set of elements of type A |
| `Multiset A` | Finite multiset (bag) — like a set but with repetition |
| `List A` | Ordered list |
| `Fin n` | {0, 1, ..., n-1} |
| `Prop` | A proposition (something true or false) |
| `Bool` | true or false (computational) |

## Building the Project

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone <repo-url>
cd zpnenp
lake build
```

If it compiles with no errors and no `sorry`, every theorem is valid.

## Further Reading

- [Lean 4 documentation](https://lean-lang.org/documentation/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4) (interactive Lean tutorial)
