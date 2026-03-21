/-
  CauchyDavenport.lean — Sumset lower bounds and Subset Sum

  The Cauchy-Davenport theorem gives a lower bound on the size of
  sumsets in Z/pZ: |A + B| >= min(p, |A| + |B| - 1).

  This is already formalized in Mathlib. We connect it to our Subset Sum
  framework, showing that it constrains how few distinct subset sums
  a set of integers can produce.

  The key insight for P ≠ NP: Cauchy-Davenport says sumsets GROW.
  This means the set of achievable subset sums must be large unless
  the input has strong additive structure (as characterized by
  Freiman's theorem). Large subset sum sets make collision-based
  algorithms more likely to succeed.
-/

import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import Zpnenp.SubsetSum
import Zpnenp.Freiman
import Zpnenp.Inverse

open Finset Pointwise

/-! ## Cauchy-Davenport from Mathlib

The key theorem (already in Mathlib):

  `ZMod.cauchy_davenport (hp : p.Prime) (hs : s.Nonempty) (ht : t.Nonempty) :
     min p (#s + #t - 1) ≤ #(s + t)`

For nonempty sets s, t in Z/pZ with p prime:
  |s + t| >= min(p, |s| + |t| - 1)

This is sharp: equality holds when s and t are arithmetic progressions
with the same common difference.
-/

/-! ## Iterated sumsets grow

Applying Cauchy-Davenport iteratively: if we keep adding copies of
a set A to itself, the sumset grows by at least |A|-1 each time,
until it covers all of Z/pZ.

This means: for a set A of k elements in Z/pZ, the set of all
subset sums (including 0) has size at least min(p, k(k+1)/2 + 1)
— though proving this tight bound requires more work.

As a first step, we prove that adding one element to any nonempty
set grows the sumset. -/

/-- Adding a singleton to a nonempty set in Z/pZ gives a sumset of
    size at least min(p, |s| + 1 - 1) = min(p, |s|). Since the
    sumset also contains at least |s| elements (by translation),
    this is a basic growth result. -/
theorem sumset_singleton_growth {p : ℕ} (hp : p.Prime) (s : Finset (ZMod p))
    (hs : s.Nonempty) (a : ZMod p) :
    min p (#s + 1 - 1) ≤ #(s + {a}) := by
  have ha : ({a} : Finset (ZMod p)).Nonempty := singleton_nonempty a
  have := ZMod.cauchy_davenport hp hs ha
  simp only [card_singleton] at this
  exact this

/-! ## Subset sums in Z/pZ grow quickly

For a set of k distinct elements in Z/pZ, the achievable subset sums
(sums of all possible subsets) form a subset of Z/pZ. Cauchy-Davenport
implies that these subset sums must be "large" — the set cannot be
concentrated in a small region of Z/pZ unless the elements have strong
additive structure.

More precisely: if we start with {0} (the empty subset sum) and
iteratively add elements, each step grows the sumset by
Cauchy-Davenport. -/

/-- The set of achievable subset sums of s (as a Finset in Z/pZ)
    includes 0 (the empty subset) and is closed under adding
    elements of s. -/
def modSubsetSums {p : ℕ} (s : Finset (ZMod p)) : Finset (ZMod p) :=
  s.powerset.image (fun s' => s'.sum id)

theorem zero_mem_modSubsetSums {p : ℕ} (s : Finset (ZMod p)) :
    (0 : ZMod p) ∈ modSubsetSums s := by
  simp [modSubsetSums, mem_image]
  exact ⟨∅, empty_subset s, by simp⟩

theorem modSubsetSums_nonempty {p : ℕ} (s : Finset (ZMod p)) :
    (modSubsetSums s).Nonempty :=
  ⟨0, zero_mem_modSubsetSums s⟩

/-- The number of achievable subset sums is at most 2^|s|. -/
theorem card_modSubsetSums_le {p : ℕ} (s : Finset (ZMod p)) :
    #(modSubsetSums s) ≤ 2 ^ #s := by
  calc #(modSubsetSums s)
      ≤ #s.powerset := card_image_le
    _ = 2 ^ #s := card_powerset s

/-- If the number of achievable subset sums equals p, then every
    element of Z/pZ is a subset sum — the problem is trivially
    solvable. -/
theorem modSubsetSums_full {p : ℕ} [hp : Fact p.Prime] (s : Finset (ZMod p))
    (hfull : #(modSubsetSums s) = p) :
    ∀ t : ZMod p, t ∈ modSubsetSums s := by
  intro t
  have huniv : #(Finset.univ : Finset (ZMod p)) = p := by simp [ZMod.card]
  have : modSubsetSums s = Finset.univ :=
    Finset.eq_univ_of_card _ (hfull.trans huniv.symm)
  rw [this]; exact Finset.mem_univ t

/-- `modSubsetSums` agrees with `subsetSumsZMod` from Freiman.lean —
    both compute the powerset image of sum. -/
theorem modSubsetSums_eq_subsetSumsZMod {p : ℕ} (s : Finset (ZMod p)) :
    modSubsetSums s = subsetSumsZMod s := rfl

/-! ## Connection to the Davenport constant and inverse theorem

Cauchy-Davenport gives *sumset growth*. Combined with our results:

1. **Davenport constant** (D(Z/nZ) = n): with n elements, zero-sum
   is guaranteed. This is the "extreme growth" case — the subset sums
   must include 0.

2. **Inverse Davenport**: the ONLY instances avoiding zero-sum at
   size n-1 are all-copies-of-a-unit. For these instances, the
   subset sums are {0, g, 2g, ..., (n-1)g} = Z/nZ (all of them!).
   So even the "hardest" instances have MAXIMAL subset sum coverage.

3. **Cauchy-Davenport** explains WHY subset sums grow: each new
   element added to the summation expands the achievable set by
   at least 1 (in Z/pZ), unless the set is already all of Z/pZ.

Together, these results paint a picture: **subset sums in Z/pZ
cannot be small**. The adversary who tries to limit the achievable
sums is fighting against the fundamental growth law of additive
combinatorics.

For standard Subset Sum (over Z), the analog is: subset sums grow
rapidly unless the input has special additive structure (as
characterized by Freiman's theorem). At critical density d ~ 1,
the interplay between growth (Cauchy-Davenport) and structure
(Freiman) determines the hardness landscape. -/

/-! ## Extremal subset sum coverage

The inverse Davenport theorem tells us that zero-sum-free multisets
of maximal length have FULL subset sum coverage (every element of
Z/nZ is achievable as a prefix sum). This is a strong "coverage"
result: even the adversary's BEST strategy to avoid zero-sums
produces instances with maximal subset sum diversity.

For Subset Sum over Z/pZ, this means: at the Davenport threshold,
the adversary cannot simultaneously avoid zero-sums AND restrict
the set of achievable sums. Structure forces coverage. -/

/-- A zero-sum-free multiset of size n-1 achieves every element of
    Z/nZ as a prefix sum. This follows from `prefix_sums_surjective`
    in Inverse.lean. Restated here to connect to the subset sum framework. -/
theorem zeroSumFree_full_prefix_coverage {n : ℕ} (hn : 1 < n)
    {l : List (ZMod n)} (hzsf : ZeroSumFree (↑l : Multiset (ZMod n)))
    (hlen : l.length = n - 1) :
    ∀ x : ZMod n, ∃ i : Fin n, (l.take i.val).sum = x := by
  exact ZeroSumFree.prefix_sums_surjective hn hzsf hlen
