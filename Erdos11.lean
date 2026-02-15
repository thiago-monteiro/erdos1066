/-
Copyright (c) 2024 Erdos11 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos11 Project
-/
import Mathlib

namespace Erdos11

/--
`Represents n` means `n` is the sum of a positive squarefree number and a power of `2`.
-/
def Represents (n : Nat) : Prop :=
  ∃ m k : Nat, m > 0 ∧ Squarefree m ∧ n = m + 2 ^ k

/--
Formal statement of the Erdős #11 conjecture:
all sufficiently large odd numbers satisfy `Represents`.
-/
def Erdos11Conjecture : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → Odd n → Represents n

/-- Candidate exponents bounded by `log_2 n` and satisfying `2^k < n`. -/
def candidateExponents (n : Nat) : Finset Nat :=
  (Finset.range (Nat.log 2 n + 1)).filter (fun k => 2 ^ k < n)

/--
Boolean predicate for a good exponent:
`2^k < n` and `n - 2^k` is squarefree.
-/
def goodExponent (n k : Nat) : Bool :=
  decide (2 ^ k < n ∧ Squarefree (n - 2 ^ k))

/--
Linear search up to a bound `b`.
Returns the first exponent that satisfies `goodExponent`.
-/
def searchExponent (n : Nat) : Nat → Option Nat
  | 0 => if goodExponent n 0 then some 0 else none
  | b + 1 =>
      match searchExponent n b with
      | some k => some k
      | none => if goodExponent n (b + 1) then some (b + 1) else none

/-- Main executable exponent finder, searched up to `Nat.log 2 n`. -/
def findExponent? (n : Nat) : Option Nat :=
  searchExponent n (Nat.log 2 n)

lemma searchExponent_sound {n b k} (h : searchExponent n b = some k) :
    2 ^ k < n ∧ Squarefree (n - 2 ^ k) := by
  induction b generalizing k with
  | zero =>
      simp [searchExponent, goodExponent] at h
      rcases h with ⟨hgood, hk⟩
      subst hk
      simpa using hgood
  | succ b ih =>
      dsimp [searchExponent] at h
      cases hs : searchExponent n b with
      | none =>
          simp [hs, goodExponent] at h
          rcases h with ⟨hgood, hk⟩
          subst hk
          simpa using hgood
      | some k' =>
          simp [hs] at h
          subst h
          exact ih hs

lemma findExponent_sound {n k} (h : findExponent? n = some k) :
    2 ^ k < n ∧ Squarefree (n - 2 ^ k) := by
  exact searchExponent_sound (b := Nat.log 2 n) h

lemma represents_of_exponent {n k : Nat} (hk : 2 ^ k < n) (hsq : Squarefree (n - 2 ^ k)) :
    Represents n := by
  refine ⟨n - 2 ^ k, k, Nat.sub_pos_of_lt hk, hsq, ?_⟩
  exact (Nat.sub_add_cancel (le_of_lt hk)).symm

lemma represents_of_findExponent_isSome {n : Nat} (h : (findExponent? n).isSome = true) :
    Represents n := by
  have hs : (findExponent? n).isSome := by simpa using h
  rcases Option.isSome_iff_exists.mp hs with ⟨k, hk⟩
  have hgood := findExponent_sound hk
  exact represents_of_exponent hgood.1 hgood.2

/--
Certified solver returning `(m, k)` when successful, with
`m = n - 2^k`.
-/
def solver? (n : Nat) : Option (Nat × Nat) :=
  (findExponent? n).map (fun k => (n - 2 ^ k, k))

lemma solver_sound {n m k : Nat} (h : solver? n = some (m, k)) :
    m > 0 ∧ Squarefree m ∧ n = m + 2 ^ k := by
  unfold solver? at h
  cases hfind : findExponent? n with
  | none =>
      simp [hfind] at h
  | some k0 =>
      simp [hfind] at h
      rcases h with ⟨hm, hk⟩
      subst hm hk
      have hgood := findExponent_sound hfind
      exact ⟨Nat.sub_pos_of_lt hgood.1, hgood.2,
        (Nat.sub_add_cancel (le_of_lt hgood.1)).symm⟩

lemma represents_of_solver_eq_some {n m k : Nat} (h : solver? n = some (m, k)) :
    Represents n := by
  rcases solver_sound h with ⟨hm, hsq, hsum⟩
  exact ⟨m, k, hm, hsq, hsum⟩

/-- Odd candidates in `[3, B]`, as an executable list. -/
def oddCandidates (B : Nat) : List Nat :=
  (List.range (B + 1)).filter (fun n => decide (3 <= n ∧ Odd n))

/--
Computable finite check:
every odd candidate up to `B` has a successful exponent search.
-/
def solverSucceedsUpTo (B : Nat) : Bool :=
  (oddCandidates B).all fun n => (findExponent? n).isSome

/-- Mathematical finite verification statement up to bound `B`. -/
def VerifiedUpTo (B : Nat) : Prop :=
  ∀ n, 3 <= n -> n <= B -> Odd n -> Represents n

lemma solverSucceedsUpTo_spec {B : Nat} (h : solverSucceedsUpTo B = true) :
    ∀ n, n ∈ oddCandidates B → (findExponent? n).isSome = true := by
  unfold solverSucceedsUpTo at h
  simpa using h

lemma mem_oddCandidates_of_bounds {B n : Nat}
    (h3 : 3 <= n) (hB : n <= B) (hodd : Odd n) :
    n ∈ oddCandidates B := by
  unfold oddCandidates
  refine List.mem_filter.mpr ?_
  refine ⟨List.mem_range.mpr (Nat.lt_succ_of_le hB), ?_⟩
  have hprop : 3 <= n ∧ Odd n := ⟨h3, hodd⟩
  simpa [Bool.decide_eq_true] using hprop

lemma verifiedUpTo_of_solverSucceedsUpTo (B : Nat) (h : solverSucceedsUpTo B = true) :
    VerifiedUpTo B := by
  intro n h3 hB hodd
  exact represents_of_findExponent_isSome
    (solverSucceedsUpTo_spec h n (mem_oddCandidates_of_bounds h3 hB hodd))

/--
Executable finite verification result:
the solver is certified for every odd `n` with `3 <= n <= 2^20`.
-/
lemma solverSucceedsUpTo_2pow20 : solverSucceedsUpTo (2 ^ 20) = true := by
  native_decide

/--
Formal finite theorem:
for every odd `n` with `3 <= n <= 2^20`, `Represents n` holds.
-/
lemma verifiedUpTo_2pow20 : VerifiedUpTo (2 ^ 20) :=
  verifiedUpTo_of_solverSucceedsUpTo (2 ^ 20) solverSucceedsUpTo_2pow20

namespace AsymptoticGraph

/-- D1: logarithmic scale parameter. -/
def L (n : Nat) : Nat := Nat.log 2 n

/-- D2: exponent window. -/
def K (n : Nat) : Finset Nat := candidateExponents n

/-- D3: translated value `n - 2^k`. -/
def M (n k : Nat) : Nat := n - 2 ^ k

/-- D4: clean set after removing small prime-square divisibility. -/
noncomputable def A (n z : Nat) : Finset Nat := by
  classical
  exact (K n).filter (fun k =>
    forall p : Nat, Nat.Prime p -> p <= z -> Not ((M n k) % (p ^ 2) = 0))

/-- D5: bad set created by large prime-square divisibility. -/
noncomputable def B (n z : Nat) : Finset Nat := by
  classical
  exact (K n).filter (fun k =>
    exists p : Nat, Nat.Prime p /\ z < p /\ (M n k) % (p ^ 2) = 0)

/-- Small-prime bad set: divisible by `p^2` for some prime `p ≤ z`. -/
noncomputable def smallPrimeBad (n z : Nat) : Finset Nat := by
  classical
  exact (K n).filter (fun k =>
    exists p : Nat, Nat.Prime p /\ p <= z /\ (M n k) % (p ^ 2) = 0)

/-- L1: local counting function for a fixed prime `p`. -/
def Np (n p : Nat) : Nat :=
  ((K n).filter (fun k => (M n k) % (p ^ 2) = 0)).card

/-- Cutoff used in the split between small and large primes. -/
def z (n : Nat) : Nat := L n / 2

lemma A_subset_K (n z0 : Nat) : A n z0 ⊆ K n := by
  classical
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma B_subset_K (n z0 : Nat) : B n z0 ⊆ K n := by
  classical
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma smallPrimeBad_subset_K (n z0 : Nat) : smallPrimeBad n z0 ⊆ K n := by
  classical
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma card_A_le_card_K (n z0 : Nat) : (A n z0).card <= (K n).card :=
  Finset.card_le_card (A_subset_K n z0)

lemma card_B_le_card_K (n z0 : Nat) : (B n z0).card <= (K n).card :=
  Finset.card_le_card (B_subset_K n z0)

lemma A_eq_K_sdiff_smallPrimeBad (n z0 : Nat) :
    A n z0 = K n \ smallPrimeBad n z0 := by
  classical
  ext k
  constructor
  · intro hkA
    have hkK : k ∈ K n := (Finset.mem_filter.mp hkA).1
    have hsmall :
        forall p : Nat, Nat.Prime p -> p <= z0 -> Not ((M n k) % (p ^ 2) = 0) :=
      (Finset.mem_filter.mp hkA).2
    refine Finset.mem_sdiff.mpr ?_
    refine ⟨hkK, ?_⟩
    intro hkBad
    rcases (Finset.mem_filter.mp hkBad).2 with ⟨p, hp, hpz, hmod0⟩
    exact hsmall p hp hpz hmod0
  · intro hkDiff
    rcases Finset.mem_sdiff.mp hkDiff with ⟨hkK, hkNotBad⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨hkK, ?_⟩
    intro p hp hpz hmod0
    apply hkNotBad
    refine Finset.mem_filter.mpr ?_
    exact ⟨hkK, ⟨p, hp, hpz, hmod0⟩⟩

lemma card_A_eq_card_K_sub_smallPrimeBad (n z0 : Nat) :
    (A n z0).card = (K n).card - (smallPrimeBad n z0).card := by
  classical
  calc
    (A n z0).card = (K n \ smallPrimeBad n z0).card := by
      simp [A_eq_K_sdiff_smallPrimeBad n z0]
    _ = (K n).card - (smallPrimeBad n z0).card := by
      exact Finset.card_sdiff_of_subset (smallPrimeBad_subset_K n z0)

/-- C1: membership in `K n` gives `2^k < n`. -/
lemma C1 {n k : Nat} (hk : k ∈ K n) : 2 ^ k < n := by
  exact (Finset.mem_filter.mp hk).2

/-- C2: outside both bad mechanisms implies squarefree. -/
lemma C2 {n z k : Nat} (hkA : k ∈ A n z) (hkB : k ∉ B n z) :
    Squarefree (M n k) := by
  classical
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hkK : k ∈ K n := (Finset.mem_filter.mp hkA).1
  have hsmall :
      forall q : Nat, Nat.Prime q -> q <= z -> Not ((M n k) % (q ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hmod0 : (M n k) % (p ^ 2) = 0 := Nat.mod_eq_zero_of_dvd (by
    simpa [pow_two] using hpp)
  by_cases hple : p <= z
  · exact hsmall p hp hple hmod0
  · have hpgt : z < p := lt_of_not_ge hple
    have hmemB : k ∈ B n z := by
      unfold B
      classical
      exact Finset.mem_filter.mpr
        ⟨hkK, ⟨p, hp, hpgt, hmod0⟩⟩
    exact hkB hmemB

/-- C3: basic cardinal inequality for survivors. -/
lemma C3 (n z : Nat) :
  (A n z).card - (B n z).card <= (A n z \ B n z).card := by
  simpa using (Finset.le_card_sdiff (B n z) (A n z))

/-- C4: positive net count gives a squarefree witness. -/
lemma C4 {n z : Nat} (hpos : (A n z).card - (B n z).card > 0) :
    exists k : Nat, k ∈ K n /\ Squarefree (M n k) := by
  classical
  have hsurv : 0 < (A n z \ B n z).card := lt_of_lt_of_le hpos (C3 n z)
  rcases Finset.card_pos.mp hsurv with ⟨k, hk⟩
  have hkA : k ∈ A n z := (Finset.mem_sdiff.mp hk).1
  have hkNotB : k ∉ B n z := (Finset.mem_sdiff.mp hk).2
  have hkK : k ∈ K n := (Finset.mem_filter.mp hkA).1
  exact ⟨k, hkK, C2 hkA hkNotB⟩

/-- C5: convert exponent witness into `Represents`. -/
lemma C5 {n k : Nat} (hk : 2 ^ k < n) (hsq : Squarefree (M n k)) :
    Represents n := by
  exact represents_of_exponent hk hsq

/-- Prime support used in small-prime counting. -/
noncomputable def smallPrimeSupport (n : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 2 (z n)).filter Nat.Prime

/-- Prime support used in large-prime counting. -/
noncomputable def largePrimeSupport (n : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc (z n + 1) n).filter Nat.Prime

/-- Size bound for the exponent window. -/
lemma card_K_le (n : Nat) : (K n).card <= L n + 1 := by
  unfold K L candidateExponents
  simpa using (Finset.card_filter_le (s := Finset.range (Nat.log 2 n + 1))
    (p := fun k => 2 ^ k < n))

/-- Trivial local counting bound by cardinality of the search window. -/
lemma Np_le_cardK (n p : Nat) : Np n p <= (K n).card := by
  unfold Np
  simpa using (Finset.card_filter_le (s := K n)
    (p := fun k => (M n k) % (p ^ 2) = 0))

/--
L2 (coarse form): local count is bounded by the window size.
The sharper periodic/order bound is a future strengthening.
-/
lemma L2_local_periodic (n p : Nat) (_hp : Nat.Prime p) :
  Np n p <= L n + 1 := by
  exact le_trans (Np_le_cardK n p) (card_K_le n)

/-- If `n ≡ 1 [MOD 4]` and `2 ≤ z n`, then `k = 0` is excluded from `A n (z n)`. -/
lemma zero_not_mem_A_of_mod4 {n : Nat}
    (hz2 : 2 <= z n) (hmod4 : n % 4 = 1) : 0 ∉ A n (z n) := by
  classical
  intro h0
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n 0) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp h0).2
  have hnot : Not ((M n 0) % (2 ^ 2) = 0) := hsmall 2 (by decide) hz2
  have hmod0 : (M n 0) % (2 ^ 2) = 0 := by
    unfold M
    have hsub : (n - 1) % 4 = 0 := by omega
    simpa [pow_two] using hsub
  exact hnot hmod0

/-- If `n ≡ 2 [MOD 9]` and `3 ≤ z n`, then `k = 1` is excluded from `A n (z n)`. -/
lemma one_not_mem_A_of_mod9 {n : Nat}
    (hz3 : 3 <= z n) (hmod9 : n % 9 = 2) : 1 ∉ A n (z n) := by
  classical
  intro h1
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n 1) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp h1).2
  have hnot : Not ((M n 1) % (3 ^ 2) = 0) := hsmall 3 (by decide) hz3
  have hmod0 : (M n 1) % (3 ^ 2) = 0 := by
    unfold M
    have hsub : (n - 2) % 9 = 0 := by omega
    simpa [pow_two] using hsub
  exact hnot hmod0

lemma mem_K_of_pow_lt {n k : Nat} (hn0 : n ≠ 0) (hpow : 2 ^ k < n) : k ∈ K n := by
  unfold K candidateExponents
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_range.mpr ?_, hpow⟩
  exact Nat.lt_succ_iff.mpr ((Nat.le_log_iff_pow_le Nat.one_lt_two hn0).2 (le_of_lt hpow))

lemma pow_two_mod_nine_cycle (t : Nat) : (2 ^ (6 * t + 1)) % 9 = 2 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 6 * (t + 1) + 1 = (6 * t + 1) + 6 := by omega
      rw [hExp, Nat.pow_add]
      norm_num [Nat.mul_mod, ih]

lemma pow_two_mod_nine_of_mod6_eq1 {k : Nat} (hkmod : k % 6 = 1) :
    (2 ^ k) % 9 = 2 := by
  have hkdecomp : k = 6 * (k / 6) + 1 := by
    have hdiv : k % 6 + 6 * (k / 6) = k := Nat.mod_add_div k 6
    omega
  rw [hkdecomp]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using pow_two_mod_nine_cycle (k / 6)

lemma k_not_mem_A_of_mod9_class {n k : Nat}
    (hz3 : 3 <= z n) (hmod9 : n % 9 = 2) (hkmod : k % 6 = 1) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk9 : (2 ^ k) % 9 = 2 := pow_two_mod_nine_of_mod6_eq1 hkmod
  have hmod0 : (M n k) % (3 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 9 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 3 (by decide) hz3 hmod0

lemma card_A_le_card_K_sub_two {n z0 : Nat}
    (h0K : 0 ∈ K n) (h1K : 1 ∈ K n)
    (h0A : 0 ∉ A n z0) (h1A : 1 ∉ A n z0) :
    (A n z0).card <= (K n).card - 2 := by
  classical
  have hsubsetErase : A n z0 ⊆ ((K n).erase 0).erase 1 := by
    intro k hkA
    have hkK : k ∈ K n := A_subset_K n z0 hkA
    refine Finset.mem_erase.mpr ?_
    refine ⟨?_, ?_⟩
    · intro hk1
      exact h1A (hk1 ▸ hkA)
    · refine Finset.mem_erase.mpr ?_
      refine ⟨?_, hkK⟩
      intro hk0
      exact h0A (hk0 ▸ hkA)
  have hcardErase : (((K n).erase 0).erase 1).card = (K n).card - 2 := by
    have h1Erase : 1 ∈ (K n).erase 0 := Finset.mem_erase.mpr ⟨by decide, h1K⟩
    calc
      (((K n).erase 0).erase 1).card = ((K n).erase 0).card - 1 := Finset.card_erase_of_mem h1Erase
      _ = (K n).card - 1 - 1 := by rw [Finset.card_erase_of_mem h0K]
      _ = (K n).card - 2 := by omega
  calc
    (A n z0).card <= (((K n).erase 0).erase 1).card := Finset.card_le_card hsubsetErase
    _ = (K n).card - 2 := hcardErase

lemma S1_fails_on_progression (t : Nat) :
    ¬ L (65 + 36 * t) <= (A (65 + 36 * t) (z (65 + 36 * t))).card := by
  let n := 65 + 36 * t
  have hn65 : 65 <= n := by
    dsimp [n]
    omega
  have hmod4 : n % 4 = 1 := by
    dsimp [n]
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hn0 : n ≠ 0 := by omega
  have hL6 : 6 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    norm_num
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz2 : 2 <= z n := by omega
  have h0A : 0 ∉ A n (z n) := zero_not_mem_A_of_mod4 hz2 hmod4
  have h1A : 1 ∉ A n (z n) := one_not_mem_A_of_mod9 hz3 hmod9
  have h0K : 0 ∈ K n := by
    unfold K candidateExponents
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
    change 1 < n
    omega
  have h1K : 1 ∈ K n := by
    unfold K candidateExponents
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · unfold L at hL6
      omega
    · change 2 < n
      omega
  have hA_le_Km2 : (A n (z n)).card <= (K n).card - 2 :=
    card_A_le_card_K_sub_two h0K h1K h0A h1A
  have hA_le_Lm1 : (A n (z n)).card <= L n - 1 := by
    have hK : (K n).card <= L n + 1 := card_K_le n
    have htmp : (A n (z n)).card <= (L n + 1) - 2 := by
      exact le_trans hA_le_Km2 (Nat.sub_le_sub_right hK 2)
    have hcalc : (L n + 1) - 2 = L n - 1 := by omega
    simpa [hcalc] using htmp
  intro hS1n
  have : L n <= L n - 1 := le_trans hS1n hA_le_Lm1
  omega

/-- S1: small-prime sieve lower bound (analytic input). -/
def S1_small_prime_sieve : Prop :=
  exists N1 : Nat, forall n : Nat, N1 <= n -> Odd n -> L n <= (A n (z n)).card

/--
Corrected S1 shape with additive slack:
eventually, `A` contains at least `L n - C` exponents.
-/
def S1_small_prime_sieve_slack (C : Nat) : Prop :=
  exists N1 : Nat, forall n : Nat, N1 <= n -> Odd n -> L n - C <= (A n (z n)).card

lemma not_S1_small_prime_sieve : ¬ S1_small_prime_sieve := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let n := 65 + 36 * N1
  have hnN : N1 <= n := by
    dsimp [n]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨32 + 18 * N1, ?_⟩
    omega
  have hbound : L n <= (A n (z n)).card := hN1 n hnN hodd
  have hfail : ¬ L n <= (A n (z n)).card := by
    dsimp [n]
    simpa using (S1_fails_on_progression N1)
  exact hfail hbound

lemma not_S1_small_prime_sieve_slack (C : Nat) : ¬ S1_small_prime_sieve_slack C := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (2 ^ (6 * (C + 1) + 1))
  let n : Nat := 65 + 36 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨32 + 18 * t, ?_⟩
    omega
  have hbound : L n - C <= (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL6 : 6 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    dsimp [n]
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  let S : Finset Nat := (Finset.range (C + 2)).image (fun i => 6 * i + 1)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    have hiLe : i <= C + 1 := by
      exact Nat.le_of_lt_succ (by simpa [Nat.add_assoc] using Finset.mem_range.mp hi)
    have hpow_le :
        2 ^ (6 * i + 1) <= 2 ^ (6 * (C + 1) + 1) := by
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have ht : 2 ^ (6 * (C + 1) + 1) <= t := by
      dsimp [t]
      exact le_max_right N1 (2 ^ (6 * (C + 1) + 1))
    have hpow_t : 2 ^ (6 * i + 1) <= t := le_trans hpow_le ht
    have hpow_n : 2 ^ (6 * i + 1) < n := lt_of_le_of_lt hpow_t (by dsimp [n]; omega)
    have hkK : (6 * i + 1) ∈ K n := mem_K_of_pow_lt hn0 hpow_n
    have hkmod : (6 * i + 1) % 6 = 1 := by omega
    have hkNotA : (6 * i + 1) ∉ A n (z n) := k_not_mem_A_of_mod9_class hz3 hmod9 hkmod
    exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩
  have hcardS : S.card = C + 2 := by
    unfold S
    simpa using Finset.card_image_of_injective (s := Finset.range (C + 2))
      (f := fun i => 6 * i + 1) (by
        intro i j hij
        have hmul : 6 * i = 6 * j := Nat.add_right_cancel hij
        exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 6) hmul)
  have hcardLower : C + 2 <= (K n \ A n (z n)).card := by
    calc
      C + 2 = S.card := by symm; exact hcardS
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (C + 2) + (A n (z n)).card <= (K n).card := by
    have h1 : (C + 2) + (A n (z n)).card <=
        (K n \ A n (z n)).card + (A n (z n)).card :=
      Nat.add_le_add_right hcardLower (A n (z n)).card
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' : (A n (z n)).card + (C + 2) <= (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K : (A n (z n)).card <= (K n).card - (C + 2) := Nat.le_sub_of_add_le hAdd'
  have hA_le_L : (A n (z n)).card <= L n - C - 1 := by
    have hK : (K n).card <= L n + 1 := card_K_le n
    have htmp : (A n (z n)).card <= (L n + 1) - (C + 2) := by
      exact le_trans hA_le_K (Nat.sub_le_sub_right hK (C + 2))
    have hcalc : (L n + 1) - (C + 2) = L n - C - 1 := by omega
    simpa [hcalc] using htmp
  have ht : 2 ^ (6 * (C + 1) + 1) <= t := by
    dsimp [t]
    exact le_max_right N1 (2 ^ (6 * (C + 1) + 1))
  have ht_le_n : t <= n := by
    dsimp [n]
    omega
  have hpowC : 2 ^ (C + 1) <= 2 ^ (6 * (C + 1) + 1) := by
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hC1L : C + 1 <= L n := by
    unfold L
    refine (Nat.le_log_iff_pow_le Nat.one_lt_two hn0).2 ?_
    exact le_trans hpowC (le_trans ht ht_le_n)
  have hCL : C < L n := lt_of_lt_of_le (Nat.lt_succ_self C) hC1L
  have hposLC : 0 < L n - C := Nat.sub_pos_of_lt hCL
  have hcontr : L n - C <= L n - C - 1 := le_trans hbound hA_le_L
  have hltLC : L n - C - 1 < L n - C := Nat.sub_lt hposLC (by decide : 0 < 1)
  exact (Nat.not_le_of_gt hltLC) hcontr

lemma S1_small_prime_sieve_slack_of_strong {C : Nat}
    (hS1 : S1_small_prime_sieve) : S1_small_prime_sieve_slack C := by
  rcases hS1 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact le_trans (Nat.sub_le _ _) (hN n hn hodd)

/--
Sufficient condition for `S1_small_prime_sieve`:
eventually, the small-prime bad set has cardinality at most `|K n| - L n`.
-/
def S1_small_prime_bad_bound_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (smallPrimeBad n (z n)).card <= (K n).card - L n

/--
Slackened small-prime bad-set condition:
eventually, `|smallPrimeBad| ≤ |K| - L + C`.
-/
def S1_small_prime_bad_bound_eventually_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (smallPrimeBad n (z n)).card <= (K n).card - L n + C

/-- S1 decomposition: small-prime bad set is covered by local prime classes. -/
lemma S1_small_prime_decomp (n : Nat) :
  (smallPrimeBad n (z n)).card <= Finset.sum (smallPrimeSupport n) (fun p => Np n p) := by
  classical
  let badAt : Nat -> Finset Nat := fun p => (K n).filter (fun k => (M n k) % (p ^ 2) = 0)
  have hsubset :
      smallPrimeBad n (z n) ⊆ (smallPrimeSupport n).biUnion badAt := by
    intro k hkB
    have hkK : k ∈ K n := (Finset.mem_filter.mp hkB).1
    rcases (Finset.mem_filter.mp hkB).2 with ⟨p, hp, hpz, hmod0⟩
    have hpIcc : p ∈ Finset.Icc 2 (z n) := Finset.mem_Icc.mpr ⟨hp.two_le, hpz⟩
    have hpSupport : p ∈ smallPrimeSupport n := by
      unfold smallPrimeSupport
      exact Finset.mem_filter.mpr ⟨hpIcc, hp⟩
    have hkBadAt : k ∈ badAt p := Finset.mem_filter.mpr ⟨hkK, hmod0⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpSupport, hkBadAt⟩
  calc
    (smallPrimeBad n (z n)).card <= ((smallPrimeSupport n).biUnion badAt).card :=
      Finset.card_le_card hsubset
    _ <= Finset.sum (smallPrimeSupport n) (fun p => (badAt p).card) := Finset.card_biUnion_le
    _ = Finset.sum (smallPrimeSupport n) (fun p => Np n p) := by
      simp [Np, badAt]

/--
Sufficient condition for `S1_small_prime_sieve`:
eventually, the small-prime local-count sum is bounded by `|K n| - L n`.
-/
def S1_small_prime_sum_bound_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (smallPrimeSupport n) (fun p => Np n p) <= (K n).card - L n

/--
Slackened small-prime sum condition:
eventually, the small-prime local-count sum is at most `|K| - L + C`.
-/
def S1_small_prime_sum_bound_eventually_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (smallPrimeSupport n) (fun p => Np n p) <= (K n).card - L n + C

/--
Sufficient condition for `S1_small_prime_sieve`:
eventually, local counts are uniformly bounded by a constant `C`,
and support size times `C` is bounded by `|K n| - L n`.
-/
def S1_uniform_local_bound_eventually (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (forall p : Nat, p ∈ smallPrimeSupport n -> Np n p <= C) /\
    (smallPrimeSupport n).card * C <= (K n).card - L n

/--
Slackened uniform local bound for small primes:
`Np ≤ C0` pointwise and support-size product `≤ |K| - L + C`.
-/
def S1_uniform_local_bound_eventually_slack (C0 C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (forall p : Nat, p ∈ smallPrimeSupport n -> Np n p <= C0) /\
    (smallPrimeSupport n).card * C0 <= (K n).card - L n + C

/-- G1: decompose large-prime contribution via local counts. -/
lemma G1_large_prime_decomp (n : Nat) :
  (B n (z n)).card <= Finset.sum (largePrimeSupport n) (fun p => Np n p) := by
  classical
  let badAt : Nat -> Finset Nat := fun p => (K n).filter (fun k => (M n k) % (p ^ 2) = 0)
  have hsubset :
      B n (z n) ⊆ (largePrimeSupport n).biUnion badAt := by
    intro k hkB
    have hkK : k ∈ K n := (Finset.mem_filter.mp hkB).1
    rcases (Finset.mem_filter.mp hkB).2 with ⟨p, hp, hpgt, hmod0⟩
    have hklt : 2 ^ k < n := C1 hkK
    have hmPos : 0 < M n k := by
      unfold M
      exact Nat.sub_pos_of_lt hklt
    have hp2dvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 hmod0
    have hp2_le_m : p ^ 2 <= M n k := Nat.le_of_dvd hmPos hp2dvd
    have hp_le_sq : p <= p ^ 2 := by
      calc
        p = p * 1 := by simp
        _ <= p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hp.pos)
        _ = p ^ 2 := by simp [pow_two]
    have hp_le_n : p <= n := by
      exact le_trans hp_le_sq (le_trans hp2_le_m (Nat.sub_le n (2 ^ k)))
    have hpIcc : p ∈ Finset.Icc (z n + 1) n := Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt hpgt, hp_le_n⟩
    have hpSupport : p ∈ largePrimeSupport n := by
      unfold largePrimeSupport
      exact Finset.mem_filter.mpr ⟨hpIcc, hp⟩
    have hkBadAt : k ∈ badAt p := Finset.mem_filter.mpr ⟨hkK, hmod0⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpSupport, hkBadAt⟩
  calc
    (B n (z n)).card <= ((largePrimeSupport n).biUnion badAt).card := Finset.card_le_card hsubset
    _ <= Finset.sum (largePrimeSupport n) (fun p => (badAt p).card) := Finset.card_biUnion_le
    _ = Finset.sum (largePrimeSupport n) (fun p => Np n p) := by
      simp [Np, badAt]

/-- G2 (coarse form): summing local bounds over large-prime support. -/
lemma G2_large_prime_via_local (n : Nat) :
  Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
    (largePrimeSupport n).card * (L n + 1) := by
  have hpoint : ∀ p ∈ largePrimeSupport n, Np n p <= L n + 1 := by
    intro p hp
    exact L2_local_periodic n p ((Finset.mem_filter.mp hp).2)
  calc
    Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
        Finset.sum (largePrimeSupport n) (fun _ => L n + 1) := by
          exact Finset.sum_le_sum hpoint
    _ = (largePrimeSupport n).card * (L n + 1) := by
          simp

/-- G3: strict asymptotic control for large-prime contamination (analytic input). -/
def G3_large_prime_error : Prop :=
  exists N2 : Nat, forall n : Nat, N2 <= n -> Odd n -> (B n (z n)).card < L n

/--
Corrected G3 shape with additive slack:
eventually, `B` is strictly below `L n - C`.
-/
def G3_large_prime_error_slack (C : Nat) : Prop :=
  exists N2 : Nat, forall n : Nat, N2 <= n -> Odd n -> (B n (z n)).card < L n - C

lemma G3_large_prime_error_slack_zero_of_strong
    (hG3 : G3_large_prime_error) : G3_large_prime_error_slack 0 := by
  rcases hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  simpa using hN n hn hodd

lemma not_strong_graph_assumptions :
    ¬ (S1_small_prime_sieve ∧ G3_large_prime_error) := by
  intro h
  exact not_S1_small_prime_sieve h.1

/--
Sufficient condition for `G3_large_prime_error`:
an eventual strict bound on the large-prime sum already implies strict control of `B`.
-/
def G3_sum_bound_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (largePrimeSupport n) (fun p => Np n p) < L n

/--
Slackened large-prime sum condition:
eventually, the large-prime local-count sum is `< L n - C`.
-/
def G3_sum_bound_eventually_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (largePrimeSupport n) (fun p => Np n p) < L n - C

lemma G3_of_sum_bound_eventually (hSum : G3_sum_bound_eventually) :
    G3_large_prime_error := by
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (G1_large_prime_decomp n) (hN n hn hodd)

lemma G3_of_sum_bound_eventually_slack {C : Nat}
    (hSum : G3_sum_bound_eventually_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (G1_large_prime_decomp n) (hN n hn hodd)

/--
Sufficient condition for `G3_large_prime_error`:
eventually, local counts are uniformly bounded by a constant `C`,
and support size times `C` is strictly below `L n`.
-/
def G3_uniform_local_bound_eventually (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (forall p : Nat, p ∈ largePrimeSupport n -> Np n p <= C) /\
    (largePrimeSupport n).card * C < L n

/--
Slackened uniform local bound for large primes:
`Np ≤ C0` pointwise and support-size product `< L n - C`.
-/
def G3_uniform_local_bound_eventually_slack (C0 C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (forall p : Nat, p ∈ largePrimeSupport n -> Np n p <= C0) /\
    (largePrimeSupport n).card * C0 < L n - C

lemma G3_of_uniform_local_bound_eventually {C : Nat}
    (hUni : G3_uniform_local_bound_eventually C) : G3_large_prime_error := by
  rcases hUni with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨hpoint, hmul⟩
  have hsum :
      Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
        (largePrimeSupport n).card * C := by
    calc
      Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
          Finset.sum (largePrimeSupport n) (fun _ => C) := by
            exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
      _ = (largePrimeSupport n).card * C := by
            simp
  exact lt_of_le_of_lt (le_trans (G1_large_prime_decomp n) hsum) hmul

lemma G3_of_uniform_local_bound_eventually_slack {C0 C : Nat}
    (hUni : G3_uniform_local_bound_eventually_slack C0 C) :
    G3_large_prime_error_slack C := by
  rcases hUni with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨hpoint, hmul⟩
  have hsum :
      Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
        (largePrimeSupport n).card * C0 := by
    calc
      Finset.sum (largePrimeSupport n) (fun p => Np n p) <=
          Finset.sum (largePrimeSupport n) (fun _ => C0) := by
            exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
      _ = (largePrimeSupport n).card * C0 := by
            simp
  exact lt_of_le_of_lt (le_trans (G1_large_prime_decomp n) hsum) hmul

/-- Exponents below `L n` produce powers strictly below `n` (for positive `n`). -/
lemma two_pow_lt_of_lt_log {n k : Nat} (hn : 0 < n) (hk : k < L n) : 2 ^ k < n := by
  unfold L at hk
  have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hk
  have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  exact lt_of_lt_of_le hpow hle

/-- Lower bound for the cardinality of the exponent window. -/
lemma L_le_card_K_of_pos {n : Nat} (hn : 0 < n) : L n <= (K n).card := by
  have hsubset : Finset.range (L n) ⊆ K n := by
    intro k hk
    unfold K candidateExponents
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (Nat.lt_succ_self _)), ?_⟩
    exact two_pow_lt_of_lt_log hn (Finset.mem_range.mp hk)
  have hcard : (Finset.range (L n)).card <= (K n).card := Finset.card_le_card hsubset
  simpa using hcard

lemma S1_of_small_prime_bad_bound_eventually (hBad : S1_small_prime_bad_bound_eventually) :
    S1_small_prime_sieve := by
  rcases hBad with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  have hnpos : 0 < n := hodd.pos
  have hL : L n <= (K n).card := L_le_card_K_of_pos hnpos
  have hbad : (smallPrimeBad n (z n)).card <= (K n).card - L n := hN n hn hodd
  have hsub :
      (K n).card - ((K n).card - L n) <= (K n).card - (smallPrimeBad n (z n)).card := by
    exact Nat.sub_le_sub_left hbad (K n).card
  have hL_to_Kbad : L n <= (K n).card - (smallPrimeBad n (z n)).card := by
    simpa [Nat.sub_sub_self hL] using hsub
  calc
    L n <= (K n).card - (smallPrimeBad n (z n)).card := hL_to_Kbad
    _ = (A n (z n)).card := by
      symm
      exact card_A_eq_card_K_sub_smallPrimeBad n (z n)

lemma S1_of_small_prime_bad_bound_eventually_slack {C : Nat}
    (hBad : S1_small_prime_bad_bound_eventually_slack C) :
    S1_small_prime_sieve_slack C := by
  rcases hBad with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  have hnpos : 0 < n := hodd.pos
  have hL : L n <= (K n).card := L_le_card_K_of_pos hnpos
  have hbad : (smallPrimeBad n (z n)).card <= (K n).card - L n + C := hN n hn hodd
  have hsub :
      (K n).card - ((K n).card - L n + C) <= (K n).card - (smallPrimeBad n (z n)).card := by
    exact Nat.sub_le_sub_left hbad (K n).card
  have hbase : L n - C <= (K n).card - ((K n).card - L n + C) := by
    omega
  calc
    L n - C <= (K n).card - ((K n).card - L n + C) := hbase
    _ <= (K n).card - (smallPrimeBad n (z n)).card := hsub
    _ = (A n (z n)).card := by
      symm
      exact card_A_eq_card_K_sub_smallPrimeBad n (z n)

lemma S1_of_small_prime_sum_bound_eventually (hSum : S1_small_prime_sum_bound_eventually) :
    S1_small_prime_sieve := by
  apply S1_of_small_prime_bad_bound_eventually
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact le_trans (S1_small_prime_decomp n) (hN n hn hodd)

lemma S1_of_small_prime_sum_bound_eventually_slack {C : Nat}
    (hSum : S1_small_prime_sum_bound_eventually_slack C) :
    S1_small_prime_sieve_slack C := by
  apply S1_of_small_prime_bad_bound_eventually_slack
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact le_trans (S1_small_prime_decomp n) (hN n hn hodd)

lemma S1_of_uniform_local_bound_eventually {C : Nat}
    (hUni : S1_uniform_local_bound_eventually C) : S1_small_prime_sieve := by
  apply S1_of_small_prime_sum_bound_eventually
  rcases hUni with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨hpoint, hmul⟩
  have hsum :
      Finset.sum (smallPrimeSupport n) (fun p => Np n p) <=
        (smallPrimeSupport n).card * C := by
    calc
      Finset.sum (smallPrimeSupport n) (fun p => Np n p) <=
          Finset.sum (smallPrimeSupport n) (fun _ => C) := by
            exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
      _ = (smallPrimeSupport n).card * C := by
            simp
  exact le_trans hsum hmul

lemma S1_of_uniform_local_bound_eventually_slack {C0 C : Nat}
    (hUni : S1_uniform_local_bound_eventually_slack C0 C) :
    S1_small_prime_sieve_slack C := by
  apply S1_of_small_prime_sum_bound_eventually_slack
  rcases hUni with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨hpoint, hmul⟩
  have hsum :
      Finset.sum (smallPrimeSupport n) (fun p => Np n p) <=
        (smallPrimeSupport n).card * C0 := by
    calc
      Finset.sum (smallPrimeSupport n) (fun p => Np n p) <=
          Finset.sum (smallPrimeSupport n) (fun _ => C0) := by
            exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
      _ = (smallPrimeSupport n).card * C0 := by
            simp
  exact le_trans hsum hmul

/--
Sufficient condition for `S1_small_prime_sieve`:
eventually, the small-prime-clean set `A` coincides with the whole exponent window `K`.
-/
def S1_full_window_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n -> A n (z n) = K n

lemma S1_of_full_window_eventually (hA : S1_full_window_eventually) :
    S1_small_prime_sieve := by
  rcases hA with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  have hnpos : 0 < n := hodd.pos
  have hEq : A n (z n) = K n := hN n hn hodd
  calc
    L n <= (K n).card := L_le_card_K_of_pos hnpos
    _ = (A n (z n)).card := by simp [hEq]

/--
Sufficient condition for `G3_large_prime_error`:
eventually, the support-size coarse bound is already `< L n`.
-/
def G3_support_bound_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupport n).card * (L n + 1) < L n

/--
Slackened support-size coarse condition:
eventually, support-size coarse bound is `< L n - C`.
-/
def G3_support_bound_eventually_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupport n).card * (L n + 1) < L n - C

lemma G3_of_support_bound_eventually (hSupp : G3_support_bound_eventually) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (le_trans (G1_large_prime_decomp n) (G2_large_prime_via_local n))
    (hN n hn hodd)

lemma G3_of_support_bound_eventually_slack {C : Nat}
    (hSupp : G3_support_bound_eventually_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (le_trans (G1_large_prime_decomp n) (G2_large_prime_via_local n))
    (hN n hn hodd)

/-- F1 (slack form): positive survivor count from matched slack assumptions. -/
lemma F1_positive_survivors_slack {C : Nat}
    (hS1 : S1_small_prime_sieve_slack C) (hG3 : G3_large_prime_error_slack C) :
    exists N3 : Nat,
      forall n : Nat, N3 <= n -> Odd n -> (A n (z n)).card - (B n (z n)).card > 0 := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hG3 with ⟨N2, hG3'⟩
  refine ⟨max N1 N2, ?_⟩
  intro n hn hodd
  have hn1 : N1 <= n := le_trans (le_max_left N1 N2) hn
  have hn2 : N2 <= n := le_trans (le_max_right N1 N2) hn
  have hA : L n - C <= (A n (z n)).card := hS1' n hn1 hodd
  have hB : (B n (z n)).card < L n - C := hG3' n hn2 hodd
  exact Nat.sub_pos_of_lt (lt_of_lt_of_le hB hA)

/-- F2 (slack form): eventual existence of a squarefree translated value. -/
lemma F2_eventual_squarefree_slack {C : Nat}
    (hS1 : S1_small_prime_sieve_slack C) (hG3 : G3_large_prime_error_slack C) :
    exists N : Nat, forall n : Nat, N <= n -> Odd n ->
      exists k : Nat, k ∈ K n /\ Squarefree (M n k) := by
  rcases F1_positive_survivors_slack hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact C4 (hN n hn hodd)

/-- T0 (slack form): asymptotic theorem from matched slack graph assumptions. -/
lemma T0_erdos11_from_graph_assumptions_slack {C : Nat}
    (hS1 : S1_small_prime_sieve_slack C) (hG3 : G3_large_prime_error_slack C) :
    Erdos11Conjecture := by
  rcases F2_eventual_squarefree_slack hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨k, hkK, hsq⟩
  exact C5 (C1 hkK) hsq

/--
Density-form small-prime bound:
eventually, `a * L n ≤ d * |A n|`.
-/
def S1_density (a d : Nat) : Prop :=
  exists N1 : Nat, forall n : Nat, N1 <= n -> Odd n ->
    a * L n <= d * (A n (z n)).card

/--
Density-form large-prime bound:
eventually, `d * |B n| < b * L n`.
-/
def G3_density (b d : Nat) : Prop :=
  exists N2 : Nat, forall n : Nat, N2 <= n -> Odd n ->
    d * (B n (z n)).card < b * L n

/-- F1 (density form): positive survivors from `b < a` and density bounds. -/
lemma F1_positive_survivors_density {a b d : Nat}
    (hab : b < a) (hS1 : S1_density a d) (hG3 : G3_density b d) :
    exists N3 : Nat,
      forall n : Nat, N3 <= n -> Odd n -> (A n (z n)).card - (B n (z n)).card > 0 := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hG3 with ⟨N2, hG3'⟩
  refine ⟨max (max N1 N2) 3, ?_⟩
  intro n hn hodd
  have hn1 : N1 <= n := le_trans (le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 3)) hn
  have hn2 : N2 <= n := le_trans (le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 3)) hn
  have hn3 : 3 <= n := le_trans (le_max_right (max N1 N2) 3) hn
  have hLpos : 0 < L n := by
    unfold L
    have h2n : 2 <= n := by omega
    exact Nat.log_pos Nat.one_lt_two h2n
  have hA : a * L n <= d * (A n (z n)).card := hS1' n hn1 hodd
  have hB : d * (B n (z n)).card < b * L n := hG3' n hn2 hodd
  have hnot : ¬ (A n (z n)).card <= (B n (z n)).card := by
    intro hle
    have hmul_le : d * (A n (z n)).card <= d * (B n (z n)).card := Nat.mul_le_mul_left d hle
    have hltAB : a * L n < b * L n := lt_of_le_of_lt hA (lt_of_le_of_lt hmul_le hB)
    have hltBA : b * L n < a * L n := Nat.mul_lt_mul_of_pos_right hab hLpos
    exact (lt_asymm hltBA hltAB)
  have hBltA : (B n (z n)).card < (A n (z n)).card := lt_of_not_ge hnot
  exact Nat.sub_pos_of_lt hBltA

/-- F2 (density form): eventual squarefree witness. -/
lemma F2_eventual_squarefree_density {a b d : Nat}
    (hab : b < a) (hS1 : S1_density a d) (hG3 : G3_density b d) :
    exists N : Nat, forall n : Nat, N <= n -> Odd n ->
      exists k : Nat, k ∈ K n /\ Squarefree (M n k) := by
  rcases F1_positive_survivors_density hab hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact C4 (hN n hn hodd)

/-- T0 (density form): asymptotic theorem from density assumptions. -/
lemma T0_erdos11_from_density_assumptions {a b d : Nat}
    (hab : b < a) (hS1 : S1_density a d) (hG3 : G3_density b d) :
    Erdos11Conjecture := by
  rcases F2_eventual_squarefree_density hab hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨k, hkK, hsq⟩
  exact C5 (C1 hkK) hsq

/-- F1: positive survivor count from small and large prime estimates. -/
lemma F1_positive_survivors (hS1 : S1_small_prime_sieve) (hG3 : G3_large_prime_error) :
    exists N3 : Nat,
      forall n : Nat, N3 <= n -> Odd n -> (A n (z n)).card - (B n (z n)).card > 0 := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hG3 with ⟨N2, hG3'⟩
  refine ⟨max N1 N2, ?_⟩
  intro n hn hodd
  have hn1 : N1 <= n := le_trans (le_max_left N1 N2) hn
  have hn2 : N2 <= n := le_trans (le_max_right N1 N2) hn
  have hA : L n <= (A n (z n)).card := hS1' n hn1 hodd
  have hB : (B n (z n)).card < L n := hG3' n hn2 hodd
  exact Nat.sub_pos_of_lt (lt_of_lt_of_le hB hA)

/-- F2: eventual existence of a squarefree translated value. -/
lemma F2_eventual_squarefree (hS1 : S1_small_prime_sieve) (hG3 : G3_large_prime_error) :
    exists N : Nat, forall n : Nat, N <= n -> Odd n ->
      exists k : Nat, k ∈ K n /\ Squarefree (M n k) := by
  rcases F1_positive_survivors hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact C4 (hN n hn hodd)

/-- T0: asymptotic theorem from the graph assumptions. -/
lemma T0_erdos11_from_graph_assumptions
    (hS1 : S1_small_prime_sieve) (hG3 : G3_large_prime_error) : Erdos11Conjecture := by
  rcases F2_eventual_squarefree hS1 hG3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  rcases hN n hn hodd with ⟨k, hkK, hsq⟩
  exact C5 (C1 hkK) hsq

lemma T0_erdos11_from_sum_bounds
    (hS1 : S1_small_prime_sum_bound_eventually) (hG3 : G3_sum_bound_eventually) :
    Erdos11Conjecture := by
  exact T0_erdos11_from_graph_assumptions
    (S1_of_small_prime_sum_bound_eventually hS1)
    (G3_of_sum_bound_eventually hG3)

lemma T0_erdos11_from_uniform_local_bounds {Csmall Clarge : Nat}
    (hS1 : S1_uniform_local_bound_eventually Csmall)
    (hG3 : G3_uniform_local_bound_eventually Clarge) : Erdos11Conjecture := by
  exact T0_erdos11_from_graph_assumptions
    (S1_of_uniform_local_bound_eventually hS1)
    (G3_of_uniform_local_bound_eventually hG3)

lemma T0_erdos11_from_sum_bounds_slack {C : Nat}
    (hS1 : S1_small_prime_sum_bound_eventually_slack C)
    (hG3 : G3_sum_bound_eventually_slack C) : Erdos11Conjecture := by
  exact T0_erdos11_from_graph_assumptions_slack
    (S1_of_small_prime_sum_bound_eventually_slack hS1)
    (G3_of_sum_bound_eventually_slack hG3)

lemma T0_erdos11_from_uniform_local_bounds_slack {Csmall Clarge C : Nat}
    (hS1 : S1_uniform_local_bound_eventually_slack Csmall C)
    (hG3 : G3_uniform_local_bound_eventually_slack Clarge C) : Erdos11Conjecture := by
  exact T0_erdos11_from_graph_assumptions_slack
    (S1_of_uniform_local_bound_eventually_slack hS1)
    (G3_of_uniform_local_bound_eventually_slack hG3)

/--
Unified corrected analytic target:
there exists a shared slack `C` such that both sum-bounds hold eventually.
-/
def MatchedSumBounds : Prop :=
  exists C : Nat,
    S1_small_prime_sum_bound_eventually_slack C /\ G3_sum_bound_eventually_slack C

lemma T0_of_matched_sum_bounds (h : MatchedSumBounds) : Erdos11Conjecture := by
  rcases h with ⟨C, hS1, hG3⟩
  exact T0_erdos11_from_sum_bounds_slack hS1 hG3

/--
Unified corrected local target:
there exists a shared slack `C` from uniform local bounds.
-/
def MatchedUniformBounds : Prop :=
  exists Csmall Clarge C : Nat,
    S1_uniform_local_bound_eventually_slack Csmall C /\
    G3_uniform_local_bound_eventually_slack Clarge C

lemma T0_of_matched_uniform_bounds (h : MatchedUniformBounds) :
    Erdos11Conjecture := by
  rcases h with ⟨Csmall, Clarge, C, hS1, hG3⟩
  exact T0_erdos11_from_uniform_local_bounds_slack hS1 hG3

/--
Unified density target:
there exist `a,b,d` with `b < a` giving matched density bounds.
-/
def MatchedDensityBounds : Prop :=
  exists a b d : Nat, b < a /\ S1_density a d /\ G3_density b d

lemma T0_of_matched_density_bounds (h : MatchedDensityBounds) :
    Erdos11Conjecture := by
  rcases h with ⟨a, b, d, hab, hS1, hG3⟩
  exact T0_erdos11_from_density_assumptions hab hS1 hG3

end AsymptoticGraph

end Erdos11

