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

lemma not_Erdos11Conjecture_iff_unbounded_odd_counterexamples :
    ¬ Erdos11Conjecture ↔
      ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n := by
  constructor
  · intro hNot N
    by_contra hNo
    have hAll : ∀ n : Nat, N ≤ n → Odd n → Represents n := by
      intro n hn hodd
      by_contra hRep
      exact hNo ⟨n, hn, hodd, hRep⟩
    exact hNot ⟨N, hAll⟩
  · intro hUnbounded hE
    rcases hE with ⟨N, hN⟩
    rcases hUnbounded N with ⟨n, hn, hodd, hNotRep⟩
    exact hNotRep (hN n hn hodd)

lemma unbounded_counterexamples_elim_of_erdos11 {P : Prop}
    (hE : Erdos11Conjecture) :
    (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P := by
  intro hUnbounded
  exact False.elim
    ((not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mpr hUnbounded) hE)

lemma not_erdos11_elim_of_erdos11 {P : Prop}
    (hE : Erdos11Conjecture) :
    (¬ Erdos11Conjecture → P) := by
  intro hNot
  exact False.elim (hNot hE)

lemma force_false_target_iff_not_unbounded_odd_counterexamples {P : Prop}
    (hP : ¬ P) :
    ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  constructor
  · intro hForce hUnbounded
    exact hP (hForce hUnbounded)
  · intro hNo hUnbounded
    exact False.elim (hNo hUnbounded)

lemma force_false_target_iff_erdos11 {P : Prop}
    (hP : ¬ P) :
    ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      Erdos11Conjecture := by
  constructor
  · intro hForce
    by_contra hNot
    exact hP (hForce (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot))
  · exact unbounded_counterexamples_elim_of_erdos11

lemma neg_force_false_target_iff_erdos11 {P : Prop}
    (hP : ¬ P) :
    (¬ Erdos11Conjecture → P) ↔ Erdos11Conjecture := by
  constructor
  · intro hForce
    by_contra hNot
    exact hP (hForce hNot)
  · exact not_erdos11_elim_of_erdos11

lemma force_false_targets_iff {P Q : Prop}
    (hP : ¬ P) (hQ : ¬ Q) :
    (((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → Q)) := by
  rw [force_false_target_iff_not_unbounded_odd_counterexamples hP,
    force_false_target_iff_not_unbounded_odd_counterexamples hQ]

lemma neg_force_false_targets_iff {P Q : Prop}
    (hP : ¬ P) (hQ : ¬ Q) :
    ((¬ Erdos11Conjecture → P) ↔ (¬ Erdos11Conjecture → Q)) := by
  rw [neg_force_false_target_iff_erdos11 hP, neg_force_false_target_iff_erdos11 hQ]

lemma force_target_iff_not_unbounded_odd_counterexamples_of_not_target_of_unbounded {P : Prop}
    (hNotP : (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → ¬ P) :
    ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  constructor
  · intro hForce hUnbounded
    exact hNotP hUnbounded (hForce hUnbounded)
  · intro hNo hUnbounded
    exact False.elim (hNo hUnbounded)

lemma force_target_iff_erdos11_of_not_target_of_unbounded {P : Prop}
    (hNotP : (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → ¬ P) :
    ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      Erdos11Conjecture := by
  constructor
  · intro hForce
    by_contra hNot
    exact hNotP
      (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot)
      (hForce (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot))
  · exact unbounded_counterexamples_elim_of_erdos11

lemma force_targets_iff_of_not_targets_of_unbounded {P Q : Prop}
    (hNotP : (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → ¬ P)
    (hNotQ : (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → ¬ Q) :
    (((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → P) ↔
      ((∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) → Q)) := by
  rw [force_target_iff_not_unbounded_odd_counterexamples_of_not_target_of_unbounded hNotP,
    force_target_iff_not_unbounded_odd_counterexamples_of_not_target_of_unbounded hNotQ]

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

/-- Explicit square-divisibility fiber for a fixed prime `p`. -/
noncomputable def badAtSq (n p : Nat) : Finset Nat := by
  classical
  exact (K n).filter (fun k => (M n k) % (p ^ 2) = 0)

lemma card_badAtSq_eq_Np (n p : Nat) : (badAtSq n p).card = Np n p := by
  classical
  simp [badAtSq, Np]

/-- Clean square-divisibility fiber: exponents surviving the small-prime sieve and lying in `badAtSq`. -/
noncomputable def cleanBadAtSq (n z0 p : Nat) : Finset Nat := by
  classical
  exact (A n z0).filter (fun k => (M n k) % (p ^ 2) = 0)

/-- Local clean count for a fixed prime `p`. -/
noncomputable def cleanNp (n z0 p : Nat) : Nat :=
  (cleanBadAtSq n z0 p).card

lemma card_cleanBadAtSq_eq_cleanNp (n z0 p : Nat) :
    (cleanBadAtSq n z0 p).card = cleanNp n z0 p := by
  rfl

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

lemma A_subset_B_of_not_represents {n z0 : Nat} (hNotRep : ¬ Represents n) :
    A n z0 ⊆ B n z0 := by
  intro k hkA
  by_contra hkB
  have hsq : Squarefree (M n k) := C2 hkA hkB
  have hkK : k ∈ K n := A_subset_K n z0 hkA
  exact hNotRep (C5 (C1 hkK) hsq)

lemma card_A_le_card_B_of_not_represents {n z0 : Nat} (hNotRep : ¬ Represents n) :
    (A n z0).card <= (B n z0).card := by
  exact Finset.card_le_card (A_subset_B_of_not_represents hNotRep)

lemma card_A_sub_B_eq_zero_of_not_represents {n z0 : Nat} (hNotRep : ¬ Represents n) :
    (A n z0 \ B n z0).card = 0 := by
  apply Finset.card_eq_zero.mpr
  exact Finset.eq_empty_iff_forall_notMem.mpr (by
    intro k hk
    have hkA : k ∈ A n z0 := (Finset.mem_sdiff.mp hk).1
    have hkB : k ∉ B n z0 := (Finset.mem_sdiff.mp hk).2
    have hsq : Squarefree (M n k) := C2 hkA hkB
    have hkK : k ∈ K n := A_subset_K n z0 hkA
    exact hNotRep (C5 (C1 hkK) hsq))

lemma card_A_sub_card_B_eq_zero_of_not_represents {n z0 : Nat} (hNotRep : ¬ Represents n) :
    (A n z0).card - (B n z0).card = 0 := by
  exact Nat.sub_eq_zero_of_le (card_A_le_card_B_of_not_represents hNotRep)

lemma card_K_le_smallPrimeBad_add_B_of_not_represents {n : Nat}
    (hNotRep : ¬ Represents n) :
    (K n).card <= (smallPrimeBad n (z n)).card + (B n (z n)).card := by
  have hKminus_le_B :
      (K n \ smallPrimeBad n (z n)).card <= (B n (z n)).card := by
    have hAeq : A n (z n) = K n \ smallPrimeBad n (z n) := A_eq_K_sdiff_smallPrimeBad n (z n)
    have hA_le_B : (A n (z n)).card <= (B n (z n)).card :=
      card_A_le_card_B_of_not_represents (z0 := z n) hNotRep
    simpa [hAeq] using hA_le_B
  have hKs : (K n).card - (smallPrimeBad n (z n)).card <= (B n (z n)).card := by
    have hcard :
        (K n \ smallPrimeBad n (z n)).card = (K n).card - (smallPrimeBad n (z n)).card :=
      Finset.card_sdiff_of_subset (smallPrimeBad_subset_K n (z n))
    simpa [hcard] using hKminus_le_B
  have hK_le_BS :
      (K n).card <= (B n (z n)).card + (smallPrimeBad n (z n)).card :=
    (Nat.sub_le_iff_le_add).1 hKs
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hK_le_BS

/-- Prime support used in small-prime counting. -/
noncomputable def smallPrimeSupport (n : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 2 (z n)).filter Nat.Prime

/-- Prime support used in large-prime counting. -/
noncomputable def largePrimeSupport (n : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc (z n + 1) n).filter Nat.Prime

/--
Large-prime support truncated to the non-vacuous square range `p^2 <= n`.
For `p^2 > n`, the local condition `(n - 2^k) % p^2 = 0` is impossible on `K n`.
-/
noncomputable def largePrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupport n).filter (fun p => p ^ 2 <= n)

/-- Base-2 Wieferich condition at `p`: `2^(p-1) ≡ 1 [MOD p^2]`. -/
def WieferichBase2 (p : Nat) : Prop :=
  2 ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- Large-prime square support split by the base-2 Wieferich condition. -/
noncomputable def wieferichLargePrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter WieferichBase2

/-- Complementary large-prime square support: primes failing the base-2 Wieferich condition. -/
noncomputable def nonWieferichLargePrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => ¬ WieferichBase2 p)

lemma wieferichLargePrimeSupportSq_subset (n : Nat) :
    wieferichLargePrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma nonWieferichLargePrimeSupportSq_subset (n : Nat) :
    nonWieferichLargePrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma card_wieferich_add_card_nonWieferichLargePrimeSupportSq (n : Nat) :
    (wieferichLargePrimeSupportSq n).card + (nonWieferichLargePrimeSupportSq n).card =
      (largePrimeSupportSq n).card := by
  classical
  simpa [wieferichLargePrimeSupportSq, nonWieferichLargePrimeSupportSq] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeSupportSq n) (p := WieferichBase2))

/-- Active square-range large primes: those with nonzero local count `Np`. -/
noncomputable def largePrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => Np n p ≠ 0)

/-- Active square-range large primes satisfying the base-2 Wieferich condition. -/
noncomputable def wieferichLargePrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeActiveSupportSq n).filter WieferichBase2

/-- Active square-range large primes failing the base-2 Wieferich condition. -/
noncomputable def nonWieferichLargePrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeActiveSupportSq n).filter (fun p => ¬ WieferichBase2 p)

lemma largePrimeActiveSupportSq_subset (n : Nat) :
    largePrimeActiveSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma wieferichLargePrimeActiveSupportSq_subset (n : Nat) :
    wieferichLargePrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma nonWieferichLargePrimeActiveSupportSq_subset (n : Nat) :
    nonWieferichLargePrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma wieferichLargePrimeActiveSupportSq_subset_wieferichLargePrimeSupportSq (n : Nat) :
    wieferichLargePrimeActiveSupportSq n ⊆ wieferichLargePrimeSupportSq n := by
  classical
  intro p hp
  have hpAct : p ∈ largePrimeActiveSupportSq n := (Finset.mem_filter.mp hp).1
  have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
  exact Finset.mem_filter.mpr ⟨hpSq, (Finset.mem_filter.mp hp).2⟩

lemma nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq (n : Nat) :
    nonWieferichLargePrimeActiveSupportSq n ⊆ nonWieferichLargePrimeSupportSq n := by
  classical
  intro p hp
  have hpAct : p ∈ largePrimeActiveSupportSq n := (Finset.mem_filter.mp hp).1
  have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
  exact Finset.mem_filter.mpr ⟨hpSq, (Finset.mem_filter.mp hp).2⟩

lemma card_wieferich_add_card_nonWieferichLargePrimeActiveSupportSq (n : Nat) :
    (wieferichLargePrimeActiveSupportSq n).card +
        (nonWieferichLargePrimeActiveSupportSq n).card =
      (largePrimeActiveSupportSq n).card := by
  classical
  simpa [wieferichLargePrimeActiveSupportSq, nonWieferichLargePrimeActiveSupportSq] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeActiveSupportSq n) (p := WieferichBase2))

/-- Clean square-range large primes: those contributing to the clean set `A n (z n)`. -/
noncomputable def largePrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => cleanNp n (z n) p ≠ 0)

/-- Clean square-range large primes satisfying the base-2 Wieferich condition. -/
noncomputable def wieferichLargePrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeCleanSupportSq n).filter WieferichBase2

/-- Clean square-range large primes failing the base-2 Wieferich condition. -/
noncomputable def nonWieferichLargePrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeCleanSupportSq n).filter (fun p => ¬ WieferichBase2 p)

lemma largePrimeCleanSupportSq_subset (n : Nat) :
    largePrimeCleanSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma wieferichLargePrimeCleanSupportSq_subset (n : Nat) :
    wieferichLargePrimeCleanSupportSq n ⊆ largePrimeCleanSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma nonWieferichLargePrimeCleanSupportSq_subset (n : Nat) :
    nonWieferichLargePrimeCleanSupportSq n ⊆ largePrimeCleanSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma card_wieferich_add_card_nonWieferichLargePrimeCleanSupportSq (n : Nat) :
    (wieferichLargePrimeCleanSupportSq n).card +
        (nonWieferichLargePrimeCleanSupportSq n).card =
      (largePrimeCleanSupportSq n).card := by
  classical
  simpa [wieferichLargePrimeCleanSupportSq, nonWieferichLargePrimeCleanSupportSq] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeCleanSupportSq n) (p := WieferichBase2))

/--
Very large active square-range primes: `p^4 > n`.
Two distinct such primes cannot both divide the same `M n k` to square order.
-/
noncomputable def veryLargePrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeActiveSupportSq n).filter (fun p => n < p ^ 4)

/-- Complementary active square-range primes with `p^4 <= n`. -/
noncomputable def lowFourthPrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeActiveSupportSq n).filter (fun p => p ^ 4 <= n)

/-- Very large clean square-range primes: `p^4 > n`. -/
noncomputable def veryLargePrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeCleanSupportSq n).filter (fun p => n < p ^ 4)

/-- Complementary clean square-range primes with `p^4 <= n`. -/
noncomputable def lowFourthPrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeCleanSupportSq n).filter (fun p => p ^ 4 <= n)

/-- Low-fourth clean square-range primes satisfying the base-2 Wieferich condition. -/
noncomputable def wieferichLowFourthPrimeCleanSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (lowFourthPrimeCleanSupportSq n).filter WieferichBase2

/--
Higher large-prime square range with `p^6 > n`.
For a fixed exponent `k`, at most two such primes can divide `M n k` to square order.
-/
noncomputable def highSixthPrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => n < p ^ 6)

/--
Higher large-prime square range with `p^5 > n`.
For a fixed exponent `k`, at most two such primes can divide `M n k` to square order.
-/
noncomputable def highFifthPrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => n < p ^ 5)

/-- Complementary square-range large primes with `p^5 <= n`. -/
noncomputable def lowFifthPrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => p ^ 5 <= n)

/-- Active low-fifth square-range large primes. -/
noncomputable def lowFifthPrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (lowFifthPrimeSupportSq n).filter (fun p => Np n p ≠ 0)

/-- Active low-fifth square-range large primes satisfying the base-2 Wieferich condition. -/
noncomputable def wieferichLowFifthPrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (lowFifthPrimeActiveSupportSq n).filter WieferichBase2

/-- Complementary square-range large primes with `p^6 <= n`. -/
noncomputable def lowSixthPrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupportSq n).filter (fun p => p ^ 6 <= n)

/-- Active low-sixth square-range large primes. -/
noncomputable def lowSixthPrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (lowSixthPrimeSupportSq n).filter (fun p => Np n p ≠ 0)

/-- Active low-sixth square-range large primes satisfying the base-2 Wieferich condition. -/
noncomputable def wieferichLowSixthPrimeActiveSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (lowSixthPrimeActiveSupportSq n).filter WieferichBase2

lemma veryLargePrimeActiveSupportSq_subset (n : Nat) :
    veryLargePrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma lowFourthPrimeActiveSupportSq_subset (n : Nat) :
    lowFourthPrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma veryLargePrimeCleanSupportSq_subset (n : Nat) :
    veryLargePrimeCleanSupportSq n ⊆ largePrimeCleanSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma lowFourthPrimeCleanSupportSq_subset (n : Nat) :
    lowFourthPrimeCleanSupportSq n ⊆ largePrimeCleanSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma highSixthPrimeSupportSq_subset (n : Nat) :
    highSixthPrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma highFifthPrimeSupportSq_subset (n : Nat) :
    highFifthPrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma lowFifthPrimeSupportSq_subset (n : Nat) :
    lowFifthPrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma lowFifthPrimeActiveSupportSq_subset (n : Nat) :
    lowFifthPrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpLow, hNp⟩
  exact Finset.mem_filter.mpr ⟨lowFifthPrimeSupportSq_subset n hpLow, hNp⟩

lemma lowSixthPrimeSupportSq_subset (n : Nat) :
    lowSixthPrimeSupportSq n ⊆ largePrimeSupportSq n := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma lowSixthPrimeActiveSupportSq_subset (n : Nat) :
    lowSixthPrimeActiveSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpLow, hNp⟩
  exact Finset.mem_filter.mpr ⟨lowSixthPrimeSupportSq_subset n hpLow, hNp⟩

lemma card_veryLarge_add_card_lowFourthPrimeActiveSupportSq (n : Nat) :
    (veryLargePrimeActiveSupportSq n).card + (lowFourthPrimeActiveSupportSq n).card =
      (largePrimeActiveSupportSq n).card := by
  classical
  simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4))

lemma card_veryLarge_add_card_lowFourthPrimeCleanSupportSq (n : Nat) :
    (veryLargePrimeCleanSupportSq n).card + (lowFourthPrimeCleanSupportSq n).card =
      (largePrimeCleanSupportSq n).card := by
  classical
  simpa [veryLargePrimeCleanSupportSq, lowFourthPrimeCleanSupportSq] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeCleanSupportSq n) (p := fun p => n < p ^ 4))

/-- Size bound for the exponent window. -/
lemma card_K_le (n : Nat) : (K n).card <= L n + 1 := by
  unfold K L candidateExponents
  simpa using (Finset.card_filter_le (s := Finset.range (Nat.log 2 n + 1))
    (p := fun k => 2 ^ k < n))

lemma prime_of_mem_largePrimeSupportSq {n p : Nat} (hpS : p ∈ largePrimeSupportSq n) :
    Nat.Prime p := by
  exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hpS).1)).2

lemma prime_of_mem_largePrimeActiveSupportSq {n p : Nat} (hpS : p ∈ largePrimeActiveSupportSq n) :
    Nat.Prime p := by
  exact prime_of_mem_largePrimeSupportSq (largePrimeActiveSupportSq_subset n hpS)

lemma badAtSq_nonempty_of_mem_largePrimeActiveSupportSq {n p : Nat}
    (hpS : p ∈ largePrimeActiveSupportSq n) :
    (badAtSq n p).Nonempty := by
  have hNpNe : Np n p ≠ 0 := (Finset.mem_filter.mp hpS).2
  have hcardNe : (badAtSq n p).card ≠ 0 := by simpa [card_badAtSq_eq_Np n p] using hNpNe
  exact Finset.card_ne_zero.mp hcardNe

lemma disjoint_badAtSq_of_mem_veryLargePrimeActiveSupportSq {n p q : Nat}
    (hpS : p ∈ veryLargePrimeActiveSupportSq n)
    (hqS : q ∈ veryLargePrimeActiveSupportSq n)
    (hpq : p ≠ q) :
    Disjoint (badAtSq n p) (badAtSq n q) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro k hkP hkQ
  have hkK : k ∈ K n := (Finset.mem_filter.mp hkP).1
  have hpdvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hkP).2
  have hqdvd : q ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hkQ).2
  have hpPrime : Nat.Prime p := prime_of_mem_largePrimeActiveSupportSq ((Finset.mem_filter.mp hpS).1)
  have hqPrime : Nat.Prime q := prime_of_mem_largePrimeActiveSupportSq ((Finset.mem_filter.mp hqS).1)
  have hpqcop : Nat.Coprime p q := by
    exact (Nat.Prime.coprime_iff_not_dvd hpPrime).2 (by
      intro hdiv
      rcases (Nat.dvd_prime hqPrime).1 hdiv with h1 | h2
      · exact hpPrime.ne_one h1
      · exact hpq h2)
  have hcop_p_qsq : Nat.Coprime p (q ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) p q).2 hpqcop
  have hcop_qsq_psq : Nat.Coprime (q ^ 2) (p ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) (q ^ 2) p).2 hcop_p_qsq.symm
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) := hcop_qsq_psq.symm
  have hprodDvd : p ^ 2 * q ^ 2 ∣ M n k := hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  have hp4 : n < p ^ 4 := (Finset.mem_filter.mp hpS).2
  have hq4 : n < q ^ 4 := (Finset.mem_filter.mp hqS).2
  have hprodGt : n < p ^ 2 * q ^ 2 := by
    rcases le_total p q with hpqle | hqple
    · have hsq : p ^ 2 <= q ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hpqle hpqle
      have hp4le : p ^ 4 <= p ^ 2 * q ^ 2 := by
        have hmul : p ^ 2 * p ^ 2 <= p ^ 2 * q ^ 2 := Nat.mul_le_mul_left (p ^ 2) hsq
        ring_nf at hmul
        ring_nf
        exact hmul
      exact lt_of_lt_of_le hp4 hp4le
    · have hsq : q ^ 2 <= p ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hqple hqple
      have hq4le : q ^ 4 <= p ^ 2 * q ^ 2 := by
        have hmul : q ^ 2 * q ^ 2 <= p ^ 2 * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hsq
        ring_nf at hmul
        ring_nf
        exact hmul
      exact lt_of_lt_of_le hq4 hq4le
  have hmLe : M n k <= n := by
    unfold M
    exact Nat.sub_le n (2 ^ k)
  have hprodLe : p ^ 2 * q ^ 2 <= M n k := Nat.le_of_dvd (Nat.sub_pos_of_lt (C1 hkK)) hprodDvd
  exact (Nat.lt_irrefl n) (lt_of_lt_of_le hprodGt (le_trans hprodLe hmLe))

lemma card_veryLargePrimeActiveSupportSq_le_cardK (n : Nat) :
    (veryLargePrimeActiveSupportSq n).card <= (K n).card := by
  classical
  let S := veryLargePrimeActiveSupportSq n
  have hsum :
      S.card <= Finset.sum S (fun p => (badAtSq n p).card) := by
    calc
      S.card = Finset.sum S (fun _ => 1) := by simp
      _ <= Finset.sum S (fun p => (badAtSq n p).card) := by
        exact Finset.sum_le_sum (by
          intro p hp
          have hne : (badAtSq n p).Nonempty := badAtSq_nonempty_of_mem_largePrimeActiveSupportSq
            (veryLargePrimeActiveSupportSq_subset n hp)
          exact Nat.succ_le_of_lt (Finset.card_pos.mpr hne))
  have hpair : (↑S : Set Nat).PairwiseDisjoint (badAtSq n) := by
    intro p hp q hq hpq
    exact disjoint_badAtSq_of_mem_veryLargePrimeActiveSupportSq hp hq hpq
  have hsubset :
      S.biUnion (badAtSq n) ⊆ K n := by
    intro k hk
    rcases Finset.mem_biUnion.mp hk with ⟨p, hp, hkBad⟩
    exact (Finset.mem_filter.mp hkBad).1
  calc
    S.card <= Finset.sum S (fun p => (badAtSq n p).card) := hsum
    _ = (S.biUnion (badAtSq n)).card := by symm; exact Finset.card_biUnion hpair
    _ <= (K n).card := Finset.card_le_card hsubset

lemma sum_Np_veryLargePrimeActiveSupportSq_le_cardK (n : Nat) :
    Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) <= (K n).card := by
  classical
  let S := veryLargePrimeActiveSupportSq n
  have hpair : (↑S : Set Nat).PairwiseDisjoint (badAtSq n) := by
    intro p hp q hq hpq
    exact disjoint_badAtSq_of_mem_veryLargePrimeActiveSupportSq hp hq hpq
  have hsubset :
      S.biUnion (badAtSq n) ⊆ K n := by
    intro k hk
    rcases Finset.mem_biUnion.mp hk with ⟨p, hp, hkBad⟩
    exact (Finset.mem_filter.mp hkBad).1
  calc
    Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum S (fun p => (badAtSq n p).card) := by
          simp [S, card_badAtSq_eq_Np]
    _ = (S.biUnion (badAtSq n)).card := by
          symm
          exact Finset.card_biUnion hpair
    _ <= (K n).card := Finset.card_le_card hsubset

lemma card_veryLargePrimeActiveSupportSq_le_L_add_one (n : Nat) :
    (veryLargePrimeActiveSupportSq n).card <= L n + 1 := by
  exact le_trans (card_veryLargePrimeActiveSupportSq_le_cardK n) (card_K_le n)

lemma card_largePrimeActiveSupportSq_le_lowFourth_add_L_add_one (n : Nat) :
    (largePrimeActiveSupportSq n).card <=
      (lowFourthPrimeActiveSupportSq n).card + (L n + 1) := by
  calc
    (largePrimeActiveSupportSq n).card =
        (veryLargePrimeActiveSupportSq n).card + (lowFourthPrimeActiveSupportSq n).card := by
          symm
          exact card_veryLarge_add_card_lowFourthPrimeActiveSupportSq n
    _ <= (L n + 1) + (lowFourthPrimeActiveSupportSq n).card := by
          exact Nat.add_le_add_right (card_veryLargePrimeActiveSupportSq_le_L_add_one n) _
    _ = (lowFourthPrimeActiveSupportSq n).card + (L n + 1) := by ac_rfl

lemma coprime_sq_sq_of_distinct_primes {p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.Coprime (p ^ 2) (q ^ 2) := by
  have hpqcop : Nat.Coprime p q := by
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (by
      intro hdiv
      rcases (Nat.dvd_prime hq).1 hdiv with h1 | h2
      · exact hp.ne_one h1
      · exact hpq h2)
  have hcop_p_qsq : Nat.Coprime p (q ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) p q).2 hpqcop
  have hcop_qsq_psq : Nat.Coprime (q ^ 2) (p ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) (q ^ 2) p).2 hcop_p_qsq.symm
  exact hcop_qsq_psq.symm

lemma pow_six_le_sq_triprod_of_le_le {p q r : Nat}
    (hpq : p <= q) (hpr : p <= r) :
    p ^ 6 <= p ^ 2 * q ^ 2 * r ^ 2 := by
  have hsqpq : p ^ 2 <= q ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpq hpq
  have hsqpr : p ^ 2 <= r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpr hpr
  calc
    p ^ 6 = (p ^ 2 * p ^ 2) * p ^ 2 := by
      rw [show (6 : Nat) = 2 + 2 + 2 by decide, Nat.pow_add, Nat.pow_add]
    _ <= (p ^ 2 * q ^ 2) * p ^ 2 := by
      exact Nat.mul_le_mul_right (p ^ 2) (Nat.mul_le_mul_left (p ^ 2) hsqpq)
    _ <= (p ^ 2 * q ^ 2) * r ^ 2 := by
      exact Nat.mul_le_mul_left (p ^ 2 * q ^ 2) hsqpr
    _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl

lemma pow_five_le_pow_six_of_one_le {p : Nat} (hp1 : 1 <= p) : p ^ 5 <= p ^ 6 := by
  calc
    p ^ 5 = p ^ 5 * 1 := by simp
    _ <= p ^ 5 * p := Nat.mul_le_mul_left (p ^ 5) hp1
    _ = p ^ 6 := by
      rw [show (6 : Nat) = 5 + 1 by decide, Nat.pow_add]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma card_highFifthPrimeSupportSq_filter_badAtSq_le_two (n k : Nat) :
    ((highFifthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card <= 2 := by
  classical
  by_contra hcard
  have hgt :
      2 < ((highFifthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card :=
    lt_of_not_ge hcard
  rcases Finset.two_lt_card.mp hgt with ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩
  have hpHigh : p ∈ highFifthPrimeSupportSq n := (Finset.mem_filter.mp hp).1
  have hqHigh : q ∈ highFifthPrimeSupportSq n := (Finset.mem_filter.mp hq).1
  have hrHigh : r ∈ highFifthPrimeSupportSq n := (Finset.mem_filter.mp hr).1
  have hpk : k ∈ badAtSq n p := (Finset.mem_filter.mp hp).2
  have hqk : k ∈ badAtSq n q := (Finset.mem_filter.mp hq).2
  have hrk : k ∈ badAtSq n r := (Finset.mem_filter.mp hr).2
  have hkK : k ∈ K n := (Finset.mem_filter.mp hpk).1
  have hpdvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hpk).2
  have hqdvd : q ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hqk).2
  have hrdvd : r ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hrk).2
  have hpPrime : Nat.Prime p := prime_of_mem_largePrimeSupportSq (highFifthPrimeSupportSq_subset n hpHigh)
  have hqPrime : Nat.Prime q := prime_of_mem_largePrimeSupportSq (highFifthPrimeSupportSq_subset n hqHigh)
  have hrPrime : Nat.Prime r := prime_of_mem_largePrimeSupportSq (highFifthPrimeSupportSq_subset n hrHigh)
  have hcopPQ : Nat.Coprime (p ^ 2) (q ^ 2) := coprime_sq_sq_of_distinct_primes hpPrime hqPrime hpq
  have hcopPR : Nat.Coprime (p ^ 2) (r ^ 2) := coprime_sq_sq_of_distinct_primes hpPrime hrPrime hpr
  have hcopQR : Nat.Coprime (q ^ 2) (r ^ 2) := coprime_sq_sq_of_distinct_primes hqPrime hrPrime hqr
  have hpqDvd : p ^ 2 * q ^ 2 ∣ M n k := hcopPQ.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  have hcopPQr : Nat.Coprime (p ^ 2 * q ^ 2) (r ^ 2) := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcopPR, hcopQR⟩
  have hprodDvd : p ^ 2 * q ^ 2 * r ^ 2 ∣ M n k := hcopPQr.mul_dvd_of_dvd_of_dvd hpqDvd hrdvd
  have hp5 : n < p ^ 5 := (Finset.mem_filter.mp hpHigh).2
  have hq5 : n < q ^ 5 := (Finset.mem_filter.mp hqHigh).2
  have hr5 : n < r ^ 5 := (Finset.mem_filter.mp hrHigh).2
  have hprodGt : n < p ^ 2 * q ^ 2 * r ^ 2 := by
    rcases le_total p q with hpqle | hqple
    · rcases le_total p r with hprle | hrple
      · have hp1 : 1 <= p := Nat.succ_le_of_lt hpPrime.pos
        exact lt_of_lt_of_le hp5
          (le_trans (pow_five_le_pow_six_of_one_le hp1)
            (pow_six_le_sq_triprod_of_le_le hpqle hprle))
      · have hrple' : r <= p := hrple
        have hrqle : r <= q := le_trans hrple' hpqle
        have hr1 : 1 <= r := Nat.succ_le_of_lt hrPrime.pos
        exact lt_of_lt_of_le hr5
          (le_trans (pow_five_le_pow_six_of_one_le hr1)
            (by
              calc
                r ^ 6 <= r ^ 2 * p ^ 2 * q ^ 2 := pow_six_le_sq_triprod_of_le_le hrple' hrqle
                _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl))
    · have hqple' : q <= p := hqple
      rcases le_total q r with hqrle | hrqle
      · have hq1 : 1 <= q := Nat.succ_le_of_lt hqPrime.pos
        exact lt_of_lt_of_le hq5
          (le_trans (pow_five_le_pow_six_of_one_le hq1)
            (by
              calc
                q ^ 6 <= q ^ 2 * p ^ 2 * r ^ 2 := pow_six_le_sq_triprod_of_le_le hqple' hqrle
                _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl))
      · have hrqle' : r <= q := hrqle
        have hrple : r <= p := le_trans hrqle' hqple'
        have hr1 : 1 <= r := Nat.succ_le_of_lt hrPrime.pos
        exact lt_of_lt_of_le hr5
          (le_trans (pow_five_le_pow_six_of_one_le hr1)
            (by
              calc
                r ^ 6 <= r ^ 2 * p ^ 2 * q ^ 2 := pow_six_le_sq_triprod_of_le_le hrple hrqle'
                _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl))
  have hmLe : M n k <= n := by
    unfold M
    exact Nat.sub_le n (2 ^ k)
  have hprodLe : p ^ 2 * q ^ 2 * r ^ 2 <= M n k := by
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt (C1 hkK)) hprodDvd
  exact (Nat.lt_irrefl n) (lt_of_lt_of_le hprodGt (le_trans hprodLe hmLe))

lemma card_highSixthPrimeSupportSq_filter_badAtSq_le_two (n k : Nat) :
    ((highSixthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card <= 2 := by
  classical
  by_contra hcard
  have hgt :
      2 < ((highSixthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card :=
    lt_of_not_ge hcard
  rcases Finset.two_lt_card.mp hgt with ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩
  have hpHigh : p ∈ highSixthPrimeSupportSq n := (Finset.mem_filter.mp hp).1
  have hqHigh : q ∈ highSixthPrimeSupportSq n := (Finset.mem_filter.mp hq).1
  have hrHigh : r ∈ highSixthPrimeSupportSq n := (Finset.mem_filter.mp hr).1
  have hpk : k ∈ badAtSq n p := (Finset.mem_filter.mp hp).2
  have hqk : k ∈ badAtSq n q := (Finset.mem_filter.mp hq).2
  have hrk : k ∈ badAtSq n r := (Finset.mem_filter.mp hr).2
  have hkK : k ∈ K n := (Finset.mem_filter.mp hpk).1
  have hpdvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hpk).2
  have hqdvd : q ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hqk).2
  have hrdvd : r ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 (Finset.mem_filter.mp hrk).2
  have hpPrime : Nat.Prime p := prime_of_mem_largePrimeSupportSq (highSixthPrimeSupportSq_subset n hpHigh)
  have hqPrime : Nat.Prime q := prime_of_mem_largePrimeSupportSq (highSixthPrimeSupportSq_subset n hqHigh)
  have hrPrime : Nat.Prime r := prime_of_mem_largePrimeSupportSq (highSixthPrimeSupportSq_subset n hrHigh)
  have hcopPQ : Nat.Coprime (p ^ 2) (q ^ 2) := coprime_sq_sq_of_distinct_primes hpPrime hqPrime hpq
  have hcopPR : Nat.Coprime (p ^ 2) (r ^ 2) := coprime_sq_sq_of_distinct_primes hpPrime hrPrime hpr
  have hcopQR : Nat.Coprime (q ^ 2) (r ^ 2) := coprime_sq_sq_of_distinct_primes hqPrime hrPrime hqr
  have hpqDvd : p ^ 2 * q ^ 2 ∣ M n k := hcopPQ.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  have hcopPQr : Nat.Coprime (p ^ 2 * q ^ 2) (r ^ 2) := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hcopPR, hcopQR⟩
  have hprodDvd : p ^ 2 * q ^ 2 * r ^ 2 ∣ M n k := hcopPQr.mul_dvd_of_dvd_of_dvd hpqDvd hrdvd
  have hp6 : n < p ^ 6 := (Finset.mem_filter.mp hpHigh).2
  have hq6 : n < q ^ 6 := (Finset.mem_filter.mp hqHigh).2
  have hr6 : n < r ^ 6 := (Finset.mem_filter.mp hrHigh).2
  have hp6eq : p ^ 6 = (p ^ 2 * p ^ 2) * p ^ 2 := by
    rw [show (6 : Nat) = 2 + 2 + 2 by decide, Nat.pow_add, Nat.pow_add]
  have hq6eq : q ^ 6 = (q ^ 2 * q ^ 2) * q ^ 2 := by
    rw [show (6 : Nat) = 2 + 2 + 2 by decide, Nat.pow_add, Nat.pow_add]
  have hr6eq : r ^ 6 = (r ^ 2 * r ^ 2) * r ^ 2 := by
    rw [show (6 : Nat) = 2 + 2 + 2 by decide, Nat.pow_add, Nat.pow_add]
  have hprodGt : n < p ^ 2 * q ^ 2 * r ^ 2 := by
    rcases le_total p q with hpqle | hqple
    · rcases le_total p r with hprle | hrple
      · have hsqpq : p ^ 2 <= q ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hpqle hpqle
        have hsqpr : p ^ 2 <= r ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hprle hprle
        have hp6le : p ^ 6 <= p ^ 2 * q ^ 2 * r ^ 2 := by
          calc
            p ^ 6 = (p ^ 2 * p ^ 2) * p ^ 2 := hp6eq
            _ <= (p ^ 2 * q ^ 2) * p ^ 2 := Nat.mul_le_mul_right (p ^ 2)
                  (Nat.mul_le_mul_left (p ^ 2) hsqpq)
            _ <= (p ^ 2 * q ^ 2) * r ^ 2 := Nat.mul_le_mul_left (p ^ 2 * q ^ 2) hsqpr
            _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl
        exact lt_of_lt_of_le hp6 hp6le
      · have hrple' : r <= p := hrple
        have hrqle : r <= q := le_trans hrple' hpqle
        have hsqrp : r ^ 2 <= p ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hrple' hrple'
        have hsqrq : r ^ 2 <= q ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hrqle hrqle
        have hr6le : r ^ 6 <= p ^ 2 * q ^ 2 * r ^ 2 := by
          calc
            r ^ 6 = (r ^ 2 * r ^ 2) * r ^ 2 := hr6eq
            _ <= (p ^ 2 * r ^ 2) * r ^ 2 := Nat.mul_le_mul_right (r ^ 2)
                  (Nat.mul_le_mul_right (r ^ 2) hsqrp)
            _ <= (p ^ 2 * q ^ 2) * r ^ 2 := Nat.mul_le_mul_right (r ^ 2)
                  (Nat.mul_le_mul_left (p ^ 2) hsqrq)
            _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl
        exact lt_of_lt_of_le hr6 hr6le
    · have hqple' : q <= p := hqple
      rcases le_total q r with hqrle | hrqle
      · have hsqqp : q ^ 2 <= p ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hqple' hqple'
        have hsqqr : q ^ 2 <= r ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hqrle hqrle
        have hq6le : q ^ 6 <= p ^ 2 * q ^ 2 * r ^ 2 := by
          calc
            q ^ 6 = (q ^ 2 * q ^ 2) * q ^ 2 := hq6eq
            _ <= (p ^ 2 * q ^ 2) * q ^ 2 := Nat.mul_le_mul_right (q ^ 2)
                  (Nat.mul_le_mul_right (q ^ 2) hsqqp)
            _ <= (p ^ 2 * q ^ 2) * r ^ 2 := Nat.mul_le_mul_left (p ^ 2 * q ^ 2) hsqqr
            _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl
        exact lt_of_lt_of_le hq6 hq6le
      · have hrqle' : r <= q := hrqle
        have hrple : r <= p := le_trans hrqle' hqple'
        have hsqrp : r ^ 2 <= p ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hrple hrple
        have hsqrq : r ^ 2 <= q ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hrqle' hrqle'
        have hr6le : r ^ 6 <= p ^ 2 * q ^ 2 * r ^ 2 := by
          calc
            r ^ 6 = (r ^ 2 * r ^ 2) * r ^ 2 := hr6eq
            _ <= (p ^ 2 * r ^ 2) * r ^ 2 := Nat.mul_le_mul_right (r ^ 2)
                  (Nat.mul_le_mul_right (r ^ 2) hsqrp)
            _ <= (p ^ 2 * q ^ 2) * r ^ 2 := Nat.mul_le_mul_right (r ^ 2)
                  (Nat.mul_le_mul_left (p ^ 2) hsqrq)
            _ = p ^ 2 * q ^ 2 * r ^ 2 := by ac_rfl
        exact lt_of_lt_of_le hr6 hr6le
  have hmLe : M n k <= n := by
    unfold M
    exact Nat.sub_le n (2 ^ k)
  have hprodLe : p ^ 2 * q ^ 2 * r ^ 2 <= M n k := by
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt (C1 hkK)) hprodDvd
  exact (Nat.lt_irrefl n) (lt_of_lt_of_le hprodGt (le_trans hprodLe hmLe))

lemma sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK (n : Nat) :
    Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) <= (K n).card * 2 := by
  classical
  let T : Finset (Sigma fun _ : Nat => Nat) := (highSixthPrimeSupportSq n).sigma (badAtSq n)
  have hcardT :
      T.card = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) := by
    dsimp [T]
    simp [card_badAtSq_eq_Np]
  have hmaps : ∀ x : Sigma fun _ : Nat => Nat, x ∈ T → x.2 ∈ K n := by
    intro x hx
    have hx' : x.1 ∈ highSixthPrimeSupportSq n ∧ x.2 ∈ badAtSq n x.1 := by
      simpa [T] using hx
    exact (Finset.mem_filter.mp hx'.2).1
  have hfiber : ∀ k ∈ K n, (T.filter fun x => x.2 = k).card <= 2 := by
    intro k hk
    have hEq :
        (T.filter fun x => x.2 = k).card =
          ((highSixthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card := by
      dsimp [T]
      refine Finset.card_bij'
        (fun x _ => x.1)
        (fun p _ => ⟨p, k⟩) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxT, hxk⟩
        rcases Finset.mem_sigma.mp hxT with ⟨hxHigh, hxBad⟩
        exact Finset.mem_filter.mpr ⟨hxHigh, by simpa [hxk] using hxBad⟩
      · intro p hp
        refine Finset.mem_filter.mpr ⟨?_, rfl⟩
        rcases Finset.mem_filter.mp hp with ⟨hpHigh, hpBad⟩
        exact Finset.mem_sigma.mpr ⟨hpHigh, by simpa using hpBad⟩
      · intro x hx
        rcases x with ⟨p, l⟩
        rcases Finset.mem_filter.mp hx with ⟨_, hlk⟩
        cases hlk
        rfl
      · intro p hp
        rfl
    calc
      (T.filter fun x => x.2 = k).card =
          ((highSixthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card := hEq
      _ <= 2 := card_highSixthPrimeSupportSq_filter_badAtSq_le_two n k
  calc
    Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) = T.card := by
      symm
      exact hcardT
    _ = ∑ k ∈ K n, (T.filter fun x => x.2 = k).card := by
      have hmapsTo : Set.MapsTo (fun x : Sigma fun _ : Nat => Nat => x.2)
          (T : Set (Sigma fun _ : Nat => Nat)) (K n : Set Nat) := by
        intro x hx
        exact hmaps x hx
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun x : Sigma fun _ : Nat => Nat => x.2) (s := T) (t := K n) hmapsTo)
    _ <= ∑ _k ∈ K n, 2 := by
      exact Finset.sum_le_sum hfiber
    _ = (K n).card * 2 := by simp [Nat.mul_comm]

lemma sum_Np_highFifthPrimeSupportSq_le_two_mul_cardK (n : Nat) :
    Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) <= (K n).card * 2 := by
  classical
  let T : Finset (Sigma fun _ : Nat => Nat) := (highFifthPrimeSupportSq n).sigma (badAtSq n)
  have hcardT :
      T.card = Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) := by
    dsimp [T]
    simp [card_badAtSq_eq_Np]
  have hmaps : ∀ x : Sigma fun _ : Nat => Nat, x ∈ T → x.2 ∈ K n := by
    intro x hx
    have hx' : x.1 ∈ highFifthPrimeSupportSq n ∧ x.2 ∈ badAtSq n x.1 := by
      simpa [T] using hx
    exact (Finset.mem_filter.mp hx'.2).1
  have hfiber : ∀ k ∈ K n, (T.filter fun x => x.2 = k).card <= 2 := by
    intro k hk
    have hEq :
        (T.filter fun x => x.2 = k).card =
          ((highFifthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card := by
      dsimp [T]
      refine Finset.card_bij'
        (fun x _ => x.1)
        (fun p _ => ⟨p, k⟩) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxT, hxk⟩
        rcases Finset.mem_sigma.mp hxT with ⟨hxHigh, hxBad⟩
        exact Finset.mem_filter.mpr ⟨hxHigh, by simpa [hxk] using hxBad⟩
      · intro p hp
        refine Finset.mem_filter.mpr ⟨?_, rfl⟩
        rcases Finset.mem_filter.mp hp with ⟨hpHigh, hpBad⟩
        exact Finset.mem_sigma.mpr ⟨hpHigh, by simpa using hpBad⟩
      · intro x hx
        rcases x with ⟨p, l⟩
        rcases Finset.mem_filter.mp hx with ⟨_, hlk⟩
        cases hlk
        rfl
      · intro p hp
        rfl
    calc
      (T.filter fun x => x.2 = k).card =
          ((highFifthPrimeSupportSq n).filter (fun p => k ∈ badAtSq n p)).card := hEq
      _ <= 2 := card_highFifthPrimeSupportSq_filter_badAtSq_le_two n k
  calc
    Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) = T.card := by
      symm
      exact hcardT
    _ = ∑ k ∈ K n, (T.filter fun x => x.2 = k).card := by
      have hmapsTo : Set.MapsTo (fun x : Sigma fun _ : Nat => Nat => x.2)
          (T : Set (Sigma fun _ : Nat => Nat)) (K n : Set Nat) := by
        intro x hx
        exact hmaps x hx
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (f := fun x : Sigma fun _ : Nat => Nat => x.2) (s := T) (t := K n) hmapsTo)
    _ <= ∑ _k ∈ K n, 2 := by
      exact Finset.sum_le_sum hfiber
    _ = (K n).card * 2 := by simp [Nat.mul_comm]

lemma sum_Np_lowFifthPrimeSupportSq_eq_sum_lowFifthPrimeActiveSupportSq (n : Nat) :
    Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) =
      Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
  classical
  simpa [lowFifthPrimeActiveSupportSq] using
    (Finset.sum_filter_ne_zero (s := lowFifthPrimeSupportSq n) (f := fun p => Np n p))

lemma sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq (n : Nat) :
    Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) =
      Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
  classical
  simpa [lowSixthPrimeActiveSupportSq] using
    (Finset.sum_filter_ne_zero (s := lowSixthPrimeSupportSq n) (f := fun p => Np n p))

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

/--
For exponents in range (`2^k ≤ n`), divisibility of `n - 2^k` by `p^2`
is equivalent to the congruence `2^k ≡ n [MOD p^2]`.
-/
lemma M_mod_sq_iff_two_pow_modEq {n p k : Nat} (hk : 2 ^ k <= n) :
    (M n k) % (p ^ 2) = 0 ↔ 2 ^ k ≡ n [MOD p ^ 2] := by
  unfold M
  constructor
  · intro hmod
    exact (Nat.modEq_iff_dvd' hk).2 (Nat.dvd_of_mod_eq_zero hmod)
  · intro hmod
    exact Nat.mod_eq_zero_of_dvd ((Nat.modEq_iff_dvd' hk).1 hmod)

/-- Unpack the `Np` filter predicate into a congruence class condition. -/
lemma mem_Np_filter_iff_two_pow_modEq {n p k : Nat} :
    k ∈ (K n).filter (fun t => (M n t) % (p ^ 2) = 0) ↔
      k ∈ K n ∧ 2 ^ k ≡ n [MOD p ^ 2] := by
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkK, hmod⟩
    have hkLe : 2 ^ k <= n := le_of_lt (C1 hkK)
    exact ⟨hkK, (M_mod_sq_iff_two_pow_modEq hkLe).1 hmod⟩
  · intro hk
    rcases hk with ⟨hkK, hmod⟩
    have hkLe : 2 ^ k <= n := le_of_lt (C1 hkK)
    exact Finset.mem_filter.mpr ⟨hkK, (M_mod_sq_iff_two_pow_modEq hkLe).2 hmod⟩

/--
If two exponents yield the same residue modulo `p^2` and both target a unit class,
then they are congruent modulo the order of `2` in `(ZMod (p^2))ˣ`.
-/
lemma exponents_modEq_order_of_two_unit
    {n p k l : Nat}
    (h2cop : Nat.Coprime 2 (p ^ 2))
    (hncop : Nat.Coprime n (p ^ 2))
    (hk : 2 ^ k ≡ n [MOD p ^ 2])
    (hl : 2 ^ l ≡ n [MOD p ^ 2]) :
    k ≡ l [MOD orderOf (ZMod.unitOfCoprime 2 h2cop)] := by
  let u : (ZMod (p ^ 2))ˣ := ZMod.unitOfCoprime 2 h2cop
  let v : (ZMod (p ^ 2))ˣ := ZMod.unitOfCoprime n hncop
  have hk' : u ^ k = v := by
    apply Units.ext
    calc
      ((u ^ k : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) = ((2 : ZMod (p ^ 2)) ^ k) := by
        simp [u]
      _ = (n : ZMod (p ^ 2)) := by
        simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2 ^ k) n (p ^ 2)).2 hk
      _ = ((v : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) := by
        simp [v]
  have hl' : u ^ l = v := by
    apply Units.ext
    calc
      ((u ^ l : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) = ((2 : ZMod (p ^ 2)) ^ l) := by
        simp [u]
      _ = (n : ZMod (p ^ 2)) := by
        simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff (2 ^ l) n (p ^ 2)).2 hl
      _ = ((v : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) := by
        simp [v]
  have hEq : u ^ k = u ^ l := hk'.trans hl'.symm
  exact (pow_eq_pow_iff_modEq).1 hEq

/--
For odd primes dividing `n`, the congruence `2^k ≡ n [MOD p]` is impossible.
-/
lemma not_two_pow_modEq_of_prime_dvd_n
    {n p k : Nat}
    (hp : Nat.Prime p) (hpne2 : p ≠ 2) (hpn : p ∣ n) :
    ¬ (2 ^ k ≡ n [MOD p]) := by
  intro hk
  have hdivPow : p ∣ 2 ^ k := (hk.dvd_iff (dvd_refl p)).2 hpn
  have hdiv2 : p ∣ 2 := hp.dvd_of_dvd_pow hdivPow
  have hpEq2 : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv2 with hp1 | hp2
    · exact (hp.ne_one hp1).elim
    · exact hp2
  exact hpne2 hpEq2

/--
For odd primes dividing `n`, the stronger congruence `2^k ≡ n [MOD p^2]` is impossible.
-/
lemma not_two_pow_modEq_sq_of_prime_dvd_n
    {n p k : Nat}
    (hp : Nat.Prime p) (hpne2 : p ≠ 2) (hpn : p ∣ n) :
    ¬ (2 ^ k ≡ n [MOD p ^ 2]) := by
  intro hk
  have hk2 : 2 ^ k ≡ n [MOD p * p] := by simpa [pow_two] using hk
  have hk' : 2 ^ k ≡ n [MOD p] := Nat.ModEq.of_dvd (dvd_mul_right p p) hk2
  exact not_two_pow_modEq_of_prime_dvd_n hp hpne2 hpn hk'

/--
Consequently, if an odd prime `p` divides `n`, then the local count at `p` is zero.
-/
lemma Np_eq_zero_of_prime_ne_two_dvd_n
    {n p : Nat}
    (hp : Nat.Prime p) (hpne2 : p ≠ 2) (hpn : p ∣ n) :
    Np n p = 0 := by
  unfold Np
  apply Finset.card_eq_zero.mpr
  exact Finset.eq_empty_iff_forall_notMem.mpr (by
    intro k hk
    exact not_two_pow_modEq_sq_of_prime_dvd_n hp hpne2 hpn
      (mem_Np_filter_iff_two_pow_modEq.1 hk).2)

/--
If `p^2 > n`, then no exponent `k ∈ K n` can satisfy `(M n k) % p^2 = 0`,
so the local count is zero.
-/
lemma Np_eq_zero_of_sq_gt {n p : Nat} (hgt : n < p ^ 2) :
    Np n p = 0 := by
  unfold Np
  apply Finset.card_eq_zero.mpr
  exact Finset.eq_empty_iff_forall_notMem.mpr (by
    intro k hk
    have hkK : k ∈ K n := (Finset.mem_filter.mp hk).1
    have hmod0 : (M n k) % (p ^ 2) = 0 := (Finset.mem_filter.mp hk).2
    have hklt : 2 ^ k < n := C1 hkK
    have hmPos : 0 < M n k := by
      unfold M
      exact Nat.sub_pos_of_lt hklt
    have hmLe : M n k <= n := Nat.sub_le _ _
    have hmLt : M n k < p ^ 2 := lt_of_le_of_lt hmLe hgt
    have hmZero : M n k = 0 := by
      have hmodEq : (M n k) % (p ^ 2) = M n k := Nat.mod_eq_of_lt hmLt
      simpa [hmodEq] using hmod0
    exact (Nat.ne_of_gt hmPos) hmZero)

/-- A congruence class in `range b` has size at most `b / r + 1`. -/
lemma card_range_modEq_le_div_add_one {b r v : Nat} (hr : 0 < r) :
    {x ∈ Finset.range b | x ≡ v [MOD r]}.card <= b / r + 1 := by
  have hcount := Nat.count_modEq_card b hr v
  rw [Nat.count_eq_card_filter_range] at hcount
  rw [hcount]
  by_cases hlt : v % r < b % r
  · simp [hlt]
  · simp [hlt]

/-- A residue class in `range b` has size at least `b / r`. -/
lemma card_range_modEq_ge_div {b r v : Nat} (hr : 0 < r) :
    b / r <= {x ∈ Finset.range b | x ≡ v [MOD r]}.card := by
  have hcount := Nat.count_modEq_card b hr v
  rw [Nat.count_eq_card_filter_range] at hcount
  rw [hcount]
  by_cases hlt : v % r < b % r
  · simp [hlt]
  · simp [hlt]

lemma six_mul_sub_div_six_le (m : Nat) :
    6 * (m + 1 - m / 6) <= 5 * m + 11 := by
  let q : Nat := m / 6
  let r : Nat := m % 6
  have hrlt : r < 6 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide : 0 < 6)
  have hm : m = r + 6 * q := by
    dsimp [r, q]
    exact (Nat.mod_add_div m 6).symm
  have hdiv : (r + 6 * q) / 6 = q := by
    calc
      (r + 6 * q) / 6 = r / 6 + q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.add_mul_div_left r q (by decide : 0 < 6)
      _ = q := by
        simp [Nat.div_eq_of_lt hrlt]
  rw [hm, hdiv]
  omega

lemma d_mul_fiveL_add11_lt_six_mul_aL {a d L0 : Nat}
    (hRate : 5 * d < 6 * a) (hL : 11 * d + 1 <= L0) :
    d * (5 * L0 + 11) < 6 * (a * L0) := by
  have hdeltaPos : 0 < 6 * a - 5 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 6 * a - 5 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 11 * d + 1 <= (6 * a - 5 * d) * L0 := by
    have hmul : L0 <= (6 * a - 5 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (6 * a - 5 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have h11lt : 11 * d < (6 * a - 5 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (11 * d)) hLm
  have hsum :
      5 * (d * L0) + 11 * d < 5 * (d * L0) + (6 * a - 5 * d) * L0 := by
    exact Nat.add_lt_add_left h11lt (5 * (d * L0))
  have hleft :
      d * (5 * L0 + 11) = 5 * (d * L0) + 11 * d := by
    calc
      d * (5 * L0 + 11) = d * (5 * L0) + d * 11 := by rw [Nat.mul_add]
      _ = 5 * (d * L0) + 11 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      5 * (d * L0) + (6 * a - 5 * d) * L0 = 6 * (a * L0) := by
    calc
      5 * (d * L0) + (6 * a - 5 * d) * L0 =
          (5 * d) * L0 + (6 * a - 5 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((5 * d) + (6 * a - 5 * d)) * L0 := by rw [Nat.add_mul]
      _ = (6 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 6 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma sixty_mul_sub_div_six_add_div_twenty_le (m : Nat) :
    60 * (m + 1 - (m / 6 + m / 20)) <= 47 * m + 167 := by
  have h6mod : m % 6 <= 5 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 6))
  have h20mod : m % 20 <= 19 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 20))
  have h6 : m <= 6 * (m / 6) + 5 := by
    have hm : m % 6 + 6 * (m / 6) = m := Nat.mod_add_div m 6
    omega
  have h20 : m <= 20 * (m / 20) + 19 := by
    have hm : m % 20 + 20 * (m / 20) = m := Nat.mod_add_div m 20
    omega
  have h10 : 10 * m <= 60 * (m / 6) + 50 := by
    omega
  have h3 : 3 * m <= 60 * (m / 20) + 57 := by
    omega
  have h13 : 13 * m <= 60 * (m / 6) + 60 * (m / 20) + 107 := by
    omega
  omega

lemma d_mul_47L_add167_lt_sixty_mul_aL {a d L0 : Nat}
    (hRate : 47 * d < 60 * a) (hL : 167 * d + 1 <= L0) :
    d * (47 * L0 + 167) < 60 * (a * L0) := by
  have hdeltaPos : 0 < 60 * a - 47 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 60 * a - 47 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 167 * d + 1 <= (60 * a - 47 * d) * L0 := by
    have hmul : L0 <= (60 * a - 47 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (60 * a - 47 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have h167lt : 167 * d < (60 * a - 47 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (167 * d)) hLm
  have hsum :
      47 * (d * L0) + 167 * d < 47 * (d * L0) + (60 * a - 47 * d) * L0 := by
    exact Nat.add_lt_add_left h167lt (47 * (d * L0))
  have hleft :
      d * (47 * L0 + 167) = 47 * (d * L0) + 167 * d := by
    calc
      d * (47 * L0 + 167) = d * (47 * L0) + d * 167 := by rw [Nat.mul_add]
      _ = 47 * (d * L0) + 167 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      47 * (d * L0) + (60 * a - 47 * d) * L0 = 60 * (a * L0) := by
    calc
      47 * (d * L0) + (60 * a - 47 * d) * L0 =
          (47 * d) * L0 + (60 * a - 47 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((47 * d) + (60 * a - 47 * d)) * L0 := by rw [Nat.add_mul]
      _ = (60 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 60 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma fourtwenty_mul_sub_div_six_add_div_twenty_add_div_forty_two_le (m : Nat) :
    420 * (m + 1 - (m / 6 + m / 20 + m / 42)) <= 319 * m + 1579 := by
  have h6mod : m % 6 <= 5 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 6))
  have h20mod : m % 20 <= 19 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 20))
  have h42mod : m % 42 <= 41 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 42))
  have h6 : m <= 6 * (m / 6) + 5 := by
    have hm : m % 6 + 6 * (m / 6) = m := Nat.mod_add_div m 6
    omega
  have h20 : m <= 20 * (m / 20) + 19 := by
    have hm : m % 20 + 20 * (m / 20) = m := Nat.mod_add_div m 20
    omega
  have h42 : m <= 42 * (m / 42) + 41 := by
    have hm : m % 42 + 42 * (m / 42) = m := Nat.mod_add_div m 42
    omega
  have h70 : 70 * m <= 420 * (m / 6) + 350 := by omega
  have h21 : 21 * m <= 420 * (m / 20) + 399 := by omega
  have h10 : 10 * m <= 420 * (m / 42) + 410 := by omega
  have h101 : 101 * m <= 420 * (m / 6) + 420 * (m / 20) + 420 * (m / 42) + 1159 := by
    omega
  omega

lemma d_mul_319L_add1579_lt_fourtwenty_mul_aL {a d L0 : Nat}
    (hRate : 319 * d < 420 * a) (hL : 1579 * d + 1 <= L0) :
    d * (319 * L0 + 1579) < 420 * (a * L0) := by
  have hdeltaPos : 0 < 420 * a - 319 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 420 * a - 319 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 1579 * d + 1 <= (420 * a - 319 * d) * L0 := by
    have hmul : L0 <= (420 * a - 319 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (420 * a - 319 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have h1579lt : 1579 * d < (420 * a - 319 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (1579 * d)) hLm
  have hsum :
      319 * (d * L0) + 1579 * d < 319 * (d * L0) + (420 * a - 319 * d) * L0 := by
    exact Nat.add_lt_add_left h1579lt (319 * (d * L0))
  have hleft :
      d * (319 * L0 + 1579) = 319 * (d * L0) + 1579 * d := by
    calc
      d * (319 * L0 + 1579) = d * (319 * L0) + d * 1579 := by rw [Nat.mul_add]
      _ = 319 * (d * L0) + 1579 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      319 * (d * L0) + (420 * a - 319 * d) * L0 = 420 * (a * L0) := by
    calc
      319 * (d * L0) + (420 * a - 319 * d) * L0 =
          (319 * d) * L0 + (420 * a - 319 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((319 * d) + (420 * a - 319 * d)) * L0 := by rw [Nat.add_mul]
      _ = (420 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 420 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma f4620_bound (m : Nat) :
    4620 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110)) <= 3467 * m + 21947 := by
  have h6mod : m % 6 <= 5 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 6))
  have h20mod : m % 20 <= 19 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 20))
  have h42mod : m % 42 <= 41 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 42))
  have h110mod : m % 110 <= 109 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 110))
  have h6 : m <= 6 * (m / 6) + 5 := by
    have hm : m % 6 + 6 * (m / 6) = m := Nat.mod_add_div m 6
    omega
  have h20 : m <= 20 * (m / 20) + 19 := by
    have hm : m % 20 + 20 * (m / 20) = m := Nat.mod_add_div m 20
    omega
  have h42 : m <= 42 * (m / 42) + 41 := by
    have hm : m % 42 + 42 * (m / 42) = m := Nat.mod_add_div m 42
    omega
  have h110 : m <= 110 * (m / 110) + 109 := by
    have hm : m % 110 + 110 * (m / 110) = m := Nat.mod_add_div m 110
    omega
  have h770 : 770 * m <= 4620 * (m / 6) + 3850 := by omega
  have h231 : 231 * m <= 4620 * (m / 20) + 4389 := by omega
  have h110c : 110 * m <= 4620 * (m / 42) + 4510 := by omega
  have h42c : 42 * m <= 4620 * (m / 110) + 4578 := by omega
  have h1153 :
      1153 * m <=
        4620 * (m / 6) + 4620 * (m / 20) + 4620 * (m / 42) + 4620 * (m / 110) + 17327 := by
    omega
  omega

lemma d_mul_3467L_add21947_lt_4620_mul_aL {a d L0 : Nat}
    (hRate : 3467 * d < 4620 * a) (hL : 21947 * d + 1 <= L0) :
    d * (3467 * L0 + 21947) < 4620 * (a * L0) := by
  have hdeltaPos : 0 < 4620 * a - 3467 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 4620 * a - 3467 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 21947 * d + 1 <= (4620 * a - 3467 * d) * L0 := by
    have hmul : L0 <= (4620 * a - 3467 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (4620 * a - 3467 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have hC : 21947 * d < (4620 * a - 3467 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (21947 * d)) hLm
  have hsum :
      3467 * (d * L0) + 21947 * d < 3467 * (d * L0) + (4620 * a - 3467 * d) * L0 := by
    exact Nat.add_lt_add_left hC (3467 * (d * L0))
  have hleft :
      d * (3467 * L0 + 21947) = 3467 * (d * L0) + 21947 * d := by
    calc
      d * (3467 * L0 + 21947) = d * (3467 * L0) + d * 21947 := by rw [Nat.mul_add]
      _ = 3467 * (d * L0) + 21947 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      3467 * (d * L0) + (4620 * a - 3467 * d) * L0 = 4620 * (a * L0) := by
    calc
      3467 * (d * L0) + (4620 * a - 3467 * d) * L0 =
          (3467 * d) * L0 + (4620 * a - 3467 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((3467 * d) + (4620 * a - 3467 * d)) * L0 := by rw [Nat.add_mul]
      _ = (4620 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 4620 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma f60060_bound (m : Nat) :
    60060 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156)) <=
      44686 * m + 344986 := by
  have h6mod : m % 6 <= 5 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 6))
  have h20mod : m % 20 <= 19 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 20))
  have h42mod : m % 42 <= 41 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 42))
  have h110mod : m % 110 <= 109 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 110))
  have h156mod : m % 156 <= 155 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 156))
  have h6 : m <= 6 * (m / 6) + 5 := by
    have hm : m % 6 + 6 * (m / 6) = m := Nat.mod_add_div m 6
    omega
  have h20 : m <= 20 * (m / 20) + 19 := by
    have hm : m % 20 + 20 * (m / 20) = m := Nat.mod_add_div m 20
    omega
  have h42 : m <= 42 * (m / 42) + 41 := by
    have hm : m % 42 + 42 * (m / 42) = m := Nat.mod_add_div m 42
    omega
  have h110 : m <= 110 * (m / 110) + 109 := by
    have hm : m % 110 + 110 * (m / 110) = m := Nat.mod_add_div m 110
    omega
  have h156 : m <= 156 * (m / 156) + 155 := by
    have hm : m % 156 + 156 * (m / 156) = m := Nat.mod_add_div m 156
    omega
  have h10010 : 10010 * m <= 60060 * (m / 6) + 50050 := by omega
  have h3003 : 3003 * m <= 60060 * (m / 20) + 57057 := by omega
  have h1430 : 1430 * m <= 60060 * (m / 42) + 58630 := by omega
  have h546 : 546 * m <= 60060 * (m / 110) + 59514 := by omega
  have h385 : 385 * m <= 60060 * (m / 156) + 59675 := by omega
  have h15374 :
      15374 * m <=
        60060 * (m / 6) + 60060 * (m / 20) + 60060 * (m / 42) + 60060 * (m / 110) +
          60060 * (m / 156) + 284926 := by
    omega
  omega

lemma d_mul_44686L_add344986_lt_60060_mul_aL {a d L0 : Nat}
    (hRate : 44686 * d < 60060 * a) (hL : 344986 * d + 1 <= L0) :
    d * (44686 * L0 + 344986) < 60060 * (a * L0) := by
  have hdeltaPos : 0 < 60060 * a - 44686 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 60060 * a - 44686 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 344986 * d + 1 <= (60060 * a - 44686 * d) * L0 := by
    have hmul : L0 <= (60060 * a - 44686 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (60060 * a - 44686 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have hC : 344986 * d < (60060 * a - 44686 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (344986 * d)) hLm
  have hsum :
      44686 * (d * L0) + 344986 * d < 44686 * (d * L0) + (60060 * a - 44686 * d) * L0 := by
    exact Nat.add_lt_add_left hC (44686 * (d * L0))
  have hleft :
      d * (44686 * L0 + 344986) = 44686 * (d * L0) + 344986 * d := by
    calc
      d * (44686 * L0 + 344986) = d * (44686 * L0) + d * 344986 := by rw [Nat.mul_add]
      _ = 44686 * (d * L0) + 344986 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      44686 * (d * L0) + (60060 * a - 44686 * d) * L0 = 60060 * (a * L0) := by
    calc
      44686 * (d * L0) + (60060 * a - 44686 * d) * L0 =
          (44686 * d) * L0 + (60060 * a - 44686 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((44686 * d) + (60060 * a - 44686 * d)) * L0 := by rw [Nat.add_mul]
      _ = (60060 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 60060 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma f2462460_bound (m : Nat) :
    2462460 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820)) <=
      1829123 * m + 16603883 := by
  let S5 : Nat := m / 6 + m / 20 + m / 42 + m / 110 + m / 156
  have h60060 : 60060 * (m + 1 - S5) <= 44686 * m + 344986 := by
    simpa [S5, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using f60060_bound m
  have h2462460' : (m + 1 - S5) * 2462460 <= 1832126 * m + 14144426 := by
    have h41 : 41 * (60060 * (m + 1 - S5)) <= 41 * (44686 * m + 344986) :=
      Nat.mul_le_mul_left 41 h60060
    omega
  have h2462460 : 2462460 * (m + 1 - S5) <= 1832126 * m + 14144426 := by
    simpa [Nat.mul_comm] using h2462460'
  have h820mod : m % 820 <= 819 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 820))
  have h820 : m <= 820 * (m / 820) + 819 := by
    have hm : m % 820 + 820 * (m / 820) = m := Nat.mod_add_div m 820
    omega
  have h3003 : 3003 * m <= 2462460 * (m / 820) + 2459457 := by
    omega
  have hUpper :
      2462460 * (m + 1 - S5) <=
        (1829123 * m + 16603883) + 2462460 * (m / 820) := by
    have hAdjust :
        1832126 * m + 14144426 <= (1829123 * m + 16603883) + 2462460 * (m / 820) := by
      omega
    exact le_trans h2462460 hAdjust
  have hSub : 2462460 * ((m + 1 - S5) - (m / 820)) <= 1829123 * m + 16603883 := by
    rw [Nat.mul_sub_left_distrib]
    refine (Nat.sub_le_iff_le_add).2 ?_
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpper
  calc
    2462460 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820)) =
        2462460 * (m + 1 - (S5 + m / 820)) := by
          simp [S5, Nat.add_assoc]
    _ = 2462460 * ((m + 1 - S5) - (m / 820)) := by rw [Nat.sub_sub]
    _ <= 1829123 * m + 16603883 := hSub

lemma d_mul_1829123L_add16603883_lt_2462460_mul_aL {a d L0 : Nat}
    (hRate : 1829123 * d < 2462460 * a) (hL : 16603883 * d + 1 <= L0) :
    d * (1829123 * L0 + 16603883) < 2462460 * (a * L0) := by
  have hdeltaPos : 0 < 2462460 * a - 1829123 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 2462460 * a - 1829123 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 16603883 * d + 1 <= (2462460 * a - 1829123 * d) * L0 := by
    have hmul : L0 <= (2462460 * a - 1829123 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (2462460 * a - 1829123 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have hC : 16603883 * d < (2462460 * a - 1829123 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (16603883 * d)) hLm
  have hsum :
      1829123 * (d * L0) + 16603883 * d < 1829123 * (d * L0) + (2462460 * a - 1829123 * d) * L0 := by
    exact Nat.add_lt_add_left hC (1829123 * (d * L0))
  have hleft :
      d * (1829123 * L0 + 16603883) = 1829123 * (d * L0) + 16603883 * d := by
    calc
      d * (1829123 * L0 + 16603883) = d * (1829123 * L0) + d * 16603883 := by rw [Nat.mul_add]
      _ = 1829123 * (d * L0) + 16603883 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      1829123 * (d * L0) + (2462460 * a - 1829123 * d) * L0 = 2462460 * (a * L0) := by
    calc
      1829123 * (d * L0) + (2462460 * a - 1829123 * d) * L0 =
          (1829123 * d) * L0 + (2462460 * a - 1829123 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((1829123 * d) + (2462460 * a - 1829123 * d)) * L0 := by rw [Nat.add_mul]
      _ = (2462460 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 2462460 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma f273333060_bound (m : Nat) :
    273333060 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820 + m / 1332)) <=
      202827448 * m + 2116158868 := by
  let S6 : Nat := m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820
  have h246 : 2462460 * (m + 1 - S6) <= 1829123 * m + 16603883 := by
    simpa [S6, Nat.add_assoc] using f2462460_bound m
  have h273' : 273333060 * (m + 1 - S6) <= 203032653 * m + 1843031013 := by
    have h111 : 111 * (2462460 * (m + 1 - S6)) <= 111 * (1829123 * m + 16603883) :=
      Nat.mul_le_mul_left 111 h246
    omega
  have h1332mod : m % 1332 <= 1331 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 1332))
  have h1332 : m <= 1332 * (m / 1332) + 1331 := by
    have hm : m % 1332 + 1332 * (m / 1332) = m := Nat.mod_add_div m 1332
    omega
  have h205205 : 205205 * m <= 273333060 * (m / 1332) + 273127855 := by
    omega
  have hUpper :
      273333060 * (m + 1 - S6) <=
        (202827448 * m + 2116158868) + 273333060 * (m / 1332) := by
    have hAdjust :
        203032653 * m + 1843031013 <= (202827448 * m + 2116158868) + 273333060 * (m / 1332) := by
      omega
    exact le_trans h273' hAdjust
  have hSub : 273333060 * ((m + 1 - S6) - (m / 1332)) <= 202827448 * m + 2116158868 := by
    rw [Nat.mul_sub_left_distrib]
    refine (Nat.sub_le_iff_le_add).2 ?_
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpper
  calc
    273333060 * (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820 + m / 1332)) =
        273333060 * (m + 1 - (S6 + m / 1332)) := by
          simp [S6, Nat.add_assoc]
    _ = 273333060 * ((m + 1 - S6) - (m / 1332)) := by rw [Nat.sub_sub]
    _ <= 202827448 * m + 2116158868 := hSub

lemma d_mul_202827448L_add2116158868_lt_273333060_mul_aL {a d L0 : Nat}
    (hRate : 202827448 * d < 273333060 * a) (hL : 2116158868 * d + 1 <= L0) :
    d * (202827448 * L0 + 2116158868) < 273333060 * (a * L0) := by
  have hdeltaPos : 0 < 273333060 * a - 202827448 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 273333060 * a - 202827448 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 2116158868 * d + 1 <= (273333060 * a - 202827448 * d) * L0 := by
    have hmul : L0 <= (273333060 * a - 202827448 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (273333060 * a - 202827448 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have hC : 2116158868 * d < (273333060 * a - 202827448 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (2116158868 * d)) hLm
  have hsum :
      202827448 * (d * L0) + 2116158868 * d <
        202827448 * (d * L0) + (273333060 * a - 202827448 * d) * L0 := by
    exact Nat.add_lt_add_left hC (202827448 * (d * L0))
  have hleft :
      d * (202827448 * L0 + 2116158868) = 202827448 * (d * L0) + 2116158868 * d := by
    calc
      d * (202827448 * L0 + 2116158868) = d * (202827448 * L0) + d * 2116158868 := by rw [Nat.mul_add]
      _ = 202827448 * (d * L0) + 2116158868 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      202827448 * (d * L0) + (273333060 * a - 202827448 * d) * L0 = 273333060 * (a * L0) := by
    calc
      202827448 * (d * L0) + (273333060 * a - 202827448 * d) * L0 =
          (202827448 * d) * L0 + (273333060 * a - 202827448 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((202827448 * d) + (273333060 * a - 202827448 * d)) * L0 := by rw [Nat.add_mul]
      _ = (273333060 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 273333060 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

lemma f16673316660_bound (m : Nat) :
    16673316660 *
        (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820 + m / 1332 + m / 3660)) <=
      12367918777 * m + 145754452057 := by
  let S7 : Nat := m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820 + m / 1332
  have h273 : 273333060 * (m + 1 - S7) <= 202827448 * m + 2116158868 := by
    simpa [S7, Nat.add_assoc] using f273333060_bound m
  have h16673' : 16673316660 * (m + 1 - S7) <= 12372474328 * m + 129085690948 := by
    have h61 : 61 * (273333060 * (m + 1 - S7)) <= 61 * (202827448 * m + 2116158868) :=
      Nat.mul_le_mul_left 61 h273
    omega
  have h3660mod : m % 3660 <= 3659 := Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 3660))
  have h3660 : m <= 3660 * (m / 3660) + 3659 := by
    have hm : m % 3660 + 3660 * (m / 3660) = m := Nat.mod_add_div m 3660
    omega
  have h4555551 : 4555551 * m <= 16673316660 * (m / 3660) + 16668761109 := by
    omega
  have hUpper :
      16673316660 * (m + 1 - S7) <=
        (12367918777 * m + 145754452057) + 16673316660 * (m / 3660) := by
    have hAdjust :
        12372474328 * m + 129085690948 <=
          (12367918777 * m + 145754452057) + 16673316660 * (m / 3660) := by
      omega
    exact le_trans h16673' hAdjust
  have hSub : 16673316660 * ((m + 1 - S7) - (m / 3660)) <= 12367918777 * m + 145754452057 := by
    rw [Nat.mul_sub_left_distrib]
    refine (Nat.sub_le_iff_le_add).2 ?_
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpper
  calc
    16673316660 *
        (m + 1 - (m / 6 + m / 20 + m / 42 + m / 110 + m / 156 + m / 820 + m / 1332 + m / 3660)) =
        16673316660 * (m + 1 - (S7 + m / 3660)) := by
          simp [S7, Nat.add_assoc]
    _ = 16673316660 * ((m + 1 - S7) - (m / 3660)) := by rw [Nat.sub_sub]
    _ <= 12367918777 * m + 145754452057 := hSub

lemma d_mul_12367918777L_add145754452057_lt_16673316660_mul_aL {a d L0 : Nat}
    (hRate : 12367918777 * d < 16673316660 * a) (hL : 145754452057 * d + 1 <= L0) :
    d * (12367918777 * L0 + 145754452057) < 16673316660 * (a * L0) := by
  have hdeltaPos : 0 < 16673316660 * a - 12367918777 * d := Nat.sub_pos_of_lt hRate
  have hdeltaGe1 : 1 <= 16673316660 * a - 12367918777 * d := Nat.succ_le_of_lt hdeltaPos
  have hLm : 145754452057 * d + 1 <= (16673316660 * a - 12367918777 * d) * L0 := by
    have hmul : L0 <= (16673316660 * a - 12367918777 * d) * L0 := by
      calc
        L0 = 1 * L0 := by simp
        _ <= (16673316660 * a - 12367918777 * d) * L0 := Nat.mul_le_mul_right L0 hdeltaGe1
    exact le_trans hL hmul
  have hC : 145754452057 * d < (16673316660 * a - 12367918777 * d) * L0 := by
    exact lt_of_lt_of_le (Nat.lt_succ_self (145754452057 * d)) hLm
  have hsum :
      12367918777 * (d * L0) + 145754452057 * d <
        12367918777 * (d * L0) + (16673316660 * a - 12367918777 * d) * L0 := by
    exact Nat.add_lt_add_left hC (12367918777 * (d * L0))
  have hleft :
      d * (12367918777 * L0 + 145754452057) = 12367918777 * (d * L0) + 145754452057 * d := by
    calc
      d * (12367918777 * L0 + 145754452057) = d * (12367918777 * L0) + d * 145754452057 := by rw [Nat.mul_add]
      _ = 12367918777 * (d * L0) + 145754452057 * d := by
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hright :
      12367918777 * (d * L0) + (16673316660 * a - 12367918777 * d) * L0 = 16673316660 * (a * L0) := by
    calc
      12367918777 * (d * L0) + (16673316660 * a - 12367918777 * d) * L0 =
          (12367918777 * d) * L0 + (16673316660 * a - 12367918777 * d) * L0 := by
            simp [Nat.mul_assoc]
      _ = ((12367918777 * d) + (16673316660 * a - 12367918777 * d)) * L0 := by rw [Nat.add_mul]
      _ = (16673316660 * a) * L0 := by
            simp [Nat.add_sub_of_le (Nat.le_of_lt hRate)]
      _ = 16673316660 * (a * L0) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hleft ▸ (lt_of_lt_of_eq hsum hright)

/--
When `n` is a unit modulo `p^2`, all local solutions lie in one residue class
modulo the order of `2`, giving a first cardinality upper bound for `Np`.
-/
lemma Np_le_order_class_bound
    {n p : Nat}
    (h2cop : Nat.Coprime 2 (p ^ 2))
    (hncop : Nat.Coprime n (p ^ 2)) :
    Np n p <= (L n + 1) / orderOf (ZMod.unitOfCoprime 2 h2cop) + 1 := by
  classical
  let T : Nat := orderOf (ZMod.unitOfCoprime 2 h2cop)
  have hTpos : 0 < T := by
    dsimp [T]
    exact orderOf_pos (ZMod.unitOfCoprime 2 h2cop)
  let S : Finset Nat := (K n).filter (fun t => (M n t) % (p ^ 2) = 0)
  have hNp : Np n p = S.card := by
    unfold Np
    simp [S]
  rw [hNp]
  by_cases hsempty : S = ∅
  · rw [hsempty]
    simp
  · rcases Finset.nonempty_iff_ne_empty.mpr hsempty with ⟨k0, hk0S⟩
    have hk0mod : 2 ^ k0 ≡ n [MOD p ^ 2] := (mem_Np_filter_iff_two_pow_modEq.1 hk0S).2
    have hsubset :
        S ⊆ {x ∈ Finset.range (L n + 1) | x ≡ k0 [MOD T]} := by
      intro k hkS
      have hkK : k ∈ K n := (Finset.mem_filter.mp hkS).1
      have hkmod : 2 ^ k ≡ n [MOD p ^ 2] := (mem_Np_filter_iff_two_pow_modEq.1 hkS).2
      have hkT : k ≡ k0 [MOD T] := by
        dsimp [T]
        exact exponents_modEq_order_of_two_unit h2cop hncop hkmod hk0mod
      have hkLt : k < L n + 1 := by
        unfold K candidateExponents at hkK
        exact Finset.mem_range.mp (Finset.mem_filter.mp hkK).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkLt, hkT⟩
    have hcard1 :
        S.card <= {x ∈ Finset.range (L n + 1) | x ≡ k0 [MOD T]}.card :=
      Finset.card_le_card hsubset
    have hcard2 :
        {x ∈ Finset.range (L n + 1) | x ≡ k0 [MOD T]}.card <= (L n + 1) / T + 1 :=
      card_range_modEq_le_div_add_one hTpos
    exact le_trans hcard1 (by simpa [T] using hcard2)

/--
Odd-prime local bound with case split:
if `p ∣ n`, the local count is zero; otherwise we can use the order-class bound.
-/
lemma Np_le_order_class_bound_of_prime_ne_two
    {n p : Nat}
    (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    Np n p <=
      (L n + 1) /
        orderOf
          (ZMod.unitOfCoprime 2
            ((Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
              (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
                intro hdiv
                rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
                · exact hp.ne_one h1
                · exact hpne2 h2)).symm))) + 1 := by
  let h2cop : Nat.Coprime 2 (p ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
      (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm)
  by_cases hpn : p ∣ n
  · have hzero : Np n p = 0 := Np_eq_zero_of_prime_ne_two_dvd_n hp hpne2 hpn
    rw [hzero]
    exact Nat.zero_le _
  · have hncopP : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
    have hncop : Nat.Coprime n (p ^ 2) := by
      have hnp : Nat.Coprime n p := hncopP.symm
      exact (Nat.coprime_pow_right_iff (by decide : 0 < 2) n p).2 hnp
    simpa [h2cop] using Np_le_order_class_bound (n := n) (p := p) h2cop hncop

/--
Order of `2` in the unit group modulo `p` (for odd prime `p`).
-/
noncomputable def twoOrder (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) : Nat :=
  orderOf
    (ZMod.unitOfCoprime 2
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm)

lemma twoOrder_pos (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    0 < twoOrder p hp hpne2 := by
  unfold twoOrder
  exact orderOf_pos _

lemma twoOrder_dvd_pred (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    twoOrder p hp hpne2 ∣ p - 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (Units (ZMod p)) = p - 1 := by
    rw [ZMod.card_units_eq_totient p, Nat.totient_prime hp]
  unfold twoOrder
  rw [← hcard]
  exact orderOf_dvd_card

lemma twoOrder_ne_one (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    twoOrder p hp hpne2 ≠ 1 := by
  let u : (ZMod p)ˣ :=
    ZMod.unitOfCoprime 2
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm
  intro hord
  have hu1 : u = 1 := by
    have hord' : orderOf u = 1 := by simpa [twoOrder, u] using hord
    exact (orderOf_eq_one_iff).1 hord'
  have hcast : ((2 : Nat) : ZMod p) = 1 := by
    simpa [u] using congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hu1
  have honez : ((1 : Nat) : ZMod p) = 0 := by
    have hsub : (2 : ZMod p) - 1 = 1 - 1 := by
      simpa using congrArg (fun x : ZMod p => x - 1) hcast
    calc
      ((1 : Nat) : ZMod p) = (2 : ZMod p) - 1 := by norm_num
      _ = 1 - 1 := hsub
      _ = 0 := by simp
  have hdiv1 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 honez
  exact hp.ne_one (Nat.dvd_one.mp hdiv1)

lemma twoOrder_ne_two_of_prime_ne_three (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hpne3 : p ≠ 3) :
    twoOrder p hp hpne2 ≠ 2 := by
  let u : (ZMod p)ˣ :=
    ZMod.unitOfCoprime 2
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm
  intro hord
  have hu2 : u ^ 2 = 1 := by
    have hord' : orderOf u = 2 := by simpa [twoOrder, u] using hord
    simpa [hord'] using pow_orderOf_eq_one u
  have hpow : ((2 : ZMod p) ^ 2) = (1 : ZMod p) := by
    simpa [u, Nat.cast_pow] using congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hu2
  have hthreez : ((3 : Nat) : ZMod p) = 0 := by
    calc
      ((3 : Nat) : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by norm_num
      _ = (1 : ZMod p) - 1 := by simp [hpow]
      _ = 0 := by simp
  have hdiv3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 hthreez
  rcases (Nat.dvd_prime Nat.prime_three).1 hdiv3 with h1 | h3
  · exact hp.ne_one h1
  · exact hpne3 h3

lemma three_le_twoOrder_of_prime_ne_three (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hpne3 : p ≠ 3) :
    3 <= twoOrder p hp hpne2 := by
  have hpos : 0 < twoOrder p hp hpne2 := twoOrder_pos p hp hpne2
  have hne1 : twoOrder p hp hpne2 ≠ 1 := twoOrder_ne_one p hp hpne2
  have hne2 : twoOrder p hp hpne2 ≠ 2 := twoOrder_ne_two_of_prime_ne_three p hp hpne2 hpne3
  omega

/--
Order of `2` in the unit group modulo `p^2` (for odd prime `p`).
-/
noncomputable def twoOrderSq (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) : Nat :=
  orderOf
    (ZMod.unitOfCoprime 2
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
        (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
          intro hdiv
          rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
          · exact hp.ne_one h1
          · exact hpne2 h2)).symm)))

lemma twoOrderSq_pos (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    0 < twoOrderSq p hp hpne2 := by
  unfold twoOrderSq
  exact orderOf_pos _

lemma twoOrderSq_ge_two (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    2 <= twoOrderSq p hp hpne2 := by
  unfold twoOrderSq
  let u : (ZMod (p ^ 2))ˣ :=
    ZMod.unitOfCoprime 2
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
        (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
          intro hdiv
          rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
          · exact hp.ne_one h1
          · exact hpne2 h2)).symm))
  have huPos : 0 < orderOf u := orderOf_pos u
  have huNeOne : u ≠ 1 := by
    intro hu1
    have hcast : ((2 : ZMod (p ^ 2)) : ZMod (p ^ 2)) = (1 : ZMod (p ^ 2)) := by
      exact by simpa [u] using congrArg (fun x : (ZMod (p ^ 2))ˣ => (x : ZMod (p ^ 2))) hu1
    have honez : ((1 : Nat) : ZMod (p ^ 2)) = 0 := by
      calc
        ((1 : Nat) : ZMod (p ^ 2)) = (2 : ZMod (p ^ 2)) - 1 := by norm_num
        _ = (1 : ZMod (p ^ 2)) - 1 := by simp [hcast]
        _ = 0 := by simp
    have hdiv1 : p ^ 2 ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (p ^ 2)).1 honez
    have hp_le_sq : p <= p ^ 2 := by
      calc
        p = p * 1 := by simp
        _ <= p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hp.pos)
        _ = p ^ 2 := by simp [pow_two]
    have hsqNeOne : p ^ 2 ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le hp.one_lt hp_le_sq)
    exact hsqNeOne (Nat.dvd_one.mp hdiv1)
  have hordNeOne : orderOf u ≠ 1 := by
    intro hord1
    exact huNeOne ((orderOf_eq_one_iff).1 hord1)
  exact (Nat.two_le_iff (orderOf u)).2 ⟨Nat.ne_of_gt huPos, hordNeOne⟩

lemma twoOrderSq_dvd_p_mul_pred (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    twoOrderSq p hp hpne2 ∣ p * (p - 1) := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcard : Fintype.card (Units (ZMod (p ^ 2))) = p * (p - 1) := by
    rw [ZMod.card_units_eq_totient (p ^ 2)]
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.totient_prime_pow_succ hp 1)
  unfold twoOrderSq
  rw [← hcard]
  exact orderOf_dvd_card

lemma sq_dvd_two_pow_twoOrderSq_sub_one
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    p ^ 2 ∣ 2 ^ twoOrderSq p hp hpne2 - 1 := by
  let h2cop : Nat.Coprime 2 (p ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
      (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm)
  have hu :
      (ZMod.unitOfCoprime 2 h2cop : (ZMod (p ^ 2))ˣ) ^ twoOrderSq p hp hpne2 = 1 := by
    unfold twoOrderSq
    simpa using pow_orderOf_eq_one (ZMod.unitOfCoprime 2 h2cop)
  have hpow :
      ((2 : ZMod (p ^ 2)) ^ twoOrderSq p hp hpne2) = (1 : ZMod (p ^ 2)) := by
    simpa [h2cop, Nat.cast_pow] using
      congrArg (fun x : (ZMod (p ^ 2))ˣ => (x : ZMod (p ^ 2))) hu
  have hmod : 2 ^ twoOrderSq p hp hpne2 ≡ 1 [MOD p ^ 2] :=
    (ZMod.natCast_eq_natCast_iff (2 ^ twoOrderSq p hp hpne2) 1 (p ^ 2)).1 <| by
      simpa [Nat.cast_pow] using hpow
  have hpowPos : 1 <= 2 ^ twoOrderSq p hp hpne2 := by
    exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
  exact (Nat.modEq_iff_dvd' hpowPos).1 hmod.symm

lemma lt_twoOrderSq_of_two_pow_lt_sq
    (p d : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hpow : 2 ^ d < p ^ 2) :
    d < twoOrderSq p hp hpne2 := by
  by_contra hd
  have hOrdLe : twoOrderSq p hp hpne2 <= d := Nat.not_lt.mp hd
  have hpowPos : 0 < 2 ^ twoOrderSq p hp hpne2 - 1 := by
    have hpowGe : 2 <= 2 ^ twoOrderSq p hp hpne2 := by
      have hOrdPos : 1 <= twoOrderSq p hp hpne2 := Nat.succ_le_of_lt (twoOrderSq_pos p hp hpne2)
      calc
        2 = 2 ^ 1 := by norm_num
        _ <= 2 ^ twoOrderSq p hp hpne2 := by
          exact Nat.pow_le_pow_right (by decide : 1 <= 2) hOrdPos
    omega
  have hsqLe : p ^ 2 <= 2 ^ twoOrderSq p hp hpne2 - 1 := by
    exact Nat.le_of_dvd hpowPos (sq_dvd_two_pow_twoOrderSq_sub_one p hp hpne2)
  have hpowLe : 2 ^ twoOrderSq p hp hpne2 <= 2 ^ d := by
    exact Nat.pow_le_pow_right (by decide : 1 <= 2) hOrdLe
  have hlt :
      2 ^ twoOrderSq p hp hpne2 - 1 < p ^ 2 := by
    calc
      2 ^ twoOrderSq p hp hpne2 - 1 < 2 ^ twoOrderSq p hp hpne2 := by
        exact Nat.sub_lt (pow_pos (by decide : 0 < 2) _) (by decide : 0 < 1)
      _ <= 2 ^ d := hpowLe
      _ < p ^ 2 := hpow
  exact (Nat.lt_irrefl (p ^ 2)) (lt_of_le_of_lt hsqLe hlt)

lemma twoOrder_dvd_twoOrderSq (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    twoOrder p hp hpne2 ∣ twoOrderSq p hp hpne2 := by
  let u : (ZMod p)ˣ :=
    ZMod.unitOfCoprime 2
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm
  let uSq : (ZMod (p ^ 2))ˣ :=
    ZMod.unitOfCoprime 2
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
        (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
          intro hdiv
          rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
          · exact hp.ne_one h1
          · exact hpne2 h2)).symm))
  have hm : p ∣ p ^ 2 := by
    simpa [pow_two] using Nat.dvd_mul_right p p
  have hmap : ZMod.unitsMap hm uSq = u := by
    apply Units.ext
    calc
      ↑((ZMod.unitsMap hm) uSq) = (((2 : ZMod (p ^ 2)).cast) : ZMod p) := by
        simpa [uSq] using (ZMod.unitsMap_val hm uSq)
      _ = (2 : ZMod p) := by
            simpa using (ZMod.cast_natCast hm 2 : (((2 : ZMod (p ^ 2)).cast) : ZMod p) = _)
      _ = ↑u := by simp [u]
  have h := orderOf_map_dvd (ZMod.unitsMap hm) uSq
  simpa [twoOrder, twoOrderSq, u, uSq, hmap] using h

lemma three_le_twoOrderSq_of_prime_ne_three (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hpne3 : p ≠ 3) :
    3 <= twoOrderSq p hp hpne2 := by
  exact le_trans
    (three_le_twoOrder_of_prime_ne_three p hp hpne2 hpne3)
    (Nat.le_of_dvd (twoOrderSq_pos p hp hpne2) (twoOrder_dvd_twoOrderSq p hp hpne2))

lemma wieferichBase2_of_twoOrderSq_dvd_pred
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hdvd : twoOrderSq p hp hpne2 ∣ p - 1) :
    WieferichBase2 p := by
  let h2cop : Nat.Coprime 2 (p ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) 2 p).2
      (((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        intro hdiv
        rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h2
        · exact hp.ne_one h1
        · exact hpne2 h2)).symm)
  have hu :
      (ZMod.unitOfCoprime 2 h2cop : (ZMod (p ^ 2))ˣ) ^ (p - 1) = 1 := by
    rcases hdvd with ⟨m, hm⟩
    unfold twoOrderSq at hm
    rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hpow :
      ((2 : ZMod (p ^ 2)) ^ (p - 1)) = (1 : ZMod (p ^ 2)) := by
    simpa [h2cop, Nat.cast_pow] using
      congrArg (fun x : (ZMod (p ^ 2))ˣ => (x : ZMod (p ^ 2))) hu
  exact (ZMod.natCast_eq_natCast_iff (2 ^ (p - 1)) 1 (p ^ 2)).1 <| by
    simpa [Nat.cast_pow] using hpow

lemma dvd_twoOrderSq_of_not_wieferichBase2
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hNotWieferich : ¬ WieferichBase2 p) :
    p ∣ twoOrderSq p hp hpne2 := by
  by_contra hNotDvd
  have hcop : Nat.Coprime p (twoOrderSq p hp hpne2) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hNotDvd
  have hpred : twoOrderSq p hp hpne2 ∣ p - 1 :=
    hcop.symm.dvd_of_dvd_mul_left (twoOrderSq_dvd_p_mul_pred p hp hpne2)
  exact hNotWieferich (wieferichBase2_of_twoOrderSq_dvd_pred p hp hpne2 hpred)

lemma le_twoOrderSq_of_not_wieferichBase2
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hNotWieferich : ¬ WieferichBase2 p) :
    p <= twoOrderSq p hp hpne2 := by
  exact Nat.le_of_dvd (twoOrderSq_pos p hp hpne2)
    (dvd_twoOrderSq_of_not_wieferichBase2 p hp hpne2 hNotWieferich)

lemma coprime_prime_twoOrder (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    Nat.Coprime p (twoOrder p hp hpne2) := by
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    have hpred : p ∣ p - 1 := dvd_trans hdiv (twoOrder_dvd_pred p hp hpne2)
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hle : p <= p - 1 := Nat.le_of_dvd hpos hpred
    omega)

lemma p_mul_twoOrder_dvd_twoOrderSq_of_not_wieferichBase2
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (hNotWieferich : ¬ WieferichBase2 p) :
    p * twoOrder p hp hpne2 ∣ twoOrderSq p hp hpne2 := by
  exact (coprime_prime_twoOrder p hp hpne2).mul_dvd_of_dvd_of_dvd
    (dvd_twoOrderSq_of_not_wieferichBase2 p hp hpne2 hNotWieferich)
    (twoOrder_dvd_twoOrderSq p hp hpne2)

lemma three_mul_le_twoOrderSq_of_not_wieferichBase2
    (p : Nat) (hp : Nat.Prime p) (hpne2 : p ≠ 2) (hpne3 : p ≠ 3)
    (hNotWieferich : ¬ WieferichBase2 p) :
    3 * p <= twoOrderSq p hp hpne2 := by
  have hmulDvd :
      p * twoOrder p hp hpne2 ∣ twoOrderSq p hp hpne2 :=
    p_mul_twoOrder_dvd_twoOrderSq_of_not_wieferichBase2 p hp hpne2 hNotWieferich
  have hmulLe :
      p * twoOrder p hp hpne2 <= twoOrderSq p hp hpne2 := by
    exact Nat.le_of_dvd (twoOrderSq_pos p hp hpne2) hmulDvd
  calc
    3 * p <= p * twoOrder p hp hpne2 := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mul_le_mul_left p (three_le_twoOrder_of_prime_ne_three p hp hpne2 hpne3))
    _ <= twoOrderSq p hp hpne2 := hmulLe

lemma Np_le_order_class_bound_of_prime_ne_two'
    {n p : Nat}
    (hp : Nat.Prime p) (hpne2 : p ≠ 2) :
    Np n p <= (L n + 1) / twoOrderSq p hp hpne2 + 1 := by
  simpa [twoOrderSq] using Np_le_order_class_bound_of_prime_ne_two (n := n) hp hpne2

lemma Np_le_smallPrimeSupport_piecewise (n p : Nat)
    (hpS : p ∈ smallPrimeSupport n) :
    Np n p <=
      if hp2 : p = 2 then
        L n + 1
      else
        (L n + 1) / twoOrderSq p ((Finset.mem_filter.mp hpS).2) hp2 + 1 := by
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  by_cases hp2 : p = 2
  · subst hp2
    exact L2_local_periodic n 2 (by decide)
  · have hloc : Np n p <= (L n + 1) / twoOrderSq p hp hp2 + 1 :=
      Np_le_order_class_bound_of_prime_ne_two' (n := n) hp hp2
    simpa [hp2] using hloc

lemma Np_le_largePrimeSupport_piecewise (n p : Nat)
    (hpS : p ∈ largePrimeSupport n) :
    Np n p <=
      if hp2 : p = 2 then
        L n + 1
      else
        (L n + 1) / twoOrderSq p ((Finset.mem_filter.mp hpS).2) hp2 + 1 := by
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  by_cases hp2 : p = 2
  · subst hp2
    exact L2_local_periodic n 2 (by decide)
  · have hloc : Np n p <= (L n + 1) / twoOrderSq p hp hp2 + 1 :=
      Np_le_order_class_bound_of_prime_ne_two' (n := n) hp hp2
    simpa [hp2] using hloc

/--
Unified local bound used for both small- and large-prime supports.
-/
noncomputable def localOrderBound (n p : Nat) : Nat :=
  if hp : Nat.Prime p then
    if hp2 : p = 2 then
      L n + 1
    else
      (L n + 1) / twoOrderSq p hp hp2 + 1
  else
    L n + 1

lemma Np_le_localOrderBound_of_smallPrimeSupport (n p : Nat)
    (hpS : p ∈ smallPrimeSupport n) :
    Np n p <= localOrderBound n p := by
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  unfold localOrderBound
  simpa [hp] using Np_le_smallPrimeSupport_piecewise n p hpS

lemma Np_le_localOrderBound_of_largePrimeSupport (n p : Nat)
    (hpS : p ∈ largePrimeSupport n) :
    Np n p <= localOrderBound n p := by
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  unfold localOrderBound
  simpa [hp] using Np_le_largePrimeSupport_piecewise n p hpS

lemma localOrderBound_le_L_add_one_of_prime {n p : Nat} (hp : Nat.Prime p) :
    localOrderBound n p <= L n + 1 := by
  unfold localOrderBound
  have hprime :
      (if hp' : Nat.Prime p then
          if hp2 : p = 2 then
            L n + 1
          else
            (L n + 1) / twoOrderSq p hp' hp2 + 1
        else
          L n + 1) =
        (if hp2 : p = 2 then
          L n + 1
        else
          (L n + 1) / twoOrderSq p hp hp2 + 1) := by
    simp [hp]
  rw [hprime]
  by_cases hp2 : p = 2
  · simp [hp2]
  · have hOrd2 : 2 <= twoOrderSq p hp hp2 := twoOrderSq_ge_two p hp hp2
    have hdiv :
        (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / 2 :=
      Nat.div_le_div_left hOrd2 (by decide : 0 < 2)
    have hhalf : (L n + 1) / 2 <= L n := by
      omega
    simpa [hp2] using (le_trans hdiv hhalf)

lemma sum_localOrderBound_small_le (n : Nat) :
    Finset.sum (smallPrimeSupport n) (fun p => localOrderBound n p) <=
      (smallPrimeSupport n).card * (L n + 1) := by
  calc
    Finset.sum (smallPrimeSupport n) (fun p => localOrderBound n p) <=
        Finset.sum (smallPrimeSupport n) (fun _ => L n + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            exact localOrderBound_le_L_add_one_of_prime ((Finset.mem_filter.mp hpS).2))
    _ = (smallPrimeSupport n).card * (L n + 1) := by simp

lemma sum_localOrderBound_large_le (n : Nat) :
    Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) <=
      (largePrimeSupport n).card * (L n + 1) := by
  calc
    Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) <=
        Finset.sum (largePrimeSupport n) (fun _ => L n + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            exact localOrderBound_le_L_add_one_of_prime ((Finset.mem_filter.mp hpS).2))
    _ = (largePrimeSupport n).card * (L n + 1) := by simp

lemma sum_localOrderBound_largeSq_le (n : Nat) :
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (largePrimeSupportSq n).card * (L n + 1) := by
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (largePrimeSupportSq n) (fun _ => L n + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpS).1
            exact localOrderBound_le_L_add_one_of_prime ((Finset.mem_filter.mp hpLarge).2))
    _ = (largePrimeSupportSq n).card * (L n + 1) := by simp

lemma localOrderBound_le_half_add_one_of_prime_ne_two {n p : Nat}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    localOrderBound n p <= (L n + 1) / 2 + 1 := by
  have hdiv :
      (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / 2 :=
    Nat.div_le_div_left (twoOrderSq_ge_two p hp hp2) (by decide : 0 < 2)
  have hdiv1 :
      (L n + 1) / twoOrderSq p hp hp2 + 1 <= (L n + 1) / 2 + 1 :=
    Nat.add_le_add_right hdiv 1
  unfold localOrderBound
  simpa [hp, hp2] using hdiv1

lemma localOrderBound_le_div_prime_add_one_of_not_wieferich {n p : Nat}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hNotWieferich : ¬ WieferichBase2 p) :
    localOrderBound n p <= (L n + 1) / p + 1 := by
  have hdiv :
      (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / p :=
    Nat.div_le_div_left
      (le_twoOrderSq_of_not_wieferichBase2 p hp hp2 hNotWieferich) hp.pos
  have hdiv1 :
      (L n + 1) / twoOrderSq p hp hp2 + 1 <= (L n + 1) / p + 1 :=
    Nat.add_le_add_right hdiv 1
  unfold localOrderBound
  simpa [hp, hp2] using hdiv1

lemma prime_ne_two_of_mem_largePrimeSupport {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupport n) :
    p ≠ 2 := by
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).1
  intro hp2
  have h3le : 3 <= p := le_trans (Nat.succ_le_succ hz2) hpLow
  have h3le2 : 3 <= 2 := hp2 ▸ h3le
  exact Nat.not_succ_le_self 2 h3le2

lemma prime_ne_three_of_mem_largePrimeSupport {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ largePrimeSupport n) :
    p ≠ 3 := by
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).1
  intro hp3
  have h4le : 4 <= p := le_trans (Nat.succ_le_succ hz3) hpLow
  omega

lemma localOrderBound_le_half_add_one_of_largePrimeSupport {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupport n) :
    localOrderBound n p <= (L n + 1) / 2 + 1 := by
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpS).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpS
  exact localOrderBound_le_half_add_one_of_prime_ne_two hp hp2

lemma localOrderBound_le_half_add_one_of_largePrimeSupportSq {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupportSq n) :
    localOrderBound n p <= (L n + 1) / 2 + 1 := by
  exact localOrderBound_le_half_add_one_of_largePrimeSupport hz2 ((Finset.mem_filter.mp hpS).1)

lemma localOrderBound_le_div_prime_add_one_of_nonWieferichLargePrimeSupportSq {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ nonWieferichLargePrimeSupportSq n) :
    localOrderBound n p <= (L n + 1) / p + 1 := by
  classical
  have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hpS).1
  have hNotWieferich : ¬ WieferichBase2 p := (Finset.mem_filter.mp hpS).2
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  exact localOrderBound_le_div_prime_add_one_of_not_wieferich hp hp2 hNotWieferich

lemma L_add_one_div_le_two_of_mem_largePrimeSupport {n p : Nat}
    (hpS : p ∈ largePrimeSupport n) :
    (L n + 1) / p <= 2 := by
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).1
  have hmul : L n + 1 <= p * 2 := by
    unfold z at hpLow
    omega
  exact Nat.div_le_of_le_mul hmul

lemma localOrderBound_le_three_of_nonWieferichLargePrimeSupportSq {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ nonWieferichLargePrimeSupportSq n) :
    localOrderBound n p <= 3 := by
  classical
  have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hpS).1
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
  have hdiv : (L n + 1) / p <= 2 := L_add_one_div_le_two_of_mem_largePrimeSupport hpLarge
  calc
    localOrderBound n p <= (L n + 1) / p + 1 := by
      exact localOrderBound_le_div_prime_add_one_of_nonWieferichLargePrimeSupportSq hz2 hpS
    _ <= 2 + 1 := Nat.add_le_add_right hdiv 1
    _ = 3 := by norm_num

lemma L_add_one_div_le_one_of_z_add_two_le {n p : Nat}
    (hpLow : z n + 2 <= p) :
    (L n + 1) / p <= 1 := by
  have hpTwo : 2 <= p := le_trans (by omega) hpLow
  have hpPos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hpTwo
  have hlt : L n + 1 < 2 * p := by
    unfold z at hpLow
    omega
  have hdivlt : (L n + 1) / p < 2 := (Nat.div_lt_iff_lt_mul hpPos).2 hlt
  omega

lemma localOrderBound_le_two_of_nonWieferichLargePrimeSupportSq_of_z_add_two_le {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ nonWieferichLargePrimeSupportSq n) (hpLow : z n + 2 <= p) :
    localOrderBound n p <= 2 := by
  classical
  have hdiv :
      (L n + 1) / p <= 1 := L_add_one_div_le_one_of_z_add_two_le hpLow
  calc
    localOrderBound n p <= (L n + 1) / p + 1 := by
      exact localOrderBound_le_div_prime_add_one_of_nonWieferichLargePrimeSupportSq hz2 hpS
    _ <= 1 + 1 := Nat.add_le_add_right hdiv 1
    _ = 2 := by norm_num

lemma L_add_one_lt_three_mul_z_add_one (n : Nat) :
    L n + 1 < 3 * (z n + 1) := by
  unfold z
  omega

lemma localOrderBound_le_one_of_nonWieferichLargePrimeSupportSq {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ nonWieferichLargePrimeSupportSq n) :
    localOrderBound n p <= 1 := by
  classical
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hpS).1
  have hNotWieferich : ¬ WieferichBase2 p := (Finset.mem_filter.mp hpS).2
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpLarge).1).1
  have hpne3 : p ≠ 3 := prime_ne_three_of_mem_largePrimeSupport hz3 hpLarge
  have hOrdLe :
      3 * p <= twoOrderSq p hp hp2 :=
    three_mul_le_twoOrderSq_of_not_wieferichBase2 p hp hp2 hpne3 hNotWieferich
  have hlt : L n + 1 < twoOrderSq p hp hp2 := by
    have hbase : L n + 1 < 3 * (z n + 1) := L_add_one_lt_three_mul_z_add_one n
    exact lt_of_lt_of_le hbase (le_trans (Nat.mul_le_mul_left 3 hpLow) hOrdLe)
  have hdiv0 : (L n + 1) / twoOrderSq p hp hp2 = 0 := Nat.div_eq_of_lt hlt
  unfold localOrderBound
  simpa [hp, hp2, hdiv0]

lemma localOrderBound_eq_one_of_nonWieferichLargePrimeSupportSq {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ nonWieferichLargePrimeSupportSq n) :
    localOrderBound n p = 1 := by
  have hle : localOrderBound n p <= 1 :=
    localOrderBound_le_one_of_nonWieferichLargePrimeSupportSq hz3 hpS
  have hpSq : p ∈ largePrimeSupportSq n := nonWieferichLargePrimeSupportSq_subset n hpS
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  have hpos : 0 < localOrderBound n p := by
    unfold localOrderBound
    simp [hp, hp2]
  omega

lemma Np_eq_one_of_nonWieferichLargePrimeActiveSupportSq {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ nonWieferichLargePrimeActiveSupportSq n) :
    Np n p = 1 := by
  have hpAct : p ∈ largePrimeActiveSupportSq n :=
    nonWieferichLargePrimeActiveSupportSq_subset n hpS
  have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
  have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
    nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n hpS
  have hle : Np n p <= 1 := by
    calc
      Np n p <= localOrderBound n p :=
        Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1)
      _ = 1 := localOrderBound_eq_one_of_nonWieferichLargePrimeSupportSq hz3 hpNon
  have hpos : 0 < Np n p := Nat.pos_of_ne_zero (Finset.mem_filter.mp hpAct).2
  omega

lemma localOrderBound_le_third_add_one_of_largePrimeSupportSq {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ largePrimeSupportSq n) :
    localOrderBound n p <= (L n + 1) / 3 + 1 := by
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpS).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  have hp3 : p ≠ 3 := prime_ne_three_of_mem_largePrimeSupport hz3 hpLarge
  have hdiv :
      (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / 3 :=
    Nat.div_le_div_left (three_le_twoOrderSq_of_prime_ne_three p hp hp2 hp3) (by decide : 0 < 3)
  have hdiv1 :
      (L n + 1) / twoOrderSq p hp hp2 + 1 <= (L n + 1) / 3 + 1 :=
    Nat.add_le_add_right hdiv 1
  unfold localOrderBound
  simpa [hp, hp2] using hdiv1

lemma localOrderBound_le_div_add_one_of_largePrimeSupportSq
    {n p d : Nat} (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupportSq n)
    (hpow : 2 ^ d < (z n + 1) ^ 2) :
    localOrderBound n p <= (L n + 1) / (d + 1) + 1 := by
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpS).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpLarge).1).1
  have hsquare :
      (z n + 1) ^ 2 <= p ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hpLow hpLow
  have hOrdGt : d < twoOrderSq p hp hp2 := by
    exact lt_twoOrderSq_of_two_pow_lt_sq p d hp hp2 (lt_of_lt_of_le hpow hsquare)
  have hOrdGe : d + 1 <= twoOrderSq p hp hp2 := Nat.succ_le_of_lt hOrdGt
  have hdiv :
      (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / (d + 1) :=
    Nat.div_le_div_left hOrdGe (Nat.succ_pos d)
  have hdiv1 :
      (L n + 1) / twoOrderSq p hp hp2 + 1 <= (L n + 1) / (d + 1) + 1 :=
    Nat.add_le_add_right hdiv 1
  unfold localOrderBound
  simpa [hp, hp2] using hdiv1

lemma two_pow_two_mul_log_sub_one_lt_sq {m : Nat} (hm : 2 <= m) :
    2 ^ (2 * Nat.log 2 m - 1) < m ^ 2 := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 2) hm
  have hlogPos : 0 < Nat.log 2 m := Nat.log_pos Nat.one_lt_two hm1
  have htwoLogPos : 0 < 2 * Nat.log 2 m := Nat.mul_pos (by decide : 0 < 2) hlogPos
  have hExpLt : 2 * Nat.log 2 m - 1 < 2 * Nat.log 2 m := Nat.sub_lt htwoLogPos (by decide : 0 < 1)
  have hpowLt :
      2 ^ (2 * Nat.log 2 m - 1) < 2 ^ (2 * Nat.log 2 m) :=
    Nat.pow_lt_pow_right Nat.one_lt_two hExpLt
  have hlogLe : 2 ^ Nat.log 2 m <= m := Nat.pow_log_le_self 2 hm0
  have hpowLe : 2 ^ (2 * Nat.log 2 m) <= m ^ 2 := by
    calc
      2 ^ (2 * Nat.log 2 m) = 2 ^ Nat.log 2 m * 2 ^ Nat.log 2 m := by
        rw [show 2 * Nat.log 2 m = Nat.log 2 m + Nat.log 2 m by omega, Nat.pow_add]
      _ <= m * m := Nat.mul_le_mul hlogLe hlogLe
      _ = m ^ 2 := by rw [pow_two]
  exact lt_of_lt_of_le hpowLt hpowLe

lemma localOrderBound_le_logPrime_add_one_of_largePrimeSupportSq
    {n p : Nat} (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupportSq n) :
    localOrderBound n p <= (L n + 1) / (2 * Nat.log 2 p) + 1 := by
  have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpS).1
  have hp : Nat.Prime p := (Finset.mem_filter.mp hpLarge).2
  have hp2 : p ≠ 2 := prime_ne_two_of_mem_largePrimeSupport hz2 hpLarge
  have hpGe2 : 2 <= p := hp.two_le
  have hpow :
      2 ^ (2 * Nat.log 2 p - 1) < p ^ 2 :=
    two_pow_two_mul_log_sub_one_lt_sq hpGe2
  have hOrdGt :
      2 * Nat.log 2 p - 1 < twoOrderSq p hp hp2 :=
    lt_twoOrderSq_of_two_pow_lt_sq p (2 * Nat.log 2 p - 1) hp hp2 hpow
  have hlogPos : 1 <= 2 * Nat.log 2 p := by
    have hlog : 0 < Nat.log 2 p := Nat.log_pos Nat.one_lt_two hp.one_lt
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hlog)
  have hOrdGe :
      2 * Nat.log 2 p <= twoOrderSq p hp hp2 := by
    simpa [Nat.sub_add_cancel hlogPos] using Nat.succ_le_of_lt hOrdGt
  have hdiv :
      (L n + 1) / twoOrderSq p hp hp2 <= (L n + 1) / (2 * Nat.log 2 p) :=
    Nat.div_le_div_left hOrdGe (lt_of_lt_of_le (by decide : 0 < 1) hlogPos)
  have hdiv1 :
      (L n + 1) / twoOrderSq p hp hp2 + 1 <= (L n + 1) / (2 * Nat.log 2 p) + 1 :=
    Nat.add_le_add_right hdiv 1
  unfold localOrderBound
  simpa [hp, hp2] using hdiv1

lemma sum_localOrderBound_large_le_half_add_one (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) <=
      (largePrimeSupport n).card * ((L n + 1) / 2 + 1) := by
  calc
    Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) <=
        Finset.sum (largePrimeSupport n) (fun _ => (L n + 1) / 2 + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            exact localOrderBound_le_half_add_one_of_largePrimeSupport hz2 hpS)
    _ = (largePrimeSupport n).card * ((L n + 1) / 2 + 1) := by simp

lemma sum_localOrderBound_largeSq_le_half_add_one (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (largePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (largePrimeSupportSq n) (fun _ => (L n + 1) / 2 + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2 hpS)
    _ = (largePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by simp

lemma sum_localOrderBound_wieferichLargeSq_le_half_add_one (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (wieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by
  classical
  calc
    Finset.sum (wieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (wieferichLargePrimeSupportSq n) (fun _ => (L n + 1) / 2 + 1) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2
              ((Finset.mem_filter.mp hpS).1))
    _ = (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by simp

lemma sum_localOrderBound_nonWieferichLargeSq_le_div_prime_add_one
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
      Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
  classical
  exact Finset.sum_le_sum (by
    intro p hpS
    exact localOrderBound_le_div_prime_add_one_of_nonWieferichLargePrimeSupportSq hz2 hpS)

lemma sum_localOrderBound_largeSq_le_wieferich_split (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
        Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
  classical
  have hsplit :
      Finset.sum (wieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) := by
    simpa [wieferichLargePrimeSupportSq, nonWieferichLargePrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := WieferichBase2)
        (f := fun p => localOrderBound n p))
  have hWieferich :
      Finset.sum (wieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
        (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) :=
    sum_localOrderBound_wieferichLargeSq_le_half_add_one n hz2
  have hNon :
      Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) :=
    sum_localOrderBound_nonWieferichLargeSq_le_div_prime_add_one n hz2
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) =
        Finset.sum (wieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) := by
            symm
            exact hsplit
    _ <= (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
          Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
            exact Nat.add_le_add hWieferich hNon

lemma sum_nonWieferichLargeSq_div_prime_add_one_le_three (n : Nat) :
    Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) <=
      (nonWieferichLargePrimeSupportSq n).card * 3 := by
  classical
  calc
    Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) <=
        Finset.sum (nonWieferichLargePrimeSupportSq n) (fun _ => 3) := by
          exact Finset.sum_le_sum (by
            intro p hpS
            have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hpS).1
            have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
            have hdiv : (L n + 1) / p <= 2 := L_add_one_div_le_two_of_mem_largePrimeSupport hpLarge
            calc
              (L n + 1) / p + 1 <= 2 + 1 := Nat.add_le_add_right hdiv 1
              _ = 3 := by norm_num)
    _ = (nonWieferichLargePrimeSupportSq n).card * 3 := by simp

lemma sum_localOrderBound_nonWieferichLargeSq_le_three (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (nonWieferichLargePrimeSupportSq n).card * 3 := by
  calc
    Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
          exact sum_localOrderBound_nonWieferichLargeSq_le_div_prime_add_one n hz2
    _ <= (nonWieferichLargePrimeSupportSq n).card * 3 := by
      exact sum_nonWieferichLargeSq_div_prime_add_one_le_three n

lemma sum_localOrderBound_largeSq_le_wieferich_three_split (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
        (nonWieferichLargePrimeSupportSq n).card * 3 := by
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
        (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
          Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
            exact sum_localOrderBound_largeSq_le_wieferich_split n hz2
    _ <= (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
          (nonWieferichLargePrimeSupportSq n).card * 3 := by
            exact Nat.add_le_add_left
              (sum_nonWieferichLargeSq_div_prime_add_one_le_three n)
              ((wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1))

lemma three_le_half_add_one_of_two_le_z (n : Nat) (hz2 : 2 <= z n) :
    3 <= (L n + 1) / 2 + 1 := by
  have hL4 : 4 <= L n := by
    unfold z at hz2
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 hz2
  have hhalf : 2 <= (L n + 1) / 2 := by
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (le_trans hL4 (Nat.le_succ _))
  exact Nat.succ_le_succ hhalf

lemma wieferich_three_split_eq_supportSq_three_add_excess (n : Nat) (hz2 : 2 <= z n) :
    (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
        (nonWieferichLargePrimeSupportSq n).card * 3 =
      (largePrimeSupportSq n).card * 3 +
        (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  let a := (wieferichLargePrimeSupportSq n).card
  let b := (nonWieferichLargePrimeSupportSq n).card
  let h := (L n + 1) / 2 + 1
  have hh : 3 <= h := by
    dsimp [h]
    exact three_le_half_add_one_of_two_le_z n hz2
  have hab : a + b = (largePrimeSupportSq n).card := by
    dsimp [a, b]
    exact card_wieferich_add_card_nonWieferichLargePrimeSupportSq n
  calc
    a * h + b * 3 = a * ((h - 3) + 3) + b * 3 := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 3) + a * 3 + b * 3 := by
      rw [Nat.mul_add]
    _ = a * (h - 3) + (a * 3 + b * 3) := by ac_rfl
    _ = a * (h - 3) + (a + b) * 3 := by rw [← Nat.add_mul]
    _ = a * (h - 3) + (largePrimeSupportSq n).card * 3 := by rw [hab]
    _ = (largePrimeSupportSq n).card * 3 + a * (h - 3) := by ac_rfl
    _ =
        (largePrimeSupportSq n).card * 3 +
          (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
            rfl

lemma sum_localOrderBound_largeSq_le_supportSq_three_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
      (largePrimeSupportSq n).card * 3 +
        (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) <=
        (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
          (nonWieferichLargePrimeSupportSq n).card * 3 := by
            exact sum_localOrderBound_largeSq_le_wieferich_three_split n hz2
    _ = (largePrimeSupportSq n).card * 3 +
          (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
            exact wieferich_three_split_eq_supportSq_three_add_excess n hz2

lemma sum_Np_largePrimeSupportSq_eq_sum_largePrimeActiveSupportSq (n : Nat) :
    Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) =
      Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
  classical
  simpa [largePrimeActiveSupportSq] using
    (Finset.sum_filter_ne_zero (s := largePrimeSupportSq n) (f := fun p => Np n p))

lemma sum_localOrderBound_largePrimeActiveSq_le_wieferich_three_split
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
      (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
        (nonWieferichLargePrimeActiveSupportSq n).card * 3 := by
  classical
  have hsplit :
      Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    simpa [wieferichLargePrimeActiveSupportSq, nonWieferichLargePrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := WieferichBase2)
        (f := fun p => localOrderBound n p))
  have hWieferich :
      Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) := by
    calc
      Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
          Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun _ => (L n + 1) / 2 + 1) := by
            exact Finset.sum_le_sum (by
              intro p hpS
              have hpSq : p ∈ largePrimeSupportSq n :=
                largePrimeActiveSupportSq_subset n ((Finset.mem_filter.mp hpS).1)
              exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2 hpSq)
      _ = (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) := by simp
  have hNon :
      Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (nonWieferichLargePrimeActiveSupportSq n).card * 3 := by
    calc
      Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
          Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun _ => 3) := by
            exact Finset.sum_le_sum (by
              intro p hpS
              have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
                nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n hpS
              exact localOrderBound_le_three_of_nonWieferichLargePrimeSupportSq hz2 hpNon)
      _ = (nonWieferichLargePrimeActiveSupportSq n).card * 3 := by simp
  calc
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) =
        Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            symm
            exact hsplit
    _ <= (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
          (nonWieferichLargePrimeActiveSupportSq n).card * 3 := by
            exact Nat.add_le_add hWieferich hNon

lemma wieferichActive_three_split_eq_activeSupportSq_three_add_excess
    (n : Nat) (hz2 : 2 <= z n) :
    (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
        (nonWieferichLargePrimeActiveSupportSq n).card * 3 =
      (largePrimeActiveSupportSq n).card * 3 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  let a := (wieferichLargePrimeActiveSupportSq n).card
  let b := (nonWieferichLargePrimeActiveSupportSq n).card
  let h := (L n + 1) / 2 + 1
  have hh : 3 <= h := by
    dsimp [h]
    exact three_le_half_add_one_of_two_le_z n hz2
  have hab : a + b = (largePrimeActiveSupportSq n).card := by
    dsimp [a, b]
    exact card_wieferich_add_card_nonWieferichLargePrimeActiveSupportSq n
  calc
    a * h + b * 3 = a * ((h - 3) + 3) + b * 3 := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 3) + a * 3 + b * 3 := by rw [Nat.mul_add]
    _ = a * (h - 3) + (a * 3 + b * 3) := by ac_rfl
    _ = a * (h - 3) + (a + b) * 3 := by rw [← Nat.add_mul]
    _ = a * (h - 3) + (largePrimeActiveSupportSq n).card * 3 := by rw [hab]
    _ = (largePrimeActiveSupportSq n).card * 3 + a * (h - 3) := by ac_rfl
    _ =
        (largePrimeActiveSupportSq n).card * 3 +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
            rfl

lemma sum_localOrderBound_largePrimeActiveSq_le_supportSq_three_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
      (largePrimeActiveSupportSq n).card * 3 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  calc
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
          (nonWieferichLargePrimeActiveSupportSq n).card * 3 := by
            exact sum_localOrderBound_largePrimeActiveSq_le_wieferich_three_split n hz2
    _ = (largePrimeActiveSupportSq n).card * 3 +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
            exact wieferichActive_three_split_eq_activeSupportSq_three_add_excess n hz2

lemma card_filter_eq_singleton_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) :
    (s.filter (fun x => x = a)).card <= 1 := by
  classical
  simpa [eq_comm] using (show (s.filter (Eq a)).card <= 1 by
    rw [Finset.filter_eq]
    split_ifs <;> simp)

lemma sum_localOrderBound_nonWieferichLargePrimeActiveSq_le_two_mul_card_add_one
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
      (nonWieferichLargePrimeActiveSupportSq n).card * 2 + 1 := by
  classical
  let a := z n + 1
  have hpoint :
      ∀ p ∈ nonWieferichLargePrimeActiveSupportSq n,
        localOrderBound n p <= if p = a then 3 else 2 := by
    intro p hpS
    by_cases hpEq : p = a
    · simpa [a, hpEq] using
        localOrderBound_le_three_of_nonWieferichLargePrimeSupportSq hz2
          (nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n hpS)
    · have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
        nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n hpS
      have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp ((Finset.mem_filter.mp hpNon).1)).1
      have hpLow1 : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpLarge).1).1
      have hpLow2 : z n + 2 <= p := by
        have hneq : z n + 1 ≠ p := by simpa [a, eq_comm] using hpEq
        have hlt : z n + 1 < p := lt_of_le_of_ne hpLow1 hneq
        exact Nat.succ_le_of_lt hlt
      simpa [a, hpEq] using
        localOrderBound_le_two_of_nonWieferichLargePrimeSupportSq_of_z_add_two_le hz2 hpNon hpLow2
  have hsum :
      Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => if p = a then 3 else 2) := by
    exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
  have hcalc :
      Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => if p = a then 3 else 2) <=
        (nonWieferichLargePrimeActiveSupportSq n).card * 2 + 1 := by
    calc
      Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => if p = a then 3 else 2) =
          Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => 2 + if p = a then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            by_cases hpEq : p = a <;> simp [hpEq]
      _ = Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun _ => 2) +
            Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => if p = a then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (nonWieferichLargePrimeActiveSupportSq n).card * 2 +
            Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => if p = a then 1 else 0) := by
              simp
      _ = (nonWieferichLargePrimeActiveSupportSq n).card * 2 +
            ((nonWieferichLargePrimeActiveSupportSq n).filter (fun p => p = a)).card := by
              simpa using congrArg
                (fun t => (nonWieferichLargePrimeActiveSupportSq n).card * 2 + t)
                (Finset.sum_boole (p := fun p => p = a) (s := nonWieferichLargePrimeActiveSupportSq n))
      _ <= (nonWieferichLargePrimeActiveSupportSq n).card * 2 + 1 := by
              exact Nat.add_le_add_left
                (card_filter_eq_singleton_le_one (nonWieferichLargePrimeActiveSupportSq n) a)
                ((nonWieferichLargePrimeActiveSupportSq n).card * 2)
  exact le_trans hsum hcalc

lemma activeWieferich_two_split_eq_activeSupportSq_two_add_excess_plus_one
    (n : Nat) (hz2 : 2 <= z n) :
    (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
        ((nonWieferichLargePrimeActiveSupportSq n).card * 2 + 1) =
      (largePrimeActiveSupportSq n).card * 2 + 1 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
  let a := (wieferichLargePrimeActiveSupportSq n).card
  let b := (nonWieferichLargePrimeActiveSupportSq n).card
  let h := (L n + 1) / 2 + 1
  have hh : 2 <= h := le_trans (by decide : 2 <= 3) (three_le_half_add_one_of_two_le_z n hz2)
  have hab : a + b = (largePrimeActiveSupportSq n).card := by
    dsimp [a, b]
    exact card_wieferich_add_card_nonWieferichLargePrimeActiveSupportSq n
  calc
    a * h + (b * 2 + 1) = a * ((h - 2) + 2) + (b * 2 + 1) := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 2) + a * 2 + (b * 2 + 1) := by rw [Nat.mul_add]
    _ = a * (h - 2) + ((a * 2 + b * 2) + 1) := by ac_rfl
    _ = a * (h - 2) + ((a + b) * 2 + 1) := by rw [← Nat.add_mul]
    _ = a * (h - 2) + ((largePrimeActiveSupportSq n).card * 2 + 1) := by rw [hab]
    _ = (largePrimeActiveSupportSq n).card * 2 + 1 + a * (h - 2) := by ac_rfl
    _ =
        (largePrimeActiveSupportSq n).card * 2 + 1 +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
            rfl

lemma sum_localOrderBound_largePrimeActiveSq_le_supportSq_two_add_wieferich_excess_plus_one
    (n : Nat) (hz2 : 2 <= z n) :
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
      (largePrimeActiveSupportSq n).card * 2 + 1 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
  classical
  calc
    Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) =
        Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichLargePrimeActiveSupportSq, nonWieferichLargePrimeActiveSupportSq] using
              (Finset.sum_filter_add_sum_filter_not
                (s := largePrimeActiveSupportSq n) (p := WieferichBase2)
                (f := fun p => localOrderBound n p))
    _ <= (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) +
          ((nonWieferichLargePrimeActiveSupportSq n).card * 2 + 1) := by
            exact Nat.add_le_add
              (by
                calc
                  Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
                      Finset.sum (wieferichLargePrimeActiveSupportSq n) (fun _ => (L n + 1) / 2 + 1) := by
                        exact Finset.sum_le_sum (by
                          intro p hpS
                          have hpSq : p ∈ largePrimeSupportSq n :=
                            largePrimeActiveSupportSq_subset n ((Finset.mem_filter.mp hpS).1)
                          exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2 hpSq)
                  _ = (wieferichLargePrimeActiveSupportSq n).card * ((L n + 1) / 2 + 1) := by simp)
              (sum_localOrderBound_nonWieferichLargePrimeActiveSq_le_two_mul_card_add_one n hz2)
    _ = (largePrimeActiveSupportSq n).card * 2 + 1 +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
            exact activeWieferich_two_split_eq_activeSupportSq_two_add_excess_plus_one n hz2

lemma sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_two_mul_card_add_one
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ nonWieferichLargePrimeActiveSupportSq n) (hz2 : 2 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <= S.card * 2 + 1 := by
  classical
  let a := z n + 1
  have hpoint :
      ∀ p ∈ S, localOrderBound n p <= if p = a then 3 else 2 := by
    intro p hpS
    by_cases hpEq : p = a
    · have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
        nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n (hS hpS)
      simpa [a, hpEq] using
        localOrderBound_le_three_of_nonWieferichLargePrimeSupportSq hz2 hpNon
    · have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
        nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n (hS hpS)
      have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp ((Finset.mem_filter.mp hpNon).1)).1
      have hpLow1 : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpLarge).1).1
      have hpLow2 : z n + 2 <= p := by
        have hneq : z n + 1 ≠ p := by simpa [a, eq_comm] using hpEq
        have hlt : z n + 1 < p := lt_of_le_of_ne hpLow1 hneq
        exact Nat.succ_le_of_lt hlt
      simpa [a, hpEq] using
        localOrderBound_le_two_of_nonWieferichLargePrimeSupportSq_of_z_add_two_le hz2 hpNon hpLow2
  have hsum :
      Finset.sum S (fun p => localOrderBound n p) <=
        Finset.sum S (fun p => if p = a then 3 else 2) := by
    exact Finset.sum_le_sum (by intro p hp; exact hpoint p hp)
  have hcalc :
      Finset.sum S (fun p => if p = a then 3 else 2) <= S.card * 2 + 1 := by
    calc
      Finset.sum S (fun p => if p = a then 3 else 2) =
          Finset.sum S (fun p => 2 + if p = a then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            by_cases hpEq : p = a <;> simp [hpEq]
      _ = Finset.sum S (fun _ => 2) +
            Finset.sum S (fun p => if p = a then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = S.card * 2 + Finset.sum S (fun p => if p = a then 1 else 0) := by
              simp
      _ = S.card * 2 + (S.filter (fun p => p = a)).card := by
              simpa using congrArg
                (fun t => S.card * 2 + t)
                (Finset.sum_boole (p := fun p => p = a) (s := S))
      _ <= S.card * 2 + 1 := by
              exact Nat.add_le_add_left (card_filter_eq_singleton_le_one S a) (S.card * 2)
  exact le_trans hsum hcalc

noncomputable def wieferichSubsupport (S : Finset Nat) : Finset Nat := by
  classical
  exact S.filter WieferichBase2

noncomputable def nonWieferichSubsupport (S : Finset Nat) : Finset Nat := by
  classical
  exact S.filter (fun p => ¬ WieferichBase2 p)

lemma activeWieferich_two_split_eq_activeSubset_two_add_excess_plus_one
    (n : Nat) (S : Finset Nat) (hz2 : 2 <= z n) :
    (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) +
        (((nonWieferichSubsupport S).card * 2) + 1) =
      S.card * 2 + 1 +
        (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 2) := by
  classical
  let a := (wieferichSubsupport S).card
  let b := (nonWieferichSubsupport S).card
  let h := (L n + 1) / 2 + 1
  have hh : 2 <= h := le_trans (by decide : 2 <= 3) (three_le_half_add_one_of_two_le_z n hz2)
  have hab : a + b = S.card := by
    dsimp [a, b]
    simpa [wieferichSubsupport, nonWieferichSubsupport] using
      (Finset.card_filter_add_card_filter_not (s := S) (p := WieferichBase2))
  calc
    a * h + (b * 2 + 1) = a * ((h - 2) + 2) + (b * 2 + 1) := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 2) + a * 2 + (b * 2 + 1) := by rw [Nat.mul_add]
    _ = a * (h - 2) + ((a * 2 + b * 2) + 1) := by ac_rfl
    _ = a * (h - 2) + ((a + b) * 2 + 1) := by rw [← Nat.add_mul]
    _ = a * (h - 2) + (S.card * 2 + 1) := by rw [hab]
    _ = S.card * 2 + 1 + a * (h - 2) := by ac_rfl
    _ =
        S.card * 2 + 1 +
          (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 2) := by
            rfl

lemma sum_localOrderBound_largePrimeActiveSubset_le_two_mul_card_add_wieferich_excess_plus_one
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz2 : 2 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card * 2 + 1 +
        (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 2) := by
  classical
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
    _ <= (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) +
          (((nonWieferichSubsupport S).card * 2) + 1) := by
            exact Nat.add_le_add
              (by
                calc
                  Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) <=
                      Finset.sum (wieferichSubsupport S) (fun _ => (L n + 1) / 2 + 1) := by
                        exact Finset.sum_le_sum (by
                          intro p hpS
                          have hpAct : p ∈ largePrimeActiveSupportSq n := by
                            have hpMem : p ∈ S := by
                              simpa [wieferichSubsupport] using (Finset.mem_filter.mp hpS).1
                            exact hS hpMem
                          have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
                          exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2 hpSq)
                  _ = (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) := by simp)
              (sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_two_mul_card_add_one
                n (nonWieferichSubsupport S)
                (by
                  intro p hp
                  have hpS : p ∈ S := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
                  have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
                  have hpNot : ¬ WieferichBase2 p := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
                  exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩)
                hz2)
    _ = S.card * 2 + 1 +
          (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 2) := by
            exact activeWieferich_two_split_eq_activeSubset_two_add_excess_plus_one n S hz2

lemma sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_card
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ nonWieferichLargePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <= S.card := by
  classical
  calc
    Finset.sum S (fun p => localOrderBound n p) <= Finset.sum S (fun _ => 1) := by
      exact Finset.sum_le_sum (by
        intro p hpS
        have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
          nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n (hS hpS)
        exact localOrderBound_le_one_of_nonWieferichLargePrimeSupportSq hz3 hpNon)
    _ = S.card := by simp

lemma sum_localOrderBound_nonWieferichLargePrimeActiveSubset_eq_card
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ nonWieferichLargePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) = S.card := by
  classical
  calc
    Finset.sum S (fun p => localOrderBound n p) = Finset.sum S (fun _ => 1) := by
      refine Finset.sum_congr rfl ?_
      intro p hpS
      have hpNon : p ∈ nonWieferichLargePrimeSupportSq n :=
        nonWieferichLargePrimeActiveSupportSq_subset_nonWieferichLargePrimeSupportSq n (hS hpS)
      exact localOrderBound_eq_one_of_nonWieferichLargePrimeSupportSq hz3 hpNon
    _ = S.card := by simp

lemma sum_Np_nonWieferichLargePrimeActiveSubset_eq_card
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ nonWieferichLargePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => Np n p) = S.card := by
  classical
  calc
    Finset.sum S (fun p => Np n p) = Finset.sum S (fun _ => 1) := by
      refine Finset.sum_congr rfl ?_
      intro p hpS
      exact Np_eq_one_of_nonWieferichLargePrimeActiveSupportSq hz3 (hS hpS)
    _ = S.card := by simp

lemma sum_Np_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => Np n p) =
      (nonWieferichSubsupport S).card +
        Finset.sum (wieferichSubsupport S) (fun p => Np n p) := by
  classical
  have hNonSub : nonWieferichSubsupport S ⊆ nonWieferichLargePrimeActiveSupportSq n := by
    intro p hp
    have hpS : p ∈ S := by
      simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
    have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
    have hpNot : ¬ WieferichBase2 p := by
      simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩
  calc
    Finset.sum S (fun p => Np n p) =
        Finset.sum (wieferichSubsupport S) (fun p => Np n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => Np n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => Np n p))
    _ = Finset.sum (wieferichSubsupport S) (fun p => Np n p) +
          (nonWieferichSubsupport S).card := by
            rw [sum_Np_nonWieferichLargePrimeActiveSubset_eq_card
              n (nonWieferichSubsupport S) hNonSub hz3]
    _ = (nonWieferichSubsupport S).card +
          Finset.sum (wieferichSubsupport S) (fun p => Np n p) := by
            ac_rfl

lemma sum_Np_largePrimeActiveSubset_eq_card_add_wieferich_excess
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => Np n p) =
      S.card + Finset.sum (wieferichSubsupport S) (fun p => Np n p - 1) := by
  classical
  have hpos :
      ∀ p ∈ wieferichSubsupport S, 0 < Np n p := by
    intro p hp
    have hpS : p ∈ S := by
      simpa [wieferichSubsupport] using (Finset.mem_filter.mp hp).1
    exact Nat.pos_of_ne_zero ((Finset.mem_filter.mp (hS hpS)).2)
  calc
    Finset.sum S (fun p => Np n p) =
      (nonWieferichSubsupport S).card +
        Finset.sum (wieferichSubsupport S) (fun p => Np n p) := by
          exact sum_Np_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum n S hS hz3
    _ = (nonWieferichSubsupport S).card +
          (Finset.sum (wieferichSubsupport S) (fun p => (Np n p - 1) + 1)) := by
            refine congrArg (fun t => (nonWieferichSubsupport S).card + t) ?_
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (hpos p hp))).symm
    _ = (nonWieferichSubsupport S).card +
          (Finset.sum (wieferichSubsupport S) (fun p => Np n p - 1) +
            Finset.sum (wieferichSubsupport S) (fun _ => 1)) := by
            rw [Finset.sum_add_distrib]
    _ = (nonWieferichSubsupport S).card +
          (Finset.sum (wieferichSubsupport S) (fun p => Np n p - 1) +
            (wieferichSubsupport S).card) := by
            simp
    _ = S.card + Finset.sum (wieferichSubsupport S) (fun p => Np n p - 1) := by
          have hcard :
              (wieferichSubsupport S).card + (nonWieferichSubsupport S).card = S.card := by
                simpa [wieferichSubsupport, nonWieferichSubsupport] using
                  (Finset.card_filter_add_card_filter_not (s := S) (p := WieferichBase2))
          omega

lemma cleanBadAtSq_subset_badAtSq {n z0 p : Nat} :
    cleanBadAtSq n z0 p ⊆ badAtSq n p := by
  classical
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨hkA, hmod0⟩
  exact Finset.mem_filter.mpr ⟨A_subset_K n z0 hkA, hmod0⟩

lemma cleanNp_le_Np (n z0 p : Nat) :
    cleanNp n z0 p <= Np n p := by
  exact Finset.card_le_card (cleanBadAtSq_subset_badAtSq (n := n) (z0 := z0) (p := p))

lemma largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq (n : Nat) :
    largePrimeCleanSupportSq n ⊆ largePrimeActiveSupportSq n := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpSq, hclean⟩
  have hcleanPos : 0 < cleanNp n (z n) p := Nat.pos_of_ne_zero hclean
  have hNpPos : 0 < Np n p := lt_of_lt_of_le hcleanPos (cleanNp_le_Np n (z n) p)
  exact Finset.mem_filter.mpr ⟨hpSq, Nat.ne_of_gt hNpPos⟩

lemma wieferichLargePrimeCleanSupportSq_subset_wieferichLargePrimeActiveSupportSq (n : Nat) :
    wieferichLargePrimeCleanSupportSq n ⊆ wieferichLargePrimeActiveSupportSq n := by
  classical
  intro p hp
  have hpClean : p ∈ largePrimeCleanSupportSq n := (Finset.mem_filter.mp hp).1
  have hpAct : p ∈ largePrimeActiveSupportSq n :=
    largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq n hpClean
  exact Finset.mem_filter.mpr ⟨hpAct, (Finset.mem_filter.mp hp).2⟩

lemma nonWieferichLargePrimeCleanSupportSq_subset_nonWieferichLargePrimeActiveSupportSq (n : Nat) :
    nonWieferichLargePrimeCleanSupportSq n ⊆ nonWieferichLargePrimeActiveSupportSq n := by
  classical
  intro p hp
  have hpClean : p ∈ largePrimeCleanSupportSq n := (Finset.mem_filter.mp hp).1
  have hpAct : p ∈ largePrimeActiveSupportSq n :=
    largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq n hpClean
  exact Finset.mem_filter.mpr ⟨hpAct, (Finset.mem_filter.mp hp).2⟩

lemma veryLargePrimeCleanSupportSq_subset_veryLargePrimeActiveSupportSq (n : Nat) :
    veryLargePrimeCleanSupportSq n ⊆ veryLargePrimeActiveSupportSq n := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpClean, hpLarge⟩
  have hpAct : p ∈ largePrimeActiveSupportSq n :=
    largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq n hpClean
  exact Finset.mem_filter.mpr ⟨hpAct, hpLarge⟩

lemma lowFourthPrimeCleanSupportSq_subset_lowFourthPrimeActiveSupportSq (n : Nat) :
    lowFourthPrimeCleanSupportSq n ⊆ lowFourthPrimeActiveSupportSq n := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpClean, hpLow⟩
  have hpAct : p ∈ largePrimeActiveSupportSq n :=
    largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq n hpClean
  exact Finset.mem_filter.mpr ⟨hpAct, hpLow⟩

lemma lowFourthPrimeCleanSupportSq_subset_largePrimeActiveSupportSq (n : Nat) :
    lowFourthPrimeCleanSupportSq n ⊆ largePrimeActiveSupportSq n := by
  intro p hp
  exact lowFourthPrimeActiveSupportSq_subset n
    (lowFourthPrimeCleanSupportSq_subset_lowFourthPrimeActiveSupportSq n hp)

lemma sum_cleanNp_largePrimeSupportSq_eq_sum_largePrimeCleanSupportSq (n : Nat) :
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
      Finset.sum (largePrimeSupportSq n) (fun p => cleanNp n (z n) p) := by
  classical
  simpa [largePrimeCleanSupportSq] using
    (Finset.sum_filter_ne_zero (s := largePrimeSupportSq n) (f := fun p => cleanNp n (z n) p))

lemma cleanNp_eq_one_of_nonWieferichLargePrimeCleanSupportSq {n p : Nat}
    (hz3 : 3 <= z n) (hpS : p ∈ nonWieferichLargePrimeCleanSupportSq n) :
    cleanNp n (z n) p = 1 := by
  classical
  have hpClean : p ∈ largePrimeCleanSupportSq n := (Finset.mem_filter.mp hpS).1
  have hpAct : p ∈ nonWieferichLargePrimeActiveSupportSq n :=
    nonWieferichLargePrimeCleanSupportSq_subset_nonWieferichLargePrimeActiveSupportSq n hpS
  have hle : cleanNp n (z n) p <= 1 := by
    calc
      cleanNp n (z n) p <= Np n p := cleanNp_le_Np n (z n) p
      _ = 1 := Np_eq_one_of_nonWieferichLargePrimeActiveSupportSq hz3 hpAct
  have hpos : 0 < cleanNp n (z n) p := Nat.pos_of_ne_zero ((Finset.mem_filter.mp hpClean).2)
  omega

lemma sum_cleanNp_nonWieferichLargePrimeCleanSupportSq_eq_card
    (n : Nat) (hz3 : 3 <= z n) :
    Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
      (nonWieferichLargePrimeCleanSupportSq n).card := by
  classical
  calc
    Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
        Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun _ => 1) := by
          refine Finset.sum_congr rfl ?_
          intro p hpS
          exact cleanNp_eq_one_of_nonWieferichLargePrimeCleanSupportSq hz3 hpS
    _ = (nonWieferichLargePrimeCleanSupportSq n).card := by simp

lemma sum_cleanNp_largePrimeCleanSupportSq_eq_nonWieferich_card_add_wieferich_sum
    (n : Nat) (hz3 : 3 <= z n) :
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
      (nonWieferichLargePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
  classical
  calc
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
            symm
            simpa [wieferichLargePrimeCleanSupportSq, nonWieferichLargePrimeCleanSupportSq] using
              (Finset.sum_filter_add_sum_filter_not
                (s := largePrimeCleanSupportSq n) (p := WieferichBase2)
                (f := fun p => cleanNp n (z n) p))
    _ = Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          (nonWieferichLargePrimeCleanSupportSq n).card := by
            rw [sum_cleanNp_nonWieferichLargePrimeCleanSupportSq_eq_card n hz3]
    _ = (nonWieferichLargePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
            ac_rfl

lemma sum_cleanNp_largePrimeCleanSupportSq_eq_card_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
      (largePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
  classical
  have hpos :
      ∀ p ∈ wieferichLargePrimeCleanSupportSq n, 0 < cleanNp n (z n) p := by
    intro p hp
    have hpClean : p ∈ largePrimeCleanSupportSq n := (Finset.mem_filter.mp hp).1
    exact Nat.pos_of_ne_zero ((Finset.mem_filter.mp hpClean).2)
  calc
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
      (nonWieferichLargePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
          exact sum_cleanNp_largePrimeCleanSupportSq_eq_nonWieferich_card_add_wieferich_sum n hz3
    _ = (nonWieferichLargePrimeCleanSupportSq n).card +
          (Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (cleanNp n (z n) p - 1) + 1)) := by
              refine congrArg (fun t => (nonWieferichLargePrimeCleanSupportSq n).card + t) ?_
              refine Finset.sum_congr rfl ?_
              intro p hp
              exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (hpos p hp))).symm
    _ = (nonWieferichLargePrimeCleanSupportSq n).card +
          (Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) +
            Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun _ => 1)) := by
              rw [Finset.sum_add_distrib]
    _ = (nonWieferichLargePrimeCleanSupportSq n).card +
          (Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) +
            (wieferichLargePrimeCleanSupportSq n).card) := by
              simp
    _ = (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
            have hcard :
                (wieferichLargePrimeCleanSupportSq n).card +
                    (nonWieferichLargePrimeCleanSupportSq n).card =
                  (largePrimeCleanSupportSq n).card := by
              exact card_wieferich_add_card_nonWieferichLargePrimeCleanSupportSq n
            omega

lemma A_large_prime_decomp_sq_clean_of_not_represents {n : Nat}
    (hNotRep : ¬ Represents n) :
    (A n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => cleanNp n (z n) p) := by
  classical
  let badAt : Nat → Finset Nat := fun p => cleanBadAtSq n (z n) p
  have hsubset :
      A n (z n) ⊆ (largePrimeSupportSq n).biUnion badAt := by
    intro k hkA
    have hkB : k ∈ B n (z n) := A_subset_B_of_not_represents (z0 := z n) hNotRep hkA
    have hkK : k ∈ K n := A_subset_K n (z n) hkA
    rcases (Finset.mem_filter.mp hkB).2 with ⟨p, hp, hpgt, hmod0⟩
    have hklt : 2 ^ k < n := C1 hkK
    have hmPos : 0 < M n k := by
      unfold M
      exact Nat.sub_pos_of_lt hklt
    have hp2dvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 hmod0
    have hp2_le_m : p ^ 2 <= M n k := Nat.le_of_dvd hmPos hp2dvd
    have hp2_le_n : p ^ 2 <= n := le_trans hp2_le_m (Nat.sub_le n (2 ^ k))
    have hp_le_sq : p <= p ^ 2 := by
      calc
        p = p * 1 := by simp
        _ <= p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hp.pos)
        _ = p ^ 2 := by simp [pow_two]
    have hp_le_n : p <= n := le_trans hp_le_sq hp2_le_n
    have hpIcc : p ∈ Finset.Icc (z n + 1) n := Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt hpgt, hp_le_n⟩
    have hpLarge : p ∈ largePrimeSupport n := by
      unfold largePrimeSupport
      exact Finset.mem_filter.mpr ⟨hpIcc, hp⟩
    have hpSq : p ∈ largePrimeSupportSq n := by
      unfold largePrimeSupportSq
      exact Finset.mem_filter.mpr ⟨hpLarge, hp2_le_n⟩
    have hkBadAt : k ∈ badAt p := Finset.mem_filter.mpr ⟨hkA, hmod0⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpSq, hkBadAt⟩
  calc
    (A n (z n)).card <= ((largePrimeSupportSq n).biUnion badAt).card := Finset.card_le_card hsubset
    _ <= Finset.sum (largePrimeSupportSq n) (fun p => (badAt p).card) := Finset.card_biUnion_le
    _ = Finset.sum (largePrimeSupportSq n) (fun p => cleanNp n (z n) p) := by
          simp [badAt, cleanNp]

lemma A_large_prime_decomp_sq_cleanSupport_of_not_represents {n : Nat}
    (hNotRep : ¬ Represents n) :
    (A n (z n)).card <= Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
  calc
    (A n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => cleanNp n (z n) p) := by
      exact A_large_prime_decomp_sq_clean_of_not_represents hNotRep
    _ = Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
      symm
      exact sum_cleanNp_largePrimeSupportSq_eq_sum_largePrimeCleanSupportSq n

lemma A_large_prime_decomp_sq_cleanSupport_nonWieferich_card_add_wieferich_sum_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (A n (z n)).card <=
      (nonWieferichLargePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
  calc
    (A n (z n)).card <= Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
      exact A_large_prime_decomp_sq_cleanSupport_of_not_represents hNotRep
    _ = (nonWieferichLargePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
            exact sum_cleanNp_largePrimeCleanSupportSq_eq_nonWieferich_card_add_wieferich_sum n hz3

lemma A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_excess_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (A n (z n)).card <=
      (largePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
  calc
    (A n (z n)).card <= Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
      exact A_large_prime_decomp_sq_cleanSupport_of_not_represents hNotRep
    _ = (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
            exact sum_cleanNp_largePrimeCleanSupportSq_eq_card_add_wieferich_excess n hz3

/-- Clean large-prime mass: clean support plus clean Wieferich excess. -/
noncomputable def cleanLargePrimeMass (n : Nat) : Nat :=
  (largePrimeCleanSupportSq n).card +
    Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1)

lemma A_large_prime_decomp_sq_cleanLargePrimeMass_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (A n (z n)).card <= cleanLargePrimeMass n := by
  simpa [cleanLargePrimeMass] using
    A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_excess_of_not_represents hNotRep hz3

lemma card_K_le_smallPrimeBad_add_cleanLargePrimeMass_of_not_represents {n : Nat}
    (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (K n).card <= (smallPrimeBad n (z n)).card + cleanLargePrimeMass n := by
  have hKs :
      (K n).card - (smallPrimeBad n (z n)).card <= cleanLargePrimeMass n := by
    simpa [card_A_eq_card_K_sub_smallPrimeBad n (z n)] using
      (A_large_prime_decomp_sq_cleanLargePrimeMass_of_not_represents hNotRep hz3)
  have hK_le :
      (K n).card <= cleanLargePrimeMass n + (smallPrimeBad n (z n)).card :=
    (Nat.sub_le_iff_le_add).1 hKs
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hK_le

lemma sum_cleanNp_largePrimeCleanSupportSq_le_sum_localOrderBound (n : Nat) :
    Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
      Finset.sum (largePrimeCleanSupportSq n) (fun p => localOrderBound n p) := by
  exact Finset.sum_le_sum (by
    intro p hp
    have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hp).1
    have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
    calc
      cleanNp n (z n) p <= Np n p := cleanNp_le_Np n (z n) p
      _ <= localOrderBound n p := Np_le_localOrderBound_of_largePrimeSupport n p hpLarge)

lemma cleanLargePrimeMass_le_card_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    cleanLargePrimeMass n <=
      (largePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n)
          (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
  classical
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  have hsplit :
      Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
    symm
    simpa [wieferichLargePrimeCleanSupportSq, nonWieferichLargePrimeCleanSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeCleanSupportSq n) (p := WieferichBase2) (f := fun p => cleanNp n (z n) p))
  have hW :
      Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
        Finset.sum (wieferichLargePrimeCleanSupportSq n)
          (fun p => (L n + 1) / (2 * Nat.log 2 p) + 1) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpClean : p ∈ largePrimeCleanSupportSq n := (Finset.mem_filter.mp hp).1
      have hpSq : p ∈ largePrimeSupportSq n := (Finset.mem_filter.mp hpClean).1
      have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
      calc
        cleanNp n (z n) p <= Np n p := cleanNp_le_Np n (z n) p
        _ <= localOrderBound n p := Np_le_localOrderBound_of_largePrimeSupport n p hpLarge
        _ <= (L n + 1) / (2 * Nat.log 2 p) + 1 := by
              exact localOrderBound_le_logPrime_add_one_of_largePrimeSupportSq hz2 hpSq)
  have hN :
      Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
        (nonWieferichLargePrimeCleanSupportSq n).card := by
    exact le_of_eq (sum_cleanNp_nonWieferichLargePrimeCleanSupportSq_eq_card n hz3)
  have hcard :
      (wieferichLargePrimeCleanSupportSq n).card +
          (nonWieferichLargePrimeCleanSupportSq n).card =
        (largePrimeCleanSupportSq n).card := by
    exact card_wieferich_add_card_nonWieferichLargePrimeCleanSupportSq n
  calc
    cleanLargePrimeMass n =
        Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
          symm
          exact sum_cleanNp_largePrimeCleanSupportSq_eq_card_add_wieferich_excess n hz3
    _ =
        Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          Finset.sum (nonWieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := hsplit
    _ <= Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p) + 1) +
          (nonWieferichLargePrimeCleanSupportSq n).card := by
          exact Nat.add_le_add hW hN
    _ = Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) +
          (wieferichLargePrimeCleanSupportSq n).card +
            (nonWieferichLargePrimeCleanSupportSq n).card := by
          rw [Finset.sum_add_distrib]
          simp
    _ = Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) +
          ((wieferichLargePrimeCleanSupportSq n).card +
            (nonWieferichLargePrimeCleanSupportSq n).card) := by
          ac_rfl
    _ = Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) +
          (largePrimeCleanSupportSq n).card := by
          rw [hcard]
    _ = (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
          ac_rfl

lemma A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_logPrime_excess_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (A n (z n)).card <=
      (largePrimeCleanSupportSq n).card +
        Finset.sum (wieferichLargePrimeCleanSupportSq n)
          (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
  exact le_trans
    (A_large_prime_decomp_sq_cleanLargePrimeMass_of_not_represents hNotRep hz3)
    (cleanLargePrimeMass_le_card_add_wieferich_logPrime_excess n hz3)

lemma card_K_le_smallPrimeBad_add_cleanSupport_card_add_wieferich_logPrime_excess_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (K n).card <=
      (smallPrimeBad n (z n)).card +
        ((largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  have hKs :
      (K n).card - (smallPrimeBad n (z n)).card <=
        (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
    simpa [card_A_eq_card_K_sub_smallPrimeBad n (z n)] using
      (A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_logPrime_excess_of_not_represents
        hNotRep hz3)
  have hK_le :
      (K n).card <=
        ((largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) +
          (smallPrimeBad n (z n)).card :=
    (Nat.sub_le_iff_le_add).1 hKs
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hK_le

lemma sum_localOrderBound_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) =
      (nonWieferichSubsupport S).card +
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) := by
  classical
  have hNonSub : nonWieferichSubsupport S ⊆ nonWieferichLargePrimeActiveSupportSq n := by
    intro p hp
    have hpS : p ∈ S := by
      simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
    have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
    have hpNot : ¬ WieferichBase2 p := by
      simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
    _ = Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          (nonWieferichSubsupport S).card := by
            rw [sum_localOrderBound_nonWieferichLargePrimeActiveSubset_eq_card
              n (nonWieferichSubsupport S) hNonSub hz3]
    _ = (nonWieferichSubsupport S).card +
          Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) := by
            ac_rfl

lemma activeWieferich_one_split_eq_activeSubset_one_add_excess
    (n : Nat) (S : Finset Nat) :
    (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) + (nonWieferichSubsupport S).card =
      S.card + (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 1) := by
  classical
  let a := (wieferichSubsupport S).card
  let b := (nonWieferichSubsupport S).card
  let h := (L n + 1) / 2 + 1
  have hh : 1 <= h := by
    dsimp [h]
    omega
  have hab : a + b = S.card := by
    dsimp [a, b]
    simpa [wieferichSubsupport, nonWieferichSubsupport] using
      (Finset.card_filter_add_card_filter_not (s := S) (p := WieferichBase2))
  calc
    a * h + b = a * ((h - 1) + 1) + b := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 1) + a + b := by
          rw [Nat.mul_add, Nat.mul_one]
    _ = a * (h - 1) + (a + b) := by omega
    _ = a * (h - 1) + S.card := by rw [hab]
    _ = S.card + a * (h - 1) := by ac_rfl
    _ = S.card + (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 1) := by
          rfl

lemma activeWieferich_one_split_eq_activeSubset_one_add_excess_of_h
    (S : Finset Nat) (h : Nat) (hh : 1 <= h) :
    (wieferichSubsupport S).card * h + (nonWieferichSubsupport S).card =
      S.card + (wieferichSubsupport S).card * (h - 1) := by
  classical
  let a := (wieferichSubsupport S).card
  let b := (nonWieferichSubsupport S).card
  have hab : a + b = S.card := by
    dsimp [a, b]
    simpa [wieferichSubsupport, nonWieferichSubsupport] using
      (Finset.card_filter_add_card_filter_not (s := S) (p := WieferichBase2))
  calc
    a * h + b = a * ((h - 1) + 1) + b := by rw [Nat.sub_add_cancel hh]
    _ = a * (h - 1) + a + b := by rw [Nat.mul_add, Nat.mul_one]
    _ = a * (h - 1) + (a + b) := by omega
    _ = a * (h - 1) + S.card := by rw [hab]
    _ = S.card + a * (h - 1) := by ac_rfl
    _ = S.card + (wieferichSubsupport S).card * (h - 1) := by rfl

lemma sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_excess
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card + (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 1) := by
  classical
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
    _ <= (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) +
          (nonWieferichSubsupport S).card := by
            exact Nat.add_le_add
              (by
                calc
                  Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) <=
                      Finset.sum (wieferichSubsupport S) (fun _ => (L n + 1) / 2 + 1) := by
                        exact Finset.sum_le_sum (by
                          intro p hpS
                          have hpAct : p ∈ largePrimeActiveSupportSq n := by
                            have hpMem : p ∈ S := by
                              simpa [wieferichSubsupport] using (Finset.mem_filter.mp hpS).1
                            exact hS hpMem
                          have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
                          exact localOrderBound_le_half_add_one_of_largePrimeSupportSq hz2 hpSq)
                  _ = (wieferichSubsupport S).card * ((L n + 1) / 2 + 1) := by simp)
              (sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_card
                n (nonWieferichSubsupport S)
                (by
                  intro p hp
                  have hpS : p ∈ S := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
                  have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
                  have hpNot : ¬ WieferichBase2 p := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
                  exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩)
                hz3)
    _ = S.card + (wieferichSubsupport S).card * (((L n + 1) / 2 + 1) - 1) := by
          exact activeWieferich_one_split_eq_activeSubset_one_add_excess n S

lemma sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_third_excess
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card + (wieferichSubsupport S).card * (((L n + 1) / 3 + 1) - 1) := by
  classical
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
    _ <= (wieferichSubsupport S).card * ((L n + 1) / 3 + 1) +
          (nonWieferichSubsupport S).card := by
            exact Nat.add_le_add
              (by
                calc
                  Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) <=
                      Finset.sum (wieferichSubsupport S) (fun _ => (L n + 1) / 3 + 1) := by
                        exact Finset.sum_le_sum (by
                          intro p hpS
                          have hpAct : p ∈ largePrimeActiveSupportSq n := by
                            have hpMem : p ∈ S := by
                              simpa [wieferichSubsupport] using (Finset.mem_filter.mp hpS).1
                            exact hS hpMem
                          have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
                          exact localOrderBound_le_third_add_one_of_largePrimeSupportSq hz3 hpSq)
                  _ = (wieferichSubsupport S).card * ((L n + 1) / 3 + 1) := by simp)
              (sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_card
                n (nonWieferichSubsupport S)
                (by
                  intro p hp
                  have hpS : p ∈ S := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
                  have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
                  have hpNot : ¬ WieferichBase2 p := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
                  exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩)
                hz3)
    _ = S.card + (wieferichSubsupport S).card * (((L n + 1) / 3 + 1) - 1) := by
          exact activeWieferich_one_split_eq_activeSubset_one_add_excess_of_h
            S (((L n + 1) / 3) + 1) (by omega)

lemma sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_div_excess
    (n : Nat) (S : Finset Nat) (d : Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n)
    (hpow : 2 ^ d < (z n + 1) ^ 2) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card + (wieferichSubsupport S).card * ((((L n + 1) / (d + 1)) + 1) - 1) := by
  classical
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
            symm
            simpa [wieferichSubsupport, nonWieferichSubsupport] using
              (Finset.sum_filter_add_sum_filter_not
                (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
    _ <= (wieferichSubsupport S).card * (((L n + 1) / (d + 1)) + 1) +
          (nonWieferichSubsupport S).card := by
            exact Nat.add_le_add
              (by
                calc
                  Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) <=
                      Finset.sum (wieferichSubsupport S) (fun _ => ((L n + 1) / (d + 1)) + 1) := by
                        exact Finset.sum_le_sum (by
                          intro p hpS
                          have hpAct : p ∈ largePrimeActiveSupportSq n := by
                            have hpMem : p ∈ S := by
                              simpa [wieferichSubsupport] using (Finset.mem_filter.mp hpS).1
                            exact hS hpMem
                          have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
                          exact localOrderBound_le_div_add_one_of_largePrimeSupportSq hz2 hpSq hpow)
                  _ = (wieferichSubsupport S).card * (((L n + 1) / (d + 1)) + 1) := by simp)
              (sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_card
                n (nonWieferichSubsupport S)
                (by
                  intro p hp
                  have hpS : p ∈ S := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
                  have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
                  have hpNot : ¬ WieferichBase2 p := by
                    simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
                  exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩)
                hz3)
    _ = S.card + (wieferichSubsupport S).card * ((((L n + 1) / (d + 1)) + 1) - 1) := by
          exact activeWieferich_one_split_eq_activeSubset_one_add_excess_of_h
            S (((L n + 1) / (d + 1)) + 1) (Nat.succ_le_succ (Nat.zero_le _))

lemma sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_log_excess
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card + (wieferichSubsupport S).card *
        ((((L n + 1) / (2 * Nat.log 2 (z n + 1))) + 1) - 1) := by
  have hm : 2 <= z n + 1 := by omega
  have hm1 : 1 < z n + 1 := lt_of_lt_of_le (by decide : 1 < 2) hm
  have hpow :
      2 ^ (2 * Nat.log 2 (z n + 1) - 1) < (z n + 1) ^ 2 :=
    two_pow_two_mul_log_sub_one_lt_sq hm
  have hmain :=
    sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_div_excess
      n S (2 * Nat.log 2 (z n + 1) - 1) hS hz3 hpow
  have hlogPos : 1 <= 2 * Nat.log 2 (z n + 1) := by
    have hlog : 0 < Nat.log 2 (z n + 1) := Nat.log_pos Nat.one_lt_two hm1
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hlog)
  have hden :
      (2 * Nat.log 2 (z n + 1) - 1) + 1 = 2 * Nat.log 2 (z n + 1) :=
    Nat.sub_add_cancel hlogPos
  simpa [hden] using hmain

lemma sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_logPrime_excess
    (n : Nat) (S : Finset Nat)
    (hS : S ⊆ largePrimeActiveSupportSq n) (hz3 : 3 <= z n) :
    Finset.sum S (fun p => localOrderBound n p) <=
      S.card + Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
  classical
  have hz2 : 2 <= z n := le_trans (by decide : 2 <= 3) hz3
  have hsplit :
      Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := by
    symm
    simpa [wieferichSubsupport, nonWieferichSubsupport] using
      (Finset.sum_filter_add_sum_filter_not
        (s := S) (p := WieferichBase2) (f := fun p => localOrderBound n p))
  have hW :
      Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) <=
        Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p) + 1) := by
    exact Finset.sum_le_sum (by
      intro p hpS
      have hpAct : p ∈ largePrimeActiveSupportSq n := by
        have hpMem : p ∈ S := by
          simpa [wieferichSubsupport] using (Finset.mem_filter.mp hpS).1
        exact hS hpMem
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact localOrderBound_le_logPrime_add_one_of_largePrimeSupportSq hz2 hpSq)
  have hN :
      Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) <=
        (nonWieferichSubsupport S).card := by
    exact sum_localOrderBound_nonWieferichLargePrimeActiveSubset_le_card
      n (nonWieferichSubsupport S)
      (by
        intro p hp
        have hpS : p ∈ S := by
          simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).1
        have hpAct : p ∈ largePrimeActiveSupportSq n := hS hpS
        have hpNot : ¬ WieferichBase2 p := by
          simpa [nonWieferichSubsupport] using (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨hpAct, hpNot⟩)
      hz3
  have hcard :
      (wieferichSubsupport S).card + (nonWieferichSubsupport S).card = S.card := by
    simpa [wieferichSubsupport, nonWieferichSubsupport] using
      (Finset.card_filter_add_card_filter_not (s := S) (p := WieferichBase2))
  calc
    Finset.sum S (fun p => localOrderBound n p) =
        Finset.sum (wieferichSubsupport S) (fun p => localOrderBound n p) +
          Finset.sum (nonWieferichSubsupport S) (fun p => localOrderBound n p) := hsplit
    _ <= Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p) + 1) +
          (nonWieferichSubsupport S).card := by
            exact Nat.add_le_add hW hN
    _ = Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p)) +
          (wieferichSubsupport S).card + (nonWieferichSubsupport S).card := by
            rw [Finset.sum_add_distrib]
            simp
    _ = Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p)) +
          ((wieferichSubsupport S).card + (nonWieferichSubsupport S).card) := by
            ac_rfl
    _ = Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p)) + S.card := by
            rw [hcard]
    _ = S.card + Finset.sum (wieferichSubsupport S) (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
            ac_rfl

lemma sum_cleanNp_veryLargePrimeCleanSupportSq_le_L_add_one (n : Nat) :
    Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <= L n + 1 := by
  have hCleanNp :
      Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
        Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => Np n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      exact cleanNp_le_Np n (z n) p)
  have hSubset :
      Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => Np n p) <=
        Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (veryLargePrimeCleanSupportSq_subset_veryLargePrimeActiveSupportSq n)
      (by
        intro p hp1 hp2
        exact Nat.zero_le (Np n p))
  exact le_trans hCleanNp <|
    le_trans hSubset <|
      le_trans (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) (card_K_le n)

lemma sum_cleanNp_lowFourthPrimeCleanSupportSq_le_card_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
      (lowFourthPrimeCleanSupportSq n).card +
        Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
          (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
  have hCleanLocal :
      Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) <=
        Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpClean : p ∈ largePrimeCleanSupportSq n := lowFourthPrimeCleanSupportSq_subset n hp
      have hpAct : p ∈ largePrimeActiveSupportSq n :=
        largePrimeCleanSupportSq_subset_largePrimeActiveSupportSq n hpClean
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      have hpLarge : p ∈ largePrimeSupport n := (Finset.mem_filter.mp hpSq).1
      calc
        cleanNp n (z n) p <= Np n p := cleanNp_le_Np n (z n) p
        _ <= localOrderBound n p := Np_le_localOrderBound_of_largePrimeSupport n p hpLarge)
  have hLocal :
      Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => localOrderBound n p) <=
        (lowFourthPrimeCleanSupportSq n).card +
          Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
    simpa [wieferichSubsupport, wieferichLowFourthPrimeCleanSupportSq] using
      (sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_logPrime_excess
        n (lowFourthPrimeCleanSupportSq n)
        (lowFourthPrimeCleanSupportSq_subset_largePrimeActiveSupportSq n) hz3)
  exact le_trans hCleanLocal hLocal

lemma cleanLargePrimeMass_le_lowFourth_card_add_L_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    cleanLargePrimeMass n <=
      (L n + 1) +
        ((lowFourthPrimeCleanSupportSq n).card +
          Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  have hsplit :
      Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) =
        Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
    symm
    simpa [veryLargePrimeCleanSupportSq, lowFourthPrimeCleanSupportSq, Nat.not_lt] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeCleanSupportSq n) (p := fun p => n < p ^ 4)
        (f := fun p => cleanNp n (z n) p))
  calc
    cleanLargePrimeMass n =
        Finset.sum (largePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := by
          symm
          exact sum_cleanNp_largePrimeCleanSupportSq_eq_card_add_wieferich_excess n hz3
    _ = Finset.sum (veryLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) +
          Finset.sum (lowFourthPrimeCleanSupportSq n) (fun p => cleanNp n (z n) p) := hsplit
    _ <= (L n + 1) +
          ((lowFourthPrimeCleanSupportSq n).card +
            Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
          exact Nat.add_le_add
            (sum_cleanNp_veryLargePrimeCleanSupportSq_le_L_add_one n)
            (sum_cleanNp_lowFourthPrimeCleanSupportSq_le_card_add_wieferich_logPrime_excess n hz3)

lemma A_large_prime_decomp_sq_cleanSupport_lowFourth_card_add_L_add_wieferich_logPrime_excess_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (A n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeCleanSupportSq n).card +
          Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  exact le_trans
    (A_large_prime_decomp_sq_cleanLargePrimeMass_of_not_represents hNotRep hz3)
    (cleanLargePrimeMass_le_lowFourth_card_add_L_add_wieferich_logPrime_excess n hz3)

lemma card_K_le_smallPrimeBad_add_cleanSupport_lowFourth_card_add_L_add_wieferich_logPrime_excess_of_not_represents
    {n : Nat} (hNotRep : ¬ Represents n) (hz3 : 3 <= z n) :
    (K n).card <=
      (smallPrimeBad n (z n)).card +
        ((L n + 1) +
          ((lowFourthPrimeCleanSupportSq n).card +
            Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
              (fun p => (L n + 1) / (2 * Nat.log 2 p)))) := by
  have hKs :
      (K n).card - (smallPrimeBad n (z n)).card <=
        (L n + 1) +
          ((lowFourthPrimeCleanSupportSq n).card +
            Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
    simpa [card_A_eq_card_K_sub_smallPrimeBad n (z n)] using
      (A_large_prime_decomp_sq_cleanSupport_lowFourth_card_add_L_add_wieferich_logPrime_excess_of_not_represents
        hNotRep hz3)
  have hK_le :
      (K n).card <=
        ((L n + 1) +
          ((lowFourthPrimeCleanSupportSq n).card +
            Finset.sum (wieferichLowFourthPrimeCleanSupportSq n)
              (fun p => (L n + 1) / (2 * Nat.log 2 p)))) +
          (smallPrimeBad n (z n)).card := by
    exact (Nat.sub_le_iff_le_add).1 hKs
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hK_le

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

lemma pow_two_mod_twenty_five_cycle (t : Nat) : (2 ^ (20 * t)) % 25 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 20 * (t + 1) = 20 * t + 20 := by omega
      rw [hExp, Nat.pow_add]
      norm_num [Nat.mul_mod, ih]

lemma pow_two_mod_twenty_five_of_mod20_eq0 {k : Nat} (hkmod : k % 20 = 0) :
    (2 ^ k) % 25 = 1 := by
  have hkdecomp : k = 20 * (k / 20) := by
    have hdiv : k % 20 + 20 * (k / 20) = k := Nat.mod_add_div k 20
    omega
  rw [hkdecomp]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    pow_two_mod_twenty_five_cycle (k / 20)

lemma pow_two_mod_forty_nine_cycle (t : Nat) : (2 ^ (21 * t)) % 49 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 21 * (t + 1) = 21 * t + 21 := by omega
      rw [hExp, Nat.pow_add]
      norm_num [Nat.mul_mod, ih]

lemma pow_two_mod_forty_nine_of_mod42_eq3 {k : Nat} (hkmod : k % 42 = 3) :
    (2 ^ k) % 49 = 8 := by
  have hkdecomp : k = 42 * (k / 42) + 3 := by
    have hdiv : k % 42 + 42 * (k / 42) = k := Nat.mod_add_div k 42
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (42 * (k / 42))) % 49 = 1 := by
    have hExp : 42 * (k / 42) = 21 * (2 * (k / 42)) := by omega
    rw [hExp]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_forty_nine_cycle (2 * (k / 42))
  calc
    (2 ^ (42 * (k / 42)) * 2 ^ 3) % 49 =
        (2 ^ (42 * (k / 42)) % 49 * (2 ^ 3 % 49)) % 49 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 8) % 49 := by
      rw [hcycle]
      norm_num
    _ = 8 := by norm_num

lemma pow_two_mod_one_twenty_one_cycle (t : Nat) : (2 ^ (110 * t)) % 121 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 110 * (t + 1) = 110 * t + 110 := by omega
      rw [hExp, Nat.pow_add]
      norm_num [Nat.mul_mod, ih]

lemma pow_two_mod_one_twenty_one_of_mod110_eq6 {k : Nat} (hkmod : k % 110 = 6) :
    (2 ^ k) % 121 = 64 := by
  have hkdecomp : k = 110 * (k / 110) + 6 := by
    have hdiv : k % 110 + 110 * (k / 110) = k := Nat.mod_add_div k 110
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (110 * (k / 110))) % 121 = 1 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_one_twenty_one_cycle (k / 110)
  calc
    (2 ^ (110 * (k / 110)) * 2 ^ 6) % 121 =
        (2 ^ (110 * (k / 110)) % 121 * (2 ^ 6 % 121)) % 121 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 64) % 121 := by
      rw [hcycle]
      norm_num
    _ = 64 := by norm_num

lemma pow_two_mod_one_sixty_nine_cycle (t : Nat) : (2 ^ (156 * t)) % 169 = 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 156 * (t + 1) = 156 * t + 156 := by omega
      rw [hExp, Nat.pow_add]
      norm_num [Nat.mul_mod, ih]

lemma pow_two_mod_one_sixty_nine_of_mod156_eq11 {k : Nat} (hkmod : k % 156 = 11) :
    (2 ^ k) % 169 = 20 := by
  have hkdecomp : k = 156 * (k / 156) + 11 := by
    have hdiv : k % 156 + 156 * (k / 156) = k := Nat.mod_add_div k 156
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (156 * (k / 156))) % 169 = 1 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_one_sixty_nine_cycle (k / 156)
  calc
    (2 ^ (156 * (k / 156)) * 2 ^ 11) % 169 =
        (2 ^ (156 * (k / 156)) % 169 * (2 ^ 11 % 169)) % 169 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 20) % 169 := by
      rw [hcycle]
      norm_num
    _ = 20 := by norm_num

lemma pow_two_mod_sixteen_eighty_one_cycle (t : Nat) : (2 ^ (820 * t)) % 1681 = 1 := by
  have hbase : 2 ^ 820 % 1681 = 1 := by
    set_option maxRecDepth 1000000 in
      decide
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 820 * (t + 1) = 820 * t + 820 := by omega
      rw [hExp, Nat.pow_add]
      calc
        (2 ^ (820 * t) * 2 ^ 820) % 1681 =
            (2 ^ (820 * t) % 1681 * (2 ^ 820 % 1681)) % 1681 := by
              simp [Nat.mul_mod, Nat.mul_comm]
        _ = (1 * 1) % 1681 := by rw [ih, hbase]
        _ = 1 := by norm_num

lemma pow_two_mod_sixteen_eighty_one_of_mod820_eq2 {k : Nat} (hkmod : k % 820 = 2) :
    (2 ^ k) % 1681 = 4 := by
  have hkdecomp : k = 820 * (k / 820) + 2 := by
    have hdiv : k % 820 + 820 * (k / 820) = k := Nat.mod_add_div k 820
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (820 * (k / 820))) % 1681 = 1 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_sixteen_eighty_one_cycle (k / 820)
  calc
    (2 ^ (820 * (k / 820)) * 2 ^ 2) % 1681 =
        (2 ^ (820 * (k / 820)) % 1681 * (2 ^ 2 % 1681)) % 1681 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 4) % 1681 := by
      rw [hcycle]
      norm_num
    _ = 4 := by norm_num

lemma pow_two_mod_thirteen_sixty_nine_cycle (t : Nat) : (2 ^ (1332 * t)) % 1369 = 1 := by
  have hbase : 2 ^ 1332 % 1369 = 1 := by
    set_option maxRecDepth 1000000 in
      decide
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 1332 * (t + 1) = 1332 * t + 1332 := by omega
      rw [hExp, Nat.pow_add]
      calc
        (2 ^ (1332 * t) * 2 ^ 1332) % 1369 =
            (2 ^ (1332 * t) % 1369 * (2 ^ 1332 % 1369)) % 1369 := by
              simp [Nat.mul_mod, Nat.mul_comm]
        _ = (1 * 1) % 1369 := by rw [ih, hbase]
        _ = 1 := by norm_num

lemma pow_two_mod_thirteen_sixty_nine_of_mod1332_eq5 {k : Nat} (hkmod : k % 1332 = 5) :
    (2 ^ k) % 1369 = 32 := by
  have hkdecomp : k = 1332 * (k / 1332) + 5 := by
    have hdiv : k % 1332 + 1332 * (k / 1332) = k := Nat.mod_add_div k 1332
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (1332 * (k / 1332))) % 1369 = 1 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_thirteen_sixty_nine_cycle (k / 1332)
  calc
    (2 ^ (1332 * (k / 1332)) * 2 ^ 5) % 1369 =
        (2 ^ (1332 * (k / 1332)) % 1369 * (2 ^ 5 % 1369)) % 1369 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 32) % 1369 := by
      rw [hcycle]
      norm_num
    _ = 32 := by norm_num

lemma pow_two_mod_thirty_seven_twenty_one_cycle (t : Nat) : (2 ^ (3660 * t)) % 3721 = 1 := by
  have hbase : 2 ^ 3660 % 3721 = 1 := by
    set_option maxRecDepth 1000000 in
      decide
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hExp : 3660 * (t + 1) = 3660 * t + 3660 := by omega
      rw [hExp, Nat.pow_add]
      calc
        (2 ^ (3660 * t) * 2 ^ 3660) % 3721 =
            (2 ^ (3660 * t) % 3721 * (2 ^ 3660 % 3721)) % 3721 := by
              simp [Nat.mul_mod, Nat.mul_comm]
        _ = (1 * 1) % 3721 := by rw [ih, hbase]
        _ = 1 := by norm_num

lemma pow_two_mod_thirty_seven_twenty_one_of_mod3660_eq4 {k : Nat} (hkmod : k % 3660 = 4) :
    (2 ^ k) % 3721 = 16 := by
  have hkdecomp : k = 3660 * (k / 3660) + 4 := by
    have hdiv : k % 3660 + 3660 * (k / 3660) = k := Nat.mod_add_div k 3660
    omega
  rw [hkdecomp, Nat.pow_add]
  have hcycle : (2 ^ (3660 * (k / 3660))) % 3721 = 1 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      pow_two_mod_thirty_seven_twenty_one_cycle (k / 3660)
  calc
    (2 ^ (3660 * (k / 3660)) * 2 ^ 4) % 3721 =
        (2 ^ (3660 * (k / 3660)) % 3721 * (2 ^ 4 % 3721)) % 3721 := by
      simp [Nat.mul_mod, Nat.mul_comm]
    _ = (1 * 16) % 3721 := by
      rw [hcycle]
      norm_num
    _ = 16 := by norm_num

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

lemma k_not_mem_A_of_mod25_class {n k : Nat}
    (hz5 : 5 <= z n) (hmod25 : n % 25 = 1) (hkmod20 : k % 20 = 0) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk25 : (2 ^ k) % 25 = 1 := pow_two_mod_twenty_five_of_mod20_eq0 hkmod20
  have hmod0 : (M n k) % (5 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 25 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 5 (by decide) hz5 hmod0

lemma k_not_mem_A_of_mod49_class {n k : Nat}
    (hz7 : 7 <= z n) (hmod49 : n % 49 = 8) (hkmod42 : k % 42 = 3) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk49 : (2 ^ k) % 49 = 8 := pow_two_mod_forty_nine_of_mod42_eq3 hkmod42
  have hmod0 : (M n k) % (7 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 49 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 7 (by decide) hz7 hmod0

lemma k_not_mem_A_of_mod121_class {n k : Nat}
    (hz11 : 11 <= z n) (hmod121 : n % 121 = 64) (hkmod110 : k % 110 = 6) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk121 : (2 ^ k) % 121 = 64 := pow_two_mod_one_twenty_one_of_mod110_eq6 hkmod110
  have hmod0 : (M n k) % (11 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 121 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 11 (by decide) hz11 hmod0

lemma k_not_mem_A_of_mod169_class {n k : Nat}
    (hz13 : 13 <= z n) (hmod169 : n % 169 = 20) (hkmod156 : k % 156 = 11) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk169 : (2 ^ k) % 169 = 20 := pow_two_mod_one_sixty_nine_of_mod156_eq11 hkmod156
  have hmod0 : (M n k) % (13 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 169 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 13 (by decide) hz13 hmod0

lemma k_not_mem_A_of_mod1681_class {n k : Nat}
    (hz41 : 41 <= z n) (hmod1681 : n % 1681 = 4) (hkmod820 : k % 820 = 2) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk1681 : (2 ^ k) % 1681 = 4 := pow_two_mod_sixteen_eighty_one_of_mod820_eq2 hkmod820
  have hmod0 : (M n k) % (41 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 1681 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 41 (by decide) hz41 hmod0

lemma k_not_mem_A_of_mod1369_class {n k : Nat}
    (hz37 : 37 <= z n) (hmod1369 : n % 1369 = 32) (hkmod1332 : k % 1332 = 5) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk1369 : (2 ^ k) % 1369 = 32 := pow_two_mod_thirteen_sixty_nine_of_mod1332_eq5 hkmod1332
  have hmod0 : (M n k) % (37 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 1369 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 37 (by decide) hz37 hmod0

lemma k_not_mem_A_of_mod3721_class {n k : Nat}
    (hz61 : 61 <= z n) (hmod3721 : n % 3721 = 16) (hkmod3660 : k % 3660 = 4) :
    k ∉ A n (z n) := by
  classical
  intro hkA
  have hsmall :
      forall p : Nat, Nat.Prime p -> p <= z n -> Not ((M n k) % (p ^ 2) = 0) :=
    (Finset.mem_filter.mp hkA).2
  have hk3721 : (2 ^ k) % 3721 = 16 := pow_two_mod_thirty_seven_twenty_one_of_mod3660_eq4 hkmod3660
  have hmod0 : (M n k) % (61 ^ 2) = 0 := by
    unfold M
    have : (n - 2 ^ k) % 3721 = 0 := by
      omega
    simpa [pow_two] using this
  exact hsmall 61 (by decide) hz61 hmod0

lemma mod9_class_one_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hmod9 : n % 9 = 2) :
    {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 1 [MOD 6] := (Finset.mem_filter.mp hk).2
  have hkmod : k % 6 = 1 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod9_class hz3 hmod9 hkmod
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma card_A_le_L_add_one_sub_div_six_of_mod9 {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hmod9 : n % 9 = 2) :
    (A n (z n)).card <= L n + 1 - L n / 6 := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS6card : L n / 6 <= S6.card := by
    have hcard :=
      card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hLower : L n / 6 <= (K n \ A n (z n)).card := le_trans hS6card (Finset.card_le_card hS6sub)
  have hAdd :
      (L n / 6) + (A n (z n)).card <= (K n).card := by
    have h1 : (L n / 6) + (A n (z n)).card <=
        (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' : (A n (z n)).card + (L n / 6) <= (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K : (A n (z n)).card <= (K n).card - L n / 6 := Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <= (K n).card - L n / 6 := hA_le_K
    _ <= (L n + 1) - L n / 6 := Nat.sub_le_sub_right (card_K_le n) (L n / 6)

lemma mod25_class_zero_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz5 : 5 <= z n) (hmod25 : n % 25 = 1) :
    {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 0 [MOD 20] := (Finset.mem_filter.mp hk).2
  have hkmod20 : k % 20 = 0 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod25_class hz5 hmod25 hkmod20
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod49_class_three_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz7 : 7 <= z n) (hmod49 : n % 49 = 8) :
    {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 3 [MOD 42] := (Finset.mem_filter.mp hk).2
  have hkmod42 : k % 42 = 3 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod49_class hz7 hmod49 hkmod42
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod121_class_six_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz11 : 11 <= z n) (hmod121 : n % 121 = 64) :
    {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 6 [MOD 110] := (Finset.mem_filter.mp hk).2
  have hkmod110 : k % 110 = 6 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod121_class hz11 hmod121 hkmod110
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod169_class_eleven_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz13 : 13 <= z n) (hmod169 : n % 169 = 20) :
    {k ∈ Finset.range (L n) | k ≡ 11 [MOD 156]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 11 [MOD 156] := (Finset.mem_filter.mp hk).2
  have hkmod156 : k % 156 = 11 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod169_class hz13 hmod169 hkmod156
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod1681_class_two_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz41 : 41 <= z n) (hmod1681 : n % 1681 = 4) :
    {k ∈ Finset.range (L n) | k ≡ 2 [MOD 820]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 2 [MOD 820] := (Finset.mem_filter.mp hk).2
  have hkmod820 : k % 820 = 2 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod1681_class hz41 hmod1681 hkmod820
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod1369_class_five_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz37 : 37 <= z n) (hmod1369 : n % 1369 = 32) :
    {k ∈ Finset.range (L n) | k ≡ 5 [MOD 1332]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 5 [MOD 1332] := (Finset.mem_filter.mp hk).2
  have hkmod1332 : k % 1332 = 5 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod1369_class hz37 hmod1369 hkmod1332
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod3721_class_four_range_subset_K_sdiff_A {n : Nat}
    (hn0 : n ≠ 0) (hz61 : 61 <= z n) (hmod3721 : n % 3721 = 16) :
    {k ∈ Finset.range (L n) | k ≡ 4 [MOD 3660]} ⊆ K n \ A n (z n) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (L n) := (Finset.mem_filter.mp hk).1
  have hkLt : k < L n := Finset.mem_range.mp hkRange
  have hkModEq : k ≡ 4 [MOD 3660] := (Finset.mem_filter.mp hk).2
  have hkmod3660 : k % 3660 = 4 := by
    simpa [Nat.ModEq] using hkModEq
  have hkPow : 2 ^ k < n := by
    unfold L at hkLt
    have hpow : 2 ^ k < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right Nat.one_lt_two hkLt
    have hle : 2 ^ Nat.log 2 n <= n := Nat.pow_log_le_self 2 hn0
    exact lt_of_lt_of_le hpow hle
  have hkK : k ∈ K n := mem_K_of_pow_lt hn0 hkPow
  have hkNotA : k ∉ A n (z n) := k_not_mem_A_of_mod3721_class hz61 hmod3721 hkmod3660
  exact Finset.mem_sdiff.mpr ⟨hkK, hkNotA⟩

lemma mod9_mod25_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk20
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk6To2 : k % 2 = 1 := by omega
  have hk20To2 : k % 2 = 0 := by omega
  have h10 : (1 : Nat) = 0 := hk6To2.symm.trans hk20To2
  exact Nat.one_ne_zero h10

lemma mod9_mod49_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk42
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk42To6 : k % 6 = 3 := by omega
  have : False := by omega
  exact this.elim

lemma mod20_mod49_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk42
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk20To2 : k % 2 = 0 := by omega
  have hk42To2 : k % 2 = 1 := by omega
  have h01 : (0 : Nat) = 1 := hk20To2.symm.trans hk42To2
  exact Nat.zero_ne_one h01

lemma mod9_mod121_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk110
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk6To2 : k % 2 = 1 := by omega
  have hk110To2 : k % 2 = 0 := by omega
  have h10 : (1 : Nat) = 0 := hk6To2.symm.trans hk110To2
  exact Nat.one_ne_zero h10

lemma mod20_mod121_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk110
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk20To10 : k % 10 = 0 := by omega
  have hk110To10 : k % 10 = 6 := by omega
  have h06 : (0 : Nat) = 6 := hk20To10.symm.trans hk110To10
  have : False := by omega
  exact this.elim

lemma mod49_mod121_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]}
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk42 hk110
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk42To2 : k % 2 = 1 := by omega
  have hk110To2 : k % 2 = 0 := by omega
  have h10 : (1 : Nat) = 0 := hk42To2.symm.trans hk110To2
  exact Nat.one_ne_zero h10

lemma mod9_mod169_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk156
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk156To6 : k % 6 = 5 := by omega
  have : False := by omega
  exact this.elim

lemma mod20_mod169_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk156
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk20To2 : k % 2 = 0 := by omega
  have hk156To2 : k % 2 = 1 := by omega
  have : False := by omega
  exact this.elim

lemma mod49_mod169_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]}
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk42 hk156
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk42To6 : k % 6 = 3 := by omega
  have hk156To6 : k % 6 = 5 := by omega
  have : False := by omega
  exact this.elim

lemma mod121_mod169_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]}
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk110 hk156
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk110To2 : k % 2 = 0 := by omega
  have hk156To2 : k % 2 = 1 := by omega
  have : False := by omega
  exact this.elim

lemma mod9_mod1681_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk820
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk6To2 : k % 2 = 1 := by omega
  have hk820To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma mod20_mod1681_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk820
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk820To20 : k % 20 = 2 := by omega
  have : False := by omega
  exact this.elim

lemma mod49_mod1681_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]}
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk42 hk820
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk42To2 : k % 2 = 1 := by omega
  have hk820To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma mod121_mod1681_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]}
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk110 hk820
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk110To10 : k % 10 = 6 := by omega
  have hk820To10 : k % 10 = 2 := by omega
  have : False := by omega
  exact this.elim

lemma mod169_mod1681_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]}
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk156 hk820
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk156To4 : k % 4 = 3 := by omega
  have hk820To4 : k % 4 = 2 := by omega
  have : False := by omega
  exact this.elim

lemma mod9_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk1332
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk1332To6 : k % 6 = 5 := by omega
  have : False := by omega
  exact this.elim

lemma mod20_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk1332
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk20To4 : k % 4 = 0 := by omega
  have hk1332To4 : k % 4 = 1 := by omega
  have : False := by omega
  exact this.elim

lemma mod49_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk42 hk1332
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk42To6 : k % 6 = 3 := by omega
  have hk1332To6 : k % 6 = 5 := by omega
  have : False := by omega
  exact this.elim

lemma mod121_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk110 hk1332
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk110To2 : k % 2 = 0 := by omega
  have hk1332To2 : k % 2 = 1 := by omega
  have : False := by omega
  exact this.elim

lemma mod169_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk156 hk1332
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk156To12 : k % 12 = 11 := by omega
  have hk1332To12 : k % 12 = 5 := by omega
  have : False := by omega
  exact this.elim

lemma mod1681_mod1369_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]}
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk820 hk1332
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk820To4 : k % 4 = 2 := by omega
  have hk1332To4 : k % 4 = 1 := by omega
  have : False := by omega
  exact this.elim

lemma mod9_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 1 [MOD 6]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk6 hk3660
  have hk6mod : k % 6 = 1 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk6).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk6To2 : k % 2 = 1 := by omega
  have hk3660To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma mod20_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 0 [MOD 20]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk20 hk3660
  have hk20mod : k % 20 = 0 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk20).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk3660To20 : k % 20 = 4 := by omega
  have : False := by omega
  exact this.elim

lemma mod49_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 3 [MOD 42]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk42 hk3660
  have hk42mod : k % 42 = 3 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk42).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk42To2 : k % 2 = 1 := by omega
  have hk3660To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma mod121_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 6 [MOD 110]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk110 hk3660
  have hk110mod : k % 110 = 6 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk110).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk110To10 : k % 10 = 6 := by omega
  have hk3660To10 : k % 10 = 4 := by omega
  have : False := by omega
  exact this.elim

lemma mod169_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 11 [MOD 156]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk156 hk3660
  have hk156mod : k % 156 = 11 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk156).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk156To2 : k % 2 = 1 := by omega
  have hk3660To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma mod1681_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 2 [MOD 820]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk820 hk3660
  have hk820mod : k % 820 = 2 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk820).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk820To20 : k % 20 = 2 := by omega
  have hk3660To20 : k % 20 = 4 := by omega
  have : False := by omega
  exact this.elim

lemma mod1369_mod3721_class_disjoint (m : Nat) :
    Disjoint
      {k ∈ Finset.range m | k ≡ 5 [MOD 1332]}
      {k ∈ Finset.range m | k ≡ 4 [MOD 3660]} := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk1332 hk3660
  have hk1332mod : k % 1332 = 5 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk1332).2
  have hk3660mod : k % 3660 = 4 := by
    simpa [Nat.ModEq] using (Finset.mem_filter.mp hk3660).2
  have hk1332To2 : k % 2 = 1 := by omega
  have hk3660To2 : k % 2 = 0 := by omega
  have : False := by omega
  exact this.elim

lemma card_A_le_L_add_one_sub_div_six_add_div_twenty_of_mod9_mod25 {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) :
    (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S : Finset Nat := S6 ∪ S20
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk6 | hk20
    · exact hS6sub hk6
    · exact hS20sub hk20
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hDisj : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hSCardEq : S.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S, hinter] using hcard
  have hLower : L n / 6 + L n / 20 <= (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 <= S6.card + S20.card := Nat.add_le_add hS6card hS20card
      _ = S.card := by symm; exact hSCardEq
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20) + (A n (z n)).card <= (K n).card := by
    have h1 : (L n / 6 + L n / 20) + (A n (z n)).card <=
        (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' : (A n (z n)).card + (L n / 6 + L n / 20) <= (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K : (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20) :=
      Nat.sub_le_sub_right (card_K_le n) (L n / 6 + L n / 20)

lemma card_A_le_L_add_one_sub_div_six_add_div_twenty_add_div_forty_two_of_mod9_mod25_mod49
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8) :
    (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S620 : Finset Nat := S6 ∪ S20
  let S : Finset Nat := S620 ∪ S42
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk620 | hk42
    · rcases Finset.mem_union.mp hk620 with hk6 | hk20
      · exact hS6sub hk6
      · exact hS20sub hk20
    · exact hS42sub hk42
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hScard : S.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S.card = S620.card + S42.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hLower : L n / 6 + L n / 20 + L n / 42 <= (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 + L n / 42 <= S6.card + S20.card + S42.card := by
        exact Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card
      _ = S.card := by symm; exact hScard
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42) + (A n (z n)).card <= (K n).card := by
    have h1 : (L n / 6 + L n / 20 + L n / 42) + (A n (z n)).card <=
        (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' : (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42) <= (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K : (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20 + L n / 42) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20 + L n / 42) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42) :=
      Nat.sub_le_sub_right (card_K_le n) (L n / 6 + L n / 20 + L n / 42)

lemma card_A_le_L_add_one_sub_div_6_20_42_110_of_mods
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n) (hz11 : 11 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8) (hmod121 : n % 121 = 64) :
    (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S110 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]}
  let S620 : Finset Nat := S6 ∪ S20
  let S62042 : Finset Nat := S620 ∪ S42
  let S : Finset Nat := S62042 ∪ S110
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hS110sub : S110 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod121_class_six_range_subset_K_sdiff_A hn0 hz11 hmod121 (by simpa [S110] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk62042 | hk110
    · rcases Finset.mem_union.mp hk62042 with hk620 | hk42
      · rcases Finset.mem_union.mp hk620 with hk6 | hk20
        · exact hS6sub hk6
        · exact hS20sub hk20
      · exact hS42sub hk42
    · exact hS110sub hk110
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hS110card : L n / 110 <= S110.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 110) (v := 6) (by decide : 0 < 110)
    simpa [S110] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hDisj6_110 : Disjoint S6 S110 := by
    simpa [S6, S110] using mod9_mod121_class_disjoint (L n)
  have hDisj20_110 : Disjoint S20 S110 := by
    simpa [S20, S110] using mod20_mod121_class_disjoint (L n)
  have hDisj42_110 : Disjoint S42 S110 := by
    simpa [S42, S110] using mod49_mod121_class_disjoint (L n)
  have hDisj620_110 : Disjoint S620 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk110
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_110) hk6 hk110
    · exact (Finset.disjoint_left.mp hDisj20_110) hk20 hk110
  have hDisj62042_110 : Disjoint S62042 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk110
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_110) hk620 hk110
    · exact (Finset.disjoint_left.mp hDisj42_110) hk42 hk110
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hS62042card : S62042.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S62042.card = S620.card + S42.card := by
        simpa [S62042, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hScard : S.card = S6.card + S20.card + S42.card + S110.card := by
    have hinter : S62042 ∩ S110 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj62042_110
    have hcard : (S62042 ∪ S110).card + (S62042 ∩ S110).card = S62042.card + S110.card :=
      Finset.card_union_add_card_inter S62042 S110
    calc
      S.card = S62042.card + S110.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card := by rw [hS62042card]
  have hLower : L n / 6 + L n / 20 + L n / 42 + L n / 110 <= (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 <= S6.card + S20.card + S42.card + S110.card := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card) hS110card
      _ = S.card := by symm; exact hScard
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42 + L n / 110) + (A n (z n)).card <= (K n).card := by
    have h1 : (L n / 6 + L n / 20 + L n / 42 + L n / 110) + (A n (z n)).card <=
        (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' : (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42 + L n / 110) <= (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K :
      (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42 + L n / 110) :=
      Nat.sub_le_sub_right (card_K_le n) (L n / 6 + L n / 20 + L n / 42 + L n / 110)

lemma card_A_le_L_add_one_sub_div_6_20_42_110_156_of_mods
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n) (hz11 : 11 <= z n)
    (hz13 : 13 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8)
    (hmod121 : n % 121 = 64) (hmod169 : n % 169 = 20) :
    (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S110 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]}
  let S156 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 11 [MOD 156]}
  let S620 : Finset Nat := S6 ∪ S20
  let S62042 : Finset Nat := S620 ∪ S42
  let Sprev : Finset Nat := S62042 ∪ S110
  let S : Finset Nat := Sprev ∪ S156
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hS110sub : S110 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod121_class_six_range_subset_K_sdiff_A hn0 hz11 hmod121 (by simpa [S110] using hk)
  have hS156sub : S156 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod169_class_eleven_range_subset_K_sdiff_A hn0 hz13 hmod169 (by simpa [S156] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hkPrev | hk156
    · rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
      · rcases Finset.mem_union.mp hk62042 with hk620 | hk42
        · rcases Finset.mem_union.mp hk620 with hk6 | hk20
          · exact hS6sub hk6
          · exact hS20sub hk20
        · exact hS42sub hk42
      · exact hS110sub hk110
    · exact hS156sub hk156
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hS110card : L n / 110 <= S110.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 110) (v := 6) (by decide : 0 < 110)
    simpa [S110] using hcard
  have hS156card : L n / 156 <= S156.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 156) (v := 11) (by decide : 0 < 156)
    simpa [S156] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hDisj6_110 : Disjoint S6 S110 := by
    simpa [S6, S110] using mod9_mod121_class_disjoint (L n)
  have hDisj20_110 : Disjoint S20 S110 := by
    simpa [S20, S110] using mod20_mod121_class_disjoint (L n)
  have hDisj42_110 : Disjoint S42 S110 := by
    simpa [S42, S110] using mod49_mod121_class_disjoint (L n)
  have hDisj620_110 : Disjoint S620 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk110
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_110) hk6 hk110
    · exact (Finset.disjoint_left.mp hDisj20_110) hk20 hk110
  have hDisj62042_110 : Disjoint S62042 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk110
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_110) hk620 hk110
    · exact (Finset.disjoint_left.mp hDisj42_110) hk42 hk110
  have hDisj6_156 : Disjoint S6 S156 := by
    simpa [S6, S156] using mod9_mod169_class_disjoint (L n)
  have hDisj20_156 : Disjoint S20 S156 := by
    simpa [S20, S156] using mod20_mod169_class_disjoint (L n)
  have hDisj42_156 : Disjoint S42 S156 := by
    simpa [S42, S156] using mod49_mod169_class_disjoint (L n)
  have hDisj110_156 : Disjoint S110 S156 := by
    simpa [S110, S156] using mod121_mod169_class_disjoint (L n)
  have hDisj620_156 : Disjoint S620 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk156
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_156) hk6 hk156
    · exact (Finset.disjoint_left.mp hDisj20_156) hk20 hk156
  have hDisj62042_156 : Disjoint S62042 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk156
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_156) hk620 hk156
    · exact (Finset.disjoint_left.mp hDisj42_156) hk42 hk156
  have hDisjPrev_156 : Disjoint Sprev S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk156
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_156) hk62042 hk156
    · exact (Finset.disjoint_left.mp hDisj110_156) hk110 hk156
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hS62042card : S62042.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S62042.card = S620.card + S42.card := by
        simpa [S62042, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hSprevcard : Sprev.card = S6.card + S20.card + S42.card + S110.card := by
    have hinter : S62042 ∩ S110 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj62042_110
    have hcard : (S62042 ∪ S110).card + (S62042 ∩ S110).card = S62042.card + S110.card :=
      Finset.card_union_add_card_inter S62042 S110
    calc
      Sprev.card = S62042.card + S110.card := by
        simpa [Sprev, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card := by rw [hS62042card]
  have hScard : S.card = S6.card + S20.card + S42.card + S110.card + S156.card := by
    have hinter : Sprev ∩ S156 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev_156
    have hcard : (Sprev ∪ S156).card + (Sprev ∩ S156).card = Sprev.card + S156.card :=
      Finset.card_union_add_card_inter Sprev S156
    calc
      S.card = Sprev.card + S156.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card := by rw [hSprevcard]
  have hLower :
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 <= (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 <=
          S6.card + S20.card + S42.card + S110.card + S156.card := by
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card) hS110card)
              hS156card
      _ = S.card := by symm; exact hScard
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) + (A n (z n)).card <=
        (K n).card := by
    have h1 :
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) + (A n (z n)).card <=
          (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' :
      (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) <=
        (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K :
      (A n (z n)).card <= (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) :=
      Nat.sub_le_sub_right (card_K_le n) (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156)

lemma card_A_le_L_add_one_sub_div_6_20_42_110_156_820_of_mods
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n)
    (hz11 : 11 <= z n) (hz13 : 13 <= z n) (hz41 : 41 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8)
    (hmod121 : n % 121 = 64) (hmod169 : n % 169 = 20) (hmod1681 : n % 1681 = 4) :
    (A n (z n)).card <=
      L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S110 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]}
  let S156 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 11 [MOD 156]}
  let S820 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 2 [MOD 820]}
  let S620 : Finset Nat := S6 ∪ S20
  let S62042 : Finset Nat := S620 ∪ S42
  let Sprev : Finset Nat := S62042 ∪ S110
  let Sprev156 : Finset Nat := Sprev ∪ S156
  let S : Finset Nat := Sprev156 ∪ S820
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hS110sub : S110 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod121_class_six_range_subset_K_sdiff_A hn0 hz11 hmod121 (by simpa [S110] using hk)
  have hS156sub : S156 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod169_class_eleven_range_subset_K_sdiff_A hn0 hz13 hmod169 (by simpa [S156] using hk)
  have hS820sub : S820 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod1681_class_two_range_subset_K_sdiff_A hn0 hz41 hmod1681 (by simpa [S820] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hkPrev156 | hk820
    · rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
      · rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
        · rcases Finset.mem_union.mp hk62042 with hk620 | hk42
          · rcases Finset.mem_union.mp hk620 with hk6 | hk20
            · exact hS6sub hk6
            · exact hS20sub hk20
          · exact hS42sub hk42
        · exact hS110sub hk110
      · exact hS156sub hk156
    · exact hS820sub hk820
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hS110card : L n / 110 <= S110.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 110) (v := 6) (by decide : 0 < 110)
    simpa [S110] using hcard
  have hS156card : L n / 156 <= S156.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 156) (v := 11) (by decide : 0 < 156)
    simpa [S156] using hcard
  have hS820card : L n / 820 <= S820.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 820) (v := 2) (by decide : 0 < 820)
    simpa [S820] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hDisj6_110 : Disjoint S6 S110 := by
    simpa [S6, S110] using mod9_mod121_class_disjoint (L n)
  have hDisj20_110 : Disjoint S20 S110 := by
    simpa [S20, S110] using mod20_mod121_class_disjoint (L n)
  have hDisj42_110 : Disjoint S42 S110 := by
    simpa [S42, S110] using mod49_mod121_class_disjoint (L n)
  have hDisj620_110 : Disjoint S620 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk110
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_110) hk6 hk110
    · exact (Finset.disjoint_left.mp hDisj20_110) hk20 hk110
  have hDisj62042_110 : Disjoint S62042 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk110
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_110) hk620 hk110
    · exact (Finset.disjoint_left.mp hDisj42_110) hk42 hk110
  have hDisj6_156 : Disjoint S6 S156 := by
    simpa [S6, S156] using mod9_mod169_class_disjoint (L n)
  have hDisj20_156 : Disjoint S20 S156 := by
    simpa [S20, S156] using mod20_mod169_class_disjoint (L n)
  have hDisj42_156 : Disjoint S42 S156 := by
    simpa [S42, S156] using mod49_mod169_class_disjoint (L n)
  have hDisj110_156 : Disjoint S110 S156 := by
    simpa [S110, S156] using mod121_mod169_class_disjoint (L n)
  have hDisj620_156 : Disjoint S620 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk156
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_156) hk6 hk156
    · exact (Finset.disjoint_left.mp hDisj20_156) hk20 hk156
  have hDisj62042_156 : Disjoint S62042 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk156
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_156) hk620 hk156
    · exact (Finset.disjoint_left.mp hDisj42_156) hk42 hk156
  have hDisjPrev_156 : Disjoint Sprev S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk156
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_156) hk62042 hk156
    · exact (Finset.disjoint_left.mp hDisj110_156) hk110 hk156
  have hDisj6_820 : Disjoint S6 S820 := by
    simpa [S6, S820] using mod9_mod1681_class_disjoint (L n)
  have hDisj20_820 : Disjoint S20 S820 := by
    simpa [S20, S820] using mod20_mod1681_class_disjoint (L n)
  have hDisj42_820 : Disjoint S42 S820 := by
    simpa [S42, S820] using mod49_mod1681_class_disjoint (L n)
  have hDisj110_820 : Disjoint S110 S820 := by
    simpa [S110, S820] using mod121_mod1681_class_disjoint (L n)
  have hDisj156_820 : Disjoint S156 S820 := by
    simpa [S156, S820] using mod169_mod1681_class_disjoint (L n)
  have hDisj620_820 : Disjoint S620 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk820
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_820) hk6 hk820
    · exact (Finset.disjoint_left.mp hDisj20_820) hk20 hk820
  have hDisj62042_820 : Disjoint S62042 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk820
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_820) hk620 hk820
    · exact (Finset.disjoint_left.mp hDisj42_820) hk42 hk820
  have hDisjPrev_820 : Disjoint Sprev S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk820
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_820) hk62042 hk820
    · exact (Finset.disjoint_left.mp hDisj110_820) hk110 hk820
  have hDisjPrev156_820 : Disjoint Sprev156 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev156 hk820
    rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
    · exact (Finset.disjoint_left.mp hDisjPrev_820) hkPrev hk820
    · exact (Finset.disjoint_left.mp hDisj156_820) hk156 hk820
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hS62042card : S62042.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S62042.card = S620.card + S42.card := by
        simpa [S62042, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hSprevcard : Sprev.card = S6.card + S20.card + S42.card + S110.card := by
    have hinter : S62042 ∩ S110 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj62042_110
    have hcard : (S62042 ∪ S110).card + (S62042 ∩ S110).card = S62042.card + S110.card :=
      Finset.card_union_add_card_inter S62042 S110
    calc
      Sprev.card = S62042.card + S110.card := by
        simpa [Sprev, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card := by rw [hS62042card]
  have hSprev156card : Sprev156.card = S6.card + S20.card + S42.card + S110.card + S156.card := by
    have hinter : Sprev ∩ S156 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev_156
    have hcard : (Sprev ∪ S156).card + (Sprev ∩ S156).card = Sprev.card + S156.card :=
      Finset.card_union_add_card_inter Sprev S156
    calc
      Sprev156.card = Sprev.card + S156.card := by
        simpa [Sprev156, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card := by rw [hSprevcard]
  have hScard :
      S.card = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
    have hinter : Sprev156 ∩ S820 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev156_820
    have hcard : (Sprev156 ∪ S820).card + (Sprev156 ∩ S820).card = Sprev156.card + S820.card :=
      Finset.card_union_add_card_inter Sprev156 S820
    calc
      S.card = Sprev156.card + S820.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
        rw [hSprev156card]
  have hLower :
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 <=
        (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 <=
          S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
            exact Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card) hS110card)
                hS156card)
              hS820card
      _ = S.card := by symm; exact hScard
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) + (A n (z n)).card <=
        (K n).card := by
    have h1 :
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) + (A n (z n)).card <=
          (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' :
      (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) <=
        (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K :
      (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) :=
      Nat.sub_le_sub_right (card_K_le n)
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820)

lemma card_A_le_L_add_one_sub_div_6_20_42_110_156_820_1332_of_mods
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n)
    (hz11 : 11 <= z n) (hz13 : 13 <= z n) (hz41 : 41 <= z n) (hz37 : 37 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8)
    (hmod121 : n % 121 = 64) (hmod169 : n % 169 = 20) (hmod1681 : n % 1681 = 4)
    (hmod1369 : n % 1369 = 32) :
    (A n (z n)).card <=
      L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S110 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]}
  let S156 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 11 [MOD 156]}
  let S820 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 2 [MOD 820]}
  let S1332 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 5 [MOD 1332]}
  let S620 : Finset Nat := S6 ∪ S20
  let S62042 : Finset Nat := S620 ∪ S42
  let Sprev : Finset Nat := S62042 ∪ S110
  let Sprev156 : Finset Nat := Sprev ∪ S156
  let Sprev820 : Finset Nat := Sprev156 ∪ S820
  let S : Finset Nat := Sprev820 ∪ S1332
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hS110sub : S110 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod121_class_six_range_subset_K_sdiff_A hn0 hz11 hmod121 (by simpa [S110] using hk)
  have hS156sub : S156 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod169_class_eleven_range_subset_K_sdiff_A hn0 hz13 hmod169 (by simpa [S156] using hk)
  have hS820sub : S820 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod1681_class_two_range_subset_K_sdiff_A hn0 hz41 hmod1681 (by simpa [S820] using hk)
  have hS1332sub : S1332 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod1369_class_five_range_subset_K_sdiff_A hn0 hz37 hmod1369 (by simpa [S1332] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hkPrev820 | hk1332
    · rcases Finset.mem_union.mp hkPrev820 with hkPrev156 | hk820
      · rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
        · rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
          · rcases Finset.mem_union.mp hk62042 with hk620 | hk42
            · rcases Finset.mem_union.mp hk620 with hk6 | hk20
              · exact hS6sub hk6
              · exact hS20sub hk20
            · exact hS42sub hk42
          · exact hS110sub hk110
        · exact hS156sub hk156
      · exact hS820sub hk820
    · exact hS1332sub hk1332
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hS110card : L n / 110 <= S110.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 110) (v := 6) (by decide : 0 < 110)
    simpa [S110] using hcard
  have hS156card : L n / 156 <= S156.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 156) (v := 11) (by decide : 0 < 156)
    simpa [S156] using hcard
  have hS820card : L n / 820 <= S820.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 820) (v := 2) (by decide : 0 < 820)
    simpa [S820] using hcard
  have hS1332card : L n / 1332 <= S1332.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 1332) (v := 5) (by decide : 0 < 1332)
    simpa [S1332] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hDisj6_110 : Disjoint S6 S110 := by
    simpa [S6, S110] using mod9_mod121_class_disjoint (L n)
  have hDisj20_110 : Disjoint S20 S110 := by
    simpa [S20, S110] using mod20_mod121_class_disjoint (L n)
  have hDisj42_110 : Disjoint S42 S110 := by
    simpa [S42, S110] using mod49_mod121_class_disjoint (L n)
  have hDisj620_110 : Disjoint S620 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk110
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_110) hk6 hk110
    · exact (Finset.disjoint_left.mp hDisj20_110) hk20 hk110
  have hDisj62042_110 : Disjoint S62042 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk110
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_110) hk620 hk110
    · exact (Finset.disjoint_left.mp hDisj42_110) hk42 hk110
  have hDisj6_156 : Disjoint S6 S156 := by
    simpa [S6, S156] using mod9_mod169_class_disjoint (L n)
  have hDisj20_156 : Disjoint S20 S156 := by
    simpa [S20, S156] using mod20_mod169_class_disjoint (L n)
  have hDisj42_156 : Disjoint S42 S156 := by
    simpa [S42, S156] using mod49_mod169_class_disjoint (L n)
  have hDisj110_156 : Disjoint S110 S156 := by
    simpa [S110, S156] using mod121_mod169_class_disjoint (L n)
  have hDisj620_156 : Disjoint S620 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk156
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_156) hk6 hk156
    · exact (Finset.disjoint_left.mp hDisj20_156) hk20 hk156
  have hDisj62042_156 : Disjoint S62042 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk156
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_156) hk620 hk156
    · exact (Finset.disjoint_left.mp hDisj42_156) hk42 hk156
  have hDisjPrev_156 : Disjoint Sprev S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk156
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_156) hk62042 hk156
    · exact (Finset.disjoint_left.mp hDisj110_156) hk110 hk156
  have hDisj6_820 : Disjoint S6 S820 := by
    simpa [S6, S820] using mod9_mod1681_class_disjoint (L n)
  have hDisj20_820 : Disjoint S20 S820 := by
    simpa [S20, S820] using mod20_mod1681_class_disjoint (L n)
  have hDisj42_820 : Disjoint S42 S820 := by
    simpa [S42, S820] using mod49_mod1681_class_disjoint (L n)
  have hDisj110_820 : Disjoint S110 S820 := by
    simpa [S110, S820] using mod121_mod1681_class_disjoint (L n)
  have hDisj156_820 : Disjoint S156 S820 := by
    simpa [S156, S820] using mod169_mod1681_class_disjoint (L n)
  have hDisj620_820 : Disjoint S620 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk820
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_820) hk6 hk820
    · exact (Finset.disjoint_left.mp hDisj20_820) hk20 hk820
  have hDisj62042_820 : Disjoint S62042 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk820
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_820) hk620 hk820
    · exact (Finset.disjoint_left.mp hDisj42_820) hk42 hk820
  have hDisjPrev_820 : Disjoint Sprev S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk820
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_820) hk62042 hk820
    · exact (Finset.disjoint_left.mp hDisj110_820) hk110 hk820
  have hDisjPrev156_820 : Disjoint Sprev156 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev156 hk820
    rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
    · exact (Finset.disjoint_left.mp hDisjPrev_820) hkPrev hk820
    · exact (Finset.disjoint_left.mp hDisj156_820) hk156 hk820
  have hDisj6_1332 : Disjoint S6 S1332 := by
    simpa [S6, S1332] using mod9_mod1369_class_disjoint (L n)
  have hDisj20_1332 : Disjoint S20 S1332 := by
    simpa [S20, S1332] using mod20_mod1369_class_disjoint (L n)
  have hDisj42_1332 : Disjoint S42 S1332 := by
    simpa [S42, S1332] using mod49_mod1369_class_disjoint (L n)
  have hDisj110_1332 : Disjoint S110 S1332 := by
    simpa [S110, S1332] using mod121_mod1369_class_disjoint (L n)
  have hDisj156_1332 : Disjoint S156 S1332 := by
    simpa [S156, S1332] using mod169_mod1369_class_disjoint (L n)
  have hDisj820_1332 : Disjoint S820 S1332 := by
    simpa [S820, S1332] using mod1681_mod1369_class_disjoint (L n)
  have hDisj620_1332 : Disjoint S620 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk1332
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_1332) hk6 hk1332
    · exact (Finset.disjoint_left.mp hDisj20_1332) hk20 hk1332
  have hDisj62042_1332 : Disjoint S62042 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk1332
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_1332) hk620 hk1332
    · exact (Finset.disjoint_left.mp hDisj42_1332) hk42 hk1332
  have hDisjPrev_1332 : Disjoint Sprev S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk1332
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_1332) hk62042 hk1332
    · exact (Finset.disjoint_left.mp hDisj110_1332) hk110 hk1332
  have hDisjPrev156_1332 : Disjoint Sprev156 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev156 hk1332
    rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
    · exact (Finset.disjoint_left.mp hDisjPrev_1332) hkPrev hk1332
    · exact (Finset.disjoint_left.mp hDisj156_1332) hk156 hk1332
  have hDisjPrev820_1332 : Disjoint Sprev820 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev820 hk1332
    rcases Finset.mem_union.mp hkPrev820 with hkPrev156 | hk820
    · exact (Finset.disjoint_left.mp hDisjPrev156_1332) hkPrev156 hk1332
    · exact (Finset.disjoint_left.mp hDisj820_1332) hk820 hk1332
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hS62042card : S62042.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S62042.card = S620.card + S42.card := by
        simpa [S62042, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hSprevcard : Sprev.card = S6.card + S20.card + S42.card + S110.card := by
    have hinter : S62042 ∩ S110 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj62042_110
    have hcard : (S62042 ∪ S110).card + (S62042 ∩ S110).card = S62042.card + S110.card :=
      Finset.card_union_add_card_inter S62042 S110
    calc
      Sprev.card = S62042.card + S110.card := by
        simpa [Sprev, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card := by rw [hS62042card]
  have hSprev156card : Sprev156.card = S6.card + S20.card + S42.card + S110.card + S156.card := by
    have hinter : Sprev ∩ S156 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev_156
    have hcard : (Sprev ∪ S156).card + (Sprev ∩ S156).card = Sprev.card + S156.card :=
      Finset.card_union_add_card_inter Sprev S156
    calc
      Sprev156.card = Sprev.card + S156.card := by
        simpa [Sprev156, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card := by rw [hSprevcard]
  have hSprev820card : Sprev820.card = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
    have hinter : Sprev156 ∩ S820 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev156_820
    have hcard : (Sprev156 ∪ S820).card + (Sprev156 ∩ S820).card = Sprev156.card + S820.card :=
      Finset.card_union_add_card_inter Sprev156 S820
    calc
      Sprev820.card = Sprev156.card + S820.card := by
        simpa [Sprev820, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
        rw [hSprev156card]
  have hScard :
      S.card = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
    have hinter : Sprev820 ∩ S1332 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev820_1332
    have hcard : (Sprev820 ∪ S1332).card + (Sprev820 ∩ S1332).card = Sprev820.card + S1332.card :=
      Finset.card_union_add_card_inter Sprev820 S1332
    calc
      S.card = Sprev820.card + S1332.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
        rw [hSprev820card]
  have hLower :
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 <=
        (K n \ A n (z n)).card := by
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 <=
          S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
            exact Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card) hS110card)
                  hS156card)
                hS820card)
              hS1332card
      _ = S.card := by symm; exact hScard
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) + (A n (z n)).card <=
        (K n).card := by
    have h1 :
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) + (A n (z n)).card <=
          (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' :
      (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) <=
        (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K :
      (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) :=
      Nat.sub_le_sub_right (card_K_le n)
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332)

lemma card_A_le_L_add_one_sub_div_6_20_42_110_156_820_1332_3660_of_mods
    {n : Nat}
    (hn0 : n ≠ 0) (hz3 : 3 <= z n) (hz5 : 5 <= z n) (hz7 : 7 <= z n)
    (hz11 : 11 <= z n) (hz13 : 13 <= z n) (hz41 : 41 <= z n) (hz37 : 37 <= z n)
    (hz61 : 61 <= z n)
    (hmod9 : n % 9 = 2) (hmod25 : n % 25 = 1) (hmod49 : n % 49 = 8)
    (hmod121 : n % 121 = 64) (hmod169 : n % 169 = 20) (hmod1681 : n % 1681 = 4)
    (hmod1369 : n % 1369 = 32) (hmod3721 : n % 3721 = 16) :
    (A n (z n)).card <=
      L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) := by
  classical
  let S6 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 1 [MOD 6]}
  let S20 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 0 [MOD 20]}
  let S42 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 3 [MOD 42]}
  let S110 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 6 [MOD 110]}
  let S156 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 11 [MOD 156]}
  let S820 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 2 [MOD 820]}
  let S1332 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 5 [MOD 1332]}
  let S3660 : Finset Nat := {k ∈ Finset.range (L n) | k ≡ 4 [MOD 3660]}
  let S620 : Finset Nat := S6 ∪ S20
  let S62042 : Finset Nat := S620 ∪ S42
  let Sprev : Finset Nat := S62042 ∪ S110
  let Sprev156 : Finset Nat := Sprev ∪ S156
  let Sprev820 : Finset Nat := Sprev156 ∪ S820
  let S : Finset Nat := Sprev820 ∪ S1332
  have hS6sub : S6 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod9_class_one_range_subset_K_sdiff_A hn0 hz3 hmod9 (by simpa [S6] using hk)
  have hS20sub : S20 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod25_class_zero_range_subset_K_sdiff_A hn0 hz5 hmod25 (by simpa [S20] using hk)
  have hS42sub : S42 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod49_class_three_range_subset_K_sdiff_A hn0 hz7 hmod49 (by simpa [S42] using hk)
  have hS110sub : S110 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod121_class_six_range_subset_K_sdiff_A hn0 hz11 hmod121 (by simpa [S110] using hk)
  have hS156sub : S156 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod169_class_eleven_range_subset_K_sdiff_A hn0 hz13 hmod169 (by simpa [S156] using hk)
  have hS820sub : S820 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod1681_class_two_range_subset_K_sdiff_A hn0 hz41 hmod1681 (by simpa [S820] using hk)
  have hS1332sub : S1332 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod1369_class_five_range_subset_K_sdiff_A hn0 hz37 hmod1369 (by simpa [S1332] using hk)
  have hSsub : S ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hkPrev820 | hk1332
    · rcases Finset.mem_union.mp hkPrev820 with hkPrev156 | hk820
      · rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
        · rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
          · rcases Finset.mem_union.mp hk62042 with hk620 | hk42
            · rcases Finset.mem_union.mp hk620 with hk6 | hk20
              · exact hS6sub hk6
              · exact hS20sub hk20
            · exact hS42sub hk42
          · exact hS110sub hk110
        · exact hS156sub hk156
      · exact hS820sub hk820
    · exact hS1332sub hk1332
  have hS6card : L n / 6 <= S6.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 6) (v := 1) (by decide : 0 < 6)
    simpa [S6] using hcard
  have hS20card : L n / 20 <= S20.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 20) (v := 0) (by decide : 0 < 20)
    simpa [S20] using hcard
  have hS42card : L n / 42 <= S42.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 42) (v := 3) (by decide : 0 < 42)
    simpa [S42] using hcard
  have hS110card : L n / 110 <= S110.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 110) (v := 6) (by decide : 0 < 110)
    simpa [S110] using hcard
  have hS156card : L n / 156 <= S156.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 156) (v := 11) (by decide : 0 < 156)
    simpa [S156] using hcard
  have hS820card : L n / 820 <= S820.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 820) (v := 2) (by decide : 0 < 820)
    simpa [S820] using hcard
  have hS1332card : L n / 1332 <= S1332.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 1332) (v := 5) (by decide : 0 < 1332)
    simpa [S1332] using hcard
  have hDisj620 : Disjoint S6 S20 := by
    simpa [S6, S20] using mod9_mod25_class_disjoint (L n)
  have hDisj642 : Disjoint S6 S42 := by
    simpa [S6, S42] using mod9_mod49_class_disjoint (L n)
  have hDisj2042 : Disjoint S20 S42 := by
    simpa [S20, S42] using mod20_mod49_class_disjoint (L n)
  have hDisj620_42 : Disjoint S620 S42 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk42
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj642) hk6 hk42
    · exact (Finset.disjoint_left.mp hDisj2042) hk20 hk42
  have hDisj6_110 : Disjoint S6 S110 := by
    simpa [S6, S110] using mod9_mod121_class_disjoint (L n)
  have hDisj20_110 : Disjoint S20 S110 := by
    simpa [S20, S110] using mod20_mod121_class_disjoint (L n)
  have hDisj42_110 : Disjoint S42 S110 := by
    simpa [S42, S110] using mod49_mod121_class_disjoint (L n)
  have hDisj620_110 : Disjoint S620 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk110
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_110) hk6 hk110
    · exact (Finset.disjoint_left.mp hDisj20_110) hk20 hk110
  have hDisj62042_110 : Disjoint S62042 S110 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk110
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_110) hk620 hk110
    · exact (Finset.disjoint_left.mp hDisj42_110) hk42 hk110
  have hDisj6_156 : Disjoint S6 S156 := by
    simpa [S6, S156] using mod9_mod169_class_disjoint (L n)
  have hDisj20_156 : Disjoint S20 S156 := by
    simpa [S20, S156] using mod20_mod169_class_disjoint (L n)
  have hDisj42_156 : Disjoint S42 S156 := by
    simpa [S42, S156] using mod49_mod169_class_disjoint (L n)
  have hDisj110_156 : Disjoint S110 S156 := by
    simpa [S110, S156] using mod121_mod169_class_disjoint (L n)
  have hDisj620_156 : Disjoint S620 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk156
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_156) hk6 hk156
    · exact (Finset.disjoint_left.mp hDisj20_156) hk20 hk156
  have hDisj62042_156 : Disjoint S62042 S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk156
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_156) hk620 hk156
    · exact (Finset.disjoint_left.mp hDisj42_156) hk42 hk156
  have hDisjPrev_156 : Disjoint Sprev S156 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk156
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_156) hk62042 hk156
    · exact (Finset.disjoint_left.mp hDisj110_156) hk110 hk156
  have hDisj6_820 : Disjoint S6 S820 := by
    simpa [S6, S820] using mod9_mod1681_class_disjoint (L n)
  have hDisj20_820 : Disjoint S20 S820 := by
    simpa [S20, S820] using mod20_mod1681_class_disjoint (L n)
  have hDisj42_820 : Disjoint S42 S820 := by
    simpa [S42, S820] using mod49_mod1681_class_disjoint (L n)
  have hDisj110_820 : Disjoint S110 S820 := by
    simpa [S110, S820] using mod121_mod1681_class_disjoint (L n)
  have hDisj156_820 : Disjoint S156 S820 := by
    simpa [S156, S820] using mod169_mod1681_class_disjoint (L n)
  have hDisj620_820 : Disjoint S620 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk820
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_820) hk6 hk820
    · exact (Finset.disjoint_left.mp hDisj20_820) hk20 hk820
  have hDisj62042_820 : Disjoint S62042 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk820
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_820) hk620 hk820
    · exact (Finset.disjoint_left.mp hDisj42_820) hk42 hk820
  have hDisjPrev_820 : Disjoint Sprev S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk820
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_820) hk62042 hk820
    · exact (Finset.disjoint_left.mp hDisj110_820) hk110 hk820
  have hDisjPrev156_820 : Disjoint Sprev156 S820 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev156 hk820
    rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
    · exact (Finset.disjoint_left.mp hDisjPrev_820) hkPrev hk820
    · exact (Finset.disjoint_left.mp hDisj156_820) hk156 hk820
  have hDisj6_1332 : Disjoint S6 S1332 := by
    simpa [S6, S1332] using mod9_mod1369_class_disjoint (L n)
  have hDisj20_1332 : Disjoint S20 S1332 := by
    simpa [S20, S1332] using mod20_mod1369_class_disjoint (L n)
  have hDisj42_1332 : Disjoint S42 S1332 := by
    simpa [S42, S1332] using mod49_mod1369_class_disjoint (L n)
  have hDisj110_1332 : Disjoint S110 S1332 := by
    simpa [S110, S1332] using mod121_mod1369_class_disjoint (L n)
  have hDisj156_1332 : Disjoint S156 S1332 := by
    simpa [S156, S1332] using mod169_mod1369_class_disjoint (L n)
  have hDisj820_1332 : Disjoint S820 S1332 := by
    simpa [S820, S1332] using mod1681_mod1369_class_disjoint (L n)
  have hDisj620_1332 : Disjoint S620 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk620 hk1332
    rcases Finset.mem_union.mp hk620 with hk6 | hk20
    · exact (Finset.disjoint_left.mp hDisj6_1332) hk6 hk1332
    · exact (Finset.disjoint_left.mp hDisj20_1332) hk20 hk1332
  have hDisj62042_1332 : Disjoint S62042 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hk62042 hk1332
    rcases Finset.mem_union.mp hk62042 with hk620 | hk42
    · exact (Finset.disjoint_left.mp hDisj620_1332) hk620 hk1332
    · exact (Finset.disjoint_left.mp hDisj42_1332) hk42 hk1332
  have hDisjPrev_1332 : Disjoint Sprev S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev hk1332
    rcases Finset.mem_union.mp hkPrev with hk62042 | hk110
    · exact (Finset.disjoint_left.mp hDisj62042_1332) hk62042 hk1332
    · exact (Finset.disjoint_left.mp hDisj110_1332) hk110 hk1332
  have hDisjPrev156_1332 : Disjoint Sprev156 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev156 hk1332
    rcases Finset.mem_union.mp hkPrev156 with hkPrev | hk156
    · exact (Finset.disjoint_left.mp hDisjPrev_1332) hkPrev hk1332
    · exact (Finset.disjoint_left.mp hDisj156_1332) hk156 hk1332
  have hDisjPrev820_1332 : Disjoint Sprev820 S1332 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkPrev820 hk1332
    rcases Finset.mem_union.mp hkPrev820 with hkPrev156 | hk820
    · exact (Finset.disjoint_left.mp hDisjPrev156_1332) hkPrev156 hk1332
    · exact (Finset.disjoint_left.mp hDisj820_1332) hk820 hk1332
  have hS620card : S620.card = S6.card + S20.card := by
    have hinter : S6 ∩ S20 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620
    have hcard : (S6 ∪ S20).card + (S6 ∩ S20).card = S6.card + S20.card :=
      Finset.card_union_add_card_inter S6 S20
    simpa [S620, hinter] using hcard
  have hS62042card : S62042.card = S6.card + S20.card + S42.card := by
    have hinter : S620 ∩ S42 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj620_42
    have hcard : (S620 ∪ S42).card + (S620 ∩ S42).card = S620.card + S42.card :=
      Finset.card_union_add_card_inter S620 S42
    calc
      S62042.card = S620.card + S42.card := by
        simpa [S62042, hinter] using hcard
      _ = S6.card + S20.card + S42.card := by rw [hS620card]
  have hSprevcard : Sprev.card = S6.card + S20.card + S42.card + S110.card := by
    have hinter : S62042 ∩ S110 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisj62042_110
    have hcard : (S62042 ∪ S110).card + (S62042 ∩ S110).card = S62042.card + S110.card :=
      Finset.card_union_add_card_inter S62042 S110
    calc
      Sprev.card = S62042.card + S110.card := by
        simpa [Sprev, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card := by rw [hS62042card]
  have hSprev156card : Sprev156.card = S6.card + S20.card + S42.card + S110.card + S156.card := by
    have hinter : Sprev ∩ S156 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev_156
    have hcard : (Sprev ∪ S156).card + (Sprev ∩ S156).card = Sprev.card + S156.card :=
      Finset.card_union_add_card_inter Sprev S156
    calc
      Sprev156.card = Sprev.card + S156.card := by
        simpa [Sprev156, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card := by rw [hSprevcard]
  have hSprev820card : Sprev820.card = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
    have hinter : Sprev156 ∩ S820 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev156_820
    have hcard : (Sprev156 ∪ S820).card + (Sprev156 ∩ S820).card = Sprev156.card + S820.card :=
      Finset.card_union_add_card_inter Sprev156 S820
    calc
      Sprev820.card = Sprev156.card + S820.card := by
        simpa [Sprev820, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card := by
        rw [hSprev156card]
  have hScard :
      S.card = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
    have hinter : Sprev820 ∩ S1332 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjPrev820_1332
    have hcard : (Sprev820 ∪ S1332).card + (Sprev820 ∩ S1332).card = Sprev820.card + S1332.card :=
      Finset.card_union_add_card_inter Sprev820 S1332
    calc
      S.card = Sprev820.card + S1332.card := by
        simpa [S, hinter] using hcard
      _ = S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
        rw [hSprev820card]

  have hS3660sub : S3660 ⊆ K n \ A n (z n) := by
    intro k hk
    exact mod3721_class_four_range_subset_K_sdiff_A hn0 hz61 hmod3721 (by simpa [S3660] using hk)
  have hS3660card : L n / 3660 <= S3660.card := by
    have hcard := card_range_modEq_ge_div (b := L n) (r := 3660) (v := 4) (by decide : 0 < 3660)
    simpa [S3660] using hcard
  have hDisj6_3660 : Disjoint S6 S3660 := by
    simpa [S6, S3660] using mod9_mod3721_class_disjoint (L n)
  have hDisj20_3660 : Disjoint S20 S3660 := by
    simpa [S20, S3660] using mod20_mod3721_class_disjoint (L n)
  have hDisj42_3660 : Disjoint S42 S3660 := by
    simpa [S42, S3660] using mod49_mod3721_class_disjoint (L n)
  have hDisj110_3660 : Disjoint S110 S3660 := by
    simpa [S110, S3660] using mod121_mod3721_class_disjoint (L n)
  have hDisj156_3660 : Disjoint S156 S3660 := by
    simpa [S156, S3660] using mod169_mod3721_class_disjoint (L n)
  have hDisj820_3660 : Disjoint S820 S3660 := by
    simpa [S820, S3660] using mod1681_mod3721_class_disjoint (L n)
  have hDisj1332_3660 : Disjoint S1332 S3660 := by
    simpa [S1332, S3660] using mod1369_mod3721_class_disjoint (L n)
  have hDisjS_3660 : Disjoint S S3660 := by
    refine Finset.disjoint_left.mpr ?_
    intro k hkS hk3660
    cases Finset.mem_union.mp hkS with
    | inl hkPrev820 =>
        cases Finset.mem_union.mp hkPrev820 with
        | inl hkPrev156 =>
            cases Finset.mem_union.mp hkPrev156 with
            | inl hkPrev =>
                cases Finset.mem_union.mp hkPrev with
                | inl hk62042 =>
                    cases Finset.mem_union.mp hk62042 with
                    | inl hk620 =>
                        cases Finset.mem_union.mp hk620 with
                        | inl hk6 => exact (Finset.disjoint_left.mp hDisj6_3660) hk6 hk3660
                        | inr hk20 => exact (Finset.disjoint_left.mp hDisj20_3660) hk20 hk3660
                    | inr hk42 => exact (Finset.disjoint_left.mp hDisj42_3660) hk42 hk3660
                | inr hk110 => exact (Finset.disjoint_left.mp hDisj110_3660) hk110 hk3660
            | inr hk156 => exact (Finset.disjoint_left.mp hDisj156_3660) hk156 hk3660
        | inr hk820 => exact (Finset.disjoint_left.mp hDisj820_3660) hk820 hk3660
    | inr hk1332 => exact (Finset.disjoint_left.mp hDisj1332_3660) hk1332 hk3660
  let Sall : Finset Nat := S ∪ S3660
  have hSallsub : Sall ⊆ K n \ A n (z n) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hkS | hk3660
    · exact hSsub hkS
    · exact hS3660sub hk3660
  have hSallcard : Sall.card = S.card + S3660.card := by
    have hinter : S ∩ S3660 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hDisjS_3660
    have hcard : (S ∪ S3660).card + (S ∩ S3660).card = S.card + S3660.card :=
      Finset.card_union_add_card_inter S S3660
    simpa [Sall, hinter] using hcard
  have hLower7 :
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 <= S.card := by
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 <=
          S6.card + S20.card + S42.card + S110.card + S156.card + S820.card + S1332.card := by
            exact Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS6card hS20card) hS42card) hS110card)
                  hS156card)
                hS820card)
              hS1332card
      _ = S.card := by simpa [hScard]
  have hLower :
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660 <=
        (K n \ A n (z n)).card := by
    have hLowerSall :
        L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660 <=
          S.card + S3660.card :=
      Nat.add_le_add hLower7 hS3660card
    calc
      L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660 <=
          S.card + S3660.card := hLowerSall
      _ = Sall.card := by rw [hSallcard]
      _ <= (K n \ A n (z n)).card := Finset.card_le_card hSallsub
  have hAdd :
      (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) + (A n (z n)).card <=
        (K n).card := by
    have h1 :
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) + (A n (z n)).card <=
          (K n \ A n (z n)).card + (A n (z n)).card := Nat.add_le_add_right hLower _
    have h2 : (K n \ A n (z n)).card + (A n (z n)).card = (K n).card :=
      Finset.card_sdiff_add_card_eq_card (A_subset_K n (z n))
    exact le_trans h1 (by simp [h2])
  have hAdd' :
      (A n (z n)).card + (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) <=
        (K n).card := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAdd
  have hA_le_K :
      (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) :=
    Nat.le_sub_of_add_le hAdd'
  calc
    (A n (z n)).card <=
        (K n).card - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) := hA_le_K
    _ <= (L n + 1) - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) :=
      Nat.sub_le_sub_right (card_K_le n)
        (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660)

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

lemma S1_small_prime_decomp_localOrder (n : Nat) :
    (smallPrimeBad n (z n)).card <=
      Finset.sum (smallPrimeSupport n) (fun p => localOrderBound n p) := by
  calc
    (smallPrimeBad n (z n)).card <= Finset.sum (smallPrimeSupport n) (fun p => Np n p) :=
      S1_small_prime_decomp n
    _ <= Finset.sum (smallPrimeSupport n) (fun p => localOrderBound n p) := by
      exact Finset.sum_le_sum (by
        intro p hp
        exact Np_le_localOrderBound_of_smallPrimeSupport n p hp)

lemma S1_small_prime_decomp_localOrder_coarse (n : Nat) :
    (smallPrimeBad n (z n)).card <= (smallPrimeSupport n).card * (L n + 1) := by
  exact le_trans (S1_small_prime_decomp_localOrder n) (sum_localOrderBound_small_le n)

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

/--
Sharper large-prime decomposition:
only primes with `p^2 <= n` can contribute to `B`.
-/
lemma G1_large_prime_decomp_sq (n : Nat) :
  (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
  classical
  let badAt : Nat -> Finset Nat := fun p => (K n).filter (fun k => (M n k) % (p ^ 2) = 0)
  have hsubset :
      B n (z n) ⊆ (largePrimeSupportSq n).biUnion badAt := by
    intro k hkB
    have hkK : k ∈ K n := (Finset.mem_filter.mp hkB).1
    rcases (Finset.mem_filter.mp hkB).2 with ⟨p, hp, hpgt, hmod0⟩
    have hklt : 2 ^ k < n := C1 hkK
    have hmPos : 0 < M n k := by
      unfold M
      exact Nat.sub_pos_of_lt hklt
    have hp2dvd : p ^ 2 ∣ M n k := (Nat.dvd_iff_mod_eq_zero).2 hmod0
    have hp2_le_m : p ^ 2 <= M n k := Nat.le_of_dvd hmPos hp2dvd
    have hp2_le_n : p ^ 2 <= n := le_trans hp2_le_m (Nat.sub_le n (2 ^ k))
    have hp_le_sq : p <= p ^ 2 := by
      calc
        p = p * 1 := by simp
        _ <= p * p := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hp.pos)
        _ = p ^ 2 := by simp [pow_two]
    have hp_le_n : p <= n := le_trans hp_le_sq hp2_le_n
    have hpIcc : p ∈ Finset.Icc (z n + 1) n := Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt hpgt, hp_le_n⟩
    have hpLarge : p ∈ largePrimeSupport n := by
      unfold largePrimeSupport
      exact Finset.mem_filter.mpr ⟨hpIcc, hp⟩
    have hpSq : p ∈ largePrimeSupportSq n := by
      unfold largePrimeSupportSq
      exact Finset.mem_filter.mpr ⟨hpLarge, hp2_le_n⟩
    have hkBadAt : k ∈ badAt p := Finset.mem_filter.mpr ⟨hkK, hmod0⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpSq, hkBadAt⟩
  calc
    (B n (z n)).card <= ((largePrimeSupportSq n).biUnion badAt).card := Finset.card_le_card hsubset
    _ <= Finset.sum (largePrimeSupportSq n) (fun p => (badAt p).card) := Finset.card_biUnion_le
    _ = Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      simp [Np, badAt]

lemma G1_large_prime_decomp_localOrder (n : Nat) :
    (B n (z n)).card <= Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) := by
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupport n) (fun p => Np n p) :=
      G1_large_prime_decomp n
    _ <= Finset.sum (largePrimeSupport n) (fun p => localOrderBound n p) := by
      exact Finset.sum_le_sum (by
        intro p hp
        exact Np_le_localOrderBound_of_largePrimeSupport n p hp)

lemma G1_large_prime_decomp_localOrder_coarse (n : Nat) :
    (B n (z n)).card <= (largePrimeSupport n).card * (L n + 1) := by
  exact le_trans (G1_large_prime_decomp_localOrder n) (sum_localOrderBound_large_le n)

lemma G1_large_prime_decomp_localOrder_half (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <= (largePrimeSupport n).card * ((L n + 1) / 2 + 1) := by
  exact le_trans (G1_large_prime_decomp_localOrder n)
    (sum_localOrderBound_large_le_half_add_one n hz2)

lemma G1_large_prime_decomp_sq_localOrder (n : Nat) :
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) := by
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) :=
      G1_large_prime_decomp_sq n
    _ <= Finset.sum (largePrimeSupportSq n) (fun p => localOrderBound n p) := by
      exact Finset.sum_le_sum (by
        intro p hp
        exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hp).1))

lemma G1_large_prime_decomp_sq_active (n : Nat) :
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) :=
      G1_large_prime_decomp_sq n
    _ = Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      symm
      exact sum_Np_largePrimeSupportSq_eq_sum_largePrimeActiveSupportSq n

lemma G1_large_prime_decomp_sq_active_localOrder (n : Nat) :
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) :=
      G1_large_prime_decomp_sq_active n
    _ <= Finset.sum (largePrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
      exact Finset.sum_le_sum (by
        intro p hp
        have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hp
        exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))

lemma G1_large_prime_decomp_sq_localOrder_coarse (n : Nat) :
    (B n (z n)).card <= (largePrimeSupportSq n).card * (L n + 1) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n) (sum_localOrderBound_largeSq_le n)

lemma G1_large_prime_decomp_sq_localOrder_half (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <= (largePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n)
    (sum_localOrderBound_largeSq_le_half_add_one n hz2)

lemma G1_large_prime_decomp_sq_localOrder_wieferich_split (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
        Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n)
    (sum_localOrderBound_largeSq_le_wieferich_split n hz2)

lemma G1_large_prime_decomp_sq_localOrder_wieferich_three_split (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
        (nonWieferichLargePrimeSupportSq n).card * 3 := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n)
    (sum_localOrderBound_largeSq_le_wieferich_three_split n hz2)

lemma G1_large_prime_decomp_sq_localOrder_supportSq_three_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (largePrimeSupportSq n).card * 3 +
        (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n)
    (sum_localOrderBound_largeSq_le_supportSq_three_add_wieferich_excess n hz2)

lemma G1_large_prime_decomp_sq_active_localOrder_supportSq_three_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (largePrimeActiveSupportSq n).card * 3 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) := by
  exact le_trans (G1_large_prime_decomp_sq_active_localOrder n)
    (sum_localOrderBound_largePrimeActiveSq_le_supportSq_three_add_wieferich_excess n hz2)

lemma G1_large_prime_decomp_sq_active_localOrder_supportSq_two_add_wieferich_excess_plus_one
    (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (largePrimeActiveSupportSq n).card * 2 + 1 +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
  exact le_trans (G1_large_prime_decomp_sq_active_localOrder n)
    (sum_localOrderBound_largePrimeActiveSq_le_supportSq_two_add_wieferich_excess_plus_one n hz2)

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_two_add_L_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) +
        (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
  have hBase :
      (largePrimeActiveSupportSq n).card * 2 + 1 <=
        (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) := by
    calc
      (largePrimeActiveSupportSq n).card * 2 + 1 <=
          ((lowFourthPrimeActiveSupportSq n).card + (L n + 1)) * 2 + 1 := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right 2 (card_largePrimeActiveSupportSq_le_lowFourth_add_L_add_one n))
              1
      _ = (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) := by
            rw [Nat.add_mul]
            ac_rfl
  calc
    (B n (z n)).card <=
        (largePrimeActiveSupportSq n).card * 2 + 1 +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
            exact G1_large_prime_decomp_sq_active_localOrder_supportSq_two_add_wieferich_excess_plus_one
              n hz2
    _ <= (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) +
          (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
            exact Nat.add_le_add_right hBase
              ((wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2))

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            (((L n + 1) / 2 + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpAct : p ∈ largePrimeActiveSupportSq n := lowFourthPrimeActiveSupportSq_subset n hp
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            (((L n + 1) / 2 + 1) - 1) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_excess
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card)
    _ <= (K n).card +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card)
    _ <= (L n + 1) +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_lowFourth_nonWieferich_card_add_L_add_wieferich_local
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => localOrderBound n p)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpAct : p ∈ largePrimeActiveSupportSq n := lowFourthPrimeActiveSupportSq_subset n hp
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) =
        (nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => localOrderBound n p) := by
    exact sum_localOrderBound_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card)
    _ = (K n).card +
          ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => localOrderBound n p)) := by
            rw [hLowLocal]
    _ <= (L n + 1) +
          ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => localOrderBound n p)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_lowFourth_nonWieferich_card_add_L_add_wieferich_Np
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => Np n p)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowExact :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        (nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => Np n p) := by
    exact sum_Np_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ = (K n).card +
          ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => Np n p)) := by
            rw [hLowExact]
    _ <= (L n + 1) +
          ((nonWieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => Np n p)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_lowFourth_card_add_L_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => Np n p - 1)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowExact :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        (lowFourthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => Np n p - 1) := by
    exact sum_Np_largePrimeActiveSubset_eq_card_add_wieferich_excess
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ = (K n).card +
          ((lowFourthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => Np n p - 1)) := by
            rw [hLowExact]
    _ <= (L n + 1) +
          ((lowFourthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => Np n p - 1)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_third_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            (((L n + 1) / 3 + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpAct : p ∈ largePrimeActiveSupportSq n := lowFourthPrimeActiveSupportSq_subset n hp
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            (((L n + 1) / 3 + 1) - 1) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_third_excess
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card)
    _ <= (K n).card +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              (((L n + 1) / 3 + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card)
    _ <= (L n + 1) +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              (((L n + 1) / 3 + 1) - 1)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_div_excess
    (n d : Nat) (hz3 : 3 <= z n) (hpow : 2 ^ d < (z n + 1) ^ 2) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            ((((L n + 1) / (d + 1)) + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpAct : p ∈ largePrimeActiveSupportSq n := lowFourthPrimeActiveSupportSq_subset n hp
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            ((((L n + 1) / (d + 1)) + 1) - 1) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_div_excess
      n (lowFourthPrimeActiveSupportSq n) d (lowFourthPrimeActiveSupportSq_subset n) hz3 hpow
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card)
    _ <= (K n).card +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              ((((L n + 1) / (d + 1)) + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card)
    _ <= (L n + 1) +
          ((lowFourthPrimeActiveSupportSq n).card +
            (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
              ((((L n + 1) / (d + 1)) + 1) - 1)) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_log_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          (wieferichSubsupport (lowFourthPrimeActiveSupportSq n)).card *
            ((((L n + 1) / (2 * Nat.log 2 (z n + 1))) + 1) - 1)) := by
  have hm : 2 <= z n + 1 := by omega
  have hm1 : 1 < z n + 1 := lt_of_lt_of_le (by decide : 1 < 2) hm
  have hpow :
      2 ^ (2 * Nat.log 2 (z n + 1) - 1) < (z n + 1) ^ 2 :=
    two_pow_two_mul_log_sub_one_lt_sq hm
  have hmain :=
    G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_div_excess
      n (2 * Nat.log 2 (z n + 1) - 1) hz3 hpow
  have hlogPos : 1 <= 2 * Nat.log 2 (z n + 1) := by
    have hlog : 0 < Nat.log 2 (z n + 1) := Nat.log_pos Nat.one_lt_two hm1
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 2) hlog)
  have hden :
      (2 * Nat.log 2 (z n + 1) - 1) + 1 = 2 * Nat.log 2 (z n + 1) :=
    Nat.sub_add_cancel hlogPos
  simpa [hden] using hmain

lemma G1_large_prime_decomp_sq_active_localOrder_lowFourth_one_add_L_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) +
        ((lowFourthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  classical
  have hsplit :
      Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
    simpa [veryLargePrimeActiveSupportSq, lowFourthPrimeActiveSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeActiveSupportSq n) (p := fun p => n < p ^ 4) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpAct : p ∈ largePrimeActiveSupportSq n := lowFourthPrimeActiveSupportSq_subset n hp
      have hpSq : p ∈ largePrimeSupportSq n := largePrimeActiveSupportSq_subset n hpAct
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFourthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_logPrime_excess
      n (lowFourthPrimeActiveSupportSq n) (lowFourthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeActiveSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq_active n
    _ = Finset.sum (veryLargePrimeActiveSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_veryLargePrimeActiveSupportSq_le_cardK n) _
    _ <= (K n).card + Finset.sum (lowFourthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card)
    _ <= (K n).card +
          ((lowFourthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card)
    _ <= (L n + 1) +
          ((lowFourthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFourthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_right (card_K_le n) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_localOrder_two_add_wieferich_excess
    (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowSixthPrimeActiveSupportSq n).card * 2 + 1 +
          (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2)) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowSixthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowSixthPrimeActiveSupportSq n).card * 2 + 1 +
          (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) := by
    simpa [wieferichLowSixthPrimeActiveSupportSq] using
      (sum_localOrderBound_largePrimeActiveSubset_le_two_mul_card_add_wieferich_excess_plus_one
        n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz2)
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowSixthPrimeActiveSupportSq n).card * 2 + 1 +
            (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowSixthPrimeActiveSupportSq n).card * 2 + 1 +
            (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_localOrder_one_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowSixthPrimeActiveSupportSq n).card +
          (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowSixthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowSixthPrimeActiveSupportSq n).card +
          (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1) := by
    simpa [wieferichLowSixthPrimeActiveSupportSq] using
      (sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_excess
        n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz3)
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            (wieferichLowSixthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_nonWieferich_card_add_wieferich_local
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => localOrderBound n p)) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowSixthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) =
        (nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => localOrderBound n p) := by
    exact sum_localOrderBound_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
      n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ = (K n).card * 2 +
          ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => localOrderBound n p)) := by
            rw [hLowLocal]
    _ <= (L n + 1) * 2 +
          ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => localOrderBound n p)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_nonWieferich_card_add_wieferich_Np
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => Np n p)) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowExact :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) =
        (nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => Np n p) := by
    exact sum_Np_largePrimeActiveSubset_eq_nonWieferich_card_add_wieferich_sum
      n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ = (K n).card * 2 +
          ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => Np n p)) := by
            rw [hLowExact]
    _ <= (L n + 1) * 2 +
          ((nonWieferichSubsupport (lowSixthPrimeActiveSupportSq n)).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => Np n p)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_card_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowSixthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => Np n p - 1)) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowExact :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) =
        (lowSixthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => Np n p - 1) := by
    exact sum_Np_largePrimeActiveSubset_eq_card_add_wieferich_excess
      n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ = (K n).card * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => Np n p - 1)) := by
            rw [hLowExact]
    _ <= (L n + 1) * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => Np n p - 1)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highSixth_lowSixthActive_localOrder_one_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowSixthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  classical
  have hsplit :
      Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highSixthPrimeSupportSq, lowSixthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 6) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowSixthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowSixthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_logPrime_excess
      n (lowSixthPrimeActiveSupportSq n) (lowSixthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highSixthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highSixthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowSixthPrimeSupportSq_eq_sum_lowSixthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowSixthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowSixthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowSixthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highFifth_lowFifthActive_localOrder_one_add_wieferich_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowFifthPrimeActiveSupportSq n).card +
          (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highFifthPrimeSupportSq, lowFifthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 5) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowFifthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFifthPrimeActiveSupportSq n).card +
          (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1) := by
    simpa [wieferichLowFifthPrimeActiveSupportSq] using
      (sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_excess
        n (lowFifthPrimeActiveSupportSq n) (lowFifthPrimeActiveSupportSq_subset n) hz3)
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highFifthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowFifthPrimeSupportSq_eq_sum_lowFifthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 1)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highFifth_lowFifthActive_localOrder_one_add_wieferich_third_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowFifthPrimeActiveSupportSq n).card +
          (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 3 + 1) - 1)) := by
  classical
  have hsplit :
      Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highFifthPrimeSupportSq, lowFifthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 5) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowFifthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFifthPrimeActiveSupportSq n).card +
          (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 3 + 1) - 1) := by
    simpa [wieferichLowFifthPrimeActiveSupportSq] using
      (sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_third_excess
        n (lowFifthPrimeActiveSupportSq n) (lowFifthPrimeActiveSupportSq_subset n) hz3)
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highFifthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowFifthPrimeSupportSq_eq_sum_lowFifthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 3 + 1) - 1)) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            (wieferichLowFifthPrimeActiveSupportSq n).card * (((L n + 1) / 3 + 1) - 1)) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

lemma G1_large_prime_decomp_sq_highFifth_lowFifthActive_localOrder_one_add_wieferich_logPrime_excess
    (n : Nat) (hz3 : 3 <= z n) :
    (B n (z n)).card <=
      (L n + 1) * 2 +
        ((lowFifthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFifthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
  classical
  have hsplit :
      Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) =
        Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
    simpa [highFifthPrimeSupportSq, lowFifthPrimeSupportSq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := largePrimeSupportSq n) (p := fun p => n < p ^ 5) (f := fun p => Np n p))
  have hLowNp :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) <=
        Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
    exact Finset.sum_le_sum (by
      intro p hp
      have hpSq : p ∈ largePrimeSupportSq n :=
        lowFifthPrimeSupportSq_subset n ((Finset.mem_filter.mp hp).1)
      exact Np_le_localOrderBound_of_largePrimeSupport n p ((Finset.mem_filter.mp hpSq).1))
  have hLowLocal :
      Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) <=
        (lowFifthPrimeActiveSupportSq n).card +
          Finset.sum (wieferichSubsupport (lowFifthPrimeActiveSupportSq n))
            (fun p => (L n + 1) / (2 * Nat.log 2 p)) := by
    exact sum_localOrderBound_largePrimeActiveSubset_le_card_add_wieferich_logPrime_excess
      n (lowFifthPrimeActiveSupportSq n) (lowFifthPrimeActiveSupportSq_subset n) hz3
  calc
    (B n (z n)).card <= Finset.sum (largePrimeSupportSq n) (fun p => Np n p) := by
      exact G1_large_prime_decomp_sq n
    _ = Finset.sum (highFifthPrimeSupportSq n) (fun p => Np n p) +
          Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            symm
            exact hsplit
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeSupportSq n) (fun p => Np n p) := by
            exact Nat.add_le_add_right (sum_Np_highFifthPrimeSupportSq_le_two_mul_cardK n) _
    _ = (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => Np n p) := by
            rw [sum_Np_lowFifthPrimeSupportSq_eq_sum_lowFifthPrimeActiveSupportSq]
    _ <= (K n).card * 2 + Finset.sum (lowFifthPrimeActiveSupportSq n) (fun p => localOrderBound n p) := by
            exact Nat.add_le_add_left hLowNp ((K n).card * 2)
    _ <= (K n).card * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFifthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_left hLowLocal ((K n).card * 2)
    _ <= (L n + 1) * 2 +
          ((lowFifthPrimeActiveSupportSq n).card +
            Finset.sum (wieferichSubsupport (lowFifthPrimeActiveSupportSq n))
              (fun p => (L n + 1) / (2 * Nat.log 2 p))) := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_right 2 (card_K_le n)) _

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

/-- G2 (square-range coarse form): same bound over `largePrimeSupportSq`. -/
lemma G2_large_prime_via_local_sq (n : Nat) :
  Finset.sum (largePrimeSupportSq n) (fun p => Np n p) <=
    (largePrimeSupportSq n).card * (L n + 1) := by
  have hpoint : ∀ p ∈ largePrimeSupportSq n, Np n p <= L n + 1 := by
    intro p hp
    exact L2_local_periodic n p ((Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).2)
  calc
    Finset.sum (largePrimeSupportSq n) (fun p => Np n p) <=
        Finset.sum (largePrimeSupportSq n) (fun _ => L n + 1) := by
          exact Finset.sum_le_sum hpoint
    _ = (largePrimeSupportSq n).card * (L n + 1) := by
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

/--
Square-truncated large-prime sum condition:
only the non-vacuous range `p^2 <= n` is summed.
-/
def G3_sumSq_bound_eventually : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (largePrimeSupportSq n) (fun p => Np n p) < L n

/--
Slackened square-truncated large-prime sum condition.
-/
def G3_sumSq_bound_eventually_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    Finset.sum (largePrimeSupportSq n) (fun p => Np n p) < L n - C

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

lemma G3_of_sumSq_bound_eventually (hSum : G3_sumSq_bound_eventually) :
    G3_large_prime_error := by
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq n) (hN n hn hodd)

lemma G3_of_sumSq_bound_eventually_slack {C : Nat}
    (hSum : G3_sumSq_bound_eventually_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSum with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hodd
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq n) (hN n hn hodd)

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

/--
Improved support-size condition using the order-based half-factor:
for `z n >= 2`, every large prime is odd, so each local term is at most
`(L n + 1) / 2 + 1`.
-/
def G3_support_bound_eventually_half : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupport n).card * ((L n + 1) / 2 + 1) < L n

/--
Square-truncated variant of the support-size condition, still with the
order-based half-factor.
-/
def G3_supportSq_bound_eventually_half : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupportSq n).card * ((L n + 1) / 2 + 1) < L n

/--
Square-truncated large-prime condition with an explicit base-2 Wieferich split:
the non-Wieferich part pays the sharper `(L n + 1) / p + 1` local cost, while the
Wieferich remainder keeps the older half-factor bound.
-/
def G3_supportSq_bound_eventually_wieferichSplit : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
      Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) < L n

/-- Slackened Wieferich-split large-prime condition. -/
def G3_supportSq_bound_eventually_wieferichSplit_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
      Finset.sum (nonWieferichLargePrimeSupportSq n) (fun p => (L n + 1) / p + 1) < L n - C

/--
Coarser but simpler square-truncated Wieferich split:
the non-Wieferich contribution is compressed to the constant local bound `3`.
-/
def G3_supportSq_bound_eventually_wieferichThreeSplit : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
      (nonWieferichLargePrimeSupportSq n).card * 3 < L n

/-- Slackened constant-`3` Wieferich split. -/
def G3_supportSq_bound_eventually_wieferichThreeSplit_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (wieferichLargePrimeSupportSq n).card * ((L n + 1) / 2 + 1) +
      (nonWieferichLargePrimeSupportSq n).card * 3 < L n - C

/--
Compressed square-range criterion:
pay `3` for every square-range large prime, plus only the Wieferich excess over `3`.
-/
def G3_supportSq_bound_eventually_wieferichExcess : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupportSq n).card * 3 +
      (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) < L n

/-- Slackened Wieferich-excess criterion. -/
def G3_supportSq_bound_eventually_wieferichExcess_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeSupportSq n).card * 3 +
      (wieferichLargePrimeSupportSq n).card * (((L n + 1) / 2 + 1) - 3) < L n - C

/--
Active-support version of the Wieferich-excess criterion:
only primes with `Np n p ≠ 0` are counted.
-/
def G3_activeSupportSq_bound_eventually_wieferichExcess : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeActiveSupportSq n).card * 3 +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) < L n

/-- Slackened active-support Wieferich-excess criterion. -/
def G3_activeSupportSq_bound_eventually_wieferichExcess_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeActiveSupportSq n).card * 3 +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 3) < L n - C

/--
Stronger active-support criterion:
the non-Wieferich active part costs only `2` per prime, with one possible endpoint bonus.
-/
def G3_activeSupportSq_bound_eventually_wieferichExcess_two : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeActiveSupportSq n).card * 2 + 1 +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) < L n

/-- Slackened version of the stronger active-support criterion. -/
def G3_activeSupportSq_bound_eventually_wieferichExcess_two_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeActiveSupportSq n).card * 2 + 1 +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) < L n - C

/--
Low-fourth-range active-support criterion:
the very-large active primes (`p^4 > n`) are absorbed into the explicit `2 * (L n + 1) + 1`
term, leaving only the low-fourth active support and the active Wieferich excess.
-/
def G3_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) < L n

/-- Slackened low-fourth-range active-support criterion. -/
def G3_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (lowFourthPrimeActiveSupportSq n).card * 2 + ((L n + 1) * 2 + 1) +
      (wieferichLargePrimeActiveSupportSq n).card * (((L n + 1) / 2 + 1) - 2) < L n - C

lemma two_le_z_of_sixteen_le {n : Nat} (hn : 16 <= n) : 2 <= z n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 16) hn)
  have hlog4 : 4 <= L n := by
    unfold L
    refine (Nat.le_log_iff_pow_le Nat.one_lt_two hn0).2 ?_
    simpa using hn
  unfold z
  omega

lemma three_le_z_of_sixtyfour_le {n : Nat} (hn : 64 <= n) : 3 <= z n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 64) hn)
  have hlog6 : 6 <= L n := by
    unfold L
    refine (Nat.le_log_iff_pow_le Nat.one_lt_two hn0).2 ?_
    simpa using hn
  unfold z
  omega

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

lemma G3_of_support_bound_eventually_half (hSupp : G3_support_bound_eventually_half) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_localOrder_half n hz2) (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_half
    (hSupp : G3_supportSq_bound_eventually_half) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq_localOrder_half n hz2) (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichSplit
    (hSupp : G3_supportSq_bound_eventually_wieferichSplit) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq_localOrder_wieferich_split n hz2)
    (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichSplit_slack {C : Nat}
    (hSupp : G3_supportSq_bound_eventually_wieferichSplit_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq_localOrder_wieferich_split n hz2)
    (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichThreeSplit
    (hSupp : G3_supportSq_bound_eventually_wieferichThreeSplit) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq_localOrder_wieferich_three_split n hz2)
    (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichThreeSplit_slack {C : Nat}
    (hSupp : G3_supportSq_bound_eventually_wieferichThreeSplit_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt (G1_large_prime_decomp_sq_localOrder_wieferich_three_split n hz2)
    (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichExcess
    (hSupp : G3_supportSq_bound_eventually_wieferichExcess) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_localOrder_supportSq_three_add_wieferich_excess n hz2)
    (hN n hnN hodd)

lemma G3_of_supportSq_bound_eventually_wieferichExcess_slack {C : Nat}
    (hSupp : G3_supportSq_bound_eventually_wieferichExcess_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_localOrder_supportSq_three_add_wieferich_excess n hz2)
    (hN n hnN hodd)

lemma G3_of_activeSupportSq_bound_eventually_wieferichExcess
    (hSupp : G3_activeSupportSq_bound_eventually_wieferichExcess) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_supportSq_three_add_wieferich_excess n hz2)
    (hN n hnN hodd)

lemma G3_of_activeSupportSq_bound_eventually_wieferichExcess_slack {C : Nat}
    (hSupp : G3_activeSupportSq_bound_eventually_wieferichExcess_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_supportSq_three_add_wieferich_excess n hz2)
    (hN n hnN hodd)

lemma G3_of_activeSupportSq_bound_eventually_wieferichExcess_two
    (hSupp : G3_activeSupportSq_bound_eventually_wieferichExcess_two) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_supportSq_two_add_wieferich_excess_plus_one n hz2)
    (hN n hnN hodd)

lemma G3_of_activeSupportSq_bound_eventually_wieferichExcess_two_slack {C : Nat}
    (hSupp : G3_activeSupportSq_bound_eventually_wieferichExcess_two_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_supportSq_two_add_wieferich_excess_plus_one n hz2)
    (hN n hnN hodd)

lemma G3_of_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two
    (hSupp : G3_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two) :
    G3_large_prime_error := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_lowFourth_two_add_L_add_wieferich_excess n hz2)
    (hN n hnN hodd)

lemma G3_of_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two_slack {C : Nat}
    (hSupp : G3_lowFourthActiveSupportSq_bound_eventually_wieferichExcess_two_slack C) :
    G3_large_prime_error_slack C := by
  rcases hSupp with ⟨N, hN⟩
  refine ⟨max N 16, ?_⟩
  intro n hn hodd
  have hnN : N <= n := le_trans (le_max_left N 16) hn
  have hn16 : 16 <= n := le_trans (le_max_right N 16) hn
  have hz2 : 2 <= z n := two_le_z_of_sixteen_le hn16
  exact lt_of_le_of_lt
    (G1_large_prime_decomp_sq_active_localOrder_lowFourth_two_add_L_add_wieferich_excess n hz2)
    (hN n hnN hodd)

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
Density lower bounds with slope strictly above `1` are impossible:
if `d < a`, then `a * L n ≤ d * |A n|` cannot hold eventually.
-/
lemma not_S1_density_of_lt {a d : Nat} (hda : d < a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (2 ^ (d + 1))
  let n : Nat := 65 + 36 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨32 + 18 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hA_le_L1 : (A n (z n)).card <= L n + 1 := by
    have hA_le_K : (A n (z n)).card <= (K n).card := Finset.card_le_card (A_subset_K n (z n))
    exact le_trans hA_le_K (card_K_le n)
  have hupper : a * L n <= d * (L n + 1) := by
    exact le_trans hbound (Nat.mul_le_mul_left d hA_le_L1)
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL_ge : d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have ht : 2 ^ (d + 1) <= t := by
      dsimp [t]
      exact le_max_right N1 (2 ^ (d + 1))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans ht ht_le_n
  have hstrict : d * (L n + 1) < a * L n := by
    have hdLtL : d < L n := lt_of_lt_of_le (Nat.lt_succ_self d) hL_ge
    have hda1 : 1 <= a - d := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hda)
    have hgap : d < (a - d) * L n := by
      have hmul_ge : L n <= (a - d) * L n := by
        calc
          L n = 1 * L n := by simp
          _ <= (a - d) * L n := Nat.mul_le_mul_right (L n) hda1
      exact lt_of_lt_of_le hdLtL hmul_ge
    have hsum :
        d * L n + d < d * L n + (a - d) * L n :=
      Nat.add_lt_add_left hgap (d * L n)
    have hleft : d * (L n + 1) = d * L n + d := by
      simp [Nat.mul_add, Nat.add_comm]
    have hright : d * L n + (a - d) * L n = a * L n := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hda)]
    exact hleft ▸ (lt_of_lt_of_eq hsum hright)
  exact (Nat.not_le_of_gt hstrict) hupper

lemma not_S1_density_of_five_mul_lt_six_mul {a d : Nat}
    (hRate : 5 * d < 6 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (2 ^ (11 * d + 1))
  let n : Nat := 65 + 36 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨32 + 18 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
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
  have hAub : (A n (z n)).card <= L n + 1 - L n / 6 :=
    card_A_le_L_add_one_sub_div_six_of_mod9 hn0 hz3 hmod9
  have hLbig : 11 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have ht : 2 ^ (11 * d + 1) <= t := by
      dsimp [t]
      exact le_max_right N1 (2 ^ (11 * d + 1))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans ht ht_le_n
  have hmul : d * (A n (z n)).card <= d * (L n + 1 - L n / 6) := Nat.mul_le_mul_left d hAub
  have hmul6 : 6 * (d * (A n (z n)).card) <= 6 * (d * (L n + 1 - L n / 6)) :=
    Nat.mul_le_mul_left 6 hmul
  have hcore : 6 * (L n + 1 - L n / 6) <= 5 * L n + 11 := six_mul_sub_div_six_le (L n)
  have hcoreMul : d * (6 * (L n + 1 - L n / 6)) <= d * (5 * L n + 11) :=
    Nat.mul_le_mul_left d hcore
  have hAupper6 : 6 * (d * (A n (z n)).card) <= d * (5 * L n + 11) := by
    have hmul6' : 6 * (d * (A n (z n)).card) <= d * (6 * (L n + 1 - L n / 6)) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul6
    exact le_trans hmul6' hcoreMul
  have hbound6 : 6 * (a * L n) <= 6 * (d * (A n (z n)).card) := Nat.mul_le_mul_left 6 hbound
  have hcontr : 6 * (a * L n) <= d * (5 * L n + 11) := le_trans hbound6 hAupper6
  have hstrict : d * (5 * L n + 11) < 6 * (a * L n) :=
    d_mul_fiveL_add11_lt_six_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_47_mul_lt_60_mul {a d : Nat}
    (hRate : 47 * d < 60 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max 3 (2 ^ (167 * d + 1)))
  let n : Nat := 101 + 450 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨50 + 225 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have ht3 : 3 <= t := by
    dsimp [t]
    exact le_trans (le_max_left 3 (2 ^ (167 * d + 1))) (le_max_right N1 (max 3 (2 ^ (167 * d + 1))))
  have hn1024 : 1024 <= n := by
    dsimp [n]
    omega
  have hL10 : 10 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hAub : (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20) :=
    card_A_le_L_add_one_sub_div_six_add_div_twenty_of_mod9_mod25 hn0 hz3 hz5 hmod9 hmod25
  have hLbig : 167 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (167 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right 3 (2 ^ (167 * d + 1)))
        (le_max_right N1 (max 3 (2 ^ (167 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <= d * (L n + 1 - (L n / 6 + L n / 20)) :=
    Nat.mul_le_mul_left d hAub
  have hmul60 :
      60 * (d * (A n (z n)).card) <= 60 * (d * (L n + 1 - (L n / 6 + L n / 20))) :=
    Nat.mul_le_mul_left 60 hmul
  have hcore : 60 * (L n + 1 - (L n / 6 + L n / 20)) <= 47 * L n + 167 :=
    sixty_mul_sub_div_six_add_div_twenty_le (L n)
  have hcoreMul : d * (60 * (L n + 1 - (L n / 6 + L n / 20))) <= d * (47 * L n + 167) :=
    Nat.mul_le_mul_left d hcore
  have hAupper60 : 60 * (d * (A n (z n)).card) <= d * (47 * L n + 167) := by
    have hmul60' :
        60 * (d * (A n (z n)).card) <= d * (60 * (L n + 1 - (L n / 6 + L n / 20))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul60
    exact le_trans hmul60' hcoreMul
  have hbound60 : 60 * (a * L n) <= 60 * (d * (A n (z n)).card) := Nat.mul_le_mul_left 60 hbound
  have hcontr : 60 * (a * L n) <= d * (47 * L n + 167) := le_trans hbound60 hAupper60
  have hstrict : d * (47 * L n + 167) < 60 * (a * L n) :=
    d_mul_47L_add167_lt_sixty_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_319_mul_lt_420_mul {a d : Nat}
    (hRate : 319 * d < 420 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max 3 (2 ^ (1579 * d + 1)))
  let n : Nat := 2801 + 22050 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨1400 + 11025 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL14 : 14 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    dsimp [n, t]
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hAub : (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42) :=
    card_A_le_L_add_one_sub_div_six_add_div_twenty_add_div_forty_two_of_mod9_mod25_mod49
      hn0 hz3 hz5 hz7 hmod9 hmod25 hmod49
  have hLbig : 1579 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (1579 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right 3 (2 ^ (1579 * d + 1)))
        (le_max_right N1 (max 3 (2 ^ (1579 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <= d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42)) :=
    Nat.mul_le_mul_left d hAub
  have hmul420 :
      420 * (d * (A n (z n)).card) <=
        420 * (d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42))) :=
    Nat.mul_le_mul_left 420 hmul
  have hcore : 420 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42)) <= 319 * L n + 1579 :=
    fourtwenty_mul_sub_div_six_add_div_twenty_add_div_forty_two_le (L n)
  have hcoreMul :
      d * (420 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42))) <= d * (319 * L n + 1579) :=
    Nat.mul_le_mul_left d hcore
  have hAupper420 : 420 * (d * (A n (z n)).card) <= d * (319 * L n + 1579) := by
    have hmul420' :
        420 * (d * (A n (z n)).card) <=
          d * (420 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul420
    exact le_trans hmul420' hcoreMul
  have hbound420 : 420 * (a * L n) <= 420 * (d * (A n (z n)).card) := Nat.mul_le_mul_left 420 hbound
  have hcontr : 420 * (a * L n) <= d * (319 * L n + 1579) := le_trans hbound420 hAupper420
  have hstrict : d * (319 * L n + 1579) < 420 * (a * L n) :=
    d_mul_319L_add1579_lt_fourtwenty_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_3467_mul_lt_4620_mul {a d : Nat}
    (hRate : 3467 * d < 4620 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max 3 (2 ^ (21947 * d + 1)))
  let n : Nat := 2516501 + 2668050 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨1258250 + 1334025 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL23 : 23 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    dsimp [n, t]
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hz11 : 11 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hmod121 : n % 121 = 64 := by
    dsimp [n]
    omega
  have hAub :
      (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110) :=
    card_A_le_L_add_one_sub_div_6_20_42_110_of_mods
      hn0 hz3 hz5 hz7 hz11 hmod9 hmod25 hmod49 hmod121
  have hLbig : 21947 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (21947 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right 3 (2 ^ (21947 * d + 1)))
        (le_max_right N1 (max 3 (2 ^ (21947 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <= d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110)) :=
    Nat.mul_le_mul_left d hAub
  have hmul4620 :
      4620 * (d * (A n (z n)).card) <=
        4620 * (d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110))) :=
    Nat.mul_le_mul_left 4620 hmul
  have hcore :
      4620 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110)) <= 3467 * L n + 21947 :=
    f4620_bound (L n)
  have hcoreMul :
      d * (4620 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110))) <=
        d * (3467 * L n + 21947) :=
    Nat.mul_le_mul_left d hcore
  have hAupper4620 : 4620 * (d * (A n (z n)).card) <= d * (3467 * L n + 21947) := by
    have hmul4620' :
        4620 * (d * (A n (z n)).card) <=
          d * (4620 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul4620
    exact le_trans hmul4620' hcoreMul
  have hbound4620 : 4620 * (a * L n) <= 4620 * (d * (A n (z n)).card) :=
    Nat.mul_le_mul_left 4620 hbound
  have hcontr : 4620 * (a * L n) <= d * (3467 * L n + 21947) := le_trans hbound4620 hAupper4620
  have hstrict : d * (3467 * L n + 21947) < 4620 * (a * L n) :=
    d_mul_3467L_add21947_lt_4620_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_44686_mul_lt_60060_mul {a d : Nat}
    (hRate : 44686 * d < 60060 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max 3 (2 ^ (344986 * d + 1)))
  let n : Nat := 199952201 + 450900450 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨99976100 + 225450225 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL30 : 30 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    dsimp [n, t]
    omega
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hz11 : 11 <= z n := by
    unfold z
    omega
  have hz13 : 13 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hmod121 : n % 121 = 64 := by
    dsimp [n]
    omega
  have hmod169 : n % 169 = 20 := by
    dsimp [n]
    omega
  have hAub :
      (A n (z n)).card <= L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156) :=
    card_A_le_L_add_one_sub_div_6_20_42_110_156_of_mods
      hn0 hz3 hz5 hz7 hz11 hz13 hmod9 hmod25 hmod49 hmod121 hmod169
  have hLbig : 344986 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (344986 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right 3 (2 ^ (344986 * d + 1)))
        (le_max_right N1 (max 3 (2 ^ (344986 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <=
        d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156)) :=
    Nat.mul_le_mul_left d hAub
  have hmul60060 :
      60060 * (d * (A n (z n)).card) <=
        60060 * (d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156))) :=
    Nat.mul_le_mul_left 60060 hmul
  have hcore :
      60060 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156)) <=
        44686 * L n + 344986 := f60060_bound (L n)
  have hcoreMul :
      d * (60060 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156))) <=
        d * (44686 * L n + 344986) :=
    Nat.mul_le_mul_left d hcore
  have hAupper60060 : 60060 * (d * (A n (z n)).card) <= d * (44686 * L n + 344986) := by
    have hmul60060' :
        60060 * (d * (A n (z n)).card) <=
          d * (60060 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul60060
    exact le_trans hmul60060' hcoreMul
  have hbound60060 : 60060 * (a * L n) <= 60060 * (d * (A n (z n)).card) :=
    Nat.mul_le_mul_left 60060 hbound
  have hcontr : 60060 * (a * L n) <= d * (44686 * L n + 344986) := le_trans hbound60060 hAupper60060
  have hstrict : d * (44686 * L n + 344986) < 60060 * (a * L n) :=
    d_mul_44686L_add344986_lt_60060_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_1829123_mul_lt_2462460_mul {a d : Nat}
    (hRate : 1829123 * d < 2462460 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max (2 ^ 82) (2 ^ (16603883 * d + 1)))
  let n : Nat := 368585619851 + 757963656450 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨184292809925 + 378981828225 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL82 : 82 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have ht82 : 2 ^ 82 <= t := by
      dsimp [t]
      exact le_trans (le_max_left (2 ^ 82) (2 ^ (16603883 * d + 1)))
        (le_max_right N1 (max (2 ^ 82) (2 ^ (16603883 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans ht82 ht_le_n
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hz11 : 11 <= z n := by
    unfold z
    omega
  have hz13 : 13 <= z n := by
    unfold z
    omega
  have hz41 : 41 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hmod121 : n % 121 = 64 := by
    dsimp [n]
    omega
  have hmod169 : n % 169 = 20 := by
    dsimp [n]
    omega
  have hmod1681 : n % 1681 = 4 := by
    dsimp [n]
    omega
  have hAub :
      (A n (z n)).card <=
        L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820) :=
    card_A_le_L_add_one_sub_div_6_20_42_110_156_820_of_mods
      hn0 hz3 hz5 hz7 hz11 hz13 hz41 hmod9 hmod25 hmod49 hmod121 hmod169 hmod1681
  have hLbig : 16603883 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (16603883 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right (2 ^ 82) (2 ^ (16603883 * d + 1)))
        (le_max_right N1 (max (2 ^ 82) (2 ^ (16603883 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <=
        d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820)) :=
    Nat.mul_le_mul_left d hAub
  have hmul2462460 :
      2462460 * (d * (A n (z n)).card) <=
        2462460 *
          (d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820))) :=
    Nat.mul_le_mul_left 2462460 hmul
  have hcore :
      2462460 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820)) <=
        1829123 * L n + 16603883 := f2462460_bound (L n)
  have hcoreMul :
      d *
          (2462460 * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820))) <=
        d * (1829123 * L n + 16603883) :=
    Nat.mul_le_mul_left d hcore
  have hAupper2462460 : 2462460 * (d * (A n (z n)).card) <= d * (1829123 * L n + 16603883) := by
    have hmul2462460' :
        2462460 * (d * (A n (z n)).card) <=
          d *
            (2462460 *
              (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul2462460
    exact le_trans hmul2462460' hcoreMul
  have hbound2462460 : 2462460 * (a * L n) <= 2462460 * (d * (A n (z n)).card) :=
    Nat.mul_le_mul_left 2462460 hbound
  have hcontr : 2462460 * (a * L n) <= d * (1829123 * L n + 16603883) :=
    le_trans hbound2462460 hAupper2462460
  have hstrict : d * (1829123 * L n + 16603883) < 2462460 * (a * L n) :=
    d_mul_1829123L_add16603883_lt_2462460_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_202827448_mul_lt_273333060_mul {a d : Nat}
    (hRate : 202827448 * d < 273333060 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max (2 ^ 82) (2 ^ (2116158868 * d + 1)))
  let n : Nat := 646153620915251 + 1037652245680050 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨323076810457625 + 518826122840025 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL82 : 82 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have ht82 : 2 ^ 82 <= t := by
      dsimp [t]
      exact le_trans (le_max_left (2 ^ 82) (2 ^ (2116158868 * d + 1)))
        (le_max_right N1 (max (2 ^ 82) (2 ^ (2116158868 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans ht82 ht_le_n
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hz11 : 11 <= z n := by
    unfold z
    omega
  have hz13 : 13 <= z n := by
    unfold z
    omega
  have hz41 : 41 <= z n := by
    unfold z
    omega
  have hz37 : 37 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hmod121 : n % 121 = 64 := by
    dsimp [n]
    omega
  have hmod169 : n % 169 = 20 := by
    dsimp [n]
    omega
  have hmod1681 : n % 1681 = 4 := by
    dsimp [n]
    omega
  have hmod1369 : n % 1369 = 32 := by
    dsimp [n]
    omega
  have hAub :
      (A n (z n)).card <=
        L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332) :=
    card_A_le_L_add_one_sub_div_6_20_42_110_156_820_1332_of_mods
      hn0 hz3 hz5 hz7 hz11 hz13 hz41 hz37
      hmod9 hmod25 hmod49 hmod121 hmod169 hmod1681 hmod1369
  have hLbig : 2116158868 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (2116158868 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right (2 ^ 82) (2 ^ (2116158868 * d + 1)))
        (le_max_right N1 (max (2 ^ 82) (2 ^ (2116158868 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <=
        d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332)) :=
    Nat.mul_le_mul_left d hAub
  have hmul273333060 :
      273333060 * (d * (A n (z n)).card) <=
        273333060 *
          (d * (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332))) :=
    Nat.mul_le_mul_left 273333060 hmul
  have hcore :
      273333060 *
          (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332)) <=
        202827448 * L n + 2116158868 := f273333060_bound (L n)
  have hcoreMul :
      d *
          (273333060 *
            (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332))) <=
        d * (202827448 * L n + 2116158868) :=
    Nat.mul_le_mul_left d hcore
  have hAupper273333060 :
      273333060 * (d * (A n (z n)).card) <= d * (202827448 * L n + 2116158868) := by
    have hmul273333060' :
        273333060 * (d * (A n (z n)).card) <=
          d *
            (273333060 *
              (L n + 1 - (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul273333060
    exact le_trans hmul273333060' hcoreMul
  have hbound273333060 : 273333060 * (a * L n) <= 273333060 * (d * (A n (z n)).card) :=
    Nat.mul_le_mul_left 273333060 hbound
  have hcontr : 273333060 * (a * L n) <= d * (202827448 * L n + 2116158868) :=
    le_trans hbound273333060 hAupper273333060
  have hstrict : d * (202827448 * L n + 2116158868) < 273333060 * (a * L n) :=
    d_mul_202827448L_add2116158868_lt_273333060_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_12367918777_mul_lt_16673316660_mul {a d : Nat}
    (hRate : 12367918777 * d < 16673316660 * a) : ¬ S1_density a d := by
  intro hS1
  rcases hS1 with ⟨N1, hN1⟩
  let t : Nat := max N1 (max (2 ^ 122) (2 ^ (145754452057 * d + 1)))
  let n : Nat := 2621755726208721551 + 3861104006175466050 * t
  have hnN : N1 <= n := by
    dsimp [n, t]
    omega
  have hodd : Odd n := by
    dsimp [n]
    refine ⟨1310877863104360775 + 1930552003087733025 * t, ?_⟩
    omega
  have hbound : a * L n <= d * (A n (z n)).card := hN1 n hnN hodd
  have hn0 : n ≠ 0 := by
    dsimp [n]
    omega
  have hL122 : 122 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have ht122 : 2 ^ 122 <= t := by
      dsimp [t]
      exact le_trans (le_max_left (2 ^ 122) (2 ^ (145754452057 * d + 1)))
        (le_max_right N1 (max (2 ^ 122) (2 ^ (145754452057 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans ht122 ht_le_n
  have hz3 : 3 <= z n := by
    unfold z
    omega
  have hz5 : 5 <= z n := by
    unfold z
    omega
  have hz7 : 7 <= z n := by
    unfold z
    omega
  have hz11 : 11 <= z n := by
    unfold z
    omega
  have hz13 : 13 <= z n := by
    unfold z
    omega
  have hz41 : 41 <= z n := by
    unfold z
    omega
  have hz37 : 37 <= z n := by
    unfold z
    omega
  have hz61 : 61 <= z n := by
    unfold z
    omega
  have hmod9 : n % 9 = 2 := by
    dsimp [n]
    omega
  have hmod25 : n % 25 = 1 := by
    dsimp [n]
    omega
  have hmod49 : n % 49 = 8 := by
    dsimp [n]
    omega
  have hmod121 : n % 121 = 64 := by
    dsimp [n]
    omega
  have hmod169 : n % 169 = 20 := by
    dsimp [n]
    omega
  have hmod1681 : n % 1681 = 4 := by
    dsimp [n]
    omega
  have hmod1369 : n % 1369 = 32 := by
    dsimp [n]
    omega
  have hmod3721 : n % 3721 = 16 := by
    dsimp [n]
    omega
  have hAub :
      (A n (z n)).card <=
        L n + 1 -
          (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660) :=
    card_A_le_L_add_one_sub_div_6_20_42_110_156_820_1332_3660_of_mods
      hn0 hz3 hz5 hz7 hz11 hz13 hz41 hz37 hz61
      hmod9 hmod25 hmod49 hmod121 hmod169 hmod1681 hmod1369 hmod3721
  have hLbig : 145754452057 * d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    have htPow : 2 ^ (145754452057 * d + 1) <= t := by
      dsimp [t]
      exact le_trans
        (le_max_right (2 ^ 122) (2 ^ (145754452057 * d + 1)))
        (le_max_right N1 (max (2 ^ 122) (2 ^ (145754452057 * d + 1))))
    have ht_le_n : t <= n := by
      dsimp [n]
      omega
    exact le_trans htPow ht_le_n
  have hmul :
      d * (A n (z n)).card <=
        d *
          (L n + 1 -
            (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660)) :=
    Nat.mul_le_mul_left d hAub
  have hmul16673316660 :
      16673316660 * (d * (A n (z n)).card) <=
        16673316660 *
          (d *
            (L n + 1 -
              (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660))) :=
    Nat.mul_le_mul_left 16673316660 hmul
  have hcore :
      16673316660 *
          (L n + 1 -
            (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660)) <=
        12367918777 * L n + 145754452057 := f16673316660_bound (L n)
  have hcoreMul :
      d *
          (16673316660 *
            (L n + 1 -
              (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660))) <=
        d * (12367918777 * L n + 145754452057) :=
    Nat.mul_le_mul_left d hcore
  have hAupper16673316660 :
      16673316660 * (d * (A n (z n)).card) <= d * (12367918777 * L n + 145754452057) := by
    have hmul16673316660' :
        16673316660 * (d * (A n (z n)).card) <=
          d *
            (16673316660 *
              (L n + 1 -
                (L n / 6 + L n / 20 + L n / 42 + L n / 110 + L n / 156 + L n / 820 + L n / 1332 + L n / 3660))) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul16673316660
    exact le_trans hmul16673316660' hcoreMul
  have hbound16673316660 : 16673316660 * (a * L n) <= 16673316660 * (d * (A n (z n)).card) :=
    Nat.mul_le_mul_left 16673316660 hbound
  have hcontr : 16673316660 * (a * L n) <= d * (12367918777 * L n + 145754452057) :=
    le_trans hbound16673316660 hAupper16673316660
  have hstrict : d * (12367918777 * L n + 145754452057) < 16673316660 * (a * L n) :=
    d_mul_12367918777L_add145754452057_lt_16673316660_mul_aL hRate hLbig
  exact (Nat.not_le_of_gt hstrict) hcontr

lemma not_S1_density_of_le_pos {a d : Nat} (ha : 0 < a) (hda : d <= a) :
    ¬ S1_density a d := by
  have h5da : 5 * d <= 5 * a := Nat.mul_le_mul_left 5 hda
  have h5a_lt_6a : 5 * a < 6 * a := by
    calc
      5 * a < 5 * a + a := Nat.lt_add_of_pos_right ha
      _ = 6 * a := by omega
  exact not_S1_density_of_five_mul_lt_six_mul (lt_of_le_of_lt h5da h5a_lt_6a)

lemma S1_density_implies_sixty_mul_a_le_fortyseven_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 60 * a <= 47 * d := by
  by_contra h
  exact (not_S1_density_of_47_mul_lt_60_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_fourtwenty_mul_a_le_threeonenine_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 420 * a <= 319 * d := by
  by_contra h
  exact (not_S1_density_of_319_mul_lt_420_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_4620_mul_a_le_3467_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 4620 * a <= 3467 * d := by
  by_contra h
  exact (not_S1_density_of_3467_mul_lt_4620_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_60060_mul_a_le_44686_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 60060 * a <= 44686 * d := by
  by_contra h
  exact (not_S1_density_of_44686_mul_lt_60060_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_2462460_mul_a_le_1829123_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 2462460 * a <= 1829123 * d := by
  by_contra h
  exact (not_S1_density_of_1829123_mul_lt_2462460_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_273333060_mul_a_le_202827448_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 273333060 * a <= 202827448 * d := by
  by_contra h
  exact (not_S1_density_of_202827448_mul_lt_273333060_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_16673316660_mul_a_le_12367918777_mul_d {a d : Nat}
    (hS1 : S1_density a d) : 16673316660 * a <= 12367918777 * d := by
  by_contra h
  exact (not_S1_density_of_12367918777_mul_lt_16673316660_mul (lt_of_not_ge h)) hS1

lemma S1_density_implies_a_le_d {a d : Nat} (hS1 : S1_density a d) : a <= d := by
  by_cases had : a <= d
  · exact had
  · exact False.elim ((not_S1_density_of_lt (lt_of_not_ge had)) hS1)

lemma S1_density_implies_a_lt_d_of_pos {a d : Nat}
    (ha : 0 < a) (hS1 : S1_density a d) : a < d := by
  have hnot : ¬ d <= a := by
    intro hda
    exact (not_S1_density_of_le_pos ha hda) hS1
  exact lt_of_not_ge hnot

/--
Density-form large-prime bound:
eventually, `d * |B n| < b * L n`.
-/
def G3_density (b d : Nat) : Prop :=
  exists N2 : Nat, forall n : Nat, N2 <= n -> Odd n ->
    d * (B n (z n)).card < b * L n

/--
Coarse unconditional density control for the large-prime side:
if `d < b`, then eventually `d * |B n| < b * L n`.
-/
lemma G3_density_of_lt {b d : Nat} (hbd : d < b) : G3_density b d := by
  let N : Nat := 2 ^ (d + 1)
  refine ⟨N, ?_⟩
  intro n hn hodd
  have hn0 : n ≠ 0 := by
    have hNpos : 0 < N := by
      dsimp [N]
      exact Nat.pow_pos (by decide : 0 < 2)
    have hNle : 1 <= N := Nat.succ_le_of_lt hNpos
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_trans hNle hn))
  have hL_ge : d + 1 <= L n := by
    unfold L
    rw [Nat.le_log_iff_pow_le Nat.one_lt_two hn0]
    exact hn
  have hB_le_K : (B n (z n)).card <= (K n).card := Finset.card_le_card (B_subset_K n (z n))
  have hB_le_L1 : (B n (z n)).card <= L n + 1 := le_trans hB_le_K (card_K_le n)
  have hmulB : d * (B n (z n)).card <= d * (L n + 1) := Nat.mul_le_mul_left d hB_le_L1
  have hltDL : d * (L n + 1) < b * L n := by
    have hdLtL : d < L n := lt_of_lt_of_le (Nat.lt_succ_self d) hL_ge
    have hbd1 : 1 <= b - d := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hbd)
    have hgap : d < (b - d) * L n := by
      have hmul_ge : L n <= (b - d) * L n := by
        calc
          L n = 1 * L n := by simp
          _ <= (b - d) * L n := Nat.mul_le_mul_right (L n) hbd1
      exact lt_of_lt_of_le hdLtL hmul_ge
    have hsum :
        d * L n + d < d * L n + (b - d) * L n :=
      Nat.add_lt_add_left hgap (d * L n)
    have hleft : d * (L n + 1) = d * L n + d := by
      simp [Nat.mul_add, Nat.add_comm]
    have hright : d * L n + (b - d) * L n = b * L n := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hbd)]
    exact hleft ▸ (lt_of_lt_of_eq hsum hright)
  exact lt_of_le_of_lt hmulB hltDL

/-- Concrete corollary used as a default large-prime density bound. -/
lemma G3_density_two_one : G3_density 2 1 := G3_density_of_lt (by decide)

/--
Any density pair with strict chain `d < b < a` is inconsistent with the `S1` side.
-/
lemma not_density_pair_of_lt_lt {a b d : Nat}
    (hdb : d < b) (hba : b < a) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  exact not_S1_density_of_lt (lt_trans hdb hba) h.1

lemma density_pair_implies_b_le_d {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (hG3 : G3_density b d) :
    b <= d := by
  by_cases hbd : b <= d
  · exact hbd
  · have hdb : d < b := lt_of_not_ge hbd
    exact False.elim ((not_density_pair_of_lt_lt hdb hba) ⟨hS1, hG3⟩)

lemma density_pair_implies_chain {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    b < a ∧ a < d := by
  refine ⟨hba, ?_⟩
  have ha : 0 < a := lt_of_le_of_lt (Nat.zero_le b) hba
  exact S1_density_implies_a_lt_d_of_pos ha hS1

lemma density_pair_implies_b_lt_d {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (hG3 : G3_density b d) :
    b < d := lt_trans hba (density_pair_implies_chain hba hS1 hG3).2

lemma density_pair_implies_scaled_gap {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    60 * b < 47 * d := by
  have hb60 : 60 * b < 60 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 60)
  exact lt_of_lt_of_le hb60 (S1_density_implies_sixty_mul_a_le_fortyseven_mul_d hS1)

lemma density_pair_implies_scaled_gap420 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    420 * b < 319 * d := by
  have hb420 : 420 * b < 420 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 420)
  exact lt_of_lt_of_le hb420 (S1_density_implies_fourtwenty_mul_a_le_threeonenine_mul_d hS1)

lemma density_pair_implies_scaled_gap4620 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    4620 * b < 3467 * d := by
  have hb4620 : 4620 * b < 4620 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 4620)
  exact lt_of_lt_of_le hb4620 (S1_density_implies_4620_mul_a_le_3467_mul_d hS1)

lemma density_pair_implies_scaled_gap60060 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    60060 * b < 44686 * d := by
  have hb60060 : 60060 * b < 60060 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 60060)
  exact lt_of_lt_of_le hb60060 (S1_density_implies_60060_mul_a_le_44686_mul_d hS1)

lemma density_pair_implies_scaled_gap2462460 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    2462460 * b < 1829123 * d := by
  have hb2462460 : 2462460 * b < 2462460 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 2462460)
  exact lt_of_lt_of_le hb2462460 (S1_density_implies_2462460_mul_a_le_1829123_mul_d hS1)

lemma density_pair_implies_scaled_gap273333060 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    273333060 * b < 202827448 * d := by
  have hb273333060 : 273333060 * b < 273333060 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 273333060)
  exact lt_of_lt_of_le hb273333060 (S1_density_implies_273333060_mul_a_le_202827448_mul_d hS1)

lemma density_pair_implies_scaled_gap16673316660 {a b d : Nat}
    (hba : b < a) (hS1 : S1_density a d) (_hG3 : G3_density b d) :
    16673316660 * b < 12367918777 * d := by
  have hb16673316660 : 16673316660 * b < 16673316660 * a := Nat.mul_lt_mul_of_pos_left hba (by decide : 0 < 16673316660)
  exact lt_of_lt_of_le hb16673316660 (S1_density_implies_16673316660_mul_a_le_12367918777_mul_d hS1)

lemma not_density_pair_of_d_le_b {a b d : Nat}
    (hba : b < a) (hdb : d <= b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hbd : b < d := density_pair_implies_b_lt_d hba h.1 h.2
  exact Nat.not_le_of_gt hbd hdb

lemma not_density_pair_of_scaled_le {a b d : Nat}
    (hba : b < a) (hscaled : 47 * d <= 60 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 60 * b < 47 * d := density_pair_implies_scaled_gap hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled420_le {a b d : Nat}
    (hba : b < a) (hscaled : 319 * d <= 420 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 420 * b < 319 * d := density_pair_implies_scaled_gap420 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled4620_le {a b d : Nat}
    (hba : b < a) (hscaled : 3467 * d <= 4620 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 4620 * b < 3467 * d := density_pair_implies_scaled_gap4620 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled60060_le {a b d : Nat}
    (hba : b < a) (hscaled : 44686 * d <= 60060 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 60060 * b < 44686 * d := density_pair_implies_scaled_gap60060 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled2462460_le {a b d : Nat}
    (hba : b < a) (hscaled : 1829123 * d <= 2462460 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 2462460 * b < 1829123 * d := density_pair_implies_scaled_gap2462460 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled273333060_le {a b d : Nat}
    (hba : b < a) (hscaled : 202827448 * d <= 273333060 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 273333060 * b < 202827448 * d := density_pair_implies_scaled_gap273333060 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_of_scaled16673316660_le {a b d : Nat}
    (hba : b < a) (hscaled : 12367918777 * d <= 16673316660 * b) :
    ¬ (S1_density a d ∧ G3_density b d) := by
  intro h
  have hgap : 16673316660 * b < 12367918777 * d := density_pair_implies_scaled_gap16673316660 hba h.1 h.2
  exact Nat.not_le_of_gt hgap hscaled

lemma not_density_pair_pointwise_of_not_represents {a b d n : Nat}
    (hba : b < a)
    (hLpos : 0 < L n)
    (hNotRep : ¬ Represents n)
    (hA : a * L n <= d * (A n (z n)).card)
    (hB : d * (B n (z n)).card < b * L n) :
    False := by
  have hAleB : (A n (z n)).card <= (B n (z n)).card :=
    card_A_le_card_B_of_not_represents (z0 := z n) hNotRep
  have hAB : a * L n <= d * (B n (z n)).card := by
    exact le_trans hA (Nat.mul_le_mul_left d hAleB)
  have hltAB : a * L n < b * L n := lt_of_le_of_lt hAB hB
  have hltBA : b * L n < a * L n := Nat.mul_lt_mul_of_pos_right hba hLpos
  exact (lt_asymm hltBA hltAB)

lemma not_density_pair_of_unbounded_odd_counterexamples {a b d : Nat}
    (hba : b < a)
    (hS1 : S1_density a d)
    (hG3 : G3_density b d)
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N <= n ∧ Odd n ∧ ¬ Represents n) :
    False := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hG3 with ⟨N2, hG3'⟩
  let N : Nat := max (max N1 N2) 3
  rcases hUnbounded N with ⟨n, hnN, hodd, hNotRep⟩
  have hn1 : N1 <= n := le_trans (le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 3)) hnN
  have hn2 : N2 <= n := le_trans (le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 3)) hnN
  have hn3 : 3 <= n := le_trans (le_max_right (max N1 N2) 3) hnN
  have hLpos : 0 < L n := by
    unfold L
    have h2n : 2 <= n := by omega
    exact Nat.log_pos Nat.one_lt_two h2n
  have hA : a * L n <= d * (A n (z n)).card := hS1' n hn1 hodd
  have hB : d * (B n (z n)).card < b * L n := hG3' n hn2 hodd
  exact not_density_pair_pointwise_of_not_represents hba hLpos hNotRep hA hB

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

/--
Clean large-prime contradiction target:
eventually, the clean set `A n (z n)` is covered by fewer than `L n` clean
large-prime square classes after collapsing the non-Wieferich part to support
cardinality and retaining only clean Wieferich excess.
-/
def A_cleanSupportSq_bound_eventually_wieferichExcess : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeCleanSupportSq n).card +
      Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) < L n

/-- Slackened clean large-prime contradiction target. -/
def A_cleanSupportSq_bound_eventually_wieferichExcess_slack (C : Nat) : Prop :=
  exists N : Nat, forall n : Nat, N <= n -> Odd n ->
    (largePrimeCleanSupportSq n).card +
      Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) <
        L n - C

/--
Direct clean contradiction route:
combine the small-prime sieve lower bound on `A` with the clean large-prime upper
bound under `¬ Represents`.
-/
lemma T0_erdos11_from_clean_support_sq_bound
    (hS1 : S1_small_prime_sieve)
    (hClean : A_cleanSupportSq_bound_eventually_wieferichExcess) :
    Erdos11Conjecture := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hClean with ⟨N2, hClean'⟩
  refine ⟨max (max N1 N2) 64, ?_⟩
  intro n hn hodd
  have hn12 : max N1 N2 <= n := le_trans (le_max_left (max N1 N2) 64) hn
  have hn1 : N1 <= n := le_trans (le_max_left N1 N2) hn12
  have hn2 : N2 <= n := le_trans (le_max_right N1 N2) hn12
  have hn64 : 64 <= n := le_trans (le_max_right (max N1 N2) 64) hn
  by_contra hNotRep
  have hA : L n <= (A n (z n)).card := hS1' n hn1 hodd
  have hz3 : 3 <= z n := three_le_z_of_sixtyfour_le hn64
  have hUpper :
      (A n (z n)).card <=
        (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
    exact A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_excess_of_not_represents hNotRep hz3
  have hCleanLt :
      (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) <
        L n := hClean' n hn2 hodd
  exact (Nat.not_lt_of_ge hA) (lt_of_le_of_lt hUpper hCleanLt)

lemma T0_erdos11_from_clean_support_sq_bound_slack {C : Nat}
    (hS1 : S1_small_prime_sieve_slack C)
    (hClean : A_cleanSupportSq_bound_eventually_wieferichExcess_slack C) :
    Erdos11Conjecture := by
  rcases hS1 with ⟨N1, hS1'⟩
  rcases hClean with ⟨N2, hClean'⟩
  refine ⟨max (max N1 N2) 64, ?_⟩
  intro n hn hodd
  have hn12 : max N1 N2 <= n := le_trans (le_max_left (max N1 N2) 64) hn
  have hn1 : N1 <= n := le_trans (le_max_left N1 N2) hn12
  have hn2 : N2 <= n := le_trans (le_max_right N1 N2) hn12
  have hn64 : 64 <= n := le_trans (le_max_right (max N1 N2) 64) hn
  by_contra hNotRep
  have hA : L n - C <= (A n (z n)).card := hS1' n hn1 hodd
  have hz3 : 3 <= z n := three_le_z_of_sixtyfour_le hn64
  have hUpper :
      (A n (z n)).card <=
        (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) := by
    exact A_large_prime_decomp_sq_cleanSupport_card_add_wieferich_excess_of_not_represents hNotRep hz3
  have hCleanLt :
      (largePrimeCleanSupportSq n).card +
          Finset.sum (wieferichLargePrimeCleanSupportSq n) (fun p => cleanNp n (z n) p - 1) <
        L n - C := hClean' n hn2 hodd
  exact (Nat.not_lt_of_ge hA) (lt_of_le_of_lt hUpper hCleanLt)

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

lemma not_MatchedSumBounds : ¬ MatchedSumBounds := by
  intro h
  rcases h with ⟨C, hS1, _hG3⟩
  have hS1' : S1_small_prime_sieve_slack C := S1_of_small_prime_sum_bound_eventually_slack hS1
  exact not_S1_small_prime_sieve_slack C hS1'

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

lemma not_MatchedUniformBounds : ¬ MatchedUniformBounds := by
  intro h
  rcases h with ⟨Csmall, Clarge, C, hS1, _hG3⟩
  have hS1' : S1_small_prime_sieve_slack C := S1_of_uniform_local_bound_eventually_slack hS1
  exact not_S1_small_prime_sieve_slack C hS1'

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

lemma not_MatchedDensityBounds_of_not_Erdos11Conjecture
    (hNot : ¬ Erdos11Conjecture) : ¬ MatchedDensityBounds := by
  intro h
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  have hUnbounded :
      ∀ N : Nat, ∃ n : Nat, N <= n ∧ Odd n ∧ ¬ Represents n :=
    not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot
  exact not_density_pair_of_unbounded_odd_counterexamples hba hS1 hG3 hUnbounded

/--
Strict density target requiring a full chain `d < b < a`.
This is incompatible with `S1_density` by the modular barrier.
-/
def MatchedDensityBoundsStrict : Prop :=
  exists a b d : Nat, d < b /\ b < a /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsStrict : ¬ MatchedDensityBoundsStrict := by
  intro h
  rcases h with ⟨a, b, d, hdb, hba, hS1, hG3⟩
  exact (not_density_pair_of_lt_lt hdb hba) ⟨hS1, hG3⟩

/--
Nonexpansive density target:
in addition to `b < a`, require `d <= b`.
This is inconsistent with the S1-side barrier.
-/
def MatchedDensityBoundsNonexpansive : Prop :=
  exists a b d : Nat, b < a /\ d <= b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsNonexpansive : ¬ MatchedDensityBoundsNonexpansive := by
  intro h
  rcases h with ⟨a, b, d, hba, hdb, hS1, hG3⟩
  exact (not_density_pair_of_d_le_b hba hdb) ⟨hS1, hG3⟩

/--
Quantitative constrained density target:
in addition to `b < a`, require `47*d <= 60*b`.
This is incompatible with the S1-side modular barrier.
-/
def MatchedDensityBoundsScaled : Prop :=
  exists a b d : Nat, b < a /\ 47 * d <= 60 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled : ¬ MatchedDensityBoundsScaled := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled_le hba hscaled) ⟨hS1, hG3⟩

/--
Stronger quantitative constrained density target:
in addition to `b < a`, require `319*d <= 420*b`.
This is incompatible with the strengthened S1-side modular barrier.
-/
def MatchedDensityBoundsScaled420 : Prop :=
  exists a b d : Nat, b < a /\ 319 * d <= 420 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled420 : ¬ MatchedDensityBoundsScaled420 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled420_le hba hscaled) ⟨hS1, hG3⟩

/--
Further strengthened quantitative constrained density target:
in addition to `b < a`, require `3467*d <= 4620*b`.
This is incompatible with the strengthened S1-side modular barrier.
-/
def MatchedDensityBoundsScaled4620 : Prop :=
  exists a b d : Nat, b < a /\ 3467 * d <= 4620 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled4620 : ¬ MatchedDensityBoundsScaled4620 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled4620_le hba hscaled) ⟨hS1, hG3⟩

/--
Even stronger quantitative constrained density target:
in addition to `b < a`, require `44686*d <= 60060*b`.
This is incompatible with the strongest S1-side modular barrier in this file.
-/
def MatchedDensityBoundsScaled60060 : Prop :=
  exists a b d : Nat, b < a /\ 44686 * d <= 60060 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled60060 : ¬ MatchedDensityBoundsScaled60060 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled60060_le hba hscaled) ⟨hS1, hG3⟩

/--
Next strengthened constrained density target:
in addition to `b < a`, require `1829123*d <= 2462460*b`.
This is incompatible with the strengthened S1-side modular barrier.
-/
def MatchedDensityBoundsScaled2462460 : Prop :=
  exists a b d : Nat, b < a /\ 1829123 * d <= 2462460 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled2462460 : ¬ MatchedDensityBoundsScaled2462460 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled2462460_le hba hscaled) ⟨hS1, hG3⟩

def MatchedDensityBoundsScaled273333060 : Prop :=
  exists a b d : Nat, b < a /\ 202827448 * d <= 273333060 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled273333060 : ¬ MatchedDensityBoundsScaled273333060 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled273333060_le hba hscaled) ⟨hS1, hG3⟩

def MatchedDensityBoundsScaled16673316660 : Prop :=
  exists a b d : Nat, b < a /\ 12367918777 * d <= 16673316660 * b /\ S1_density a d /\ G3_density b d

lemma not_MatchedDensityBoundsScaled16673316660 : ¬ MatchedDensityBoundsScaled16673316660 := by
  intro h
  rcases h with ⟨a, b, d, hba, hscaled, hS1, hG3⟩
  exact (not_density_pair_of_scaled16673316660_le hba hscaled) ⟨hS1, hG3⟩

lemma not_MatchedDensityBoundsScaled16673316660_of_not_Erdos11Conjecture
    (hNot : ¬ Erdos11Conjecture) : ¬ MatchedDensityBoundsScaled16673316660 := by
  intro hScaled
  apply (not_MatchedDensityBounds_of_not_Erdos11Conjecture hNot)
  rcases hScaled with ⟨a, b, d, hba, _hscaled, hS1, hG3⟩
  exact ⟨a, b, d, hba, hS1, hG3⟩

lemma matchedDensityBounds_implies_a_le_d (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ a <= d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, S1_density_implies_a_le_d hS1, hS1, hG3⟩

lemma matchedDensityBounds_implies_b_le_d (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ b <= d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_b_le_d hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_chain (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ a < d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, (density_pair_implies_chain hba hS1 hG3).2, hS1, hG3⟩

lemma matchedDensityBounds_implies_b_lt_d (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ b < d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_b_lt_d hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 60 * b < 47 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap420 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 420 * b < 319 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap420 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap4620 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 4620 * b < 3467 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap4620 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap60060 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 60060 * b < 44686 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap60060 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap2462460 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 2462460 * b < 1829123 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap2462460 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap273333060 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 273333060 * b < 202827448 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap273333060 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_scaled_gap16673316660 (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ 16673316660 * b < 12367918777 * d /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  exact ⟨a, b, d, hba, density_pair_implies_scaled_gap16673316660 hba hS1 hG3, hS1, hG3⟩

lemma matchedDensityBounds_implies_not_nonexpansive (h : MatchedDensityBounds) :
    exists a b d : Nat, b < a /\ ¬ d <= b /\ S1_density a d /\ G3_density b d := by
  rcases h with ⟨a, b, d, hba, hS1, hG3⟩
  have hbd : b < d := density_pair_implies_b_lt_d hba hS1 hG3
  exact ⟨a, b, d, hba, Nat.not_le_of_gt hbd, hS1, hG3⟩

lemma T0_of_matched_density_bounds (h : MatchedDensityBounds) :
    Erdos11Conjecture := by
  rcases h with ⟨a, b, d, hab, hS1, hG3⟩
  exact T0_erdos11_from_density_assumptions hab hS1 hG3

end AsymptoticGraph

/--
Main conditional asymptotic statement provided by this file:
if matched density bounds hold, then Erdős #11 holds asymptotically.
-/
lemma erdos11_conditional_asymptotic
    (h : AsymptoticGraph.MatchedDensityBounds) : Erdos11Conjecture := by
  exact AsymptoticGraph.T0_of_matched_density_bounds h

/--
Equivalent expanded form of the conditional asymptotic route.
-/
lemma erdos11_conditional_asymptotic_explicit {a b d : Nat}
    (hab : b < a)
    (hS1 : AsymptoticGraph.S1_density a d)
    (hG3 : AsymptoticGraph.G3_density b d) :
    Erdos11Conjecture := by
  exact AsymptoticGraph.T0_erdos11_from_density_assumptions hab hS1 hG3

/--
Bridge-closure principle:
if every global counterexample profile forces the scaled matched-density target,
then Erdős #11 follows unconditionally.
-/
lemma erdos11_of_counterexample_bridge16673316660
    (hBridge : ¬ Erdos11Conjecture →
      AsymptoticGraph.MatchedDensityBoundsScaled16673316660) :
    Erdos11Conjecture := by
  by_contra hNot
  exact AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660 (hBridge hNot)

/--
Equivalent bridge form phrased via unbounded odd counterexamples.
-/
lemma erdos11_of_unbounded_counterexample_bridge16673316660
    (hBridge :
      (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) →
        AsymptoticGraph.MatchedDensityBoundsScaled16673316660) :
    Erdos11Conjecture := by
  apply erdos11_of_counterexample_bridge16673316660
  intro hNot
  exact hBridge (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot)

/--
Named remaining extraction target:
unbounded odd counterexamples force the scaled matched-density profile.
-/
def CounterexampleBridge16673316660 : Prop :=
  (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) →
    AsymptoticGraph.MatchedDensityBoundsScaled16673316660

/--
Equivalent bridge form phrased directly from `¬Erdos11Conjecture`.
-/
def CounterexampleBridgeNeg16673316660 : Prop :=
  ¬ Erdos11Conjecture → AsymptoticGraph.MatchedDensityBoundsScaled16673316660

lemma counterexampleBridge16673316660_iff_not_unbounded_odd_counterexamples :
    CounterexampleBridge16673316660 ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact force_false_target_iff_not_unbounded_odd_counterexamples
    AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660

lemma counterexampleBridge16673316660_of_erdos11
    (hE : Erdos11Conjecture) :
    CounterexampleBridge16673316660 := by
  exact unbounded_counterexamples_elim_of_erdos11 hE

lemma counterexampleBridgeNeg16673316660_of_erdos11
    (hE : Erdos11Conjecture) :
    CounterexampleBridgeNeg16673316660 := by
  exact not_erdos11_elim_of_erdos11 hE

/--
Generic split-margin hypothesis:
both bad components carry a shared positive margin `Δ`, with coefficients summing to `d`.
-/
def SplitMargin (d cSmall cLarge : Nat) : Prop :=
  ∃ Δ N0 : Nat, 0 < Δ ∧
    ∀ n : Nat, N0 ≤ n → Odd n →
      d * (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card +
          Δ * AsymptoticGraph.L n <=
        cSmall * AsymptoticGraph.L n ∧
      d * (AsymptoticGraph.B n (AsymptoticGraph.z n)).card +
          Δ * AsymptoticGraph.L n <=
        cLarge * AsymptoticGraph.L n

/--
Analytic split package (step-1 target):
for a fixed positive margin `Δ`, eventually both bad parts are bounded with strict
headroom whose coefficients sum to `16673316660`.
-/
def AsymptoticSplitMargin16673316660 : Prop :=
  SplitMargin 16673316660 4305397883 12367918777

/--
Focused step-1 extraction target:
unbounded odd counterexamples force the analytic split package.
-/
def UnboundedForcesAsymptoticSplitMargin16673316660 : Prop :=
  (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) →
    AsymptoticSplitMargin16673316660

lemma unboundedForcesAsymptoticSplitMargin16673316660_of_erdos11
    (hE : Erdos11Conjecture) :
    UnboundedForcesAsymptoticSplitMargin16673316660 := by
  exact unbounded_counterexamples_elim_of_erdos11 hE

lemma matchedDensityBoundsScaled16673316660_of_asymptotic_split_margin16673316660
    (hSplit : AsymptoticSplitMargin16673316660) :
    AsymptoticGraph.MatchedDensityBoundsScaled16673316660 := by
  rcases hSplit with ⟨Δ, N0, hΔ, hSplitN⟩
  let N : Nat := max N0 3
  refine ⟨12367918778, 12367918777, 16673316660, by decide, ?_, ?_, ?_⟩
  · simpa [Nat.mul_comm]
  · refine ⟨N, ?_⟩
    intro n hn hodd
    let Ln : Nat := AsymptoticGraph.L n
    let S : Nat := (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card
    let Kc : Nat := (AsymptoticGraph.K n).card
    have hN0 : N0 ≤ n := le_trans (le_max_left N0 3) hn
    rcases hSplitN n hN0 hodd with ⟨hSmallRaw, _⟩
    have hSmall : 16673316660 * S + Δ * Ln <= 4305397883 * Ln := by
      simpa [S, Ln] using hSmallRaw
    have hDelta_ge_one : 1 <= Δ := Nat.succ_le_of_lt hΔ
    have hL_le_deltaL : Ln <= Δ * Ln := by
      simpa [one_mul] using (Nat.mul_le_mul_right Ln hDelta_ge_one)
    have hL_le_K : Ln <= Kc := by
      simpa [Ln, Kc] using AsymptoticGraph.L_le_card_K_of_pos hodd.pos
    have hLift :
        12367918778 * Ln + 16673316660 * S <=
          12367918777 * Ln + (16673316660 * S + Δ * Ln) := by
      have hLstep : 12367918778 * Ln <= 12367918777 * Ln + Δ * Ln := by
        have hEq : 12367918778 * Ln = 12367918777 * Ln + Ln := by omega
        calc
          12367918778 * Ln = 12367918777 * Ln + Ln := hEq
          _ <= 12367918777 * Ln + Δ * Ln := Nat.add_le_add_left hL_le_deltaL (12367918777 * Ln)
      have hAdd :
          12367918778 * Ln + 16673316660 * S <=
            (12367918777 * Ln + Δ * Ln) + 16673316660 * S :=
        Nat.add_le_add_right hLstep (16673316660 * S)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAdd
    have hRightBound :
        12367918777 * Ln + (16673316660 * S + Δ * Ln) <= 16673316660 * Ln := by
      have hSmall' :
          12367918777 * Ln + (16673316660 * S + Δ * Ln) <=
            12367918777 * Ln + 4305397883 * Ln :=
        Nat.add_le_add_left hSmall (12367918777 * Ln)
      have hRight :
          12367918777 * Ln + 4305397883 * Ln = 16673316660 * Ln := by
        calc
          12367918777 * Ln + 4305397883 * Ln = (12367918777 + 4305397883) * Ln := by
            rw [Nat.add_mul]
          _ = 16673316660 * Ln := by norm_num
      simpa [hRight] using hSmall'
    have hMain :
        12367918778 * Ln + 16673316660 * S <= 16673316660 * Kc := by
      exact le_trans (le_trans hLift hRightBound) (Nat.mul_le_mul_left 16673316660 hL_le_K)
    have hSub :
        12367918778 * Ln <= 16673316660 * Kc - 16673316660 * S := by
      exact Nat.le_sub_of_add_le hMain
    have hAeq :
        (AsymptoticGraph.A n (AsymptoticGraph.z n)).card = Kc - S := by
      simpa [Kc, S] using AsymptoticGraph.card_A_eq_card_K_sub_smallPrimeBad n (AsymptoticGraph.z n)
    calc
      12367918778 * AsymptoticGraph.L n = 12367918778 * Ln := by rfl
      _ <= 16673316660 * Kc - 16673316660 * S := hSub
      _ = 16673316660 * (Kc - S) := by
        symm
        exact Nat.mul_sub_left_distrib 16673316660 Kc S
      _ = 16673316660 * (AsymptoticGraph.A n (AsymptoticGraph.z n)).card := by
        simp [hAeq]
  · refine ⟨N, ?_⟩
    intro n hn hodd
    let Ln : Nat := AsymptoticGraph.L n
    let B0 : Nat := (AsymptoticGraph.B n (AsymptoticGraph.z n)).card
    have hN0 : N0 <= n := le_trans (le_max_left N0 3) hn
    rcases hSplitN n hN0 hodd with ⟨_, hLargeRaw⟩
    have hLarge : 16673316660 * B0 + Δ * Ln <= 12367918777 * Ln := by
      simpa [B0, Ln] using hLargeRaw
    have h2n : 2 <= n := by omega
    have hLpos : 0 < Ln := by
      unfold Ln AsymptoticGraph.L
      exact Nat.log_pos Nat.one_lt_two h2n
    have hDeltaLnPos : 0 < Δ * Ln := Nat.mul_pos hΔ hLpos
    calc
      16673316660 * (AsymptoticGraph.B n (AsymptoticGraph.z n)).card = 16673316660 * B0 := by rfl
      _ < 16673316660 * B0 + Δ * Ln := Nat.lt_add_of_pos_right hDeltaLnPos
      _ <= 12367918777 * Ln := hLarge
      _ = 12367918777 * AsymptoticGraph.L n := by rfl

lemma not_AsymptoticSplitMargin16673316660 : ¬ AsymptoticSplitMargin16673316660 := by
  intro hSplit
  exact AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660
    (matchedDensityBoundsScaled16673316660_of_asymptotic_split_margin16673316660 hSplit)

/--
Generic step-2 contradiction:
if small/large bad parts are both eventually bounded with a shared positive margin
and coefficients summing to `d`, unbounded odd counterexamples are impossible.
-/
lemma not_unbounded_odd_counterexamples_of_split_margin
    {d cSmall cLarge : Nat}
    (hSum : cSmall + cLarge = d)
    (hSplit : SplitMargin d cSmall cLarge) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  intro hUnbounded
  rcases hSplit with ⟨Δ, N0, hΔ, hSplitN⟩
  let N : Nat := max N0 3
  rcases hUnbounded N with ⟨n, hnN, hodd, hNotRep⟩
  let S : Nat := (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card
  let B0 : Nat := (AsymptoticGraph.B n (AsymptoticGraph.z n)).card
  let Kc : Nat := (AsymptoticGraph.K n).card
  let Ln : Nat := AsymptoticGraph.L n
  have hn0 : 0 < n := hodd.pos
  have hLpos : 0 < Ln := by
    unfold Ln AsymptoticGraph.L
    have h2n : 2 <= n := by omega
    exact Nat.log_pos Nat.one_lt_two h2n
  have hn0' : N0 <= n := le_trans (le_max_left N0 3) hnN
  rcases hSplitN n hn0' hodd with ⟨hSmallRaw, hLargeRaw⟩
  have hSmall : d * S + Δ * Ln <= cSmall * Ln := by
    simpa [S, Ln] using hSmallRaw
  have hLarge : d * B0 + Δ * Ln <= cLarge * Ln := by
    simpa [B0, Ln] using hLargeRaw
  have hK_le_SB :
      Kc <= S + B0 := by
    simpa [Kc, S, B0] using
      (AsymptoticGraph.card_K_le_smallPrimeBad_add_B_of_not_represents (n := n) hNotRep)
  have hL_le_K : Ln <= Kc := by
    simpa [Ln, Kc] using AsymptoticGraph.L_le_card_K_of_pos hn0
  have hL_le_SB : Ln <= S + B0 := le_trans hL_le_K hK_le_SB
  have hScaled : d * Ln <= d * (S + B0) := Nat.mul_le_mul_left d hL_le_SB
  have hUpper :
      d * (S + B0) + (Δ * Ln + Δ * Ln) <= d * Ln := by
    have hLeft :
        (d * S + Δ * Ln) + (d * B0 + Δ * Ln) =
          d * (S + B0) + (Δ * Ln + Δ * Ln) := by
      calc
        (d * S + Δ * Ln) + (d * B0 + Δ * Ln) =
            (d * S + d * B0) + (Δ * Ln + Δ * Ln) := by ac_rfl
        _ = d * (S + B0) + (Δ * Ln + Δ * Ln) := by
            rw [← Nat.mul_add]
    have hRight : cSmall * Ln + cLarge * Ln = d * Ln := by
      calc
        cSmall * Ln + cLarge * Ln = (cSmall + cLarge) * Ln := by
          rw [Nat.add_mul]
        _ = d * Ln := by simpa [hSum]
    calc
      d * (S + B0) + (Δ * Ln + Δ * Ln) =
          (d * S + Δ * Ln) + (d * B0 + Δ * Ln) := by
            symm
            exact hLeft
      _ <= cSmall * Ln + cLarge * Ln := Nat.add_le_add hSmall hLarge
      _ = d * Ln := hRight
  have hStrict :
      d * (S + B0) <
        d * (S + B0) + (Δ * Ln + Δ * Ln) := by
    have hPos : 0 < Δ * Ln + Δ * Ln := by
      have hDeltaLnPos : 0 < Δ * Ln := Nat.mul_pos hΔ hLpos
      omega
    exact Nat.lt_add_of_pos_right hPos
  have hlt : d * Ln < d * Ln := by
    exact lt_of_le_of_lt hScaled (lt_of_lt_of_le hStrict hUpper)
  exact (Nat.lt_irrefl _ hlt)

lemma not_splitMargin_of_unbounded_odd_counterexamples
    {d cSmall cLarge : Nat}
    (hSum : cSmall + cLarge = d)
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) :
    ¬ SplitMargin d cSmall cLarge := by
  intro hSplit
  exact (not_unbounded_odd_counterexamples_of_split_margin hSum hSplit) hUnbounded

lemma erdos11_of_not_unbounded_odd_counterexamples
    (hNo :
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n)) :
    Erdos11Conjecture := by
  by_contra hNot
  exact hNo (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot)

lemma erdos11_iff_not_unbounded_odd_counterexamples :
    Erdos11Conjecture ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  constructor
  · intro hE hUnbounded
    have hNot : ¬ Erdos11Conjecture :=
      not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mpr hUnbounded
    exact hNot hE
  · intro hNo
    exact erdos11_of_not_unbounded_odd_counterexamples hNo

/--
Master conditional theorem:
any split-margin package with coefficient sum `d` yields Erdős #11.
-/
lemma erdos11_of_split_margin
    {d cSmall cLarge : Nat}
    (hSum : cSmall + cLarge = d)
    (hSplit : SplitMargin d cSmall cLarge) :
    Erdos11Conjecture := by
  exact erdos11_of_not_unbounded_odd_counterexamples
    (not_unbounded_odd_counterexamples_of_split_margin hSum hSplit)

/--
Step-2 contradiction: the split-margin package rules out unbounded odd counterexamples.
-/
lemma not_unbounded_odd_counterexamples_of_asymptotic_split_margin16673316660
    (hSplit : AsymptoticSplitMargin16673316660) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact not_unbounded_odd_counterexamples_of_split_margin
    (d := 16673316660) (cSmall := 4305397883) (cLarge := 12367918777)
    (by norm_num) hSplit

lemma not_asymptotic_split_margin16673316660_of_unbounded_odd_counterexamples
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) :
    ¬ AsymptoticSplitMargin16673316660 := by
  exact not_splitMargin_of_unbounded_odd_counterexamples
    (d := 16673316660) (cSmall := 4305397883) (cLarge := 12367918777)
    (by norm_num) hUnbounded

lemma unboundedForcesAsymptoticSplitMargin16673316660_iff_not_unbounded_odd_counterexamples :
    UnboundedForcesAsymptoticSplitMargin16673316660 ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact force_false_target_iff_not_unbounded_odd_counterexamples
    not_AsymptoticSplitMargin16673316660

/--
Bridge theorem from the analytic split package.
-/
lemma counterexampleBridge16673316660_of_asymptotic_split_margin16673316660
    (hSplit : AsymptoticSplitMargin16673316660) :
    CounterexampleBridge16673316660 := by
  intro hUnbounded
  exact False.elim
    ((not_unbounded_odd_counterexamples_of_asymptotic_split_margin16673316660 hSplit) hUnbounded)

lemma counterexampleBridge16673316660_of_unbounded_forces_asymptotic_split_margin16673316660
    (hStep1 : UnboundedForcesAsymptoticSplitMargin16673316660) :
    CounterexampleBridge16673316660 := by
  intro hUnbounded
  exact matchedDensityBoundsScaled16673316660_of_asymptotic_split_margin16673316660
    (hStep1 hUnbounded)

lemma erdos11_of_unbounded_forces_asymptotic_split_margin16673316660
    (hStep1 : UnboundedForcesAsymptoticSplitMargin16673316660) :
    Erdos11Conjecture := by
  exact erdos11_of_unbounded_counterexample_bridge16673316660
    (counterexampleBridge16673316660_of_unbounded_forces_asymptotic_split_margin16673316660 hStep1)

lemma counterexampleBridge16673316660_iff_unboundedForcesAsymptoticSplitMargin16673316660 :
    CounterexampleBridge16673316660 ↔
      UnboundedForcesAsymptoticSplitMargin16673316660 := by
  exact force_false_targets_iff
    AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660
    not_AsymptoticSplitMargin16673316660

lemma erdos11_iff_unboundedForcesAsymptoticSplitMargin16673316660 :
    Erdos11Conjecture ↔ UnboundedForcesAsymptoticSplitMargin16673316660 := by
  exact (force_false_target_iff_erdos11 not_AsymptoticSplitMargin16673316660).symm

/--
Unconditional closure from the analytic split package.
-/
lemma erdos11_of_asymptotic_split_margin16673316660
    (hSplit : AsymptoticSplitMargin16673316660) :
    Erdos11Conjecture := by
  exact erdos11_of_split_margin (d := 16673316660) (cSmall := 4305397883) (cLarge := 12367918777)
    (by norm_num) hSplit

/--
Alternative split package with a one-tick shifted coefficient split.
This keeps the same total `16673316660` while avoiding the exact threshold lock.
-/
def AsymptoticSplitMargin16673316660Safe : Prop :=
  SplitMargin 16673316660 4305397884 12367918776

def UnboundedForcesAsymptoticSplitMargin16673316660Safe : Prop :=
  (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) →
    AsymptoticSplitMargin16673316660Safe

lemma not_unbounded_odd_counterexamples_of_asymptotic_split_margin16673316660Safe
    (hSplit : AsymptoticSplitMargin16673316660Safe) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact not_unbounded_odd_counterexamples_of_split_margin
    (d := 16673316660) (cSmall := 4305397884) (cLarge := 12367918776)
    (by norm_num) hSplit

lemma not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) :
    ¬ AsymptoticSplitMargin16673316660Safe := by
  exact not_splitMargin_of_unbounded_odd_counterexamples
    (d := 16673316660) (cSmall := 4305397884) (cLarge := 12367918776)
    (by norm_num) hUnbounded

lemma unboundedForcesAsymptoticSplitMargin16673316660Safe_of_erdos11
    (hE : Erdos11Conjecture) :
    UnboundedForcesAsymptoticSplitMargin16673316660Safe := by
  exact unbounded_counterexamples_elim_of_erdos11 hE

lemma unboundedForcesAsymptoticSplitMargin16673316660Safe_iff_not_unbounded_odd_counterexamples :
    UnboundedForcesAsymptoticSplitMargin16673316660Safe ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact force_target_iff_not_unbounded_odd_counterexamples_of_not_target_of_unbounded
    not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples

lemma erdos11_of_unbounded_forces_asymptotic_split_margin16673316660Safe
    (hStep1 : UnboundedForcesAsymptoticSplitMargin16673316660Safe) :
    Erdos11Conjecture := by
  exact (force_target_iff_erdos11_of_not_target_of_unbounded
    not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples).mp hStep1

lemma erdos11_iff_unboundedForcesAsymptoticSplitMargin16673316660Safe :
    Erdos11Conjecture ↔ UnboundedForcesAsymptoticSplitMargin16673316660Safe := by
  exact (force_target_iff_erdos11_of_not_target_of_unbounded
    not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples).symm

lemma unboundedForcesAsymptoticSplitMargin16673316660_iff_safe :
    UnboundedForcesAsymptoticSplitMargin16673316660 ↔
      UnboundedForcesAsymptoticSplitMargin16673316660Safe := by
  exact force_targets_iff_of_not_targets_of_unbounded
    not_asymptotic_split_margin16673316660_of_unbounded_odd_counterexamples
    not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples

lemma counterexampleBridge16673316660_iff_unboundedForcesAsymptoticSplitMargin16673316660Safe :
    CounterexampleBridge16673316660 ↔
      UnboundedForcesAsymptoticSplitMargin16673316660Safe := by
  rw [counterexampleBridge16673316660_iff_unboundedForcesAsymptoticSplitMargin16673316660,
    unboundedForcesAsymptoticSplitMargin16673316660_iff_safe]

lemma erdos11_of_asymptotic_split_margin16673316660Safe
    (hSplit : AsymptoticSplitMargin16673316660Safe) :
    Erdos11Conjecture := by
  exact erdos11_of_split_margin (d := 16673316660) (cSmall := 4305397884) (cLarge := 12367918776)
    (by norm_num) hSplit

/--
Clean split-margin target:
the small-prime bad set and the clean large-prime mass both carry a shared
positive margin, with coefficients summing to `d`.
-/
def CleanSplitMargin (d cSmall cClean : Nat) : Prop :=
  ∃ Δ N0 : Nat, 0 < Δ ∧
    ∀ n : Nat, N0 ≤ n → Odd n →
      d * (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card +
          Δ * AsymptoticGraph.L n <=
        cSmall * AsymptoticGraph.L n ∧
      d * AsymptoticGraph.cleanLargePrimeMass n +
          Δ * AsymptoticGraph.L n <=
        cClean * AsymptoticGraph.L n

lemma not_unbounded_odd_counterexamples_of_clean_split_margin
    {d cSmall cClean : Nat}
    (hSum : cSmall + cClean = d)
    (hSplit : CleanSplitMargin d cSmall cClean) :
    ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  intro hUnbounded
  rcases hSplit with ⟨Δ, N0, hΔ, hSplitN⟩
  let N : Nat := max N0 64
  rcases hUnbounded N with ⟨n, hnN, hodd, hNotRep⟩
  let S : Nat := (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card
  let C0 : Nat := AsymptoticGraph.cleanLargePrimeMass n
  let Kc : Nat := (AsymptoticGraph.K n).card
  let Ln : Nat := AsymptoticGraph.L n
  have hn0 : 0 < n := hodd.pos
  have h64 : 64 ≤ n := le_trans (le_max_right N0 64) hnN
  have hz3 : 3 <= AsymptoticGraph.z n := AsymptoticGraph.three_le_z_of_sixtyfour_le h64
  have hLpos : 0 < Ln := by
    unfold Ln AsymptoticGraph.L
    have h2n : 2 <= n := by omega
    exact Nat.log_pos Nat.one_lt_two h2n
  have hN0 : N0 ≤ n := le_trans (le_max_left N0 64) hnN
  rcases hSplitN n hN0 hodd with ⟨hSmallRaw, hCleanRaw⟩
  have hSmall : d * S + Δ * Ln <= cSmall * Ln := by
    simpa [S, Ln] using hSmallRaw
  have hClean : d * C0 + Δ * Ln <= cClean * Ln := by
    simpa [C0, Ln] using hCleanRaw
  have hK_le_SC : Kc <= S + C0 := by
    simpa [S, C0, Kc] using
      (AsymptoticGraph.card_K_le_smallPrimeBad_add_cleanLargePrimeMass_of_not_represents
        (n := n) hNotRep hz3)
  have hL_le_K : Ln <= Kc := by
    simpa [Ln, Kc] using AsymptoticGraph.L_le_card_K_of_pos hn0
  have hL_le_SC : Ln <= S + C0 := le_trans hL_le_K hK_le_SC
  have hScaled : d * Ln <= d * (S + C0) := Nat.mul_le_mul_left d hL_le_SC
  have hUpper :
      d * (S + C0) + (Δ * Ln + Δ * Ln) <= d * Ln := by
    have hLeft :
        (d * S + Δ * Ln) + (d * C0 + Δ * Ln) =
          d * (S + C0) + (Δ * Ln + Δ * Ln) := by
      calc
        (d * S + Δ * Ln) + (d * C0 + Δ * Ln) =
            (d * S + d * C0) + (Δ * Ln + Δ * Ln) := by ac_rfl
        _ = d * (S + C0) + (Δ * Ln + Δ * Ln) := by
            rw [← Nat.mul_add]
    have hRight : cSmall * Ln + cClean * Ln = d * Ln := by
      calc
        cSmall * Ln + cClean * Ln = (cSmall + cClean) * Ln := by
          rw [Nat.add_mul]
        _ = d * Ln := by simpa [hSum]
    calc
      d * (S + C0) + (Δ * Ln + Δ * Ln) =
          (d * S + Δ * Ln) + (d * C0 + Δ * Ln) := by
            symm
            exact hLeft
      _ <= cSmall * Ln + cClean * Ln := Nat.add_le_add hSmall hClean
      _ = d * Ln := hRight
  have hStrict :
      d * (S + C0) <
        d * (S + C0) + (Δ * Ln + Δ * Ln) := by
    have hPos : 0 < Δ * Ln + Δ * Ln := by
      have hDeltaLnPos : 0 < Δ * Ln := Nat.mul_pos hΔ hLpos
      omega
    exact Nat.lt_add_of_pos_right hPos
  have hlt : d * Ln < d * Ln := by
    exact lt_of_le_of_lt hScaled (lt_of_lt_of_le hStrict hUpper)
  exact (Nat.lt_irrefl _ hlt)

lemma not_cleanSplitMargin_of_unbounded_odd_counterexamples
    {d cSmall cClean : Nat}
    (hSum : cSmall + cClean = d)
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) :
    ¬ CleanSplitMargin d cSmall cClean := by
  intro hSplit
  exact (not_unbounded_odd_counterexamples_of_clean_split_margin hSum hSplit) hUnbounded

lemma erdos11_of_clean_split_margin
    {d cSmall cClean : Nat}
    (hSum : cSmall + cClean = d)
    (hSplit : CleanSplitMargin d cSmall cClean) :
    Erdos11Conjecture := by
  exact erdos11_of_not_unbounded_odd_counterexamples
    (not_unbounded_odd_counterexamples_of_clean_split_margin hSum hSplit)

/--
Log-prime refinement of the clean split target:
the clean large-prime side is replaced by clean support plus the prime-weighted
clean Wieferich sum.
-/
def CleanLogPrimeSplitMargin (d cSmall cClean : Nat) : Prop :=
  ∃ Δ N0 : Nat, 0 < Δ ∧
    ∀ n : Nat, N0 ≤ n → Odd n →
      d * (AsymptoticGraph.smallPrimeBad n (AsymptoticGraph.z n)).card +
          Δ * AsymptoticGraph.L n <=
        cSmall * AsymptoticGraph.L n ∧
      d * ((AsymptoticGraph.largePrimeCleanSupportSq n).card +
            Finset.sum (AsymptoticGraph.wieferichLargePrimeCleanSupportSq n)
              (fun p => (AsymptoticGraph.L n + 1) / (2 * Nat.log 2 p))) +
          Δ * AsymptoticGraph.L n <=
        cClean * AsymptoticGraph.L n

lemma cleanSplitMargin_of_cleanLogPrimeSplitMargin
    {d cSmall cClean : Nat}
    (hSplit : CleanLogPrimeSplitMargin d cSmall cClean) :
    CleanSplitMargin d cSmall cClean := by
  rcases hSplit with ⟨Δ, N0, hΔ, hSplitN⟩
  refine ⟨Δ, max N0 64, hΔ, ?_⟩
  intro n hn hodd
  have hN0 : N0 <= n := le_trans (le_max_left N0 64) hn
  have h64 : 64 <= n := le_trans (le_max_right N0 64) hn
  have hz3 : 3 <= AsymptoticGraph.z n := AsymptoticGraph.three_le_z_of_sixtyfour_le h64
  rcases hSplitN n hN0 hodd with ⟨hSmall, hLarge⟩
  refine ⟨hSmall, ?_⟩
  have hMass :
      d * AsymptoticGraph.cleanLargePrimeMass n <=
        d * ((AsymptoticGraph.largePrimeCleanSupportSq n).card +
          Finset.sum (AsymptoticGraph.wieferichLargePrimeCleanSupportSq n)
            (fun p => (AsymptoticGraph.L n + 1) / (2 * Nat.log 2 p))) := by
    exact Nat.mul_le_mul_left d
      (AsymptoticGraph.cleanLargePrimeMass_le_card_add_wieferich_logPrime_excess n hz3)
  have hMassAdd :
      d * AsymptoticGraph.cleanLargePrimeMass n + Δ * AsymptoticGraph.L n <=
        d * ((AsymptoticGraph.largePrimeCleanSupportSq n).card +
          Finset.sum (AsymptoticGraph.wieferichLargePrimeCleanSupportSq n)
            (fun p => (AsymptoticGraph.L n + 1) / (2 * Nat.log 2 p))) +
          Δ * AsymptoticGraph.L n := by
    exact Nat.add_le_add_right hMass (Δ * AsymptoticGraph.L n)
  exact le_trans hMassAdd hLarge

lemma erdos11_of_cleanLogPrime_split_margin
    {d cSmall cClean : Nat}
    (hSum : cSmall + cClean = d)
    (hSplit : CleanLogPrimeSplitMargin d cSmall cClean) :
    Erdos11Conjecture := by
  exact erdos11_of_clean_split_margin hSum
    (cleanSplitMargin_of_cleanLogPrimeSplitMargin hSplit)

/--
Clean safe split package:
the small-prime side keeps the safe coefficient `4305397884`, while the
large-prime side uses the clean large-prime mass with coefficient `12367918776`.
-/
def AsymptoticCleanSplitMargin16673316660Safe : Prop :=
  CleanSplitMargin 16673316660 4305397884 12367918776

/--
Sharper safe clean split package:
the large-prime side is stated directly with clean support plus the
log-weighted clean Wieferich sum.
-/
def AsymptoticCleanLogPrimeSplitMargin16673316660Safe : Prop :=
  CleanLogPrimeSplitMargin 16673316660 4305397884 12367918776

def UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe : Prop :=
  (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) →
    AsymptoticCleanSplitMargin16673316660Safe

lemma not_asymptotic_clean_split_margin16673316660Safe_of_unbounded_odd_counterexamples
    (hUnbounded : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) :
    ¬ AsymptoticCleanSplitMargin16673316660Safe := by
  exact not_cleanSplitMargin_of_unbounded_odd_counterexamples
    (d := 16673316660) (cSmall := 4305397884) (cClean := 12367918776)
    (by norm_num) hUnbounded

lemma unboundedForcesAsymptoticCleanSplitMargin16673316660Safe_of_erdos11
    (hE : Erdos11Conjecture) :
    UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe := by
  exact unbounded_counterexamples_elim_of_erdos11 hE

lemma unboundedForcesAsymptoticCleanSplitMargin16673316660Safe_iff_not_unbounded_odd_counterexamples :
    UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe ↔
      ¬ (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ Odd n ∧ ¬ Represents n) := by
  exact force_target_iff_not_unbounded_odd_counterexamples_of_not_target_of_unbounded
    not_asymptotic_clean_split_margin16673316660Safe_of_unbounded_odd_counterexamples

lemma erdos11_of_unbounded_forces_asymptotic_clean_split_margin16673316660Safe
    (hStep1 : UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe) :
    Erdos11Conjecture := by
  exact (force_target_iff_erdos11_of_not_target_of_unbounded
    not_asymptotic_clean_split_margin16673316660Safe_of_unbounded_odd_counterexamples).mp hStep1

lemma erdos11_iff_unboundedForcesAsymptoticCleanSplitMargin16673316660Safe :
    Erdos11Conjecture ↔ UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe := by
  exact (force_target_iff_erdos11_of_not_target_of_unbounded
    not_asymptotic_clean_split_margin16673316660Safe_of_unbounded_odd_counterexamples).symm

lemma unboundedForcesAsymptoticSplitMargin16673316660Safe_iff_clean :
    UnboundedForcesAsymptoticSplitMargin16673316660Safe ↔
      UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe := by
  exact force_targets_iff_of_not_targets_of_unbounded
    not_asymptotic_split_margin16673316660Safe_of_unbounded_odd_counterexamples
    not_asymptotic_clean_split_margin16673316660Safe_of_unbounded_odd_counterexamples

lemma counterexampleBridge16673316660_iff_unboundedForcesAsymptoticCleanSplitMargin16673316660Safe :
    CounterexampleBridge16673316660 ↔
      UnboundedForcesAsymptoticCleanSplitMargin16673316660Safe := by
  rw [counterexampleBridge16673316660_iff_unboundedForcesAsymptoticSplitMargin16673316660Safe,
    unboundedForcesAsymptoticSplitMargin16673316660Safe_iff_clean]

lemma erdos11_of_asymptotic_clean_split_margin16673316660Safe
    (hSplit : AsymptoticCleanSplitMargin16673316660Safe) :
    Erdos11Conjecture := by
  exact erdos11_of_clean_split_margin
    (d := 16673316660) (cSmall := 4305397884) (cClean := 12367918776)
    (by norm_num) hSplit

lemma erdos11_of_asymptotic_cleanLogPrime_split_margin16673316660Safe
    (hSplit : AsymptoticCleanLogPrimeSplitMargin16673316660Safe) :
    Erdos11Conjecture := by
  exact erdos11_of_cleanLogPrime_split_margin
    (d := 16673316660) (cSmall := 4305397884) (cClean := 12367918776)
    (by norm_num) hSplit

lemma counterexampleBridgeNeg16673316660_iff :
    CounterexampleBridgeNeg16673316660 ↔ CounterexampleBridge16673316660 := by
  constructor
  · intro hNeg hUnbounded
    exact hNeg (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mpr hUnbounded)
  · intro hPos hNot
    exact hPos (not_Erdos11Conjecture_iff_unbounded_odd_counterexamples.mp hNot)

lemma erdos11_iff_counterexampleBridgeNeg16673316660 :
    Erdos11Conjecture ↔ CounterexampleBridgeNeg16673316660 := by
  exact (neg_force_false_target_iff_erdos11
    AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660).symm

lemma erdos11_iff_counterexampleBridge16673316660 :
    Erdos11Conjecture ↔ CounterexampleBridge16673316660 := by
  exact (force_false_target_iff_erdos11
    AsymptoticGraph.not_MatchedDensityBoundsScaled16673316660).symm

/--
Unconditional conjecture in direct arithmetic language:
every sufficiently large odd integer is the sum of a positive squarefree
number and a power of `2`.
-/
def LargeOddSquarefreePlusPowerOfTwoConjecture : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → Odd n →
    ∃ m k : Nat, m > 0 ∧ Squarefree m ∧ n = m + 2 ^ k

lemma largeOddSquarefreePlusPowerOfTwoConjecture_iff_erdos11 :
    LargeOddSquarefreePlusPowerOfTwoConjecture ↔ Erdos11Conjecture := by
  rfl

lemma erdos11_iff_largeOddSquarefreePlusPowerOfTwoConjecture :
    Erdos11Conjecture ↔ LargeOddSquarefreePlusPowerOfTwoConjecture := by
  exact largeOddSquarefreePlusPowerOfTwoConjecture_iff_erdos11.symm

/--
Question form:
is every sufficiently large odd integer the sum of a positive squarefree
number and a power of `2`?
-/
def EveryLargeOddIsSquarefreePlusPowerOfTwo : Prop :=
  LargeOddSquarefreePlusPowerOfTwoConjecture

theorem everyLargeOddIsSquarefreePlusPowerOfTwo_iff_erdos11 :
    EveryLargeOddIsSquarefreePlusPowerOfTwo ↔ Erdos11Conjecture := by
  exact largeOddSquarefreePlusPowerOfTwoConjecture_iff_erdos11

end Erdos11
