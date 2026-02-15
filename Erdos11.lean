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

/--
Large-prime support truncated to the non-vacuous square range `p^2 <= n`.
For `p^2 > n`, the local condition `(n - 2^k) % p^2 = 0` is impossible on `K n`.
-/
noncomputable def largePrimeSupportSq (n : Nat) : Finset Nat := by
  classical
  exact (largePrimeSupport n).filter (fun p => p ^ 2 <= n)

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

lemma prime_ne_two_of_mem_largePrimeSupport {n p : Nat}
    (hz2 : 2 <= z n) (hpS : p ∈ largePrimeSupport n) :
    p ≠ 2 := by
  have hpLow : z n + 1 <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).1
  intro hp2
  have h3le : 3 <= p := le_trans (Nat.succ_le_succ hz2) hpLow
  have h3le2 : 3 <= 2 := hp2 ▸ h3le
  exact Nat.not_succ_le_self 2 h3le2

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

lemma G1_large_prime_decomp_sq_localOrder_coarse (n : Nat) :
    (B n (z n)).card <= (largePrimeSupportSq n).card * (L n + 1) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n) (sum_localOrderBound_largeSq_le n)

lemma G1_large_prime_decomp_sq_localOrder_half (n : Nat) (hz2 : 2 <= z n) :
    (B n (z n)).card <= (largePrimeSupportSq n).card * ((L n + 1) / 2 + 1) := by
  exact le_trans (G1_large_prime_decomp_sq_localOrder n)
    (sum_localOrderBound_largeSq_le_half_add_one n hz2)

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

lemma two_le_z_of_sixteen_le {n : Nat} (hn : 16 <= n) : 2 <= z n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 16) hn)
  have hlog4 : 4 <= L n := by
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

lemma T0_of_matched_density_bounds (h : MatchedDensityBounds) :
    Erdos11Conjecture := by
  rcases h with ⟨a, b, d, hab, hS1, hG3⟩
  exact T0_erdos11_from_density_assumptions hab hS1 hG3

end AsymptoticGraph

end Erdos11

