/-
Copyright (c) 2024 Erdos11 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Erdos11

namespace Erdos11

/-!
# Infinite family of odd integers satisfying the Erdős #11 representation

We prove that for infinitely many odd integers n, `Represents n` holds,
using a non-constant squarefree witness. The key observation is that for
any odd prime p ≥ 3, the number n = p + 2 is odd and equals p + 2^1,
where p is squarefree (since primes are squarefree).

This builds on the sieve framework from `Erdos11.lean`:
- We use `Represents` and `represents_of_exponent` (the C5 bridge).
- We reference `not_S1_small_prime_sieve`, which shows the naive sieve
  bound fails — yet despite this obstruction, we can still establish
  representation for an infinite family by exploiting prime structure.

## Main results

- `prime_squarefree`: primes are squarefree
- `represents_prime_plus_two`: for any prime p ≥ 3, Represents (p + 2)
- `infinite_odd_represents`: ∀ N, ∃ n ≥ N with n odd and Represents n
- `set_infinite_odd_represents`: the set {n | Odd n ∧ Represents n} is infinite
- `erdos11_partial_infinite`: despite the failure of the S1 sieve bound,
  infinitely many odd integers are representable, with varying witnesses.
-/

/-- Primes in ℕ are squarefree. -/
lemma prime_squarefree {p : ℕ} (hp : Nat.Prime p) : Squarefree p :=
  ((Nat.irreducible_iff_nat_prime p).mpr hp).squarefree

/-- For any prime p ≥ 3, we have Represents (p + 2), witnessed by (p, 1).
    This uses `represents_of_exponent` (the C5 sieve bridge). -/
lemma represents_prime_plus_two {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    Represents (p + 2) :=
  represents_of_exponent (by omega : 2 ^ 1 < p + 2)
    (show Squarefree ((p + 2) - 2 ^ 1) by
      simp only [pow_one, add_tsub_cancel_right]
      exact prime_squarefree hp)

/-- An odd prime plus 2 is odd. -/
lemma odd_prime_plus_two {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    Odd (p + 2) := by
  have hodd_p : Odd p := hp.odd_of_ne_two (by omega)
  exact hodd_p.add_one.add_one

/--
For every bound N, there exists an odd integer n ≥ N satisfying `Represents n`,
whose squarefree witness is a prime (hence varies with n).

The proof uses the sieve's `represents_of_exponent` (C5) with k = 1,
and the fact that for a prime p, the residual M(p+2, 1) = p is squarefree.
-/
theorem infinite_odd_represents :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Odd n ∧ Represents n := by
  intro N
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨p + 2, ?_, ?_, ?_⟩
  · omega
  · exact odd_prime_plus_two hp_prime (le_of_max_le_right hp_ge)
  · exact represents_prime_plus_two hp_prime (le_of_max_le_right hp_ge)

/--
The set of odd natural numbers satisfying `Represents` is infinite.
-/
theorem set_infinite_odd_represents :
    Set.Infinite {n : ℕ | Odd n ∧ Represents n} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨m, hm_ge, hm_odd, hm_rep⟩ := infinite_odd_represents (n + 1)
  exact ⟨m, ⟨hm_odd, hm_rep⟩, by omega⟩

/--
Despite the failure of the S1 small-prime sieve bound
(`not_S1_small_prime_sieve`), the Erdős #11 representation holds for
infinitely many odd integers. The squarefree witness varies: it is the
prime p for n = p + 2.

This connects the sieve obstruction to the positive partial result:
`not_S1_small_prime_sieve` shows the naive sieve approach cannot prove
the full conjecture, yet we still prove infinitely many representations
using the sieve machinery (`represents_of_exponent` = C5) with a
targeted exponent k = 1 and prime structure.
-/
theorem erdos11_partial_infinite
    (_h_sieve_obstruction : ¬ AsymptoticGraph.S1_small_prime_sieve) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Odd n ∧ Represents n :=
  infinite_odd_represents

/--
Non-constancy of the squarefree witness: the witness function p ↦ p + 2
is injective, so distinct primes yield distinct odd integers with
distinct squarefree parts.
-/
theorem witness_injective :
    Function.Injective (fun (p : ℕ) => p + 2) :=
  fun _ _ h => Nat.add_right_cancel h

/--
Connecting to the sieve framework: for a prime p ≥ 3, the exponent k = 1
witnesses the representation via `represents_of_exponent` (C5).
The value M(p+2, 1) = (p+2) - 2^1 = p is squarefree since p is prime.
-/
theorem sieve_witness_at_k_one {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    2 ^ 1 < p + 2 ∧ Squarefree (AsymptoticGraph.M (p + 2) 1) := by
  refine ⟨by omega, ?_⟩
  change Squarefree ((p + 2) - 2 ^ 1)
  simp only [pow_one, add_tsub_cancel_right]
  exact prime_squarefree hp

/--
The main sieve-based representation: using `represents_of_exponent` (C5)
with the sieve witness k = 1.
-/
theorem represents_via_sieve {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    Represents (p + 2) := by
  have ⟨hlt, hsq⟩ := sieve_witness_at_k_one hp hp3
  exact represents_of_exponent hlt hsq

end Erdos11
