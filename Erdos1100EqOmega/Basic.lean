/-
Formal proof of `erdos_1100.variants.eq_omega` from google-deepmind/formal-conjectures
(file `FormalConjectures/ErdosProblems/1100.lean`, commit 5c783f7227e86c989fd592da04915f377dc6cb23).

The definition `tauPerp` and the statement below are copied verbatim from that file.

Proof idea (Erdős–Hall [ErHa78, p. 480]): take primes `p₁ < p₂ < ⋯` with each `pᵢ` larger than
`p₁ ⋯ pᵢ₋₁`. The sorted divisor list of `n * p` (for a prime `p > n`) is the divisor list of `n`
followed by `p` times it, so exactly one new coprime adjacent pair appears, namely `(n, p)`.
-/
import Mathlib

/-!
# Erdős Problem 1100: `τ⊥(n) = ω(n)` for some squarefree `n` with `ω(n) = k`, for every `k`
-/

open scoped ArithmeticFunction.omega

namespace Erdos1100

/-- Copied verbatim from the formal-conjectures statement file. -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1))).card

/-- The divisors of `n` as a sorted list. -/
noncomputable def D (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

lemma length_D (n : ℕ) : (D n).length = n.divisors.card := Finset.length_sort _

lemma mem_D {n d : ℕ} : d ∈ D n ↔ d ∣ n ∧ n ≠ 0 := by
  simp [D, Finset.mem_sort, Nat.mem_divisors]

/-- For `n ≠ 0`, the `i`-th divisor is the `i`-th entry of the sorted divisor list. -/
lemma nth_dvd_eq {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    Nat.nth (· ∣ n) i = (D n).getD i 0 := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Finset.finite_toSet n.divisors).subset fun d hd ↦ by
      simpa [Nat.mem_divisors, hn] using hd
  rw [Nat.nth_eq_getD_sort hf]
  have : hf.toFinset = n.divisors := by
    ext d; simp [Nat.mem_divisors, hn]
  rw [this]; rfl

/-- Indicator of coprimality. -/
def c (a b : ℕ) : ℕ := if Nat.Coprime a b then 1 else 0

/-- Number of coprime adjacent pairs in a list. -/
def S (l : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (l.length - 1), c (l.getD i 0) (l.getD (i + 1) 0)

lemma tauPerp_eq {n : ℕ} (hn : n ≠ 0) : tauPerp n = S (D n) := by
  unfold tauPerp S
  rw [Finset.card_filter, length_D,
    Fin.sum_univ_eq_sum_range (fun i ↦ if Nat.Coprime (Nat.nth (· ∣ n) i)
      (Nat.nth (· ∣ n) (i + 1)) then 1 else 0)]
  simp only [nth_dvd_eq hn, c]

lemma pairwise_D (n : ℕ) : (D n).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

/-- Key structural lemma: if `p` is a prime larger than `n`, the sorted divisors of `n * p` are
the sorted divisors of `n` followed by `p` times them. -/
lemma D_mul {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hnp : n < p) :
    D (n * p) = D n ++ (D n).map (p * ·) := by
  have hnp0 : n * p ≠ 0 := Nat.mul_ne_zero hn.ne' hp.ne_zero
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (pairwise_D _) ?_ ?_
  · refine List.pairwise_append.2 ⟨pairwise_D n, ?_, ?_⟩
    · exact List.pairwise_map.2 ((pairwise_D n).imp fun h ↦
        Nat.mul_lt_mul_of_pos_left h hp.pos)
    · intro a ha b hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
      have ha' := (mem_D.1 ha).1
      have he' := (mem_D.1 he).1
      have h1 : a ≤ n := Nat.le_of_dvd hn ha'
      have h2 : 1 ≤ e := Nat.pos_of_dvd_of_pos he' hn
      calc a ≤ n := h1
        _ < p := hnp
        _ = p * 1 := (mul_one p).symm
        _ ≤ p * e := Nat.mul_le_mul_left p h2
  · intro d
    simp only [List.mem_append, List.mem_map, mem_D, ne_eq, hnp0, not_false_eq_true, and_true,
      hn.ne']
    constructor
    · intro hd
      by_cases hpd : p ∣ d
      · obtain ⟨e, rfl⟩ := hpd
        right
        exact ⟨e, Nat.dvd_of_mul_dvd_mul_right hp.pos (by rwa [mul_comm p e] at hd), rfl⟩
      · left
        exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm.dvd_of_dvd_mul_right hd
    · rintro (hd | ⟨e, he, rfl⟩)
      · exact Dvd.dvd.mul_right hd p
      · rw [mul_comm p e]; exact Nat.mul_dvd_mul_right he p

lemma getD_append_left' (L M : List ℕ) {i : ℕ} (hi : i < L.length) :
    (L ++ M).getD i 0 = L.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right' (L M : List ℕ) (i : ℕ) :
    (L ++ M).getD (L.length + i) 0 = M.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

lemma getD_map_mul (L : List ℕ) (p i : ℕ) :
    (L.map (p * ·)).getD i 0 = p * L.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> simp

/-- Counting step: appending `p` times the list adds exactly one coprime adjacent pair. -/
lemma S_append {L : List ℕ} {p : ℕ} (hp : 1 < p) (hL : 0 < L.length)
    (hbd : Nat.Coprime (L.getD (L.length - 1) 0) (p * L.getD 0 0)) :
    S (L ++ L.map (p * ·)) = S L + 1 := by
  set t := L.length with ht
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hlen : (L ++ L.map (p * ·)).length - 1 = s + (s + 1) := by
    simp [← ht]; omega
  unfold S
  rw [hlen, Finset.sum_range_add, Finset.sum_range_succ']
  have hS : t - 1 = s := by omega
  rw [hS]
  -- first block: indices inside `L`
  have h1 : ∀ i ∈ Finset.range s,
      c ((L ++ L.map (p * ·)).getD i 0) ((L ++ L.map (p * ·)).getD (i + 1) 0)
        = c (L.getD i 0) (L.getD (i + 1) 0) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [getD_append_left' _ _ (by omega), getD_append_left' _ _ (by omega)]
  -- second block: indices inside `p • L`, never coprime
  have h2 : ∀ i ∈ Finset.range s,
      c ((L ++ L.map (p * ·)).getD (s + (i + 1)) 0)
        ((L ++ L.map (p * ·)).getD (s + (i + 1) + 1) 0) = 0 := by
    intro i _
    have e1 : s + (i + 1) = t + i := by omega
    rw [e1, show t + i + 1 = t + (i + 1) by omega, ht, getD_append_right', getD_append_right', getD_map_mul, getD_map_mul]
    unfold c
    rw [if_neg]
    intro hcop
    have hdvd : p ∣ Nat.gcd (p * L.getD i 0) (p * L.getD (i + 1) 0) :=
      Nat.dvd_gcd (dvd_mul_right p _) (dvd_mul_right p _)
    rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, zero_add]
  -- the boundary pair
  have e3 : s + 0 = L.length - 1 := by omega
  have e4 : s + 0 + 1 = L.length + 0 := by omega
  rw [e4, getD_append_right', getD_map_mul, e3,
    getD_append_left' _ _ (by omega)]
  unfold c
  rw [if_pos hbd]

lemma D_one : D 1 = [1] := by
  simp [D, Nat.divisors_one]

/-- `erdos_1100.variants.eq_omega`, exactly as stated in formal-conjectures. -/
theorem erdos_1100.variants.eq_omega (k : ℕ) :
    ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = k := by
  -- Strengthened statement carried through the induction.
  suffices h : ∃ n : ℕ, 0 < n ∧ Squarefree n ∧ ω n = k ∧ tauPerp n = k ∧
      (D n).getD 0 0 = 1 ∧ (D n).getD ((D n).length - 1) 0 = n by
    obtain ⟨n, -, h⟩ := h
    exact ⟨n, h.1, h.2.1, h.2.2.1⟩
  induction k with
  | zero =>
    refine ⟨1, one_pos, squarefree_one, by simp, ?_, by simp [D_one], by simp [D_one]⟩
    rw [tauPerp_eq one_ne_zero, D_one]; rfl
  | succ k ih =>
    obtain ⟨n, hn, hsq, hω, hτ, h0, hlast⟩ := ih
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    have hnp : n < p := hpn
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦
        (Nat.le_of_dvd hn h).not_gt hnp).symm
    have hlen : 0 < (D n).length := by
      rw [length_D]; exact Finset.card_pos.2 ⟨1, by simp [hn.ne']⟩
    have hDm := D_mul hn hp hnp
    refine ⟨n * p, Nat.mul_pos hn hp.pos, ?_, ?_, ?_, ?_, ?_⟩
    · exact Nat.squarefree_mul_iff.2 ⟨hcop, hsq, hp.squarefree⟩
    · rw [ArithmeticFunction.cardDistinctFactors_mul hcop,
        ArithmeticFunction.cardDistinctFactors_apply_prime hp, hω]
    · rw [tauPerp_eq (Nat.mul_ne_zero hn.ne' hp.ne_zero), hDm,
        S_append hp.one_lt hlen (by rw [hlast, h0, mul_one]; exact hcop), ← tauPerp_eq hn.ne', hτ]
    · rw [hDm, getD_append_left' _ _ hlen, h0]
    · rw [hDm]
      have e : (D n ++ (D n).map (p * ·)).length - 1 = (D n).length + ((D n).length - 1) := by
        simp; omega
      rw [e, getD_append_right', getD_map_mul, hlast, mul_comm]

end Erdos1100
