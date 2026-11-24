module

public import Mathlib

/-!
# Erdős Problem 1100, variant `eq_omega`

The definition and statement below are copied verbatim from
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/1100.lean`
(commit 5c783f7227e86c989fd592da04915f377dc6cb23).

For $n \ge 1$ with divisors $1 = d_1 < \dots < d_{\tau(n)} = n$, $\tau_\perp(n)$ counts the indices
$i$ with $\gcd(d_i, d_{i+1}) = 1$, and $\omega(n)$ counts the distinct prime divisors of $n$.
The statement says: for every $k$ there is a squarefree $n$ with $\omega(n) = k$ and
$\tau_\perp(n) = k$. Erdős and Hall [ErHa78, p. 480] note this equality for
$n = p_1 \cdots p_k$ with $p_i > p_1 \cdots p_{i-1}$.

[ErHa78] Erdős, P. and Hall, R. R., *On some unconventional problems on the divisors of
integers*. J. Austral. Math. Soc. Ser. A 25 (1978), 479-485.
-/

@[expose] public section

open scoped ArithmeticFunction.omega

namespace Erdos1100

/-- $\tau_\perp(n)$ is the number of indices $i$ such that the divisors $d_i<d_{i+1}$ of $n$ that
are consecutive in increasing order are coprime. As in `Erdos1099`, `Nat.nth (· ∣ n) i` is the
$(i+1)$-th smallest divisor of `n` (counting from $0$), and `i` runs over the $\tau(n)-1$ pairs of
consecutive divisors. For $n = 0$ and $n = 1$ there are no such pairs and the value is $0$. -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1))).card

/-- For every $k$ there is a squarefree $n$ with $\omega(n) = k$ and $\tau_\perp(n) = k$. -/
theorem erdos_1100.variants.eq_omega (k : ℕ) :
    ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = k := by
  sorry

end Erdos1100
