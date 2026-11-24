module

public import Erdos1100EqOmega

/-!
# Proof of Erdős Problem 1100, variant `eq_omega`

Comparator checks that the declaration below has the same statement as in `Challenge.lean` and uses
only the permitted axioms. The proof is in `Erdos1100EqOmega/Basic.lean`.
-/

public section

open scoped ArithmeticFunction.omega

namespace Erdos1100

/-- For every $k$ there is a squarefree $n$ with $\omega(n) = k$ and $\tau_\perp(n) = k$. -/
theorem erdos_1100.variants.eq_omega (k : ℕ) :
    ∃ n : ℕ, Squarefree n ∧ ω n = k ∧ tauPerp n = k :=
  exists_squarefree_omega_eq_tauPerp k

end Erdos1100
