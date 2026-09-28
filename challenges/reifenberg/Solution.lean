import Statement
import GMTFoundations

/-!
# Solution: discrete and rectifiable Reifenberg theorems

The trusted vocabulary of `Statement.lean` is definitionally the library's, so the claims are the
library theorems `GMTFoundations.discrete_reifenberg` and `GMTFoundations.rectifiable_reifenberg`.
-/

theorem challenge_discrete_reifenberg (n : ℕ) : GMTChallenge.DiscreteReifenbergClaim n :=
  fun hn => GMTFoundations.discrete_reifenberg hn

theorem challenge_rectifiable_reifenberg (n : ℕ) : GMTChallenge.RectifiableReifenbergClaim n :=
  fun hn C => GMTFoundations.rectifiable_reifenberg hn C
