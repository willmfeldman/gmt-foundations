module

public import Vocabulary
public import GMTFoundations

/-!
# Solution: Rellich–Kondrachov compactness with compact trace

The trusted vocabulary of `Vocabulary.lean` is definitionally the library's, so the claim is the
library theorem `GMTFoundations.rellich_trace_weak_compactness`.
-/

@[expose] public section

theorem challenge_rellich_trace (n : ℕ) [NeZero n] : GMTChallenge.RellichTraceClaim n :=
  GMTFoundations.rellich_trace_weak_compactness
