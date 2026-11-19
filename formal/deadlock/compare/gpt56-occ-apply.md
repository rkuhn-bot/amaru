# GPT-5.6 `occ_apply` comparison

- Start: 2026-11-19 07:30:44 UTC
- Finish: 2026-11-19 07:41:06 UTC
- Wall-clock time: 10 minutes 22 seconds
- Commits: 3, including this report
- `occ_apply` kill-case `sorry` closed: yes
- Lean source diff: 398 lines added, 1 line removed
- Remaining `sorry`s: 2 (`Step.lean` and `Rank.lean`)

No existing definition or theorem statement was weakened or otherwise changed. The proof adds helper theorem statements in `Inv2.lean` to preserve `OccInv` through waiter failure, sender forgetting, one-member kill, and the subtree fold. It also adds `term_world` in `Occ.lean`, exposing the existing fact that draining and refunding queues yield the same world after replacing the actor with a dead, empty shell. These helpers are needed to align the accounting-friendly operation order with the operational order in `killOne`.

`lake build` and `lake build Deadlock` both completed successfully.

`#print axioms Deadlock.occ_apply`:

```text
'Deadlock.occ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The hard part was reconciling `killOne`'s order—refund, fail waiters, forget the killed sender, then mark it dead—with the occupancy lemmas, which are easiest to apply by draining queues and marking the actor dead first. The proof uses the drain/refund world equivalence, commutes waiter failure past the dead actor update, and proves that `forgetSender` is a no-op because a live terminable subtree member has no outstanding parked mail under `OccInv`.
