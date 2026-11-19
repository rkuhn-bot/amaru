# `occ_apply`, `kill` case — run log

Branch `compare/opus5-occ-apply`, from `7ebe0f4edc14b1aea928cd17cdb7c37481553d7e`.

## Result

| | |
| --- | --- |
| Wall clock | 26 minutes (07:30:43 UTC to 07:57 UTC) |
| Commits | 5 (4 proof commits, 1 for this file) |
| Sorry closed | yes |
| `.lean` lines added | 412 |
| `.lean` lines removed | 1 |
| Sorries in the package | 2 (`Step.lean`, `Rank.lean` — untouched) |

`lake build` completes, with the same linter warnings the base commit already had.

## Axioms

```
$ lake env lean -- '#print axioms Deadlock.occ_apply'
'Deadlock.occ_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. No new axiom, no `native_decide`.

## Definitions and statements changed

None. `occ_apply` keeps its statement; the `sorry` is replaced by two lines:

```lean
  | kill sub key =>
    rw [kill_apply_world I w w' sub key h]
    exact occ_kill I hG w sub key hO hS.cont
```

Everything else is new material appended to `Deadlock/Occ.lean`, in this order:

- `failWaiter_fate`, `fail_account`, `failFold_account` — failing a waiter keeps its
  tokens, life and typestate, keeps its continuation well-typed, and can only lower
  `pending`.
- `forgetFold_id`, `forget_id` — `forgetSender w dead = w` when no parked entry anywhere
  names `dead` as its sender.
- `countCredited_eq` — the credit a parked entry pays back equals the slot it occupies.
- `still_free` — Lemma 1 for a terminable actor: nothing it sent is parked on anyone.
- `member_terminableName` — a subtree member's role is terminable, from
  `GraphOk.subtrees`.
- `killOne_account` — what one kill does to one actor's queues, life, tokens, typestate
  and `pending`.
- `occ_killOne` — one kill keeps all fourteen fields of `OccInv`, and keeps every
  continuation well-typed.
- `occ_killFold`, `occ_kill` — fold that over the roster, then note the tombstone touches
  no actor.

## Commits

```
2ef748593 feat(deadlock): account for failing a waiter and forgetting a dead sender
f4eda388f feat(deadlock): state what one subtree kill does to each account
56a00a046 feat(deadlock): one subtree kill keeps every occupancy account
84f2919eb feat(deadlock): occupancy survives a subtree kill
```

## What was hard

The accounting, not the bookkeeping. A kill does five things at once — it reads cells,
refunds the queued messages, refunds the parked entries, fails every waiter, forgets the
dead sender, and finally blanks the actor — and `OccInv.balance` has to come out exactly
even across all of them. Three points cost real time:

1. **`forgetSender` had to be the identity.** It filters parked entries by sender, so if
   it ever removed anything it would silently destroy a slot that some other actor's
   token count is still paying for, and `balance` would break with no local repair. It
   does not remove anything, but only for a non-local reason: a subtree member is
   terminable (`GraphOk.subtrees`), and `OccInv.still` says a terminable actor owes
   nothing, so it cannot be the sender of any parked entry. Finding that chain —
   `GraphOk.subtrees` to `terminableName` to `still` to "no parked entry names it" — was
   the crux of the whole case, and it is why `still_free` and `member_terminableName`
   exist.

2. **Refunds are counted on a different field from the one that is charged.** `slot`
   charges a parked entry to `p.sender`; `refundParked` pays back on `p.msg.sender`.
   They agree only because `OccInv.parkMsg` says the two fields match, which is what
   `countCredited_eq` bridges. Until I spotted that, the `balance` arithmetic was off by
   exactly the parked count and looked like a genuine counterexample.

3. **Everything is a fold.** `killOne` is a chain of five world transformers and
   `killMembers` folds `killOne` over the roster, so every fact has to be stated as a
   per-actor bundle that survives composition. `killOne_account` is that bundle; it is
   verbose but it made `occ_killOne` mechanical. Carrying `∀ j, contTy (w.st j)` through
   the fold alongside `OccInv` was needed because `failWaiter` resumes a sender's
   continuation, and the next kill in the fold needs that continuation to still be
   well-typed.

Two smaller pieces of friction: the toolchain was not on the machine, so the first
minutes went to installing elan and Lean `v4.35.0`; and `simpa` repeatedly failed to see
through `let`-bound intermediate worlds where a term-mode `exact` went through, because
`exact` unfolds let-bindings at default transparency and `simp` does not.
