# Statement and definition changes

Running notes for the round-4 fixes. A headline theorem is `deadlock_freedom`,
`blocked_unblocks`, `blocked_chain`, `blocked_progress`, `fair_delivered`,
`cell_fresh`, and the other results printed from `Deadlock.lean`.

## Already on the branch, kept

`SemInv` gained `idleOff`, `rostered`, and `offEmpty`.

- What: an actor that is not alive is idle; a live actor is on the roster; an
  actor off the roster has an empty parked list.
- Why: a subtree kill folds the roster to fail waiters and to drop parked
  entries whose sender died. Those three facts are what makes the mailbox
  after that fold equal to the mailbox the occupancy argument already knew.
  They are proved for the initial world and preserved by `step_inv`.
- Headline theorems: unchanged. `SemInv` is not a hypothesis of those
  statements. The invariant is stronger, so every preserver has more to show,
  and `step_inv` does show it. Nothing that used to be proved became false.

`occ_apply` gained `(hSlots : OpenSlots w)`.

- What: one extra hypothesis on the internal lemma that says one step
  preserves `OccInv`.
- Why: the kill arm folds `killOne`. After each member the fold re-establishes
  `SemInv`, `MailInv`, and `OpenSlots` by `killOne_inv`, and that lemma takes
  `OpenSlots`. The next member is then still a world the occupancy lemmas
  accept. The only caller is `inv2_reachable`, which already has `OpenSlots`
  as the third conjunct of `Inv`.
- Headline theorems: unchanged. The hypothesis is discharged at that single
  call site. A proof that did not reuse `killOne_inv` would not need the
  argument; this one does, and it does not weaken the conclusion of `occ_apply`.

## This round

No theorem statement, no definition used by a headline theorem, and no
invariant field has been changed for the checker fix.

`check` used to print `pass` when `render` did, which is `checkBool` alone.
It now prints `pass` only when `checkBool` and `localOkB` both hold, in graph
mode and before a trace replay. `render`, `checkBool`, `localOkB`, and
`GraphOk` are the same functions as before. `localIssues` and `acceptReport`
are new and only build the text.

`examples/safe.json` and `examples/credit.json` gained one receive transition
per delivered label, with an empty program. That is the handler `labelHandled`
asks for. The program does not repeat the send: the edge occupancy has
already reserved the slot, so a same-state send would not pass `sendsOk`.

`examples/token-relation.json` is unchanged. Its `Release` and `Return`
transitions leave a state whose floor toward the partner is 0 and enter a
state whose floor is 11, so `sendsOk` rejects them. `NewBestTip` and
`ReturnToken` have no handler. `render` of that description is still `pass`.
`check` is not, and that is the honest result: the compatibility relation is
closed, and the programs are not a checked implementation.
