# Helen review 9 (mux / component (A)) — parent's summary, not Helen's verbatim text

Source: the parent agent's summary in the 12:12 (UTC+1) message of 2026-11-15. Helen's original text was not
supplied; the points below are the parent's account of it.

1. **The `Sent` term.** Helen's main hole: the `Sent` reply of each handler `Send` call was not counted in
   `W(mux → handler)`.
2. **The `WantNext` guards.** The bound `FromNetwork ≤ p_h` needs a guard on when handlers issue `WantNext`; Helen
   proposed "responders issue `WantNext` only in `StIdle`, never on `Registered`" and listed the sites that violate it.
3. **Re-register.** `do_register` keeps the per-protocol state when a handler is replaced, so `wanted` (and the
   buffer) carry over to the new handler.

Pass-6 findings that answer these (fork commit `3842d8947`, checked against tree `33d62a6f`) are folded into
`03-candidate-theory.md` §8 "Pass 6", §8(b), §9 and §11, split into "holds in today's code" and "requirement for the
rewrite".
