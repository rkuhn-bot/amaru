# Helen — adversarial review, round 3 (rkuhn-bot/amaru @ e16c84b58, formal/deadlock/)

Mon 16 Nov 2026, Europe/Berlin. Read-only: nothing pushed, no GitHub comments, nobody contacted. gh/git as rkuhn-bot; pragma-org untouched; no workarounds needed (fetch clean).

## Build / trust base
- `lake build Deadlock` (Lean 4.35.0): **EXIT 0**, 0 `sorry`/`admit`, no `axiom`/`unsafe` declarations in `Deadlock/`.
- `#print axioms` — every headline theorem is `[propext, Classical.choice, Quot.sound]` or a subset:
  blocked_unblocks, blocked_chain, blocked_progress, fin_exec_no_blocked, fin_exec_no_wake, cell_wake_enabled, fair_delivered, deadlock_freedom, cell_fresh.
  Witnesses demo_fair, demo_graph_ok, demo_local_ok, demo_parked/awaiting/answered/woken, park_graph_ok/local_ok/reachable/unblocks: `[propext]` or `[propext, Quot.sound]`. **No `Lean.ofReduceBool` / native_decide axioms on any witness or headline theorem.**
- `native_decide` still remains in non-headline files: Examples.lean, Failures.lean, and Counter.lean (my round-2 counterexamples as committed). These are harmless, but they keep the compiler in the trust base for those lemmas. Switching to `decide` would be cheap; my R3 file shows these sizes are kernel-decidable.
- My mechanisations: `formal/deadlock/Helen/R3.lean` (326 lines), all kernel `decide`, axioms ⊆ `[propext, Classical.choice, Quot.sound]`; `Helen/Ax3.lean` (axiom dump).

## Verdict
This is a real step forward. **N1 is genuinely fixed.** `blocked_unblocks` (Chain.lean:1240) is a tight, constructive "the chain under a blocked actor can be driven until it is unblocked" theorem. Stutter is sound. The witnesses are kernel-checked. Three problems remain before I would call the statement "Amaru is deadlock-free":
1. `FinExec` is now **uninhabited**, so `fin_exec_no_blocked` / `fin_exec_no_wake` are vacuous (proved).
2. Peer timeout is modelled as **success**, and untimed peer waits are **rejected**. Amaru's mux reader is an untimed peer wait, so the model cannot express it, and its timeout path (teardown) is not the modelled path.
3. `Delivered` is weaker than "every accepted message is dequeued" (mechanised). It is only safe because F4 forbids every reliable message to a terminable actor, and F4 is still the main expressiveness gap.

## Ranked findings

### R3-1 (high) — `FinExec` is empty, so the finite-execution theorems are vacuous
`Rank.lean:11866` `maximal : ∀ a, apply I a (cfg len) = none`. But `Semantics.lean:726`:
```lean
| .stutter => if runtimeBusy I w then none else some w
```
If stutter is disabled, runtimeBusy holds, so some roster recvBulk/recvPrio/exec/finish is enabled, which contradicts maximality. **Mechanised** (`Helen/R3.lean:8`):
```lean
theorem finexec_empty (I : Impl) (N : Nat) (e : FinExec I N) : False   -- [propext, Quot.sound]
```
So `fin_exec_no_blocked` (Progress.lean:596) and `fin_exec_no_wake` (:629) hold trivially for every I, checked or not.
**Fix:** `maximal : runtimeBusy I (cfg len) = false` (equivalently `∀ a, forced a → apply … = none`), and re-prove. The proofs should carry over, because `blocked_progress` already yields a forced action. Alternatively, delete FinExec and cite `blocked_unblocks`.

### R3-2 (high) — Peer timeout = success; untimed peer waits are inexpressible
`Semantics.lean:482-486`:
```lean
| .awaitPeer k =>
  if peerUntimed I.desc id then none else some (setActor w id (proceed (w.st id) k))
```
A timed wait resumes with the **same continuation** as a successful receive, and there is no failure branch. `Graph.lean:596` `peerFails` rejects every `untimedPeer` template.

Amaru evidence: `crates/amaru-protocols/src/mux.rs:489` `read_segment` does
`Network::new(&eff).recv(conn, HEADER_LEADING_EDGE, None)`. This is an **untimed** peer read; only the header remainder uses `Some(sdu_timeout)` (10 s handshake / 30 s established, :53/:55). Failures go through `.or_terminate_with`, i.e. **teardown**, not continuation.

Consequences:
- (a) The Amaru mux reader cannot be described in a checked description.
- (b) For timed reads, the model's "unblocking" passes through a path that in Rust kills the actor.

Is the untimed rejection needed for soundness? No. `blocked_chain` (Chain.lean:1291) already has an "untimed peer at the end of the chain" disjunct, and that is the honest statement: blocked only on the outside world.
**Fix:**
- Allow `untimedPeer`. Classify it as an *external* wait in `Deadlock` (not a deadlock) and keep the disjunct in the headline.
- Give `awaitPeer` two transitions: `peerData` (continue `k`) and `peerTimeout` (run the template's teardown/terminate continuation). The teardown must count as a legal unblocking only if it frees dependants: callers get an error reply and senders are credited. That is exactly F10.

Liveness counterpart: under `Fair`, `deadlock_freedom` + `fair_delivered` give eventual progress modulo environment. With untimed waits allowed, the statement becomes "every blocked chain ends in an outside-world wait", which is the right one.

### R3-3 (medium) — `Delivered` admits a lost accepted message (mechanised); safe only via F4
`Deliver.lean:36`: the bulk clause is
```lean
∀ i id n, n < ((ρ.cfg i).st id).box.length → ∃ j, i ≤ j ∧
  (n < drainDrops ρ id i (fun t => !((ρ.cfg t).st id).box.isEmpty) (j - i) ∨ ((ρ.cfg j).st id).box = [])
```
The `box = []` disjunct is also satisfied when the box is cleared by `terminate`.

**Mechanised** (`Helen/R3.lean:41-156`, lossImpl):
- S Go → send W Start, send W M.
- W Start → internal; terminate.
- The run is `ingress, recvBulk S, exec S, recvBulk W, exec W, exec S, finish W, exec W`, then a quiet stutter.

Theorems:
- `loss_fair : Fair lossRun`
- `m_accepted` (cfg 6: W.box = ["M"])
- `m_dropped` (cfg 8: box = [], W dead)
- `never_received` (no `recvBulk W` at any j ≥ 6)
- `no_drops`
- `delivered_clause_for_lost`: the clause for M holds **only** via `box = []`; drainDrops is 0 for every j.

Scope, honestly stated: lossImpl is **not** LocalOk (`sendsOk`/`stepsCover` fail). More importantly, it can never be made LocalOk with the edges declared: `permanentTarget` (Local.lean:161) forbids reliable send/call to any terminable template, and `receiveIngress` (Semantics.lean:520) refuses terminable targets. So in checked instances, terminable boxes hold only unreliable (droppable) messages, and the disjunct is harmless. The theorem is therefore true but weaker than it reads, and it leans on F4.
Also: Delivered says nothing about the **prio lane** or self-scheduled messages.
**Fix:** tag each message with a unique id (sequence number in `Msg`). State `Delivered` as "every reliable message accepted into box/prio is later the head consumed by recvBulk/recvPrio of that actor", with an explicit exemption for `superseding`/`tryDrop` edge messages. Once F4 is relaxed, add "or the actor terminated *and* the sender got a failure/credit" (F10).

### R3-4 (medium) — F4: no reliable message to terminable / per-peer actors
Still `permanentTarget : t.multiplicity == .one && t.terminable == false` for every reliable send/call edge. In Amaru, per-connection handlers (per-peer, terminated on disconnect) are exactly what the muxer and the miniprotocols send to reliably (mux.rs:846/858; miniprotocol.rs:232/278; connection.rs:252/258). The checked fragment therefore still excludes the actual connection topology. This is the largest remaining model-vs-Amaru gap, and it is coupled to R3-2/R3-3/F10. Relaxing it needs a teardown semantics where a dying actor drains or credits its box and parked senders and fails its pending callers.

### R3-5 (medium) — Ingress shape (N5 + new)
- `reliableTryFails` (Graph.lean:405-408) now requires every ingress edge to be a **self-edge**, and `effectsOk` forbids program `trySend` along ingress edges. Peer→handler delivery in Amaru is mux → handler (a different actor), so it must now be modelled as the handler's own ingress. That loses the mux's bounded buffer and its back-pressure, which is precisely the deadlock-relevant part.
- Ingress is still **idle-only** (Semantics.lean:517). A busy/parked actor never receives environment input, so environment pressure on a blocked chain is never modelled (N5 open).
- `ingressAllowance` evaluates `ingressLegal` at **N = 0** (`.eval 0`, Semantics.lean:495), so a per-peer affine bound `a·N+b` collapses to `max(b,1)`. The `a` coefficient is ignored at runtime. In my chain witness, `ingressLegal {a=1,b=0}` acts as "1 token" for every N.
**Fix:** use `eval w.N`. Allow ingress into non-idle actors (append to box under capacity; that is what Amaru's mailbox does). Allow a declared "environment → X" non-self edge whose source is an abstract environment node with its own budget.

### R3-6 (low) — Fairness is trivial for finite-then-quiet runs; demo_fair is reachability
Any run that reaches a quiet world (runtimeBusy false) and stutters is `Fair`, since all strong/weak obligations are discharged by nothing being enabled. That is what `demo_fair` (FairRun.lean:460) uses, and what my `loss_fair` reuses for an unchecked instance. This is sound, but demo_fair shows "a quiet reachable world exists", not "fairness constrains an infinite environment". No witness has persistent ingress.
**Optional:** a periodic run (ingress every k steps forever) proven Fair would exercise the fairness definitions non-trivially.

### R3-7 (info, positive) — Stutter, OnChain, ChainRun are right
- `runtimeBusy` (Semantics.lean:713) is exactly "some forced action is enabled", given `off_idle_reachable`. **Mechanised**: `blocked_no_stutter` (R3.lean:25). In a checked reachable world, a Blocked actor makes stutter disabled, so a run cannot stutter forever past blocked actors.
- `OnChain` (Progress.lean:44) is
  ```lean
  match actionSubject act with
  | some s => InChain w root s ∧ (match act with | .ingress _ _ => False | .spawn _ => False | .stutter => False | _ => True)
  | none => False
  ```
  and `ChainRun` (Chain.lean:174) requires `OnChain w root a` **at each intermediate world**, with no environment help.
- `blocked_unblocks` ends with `¬ Blocked w' id` in a `Reachable` world: truly unblocked. This is tight.

### R3-8 (info) — Demo coverage, and a stronger kernel witness (supplied)
- demo/park have calls and cells, kernel-checked, and GraphOk/LocalOk are **proved** (`demo_graph_ok`, `demo_local_ok`, `park_*_ok`).
- Before R3.lean there was no height > 1 chain, no per-peer instance, and no termination.
- **Supplied** (`Helen/R3.lean:158-320`, all kernel `decide`):
  - **chainImpl** setup: per-peer P (cap 2N+2, ingress per state with ingressLegal N); P→B "M" occupancy 3N; B cap 1 (mustFit false); B→C "N" occupancy 2; C cap 1. Run with N = 1.
  - `chain_graph_ok : GraphOk chainDesc`, `chain_local : localOkB chainImpl = true`
  - `height_two`: P0 parked on B while B is parked on C
  - `partner_blocked`: B's recvBulk is disabled
  - `chain_witness`: `∃ w w', Reachable chainImpl 1 w ∧ Blocked w P0 ∧ ChainRun chainImpl P0 w [recvBulk C, recvBulk B] ∧ runFrom … = some w' ∧ ¬ Blocked w' P0`
  - Axioms `[propext, Classical.choice, Quot.sound]`.

  Andrew can lift this into Witness.lean as is.
- Still missing: a witness with termination (blocked by F4) and one with a peer wait.

## F1–F11 / N1–N9 status
| ID | Topic | Status @ e16c84b58 |
|---|---|---|
| F1 | vacuity / no stimulus | **fixed** (ingress, spawn; witnesses reachable) |
| F2 | finite-execution statement | **regressed**: FinExec empty (R3-1); liveness covered by deadlock_freedom/fair_delivered |
| F3 | GraphOk/LocalOk unproven on examples | **fixed** (kernel decide) |
| F4 | no reliable sends to terminable/per-peer | **open**, main gap (R3-4) |
| F5 | (round-1) environment/ingress realism | **open** (R3-5) |
| F6/N3 | assumptions / peer waits | **fixed in form** (Assumptions = rust_refines only); timeout-as-success + untimed rejection (R3-2) |
| F7 | (round-1) Rust refinement | **open** (rust_refines is an unproved interface, by design) |
| F8/N8 | (round-1/2) | **fixed** |
| F9/N9 | (round-1/2) | **fixed** |
| F10 | teardown frees dependants | **open**; Delivered's `box=[]` disjunct masks it (R3-3) |
| F11 | (round-1) | **open** |
| N1 | chain-progress theorem | **fixed** (blocked_unblocks, tight) |
| N2 | finite-run theorem | replaced by FinExec, which is **vacuous** (R3-1) |
| N5 | idle-only ingress | **open** (+ N=0 allowance, self-edge rule) |
| N6 | fair run exists | **partial**: only quiet-terminating runs (R3-6) |
| N7 | witness coverage | **improved**; height-2 + per-peer supplied in Helen/R3.lean; termination/peer still missing |

## Target statement I would accept
For `GraphOk ∧ LocalOk` (with F4 relaxed and teardown semantics): in every reachable world, every Blocked actor has a ChainRun to unblocked, **or** its chain ends in an untimed peer wait. Every Fair run delivers every reliable accepted message (by id), or fails/credits it on teardown. `FinExec` (if kept) is maximal w.r.t. forced actions.

## Files
- `/workspace/lean-review-e16c84/REVIEW-helen-e16c84.md` (this)
- `/workspace/lean-review-e16c84/formal/deadlock/Helen/R3.lean`, `Helen/Ax3.lean`
- `/workspace/lean-review-e16c84/build.log`
