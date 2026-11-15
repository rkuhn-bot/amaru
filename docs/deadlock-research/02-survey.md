# 02 — Survey: approaches to deadlock freedom for bounded, shared-mailbox actor networks

Criteria (from `01`): **FanIn** = handles one bounded mailbox shared by many independent senders;
**Param** = result holds for all `N` (dynamic/parameterised per-peer subtrees); **Inf** = actors that run forever
(no termination-based argument); **Merge** = non-deterministic interleaving of many sessions in one mailbox;
**Bounded** = models capacity-bounded buffers with blocking producers.

Citation status: every bibliographic entry below (authors, title, venue, year, DOI) was checked against Crossref
or the publisher page on 2026-11-15. Content summaries are from the abstracts plus prior knowledge of the papers;
where a claim about content goes beyond the abstract it is marked *(content not re-read)*.

One motivating remark, made once: to our knowledge no production Cardano node has a *proof* of internal
deadlock freedom; "acyclic by design plus simulation testing" is the state of practice, and it is what we want to
go beyond. Nothing below uses another implementation as a model.

---

## A. Interconnection-network deadlock theory (buffer accounting) — **lead**

**Dally & Seitz 1987.** W. J. Dally, C. L. Seitz, *Deadlock-Free Message Routing in Multiprocessor Interconnection
Networks*, IEEE Trans. Computers, 1987. https://doi.org/10.1109/TC.1987.1676939
* Guarantees: a deterministic routing function is deadlock-free iff its **channel dependency graph** (nodes =
  buffers/channels, edge c₁→c₂ if a packet holding c₁ may request c₂) is acyclic. Cycles are broken by splitting
  channels into virtual channels ordered by a global numbering.
* Assumptions: wormhole/store-and-forward routing; finite buffers; packets eventually consumed at destination.
* FanIn: **yes** — a buffer is shared by all packets routed through it; that is exactly the shared-mailbox
  situation. Bounded: yes. Inf: yes (steady-state network). Merge: yes (arbitrary interleaving of packets).
  Param: the condition is a graph property; if the graph is generated from a template the check is on the template.
* Mechanised: Verbeek & Schmaltz, *Proof Pearl: A Formal Proof of Dally and Seitz' Necessary and Sufficient
  Condition for Deadlock-Free Routing in Interconnection Networks*, J. Automated Reasoning 2010.
  https://doi.org/10.1007/s10817-010-9206-x — useful precedent for a machine-checked version.
* **Verdict: adopt as the backbone.** Mapping: channel = stage bulk mailbox; "holding c₁ and requesting c₂" =
  a stage that dequeued from its mailbox and is in a blocking `send`/`call` to another stage. Differences we must
  handle: a stage holds *one* message (its current one) rather than a flit chain; stages perform effects and
  calls; capacity is shared by heterogeneous message kinds.

**Duato 1993/1995.** J. Duato, *A New Theory of Deadlock-Free Adaptive Routing in Wormhole Networks*, IEEE TPDS, 1993, https://doi.org/10.1109/71.250114; *A Necessary and Sufficient Condition for Deadlock-Free Adaptive
Routing in Wormhole Networks*, IEEE TPDS, 1995, https://doi.org/10.1109/71.473515.
Comment on the latter: Verbeek & Schmaltz, IEEE TPDS 2011, https://doi.org/10.1109/TPDS.2011.16.
* Guarantees: cyclic dependencies are allowed if a connected **escape** sub-function has an acyclic extended
  dependency graph and is always available.
* **Verdict: useful as a refinement** for edges that cannot be made non-blocking: if a stage has an alternative
  non-blocking path (escape) that is always eventually usable, a blocking cycle need not deadlock. In our setting
  the "escape" is a credit-reserved slot (§E). Note the 2011 comment shows the 1995 condition needed correction —
  any use must state the exact variant.

**Kahn process networks with bounded buffers.**
G. Kahn, *The Semantics of a Simple Language for Parallel Programming*, IFIP Congress 1974 (no DOI;
*bibliographic data not machine-verified*).
T. M. Parks, *Bounded Scheduling of Process Networks*, PhD thesis, UC Berkeley, Tech. Rep. UCB/ERL M95/105, 1995.
https://www2.eecs.berkeley.edu/Pubs/TechRpts/1995/2926.html
M. Geilen, T. Basten, *Requirements on the Execution of Kahn Process Networks*, ESOP 2003.
https://doi.org/10.1007/3-540-36575-3_22
* Guarantees: Parks shows that imposing buffer bounds on a KPN can introduce **artificial deadlock** (all processes
  blocked, at least one on a *write* to a full buffer) that the unbounded semantics does not have; boundedness and
  termination are undecidable in general; his scheduler grows the smallest full buffer on artificial deadlock.
  Geilen & Basten refine which executions are "correct" for KPNs.
* FanIn: **no** — KPN channels are point-to-point FIFOs with a single writer; determinism of KPNs depends on that.
  Merge: no (KPNs are deterministic). Inf: yes. Bounded: yes. Param: no.
* **Verdict: conceptual foundation for "buffer deadlock vs protocol deadlock"** (our `01` §4) and for buffer
  accounting; the growing-buffer remedy is not available to us (capacities are fixed by design). We cannot reuse the
  determinism results because our mailboxes merge senders.

**Credit-based flow control.** H. T. Kung, T. Blackwell, A. Chapman, *Credit-Based Flow Control for ATM Networks*,
SIGCOMM '94.
https://doi.org/10.1145/190314.190324
* Guarantees: a sender transmits only with a credit for a reserved downstream buffer; no buffer overflow, no
  blocking on a full buffer.
* **Verdict: adopt as the edge-discharge rule** ("credit-bounded edges", `03` §4): if the in-flight messages of
  **all** producers into a mailbox are bounded by credits whose sum fits the capacity, sends into it never park.

## A'. Communication-fabric verification (xMAS) — inductive occupancy invariants

* S. Chatterjee, M. Kishinevsky, U. Y. Ogras, *Quick Formal Modeling of Communication Fabrics to Enable
  Verification*, IEEE HLDVT 2010. https://doi.org/10.1109/HLDVT.2010.5496662 ; journal version *xMAS: Quick Formal
  Modeling of Communication Fabrics to Enable Verification*, IEEE Design & Test of Computers, 2012.
  https://doi.org/10.1109/MDT.2012.2205998 (Crossref also lists https://doi.org/10.1109/MDT.2011.72 for the same
  title, dated 2013; presumably the early-access record — *not resolved which is canonical*).
* S. Chatterjee, M. Kishinevsky, *Automatic Generation of Inductive Invariants from High-Level Microarchitectural
  Models of Communication Fabrics*, CAV 2010, LNCS. https://doi.org/10.1007/978-3-642-14295-6_29 ; extended in
  Formal Methods in System Design, 2012, https://doi.org/10.1007/s10703-011-0134-0
* A. Gotmanov, S. Chatterjee, M. Kishinevsky, *Verifying Deadlock-Freedom of Communication Fabrics*, VMCAI 2011,
  LNCS 6538, pp. 214–231. https://doi.org/10.1007/978-3-642-18275-4_16
* F. Verbeek, J. Schmaltz, *Hunting Deadlocks Efficiently in Microarchitectural Models of Communication Fabrics*,
  FMCAD 2011, pp. 223–231 (FMCAD Inc.; ACM DL https://dl.acm.org/doi/10.5555/2157654.2157688 ; IEEE Xplore
  document 6148903; PDF https://www.cs.utexas.edu/~hunt/FMCAD/fmcad11/papers/34.pdf)
* Content (from the abstracts/introductions, checked 2026-11-15): xMAS is a small set of primitives (queues, forks,
  joins, switches, merges, sources, sinks) for microarchitectural models of on-chip fabrics. Chatterjee & Kishinevsky
  automatically strengthen properties into one-step **inductive invariants** (relations between queue occupancies)
  from the high-level model. Gotmanov et al. reduce deadlock freedom, under restrictions, to **unsatisfiability of
  Boolean equations** over "a queue is permanently full/empty" predicates, using those invariants. Verbeek & Schmaltz
  capture wait-for relations in a **labelled waiting graph** and characterise a deadlock as a feasible closed
  subgraph; they target message-dependent deadlocks in networks with thousands of queues.
* FanIn: yes (merges into shared bounded queues). Bounded: yes. Merge: yes. Inf: yes. Param: no (fixed netlists,
  but very large). Effects/actors/calls: no.
* **Verdict: closest prior art for Lemma 1 and Lemma 4.** Their occupancy invariants are our credit bounds, derived
  automatically from structure; their "feasible closed subgraph" is the exact (necessary and sufficient) version of
  our sufficient acyclicity check. Worth adopting as a technique for the extractor: derive occupancy invariants from
  the typestate graph rather than hand-proving them.

## B'. CSP/occam design rules for deadlock freedom

* A. W. Roscoe, N. Dathi, *The Pursuit of Deadlock Freedom*, Information and Computation 75(3):289–327, 1987
  (volume/pages from the Oxford bibliography). https://doi.org/10.1016/0890-5401(87)90004-6 ; technical report
  PRG-57, https://www.cs.ox.ac.uk/files/3379/PRG57.pdf
  * Content (checked in the PRG-57 text): assign each process a **variant function** from its states into a
    partial order; if whenever `P_i` has an ungranted request to `P_j` the variant of `P_i` is strictly greater
    than that of `P_j`, the (finite, busy, triple-disjoint) network is deadlock-free; the condition can be checked
    on pairs of processes ("Rule 1", hereditary). Our Lemma 4 heights are such a variant function.
* P. H. Welch, G. R. R. Justo, C. J. Willcock, *Higher-Level Paradigms for Deadlock-Free High-Performance Systems*,
  in Transputer Applications and Systems '93 (Proc. 1993 World Transputer Congress), vol. 2, IOS Press, 1993.
  https://kar.kent.ac.uk/21094/ (no DOI). Page numbers differ between sources (Kent publication page: 182–196;
  KAR record: 981–1004) — *not resolved*.
  * Content (checked in the KAR PDF): I/O-PAR and Client–Server paradigms for **synchronised** message passing;
    "Client–Server Theorem: any network of client–server connections that is acyclic with respect to the
    client–server ordering is deadlock/livelock free", with servers required to accept and respond; checking is
    `O(n²)` in the number of processes instead of exponential in states.
* J. M. R. Martin, *The Design and Construction of Deadlock-Free Concurrent Systems*, DPhil thesis, University of
  Buckingham, 1996. https://www.wotug.org/docs/jeremy-martin/thesis.pdf ; republished by University of Buckingham
  Press, 2024, https://doi.org/10.5750/ubpob.8
  * Content (abstract and table of contents): catalogues design rules that eliminate deadlock (formalised in CSP,
    building on Roscoe and Welch), and a tool that proves deadlock freedom by checking adherence to them.
* FanIn: yes (shared servers). Bounded: no — channels are synchronous (capacity 0), so buffer accounting does not
  arise. Merge: yes (servers accept from many clients). Inf: yes. Param: rules are compositional, so they scale, but
  no parameterised-topology theorem as such.
* **Verdict: the direct ancestor of Theorem A.** Theorem A is the client–server rule (acyclic residual
  client→server edges + H4 "servers always answer") lifted to buffered shared mailboxes, with credit-discharged
  backward edges, superseding edges, state-dependent variants, effects/internal calls, and a template graph
  (positioning in `03` §4).

---

## B. Classical deadlock theory

* E. G. Coffman, M. Elphick, A. Shoshani, *System Deadlocks*, ACM Computing Surveys, 1971.
  https://doi.org/10.1145/356586.356588 — four necessary conditions (mutual exclusion, hold-and-wait, no
  preemption, circular wait). Our blocking `send` is hold-and-wait on mailbox slots; acyclicity attacks circular
  wait. **Verdict: framing only.**
* K. M. Chandy, J. Misra, L. M. Haas, *Distributed Deadlock Detection*, ACM TOCS, 1983.
  https://doi.org/10.1145/357360.357365 — runtime wait-for-graph detection (AND/OR models). **Verdict: runtime
  complement** (the simulation's `send_cycle` is a centralised version); detection is not a proof.

---

## C. Communicating automata and asynchronous multiparty session types

* D. Brand, P. Zafiropulo, *On Communicating Finite-State Machines*, JACM, 1983.
  https://doi.org/10.1145/322374.322380 — CFSMs with unbounded FIFO channels are Turing-powerful; most
  properties undecidable. Background for why per-system exhaustive checks need bounds.
* P.-M. Deniélou, N. Yoshida, *Multiparty Compatibility in Communicating Automata: Characterisation and Synthesis of
  Global Session Types*, ICALP 2013. https://doi.org/10.1007/978-3-642-39212-2_18
* J. Lange, N. Yoshida, *Verifying Asynchronous Interactions via Communicating Session Automata*, CAV 2019,
  LNCS 11561. https://doi.org/10.1007/978-3-030-25540-4_6 (k-MC; tool `kmc`).
* A. Bouajjani, C. Enea, K. Ji, S. Qadeer, *On the Completeness of Verifying Message Passing Programs Under
  Bounded Asynchrony*, CAV 2018. https://doi.org/10.1007/978-3-319-96142-2_23
* M. Coppo, M. Dezani-Ciancaglini, N. Yoshida, L. Padovani, *Global Progress for Dynamically Interleaved
  Multiparty Sessions*, Mathematical Structures in Computer Science, 2014 (Crossref date). https://doi.org/10.1017/S0960129514000188
* Guarantees: safety/progress for a fixed set of finite-state participants, communicating over **per-pair FIFO
  channels**; k-MC checks k-bounded executions; synchronizability results relate bounded to unbounded behaviour.
  Coppo et al. address progress when sessions interleave in one process (*content not re-read*: via an
  interaction-type analysis over session names).
* FanIn: **no** — channels are per ordered pair; a bounded buffer shared by unrelated senders is not modelled.
  Merge: partially (Coppo et al.). Param: no. Inf: yes for recursive types. Bounded: k-bounded, per pair.
* **Verdict: not the lead tool.** Keep for *per-protocol* conformance (as the existing BlockFetch typestate
  projection does). Coppo et al. is the closest MPST work to "many sessions interleaved in one actor" and should
  be read in full for its progress argument.

## D. Parameterised / dynamic MPST and choreographies

* P.-M. Deniélou, N. Yoshida, A. Bejleri, R. Hu, *Parameterised Multiparty Session Types*, LMCS, 2012.
  https://doi.org/10.2168/LMCS-8(4:6)2012
* P.-M. Deniélou, N. Yoshida, *Dynamic Multirole Session Types*, POPL 2011.
  https://doi.org/10.1145/1926385.1926435
* N. Ng, N. Yoshida, *Pabble: Parameterised Scribble*, Service Oriented Computing and Applications, 2014.
  https://doi.org/10.1007/s11761-014-0172-8
* D. Castro, R. Hu, S.-S. Jongmans, N. Ng, N. Yoshida, *Distributed Programming Using Role-Parametric Session Types
  in Go*, POPL 2019 (PACMPL). https://doi.org/10.1145/3290342
* R. Hu, N. Yoshida, *Explicit Connection Actions in Multiparty Session Types*, FASE 2017.
  https://doi.org/10.1007/978-3-662-54494-5_7
* D. Castro-Perez, F. Ferreira, L. Gheri, N. Yoshida, *Zooid: a DSL for Certified Multiparty Computation*,
  PLDI 2021. https://doi.org/10.1145/3453483.3454041
* M. Dalla Preda, M. Gabbrielli, S. Giallorenzo, I. Lanese, J. Mauro, *Dynamic Choreographies: Theory and
  Implementation*, LMCS, 2017. https://doi.org/10.23638/LMCS-13(2:1)2017
* L. Cruz-Filipe, F. Montesi, *A Core Model for Choreographic Programming*, TCS, 2020.
  https://doi.org/10.1016/j.tcs.2019.07.005
* Guarantees: deadlock freedom/progress by construction for programs projected from a global description;
  parameterised/indexed roles (Pabble, role-parametric Go) and dynamic joining (multirole, connection actions)
  give Param for *one* global protocol. Zooid gives mechanised (Coq) projection correctness.
* FanIn: **no** (asynchrony is unbounded or per pair). Merge: no — the global type fixes the order. Inf: yes.
* **Verdict: does not fit the core problem** (no single global type; capacity is shared). Role-indexed families
  are a good *notation* for the per-peer template in the Amaru instantiation, and Zooid is a model for how to
  mechanise a projection-based argument if we ever do so.

## E. Priority / level-based type systems for deadlock freedom

* N. Kobayashi, *A New Type System for Deadlock-Free Processes*, CONCUR 2006.
  https://doi.org/10.1007/11817949_16
* L. Padovani, *Deadlock and Lock Freedom in the Linear π-Calculus*, CSL-LICS 2014.
  https://doi.org/10.1145/2603088.2603116
* O. Dardha, S. J. Gay, *A New Linear Logic for Deadlock-Free Session-Typed Processes*, FoSSaCS 2018,
  LNCS 10803. https://doi.org/10.1007/978-3-319-89366-2_5
* W. Kokke, O. Dardha, *Deadlock-Free Session Types in Linear Haskell*, Haskell Symposium 2021.
  https://doi.org/10.1145/3471874.3472979 ; *Prioritise the Best Variation*, FORTE 2021,
  https://doi.org/10.1007/978-3-030-78089-0_6, extended LMCS, 2023, https://doi.org/10.46298/lmcs-19(4:28)2023
* B. Toninho, N. Yoshida, *Interconnectability of Session-Based Logical Processes*, TOPLAS, 2018.
  https://doi.org/10.1145/3242173
* N. Kobayashi, C. Laneve, *Deadlock Analysis of Unbounded Process Networks*, Information and Computation,
  2017. https://doi.org/10.1016/j.ic.2016.03.004 (conf. version Giachino, Kobayashi, Laneve, CONCUR 2014,
  https://doi.org/10.1007/978-3-662-44584-6_6)
* Guarantees: every blocking action carries a **priority/level**; well-typed processes only block in increasing
  order, so no circular wait. Obligations/capabilities (Kobayashi) also give lock freedom (every pending
  communication eventually happens). Kobayashi & Laneve handle networks whose size grows unboundedly (recursive
  process creation) *(content not re-read: via finite abstraction of lams/dependency graphs)*.
* FanIn: indirectly — channels can be shared, but capacity is not a typed resource. Param: Kobayashi & Laneve,
  yes. Inf: yes. Merge: yes.
* **Verdict: this is the typed form of our theorem.** "Every blocking edge goes up in a global order" ⇔ "the
  blocking subgraph is acyclic". Useful later if we want the check to be compositional per stage (each stage
  declares the level of its mailbox; the checker verifies its blocking sends only go to higher levels).
  Obligations are the right tool for *call-reply* waits (a pending reply is an obligation of the callee).

## F. Mailbox types and actor deadlock analyses

* U. de'Liguoro, L. Padovani, *Mailbox Types for Unordered Interactions*, ECOOP 2018, LIPIcs vol. 109.
  https://doi.org/10.4230/LIPIcs.ECOOP.2018.15 (TR: https://arxiv.org/abs/1801.04167)
* S. Fowler, D. P. Attard, F. Sowul, S. J. Gay, P. Trinder, *Special Delivery: Programming with Mailbox Types*,
  ICFP 2023 (PACMPL). https://doi.org/10.1145/3607832
* E. Giachino, C. Laneve, M. Lienhardt, *A Framework for Deadlock Detection in core ABS*, SoSyM, 2015 (Crossref date). https://doi.org/10.1007/s10270-014-0444-y
* A. Flores-Montoya, E. Albert, S. Genaim, *May-Happen-in-Parallel Based Deadlock Analysis for Concurrent
  Objects*, FMOODS/FORTE 2013. https://doi.org/10.1007/978-3-642-38592-6_19
* M. Christakis, K. Sagonas, *Detection of Asynchronous Message Passing Errors Using Static Analysis*, PADL 2011,
  LNCS 6539. https://doi.org/10.1007/978-3-642-18378-2_3
* S. Clebsch, S. Drossopoulou, S. Blessing, A. McNeil, *Deny Capabilities for Safe, Fast Actors*, AGERE 2015.
  https://doi.org/10.1145/2824815.2824816 (Pony; data-race freedom, not deadlock — listed to rule it out).
* Guarantees: mailbox types give deadlock and protocol conformance for actors with **unbounded**, unordered
  mailboxes and dynamic topologies; ABS analyses detect cycles of `await`/`get` on futures between objects (the
  analogue of our `call` reply waits) with MHP or behavioural types; Christakis & Sagonas find receive-without-
  matching-send in Erlang.
* FanIn: yes (mailbox = many senders), Merge: yes, Param: yes (mailbox types, dynamic). **Bounded: no** —
  sends never block in these models, so buffer deadlock does not exist there.
* **Verdict:** relevant for *call-reply* and protocol deadlock (ABS future waits ≈ our `call`), and as evidence that
  shared-mailbox actor deadlock analysis is tractable; they do not cover capacity. Our blocking-send edges are the
  piece they lack, which is why section A leads.

## G. Parameterised verification and cutoffs

* S. M. German, A. P. Sistla, *Reasoning about Systems with Many Processes*, JACM, 1992.
  https://doi.org/10.1145/146637.146681
* M. C. Browne, E. M. Clarke, O. Grumberg, *Reasoning about Networks with Many Identical Finite State Processes*,
  Information and Computation, 1989. https://doi.org/10.1016/0890-5401(89)90026-6
* E. A. Emerson, K. S. Namjoshi, *Reasoning about Rings*, POPL 1995. https://doi.org/10.1145/199448.199468
* E. A. Emerson, V. Kahlon, *Reducing Model Checking of the Many to the Few*, CADE-17, 2000.
  https://doi.org/10.1007/10721959_19
* R. Bloem, S. Jacobs, A. Khalimov, I. Konnov, S. Rubin, H. Veith, J. Widder, *Decidability of Parameterized
  Verification*, Synthesis Lectures on Distributed Computing Theory, Morgan & Claypool, 2015.
  https://doi.org/10.1007/978-3-031-02011-7 (survey: *Decidability in Parameterized Verification*, SIGACT News
  2016, https://doi.org/10.1145/2951860.2951873)
* Guarantees: for symmetric systems of a controller plus `N` identical finite-state user processes, many
  properties reduce to a finite cutoff `N₀` (German–Sistla: one controller, `N` users, rendezvous; Emerson–Kahlon:
  guarded/conjunctive/disjunctive systems with small cutoffs). Deadlock detection is *harder* than safety in this
  setting and cutoffs often do not exist or are large *(content not re-read: Bloem et al. survey chapter on
  deadlock)*.
* FanIn: yes (controller receives from all). Bounded: buffers must be encoded as finite state. Param: yes. Inf: yes.
* **Verdict: fallback for residual cycles only.** Our main theorem needs no cutoff because it is a property of the
  quotient (template) graph. If a blocking cycle through core and template must be kept, a cutoff argument is
  needed, and it must parameterise over capacity `c` too (a full mailbox of capacity `c` needs about `c` distinct
  producers). We do not yet have a proven cutoff; see `03` §7.

## H. Workflow formalisms

* T. T. Hildebrandt, R. R. Mukkamala, *Declarative Event-Based Workflow as Distributed Dynamic Condition Response
  Graphs*, PLACES 2010, EPTCS 69, 2011. https://doi.org/10.4204/EPTCS.69.5
* T. Hildebrandt, R. R. Mukkamala, T. Slaats, *Nested Dynamic Condition Response Graphs*, FSEN 2011,
  2012. https://doi.org/10.1007/978-3-642-29320-7_23
* Guarantees: declarative constraints between events (condition, response, include/exclude); liveness =
  pending responses eventually done; nesting gives sub-processes.
* FanIn/Bounded: no notion of buffer capacity. **Verdict: not applicable** to buffer deadlock. Could describe
  per-peer lifecycle constraints (connect → handshake → protocols → teardown), but that is not our bottleneck.

## I. Channel-based languages (closest practical precedent)

* J. Lange, N. Ng, B. Toninho, N. Yoshida, *Fencing off Go: Liveness and Safety for Channel-Based Programming*,
  POPL 2017. https://doi.org/10.1145/3009837.3009847
* Guarantees: infer behavioural types from Go programs (with **bounded channel capacities**) and model-check
  liveness/safety on finite-control abstractions *(content not re-read: fencing restricts recursion to keep the
  state space finite)*.
* FanIn: yes (Go channels are many-to-many and bounded). Param: no (fenced). Inf: yes.
* **Verdict: closest existing tool chain to "extract a model from code, check bounded channels"**; useful as a
  model-checking backend for residual SCCs of fixed size, not for the all-`N` result.

---

## Protocol specification used as a normative source

* D. Coutts, N. Davies, M. Fontaine, K. Knutsson, A. Santos, M. Szamotulski, A. Vieth, *Ouroboros Network
  Specification* (also referred to as "The Shelley Networking Protocol"), technical specification, version dated
  10 November 2026, https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf. Used for the
  mini-protocol state machines (agency, `StIdle`, `StDone`; Chain-Sync §3.7.2, Fig. 3.1; Tx-Submission §3.9.1:
  "`MsgDone` Termination message, initiated by the client when the server is making a blocking call for more
  transaction identifiers"; pipelining §3.15: the server "can simply follow the state machine of the protocol and
  process the messages in turn"). Title, authors, date and quotations verified against the PDF front page and text.
  It is a specification, not an implementation, so citing it does not violate the rule that the Haskell node is not an authority.

## Summary table

| Approach | FanIn | Bounded | Param N | Infinite | Merge | Use |
|---|---|---|---|---|---|---|
| Dally–Seitz CDG | yes | yes | via template graph | yes | yes | **backbone** |
| xMAS occupancy invariants / waiting graphs | yes | yes | no | yes | yes | technique for Lemmas 1, 4 |
| Roscoe–Dathi variants, client–server rule | yes | no (sync) | compositional | yes | yes | **ancestor of Theorem A** |
| Duato escape | yes | yes | via template | yes | yes | refinement for kept cycles |
| KPN bounded (Parks) | no | yes | no | yes | no | buffer vs protocol deadlock; accounting |
| Credit flow control | yes | yes | yes (sum of credits) | yes | yes | **edge discharge rule** |
| CFSM / k-MC / synchronizability | no | per pair | no | yes | partly | per-protocol conformance only |
| Param./dynamic MPST, choreographies | no | no | yes | yes | no | notation for templates |
| Priority/obligation types | partly | no | Kobayashi–Laneve | yes | yes | typed form of theorem; call obligations |
| Mailbox types, ABS | yes | **no** | yes | yes | yes | call/reply & protocol deadlock |
| Cutoffs (German–Sistla etc.) | yes | encoded | yes | yes | yes | residual cycles only |
| DCR graphs | no | no | nested | yes | – | not applicable |
| Go behavioural types | yes | yes | no | yes | yes | model-checking backend |

**Gap in the literature as found (narrowed):** among the surveyed works, none combines *all* of: blocking,
capacity-bounded mailboxes shared by many senders; actors that perform effects; internal calls with timeouts that
must not count as liveness; a parameterised, dynamically changing topology; and a result checked once on a template
graph. Each ingredient exists separately: buffer accounting and occupancy invariants (Dally–Seitz, Parks, xMAS),
order/variant-based rules for synchronous processes (Roscoe–Dathi, client–server, Kobayashi), actor and mailbox
analyses with non-blocking sends (mailbox types, ABS), and parameterised verification (cutoffs). `03` combines them;
it is a synthesis, not a new kind of argument. (This is a statement about the works surveyed here, not an
exhaustive literature claim.)
