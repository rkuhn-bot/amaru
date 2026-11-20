import Deadlock.Basic
import Deadlock.Graph
import Deadlock.Examples
import Deadlock.Failures
import Deadlock.Witness
import Deadlock.Semantics
import Deadlock.Proof
import Deadlock.Local
import Deadlock.Intra
import Deadlock.Theorem
import Deadlock.Compat
import Deadlock.RunInv
import Deadlock.Pres
import Deadlock.Step
import Deadlock.Mail
import Deadlock.Projects
import Deadlock.Occ
import Deadlock.Inv2
import Deadlock.Rank
import Deadlock.Progress
import Deadlock.Chain
import Deadlock.Counter
import Deadlock.FairRun
import Deadlock.Deliver
import Deadlock.Json

#print axioms Deadlock.not_stuck_effect_assumed
#print axioms Deadlock.not_stuck_peer_assumed
#print axioms Deadlock.execRun_preserves_other_run
#print axioms Deadlock.checkBool_sound
#print axioms Deadlock.groupTargets_cooccur
#print axioms Deadlock.compat_group_closed
#print axioms Deadlock.stepBreaks_closed
#print axioms Deadlock.stepsCover_of_local
#print axioms Deadlock.init_tuple_mem
#print axioms Deadlock.findTr_mem
#print axioms Deadlock.semInv_init
#print axioms Deadlock.sem_move
#print axioms Deadlock.enqueue_sem
#print axioms Deadlock.exec_basic_sem
#print axioms Deadlock.exec_done_sem
#print axioms Deadlock.mail_init
#print axioms Deadlock.mail_set_free
#print axioms Deadlock.mail_set_same
#print axioms Deadlock.mail_park_self
#print axioms Deadlock.mail_park_other
#print axioms Deadlock.enqueue_mail
#print axioms Deadlock.mail_of_clear
#print axioms Deadlock.exec_try_sem
#print axioms Deadlock.exec_sched_sem
#print axioms Deadlock.exec_reply_sem
#print axioms Deadlock.exec_cell_sem
#print axioms Deadlock.exec_term_skip_sem
#print axioms Deadlock.exec_term_die_sem
#print axioms Deadlock.deliver_inv
#print axioms Deadlock.receive_prio_inv
#print axioms Deadlock.receive_bulk_inv
#print axioms Deadlock.exec_basic_inv
#print axioms Deadlock.spawn_inv
#print axioms Deadlock.exec_head_inv
#print axioms Deadlock.step_inv
#print axioms Deadlock.inv_init
#print axioms Deadlock.inv_reachable
#print axioms Deadlock.described_park
#print axioms Deadlock.described_reply
#print axioms Deadlock.projects
#print axioms Deadlock.ty_reachable
#print axioms Deadlock.live_le_occ
#print axioms Deadlock.l1_fit
#print axioms Deadlock.l1_park_unreachable
#print axioms Deadlock.occ_init
#print axioms Deadlock.occ_set
#print axioms Deadlock.occ_finish
#print axioms Deadlock.occ_prio
#print axioms Deadlock.occ_bulk
#print axioms Deadlock.occ_enqueue
#print axioms Deadlock.occ_schedule
#print axioms Deadlock.occ_cell
#print axioms Deadlock.occ_spawn
#print axioms Deadlock.occ_try
#print axioms Deadlock.drain_eq_refund
#print axioms Deadlock.drain_eq_refund_park
#print axioms Deadlock.occ_exec
#print axioms Deadlock.inv2_reachable
#print axioms Deadlock.bulk_apply
#print axioms Deadlock.deadlock_kind
#print axioms Deadlock.park_height
#print axioms Deadlock.reply_height
#print axioms Deadlock.call_edge_unterminable
#print axioms Deadlock.await_callee_unterminable
#print axioms Deadlock.release_resumes_send
#print axioms Deadlock.minimal_not_blocked
#print axioms Deadlock.call_program_replies
#print axioms Deadlock.step_keeps_run
#print axioms Deadlock.terminate_commits
#print axioms Deadlock.terminable_no_parked_call
#print axioms Deadlock.inv3_reachable
#print axioms Deadlock.exec_shortens
#print axioms Deadlock.not_forever_run
#print axioms Deadlock.effect_resumes
#print axioms Deadlock.peer_resumes
#print axioms Deadlock.exec_drops
#print axioms Deadlock.reaches_block
#print axioms Deadlock.prio_no_crash
#print axioms Deadlock.declared_le_cap
#print axioms Deadlock.lane_has_room
#print axioms Deadlock.prog_src_reachable
#print axioms Deadlock.schedule_not_crashed
#print axioms Deadlock.lane_schedule
#print axioms Deadlock.lane_reachable
#print axioms Deadlock.reachable_not_crashed
#print axioms Deadlock.bulk_resumes_send
#print axioms Deadlock.bulk_admits_call
#print axioms Deadlock.recv_clears_head_send
#print axioms Deadlock.enqueue_queue
#print axioms Deadlock.queue_place
#print axioms Deadlock.recv_closer
#print axioms Deadlock.alive_queue
#print axioms Deadlock.step_index
#print axioms Deadlock.index_mono
#print axioms Deadlock.queued_forever_false
#print axioms Deadlock.terminate_unblocks
#print axioms Deadlock.only_terminate_kills
#print axioms Deadlock.receiver_stays
#print axioms Deadlock.alive_while_send
#print axioms Deadlock.blocking_next
#print axioms Deadlock.blocking_fuel
#print axioms Deadlock.await_next
#print axioms Deadlock.await_fuel
#print axioms Deadlock.blocking_stays
#print axioms Deadlock.await_stays
#print axioms Deadlock.send_drops_at
#print axioms Deadlock.await_drops_at
#print axioms Deadlock.parked_forever_false
#print axioms Deadlock.mailbox_alive
#print axioms Deadlock.call_below
#print axioms Deadlock.waiting_ty_step
#print axioms Deadlock.parked_typestate_stays
#print axioms Deadlock.send_height_below
#print axioms Deadlock.call_stays
#print axioms Deadlock.call_drops_at
#print axioms Deadlock.call_height_below
#print axioms Deadlock.call_callee_alive
#print axioms Deadlock.idle_when_free
#print axioms Deadlock.send_stuck_false
#print axioms Deadlock.call_parked_stuck_false
#print axioms Deadlock.call_admitted
#print axioms Deadlock.enqueue_parked_mem
#print axioms Deadlock.call_tag_init
#print axioms Deadlock.call_tag_stable
#print axioms Deadlock.finish_tag
#print axioms Deadlock.spawn_tag
#print axioms Deadlock.prio_tag
#print axioms Deadlock.deliver_call
#print axioms Deadlock.credit_tag
#print axioms Deadlock.install_plain
#print axioms Deadlock.install_call
#print axioms Deadlock.bulk_box
#print axioms Deadlock.deliver_parked_send
#print axioms Deadlock.deliver_parked_tag
#print axioms Deadlock.parked_tail_call
#print axioms Deadlock.recvBulk_tag
#print axioms Deadlock.exec_tag
#print axioms Deadlock.call_tag_reachable
#print axioms Deadlock.below_idle
#print axioms Deadlock.never_stuck
#print axioms Deadlock.deadlock_freedom
#print axioms Deadlock.cell_fresh
#print axioms Deadlock.park_graph_ok
#print axioms Deadlock.park_local_ok
#print axioms Deadlock.park_reachable
#print axioms Deadlock.park_unblocks
#print axioms Deadlock.fair_delivered
#print axioms Deadlock.loss_fair
#print axioms Deadlock.loss_not_delivered
#print axioms Deadlock.demo_fair
#print axioms Deadlock.demo_parked
#print axioms Deadlock.demo_awaiting
#print axioms Deadlock.demo_answered
#print axioms Deadlock.demo_woken
#print axioms Deadlock.forced_env_free
