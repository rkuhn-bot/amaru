import Deadlock.Basic
import Deadlock.Graph
import Deadlock.Examples
import Deadlock.Semantics
import Deadlock.Proof
import Deadlock.Local
import Deadlock.Theorem
import Deadlock.Compat
import Deadlock.RunInv
import Deadlock.Pres
import Deadlock.Step
import Deadlock.Mail

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
