(* Use the specific CTL soundness theorem, avoiding unrelated dispatcher
   dependencies. No framework theorem or source file is modified. *)
From BusyCoq.Eqv363470 Require Import GuardCertificate.

Theorem monitor_guard_nonhalts_direct :
  ~Guard.DHTMFromTM.TM.halts' monitor_guard_tm Guard.DHTMFromTM.TM.c0.
Proof.
  pose proof monitor_guard_decides as H.
  unfold Guard.decide_nonhalt, guard_parameters in H.
  apply Guard.DHTMFromTM.map_nonhalt.
  rewrite <-Guard.CTL_MITMDFA.TM.halts_halts'.
  epose proof (Guard.CTL_MITMDFA.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
  exact H1.
Qed.

Theorem monitor_guard_does_not_halt_direct :
  ~Guard.DHTMFromTM.TM.halts monitor_guard_tm Guard.DHTMFromTM.TM.c0.
Proof.
  rewrite Guard.DHTMFromTM.TM.halts_halts'.
  exact monitor_guard_nonhalts_direct.
Qed.

Print Assumptions monitor_guard_nonhalts_direct.
Print Assumptions monitor_guard_does_not_halt_direct.
