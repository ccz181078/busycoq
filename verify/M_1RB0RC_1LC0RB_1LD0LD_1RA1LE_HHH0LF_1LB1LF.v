(* 1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF does not halt from the blank tape.

   busycoq already decides the same transition table started in two other states (NG_v1.v, nonhalt12951 and
   nonhalt13144, after renaming and mirroring). Their n-gram closed tape language search does not close from the
   blank start of this machine directly. It does close once the run has settled: run the tape-history machine
   (every cell keeps its recent (state, symbol) visits, exactly as in the NG decider with asth = true) for simT
   steps from the blank start, then start busycoq's CTL_NG_QSym search from the configuration reached, histories
   included. The NG decider in CTL.v instead runs the plain machine for simT steps and then starts the search with
   every history empty; with the parameters used below it returns false here for simT = 0, 30000 and 100000. *)

From BusyCoq Require Import CTL62.

Definition hist_decide (tm: DHTMFromTM.TM.TM) (simT maxT maxS NG_n len1 len2 LRU_n: N) : bool :=
  let upd := TapeHistoryImpl.QSym_history_upd (N.to_nat len1) (N.to_nat len2) (N.to_nat LRU_n) in
  let tm1 := TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm upd in
  match TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.DH_cconfig_steps tm1
          TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.cc0 simT with
  | inl c1 =>
      let cfg := {| Ctx_NG_QSym.CTLCtx.len := N.to_nat NG_n;
                    Ctx_NG_QSym.CTLCtx.maxS := N_to_int maxS |} in
      CTL_NG_QSym.CTL_decide_nonhalt tm1 c1 cfg (N_to_int maxS) (maxT*100)
  | inr _ => false
  end.

Lemma hist_decide_spec tm simT maxT maxS NG_n len1 len2 LRU_n:
  hist_decide tm simT maxT maxS NG_n len1 len2 LRU_n = true ->
  ~DHTMFromTM.TM.halts' tm DHTMFromTM.TM.c0.
Proof.
  unfold hist_decide. intros H.
  apply DHTMFromTM.map_nonhalt.
  apply (TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.inv_map_nonhalt_c0 tm
    (TapeHistoryImpl.QSym_history_upd (N.to_nat len1) (N.to_nat len2) (N.to_nat LRU_n))).
  pose proof (TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.DH_cconfig_steps_spec
    (TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm
      (TapeHistoryImpl.QSym_history_upd (N.to_nat len1) (N.to_nat len2) (N.to_nat LRU_n)))
    TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.cc0 simT) as H0.
  destruct (TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.DH_cconfig_steps
    (TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.map_TM tm
      (TapeHistoryImpl.QSym_history_upd (N.to_nat len1) (N.to_nat len2) (N.to_nat LRU_n)))
    TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.cc0 simT); try congruence.
  rewrite <-TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.halts_halts'.
  eapply TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.evstep_nonhalt; eauto. clear H0.
  epose proof (CTL_NG_QSym.CTL_decide_nonhalt_spec _ _ _ _ _ H) as H1.
  rewrite CTL_NG_QSym.TM.halts_halts' in H1.
  rewrite TapeHistoryImpl.ListQSymTapeHistoryTMFromDHTM.TapeHistoryTM.halts_halts'.
  exact H1.
Qed.

Definition tm := TM_from_str "1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF".

Theorem nonhalt: ~halts tm c0.
Proof.
  rewrite halts_halts'.
  eapply (hist_decide_spec _ 30000 30000 30000 3 12 2 0).
  vm_cast_no_check (eq_refl true).
Time Qed.

Print Assumptions nonhalt.
