(* Exact source-machine embedding for original815 row9. *)
From BusyCoq Require Import Individual62 Row9Eval.
Require Import Lia List String PeanoNat.
Import ListNotations.
Open Scope list.

Module Row9Raw.
Definition tm := TM_from_str "1RB0LA_0RC1LE_0RD1RE_1LA1RF_1RB0LD_1RC---".
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint word_tape (w : list nat) : side :=
  match w with
  | [] => 1 >> const 0
  | g::u => 1 >> [0]^^g *> 1 >> 0 >> word_tape u
  end.
Definition reset (l : side) (w : list nat) :=
  l <* [1;0;1] {{B}}> word_tape w.
Definition scan (k : nat) (l : side) (w : list nat) :=
  l <* [0] <* [1]^^(2+k) {{C}}> word_tape w.

Lemma word_tape_head w : exists r, word_tape w = 1 >> r.
Proof. destruct w; cbn; eauto. Qed.

Lemma a_sweep l r n :
  l <* [0] <* [1]^^n <{{A}} r -->+
  l <* [1] {{B}}> [0]^^n *> r.
Proof.
  revert l r. induction n; intros.
  - es.
  - replace (S n) with (n+1)%nat by lia.
    rewrite !lpow_add. cbn. simpl_tape.
    step. specialize (IHn l (0 >> r)). rewrite lpow_shift1 in IHn. exact IHn.
Qed.

Lemma carry l w k :
  reset (l <* [0] <* [1]^^(2+k)) w -->+ reset l (k::w).
Proof.
  destruct (word_tape_head w) as [r E].
  unfold reset. cbn [word_tape]. rewrite E.
  mid10 (l <* [0] <* [1]^^(3+k) <{{A}} 1 >> 0 >> 1 >> r).
  - replace (3+k)%nat with ((2+k)+1)%nat by lia.
    rewrite lpow_add. es.
  - eapply evstep_trans; [apply progress_evstep; apply a_sweep|]. es.
Qed.

Lemma short_even l w :
  reset (l <* [0]) w -->+ scan 0 (l <* [1]) w.
Proof. destruct (word_tape_head w) as [r E]. unfold reset,scan; rewrite E. es. Qed.
Lemma short_one l w :
  reset (l <* [1;0]) w -->+ scan 0 (l <* [0;1]) w.
Proof. destruct (word_tape_head w) as [r E]. unfold reset,scan; rewrite E. es. Qed.

Lemma scan_one k l u :
  scan k l (1%nat::u) -->+ scan (k+4) l u.
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (2+(k+4))%nat with ((2+k)+4)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_two k l u :
  scan k l (2%nat::u) -->+ scan 0 (l <* [0] <* [1]^^(4+k)) u.
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_three k l u :
  scan k l (3%nat::u) -->+ scan 0 (l <* [0] <* [1]^^(4+k) <* [0]) u.
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_zero_one k l u :
  scan k l (0%nat::1%nat::u) -->+ scan 2 (l <* [0] <* [1]^^(4+k)) u.
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_zero_two k l u :
  scan k l (0%nat::2%nat::u) -->+
  scan 0 (l <* [0] <* [1]^^(4+k) <* [1;1;0]) u.
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_zero_large k l g u :
  scan k l (0%nat::S(S(S g))::u) -->+
  scan 1 (l <* [0] <* [1]^^(4+k)) (g::u).
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E.
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_zero k l :
  scan k l [0%nat] -->+ scan 1 (l <* [0] <* [1]^^(4+k)) [].
Proof.
  unfold scan; cbn [word_tape].
  replace (4+k)%nat with ((2+k)+2)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_large k l g u :
  scan k l (S(S(S(S g)))::u) -->+
  reset (l <* [0] <* [1]^^(3+k)) (g::u).
Proof.
  destruct (word_tape_head u) as [r E].
  unfold scan,reset; cbn [word_tape]; rewrite E.
  replace (3+k)%nat with ((2+k)+1)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_nil k l :
  scan k l [] -->+ reset (l <* [0] <* [1]^^(3+k)) [].
Proof.
  unfold scan,reset; cbn [word_tape].
  replace (3+k)%nat with ((2+k)+1)%nat by lia.
  rewrite lpow_add. es.
Qed.
Lemma scan_zero_zero k l u : halts tm (scan k l (0%nat::0%nat::u)).
Proof. destruct (word_tape_head u) as [r E].
  unfold scan; cbn [word_tape]; rewrite E. solve_halt. Qed.

Lemma first_plus_0 w : first_plus 0 w = w.
Proof. destruct w; cbn; [reflexivity|]. now rewrite Nat.add_0_r. Qed.
Lemma first_plus_comp k j w :
  first_plus k (first_plus j w) = first_plus (j+k) w.
Proof. destruct w; cbn; [reflexivity|]. f_equal. lia. Qed.

Lemma scan_nil_return k l :
  scan k l [] -->+ reset l [(1+k)%nat].
Proof.
  eapply progress_trans; [apply scan_nil|].
  change (reset (l <* [0] <* [1]^^(2+(1+k))) [] -->+
          reset l ((1+k)%nat::[])).
  apply carry.
Qed.
Lemma scan_large_return k l g u :
  scan k l (S(S(S(S g)))::u) -->+ reset l ((1+k)%nat::g::u).
Proof.
  eapply progress_trans; [apply scan_large|].
  change (reset (l <* [0] <* [1]^^(2+(1+k))) (g::u) -->+
          reset l ((1+k)%nat::g::u)).
  apply carry.
Qed.

Definition embedded_result k l u r :=
  match r with
  | Some v => scan k l u -->+ reset l (first_plus k v)
  | None => halts tm (scan k l u)
  end.

Theorem eval_embedding u r (H : Eval u r) :
  forall k l, embedded_result k l u r.
Proof.
  induction H; intros k l; unfold embedded_result in *.
  - cbn. apply scan_nil_return.
  - destruct r as [v|]; cbn in *.
    + rewrite first_plus_comp.
      replace (4+k)%nat with (k+4)%nat by lia.
      eapply progress_trans; [apply scan_one|]. apply IHEval.
    + eapply halts_evstep; [apply IHEval|].
      apply progress_evstep,scan_one.
  - destruct r as [v|]; cbn in *.
    + eapply progress_trans; [apply scan_two|].
      specialize (IHEval 0%nat (l <* [0] <* [1]^^(4+k))).
      rewrite first_plus_0 in IHEval.
      eapply progress_trans; [exact IHEval|]. apply carry.
    + eapply halts_evstep; [apply IHEval|].
      apply progress_evstep,scan_two.
  - eapply halts_evstep; [apply IHEval|].
    apply progress_evstep,scan_three.
  - specialize (IHEval1 0%nat (l <* [0] <* [1]^^(4+k) <* [0])).
    rewrite first_plus_0 in IHEval1.
    destruct r as [v|]; cbn in *.
    + eapply progress_trans; [apply scan_three|].
      eapply progress_trans; [exact IHEval1|].
      eapply progress_trans; [apply short_even|].
      specialize (IHEval2 0%nat (l <* [0] <* [1]^^(4+k) <* [1])).
      rewrite first_plus_0 in IHEval2.
      eapply progress_trans; [exact IHEval2|].
      change (reset (l <* [0] <* [1]^^(2+(3+k))) v -->+
              reset l ((3+k)%nat::v)). apply carry.
    + eapply halts_evstep; [apply IHEval2|].
      apply progress_evstep.
      eapply progress_trans; [apply scan_three|].
      eapply progress_trans; [exact IHEval1|]. apply short_even.
  - cbn. apply scan_large_return.
  - cbn. eapply progress_trans; [apply scan_zero|].
    eapply progress_trans; [apply scan_nil_return|].
    apply carry.
  - apply scan_zero_zero.
  - destruct r as [v|]; cbn in *.
    + eapply progress_trans; [apply scan_zero_one|].
      eapply progress_trans; [apply IHEval|]. apply carry.
    + eapply halts_evstep; [apply IHEval|].
      apply progress_evstep,scan_zero_one.
  - destruct r as [v|]; cbn in *.
    + eapply progress_trans; [apply scan_zero_two|].
      specialize (IHEval 0%nat (l <* [0] <* [1]^^(4+k) <* [1;1;0])).
      rewrite first_plus_0 in IHEval.
      eapply progress_trans; [exact IHEval|].
      eapply progress_trans with (c':=reset (l <* [0] <* [1]^^(4+k)) (0%nat::v)).
      * apply (carry (l <* [0] <* [1]^^(4+k)) v 0%nat).
      * apply carry.
    + eapply halts_evstep; [apply IHEval|].
      apply progress_evstep,scan_zero_two.
  - destruct r as [v|]; cbn in *.
    + eapply progress_trans; [apply scan_zero_large|].
      eapply progress_trans; [apply IHEval|]. apply carry.
    + eapply halts_evstep; [apply IHEval|].
      apply progress_evstep,scan_zero_large.
Qed.

Corollary f_embedding u : forall k l,
  match f u with
  | Some v => scan k l u -->+ reset l (first_plus k v)
  | None => halts tm (scan k l u)
  end.
Proof. exact (eval_embedding u (f u) (f_spec u)). Qed.

Lemma init : c0 -->+ reset (const 0) [].
Proof. unfold reset; cbn [word_tape]. es. Qed.
Lemma short_initial w :
  reset (const 0) w -->+ scan 0 (const 0 <* [1]) w.
Proof.
  pose proof (short_even (const 0) w) as H.
  cbn [Str_app] in H. rewrite <-const_unfold in H. exact H.
Qed.
Lemma short_second w :
  reset (const 0 <* [1]) w -->+ scan 0 (const 0 <* [0;1]) w.
Proof.
  pose proof (short_one (const 0) w) as H.
  cbn [Str_app] in H. rewrite <-const_unfold in H. exact H.
Qed.
Lemma short_third w :
  reset (const 0 <* [0;1]) w -->+ scan 0 (const 0 <* [1;1]) w.
Proof. exact (short_even (const 0 <* [1]) w). Qed.
Lemma phase_carry w :
  reset (const 0 <* [1;1]) w -->+ reset (const 0) (0%nat::w).
Proof.
  pose proof (carry (const 0) w 0%nat) as H.
  cbn [lpow Str_app Nat.add] in H. rewrite <-const_unfold in H. exact H.
Qed.

Definition phase3 (w : word) : result :=
  Row9Eval.bind (f w) (fun u => Row9Eval.bind (f u) (fun v => lift_prefix [0%nat] (f v))).

Theorem phase3_embedding w :
  match phase3 w with
  | Some v => reset (const 0) w -->+ reset (const 0) v
  | None => halts tm (reset (const 0) w)
  end.
Proof.
  unfold phase3. pose proof (f_embedding w 0%nat (const 0 <* [1])) as H1.
  destruct (f w) as [u|] eqn:E1; cbn [Row9Eval.bind] in *.
  - rewrite first_plus_0 in H1.
    pose proof (f_embedding u 0%nat (const 0 <* [0;1])) as H2.
    destruct (f u) as [v|] eqn:E2; cbn [Row9Eval.bind] in *.
    + rewrite first_plus_0 in H2.
      pose proof (f_embedding v 0%nat (const 0 <* [1;1])) as H3.
      destruct (f v) as [z|] eqn:E3; cbn [lift_prefix option_map] in *.
      * rewrite first_plus_0 in H3.
        eapply progress_trans; [apply short_initial|].
        eapply progress_trans; [exact H1|].
        eapply progress_trans; [apply short_second|].
        eapply progress_trans; [exact H2|].
        eapply progress_trans; [apply short_third|].
        eapply progress_trans; [exact H3|]. apply phase_carry.
      * eapply halts_evstep; [exact H3|]. apply progress_evstep.
        eapply progress_trans; [apply short_initial|].
        eapply progress_trans; [exact H1|].
        eapply progress_trans; [apply short_second|].
        eapply progress_trans; [exact H2|]. apply short_third.
    + eapply halts_evstep; [exact H2|]. apply progress_evstep.
      eapply progress_trans; [apply short_initial|].
      eapply progress_trans; [exact H1|]. apply short_second.
  - eapply halts_evstep; [exact H1|]. apply progress_evstep,short_initial.
Qed.

Theorem blank_halts_iff : halts tm c0 <-> iter_halts phase3 [].
Proof.
  rewrite (halts_evstep_iff _ _ _ (progress_evstep _ _ _ init)).
  eapply halts_iff with (P:=fun _ => True).
  - intros i _. pose proof (phase3_embedding i) as H.
    destruct (phase3 i); [split; [exact H|exact I]|exact H].
  - exact I.
Qed.

End Row9Raw.
