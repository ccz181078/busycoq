From BusyCoq Require Import Individual62 ES_v3 DivModCases.
From Coq Require Import String List ZArith NArith Lia.
Import ListNotations.
Set Default Goal Selector "1".
Ltac es_v3_TL ::= constr:(N.to_nat 1000).

Module TM1.
Definition tm : TM := Eval compute in (TM_from_str "1RB0LF_1LC1LA_1LD0LC_1RE1LB_0RB1RA_---0RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Ltac prove_literal_steps count := lazymatch count with S ?k =>
  eapply multistep_progress with (n:=k); apply multistep_c_spec; vm_compute; reflexivity end.
Tactic Notation "literal_steps" constr(n) := prove_literal_steps n.

Definition U := [S1;S1;S1;S0].
Definition V := [S1;S1;S1;S1;S1;S1;S0].
Definition K a b r := 0inf <{{D}} [1;0] *> U^^a *> V *> U^^b *> [0] *> r.
Definition J a r := 0inf <{{D}} [1;1;1;1;0] *> U^^a *> [1;1;1;1] *> r.
Definition G a r := 0inf <{{D}} [1;1;1;1;0] *> U^^(1+a) *> [0] *> r.

Lemma K_step a b r : K a (1+b) r -->+ K (1+a) b ([0;1] *> r).
Proof. unfold K,U,V. es' a b & r. Qed.

Lemma K_end a r : K a 0 r -->+ J (1+a) r.
Proof. unfold K,J,U,V. es' a & r. Qed.

Lemma K_iter b a r : K a b r -->+ J (1+b+a) ([0;1]^^b *> r).
Proof.
  gen a r. induction b; intros.
  - apply K_end.
  - cbn[Nat.add]. follow11 K_step. follow10 (IHb (1+a) ([0;1] *> r)).
    replace (1+b+(1+a)) with (S (S (b+a))) by lia.
    rewrite lpow_shift'. finish.
Qed.

Lemma G_step a r : G a r -->+ K 0 a ([0;1] *> r).
Proof. unfold G,K,U,V. es' a & r. Qed.

Lemma G_iter a r : G a r -->+ J (1+a) ([0;1]^^(1+a) *> r).
Proof.
  follow11 G_step. follow10 K_iter.
  rewrite Nat.add_0_r,lpow_shift'. finish.
Qed.

Inductive block := Three | Six.
Definition block_bits b := match b with Three => U | Six => V end.
Definition pushed_bits b := match b with
  Three => [S0;S1;S0;S1] | Six => [S0;S0;S1;S0;S1;S0;S1] end.
Definition returned_bits b := match b with
  Three => [S1;S0;S1;S1] | Six => [S1;S0;S1;S1;S1;S1;S1] end.
Definition core_bits := flat_map block_bits.
Definition returned_core := flat_map returned_bits.
Fixpoint pushed_core w := match w with
  [] => [] | b::w => pushed_core w ++ pushed_bits b end.

Lemma core_bits_app u v : core_bits (u++v) = core_bits u ++ core_bits v.
Proof. apply flat_map_app. Qed.

Lemma returned_core_app u v : returned_core (u++v) = returned_core u ++ returned_core v.
Proof. apply flat_map_app. Qed.

Lemma pushed_core_app u v : pushed_core (u++v) = pushed_core v ++ pushed_core u.
Proof.
  induction u; cbn; [rewrite app_nil_r; reflexivity|].
  rewrite IHu, app_assoc; reflexivity.
Qed.

Lemma core_bits_threes n : core_bits ([Three]^^n) = U^^n.
Proof. unfold core_bits. rewrite flat_map_lpow. reflexivity. Qed.

Lemma pushed_threes n : pushed_core ([Three]^^n) = [0;1;0;1]^^n.
Proof.
  induction n; cbn; [reflexivity|].
  rewrite IHn,lpow_shift. reflexivity.
Qed.

Lemma returned_threes n : returned_core ([Three]^^n) = [1;0;1;1]^^n.
Proof. unfold returned_core. rewrite flat_map_lpow. reflexivity. Qed.

Lemma returned_rotation w r :
  returned_core w *> [1;0] *> r = [1;0] *> core_bits w *> r.
Proof.
  induction w as [|b w IH]; [reflexivity|].
  unfold returned_core,core_bits in *; cbn[flat_map].
  rewrite !Str_app_assoc,IH. destruct b; reflexivity.
Qed.

Lemma core_starts_one w r : exists t, core_bits w *> [1] *> r=1 >> t.
Proof. destruct w as [|b w]; [eexists; reflexivity|]. destruct b; eexists; reflexivity. Qed.

Lemma right_block_head b l r :
  (D,l {{0}} block_bits b *> [1] *> r) -->+
  (D,(pushed_bits b *> l) {{0}} [1] *> r).
Proof.
  destruct b; [literal_steps 10|literal_steps 19].
Qed.

Lemma right_block b w l r :
  (D,l {{0}} core_bits (b::w) *> [1] *> r) -->+
  (D,(pushed_bits b *> l) {{0}} core_bits w *> [1] *> r).
Proof.
  change ((D,l {{0}} (block_bits b++core_bits w) *> [1] *> r) -->+
    (D,(pushed_bits b *> l) {{0}} core_bits w *> [1] *> r)).
  rewrite Str_app_assoc. destruct (core_starts_one w r) as [t H]. rewrite H.
  apply right_block_head.
Qed.
Lemma core_start w l r :
  (D,l {{0}} [1;0] *> core_bits w *> [1] *> r) -->+
  (D,([0;1] *> l) {{0}} core_bits w *> [1] *> r).
Proof.
  destruct (core_starts_one w r) as [t H]. rewrite H. literal_steps 6.
Qed.

Lemma right_core w l r :
  (D,l {{0}} core_bits w *> [1] *> r) -->*
  (D,(pushed_core w *> l) {{0}} [1] *> r).
Proof.
  gen l. induction w as [|b w IH]; intros; [finish|].
  follow100 right_block. follow IH. cbn[pushed_core].
  rewrite Str_app_assoc. finish.
Qed.

Lemma left_core w l r :
  (D,(pushed_core w *> l) {{1}} r) -->*
  (D,l {{1}} returned_core w *> r).
Proof.
  gen l r. induction w as [|b w IH]; intros; [finish|].
  cbn[pushed_core]. rewrite Str_app_assoc. follow IH.
  destruct b; apply progress_evstep; [literal_steps 4|literal_steps 7].
Qed.

Definition W w r := 0inf <{{D}} [1;0] *> core_bits w *> [0] *> r.
Definition tilted w n (r:side) :=
  (D,([0;1] *> [0;1;0;1]^^(n+2) *> [1;0;1;0;1] *>
    pushed_core w *> [0;1] *> 0inf) {{0}} r).
Definition carried w (r:side) :=
  (D,([0;0;1] *> pushed_core w *> [0;1] *> 0inf) {{0}} r).
Definition core_suffix m v r :=
  [0;1]^^m *> core_bits (Three::v++[Three]) *> [0] *> r.
Definition page w := [1;1;1;1;0] ++ core_bits w ++ [0;0].
Definition counter_pair a b r :=
  0inf <{{D}} [1;1;1;1;0] *> U^^a *> [0] *> U^^b *> [0;0] *> r.
Definition shield a b d r := counter_pair a b
  (page ([Three]^^(b/2-1)) *> page ([Three]^^d) *> r).

Lemma core_turn l r :
  (D,l {{0}} [1;1;1;0;0] *> r) -->+ (D,l {{1}} [1;0;0;0;1] *> r).
Proof. literal_steps 12. Qed.

Lemma left_edge r :
  (D,([0;1] *> 0inf) {{1}} r) -->+ (0inf <{{D}} [1;0;1;1] *> r).
Proof. literal_steps 4. Qed.

Lemma W_step w r : W (w++[Three]) r -->+ W (Three::w) ([0;1] *> r).
Proof.
  unfold W. rewrite core_bits_app. cbn[core_bits flat_map block_bits].
  unfold U. rewrite Str_app_assoc. follow10 core_start.
  follow right_core. follow100 core_turn. follow left_core. follow100 left_edge.
  change ([1;0;0;0;1] *> r) with ([1;0] *> [0;0;1] *> r).
  rewrite returned_rotation. finish.
Qed.

Lemma W_iter n w r :
  W (w++[Three]^^n) r -->* W ([Three]^^n++w) ([0;1]^^n *> r).
Proof.
  gen w r. induction n; intros.
  - cbn. rewrite app_nil_r. finish.
  - replace (w++[Three]^^S n) with ((w++[Three]^^n)++[Three])
      by (rewrite <-app_assoc,lpow_shift; reflexivity).
    follow100 W_step. follow (IHn (Three::w) ([0;1] *> r)).
    change (Three::w) with ([Three]++w).
    rewrite app_assoc,lpow_shift,lpow_shift'. finish.
Qed.

Ltac sweep1 a l r :=
  try rewrite !tl_const;
  cbn[Str_app app];
  let l := eval cbn[Str_app app] in l in
  let r := eval cbn[Str_app app] in r in
  es_v3_nmp_smp (fun s => if (s=?"a")%string then a else O)
    (fun s => if (s=?"l")%string then l else if (s=?"r")%string then r else 0inf).

Lemma core_zero w l r :
  (D,l {{0}} [0] *> core_bits w *> [1] *> r) -->+
  (D,([0] *> l) {{0}} core_bits w *> [1] *> r).
Proof.
  destruct (core_starts_one w r) as [t H]. rewrite H. literal_steps 7.
Qed.

Lemma four_right l r :
  (D,l {{0}} [1;1;1;1] *> r) -->+ (D,([0;1;0;1] *> l) {{0}} r).
Proof. literal_steps 8. Qed.

Lemma gap_left l r :
  (D,([0;0;1] *> l) {{1}} r) -->+ (D,l {{1}} [1;1;1] *> r).
Proof. literal_steps 3. Qed.

Lemma core_head v l r :
  (D,l {{0}} [1;1;1;1;0] *> core_bits v *> U *> [0] *> r) -->+
  (D,([0;1] *> l) {{1}} [1;1;1] *> returned_core v *> [1;0;0;0;1] *> r).
Proof.
  unfold U. follow10 four_right. follow100 core_zero.
  follow right_core. follow100 core_turn. follow left_core. follow100 gap_left. finish.
Qed.

Lemma W_tilt w n r :
  W (w++Six::[Three]^^n++[Six]) r -->+ tilted w n r.
Proof.
  unfold W. rewrite core_bits_app. cbn[core_bits flat_map block_bits].
  rewrite core_bits_app,core_bits_threes. cbn[core_bits flat_map block_bits].
  rewrite !Str_app_assoc. unfold U,V.
  follow10 core_start. follow right_core.
  unfold tilted. sweep1 n (pushed_core w *> [0;1] *> 0inf) r.
Qed.

Lemma W_multi_six w n b r :
  W ((w++Six::[Three]^^n++[Six])++[Three]^^b) r -->+
  tilted ([Three]^^b++w) n ([0;1]^^b *> r).
Proof.
  eapply evstep_progress_trans; [apply W_iter|].
  rewrite (app_assoc ([Three]^^b) w (Six::[Three]^^n++[Six])).
  apply W_tilt.
Qed.

Lemma zero_one l r :
  (D,l {{0}} [0;1] *> r) -->+ (D,([0] *> l) {{0}} [1] *> r).
Proof. literal_steps 7. Qed.

Lemma alternating_step l r :
  (D,l {{0}} [1;0;1] *> r) -->+ (D,([0;1] *> l) {{0}} [1] *> r).
Proof. literal_steps 6. Qed.

Lemma alternating_right n l r :
  (D,l {{0}} [1] *> [0;1]^^n *> r) -->*
  (D,([0;1]^^n *> l) {{0}} [1] *> r).
Proof.
  gen l. induction n; intros; [finish|].
  cbn[lpow]. rewrite Str_app_assoc. follow100 alternating_step.
  follow IHn. rewrite lpow_shift'. finish.
Qed.

Lemma T_turn w n m v r :
  tilted w n (core_suffix (1+m) v r) -->+
  (D,([0;1]^^(1+m) *> [0;0;1] *> [0;1;0;1]^^(n+2) *>
    [1;0;1;0;1] *> pushed_core w *> [0;1] *> 0inf) {{1}}
    [1;1;1] *> returned_core v *> [1;0;0;0;1] *> r).
Proof.
  unfold tilted,core_suffix. cbn[core_bits flat_map block_bits].
  rewrite core_bits_app. cbn[core_bits flat_map block_bits].
  rewrite !Str_app_assoc. unfold U.
  cbn[lpow Nat.add]. rewrite Str_app_assoc.
  follow10 zero_one. follow alternating_right.
  follow100 core_head. finish.
Qed.

Lemma alternating_left n l r :
  (D,([0;1;0;1]^^n *> l) {{1}} r) -->*
  (D,l {{1}} [1;0;1;1]^^n *> r).
Proof.
  pose proof (left_core ([Three]^^n) l r) as H.
  rewrite pushed_threes,returned_threes in H. exact H.
Qed.

Lemma left_101 l r :
  (D,([1;0;1] *> l) {{1}} r) -->+ (D,([0] *> l) {{0}} [1;1] *> r).
Proof. literal_steps 6. Qed.

Lemma rotate_return n r :
  [1;1] *> [1;0;1;1]^^n *> r = U^^n *> [1;1] *> r.
Proof. symmetry. apply (lpow_rotate' [1;0] [1;1]). Qed.

Lemma T_even w n m v r :
  tilted w n (core_suffix (2*m+2) v r) -->+
  carried w (U^^(n+2) *> V *> U^^m *> V *> core_bits v *> [0;0;1] *> r).
Proof.
  replace (2*m+2) with (1+(1+2*m)) by lia.
  follow10 T_turn.
  replace (1+(1+2*m)) with ((1+m)*2) by lia.
  rewrite lpow_mul. cbn[lpow app].
  follow alternating_left. follow100 gap_left. follow alternating_left.
  follow100 left_101. unfold carried,U,V.
  change ([1;0;0;0;1] *> r) with ([1;0] *> [0;0;1] *> r).
  rewrite returned_rotation.
  rewrite rotate_return. cbn[Nat.add lpow]. rewrite Str_app_assoc.
  change ([1;1] *> [1;1;1] *> [1;0;1;1] *> [1;0;1;1]^^m *>
    [1;1;1] *> [1;0] *> core_bits v *> [0;0;1] *> r)
    with (V *> [1;1] *> [1;0;1;1]^^m *> [1;1;1;1;0] *>
      core_bits v *> [0;0;1] *> r).
  rewrite rotate_return. finish.
Qed.

Lemma carried_return u v r :
  carried (u++[Three]) (core_bits (v++[Three]) *> [0] *> r) -->+
  W (Three::u++Six::v) ([0;1] *> r).
Proof.
  unfold carried,W. rewrite !core_bits_app.
  cbn[core_bits flat_map block_bits]. rewrite !Str_app_assoc. unfold U,V.
  eapply evstep_progress_trans; [apply right_core|].
  follow10 core_turn. follow left_core. follow100 gap_left. follow left_core.
  follow100 left_edge. rewrite returned_core_app.
  cbn[returned_core flat_map returned_bits]. rewrite Str_app_assoc.
  change ([1;0;0;0;1] *> r) with ([1;0] *> [0;0;1] *> r).
  rewrite returned_rotation.
  change (([1;0;1;1]++[]) *> [1;1;1] *> [1;0] *> core_bits v *> [0;0;1] *> r)
    with ([1;0] *> V *> core_bits v *> [0;0;1] *> r).
  rewrite returned_rotation,core_bits_app,Str_app_assoc. finish.
Qed.

Lemma carried_six u v n r :
  carried (u++[Three]) (core_bits (v++Six::[Three]^^n++[Six]) *> [0] *> r) -->+
  tilted (u++Six::v) n r.
Proof.
  unfold carried,tilted. rewrite !pushed_core_app,!core_bits_app.
  cbn[pushed_core pushed_bits core_bits flat_map block_bits].
  rewrite core_bits_app,core_bits_threes. cbn[core_bits flat_map block_bits].
  rewrite !Str_app_assoc. unfold U,V.
  eapply evstep_progress_trans; [apply right_core|].
  sweep1 n (pushed_core v *> [0;0;1] *> [0;1;0;1] *>
    pushed_core u *> [0;1] *> 0inf) r.
Qed.

Definition page_core n m v := [Three]^^(n+2)++Six::[Three]^^m++Six::v.

Lemma page_core_bits n m v : core_bits (page_core n m v) =
  U^^(n+2)++V++U^^m++V++core_bits v.
Proof.
  unfold page_core. rewrite core_bits_app,core_bits_threes.
  cbn[core_bits flat_map block_bits]. rewrite core_bits_app,core_bits_threes. reflexivity.
Qed.

Lemma T_even_return u n m v r :
  tilted (u++[Three]) n (core_suffix (2*m+2) (v++[Three]) r) -->+
  W (Three::u++Six::page_core n m v) ([0;1;0;1] *> r).
Proof.
  follow10 T_even.
  eapply progress_evstep.
  replace (U^^(n+2) *> V *> U^^m *> V *> core_bits (v++[Three]) *> [0;0;1] *> r)
    with (core_bits (page_core n m v++[Three]) *> [0] *> [0;1] *> r).
  - apply carried_return.
  - rewrite !core_bits_app,page_core_bits. cbn[core_bits flat_map block_bits].
    rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma T_page u n m c r :
  tilted (u++[Three]) n
    ([0;1]^^(2*m+1) *> [0;1;1;1;1;0] *> U^^(1+c) *> [0] *> r) -->+
  tilted ([Three]^^c++u++Six::[Three]^^(n+2)) m ([0;1]^^(1+c) *> r).
Proof.
  destruct c as [|c].
  - replace ([0;1]^^(2*m+1) *> [0;1;1;1;1;0] *> U^^(1+0) *> [0] *> r)
      with (core_suffix (2*m+2) [] r).
    2:{ unfold core_suffix,U. cbn[core_bits flat_map block_bits].
        replace (2*m+2) with ((2*m+1)+1) by lia. rewrite lpow_add,Str_app_assoc. reflexivity. }
    follow10 T_even.
    eapply progress_evstep.
    replace (U^^(n+2) *> V *> U^^m *> V *> core_bits [] *> [0;0;1] *> r)
      with (core_bits ([Three]^^(n+2)++Six::[Three]^^m++[Six]) *> [0] *> [0;1] *> r).
    2:{ rewrite !core_bits_app,!core_bits_threes. cbn[core_bits flat_map block_bits].
        rewrite core_bits_app,core_bits_threes,!Str_app_assoc. reflexivity. }
    apply carried_six.
  - replace ([0;1]^^(2*m+1) *> [0;1;1;1;1;0] *> U^^(1+S c) *> [0] *> r)
      with (core_suffix (2*m+2) ([Three]^^c++[Three]) r).
    2:{ unfold core_suffix. cbn[core_bits flat_map block_bits].
        rewrite !core_bits_app,core_bits_threes.
        replace (2*m+2) with ((2*m+1)+1) by lia.
        rewrite lpow_add,!Str_app_assoc.
        cbn[core_bits flat_map block_bits Nat.add lpow].
        rewrite !Str_app_assoc. cbn[app Str_app].
        change (U^^c *> [1;1;1;0] *> [1;1;1;0] *> [0] *> r)
          with (U^^c *> U *> U *> [0] *> r).
        rewrite !(@lpow_shift' Sym c U). reflexivity. }
    follow10 T_even_return.
    unfold page_core.
    replace (Three::u++Six::[Three]^^(n+2)++Six::[Three]^^m++Six::[Three]^^c)
      with (((Three::u++Six::[Three]^^(n+2))++Six::[Three]^^m++[Six])++[Three]^^c)
      by (repeat first [rewrite <- app_assoc | progress cbn[app]]; reflexivity).
    follow100 W_multi_six.
    change (Three::u++Six::[Three]^^(n+2))
      with ([Three]++(u++Six::[Three]^^(n+2))).
    rewrite app_assoc,lpow_shift.
    change ([0;1;0;1] *> r) with ([0;1] *> [0;1] *> r).
    rewrite !lpow_shift'. finish.
Qed.

Lemma q_right_step l r :
  (D,l {{0}} [1;0;1;1;1] *> r) -->+
  (D,([0;1;0;1] *> l) {{0}} [1] *> r).
Proof. literal_steps 10. Qed.

Lemma q_right n l r :
  (D,l {{0}} [1;0;1;1]^^n *> [1] *> r) -->*
  (D,([0;1;0;1]^^n *> l) {{0}} [1] *> r).
Proof.
  gen l. induction n; intros; [finish|].
  cbn[lpow]. rewrite Str_app_assoc.
  destruct n as [|n].
  - follow100 q_right_step. finish.
  - cbn[lpow] in *. rewrite Str_app_assoc in *.
    follow100 q_right_step. follow IHn. rewrite !Str_app_assoc,lpow_shift'. finish.
Qed.

Lemma odd_turn l r :
  (D,([0;1;0;0;1;0;1] *> l) {{1}} r) -->+
  (D,([1;0;1] *> l) {{0}} [1;0;1;1] *> r).
Proof. literal_steps 4. Qed.

Lemma double_left l r :
  (D,([0;1;1;0;1] *> l) {{1}} r) -->+ (D,l {{1}} [1;0;0;1;1] *> r).
Proof. literal_steps 5. Qed.

Lemma half_slide n r :
  [0;1] *> [0;1;0;1]^^n *> r = [0;1;0;1]^^n *> [0;1] *> r.
Proof. symmetry. apply (lpow_rotate' [0;1] [0;1]). Qed.

Lemma T_odd_turn w n m v r :
  tilted w n (core_suffix (2*m+1) (v++[Three]) r) -->+
  (D,([0;1] *> pushed_core w *> [0;1] *> 0inf) {{1}}
    [1;0;0;1;1] *> [1;0;1;1]^^(1+n) *>
    [1;0;0;1;1] *> [1;0;1;1]^^(1+m) *>
    [1;1;1] *> returned_core v *> [1;0;0;0;1;0;1] *> r).
Proof.
  replace (2*m+1) with (1+2*m) by lia. follow10 T_turn.
  replace (2*m) with (m*2) by lia. cbn[Nat.add lpow].
  rewrite Str_app_assoc,lpow_mul. cbn[lpow app].
  rewrite half_slide. follow alternating_left.
  replace (n+2) with (1+(1+n)) by lia.
  cbn[Nat.add lpow]. rewrite Str_app_assoc.
  follow100 odd_turn.
  change ([1;0;1;1] *> [1;0;1;1]^^m *> [1;1;1] *>
    returned_core (v++[Three]) *> [1;0;0;0;1] *> r)
    with ([1;0;1;1]^^(1+m) *> [1] *>
      [1;1] *> returned_core (v++[Three]) *> [1;0;0;0;1] *> r).
  follow q_right.
  rewrite returned_core_app. cbn[returned_core flat_map returned_bits app].
  rewrite Str_app_assoc.
  change ([1;0;1;1] *> [1;0;0;0;1] *> r)
    with ([1;0] *> [1;1;1;0;0;0;1] *> r).
  rewrite returned_rotation.
  follow100 core_head.
  rewrite half_slide. follow alternating_left. follow100 double_left.
  change (0 >> 1 >> (0::1::0::1::[0;1;0;1]^^n) *>
    [1;0;1;0;1] *> pushed_core w *> [0;1] *> 0inf)
    with ([0;1] *> [0;1;0;1]^^(1+n) *>
      [1;0;1;0;1] *> pushed_core w *> [0;1] *> 0inf).
  rewrite half_slide. follow alternating_left. follow100 double_left. finish.
Qed.

Lemma half_six w b r :
  (D,([0;1] *> pushed_core (w++Six::[Three]^^b) *> [0;1] *> 0inf) {{1}}
    [1;0;0;1;1] *> r) -->+
  (D,([0;1] *> pushed_core w *> [0;1] *> 0inf) {{1}}
    [1;0;0;1;1] *> [1;0;1;1]^^b *> [1;0;0;0;1;1;1] *> r).
Proof.
  rewrite pushed_core_app. cbn[pushed_core pushed_bits].
  rewrite pushed_threes,!Str_app_assoc.
  sweep1 b (pushed_core w *> [0;1] *> 0inf) r.
Qed.

Fixpoint row a gaps := match gaps with
  [] => [Three]^^a | b::gaps => row a gaps ++ Six::[Three]^^b end.
Fixpoint packet gaps (r:side) := match gaps with
  [] => r | b::gaps => packet gaps ([1;0;1;1]^^b *> [1;0;0;0;1;1;1] *> r) end.
Fixpoint saved_pages gaps r := match gaps with
  [] => r | b::gaps => saved_pages gaps (page ([Three]^^b) *> r) end.

Lemma half_row a gaps r :
  (D,([0;1] *> pushed_core (row a gaps) *> [0;1] *> 0inf) {{1}}
    [1;0;0;1;1] *> r) -->+ G a ([1;1] *> packet gaps r).
Proof.
  gen r. induction gaps as [|b gaps IH]; intros.
  - cbn[row packet]. rewrite pushed_threes. unfold G,U.
    es' a & r.
  - cbn[row packet]. follow11 half_six. apply IH.
Qed.

Lemma q_gap n r :
  [1;1;1] *> [1;0;1;1]^^(1+n) *> [1;0;0;1;1] *> r =
  [1;1;1;1;0] *> U^^(1+n) *> [0;1;1] *> r.
Proof.
  change ([1;1;1] *> [1;0;1;1]^^(1+n) *> [1;0;0;1;1] *> r)
    with ([1] *> ([1;1] *> [1;0;1;1]^^(1+n) *> [1;0;0;1;1] *> r)).
  rewrite rotate_return. cbn[Nat.add lpow]. rewrite Str_app_assoc.
  change ([1;1] *> [1;0;0;1;1] *> r) with (U *> [0;1;1] *> r).
  rewrite lpow_shift'. reflexivity.
Qed.

Lemma q_packet n r :
  [1;1;1] *> [1;0;1;1]^^n *> [1;0;0;0;1;1;1] *> r =
  page ([Three]^^n) *> [1;1;1] *> r.
Proof.
  unfold page. rewrite core_bits_threes,!Str_app_assoc.
  change ([1;1;1] *> [1;0;1;1]^^n *> [1;0;0;0;1;1;1] *> r)
    with ([1] *> ([1;1] *> [1;0;1;1]^^n *> [1;0;0;0;1;1;1] *> r)).
  rewrite rotate_return.
  change ([1;1] *> [1;0;0;0;1;1;1] *> r) with (U *> [0;0;1;1;1] *> r).
  rewrite lpow_shift'. reflexivity.
Qed.

Lemma packet_pages gaps r :
  [1;1;1] *> packet gaps r = saved_pages gaps ([1;1;1] *> r).
Proof.
  gen r. induction gaps; intros; cbn[packet saved_pages]; [reflexivity|].
  rewrite IHgaps,q_packet. reflexivity.
Qed.

Lemma packet_app u v r : packet (u++v) r = packet v (packet u r).
Proof. gen r. induction u; intros; cbn; [reflexivity|apply IHu]. Qed.

Lemma packet_last gaps b r :
  [1;1] *> packet (gaps++[b]) r =
  U^^(1+b) *> [0;0] *> saved_pages gaps ([1;1;1] *> r).
Proof.
  rewrite packet_app. cbn[packet]. rewrite rotate_return.
  change ([1;1] *> [1;0;0;0;1;1;1] *> packet gaps r)
    with (U *> [0;0] *> [1;1;1] *> packet gaps r).
  rewrite lpow_shift',packet_pages. reflexivity.
Qed.

Definition saved_body n m v r := [1;1;1;1;0] *> U^^(1+n) *> [0] *>
  U^^(1+m) *> V *> core_bits v *> [0;0;1;0;1] *> r.

Lemma saved_body_normal n m v r :
  [1;1;1] *> [1;0;1;1]^^(1+n) *>
  [1;0;0;1;1] *> [1;0;1;1]^^(1+m) *>
  [1;1;1] *> returned_core v *> [1;0;0;0;1;0;1] *> r = saved_body n m v r.
Proof.
  rewrite q_gap. unfold saved_body.
  change ([0;1;1] *> [1;0;1;1]^^(1+m) *>
    [1;1;1] *> returned_core v *> [1;0;0;0;1;0;1] *> r)
    with ([0] *> [1;1] *> [1;0;1;1]^^(1+m) *>
      [1;1;1] *> returned_core v *> [1;0;0;0;1;0;1] *> r).
  rewrite rotate_return.
  change ([1;0;0;0;1;0;1] *> r) with ([1;0] *> [0;0;1;0;1] *> r).
  rewrite returned_rotation. reflexivity.
Qed.

Lemma T_odd_frontier a b gaps n m v r :
  tilted (row a (gaps++[b])) n (core_suffix (2*m+1) (v++[Three]) r) -->+
  counter_pair (1+a) (1+b) (saved_pages gaps (saved_body n m v r)).
Proof.
  follow10 T_odd_turn.
  eapply evstep_trans; [apply progress_evstep,half_row|].
  rewrite packet_last,saved_body_normal. finish.
Qed.

Lemma J_even n k b r :
  J n ([0;1]^^(2*k+2) *> U^^(b+4) *> [0;0] *> r) -->+
  W (Six::[Three]^^(n+2)++Six::[Three]^^k++Six::[Three]^^b)
    ([0;1]^^3 *> [0] *> r).
Proof.
  unfold J,W.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn[core_bits flat_map block_bits]].
  rewrite !Str_app_assoc. unfold U,V.
  replace (2*k+2) with (k*2+2) by lia. es' n k b & r.
Qed.

Lemma J_odd n k b r :
  J n ([0;1]^^(2*k+1) *> U^^(b+4) *> [0;0] *> r) -->+
  K 0 n (U^^(k+1) *> V *> U^^(b+1) *> [0;0;1;0;1;0] *> r).
Proof.
  unfold J,K,U,V. replace (2*k+1) with (k*2+1) by lia.
  es' n k b & r.
Qed.

Lemma J_odd_mixed n k h b r :
  J n ([0;1]^^(2*k+1) *> U^^(h+2) *> V *> U^^(b+2) *> [0;0] *> r) -->+
  K 0 n (U^^(k+1) *> V *> U^^(h+1) *> V *> U^^b *> [0;0;1;0;1;0] *> r).
Proof.
  unfold J,K,U,V. replace (2*k+1) with (k*2+1) by lia.
  es' n k h b & r.
Qed.

Lemma J_even_twice n k h j b r :
  J n ([0;1]^^(2*k+2) *> U^^(h+2) *> V *> U^^j *> V *> U^^(b+3) *> [0;0] *> r) -->+
  W (Six::[Three]^^(n+2)++Six::[Three]^^k++Six::[Three]^^(h+1)++
      Six::[Three]^^j++Six::[Three]^^b) ([0;1]^^3 *> [0] *> r).
Proof.
  unfold J,W.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn[core_bits flat_map block_bits]].
  rewrite !Str_app_assoc. unfold U,V.
  replace (2*k+2) with (k*2+2) by lia. es' n k h j b & r.
Qed.

Lemma pair_start a b r :
  counter_pair (1+a) b r -->+ J (1+a) ([0;1]^^(1+a) *> U^^b *> [0;0] *> r).
Proof. apply G_iter. Qed.

Lemma paired_even k b r :
  counter_pair (2*k+2) (b+4) r -->+
  tilted ([Three]^^b++Six::[Three]^^(2*k+4)) k ([0;1]^^(b+3) *> [0] *> r).
Proof.
  replace (2*k+2) with (1+(2*k+1)) by lia. follow11 pair_start.
  replace (1+(2*k+1)) with (2*k+2) by lia. follow11 J_even.
  replace (2*k+2+2) with (2*k+4) by lia.
  pose proof (W_multi_six (Six::[Three]^^(2*k+4)) k b ([0;1]^^3 *> [0] *> r)) as H.
  repeat first [rewrite <- app_assoc in H | progress cbn[app] in H].
  rewrite (@lpow_add _ b 3 [S0;S1]),Str_app_assoc. exact H.
Qed.

Definition odd_outer h := Six::[Three]^^(2*h+7)++Six::[Three]^^(h+1)++
  Six::[Three]^^(h+1).

Lemma paired_odd h b r :
  counter_pair (2*h+3) (b+8) r -->+
  tilted ([Three]^^b++odd_outer h) (h+1) ([0;1]^^(b+7) *> [0] *> r).
Proof.
  replace (2*h+3) with (1+(2*h+2)) by lia. follow11 pair_start.
  replace (1+(2*h+2)) with (2*(h+1)+1) by lia.
  replace (b+8) with ((b+4)+4) by lia. follow11 J_odd. follow11 K_iter.
  rewrite Nat.add_0_r.
  replace (1+(2*(h+1)+1)) with (2*h+4) by lia.
  replace (h+1+1) with (h+2) by lia.
  replace (b+4+1) with ((b+3)+2) by lia.
  change ([0;0;1;0;1;0] *> r) with ([0;0] *> [1;0;1;0] *> r).
  follow11 J_odd_mixed. follow11 K_iter. rewrite Nat.add_0_r.
  replace (1+(2*h+4)) with (2*h+5) by lia.
  replace (2*h+4) with (2*(h+1)+2) by lia.
  replace (h+1+1) with (h+2) by lia.
  change ([0;0;1;0;1;0] *> [1;0;1;0] *> r)
    with ([0;0] *> [1;0;1;0;1;0;1;0] *> r).
  follow11 J_even_twice.
  replace (2*h+5+2) with (2*h+7) by lia.
  change ([0;1]^^3 *> [0] *> [1;0;1;0;1;0;1;0] *> r)
    with ([0;1]^^7 *> [0] *> r).
  pose proof (W_multi_six (odd_outer h) (h+1) b ([0;1]^^7 *> [0] *> r)) as H.
  unfold odd_outer in *.
  repeat first [rewrite <- app_assoc in H | progress cbn[app] in H].
  rewrite (@lpow_add _ b 7 [S0;S1]),Str_app_assoc. exact H.
Qed.

Ltac sweep3 a b c l r :=
  try rewrite !tl_const;
  cbn[Str_app app];
  let l := eval cbn[Str_app app] in l in
  let r := eval cbn[Str_app app] in r in
  es_v3_nmp_smp
    (fun s => if (s=?"a")%string then a else if (s=?"b")%string then b
      else if (s=?"c")%string then c else O)
    (fun s => if (s=?"l")%string then l else if (s=?"r")%string then r else 0inf).

Definition short_page_suffix m c r := core_suffix (2*m+1) []
  ([0;1;1;1;1;0] *> U^^(c+2) *> [0] *> r).

Lemma T_short_page_turn w n m c r :
  tilted w (1+n) (short_page_suffix m c r) -->+
  (D,([0;1] *> pushed_core w *> [0;1] *> 0inf) {{1}}
    [1;0;0;1;1] *> [1;0;1;1]^^(1+n) *>
    [1;0;0;1;1] *> [1;0;1;1]^^(1+(m+2)) *>
    [1;1;1] *> returned_core (Six::[Three]^^c) *> [1;0;0;0;1;0;1] *> r).
Proof.
  unfold tilted,short_page_suffix,core_suffix.
  cbn[core_bits flat_map block_bits returned_core returned_bits].
  rewrite returned_threes,!Str_app_assoc. unfold U.
  replace (2*m+1) with (m*2+1) by lia.
  sweep3 n m c (pushed_core w *> [0;1] *> 0inf) r.
Qed.

Lemma T_short_page_frontier a b gaps n m c r :
  tilted (row a (gaps++[b])) (1+n) (short_page_suffix m c r) -->+
  counter_pair (1+a) (1+b)
    (saved_pages gaps (saved_body n (m+2) (Six::[Three]^^c) r)).
Proof.
  follow10 T_short_page_turn.
  eapply evstep_trans; [apply progress_evstep,half_row|].
  rewrite packet_last,saved_body_normal. finish.
Qed.

Lemma positive_page_form p c r :
  core_suffix (1+p) ([Three]^^c) r =
  [0;1]^^p *> [0;1;1;1;1;0] *> U^^(1+c) *> [0] *> r.
Proof.
  unfold core_suffix. replace (1+p) with (p+1) by lia.
  rewrite (@lpow_add _ p 1 [S0;S1]).
  cbn[core_bits flat_map block_bits]. rewrite core_bits_app,core_bits_threes.
  cbn[core_bits flat_map block_bits Nat.add lpow app].
  rewrite !Str_app_assoc.
  change ((U++[]) *> [0] *> r) with (U *> [0] *> r).
  rewrite (@lpow_shift' _ c U). reflexivity.
Qed.

Definition qright x r := [1;1;1;1;0] *> U^^(2*x+2) *> [0] *> r.
Definition Qfront x y r := counter_pair (6*x+2) (2*y+4)
  (page ([Three]^^(y+2)) *> qright x r).
Definition qframe x z r := U^^(z+2) *> V *> U^^(2*x) *> [0;0;1;0;1] *> r.
Definition qleft x z := [Three]^^(4*z)++Six::[Three]^^(6*x+3).

Lemma qleft_input x z :
  [Three]^^(4*z)++Six::[Three]^^(2*(3*x)+4) = qleft x z++[Three].
Proof.
  unfold qleft. replace (2*(3*x)+4) with ((6*x+3)+1) by lia.
  rewrite lpow_add.
  repeat first [rewrite <- app_assoc | progress cbn[app]]. reflexivity.
Qed.

Lemma qleft_output x z :
  [Three]^^(2*z+1)++qleft x z++Six::[Three]^^(3*x+2) = row (6*z+1) [3*x+2;6*x+3].
Proof.
  unfold qleft. cbn[row]. replace (6*z+1) with ((2*z+1)+4*z) by lia.
  rewrite (@lpow_add _ (2*z+1) (4*z) [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app]]. reflexivity.
Qed.

Lemma qright_core m x r :
  [0;1]^^(2*m) *> [0] *> qright x r =
  core_suffix (2*m+1) ([Three]^^(2*x)++[Three]) r.
Proof.
  replace (2*m+1) with (1+2*m) by lia.
  rewrite lpow_shift. change ([Three]++[Three]^^(2*x)) with ([Three]^^(1+2*x)).
  rewrite positive_page_form. unfold qright.
  replace (1+(1+2*x)) with (2*x+2) by lia. reflexivity.
Qed.

Lemma Q_push x z r : Qfront x (2*z) r -->+ Qfront z (3*x) (qframe x z r).
Proof.
  unfold Qfront at 1.
  replace (6*x+2) with (2*(3*x)+2) by lia.
  replace (2*(2*z)+4) with (4*z+4) by lia. follow11 paired_even.
  rewrite qleft_input. replace (4*z+3) with (2*(2*z+1)+1) by lia.
  unfold page. rewrite core_bits_threes,!Str_app_assoc.
  change ([0] *> [1;1;1;1;0] *> U^^(2*z+2) *> [0;0] *> qright x r)
    with ([0;1;1;1;1;0] *> U^^(2*z+2) *> [0] *> [0] *> qright x r).
  replace (2*z+2) with (1+(2*z+1)) by lia. follow11 T_page.
  rewrite qleft_output.
  replace (1+(2*z+1)) with (2*(z+1)) by lia. rewrite qright_core.
  follow10 (T_odd_frontier (6*z+1) (6*x+3) [3*x+2]).
  unfold Qfront,qright,qframe,saved_body. cbn[saved_pages].
  rewrite core_bits_threes.
  replace (1+(6*z+1)) with (6*z+2) by lia.
  replace (1+(6*x+3)) with (2*(3*x)+4) by lia.
  replace (1+(2*z+1)) with (2*z+2) by lia.
  replace (1+(z+1)) with (z+2) by lia. finish.
Qed.

Definition callback_middle t b := [Three]^^(t+2)++Six::[Three]^^b.
Definition callback_payload t b r :=
  core_bits (Three::callback_middle t b++[Three;Three]) *> [0;0;1;0;1] *> r.
Definition callback_outer u n t := Three::u++Six::[Three]^^(n+2)++Six::[Three]^^(t+1).
Definition callback_next u n t b := [Three]^^(b+1)++u++Six::[Three]^^(n+2)++Six::[Three]^^t.

Lemma callback_input t b r :
  [0;1]^^(2*t+4) *> callback_payload t b r =
  core_suffix (2*(t+1)+2) (callback_middle t b++[Three]) ([0;1;0;1] *> r).
Proof.
  unfold callback_payload,core_suffix.
  replace (2*t+4) with (2*(t+1)+2) by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma callback_row u n t b :
  [Three]^^b++callback_outer u n t = callback_next u n t b++[Three].
Proof.
  unfold callback_outer,callback_next. rewrite !lpow_add.
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma callback_link u n t b r :
  tilted (u++[Three]) n ([0;1]^^(2*t+4) *> callback_payload t b r) -->+
  tilted (callback_next u n t b++[Three]) (t+2) ([0;1]^^(b+4) *> r).
Proof.
  rewrite callback_input. follow11 T_even_return.
  pose proof (W_multi_six (callback_outer u n t) (t+2) b ([0;1]^^4 *> r)) as H.
  unfold page_core,callback_middle,callback_outer in *.
  repeat first [rewrite <- app_assoc in H | progress cbn[app] in H].
  repeat first [rewrite <- app_assoc | progress cbn[app]].
  follow10 H.
  fold (callback_outer u n t). rewrite callback_row.
  rewrite (@lpow_add _ b 4 [S0;S1]),Str_app_assoc. finish.
Qed.

Lemma row_prepend q a gaps : [Three]^^q++row a gaps = row (a+q) gaps.
Proof.
  induction gaps as [|b gaps IH]; cbn[row].
  - rewrite <- lpow_add. f_equal; lia.
  - rewrite app_assoc,IH. reflexivity.
Qed.

Lemma callback_next_row a gaps n t b :
  callback_next (row a gaps) n t b = row (a+b+1) (t::(n+2)::gaps).
Proof.
  unfold callback_next. cbn[row]. replace (a+b+1) with (a+(b+1)) by lia.
  rewrite <- row_prepend.
  repeat first [rewrite <- app_assoc | progress cbn[app]]. reflexivity.
Qed.

Lemma row_last_three a d gaps : row a (d::gaps)++[Three] = row a ((d+1)::gaps).
Proof.
  cbn[row]. rewrite (@lpow_add _ d 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Definition exit_core v r := core_bits (Three::v++[Three;Three]) *> [0] *> r.

Lemma exit_core_form p v r : [0;1]^^p *> exit_core v r = core_suffix p (v++[Three]) r.
Proof. unfold exit_core,core_suffix. rewrite <- app_assoc. reflexivity. Qed.

Lemma callback_row_exit a b gaps n t s v r :
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*t+4) *> callback_payload t (2*s+1) (exit_core v r)) -->+
  counter_pair (a+2*s+3) (b+1)
    (saved_pages ([t+1;n+2]++gaps) (saved_body (t+2) (s+2) v r)).
Proof.
  follow11 callback_link. rewrite callback_next_row,row_last_three.
  replace (a+(2*s+1)+1) with (a+2*s+2) by lia.
  replace (2*s+1+4) with (2*(s+2)+1) by lia. rewrite exit_core_form.
  follow10 (T_odd_frontier (a+2*s+2) b ([t+1;n+2]++gaps)).
  replace (1+(a+2*s+2)) with (a+2*s+3) by lia.
  replace (1+b) with (b+1) by lia. finish.
Qed.

Fixpoint exit_chain t indices s v r := match indices with
  [] => callback_payload t (2*s+1) (exit_core v r)
  | z::indices => callback_payload t (2*z) (exit_chain z indices s v r) end.

Lemma saved_pages_append u v r : saved_pages (u++v) r = saved_pages v (saved_pages u r).
Proof. gen r. induction u; intros; cbn[saved_pages app]; [reflexivity|apply IHu]. Qed.

Lemma exit_chain_return indices : forall a b extras c d n t s v r,
  exists aa rr, a+2*s+3<=aa /\
    tilted (row a ((extras++[d;c])++[b])++[Three]) n
      ([0;1]^^(2*t+4) *> exit_chain t indices s v r) -->+
    counter_pair aa (b+1) (page ([Three]^^c) *> page ([Three]^^d) *> rr).
Proof.
  induction indices as [|z indices IH]; intros a b extras c d n t s v r.
  - exists (a+2*s+3),
      (saved_pages ([t+1;n+2]++extras) (saved_body (t+2) (s+2) v r)).
    split; [lia|]. cbn[exit_chain]. follow10 callback_row_exit.
    rewrite app_assoc,saved_pages_append. finish.
  - destruct (IH (a+2*z+1) b (t::(n+2)::extras) c d (t+2) z s v r)
      as [aa [rr [Ha H]]].
    exists aa,rr. split; [lia|]. cbn[exit_chain]. follow11 callback_link.
    rewrite callback_next_row. exact H.
Qed.

Definition qodd_first x b := [Three]^^(4*b+2)++Six::[Three]^^(6*x+3).
Definition qodd_second x b := [Three]^^(6*b+4)++Six::[Three]^^(6*x+3)++Six::[Three]^^(3*x+1).
Definition qodd_left x b := row (2*x+6*b+5) [2*b+3;3*x+1;6*x+3].

Lemma qodd_pair x b :
  [Three]^^(4*b+2)++Six::[Three]^^(2*(3*x)+4) = qodd_first x b++[Three].
Proof.
  unfold qodd_first. replace (2*(3*x)+4) with ((6*x+3)+1) by lia.
  rewrite (@lpow_add _ (6*x+3) 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma qodd_first_page x b :
  [Three]^^(2*b+2)++qodd_first x b++Six::[Three]^^(3*x+2) = qodd_second x b++[Three].
Proof.
  unfold qodd_first,qodd_second.
  replace (6*b+4) with ((2*b+2)+(4*b+2)) by lia.
  replace (3*x+2) with ((3*x+1)+1) by lia.
  rewrite (@lpow_add _ (2*b+2) (4*b+2) [Three]),(@lpow_add _ (3*x+1) 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma qodd_second_page x b :
  [Three]^^(2*x+1)++qodd_second x b++Six::[Three]^^(2*b+2+2) = qodd_left x b++[Three].
Proof.
  unfold qodd_second,qodd_left. cbn[row].
  replace (2*x+6*b+5) with ((2*x+1)+(6*b+4)) by lia.
  replace (2*b+2+2) with ((2*b+3)+1) by lia.
  rewrite (@lpow_add _ (2*x+1) (6*b+4) [Three]),(@lpow_add _ (2*b+3) 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma Q_odd_entry x b r :
  Qfront x (2*b+1) r -->+
  tilted (qodd_left x b++[Three]) (b+1) ([0;1]^^(2*x+2) *> r).
Proof.
  unfold Qfront. replace (6*x+2) with (2*(3*x)+2) by lia.
  replace (2*(2*b+1)+4) with ((4*b+2)+4) by lia.
  follow11 paired_even. rewrite qodd_pair.
  replace (2*b+1+2) with (2*b+3) by lia.
  replace (4*b+2+3) with (2*(2*b+2)+1) by lia.
  unfold page. rewrite core_bits_threes,!Str_app_assoc.
  change ([0] *> [1;1;1;1;0] *> U^^(2*b+3) *> [0;0] *> qright x r)
    with ([0;1;1;1;1;0] *> U^^(2*b+3) *> [0] *> [0] *> qright x r).
  replace (2*b+3) with (1+(2*b+2)) by lia. follow11 T_page.
  rewrite qodd_first_page.
  replace (1+(2*b+2)) with (2*(b+1)+1) by lia. unfold qright.
  change ([0] *> [1;1;1;1;0] *> U^^(2*x+2) *> [0] *> r)
    with ([0;1;1;1;1;0] *> U^^(2*x+2) *> [0] *> r).
  replace (2*x+2) with (1+(2*x+1)) by lia. follow10 T_page.
  rewrite qodd_second_page. finish.
Qed.

Lemma Q_odd_shield indices a b s v r :
  2<=b -> 24<=4*a+6*b+2*s+10 ->
  exists aa rr, 24<=aa /\ 6<=2*b+3 /\
    Qfront (2*a+1) (2*b+1) (exit_chain (2*a) indices s v r) -->+
    shield aa (12*a+10) (2*b+3) rr.
Proof.
  intros Hb Hsize.
  destruct (exit_chain_return indices (4*a+6*b+7) (12*a+9) [] (6*a+4) (2*b+3)
    (b+1) (2*a) s v r) as [aa [rr [Hbound H]]].
  exists aa,rr. split; [lia|]. split; [lia|]. follow10 Q_odd_entry.
  unfold qodd_left. replace (2*(2*a+1)+6*b+5) with (4*a+6*b+7) by lia.
  replace (3*(2*a+1)+1) with (6*a+4) by lia.
  replace (6*(2*a+1)+3) with (12*a+9) by lia.
  replace (2*(2*a+1)+2) with (2*(2*a)+4) by lia.
  eapply evstep_trans; [apply progress_evstep,H|]. unfold shield.
  replace ((12*a+10)/2-1) with (6*a+4).
  - replace (12*a+9+1) with (12*a+10) by lia. finish.
  - replace (12*a+10) with ((6*a+5)*2) by lia. rewrite Nat.div_mul by lia. lia.
Qed.

Lemma qframe_exit_chain x z indices s v r : 0<x -> 0<z ->
  qframe x z (exit_chain (x-1) indices s v r) = exit_chain (z-1) ((x-1)::indices) s v r.
Proof.
  intros Hx Hz. cbn[exit_chain]. unfold qframe,callback_payload,callback_middle.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn[core_bits flat_map block_bits]].
  replace (z-1+2) with (z+1) by lia.
  replace (z+2) with (1+(z+1)) by lia.
  replace (2*x) with (2*(x-1)+2) by lia.
  rewrite (@lpow_add _ (2*(x-1)) 2 U).
  cbn[Nat.add lpow]. rewrite !Str_app_assoc. reflexivity.
Qed.

Definition pure_page c r := page ([Three]^^c) *> r.
Definition page_header c r := [1;1;1;1;0] *> U^^c *> [0] *> r.

Lemma pure_page_header c r : pure_page c r = page_header c ([0] *> r).
Proof. unfold pure_page,page,page_header. rewrite core_bits_threes,!Str_app_assoc. reflexivity. Qed.

Lemma header_core m c r :
  [0;1]^^(2*m) *> [0] *> page_header (c+2) r =
  core_suffix (2*m+1) ([Three]^^c++[Three]) r.
Proof.
  replace (2*m+1) with (1+2*m) by lia.
  rewrite lpow_shift. change ([Three]++[Three]^^c) with ([Three]^^(1+c)).
  rewrite positive_page_form. unfold page_header.
  replace (1+(1+c)) with (c+2) by lia. reflexivity.
Qed.

Lemma page_row_next a b gaps n c :
  [Three]^^c++row a (gaps++[b])++Six::[Three]^^(n+2) =
  row (a+c) (((n+1)::gaps)++[b])++[Three].
Proof.
  cbn[row app]. rewrite <- row_prepend.
  replace (n+2) with ((n+1)+1) by lia.
  rewrite (@lpow_add _ (n+1) 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma page_row a b gaps n m c r :
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*m+1) *> [0] *> page_header (1+c) r) -->+
  tilted (row (a+c) (((n+1)::gaps)++[b])++[Three]) m ([0;1]^^(1+c) *> r).
Proof.
  unfold page_header.
  change ([0] *> [1;1;1;1;0] *> U^^(1+c) *> [0] *> r)
    with ([0;1;1;1;1;0] *> U^^(1+c) *> [0] *> r).
  follow10 T_page. rewrite page_row_next. finish.
Qed.

Definition RowReturn a b gaps n m r := exists delta tail,
  tilted (row a (gaps++[b])++[Three]) n ([0;1]^^(2*m+1) *> [0] *> r) -->+
  counter_pair (a+delta+1) (b+1) (saved_pages gaps tail).

Lemma row_return_odd_page a b gaps n m z r :
  RowReturn (a+2*z) b ((n+1)::gaps) m z r ->
  RowReturn a b gaps n m (pure_page (2*z+1) r).
Proof.
  intros [delta [tail H]].
  exists (2*z+delta),(page ([Three]^^(n+1)) *> tail).
  rewrite pure_page_header. replace (2*z+1) with (1+2*z) by lia.
  follow11 page_row. replace (1+2*z) with (2*z+1) by lia. follow10 H.
  replace (a+2*z+delta+1) with (a+(2*z+delta)+1) by lia. finish.
Qed.

Lemma row_return_even_page a b gaps n m z d r :
  RowReturn a b gaps n m (pure_page (2*z+2) (page_header (d+2) r)).
Proof.
  exists (2*z+1),(page ([Three]^^(n+2)) *> saved_body m (z+1) ([Three]^^d) r).
  rewrite pure_page_header. replace (2*z+2) with (1+(2*z+1)) by lia.
  follow11 page_row. replace (1+(2*z+1)) with (2*(z+1)) by lia.
  rewrite header_core. cbn[app]. rewrite row_last_three.
  replace (n+1+1) with (n+2) by lia.
  follow10 (T_odd_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  replace (1+(a+(2*z+1))) with (a+(2*z+1)+1) by lia.
  replace (1+b) with (b+1) by lia. finish.
Qed.

Lemma short_pure_pages z d r :
  [0;1]^^(2*z+2) *> [0] *> pure_page 1 (pure_page (d+2) r) =
  short_page_suffix (z+1) d ([0] *> r).
Proof.
  unfold short_page_suffix.
  replace (2*(z+1)+1) with (1+(2*z+2)) by lia.
  change (@nil block) with ([Three]^^0). rewrite positive_page_form.
  unfold pure_page,page. rewrite !core_bits_threes,!Str_app_assoc. reflexivity.
Qed.

Lemma row_return_even_page_short a b gaps n m z d r :
  RowReturn a b gaps n (1+m) (pure_page (2*z+2) (pure_page 1 (pure_page (d+2) r))).
Proof.
  exists (2*z+1),(page ([Three]^^(n+2)) *>
    saved_body m (z+1+2) (Six::[Three]^^d) ([0] *> r)).
  rewrite pure_page_header. replace (2*z+2) with (1+(2*z+1)) by lia.
  follow11 page_row. replace (1+(2*z+1)) with (2*z+2) by lia.
  rewrite short_pure_pages. cbn[app]. rewrite row_last_three.
  replace (n+1+1) with (n+2) by lia.
  follow10 (T_short_page_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  replace (1+(a+(2*z+1))) with (a+(2*z+1)+1) by lia.
  replace (1+b) with (b+1) by lia. finish.
Qed.

Definition frame_core s v := [Three]^^(s+2)++Six::v.
Definition frame_body s v r :=
  core_bits ([Three]^^(s+3)++Six::v++[Three;Three]) *> [0;0;1;0;1] *> r.

Lemma frame_body_core p s v r :
  [0;1]^^p *> frame_body s v r =
  core_suffix p (frame_core s v++[Three]) ([0;1;0;1] *> r).
Proof.
  unfold frame_body,frame_core,core_suffix.
  replace (s+3) with (1+(s+2)) by lia. cbn[Nat.add lpow].
  repeat first [rewrite <- app_assoc | progress cbn[app]]. reflexivity.
Qed.

Lemma row_return_odd_mixed a b gaps n m z s v r :
  RowReturn a b gaps n m (page_header (2*z+1) (frame_body s v r)).
Proof.
  exists (2*z),(page ([Three]^^(n+2)) *>
    saved_body m z (frame_core s v) ([0;1;0;1] *> r)).
  replace (2*z+1) with (1+2*z) by lia. follow11 page_row.
  replace (1+2*z) with (2*z+1) by lia. rewrite frame_body_core.
  cbn[app]. rewrite row_last_three. replace (n+1+1) with (n+2) by lia.
  follow10 (T_odd_frontier (a+2*z) b ((n+2)::gaps)).
  replace (1+(a+2*z)) with (a+2*z+1) by lia.
  replace (1+b) with (b+1) by lia. finish.
Qed.

Fixpoint frame_pages t indices s v r := match indices with
  [] => pure_page (t+1) (page_header (t+3) (frame_body s v r))
  | z::indices => pure_page t (pure_page (t+4) (frame_pages z indices s v r)) end.

Lemma frame_pages_return indices : Forall (fun z => 1<=z) indices ->
  forall t a b gaps n m s v r, 1<=t -> RowReturn a b gaps n m (frame_pages t indices s v r).
Proof.
  intro Hindices. induction Hindices as [|z indices Hz Hindices IH];
    intros t a b gaps n m s v r Ht; cbn[frame_pages].
  - pose proof (Nat.div_mod t 2 ltac:(lia)). pose proof (Nat.mod_upper_bound t 2 ltac:(lia)).
    destruct (Nat.eq_dec (t mod 2) 0).
    + replace (t+1) with (2*(t/2)+1) by lia. apply row_return_odd_page.
      replace (t+3) with (2*(t/2+1)+1) by lia. apply row_return_odd_mixed.
    + replace (t+1) with (2*(t/2)+2) by lia.
      replace (t+3) with ((2*(t/2)+2)+2) by lia. apply row_return_even_page.
  - pose proof (Nat.div_mod t 2 ltac:(lia)). pose proof (Nat.mod_upper_bound t 2 ltac:(lia)).
    destruct (Nat.eq_dec (t mod 2) 0).
    + rewrite (pure_page_header (t+4)).
      replace t with (2*(t/2-1)+2) at 1 by lia.
      replace (t+4) with ((t+2)+2) by lia. apply row_return_even_page.
    + replace t with (2*(t/2)+1) at 1 by lia. apply row_return_odd_page.
      replace (t+4) with (2*(t/2+2)+1) by lia.
      apply row_return_odd_page. apply IH. exact Hz.
Qed.

Lemma leading_page_frames_return indices : Forall (fun z => 1<=z) indices ->
  forall t a b gaps n k s v r, 1<=t ->
    RowReturn a b gaps n (k+1) (pure_page (k+3) (frame_pages t indices s v r)).
Proof.
  intros Hindices t a b gaps n k s v r Ht.
  pose proof (Nat.div_mod k 2 ltac:(lia)). pose proof (Nat.mod_upper_bound k 2 ltac:(lia)).
  destruct (Nat.eq_dec (k mod 2) 0).
  - replace (k+3) with (2*(k/2+1)+1) by lia.
    apply row_return_odd_page. apply frame_pages_return; assumption.
  - replace (k+3) with (2*(k/2+1)+2) by lia.
    destruct indices as [|z indices]; cbn[frame_pages].
    + rewrite (pure_page_header (t+1)).
      replace (t+1) with ((t-1)+2) by lia. apply row_return_even_page.
    + destruct t as [|[|t]]; [lia| |].
      * replace (k+1) with (1+k) by lia.
        change (1+4) with (3+2). apply row_return_even_page_short.
      * rewrite (pure_page_header (S (S t))).
        replace (S (S t)) with (t+2) by lia. apply row_return_even_page.
Qed.

Fixpoint chain_growth indices : nat := match indices with
  [] => 0 | z::indices => 2*z+1+chain_growth indices end.

Lemma saved_frame_body t s v r :
  saved_body (t+2) (s+2) (v++[Three;Three]) r = page_header (t+3) (frame_body s v r).
Proof.
  unfold saved_body,page_header,frame_body.
  repeat first [rewrite core_bits_app | rewrite core_bits_threes |
    progress cbn[core_bits flat_map block_bits]].
  replace (1+(t+2)) with (t+3) by lia.
  replace (1+(s+2)) with (s+3) by lia. rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma exit_chain_pages indices : forall a b gaps n t s v r,
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*t+4) *> exit_chain t indices s (v++[Three;Three]) r) -->+
  counter_pair (a+chain_growth indices+2*s+3) (b+1)
    (saved_pages gaps (pure_page (n+2) (frame_pages t indices s v r))).
Proof.
  induction indices as [|z indices IH]; intros a b gaps n t s v r.
  - cbn[exit_chain chain_growth frame_pages]. follow10 callback_row_exit.
    rewrite saved_pages_append. cbn[saved_pages]. rewrite saved_frame_body.
    replace (a+0+2*s+3) with (a+2*s+3) by lia. finish.
  - cbn[exit_chain chain_growth]. follow11 callback_link.
    rewrite callback_next_row.
    follow10 (IH (a+2*z+1) b (t::(n+2)::gaps) (t+2) z s v r).
    cbn[saved_pages frame_pages].
    replace (t+2+2) with (t+4) by lia.
    replace (a+2*z+1+chain_growth indices+2*s+3) with
      (a+(2*z+1+chain_growth indices)+2*s+3) by lia. finish.
Qed.

Definition q_page_a x b indices s := 2*x+6*b+chain_growth indices+2*s+8.
Definition q_page_output x b indices s v r :=
  counter_pair (q_page_a x b indices s) (6*x+4)
    (pure_page (3*x+1) (pure_page (2*b+3) (pure_page (b+3)
      (frame_pages (x-1) indices s v r)))).

Lemma Q_page_return x b indices s v r : 1<=x ->
  Qfront x (2*b+1) (exit_chain (x-1) indices s (v++[Three;Three]) r) -->+
  q_page_output x b indices s v r.
Proof.
  intro Hx. follow11 Q_odd_entry. unfold qodd_left.
  replace (2*x+2) with (2*(x-1)+4) by lia.
  follow10 (exit_chain_pages indices (2*x+6*b+5) (6*x+3) [2*b+3;3*x+1]).
  cbn[saved_pages]. unfold q_page_output,q_page_a.
  replace (2*x+6*b+5+chain_growth indices+2*s+3) with
    (2*x+6*b+chain_growth indices+2*s+8) by lia.
  replace (6*x+3+1) with (6*x+4) by lia.
  replace (b+1+2) with (b+3) by lia. finish.
Qed.

Lemma pure_page_row a b gaps n m c r :
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*m+1) *> [0] *> pure_page (1+c) r) -->+
  tilted (row (a+c) (((n+1)::gaps)++[b])++[Three]) m ([0;1]^^(1+c) *> [0] *> r).
Proof. rewrite pure_page_header. apply page_row. Qed.

Definition even_stage k x b r :=
  tilted (row (18*x+2*b+2) [6*x+2;k+1;2*k+3]++[Three]) (3*x)
    ([0;1]^^(2*(b+1)+1) *> [0] *> r).

Lemma even_stage_pair k x :
  [Three]^^(12*x)++Six::[Three]^^(2*k+4) = row (12*x) [2*k+3]++[Three].
Proof.
  cbn[row]. replace (2*k+4) with ((2*k+3)+1) by lia.
  rewrite (@lpow_add _ (2*k+3) 1 [Three]).
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma even_stage_return k x b r :
  counter_pair (2*k+2) (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3) r)) -->+
  even_stage k x b r.
Proof.
  follow11 paired_even. rewrite even_stage_pair.
  replace (12*x+3) with (2*(6*x+1)+1) by lia.
  replace (6*x+1) with (1+6*x) at 2 by lia.
  follow11 (pure_page_row (12*x) (2*k+3) []).
  replace (12*x+6*x) with (18*x) by lia.
  replace (1+6*x) with (2*(3*x)+1) by lia.
  replace (2*b+3) with (1+(2*b+2)) by lia.
  follow10 (pure_page_row (18*x) (2*k+3) [k+1]).
  unfold even_stage. replace (18*x+(2*b+2)) with (18*x+2*b+2) by lia.
  replace (6*x+1+1) with (6*x+2) by lia.
  replace (1+(2*b+2)) with (2*(b+1)+1) by lia. finish.
Qed.

Definition odd_stage h x b r :=
  tilted (row (18*x+2*b-2) [6*x+2;h+2;h;h+1;2*h+7]++[Three]) (3*x)
    ([0;1]^^(2*(b+1)+1) *> [0] *> r).

Lemma odd_stage_pair h x :
  [Three]^^(12*x-4)++odd_outer h = row (12*x-4) [h;h+1;2*h+7]++[Three].
Proof.
  unfold odd_outer. cbn[row].
  rewrite (@lpow_add _ h 1 [Three]) at 2.
  repeat first [rewrite <- app_assoc | progress cbn[app lpow]]. reflexivity.
Qed.

Lemma odd_stage_return h x b r : 1<=x ->
  counter_pair (2*h+3) (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3) r)) -->+
  odd_stage h x b r.
Proof.
  intro Hx. replace (12*x+4) with ((12*x-4)+8) by lia.
  follow11 paired_odd. rewrite odd_stage_pair.
  replace (12*x-4+7) with (2*(6*x+1)+1) by lia.
  replace (6*x+1) with (1+6*x) at 2 by lia.
  follow11 (pure_page_row (12*x-4) (2*h+7) [h;h+1]).
  replace (12*x-4+6*x) with (18*x-4) by lia.
  replace (h+1+1) with (h+2) by lia.
  replace (1+6*x) with (2*(3*x)+1) by lia.
  replace (2*b+3) with (1+(2*b+2)) by lia.
  follow10 (pure_page_row (18*x-4) (2*h+7) [h+2;h;h+1]).
  unfold odd_stage. replace (18*x-4+(2*b+2)) with (18*x+2*b-2) by lia.
  replace (6*x+1+1) with (6*x+2) by lia.
  replace (1+(2*b+2)) with (2*(b+1)+1) by lia. finish.
Qed.

Lemma even_frontier_frame_shield a x b indices s v r :
  5<=a -> 1<=x -> 2<=b -> Forall (fun z => 1<=z) indices ->
  exists aa rr, 24<=aa /\
    counter_pair (4*a+4) (12*x+4)
      (pure_page (6*x+1) (pure_page (2*b+3) (pure_page (b+3)
        (frame_pages (2*x-1) indices s v r)))) -->+ shield aa (4*a+6) (6*x+2) rr.
Proof.
  intros Ha Hx Hb Hindices.
  destruct (leading_page_frames_return indices Hindices (2*x-1) (18*x+2*b+2)
    (4*a+5) [6*x+2;2*a+2] (3*x) b s v r ltac:(lia)) as [delta [rr H]].
  exists (18*x+2*b+2+delta+1),rr. split; [lia|].
  replace (4*a+4) with (2*(2*a+1)+2) by lia. follow11 even_stage_return.
  unfold even_stage. replace (2*a+1+1) with (2*a+2) by lia.
  replace (2*(2*a+1)+3) with (4*a+5) by lia. follow10 H.
  unfold shield. cbn[saved_pages].
  replace (4*a+5+1) with (4*a+6) by lia.
  replace ((4*a+6)/2-1) with (2*a+2); [finish|].
  replace (4*a+6) with ((2*a+3)*2) by lia. rewrite Nat.div_mul by lia. lia.
Qed.

Lemma frame_pages_header t indices s v r : 2<=t ->
  exists d tail, frame_pages t indices s v r = page_header (d+2) tail.
Proof.
  intro Ht. destruct indices as [|z indices]; cbn[frame_pages]; rewrite pure_page_header.
  - exists (t-1),([0] *> page_header (t+3) (frame_body s v r)).
    replace (t-1+2) with (t+1) by lia. reflexivity.
  - exists (t-2),([0] *> pure_page (t+4) (frame_pages z indices s v r)).
    replace (t-2+2) with t by lia. reflexivity.
Qed.

Lemma odd_page_frames_prefix indices t a b gaps n m h s v r :
  1<=t -> Forall (fun z => 1<=z) indices ->
  exists aa tail, a+2*h+3<=aa /\
    tilted (row a (gaps++[b])++[Three]) n
      ([0;1]^^(2*m+1) *> [0] *> pure_page (2*h+3) (frame_pages t indices s v r)) -->+
    counter_pair aa (b+1) (saved_pages gaps (pure_page (n+1) tail)).
Proof.
  intros Ht Hindices.
  destruct (frame_pages_return indices Hindices t (a+2*h+2) b ((n+1)::gaps)
    m (h+1) s v r Ht) as [delta [tail H]].
  exists (a+2*h+2+delta+1),tail. split; [lia|].
  replace (2*h+3) with (1+(2*h+2)) by lia.
  follow11 pure_page_row.
  replace (a+(2*h+2)) with (a+2*h+2) by lia.
  replace (1+(2*h+2)) with (2*(h+1)+1) by lia. exact H.
Qed.

Lemma even_page_header_return a b gaps n m z d r :
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*m+1) *> [0] *> pure_page (2*z+2) (page_header (d+2) r)) -->+
  counter_pair (a+2*z+2) (b+1)
    (saved_pages gaps (pure_page (n+2) (saved_body m (z+1) ([Three]^^d) r))).
Proof.
  replace (2*z+2) with (1+(2*z+1)) by lia. follow11 pure_page_row.
  replace (1+(2*z+1)) with (2*(z+1)) by lia. rewrite header_core.
  cbn[app]. rewrite row_last_three. replace (n+1+1) with (n+2) by lia.
  follow10 (T_odd_frontier (a+(2*z+1)) b ((n+2)::gaps)).
  replace (1+(a+(2*z+1))) with (a+2*z+2) by lia.
  replace (1+b) with (b+1) by lia. finish.
Qed.

Lemma even_page_frames_prefix indices t a b gaps n m h s v r :
  2<=t -> exists tail,
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*m+1) *> [0] *> pure_page (2*h+4) (frame_pages t indices s v r)) -->+
  counter_pair (a+2*h+4) (b+1) (saved_pages gaps (pure_page (n+2) tail)).
Proof.
  intro Ht. destruct (frame_pages_header t indices s v r Ht) as [d [tail Hform]].
  exists (saved_body m (h+2) ([Three]^^d) tail). rewrite Hform.
  replace (2*h+4) with (2*(h+1)+2) by lia.
  replace (a+2*h+4) with (a+2*(h+1)+2) by lia.
  replace (h+2) with (h+1+1) by lia. apply even_page_header_return.
Qed.

Lemma odd_even_header_return a b gaps n m h z d r :
  tilted (row a (gaps++[b])++[Three]) n
    ([0;1]^^(2*m+1) *> [0] *> pure_page (2*h+3) (pure_page (2*z+2) (page_header (d+2) r))) -->+
  counter_pair (a+2*h+2*z+4) (b+1)
    (saved_pages gaps (pure_page (n+1) (pure_page (m+2)
      (saved_body (h+1) (z+1) ([Three]^^d) r)))).
Proof.
  replace (2*h+3) with (1+(2*h+2)) by lia. follow11 pure_page_row.
  replace (a+(2*h+2)) with (a+2*h+2) by lia.
  replace (1+(2*h+2)) with (2*(h+1)+1) by lia.
  follow10 (even_page_header_return (a+2*h+2) b ((n+1)::gaps)).
  replace (a+2*h+2+2*z+2) with (a+2*h+2*z+4) by lia. finish.
Qed.

Lemma odd_triple_frames_prefix indices t a b gaps h x s v r :
  1<=x -> 1<=t -> Forall (fun z => 1<=z) indices ->
  exists aa tail, a+2*h+4*x+3<=aa /\
    tilted (row a (gaps++[b])++[Three]) (3*x)
      ([0;1]^^(2*(2*h+1)+1) *> [0] *> pure_page (2*h+3)
        (pure_page (2*x-1) (pure_page (2*x+3) (frame_pages t indices s v r)))) -->+
    counter_pair aa (b+1) (saved_pages gaps
      (pure_page (3*x+1) (pure_page (2*h+2) (pure_page (h+2) tail)))).
Proof.
  intros Hx Ht Hindices.
  destruct (frame_pages_return indices Hindices t (a+2*h+4*x+2) b
    ((h+2)::(2*h+2)::(3*x+1)::gaps) (x-1) (x+1) s v r Ht) as [delta [tail H]].
  exists (a+2*h+4*x+2+delta+1),tail. split; [lia|].
  replace (2*h+3) with (1+(2*h+2)) by lia. follow11 pure_page_row.
  replace (a+(2*h+2)) with (a+2*h+2) by lia.
  replace (1+(2*h+2)) with (2*(h+1)+1) by lia.
  replace (2*x-1) with (1+(2*x-2)) by lia.
  follow11 (pure_page_row (a+2*h+2) b ((3*x+1)::gaps)).
  replace (a+2*h+2+(2*x-2)) with (a+2*h+2*x) by lia.
  replace (2*h+1+1) with (2*h+2) by lia.
  replace (1+(2*x-2)) with (2*(x-1)+1) by lia.
  replace (2*x+3) with (1+(2*x+2)) by lia.
  follow11 (pure_page_row (a+2*h+2*x) b ((2*h+2)::(3*x+1)::gaps)).
  replace (a+2*h+2*x+(2*x+2)) with (a+2*h+4*x+2) by lia.
  replace (h+1+1) with (h+2) by lia.
  replace (1+(2*x+2)) with (2*(x+1)+1) by lia. exact H.
Qed.

Definition q_pages_front a x b indices s v r :=
  counter_pair a (12*x+4) (pure_page (6*x+1) (pure_page (2*b+3)
    (pure_page (b+3) (frame_pages (2*x-1) indices s v r)))).
Definition K5front a c x h r := counter_pair a (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+1) (pure_page (2*h+2) (pure_page (h+2) r))))).
Definition O5front a k x offset r := counter_pair a (2*k+6)
  (pure_page k (pure_page (k-1) (pure_page (k+1) (pure_page (6*x+2) (pure_page (3*x+offset) r))))).
Definition KEmptyFront c x h r := counter_pair (20*x+6*h+4) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+1)
    (pure_page (2*h+3) (saved_body (h+1) x ([Three]^^(2*x)) r))))).
Definition BOddNonemptyFront c x h r := counter_pair (18*x+6*h+8) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+2)
    (saved_body (2*h+2) (h+2) ([Three]^^(2*x-3)) ([0] *> pure_page (2*x+3) r))))).
Definition BOddEmptyFront c x h r := counter_pair (18*x+6*h+8) (2*c+2)
  (pure_page c (pure_page (6*x+2) (pure_page (3*x+2)
    (saved_body (2*h+2) (h+2) ([Three]^^(2*x-2)) ([0] *> page_header (2*x+2) r))))).

Ltac align := first [reflexivity | lia |
  progress cbn[app saved_pages frame_pages]; align |
  progress f_equal; align].
Ltac follow_aligned H :=
  let T := type of H in
  lazymatch T with ?c -->+ _ =>
    lazymatch goal with |- ?g -->+ _ => replace g with c by align; follow10 H end
  end.

Lemma q_pages_even_nonempty k x h z indices s v r :
  3<=x -> 3<=h -> 1<=z -> Forall (fun n => 1<=n) indices ->
  exists aa tail, 24<=aa /\
    q_pages_front (2*k+2) x (2*h) (z::indices) s v r -->+ K5front aa (k+1) x h tail.
Proof.
  intros Hx Hh Hz Hindices.
  destruct (odd_triple_frames_prefix indices z (18*x+2*(2*h)+2) (2*k+3)
    [6*x+2;k+1] h x s v r ltac:(lia) Hz Hindices) as [aa [tail [Ha H]]].
  exists aa,tail. split; [lia|]. unfold q_pages_front. follow11 even_stage_return.
  unfold even_stage. cbn[frame_pages]. follow_aligned H.
  unfold K5front,pure_page. cbn[saved_pages]. finish; align.
Qed.

Lemma q_pages_bodd_nonempty k x h z indices s v r : 2<=x ->
  q_pages_front (2*k+2) x (2*h+1) (z::indices) s v r -->+
  BOddNonemptyFront (k+1) x h (frame_pages z indices s v r).
Proof.
  intro Hx. unfold q_pages_front. follow11 even_stage_return.
  pose proof (even_page_header_return (18*x+2*(2*h+1)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+2) (h+1) (2*x-3)
    ([0] *> pure_page (2*x+3) (frame_pages z indices s v r))) as H.
  unfold even_stage. cbn[frame_pages]. rewrite (pure_page_header (2*x-1)).
  follow_aligned H. unfold BOddNonemptyFront,pure_page. cbn[saved_pages]. finish; align.
Qed.

Lemma q_pages_bodd_empty k x h s v r : 2<=x ->
  q_pages_front (2*k+2) x (2*h+1) [] s v r -->+ BOddEmptyFront (k+1) x h (frame_body s v r).
Proof.
  intro Hx. unfold q_pages_front. follow11 even_stage_return.
  pose proof (even_page_header_return (18*x+2*(2*h+1)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+2) (h+1) (2*x-2) ([0] *> page_header (2*x+2) (frame_body s v r))) as H.
  unfold even_stage. cbn[frame_pages]. rewrite (pure_page_header (2*x-1+1)).
  follow_aligned H. unfold BOddEmptyFront,pure_page. cbn[saved_pages]. finish; align.
Qed.

Lemma q_pages_even_empty k x h s v r : 2<=x ->
  q_pages_front (2*k+2) x (2*h) [] s v r -->+ KEmptyFront (k+1) x h (frame_body s v r).
Proof.
  intro Hx. unfold q_pages_front. follow11 even_stage_return.
  unfold even_stage. cbn[frame_pages].
  pose proof (odd_even_header_return (18*x+2*(2*h)+2) (2*k+3) [6*x+2;k+1]
    (3*x) (2*h+1) h (x-1) (2*x) (frame_body s v r)) as H.
  follow_aligned H. unfold KEmptyFront,pure_page. cbn[saved_pages]. finish; align.
Qed.

Lemma q_pages_odd k x b indices s v r :
  11<=k -> 3<=x -> 6<=b -> Forall (fun n => 1<=n) indices ->
  exists aa (offset:nat) tail, 24<=aa /\ (offset=1%nat \/ offset=2) /\
    q_pages_front (2*k+3) x b indices s v r -->+ O5front aa (k+1) x offset tail.
Proof.
  intros Hk Hx Hb Hindices.


  remember (b/2) as h. assert (Hcases : b=2*h \/ b=2*h+1) by lia.
  destruct Hcases as [Hform|Hform]; subst b.
  - destruct (odd_page_frames_prefix indices (2*x-1) (18*x+2*(2*h)-2)
      (2*k+7) [6*x+2;k+2;k;k+1] (3*x) (2*h+1) h s v r ltac:(lia) Hindices)
      as [aa [tail [Ha H]]].
    exists aa,1%nat,tail. split; [lia|]. split; [left; reflexivity|].
    unfold q_pages_front.
    follow11 (odd_stage_return k x (2*h)
      (pure_page (2*h+3) (frame_pages (2*x-1) indices s v r)) ltac:(lia)).
    unfold odd_stage. follow_aligned H. unfold O5front,pure_page. cbn[saved_pages]. finish; align.
  - destruct (even_page_frames_prefix indices (2*x-1) (18*x+2*(2*h+1)-2)
      (2*k+7) [6*x+2;k+2;k;k+1] (3*x) (2*h+2) h s v r ltac:(lia)) as [tail H].
    exists (18*x+2*(2*h+1)-2+2*h+4),2,tail.
    split; [lia|]. split; [right; reflexivity|].
    unfold q_pages_front.
    follow11 (odd_stage_return k x (2*h+1)
      (pure_page (2*h+1+3) (frame_pages (2*x-1) indices s v r)) ltac:(lia)).
    unfold odd_stage. follow_aligned H. unfold O5front,pure_page. cbn[saved_pages]. finish; align.
Qed.

Definition prefix_S22 a b c r := counter_pair (24+a) (22+4*b)
  (pure_page (10+2*b) (pure_page (6+c) r)).
Definition prefix_H0 a b c r := counter_pair (28+6*a) (26+2*c)
  (pure_page (13+c) (saved_body (10+2*a) (5+a) ([Three]^^(4+b)) ([0] *> r))).
Definition prefix_H1 a b r := counter_pair (38+6*a) (26+2*b)
  (pure_page (13+b) (saved_body (14+2*a) (6+a) ([Three]^^(9+2*a)) ([0] *> r))).
Definition prefix_QShield a b c r := counter_pair (38+6*a) (30+6*b)
  (pure_page (15+3*b) (saved_body (13+2*a) (7+a) ([Three]^^(9+2*b))
    (callback_payload (3+b) (2+c) ([0] *> r)))).
Definition prefix_QH1 a b r := counter_pair (38+6*a) (40+6*b)
  (pure_page (20+3*b) (saved_body (13+2*a) (7+a) ([Three]^^(13+2*b))
    (callback_payload (4+b) (7+2*b) ([0] *> r)))).
Definition folded_front x y z r := tilted
  (row (3*x+6*y+25) [y+4;2*y+6;4*x+14;8*x+29]) (x+5)
  ([0;1]^^(x+4) *> core_bits ([Three]^^(x+4)++Six::[Three]^^(2*x+6)) *>
    [0;0;1;0;1;0] *> pure_page (z+2) r).
Definition two_gap_front x y r := tilted
  (row (9*x+37) [x+2*y+14;2*x+4*y+27]) (3*x+14)
  ([0;1]^^(3*x+12) *> [0] *> pure_page (3*x+11) (pure_page (3*x+13) r)).
Definition mixed_prefix_target c :=
  (exists a b d r, c=prefix_S22 a b d r) \/
  (exists a b r, c=prefix_H1 a b r) \/
  (exists a b d r, c=prefix_H0 a b d r) \/
  (exists a b d r, c=prefix_QShield a b d r) \/
  (exists a b r, c=prefix_QH1 a b r).
Inductive mixed_return c : Prop :=
| return_step d : c -->+ d -> mixed_prefix_target d -> mixed_return c.

Lemma mixed_return_trans c d : c -->+ d -> mixed_return d -> mixed_return c.
Proof.
  intros H [e He HP]. eapply return_step; [eapply progress_trans; eassumption|exact HP].
Qed.

Lemma mixed_return_here c d : c -->+ d -> mixed_prefix_target d -> mixed_return c.
Proof. apply return_step. Qed.

Lemma mixed_return_change c d : c=d -> mixed_return d -> mixed_return c.
Proof. intros -> H. exact H. Qed.

Set Primitive Projections.
Record affine := Aff { offset:N; coef_a:N; coef_b:N; coef_c:N; coef_d:N }.
Unset Primitive Projections.
Arguments Aff (_ _ _ _ _)%_N.
Definition affine_value a (v:list nat) := N.to_nat (offset a)+N.to_nat (coef_a a)*nth 0 v 0%nat+
  N.to_nat (coef_b a)*nth 1 v 0%nat+N.to_nat (coef_c a)*nth 2 v 0%nat+N.to_nat (coef_d a)*nth 3 v 0%nat.
Definition affine_const n := Aff n 0 0 0 0.
Definition affine_add a b := (Aff (offset a+offset b) (coef_a a+coef_a b)
  (coef_b a+coef_b b) (coef_c a+coef_c b) (coef_d a+coef_d b))%N.
Definition affine_scale k a := (Aff (k*offset a) (k*coef_a a)
  (k*coef_b a) (k*coef_c a) (k*coef_d a))%N.
Definition affine_sub a b := (Aff (offset a-offset b) (coef_a a-coef_a b)
  (coef_b a-coef_b b) (coef_c a-coef_c b) (coef_d a-coef_d b))%N.
Definition affine_le a b := ((offset a<=?offset b)%N&&(coef_a a<=?coef_a b)%N&&
  (coef_b a<=?coef_b b)%N&&(coef_c a<=?coef_c b)%N&&(coef_d a<=?coef_d b)%N)%bool.
Definition constant_affine a := match a with Aff n 0 0 0 0 => Some n | _ => None end.
Definition zero_affine a := match a with Aff 0 0 0 0 0 => true | _ => false end.

Lemma affine_const_value n v : affine_value (affine_const n) v=N.to_nat n.
Proof. unfold affine_value,affine_const; cbn; lia. Qed.
Lemma affine_add_value a b v : affine_value (affine_add a b) v=affine_value a v+affine_value b v.
Proof. destruct a,b; unfold affine_value,affine_add; cbn; rewrite !N2Nat.inj_add; nia. Qed.
Lemma affine_scale_value k a v : affine_value (affine_scale k a) v=N.to_nat k*affine_value a v.
Proof. destruct a; unfold affine_value,affine_scale; cbn; rewrite !N2Nat.inj_mul; nia. Qed.
Lemma affine_sub_add a b : affine_le b a=true -> affine_add (affine_sub a b) b=a.
Proof.
  destruct a,b; unfold affine_le,affine_add,affine_sub; cbn.
  rewrite !Bool.andb_true_iff,!N.leb_le. intros [[[[H0 H1] H2] H3] H4]. f_equal; lia.
Qed.
Lemma affine_sub_value a b v : affine_le b a=true ->
  affine_value (affine_sub a b) v=affine_value a v-affine_value b v.
Proof.
  intro H. pose proof (f_equal (fun a => affine_value a v) (affine_sub_add a b H)) as E.
  change (affine_value (affine_add (affine_sub a b) b) v=affine_value a v) in E.
  rewrite affine_add_value in E. lia.
Qed.
Lemma constant_affine_value a n v : constant_affine a=Some n -> affine_value a v=N.to_nat n.
Proof.
  destruct a as [c [|a] [|b] [|d] [|e]]; cbn[constant_affine]; try discriminate.
  intros H; inversion H; subst. unfold affine_value; cbn[offset coef_a coef_b coef_c coef_d]. lia.
Qed.
Lemma zero_affine_value a v : zero_affine a=true -> affine_value a v=0%nat.
Proof. destruct a as [[|c] [|a] [|b] [|d] [|e]]; cbn; try discriminate; reflexivity. Qed.

Inductive nat_expr := NConst (n:N) | NVar (i:nat) | NAdd (a b:nat_expr)
  | NMul (a b:nat_expr) | NSub (a b:nat_expr).
Arguments NConst _%_N.
Fixpoint nat_value e (v:list nat) := match e with
  | NConst n => N.to_nat n | NVar i => nth i v 0%nat
  | NAdd a b => nat_value a v+nat_value b v
  | NMul a b => nat_value a v*nat_value b v
  | NSub a b => nat_value a v-nat_value b v end.
Fixpoint affine_normal e : option affine := match e with
  | NConst n => Some (affine_const n)
  | NVar 0 => Some (Aff 0 1 0 0 0) | NVar 1 => Some (Aff 0 0 1 0 0)
  | NVar 2 => Some (Aff 0 0 0 1 0) | NVar 3 => Some (Aff 0 0 0 0 1) | NVar _ => None
  | NAdd a b => match affine_normal a,affine_normal b with
      Some x,Some y => Some (affine_add x y) | _,_ => None end
  | NMul a b => match affine_normal a,affine_normal b with
    | Some x,Some y => match constant_affine x with
      | Some k => Some (affine_scale k y)
      | None => match constant_affine y with Some k => Some (affine_scale k x) | None => None end end
    | _,_ => None end
  | NSub a b => match affine_normal a,affine_normal b with
      Some x,Some y => if affine_le y x then Some (affine_sub x y) else None | _,_ => None end end.

Lemma affine_normal_sound e a : affine_normal e=Some a -> forall v, nat_value e v=affine_value a v.
Proof.
  gen a. induction e; intros a H v; cbn[affine_normal] in H.
  - inversion H; subst; cbn[nat_value]; symmetry; apply affine_const_value.
  - destruct i as [|[|[|[|i]]]]; try discriminate; inversion H; subst;
      unfold affine_value; cbn[nat_value offset coef_a coef_b coef_c coef_d]; lia.
  - destruct (affine_normal e1) as [x|] eqn:Hx; try discriminate.
    destruct (affine_normal e2) as [y|] eqn:Hy; try discriminate.
    inversion H; subst; cbn[nat_value]. rewrite (IHe1 x eq_refl v),(IHe2 y eq_refl v),affine_add_value. reflexivity.
  - destruct (affine_normal e1) as [x|] eqn:Hx; try discriminate.
    destruct (affine_normal e2) as [y|] eqn:Hy; try discriminate.
    cbn[nat_value]. rewrite (IHe1 x eq_refl v),(IHe2 y eq_refl v).
    destruct (constant_affine x) as [k|] eqn:Hk.
    + inversion H; subst. rewrite affine_scale_value,(constant_affine_value x k v Hk). reflexivity.
    + destruct (constant_affine y) as [k|] eqn:Hl; try discriminate.
      inversion H; subst. rewrite affine_scale_value,(constant_affine_value y k v Hl). lia.
  - destruct (affine_normal e1) as [x|] eqn:Hx; try discriminate.
    destruct (affine_normal e2) as [y|] eqn:Hy; try discriminate.
    destruct (affine_le y x) eqn:Hle; try discriminate.
    inversion H; subst; cbn[nat_value]. rewrite (IHe1 x eq_refl v),(IHe2 y eq_refl v).
    symmetry. apply affine_sub_value,Hle.
Qed.

Lemma nat_equal_sound a b x : affine_normal a=Some x -> affine_normal b=Some x ->
  forall v, nat_value a v=nat_value b v.
Proof. intros Ha Hb v. rewrite (affine_normal_sound a x Ha v),(affine_normal_sound b x Hb v). reflexivity. Qed.

Inductive core_expr := CEmpty | CAppend (a b:core_expr) | CBlock (b:block) | CPower (n:nat_expr).
Fixpoint core_value e v := match e with
  | CEmpty => [] | CAppend a b => core_value a v++core_value b v
  | CBlock b => [b] | CPower n => [Three]^^(nat_value n v) end.
Inductive word_expr := WEmpty | WAppend (a b:word_expr)
  | WPower (n:nat_expr) (w:list Sym) | WCore (c:core_expr).
Fixpoint word_value e v := match e with
  | WEmpty => [] | WAppend a b => word_value a v++word_value b v
  | WPower n w => w^^(nat_value n v) | WCore c => core_bits (core_value c v) end.
Inductive side_expr := STail | SPrefix (w:word_expr) (r:side_expr).
Fixpoint side_value e v r := match e with
  | STail => r | SPrefix w t => word_value w v *> side_value t v r end.
Fixpoint side_word e := match e with
  | STail => WEmpty | SPrefix w t => WAppend w (side_word t) end.

Lemma side_word_value e v r : side_value e v r=word_value (side_word e) v *> r.
Proof.
  induction e; cbn[side_value side_word word_value]; [reflexivity|].
  rewrite IHe. symmetry. apply Str_app_assoc.
Qed.

Inductive word_segment := Rep (a:affine) (w:list Sym).
Definition segment_value x v := match x with Rep a w => w^^(affine_value a v) end.
Fixpoint segments_value xs v := match xs with [] => [] | x::xs => segment_value x v++segments_value xs v end.

Lemma segments_app xs ys v : segments_value (xs++ys) v=segments_value xs v++segments_value ys v.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs,app_assoc; reflexivity]. Qed.

Fixpoint compile_core e : option (list word_segment) := match e with
  | CEmpty => Some [] | CBlock b => Some [Rep (affine_const 1) (block_bits b)]
  | CPower n => match affine_normal n with Some a => Some [Rep a U] | None => None end
  | CAppend a b => match compile_core a,compile_core b with Some x,Some y => Some (x++y) | _,_ => None end end.
Fixpoint compile_word e : option (list word_segment) := match e with
  | WEmpty => Some [] | WCore c => compile_core c
  | WPower n w => match affine_normal n with Some a => Some [Rep a w] | None => None end
  | WAppend a b => match compile_word a,compile_word b with Some x,Some y => Some (x++y) | _,_ => None end end.

Lemma compile_core_sound e xs : compile_core e=Some xs ->
  forall v, core_bits (core_value e v)=segments_value xs v.
Proof.
  gen xs. induction e; intros xs H v; cbn[compile_core] in H.
  - inversion H; reflexivity.
  - destruct (compile_core e1) as [p|] eqn:Hp; try discriminate.
    destruct (compile_core e2) as [q|] eqn:Hq; try discriminate.
    inversion H; subst; cbn[core_value].
    rewrite core_bits_app,(IHe1 p eq_refl v),(IHe2 q eq_refl v),segments_app. reflexivity.
  - inversion H; subst. cbn[core_value segments_value segment_value].
    rewrite affine_const_value. destruct b; reflexivity.
  - destruct (affine_normal n) as [a|] eqn:Ha; try discriminate.
    inversion H; subst; cbn[core_value segments_value segment_value].
    rewrite core_bits_threes,(affine_normal_sound n a Ha v),app_nil_r. reflexivity.
Qed.

Lemma compile_word_sound e xs : compile_word e=Some xs -> forall v, word_value e v=segments_value xs v.
Proof.
  gen xs. induction e; intros xs H v; cbn[compile_word] in H.
  - inversion H; reflexivity.
  - destruct (compile_word e1) as [p|] eqn:Hp; try discriminate.
    destruct (compile_word e2) as [q|] eqn:Hq; try discriminate.
    inversion H; subst; cbn[word_value]. rewrite (IHe1 p eq_refl v),(IHe2 q eq_refl v),segments_app. reflexivity.
  - destruct (affine_normal n) as [a|] eqn:Ha; try discriminate.
    inversion H; subst; cbn[word_value segments_value segment_value].
    rewrite (affine_normal_sound n a Ha v),app_nil_r. reflexivity.
  - cbn[word_value]. apply compile_core_sound,H.
Qed.

Fixpoint word_eqb (x y:list Sym) := match x,y with
  | [],[] => true | a::x,b::y => (sym_eqb a b&&word_eqb x y)%bool | _,_ => false end.
Lemma word_eqb_sound x y : word_eqb x y=true -> x=y.
Proof.
  gen y. induction x; intros [|b y]; cbn[word_eqb]; try discriminate; auto.
  rewrite Bool.andb_true_iff. intros [H T].
  apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in H; subst.
  f_equal. apply IHx,T.
Qed.

Lemma empty_power n : (@nil Sym)^^n=[].
Proof. induction n; cbn[lpow app]; auto. Qed.

Definition empty_segment x := match x with Rep a w =>
  (zero_affine a||match w with [] => true | _ => false end)%bool end.
Lemma empty_segment_sound x : empty_segment x=true -> forall v, segment_value x v=[].
Proof.
  destruct x as [a w]. cbn[empty_segment]. rewrite Bool.orb_true_iff. intros [H|H] v.
  - cbn[segment_value]. rewrite (zero_affine_value a v H). reflexivity.
  - destruct w; try discriminate. apply empty_power.
Qed.
Fixpoint trim_segments xs := match xs with
  | [] => [] | x::xs => if empty_segment x then trim_segments xs else x::xs end.
Lemma trim_segments_value xs v : segments_value (trim_segments xs) v=segments_value xs v.
Proof.
  induction xs as [|x xs IH]; cbn[trim_segments]; [reflexivity|].
  destruct (empty_segment x) eqn:H; [|reflexivity].
  cbn[segments_value]. rewrite (empty_segment_sound x H v). exact IH.
Qed.

Definition cancel_segments xs ys := match xs,ys with
  | Rep a w::xs,Rep b z::ys => if word_eqb w z then
      if affine_le a b then Some (xs,Rep (affine_sub b a) z::ys) else
      if affine_le b a then Some (Rep (affine_sub a b) w::xs,ys) else None
    else None
  | _,_ => None end.
Lemma segment_split a b (w:list Sym) v : affine_le a b=true ->
  w^^(affine_value b v)=w^^(affine_value a v)++w^^(affine_value (affine_sub b a) v).
Proof.
  intro H. pose proof (f_equal (fun b => affine_value b v) (affine_sub_add b a H)) as E.
  change (affine_value (affine_add (affine_sub b a) a) v=affine_value b v) in E.
  rewrite affine_add_value in E.
  replace (affine_value b v) with (affine_value a v+affine_value (affine_sub b a) v) by lia.
  apply lpow_add.
Qed.
Lemma cancel_segments_sound xs ys p q : cancel_segments xs ys=Some (p,q) ->
  forall v, segments_value p v=segments_value q v -> segments_value xs v=segments_value ys v.
Proof.
  destruct xs as [|[a w] xs]; [destruct ys; discriminate|].
  destruct ys as [|[b z] ys]; [discriminate|]. cbn[cancel_segments].
  destruct (word_eqb w z) eqn:Hw; try discriminate. apply word_eqb_sound in Hw; subst z.
  destruct (affine_le a b) eqn:Hab.
  - intro H; inversion H; subst; intros v E; cbn[segments_value segment_value] in *.
    rewrite (segment_split a b w v Hab),<-app_assoc,E. reflexivity.
  - destruct (affine_le b a) eqn:Hba; try discriminate.
    intro H; inversion H; subst; intros v E; cbn[segments_value segment_value] in *.
    rewrite (segment_split b a w v Hba),<-app_assoc,E. reflexivity.
Qed.

Lemma rotate_power n (b:Sym) w r : (b::w)^^n++b::r=b::((w++[b])^^n++r).
Proof.
  induction n; cbn[lpow]; [reflexivity|].
  cbn[app]. repeat rewrite <-app_assoc. rewrite IHn.
  cbn[app]. repeat rewrite <-app_assoc. reflexivity.
Qed.
Definition affine_dec a := Aff (N.pred (offset a)) (coef_a a) (coef_b a) (coef_c a) (coef_d a).
Lemma affine_dec_value a v : (0<offset a)%N -> affine_value a v=S (affine_value (affine_dec a) v).
Proof.
  destruct a as [c a b d e]. unfold affine_value,affine_dec; cbn[offset coef_a coef_b coef_c coef_d].
  rewrite N2Nat.inj_pred. intro H.
  assert (0<N.to_nat c) by (destruct c; cbn in *; [lia|apply Pos2Nat.is_pos]). lia.
Qed.

Fixpoint expose_segment xs : option (Sym*list word_segment) := match xs with
  | [] => None | Rep a []::xs => expose_segment xs
  | Rep a (b::w)::xs => if zero_affine a then expose_segment xs else
    match offset a with
    | Npos _ => Some (b,Rep (affine_const 1) w::Rep (affine_dec a) (b::w)::xs)
    | N0 => match expose_segment xs with
      | Some (c,ys) => if sym_eqb b c then Some (b,Rep a (w++[b])::ys) else None
      | None => None end end end.
Lemma expose_segment_sound xs b ys : expose_segment xs=Some (b,ys) ->
  forall v, segments_value xs v=b::segments_value ys v.
Proof.
  gen b ys. induction xs as [|[a w] xs IH]; intros b ys H v; try discriminate.
  destruct w as [|c w].
  - cbn[expose_segment] in H. cbn[segments_value segment_value].
    rewrite empty_power. apply IH,H.
  - cbn[expose_segment] in H. destruct (zero_affine a) eqn:Hz.
    + cbn[segments_value segment_value]. rewrite (zero_affine_value a v Hz). apply IH,H.
    + destruct (offset a) eqn:Hn.
      * destruct (expose_segment xs) as [[d zs]|] eqn:He; try discriminate.
        destruct (sym_eqb c d) eqn:Hcd; try discriminate.
        apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in Hcd; subst d.
        inversion H; subst; cbn[segments_value segment_value].
        rewrite (IH b zs eq_refl v). apply rotate_power.
      * inversion H; subst; cbn[segments_value segment_value].
        rewrite (affine_dec_value a v ltac:(lia)),affine_const_value.
        change (N.to_nat 1%N) with 1%nat.
        cbn[lpow]. repeat rewrite <-app_assoc. reflexivity.
Qed.

Definition no_segments (xs ys:list word_segment) := match xs,ys with [],[] => true | _,_ => false end.
Fixpoint segments_equal fuel xs ys := match fuel with
  | O => false | S fuel => let x:=trim_segments xs in let y:=trim_segments ys in
    if no_segments x y then true else match cancel_segments x y with
    | Some (p,q) => segments_equal fuel p q
    | None => match expose_segment x,expose_segment y with
      | Some (b,p),Some (c,q) => (sym_eqb b c&&segments_equal fuel p q)%bool
      | _,_ => false end end end.
Lemma segments_equal_sound fuel xs ys : segments_equal fuel xs ys=true ->
  forall v, segments_value xs v=segments_value ys v.
Proof.
  gen xs ys. induction fuel as [|fuel IH]; intros xs ys H v; try discriminate.
  cbn[segments_equal] in H. rewrite <-(trim_segments_value xs v),<-(trim_segments_value ys v).
  remember (trim_segments xs) as x in *; remember (trim_segments ys) as y in *.
  destruct (no_segments x y) eqn:He.
  - destruct x,y; try discriminate; reflexivity.
  - destruct (cancel_segments x y) as [[p q]|] eqn:Hc.
    + eapply cancel_segments_sound; [exact Hc|]. apply IH,H.
    + destruct (expose_segment x) as [[b p]|] eqn:Hx; try discriminate.
      destruct (expose_segment y) as [[c q]|] eqn:Hy; try discriminate.
      apply Bool.andb_true_iff in H. destruct H as [Hbc Hrest].
      apply (proj2 (Bool.reflect_iff _ _ (sym_eqb_spec _ _))) in Hbc; subst c.
      rewrite (expose_segment_sound x b p Hx v),(expose_segment_sound y b q Hy v).
      f_equal. apply IH,Hrest.
Qed.

Definition word_equal fuel a b := match compile_word a,compile_word b with
  | Some x,Some y => segments_equal fuel x y | _,_ => false end.
Lemma word_equal_sound fuel a b : word_equal fuel a b=true -> forall v, word_value a v=word_value b v.
Proof.
  unfold word_equal. destruct (compile_word a) as [x|] eqn:Hx; try discriminate.
  destruct (compile_word b) as [y|] eqn:Hy; try discriminate. intros H v.
  rewrite (compile_word_sound a x Hx v),(compile_word_sound b y Hy v). apply (segments_equal_sound fuel x y H v).
Qed.
Lemma side_equal_sound fuel a b : word_equal fuel (side_word a) (side_word b)=true ->
  forall v r, side_value a v r=side_value b v r.
Proof. intros H v r. rewrite !side_word_value,(word_equal_sound fuel _ _ H v). reflexivity. Qed.

Lemma core_bits_injective u v : core_bits u=core_bits v -> u=v.
Proof.
  gen v. induction u as [|b u IH]; intros [|c v] H.
  - reflexivity.
  - destruct c; discriminate.
  - destruct b; discriminate.
  - destruct b,c; cbn[core_bits flat_map block_bits U V app] in H; try discriminate;
      f_equal; apply IH; congruence.
Qed.

Ltac fast_refl := lazymatch goal with |- ?a = ?b =>
  first [constr_eq a b; reflexivity | is_evar a; reflexivity | is_evar b; reflexivity] end.
Ltac split_application tac := lazymatch goal with
  | |- ?f ?a ?b = ?f ?c ?d => apply (f_equal2 f); [tac|tac]
  | |- ?f ?a = ?f ?b => apply (f_equal f); tac end.

Ltac positive_literal p := lazymatch p with
  | xH => constr:(true) | xO ?p => positive_literal p | xI ?p => positive_literal p
  | _ => constr:(false) end.
Ltac nat_literal n := lazymatch n with
  | O => constr:(Some 0%N)
  | S O => constr:(Some 1%N)
  | S (S O) => constr:(Some 2%N)
  | S _ => let p := eval vm_compute in (N.of_nat n) in
      lazymatch p with Npos ?q => let literal := positive_literal q in
        lazymatch literal with true => constr:(Some p) | false => constr:(@None N) end
      | _ => constr:(@None N) end
  | _ => constr:(@None N) end.
Ltac literal_bits w := lazymatch w with
  | [] => constr:(true)
  | S0::?w => literal_bits w
  | S1::?w => literal_bits w
  | _ => constr:(false)
  end.
Ltac atom_index n env := lazymatch env with
  | [] => constr:(@None nat)
  | ?x::?xs => lazymatch constr:((n,x)) with
    | (?v,?v) => constr:(Some 0%nat)
    | _ => let i := atom_index n xs in lazymatch i with
      | Some ?i => constr:(Some (S i)) | None => constr:(@None nat) end end end.
Ltac quote_nat n env kont := lazymatch n with
  | N.to_nat ?n => kont uconstr:(NConst n) env
  | _ => let literal := nat_literal n in lazymatch literal with
  | Some ?n => kont uconstr:(NConst n) env
  | None => lazymatch n with
    | S ?n => quote_nat n env ltac:(fun a env => kont uconstr:(NAdd (NConst 1) a) env)
    | ?a+?b => quote_nat a env ltac:(fun a env => quote_nat b env ltac:(fun b env => kont uconstr:(NAdd a b) env))
    | ?a*?b => quote_nat a env ltac:(fun a env => quote_nat b env ltac:(fun b env => kont uconstr:(NMul a b) env))
    | ?a-?b => quote_nat a env ltac:(fun a env => quote_nat b env ltac:(fun b env => kont uconstr:(NSub a b) env))
    | _ => let i := atom_index n env in lazymatch i with
      | Some ?i => kont uconstr:(NVar i) env
      | None => let i := eval cbv[List.length] in (List.length env) in
          let env := eval cbv[app] in (env++[n]) in kont uconstr:(NVar i) env end end end end.
Ltac quote_row a xs env kont := lazymatch xs with
  | [] => quote_nat a env ltac:(fun a env => kont uconstr:(CPower a) env)
  | ?b::?xs => quote_row a xs env ltac:(fun w env =>
      quote_nat b env ltac:(fun b env => kont uconstr:(CAppend w (CAppend (CBlock Six) (CPower b))) env)) end.
Ltac quote_core w env kont := lazymatch w with
  | [] => kont uconstr:(CEmpty) env
  | [Three]^^?n => quote_nat n env ltac:(fun n env => kont uconstr:(CPower n) env)
  | row ?a ?xs => let xs := eval cbv[app] in xs in quote_row a xs env kont
  | ?b::?w => quote_core w env ltac:(fun w env => kont uconstr:(CAppend (CBlock b) w) env)
  | ?u++?v => quote_core u env ltac:(fun u env => quote_core v env ltac:(fun v env => kont uconstr:(CAppend u v) env))
  | odd_outer _ => let w := eval unfold odd_outer in w in quote_core w env kont
  | page_core _ _ _ => let w := eval unfold page_core in w in quote_core w env kont end.
Ltac quote_word w env kont :=
  let w := eval cbv beta iota zeta delta[U V] in w in
  let literal := literal_bits w in lazymatch literal with
  | true => kont uconstr:(WPower (NConst 1) w) env
  | false => lazymatch w with
    | ?w^^?n => quote_nat n env ltac:(fun n env => kont uconstr:(WPower n w) env)
    | core_bits ?w => quote_core w env ltac:(fun w env => kont uconstr:(WCore w) env)
    | page _ => let w := eval unfold page in w in quote_word w env kont
    | ?u++?v => quote_word u env ltac:(fun u env => quote_word v env ltac:(fun v env => kont uconstr:(WAppend u v) env))
    | ?s::?w => quote_word w env ltac:(fun w env => kont uconstr:(WAppend (WPower (NConst 1) [s]) w) env) end end.
Ltac quote_side_to stop fuel r env kont :=
  tryif constr_eq r stop then kont uconstr:(STail) env r else lazymatch fuel with
  | O => kont uconstr:(STail) env r
  | S ?fuel =>
  let r := lazymatch r with
  | ?w *> ?t => r | ?s >> ?t => r
  | _ => eval cbv beta iota zeta delta[pure_page page_header saved_body core_suffix
    frame_body qright qframe callback_payload callback_middle saved_pages] in r end in
  lazymatch r with
  | ?w *> ?r => quote_word w env ltac:(fun w env => quote_side_to stop fuel r env ltac:(fun r env tail => kont uconstr:(SPrefix w r) env tail))
  | ?s >> ?r => quote_side_to stop fuel r env ltac:(fun r env tail => kont uconstr:(SPrefix (WPower (NConst 1) [s]) r) env tail)
  | _ => kont uconstr:(STail) env r end end.
Ltac quote_side r env kont := quote_side_to constr:(0inf) constr:(16) r env kont.
Ltac common_tail a b := lazymatch a with
  | context[b] => b
  | _ => lazymatch b with ?w *> ?r => common_tail a r | ?s >> ?r => common_tail a r | _ => b end end.
Ltac reflected_tape_eq := lazymatch goal with |- ?a = ?b =>
  let a := eval cbv beta iota zeta delta[pure_page page_header saved_body core_suffix
    frame_body qright qframe callback_payload callback_middle saved_pages] in a in
  let b := eval cbv beta iota zeta delta[pure_page page_header saved_body core_suffix
    frame_body qright qframe callback_payload callback_middle saved_pages] in b in
  let stop := common_tail a b in
  quote_side_to stop constr:(64) a constr:(@nil nat) ltac:(fun a env tail =>
  quote_side_to stop constr:(64) b env ltac:(fun b env tail' =>
    unify tail tail';
    change (side_value a env tail=side_value b env tail);
    apply (side_equal_sound (N.to_nat 64%N) a b); reflexivity)) end.
Ltac reflected_core_eq := lazymatch goal with |- ?a = ?b =>
  quote_core a constr:(@nil nat) ltac:(fun a env =>
  quote_core b env ltac:(fun b env =>
    apply core_bits_injective;
    change (word_value (WCore a) env=word_value (WCore b) env);
    apply (word_equal_sound (N.to_nat 64%N) (WCore a) (WCore b)); reflexivity)) end.
Ltac reflected_nat_eq := lazymatch goal with |- ?a = ?b =>
  quote_nat a constr:(@nil nat) ltac:(fun a env =>
  quote_nat b env ltac:(fun b env =>
    let x := eval vm_compute in (affine_normal a) in lazymatch x with Some ?x =>
      change (nat_value a env=nat_value b env);
      apply (nat_equal_sound a b x); reflexivity end)) end.
Ltac scalar_eq := first [reflected_nat_eq|lia].
Ltac term_eq := first [fast_refl|
  lazymatch goal with |- @eq nat _ _ => lia end|split_application term_eq].
Ltac core_eq := first [fast_refl|reflected_core_eq|term_eq].
Ltac native_tape_eq := first [fast_refl|reflected_tape_eq|
  unfold saved_pages,callback_payload,callback_middle,core_suffix,saved_body,pure_page,page_header,page;
  rewrite ?core_bits_app,?core_bits_threes,?Str_app_assoc;
  cbn[Str_app app block_bits U V]; term_eq].
Ltac native_eq :=
  unfold prefix_S22,prefix_H0,prefix_H1,prefix_QShield,prefix_QH1,folded_front,two_gap_front;
  lazymatch goal with
  | |- counter_pair _ _ _ = counter_pair _ _ _ =>
      apply (f_equal3 counter_pair); [first [fast_refl|scalar_eq]|first [fast_refl|scalar_eq]|native_tape_eq]
  | |- tilted _ _ _ = tilted _ _ _ =>
      apply (f_equal3 tilted); [core_eq|first [fast_refl|scalar_eq]|native_tape_eq]
  | |- carried _ _ = carried _ _ =>
      apply (f_equal2 carried); [core_eq|native_tape_eq]
  | |- W _ _ = W _ _ => apply (f_equal2 W); [core_eq|native_tape_eq]
  end.

Definition affine_quotient a n d :=
  if ((n<=?offset a)%N&&((offset a-n) mod d=?0)%N&&(coef_a a mod d=?0)%N&&
      (coef_b a mod d=?0)%N&&(coef_c a mod d=?0)%N&&(coef_d a mod d=?0)%N)%bool
  then (Some (Aff ((offset a-n)/d) (coef_a a/d) (coef_b a/d) (coef_c a/d) (coef_d a/d)))%N
  else None.
Fixpoint join_runs xs ys := match xs with
  | [] => ys | [a] => match ys with [] => xs | b::ys => affine_add a b::ys end
  | a::xs => a::join_runs xs ys end.
Fixpoint core_runs e := match e with
  | CEmpty => Some [affine_const 0]
  | CBlock Three => Some [affine_const 1]
  | CBlock Six => Some [affine_const 0;affine_const 0]
  | CPower n => match affine_normal n with Some a => Some [a] | None => None end
  | CAppend a b => match core_runs a,core_runs b with
      Some x,Some y => Some (join_runs x y) | _,_ => None end end.
Definition reduce_runs xs a b := match xs with
  | [] => [] | x::xs => match rev (affine_sub x (affine_const a)::xs) with
    | [] => [] | y::ys => rev (affine_sub y (affine_const b)::ys) end end.
Fixpoint cycle_eq p rest w := match w with
  | [] => true | b::w => match rest with
    | [] => match p with [] => false | c::rest => if sym_eqb b c then cycle_eq p rest w else false end
    | c::rest => if sym_eqb b c then cycle_eq p rest w else false end end.
Definition stop_run p (rest:list Sym) (n:affine) xs :=
  let head := firstn (List.length p-List.length rest) p in
  (n,match head with [] => xs | _ => Rep (affine_const 1) head::xs end).
Fixpoint scan_run (fuel:nat) p rest n xs := match fuel with
  | O => None
  | S fuel => match xs with
    | [] => Some (stop_run p rest n xs)
    | Rep a w::ys => if empty_segment (Rep a w) then scan_run fuel p rest n ys else
      if cycle_eq p rest (w^^(List.length p)) then
        scan_run fuel p rest (affine_add n (affine_scale (N.of_nat (List.length w/List.length p)) a)) ys
      else match offset a,w,rest with
      | Npos _,b::w',c::rest' => if sym_eqb b c then
        let ys := Rep (affine_const 1) w'::Rep (affine_dec a) w::ys in
        match rest' with
        | [] => scan_run fuel p p (affine_add n (affine_const 1)) ys
        | _ => scan_run fuel p rest' n ys end
        else Some (stop_run p rest n xs)
      | _,_,_ => None end end end.
Definition scan_prefix p xs := scan_run 256 p p (affine_const 0) xs.
Fixpoint skip_symbols (fuel n:nat) xs {struct fuel} := match n with
  | O => Some xs
  | S n' => match fuel,xs with
    | S fuel,Rep a w::ys => if empty_segment (Rep a w) then skip_symbols fuel n ys else
      match offset a,w with
      | Npos _,b::w' => skip_symbols fuel n' (Rep (affine_const 1) w'::Rep (affine_dec a) w::ys)
      | _,_ => None end
    | _,_ => None end end.
Fixpoint scan_more (fuel:nat) xs cs := match fuel with
  | O => None
  | S fuel => match scan_prefix V xs with
    | Some (n,_) => if zero_affine n then Some (rev cs,xs) else
      match offset n with
      | Npos _ => match skip_symbols 256 7 xs with
        | Some xs => match scan_prefix U xs with
          | Some (a,xs) => scan_more fuel xs (a::cs) | None => None end
        | None => None end
      | _ => None end
    | None => None end end.
Definition scan_core xs := match scan_prefix U xs with
  | Some (a,xs) => scan_more 64 xs [a] | None => None end.
Inductive macro_choice := Choice (tag:nat) (args u v:list affine) (tail:list word_segment).
Definition choose_pair a b := match affine_quotient a 2 2 with
  | Some k => Some (Choice 0 [k;affine_sub b (affine_const 4)] [] [] [])
  | None => match affine_quotient a 3 2 with
    | Some k => Some (Choice 1 [k;affine_sub b (affine_const 8)] [] [] [])
    | None => None end end.
Definition choose_tilted joined wc xs := match scan_prefix [S0;S1] xs with
  | Some (p,xs) => match (match affine_quotient p 2 2 with
    | Some m => Some (true,m)
    | None => match affine_quotient p 1 2 with Some m => Some (false,m) | None => None end end) with
    | Some (even,m) => match scan_core xs with
    | Some (cs,xs) => match skip_symbols 256 1 xs with
      | Some xs => if even then match cs with
          | [a] => Some (Choice 2 [m;affine_sub a (affine_const 2)] (reduce_runs wc 0 1) [] xs)
          | _ => if (joined&&(0<?offset (last wc (affine_const 0)))%N&&
                          (1<?offset (last cs (affine_const 0)))%N)%bool
            then Some (Choice 5 [m] (reduce_runs wc 0 1) (reduce_runs cs 1 2) xs)
            else Some (Choice 3 [m] [] (reduce_runs cs 1 1) xs) end
        else match wc with
          | a::b::g => Some (Choice 4 [a;b;m] (rev g) (reduce_runs cs 1 2) xs)
          | _ => None end
      | None => None end
    | None => None end
    | None => None end
  | None => None end.
Definition choose_carried wc xs := match scan_core xs with
  | Some (cs,xs) => match skip_symbols 256 1 xs with
    | Some xs => Some (Choice 6 [] (reduce_runs wc 0 1) (reduce_runs cs 0 1) xs)
    | None => None end
  | None => None end.
Definition choose_W wc := match rev wc with
  | b::n::cs => Some (Choice 7 [n;b] (rev cs) [] []) | _ => None end.
Fixpoint scan_headers ns xs := match ns with
  | [] => Some ([],xs)
  | n::ns => match skip_symbols 256 n xs with
    | Some xs => match scan_prefix U xs with
      | Some (a,xs) => match scan_headers ns xs with
        | Some (cs,xs) => Some (a::cs,xs) | None => None end
      | None => None end
    | None => None end end.
Definition choose_target (which:nat) a b xs := match which with
  | O => match affine_quotient b 22 4,scan_headers [5;7] xs with
    | Some b,Some ([p;c],xs) => match skip_symbols 256 2 xs with
      | Some xs => Some ([affine_sub a (affine_const 24);b;affine_sub c (affine_const 6)],xs)
      | None => None end
    | _,_ => None end
  | _ => match affine_quotient a 38 6,affine_quotient b 26 2,scan_headers [5;7;1%nat;7] xs with
    | Some a,Some b,Some (_,xs) => match skip_symbols 256 6 xs with
      | Some xs => Some ([a;b],xs) | None => None end
    | _,_,_ => None end end.

Ltac compact_nat n := lazymatch n with
  | N0 => constr:(0%nat) | Npos xH => constr:(1%nat) | Npos (xO xH) => constr:(2)
  | _ => constr:(N.to_nat n) end.
Ltac affine_terms cs env := lazymatch constr:((cs,env)) with
  | (?c::?cs,?x::?env) => let rest := affine_terms cs env in
    lazymatch c with
    | N0 => rest | _ => let t := lazymatch c with Npos xH => x |
        _ => let c := compact_nat c in constr:(x*c) end in
        lazymatch rest with O => t | _ => constr:(t+rest) end end
  | _ => constr:(0%nat) end.
Ltac unquote_affine a env := lazymatch a with Aff ?n ?a ?b ?c ?d =>
  let t := affine_terms constr:([a;b;c;d]) env in
  let n := compact_nat n in
  lazymatch constr:((n,t)) with (O,_) => t | (_,O) => n | _ => constr:(t+n) end end.
Ltac unquote_runs xs env := lazymatch xs with
  | [] => uconstr:(@nil block)
  | [?a] => let a := unquote_affine a env in uconstr:([Three]^^a)
  | ?a::?xs => let a := unquote_affine a env in let xs := unquote_runs xs env in uconstr:([Three]^^a++Six::xs) end.
Ltac unquote_args xs env := lazymatch xs with
  | [] => constr:(@nil nat) | ?a::?xs => let a := unquote_affine a env in
      let xs := unquote_args xs env in constr:(a::xs) end.
Ltac unquote_segments xs env r := lazymatch xs with
  | [] => r | Rep _ []::?xs => unquote_segments xs env r
  | Rep ?a ?w::?xs => let n := unquote_affine a env in
    let r := unquote_segments xs env r in lazymatch n with
    | O => r | S O => uconstr:(w *> r) | _ => uconstr:(w^^n *> r) end end.
Ltac quote_right fuel wc r env kont :=
  quote_side_to constr:(0inf) fuel r env ltac:(fun r env tail =>
    let parts := eval vm_compute in (compile_word (side_word r)) in
    lazymatch parts with Some ?xs => kont wc xs env tail end).
Ltac quote_parts w r kont := quote_core w constr:(@nil nat) ltac:(fun w env =>
  let parts := eval vm_compute in (core_runs w) in
  lazymatch parts with Some ?wc =>
    first [quote_right constr:(5) wc r env kont|quote_right constr:(8) wc r env kont|
      quote_right constr:(16) wc r env kont] end).
Ltac use_choice choice env r w n step := lazymatch choice with
  | Some (Choice ?tag ?args ?u ?v ?xs) =>
    let args := unquote_args args env in
    let tail := unquote_segments xs env r in
    let v := unquote_runs v env in
    lazymatch constr:((tag,args)) with
    | (O,[?k;?b]) => step constr:(1%nat) constr:(paired_even k b r)
    | (S O,[?k;?b]) => step constr:(1%nat) constr:(paired_odd k b r)
    | (2%nat,[?m;?c]) => let u := unquote_runs u env in step constr:(1%nat) constr:(T_page u n m c tail)
    | (3%nat,[?m]) => step constr:(1%nat) constr:(T_even w n m v tail)
    | (4%nat,[?a;?b;?m]) => let g := unquote_args u env in step constr:(1%nat) constr:(T_odd_frontier a b g n m v tail)
    | (5%nat,[?m]) => let u := unquote_runs u env in step constr:(2) constr:(T_even_return u n m v tail)
    | (6%nat,[]) => let u := unquote_runs u env in step constr:(1%nat) constr:(carried_return u v tail)
    | (7%nat,[?n;?b]) => let u := unquote_runs u env in step constr:(1%nat) constr:(W_multi_six u n b r)
    end end.
Ltac computed_macro fuel step c :=
  let joined := lazymatch fuel with S (S _) => constr:(true) | _ => constr:(false) end in
  lazymatch c with
  | counter_pair ?a ?b ?r => quote_nat a constr:(@nil nat) ltac:(fun a env =>
      quote_nat b env ltac:(fun b env =>
      let choice := eval vm_compute in (match affine_normal a,affine_normal b with
        Some na,Some nb => choose_pair na nb | _,_ => None end) in
      use_choice choice env r constr:(@nil block) constr:(0%nat) step))
  | tilted ?w ?n ?r => quote_parts w r ltac:(fun wc xs env r =>
      let choice := eval vm_compute in (choose_tilted joined wc xs) in use_choice choice env r w n step)
  | carried ?w ?r => quote_parts w r ltac:(fun wc xs env r =>
      let choice := eval vm_compute in (choose_carried wc xs) in use_choice choice env r w constr:(0%nat) step)
  | W ?w ?r => quote_core w constr:(@nil nat) ltac:(fun w env =>
      let choice := eval vm_compute in (match core_runs w with Some wc => choose_W wc | None => None end) in
      use_choice choice env r constr:(@nil block) constr:(0%nat) step)
  end.
Ltac native_step bridge H :=
  let T := type of H in lazymatch T with ?c -->+ ?d =>
    lazymatch goal with
    | |- mixed_return ?g => simple refine (mixed_return_change g c _ (bridge c d H _));
        [native_eq|idtac]
    end
  end.
Ltac next_macro fuel kont c := computed_macro fuel kont c.
Ltac macros n := lazymatch goal with |- mixed_return ?c =>
  next_macro n ltac:(fun used H => let rest := eval cbv[Nat.sub] in (n-used) in
    lazymatch rest with
    | O => native_step mixed_return_here H
    | _ => native_step mixed_return_trans H; macros rest
    end) c end.

Opaque counter_pair tilted carried W.

Ltac common_macros fuel used kont := lazymatch fuel with
  | O => kont used
  | S _ => lazymatch goal with |- mixed_return ?c =>
      first [next_macro fuel ltac:(fun count H =>
        native_step mixed_return_trans H;
        let rest := eval cbv[Nat.sub] in (fuel-count) in
        let used := eval cbv[Nat.add] in (used+count) in common_macros rest used kont) c |
        kont used]
    end
  end.
Ltac infer_target which c kont :=
  lazymatch c with counter_pair ?a ?b ?r =>
    quote_nat a constr:(@nil nat) ltac:(fun a env => quote_nat b env ltac:(fun b env =>
    quote_side r env ltac:(fun r env tail =>
      let result := eval vm_compute in (match affine_normal a,affine_normal b,compile_word (side_word r) with
        | Some na,Some nb,Some segments => choose_target which na nb segments | _,_,_ => None end) in
      lazymatch result with Some (?args,?xs) =>
        let args := unquote_args args env in let tail := unquote_segments xs env tail in kont args tail end))) end.
Ltac target_member which args tail :=
  unfold mixed_prefix_target;
  lazymatch which with
  | O => left | S O => right; left | S (S O) => right; right; left
  | S (S (S O)) => right; right; right; left | _ => right; right; right; right end;
  lazymatch args with
  | [?a;?b;?c] => exists a,b,c
  | [?a;?b] => exists a,b end;
  tail; native_eq.
Ltac leaf total used which args :=
  let n := eval cbv[Nat.sub] in (total-used) in macros n;
  lazymatch args with
  | [] => lazymatch goal with |- mixed_prefix_target ?c =>
      infer_target which c ltac:(fun args tail => target_member which args ltac:(exists tail)) end
  | _ => target_member which args ltac:(eexists) end.

Ltac begin_cases := pose (0%nat) as macro_depth.
Ltac advance_common shortest :=
  match goal with depth := ?used : nat |- _ =>
  let fuel := eval cbv[Nat.sub] in (shortest-1-used) in
  common_macros fuel used ltac:(fun used => clear depth; pose used as macro_depth) end.
Ltac parity x shortest :=
  advance_common shortest;
  let k := fresh "k" in let H := fresh "Hparity" in
  destruct (mod2 x) as [k H|k H];
  [rewrite Nat.mul_comm in H|rewrite Nat.mul_comm,Nat.add_comm in H];
  subst x; rename k into x.
Ltac return_to total which args :=
  match goal with depth := ?used : nat |- _ => leaf total used which args end.

Tactic Notation "split_parity" ident(x) constr(n) := parity x n.
Tactic Notation "split_zero" ident(x) constr(n) := advance_common n; destruct x as [|x].
Tactic Notation "return_S22" constr(n) := return_to n constr:(0%nat) constr:(@nil nat).
Tactic Notation "return_H1" constr(n) := return_to n constr:(1%nat) constr:(@nil nat).
Tactic Notation "return_QShield" constr(n) constr(args) := return_to n constr:(3) args.
Tactic Notation "return_QH1" constr(n) constr(args) := return_to n constr:(4) args.

Lemma folded_returns x y z r : mixed_return (folded_front x y z r).
Proof.
  unfold folded_front. begin_cases. split_parity x 1%nat.
  - return_S22 4.
  - return_S22 1%nat.
Qed.

Lemma two_gap_returns x y r : mixed_return (two_gap_front x y r).
Proof.
  unfold two_gap_front. begin_cases. split_parity x 1%nat.
  - return_H1 1%nat.
  - return_S22 2.
Qed.

Ltac folded_case := lazymatch goal with |- mixed_return (tilted ?w ?n ?r) =>
  quote_nat n constr:(@nil nat) ltac:(fun ne env =>
  quote_core w env ltac:(fun we env =>
  quote_side r env ltac:(fun re env tail =>
    let data := eval vm_compute in (match affine_normal ne,core_runs we,compile_word (side_word re) with
      | Some nn,Some wc,Some xs => match scan_prefix [S0;S1] xs with
        | Some (_,xs) => match scan_core xs with
          | Some (_,xs) => match skip_symbols 256 6 xs with
            | Some xs => match scan_headers [5] xs with
              | Some ([z],xs) => match skip_symbols 256 2 xs with
                | Some xs => Some (affine_sub nn (affine_const 5),
                    affine_sub (last wc (affine_const 0)) (affine_const 4),
                    affine_sub z (affine_const 2),xs)
                | None => None end
              | _ => None end
            | None => None end
          | None => None end
        | None => None end
      | _,_,_ => None end) in
    lazymatch data with Some (?x,?y,?z,?xs) =>
      let x := unquote_affine x env in let y := unquote_affine y env in
      let z := unquote_affine z env in
      let r := unquote_segments xs env tail in
      refine (mixed_return_change _ (folded_front x y z r) _ (folded_returns x y z r));
      native_eq end))) end.
Ltac two_gap_case := lazymatch goal with |- mixed_return (tilted ?w ?n ?r) =>
  quote_nat n constr:(@nil nat) ltac:(fun ne env =>
  quote_core w env ltac:(fun we env =>
  quote_side r env ltac:(fun re env tail =>
    let data := eval vm_compute in (match affine_normal ne,core_runs we,compile_word (side_word re) with
      | Some nn,Some wc,Some xs => match affine_quotient nn 14 3,scan_prefix [S0;S1] xs with
        | Some x,Some (_,xs) => match affine_quotient (affine_sub (last wc (affine_const 0)) x) 14 2,scan_core xs with
          | Some y,Some (_,xs) => match scan_headers [7] xs with
            | Some (_,xs) => match skip_symbols 256 2 xs with
              | Some xs => Some (x,y,xs) | None => None end
            | None => None end
          | _,_ => None end
        | _,_ => None end
      | _,_,_ => None end) in
    lazymatch data with Some (?x,?y,?xs) =>
      let x := unquote_affine x env in let y := unquote_affine y env in
      let r := unquote_segments xs env tail in
      refine (mixed_return_change _ (two_gap_front x y r) _ (two_gap_returns x y r)); native_eq end))) end.
Tactic Notation "return_folded" constr(n) := advance_common n; folded_case.
Tactic Notation "return_two_gap" constr(n) := advance_common n; two_gap_case.

Lemma S22_returns a b c r : mixed_return (prefix_S22 a b c r).
Proof.
  unfold prefix_S22 at 1. begin_cases. split_parity a 3.
  - macros constr:(3). target_member constr:(2) constr:([b;c;a]) ltac:(eexists).
  - split_parity a 6.
    + return_H1 6.
    + split_parity b 7.
      * return_S22 7.
      * split_parity a 12.
        -- return_S22 12.
        -- return_S22 16.
Qed.

Lemma H1_returns a b r : mixed_return (prefix_H1 a b r).
Proof.
  unfold prefix_H1 at 1. begin_cases. split_parity b 3.
  - split_parity a 4.
    + split_parity b 11.
      * return_H1 11.
      * split_parity a 12.
        -- split_parity b 17.
           ++ return_S22 20.
           ++ return_S22 17.
        -- return_S22 12.
    + return_S22 4.
  - return_QH1 3 [b;a].
Qed.

Lemma H0_returns a b c r : mixed_return (prefix_H0 a b c r).
Proof.
  unfold prefix_H0 at 1. begin_cases. split_parity c 3.
  - split_parity a 4.
    + return_S22 4.
    + split_parity c 11.
      * split_parity a 12.
        -- split_parity c 17.
           ++ return_S22 20.
           ++ return_S22 17.
        -- return_S22 12.
      * return_H1 11.
  - return_QShield 3 [c;a;b].
Qed.

Lemma O5_returns a b c d r : mixed_return (counter_pair (24+a) (30+2*b)
  (pure_page (12+b) (pure_page (11+b) (pure_page (13+b)
    (pure_page (20+6*c) (pure_page (10+3*c+d) r)))))).
Proof.
  begin_cases. split_parity a 3.
  - split_parity b 3.
    + return_H1 3.
    + split_parity a 4.
      * return_S22 4.
      * split_parity b 9.
        -- return_S22 9.
        -- return_S22 12.
  - split_parity b 6.
    + split_parity a 6.
      * return_H1 6.
      * split_parity b 7.
        -- split_parity a 12.
           ++ return_S22 12.
           ++ return_S22 16.
        -- return_S22 7.
    + split_parity a 7.
      * return_H1 7.
      * return_S22 8.
Qed.

Lemma K5_returns a b c d r :
  mixed_return (K5front (24+a) (13+2*b) (3+c) (3+d) r).
Proof.
  unfold K5front. begin_cases. split_parity a 4.
  - split_parity a 4.
    + return_S22 4.
    + split_parity b 9.
      * split_parity c 9.
        -- return_S22 9.
        -- split_parity a 16.
           ++ split_parity b 16.
              ** return_H1 16.
              ** split_parity c 17.
                 { return_folded 22. }
                 { return_S22 17. }
           ++ split_parity b 16.
              ** split_parity c 17.
                 { return_folded 22. }
                 { return_S22 17. }
              ** return_H1 16.
      * split_parity c 13.
        -- return_two_gap 19.
        -- return_S22 13.
  - split_parity a 7.
    + return_H1 7.
    + split_parity b 8.
      * split_parity c 8.
        -- return_S22 8.
        -- split_parity a 13.
           ++ return_S22 13.
           ++ return_S22 16.
      * split_parity c 8.
        -- split_parity a 13.
           ++ return_S22 13.
           ++ return_S22 16.
        -- return_S22 8.
Qed.

Lemma KEmpty_returns a b c r :
  mixed_return (KEmptyFront (31+2*a+6*b+2*c) (3+a) (3+b) r).
Proof.
  unfold KEmptyFront. begin_cases. split_parity b 4.
  - split_parity a 9.
    + split_parity c 9.
      * split_parity c 19.
        -- return_S22 20.
        -- return_H1 19.
      * return_S22 9.
    + split_parity c 14.
      * split_parity a 16.
        -- split_parity c 16.
           ++ return_H1 16.
           ++ return_folded 22.
        -- split_parity c 16.
           ++ return_S22 17.
           ++ return_H1 16.
      * return_S22 14.
  - return_S22 4.
Qed.

Lemma BOddNonempty_returns a b c r :
  mixed_return (BOddNonemptyFront (13+2*c) (3+a) (3+b) r).
Proof.
  unfold BOddNonemptyFront. begin_cases. split_parity a 4.
  - split_parity b 4.
    + return_S22 4.
    + split_parity c 9.
      * return_S22 9.
      * split_parity b 17.
        -- split_parity c 17.
           ++ return_S22 17.
           ++ split_parity a 22.
              ** return_S22 22.
              ** return_S22 26.
        -- split_parity c 17.
           ++ split_parity a 22.
              ** split_zero c 26.
                 { return_S22 26. }
                 { return_S22 26. }
              ** return_S22 22.
           ++ return_S22 17.
  - split_parity b 4.
    + split_parity c 12.
      * split_parity a 16.
        -- split_parity b 16.
           ++ split_parity c 16.
              ** return_H1 16.
              ** return_folded 22.
           ++ split_parity c 16.
              ** return_folded 22.
              ** return_H1 16.
        -- split_parity b 16.
           ++ split_parity c 16.
              ** return_S22 17.
              ** return_H1 16.
           ++ split_parity c 16.
              ** return_H1 16.
              ** return_S22 17.
      * return_S22 12.
    + return_S22 4.
Qed.

Lemma BOddEmpty_returns a b c r :
  mixed_return (BOddEmptyFront (35+2*a+6*b+2*c) (3+a) (3+b) r).
Proof.
  unfold BOddEmptyFront. begin_cases. split_parity a 4.
  - split_parity b 4.
    + return_S22 4.
    + split_parity c 9.
      * return_S22 9.
      * split_parity a 17.
        -- split_parity c 17.
           ++ split_parity b 22.
              ** return_S22 22.
              ** return_S22 26.
           ++ return_S22 17.
        -- split_parity c 17.
           ++ return_S22 17.
           ++ split_parity b 22.
              ** return_S22 26.
              ** return_S22 22.
  - split_parity b 4.
    + split_parity c 12.
      * split_parity c 16.
        -- return_H1 16.
        -- split_parity a 17.
           ++ return_folded 22.
           ++ return_S22 17.
      * return_S22 12.
    + return_S22 4.
Qed.

Transparent counter_pair tilted carried W.

Inductive ReturnFamily : Q*tape -> Prop :=
| family_S a b d r : ReturnFamily (prefix_S22 a b d r)
| family_H0 a b c r : ReturnFamily (prefix_H0 a b c r)
| family_H1 a b r : ReturnFamily (prefix_H1 a b r)
| family_Q x y indices s v r :
    6<=x -> 13<=y -> 3<=s -> Forall (fun z => 5<=z) indices ->
    ReturnFamily (Qfront x y (exit_chain (x-1) indices s (v++[Three;Three]) r)).

Lemma strong_shield_form a b d r :
  prefix_S22 a b d r = shield (24+a) (22+4*b) (6+d) r.
Proof.
  unfold prefix_S22,shield,pure_page.
  replace ((22+4*b)/2-1) with (10+2*b); [reflexivity|].
  replace (22+4*b) with ((11+2*b)*2) by lia.
  rewrite Nat.div_mul by lia; lia.
Qed.

Lemma strong_shield_family a b d r :
  24<=a -> 22<=b -> b mod 4=2 -> 6<=d -> ReturnFamily (shield a b d r).
Proof.
  intros Ha Hb Hmod Hd.
  replace (shield a b d r) with (prefix_S22 (a-24) (b/4-5) (d-6) r).
  - constructor.
  - rewrite strong_shield_form; f_equal; lia.
Qed.

Lemma QShield_typed a b e r :
  prefix_QShield a b e r = Qfront (6+a) (13+3*b)
    (exit_chain (6+a-1) [] (3+b)
      (([Three]^^(5+b)++Six::[Three]^^e)++[Three;Three]) ([0;1;0;1;0] *> r)).
Proof. unfold Qfront,qright,exit_chain,exit_core. native_eq. Qed.

Lemma QH1_typed a b r :
  prefix_QH1 a b r = Qfront (6+a) (18+3*b)
    (exit_chain (6+a-1) [] (5+b)
      (([Three]^^(6+b)++Six::[Three]^^(5+2*b))++[Three;Three]) ([0;1;0;1;0] *> r)).
Proof. unfold Qfront,qright,exit_chain,exit_core. native_eq. Qed.

Lemma mixed_target_family c : mixed_prefix_target c -> ReturnFamily c.
Proof.
  intros [[a [b [d [r ->]]]] | [[a [b [r ->]]] |
    [[a [b [d [r ->]]]] | [[a [b [d [r ->]]]] | [a [b [r ->]]]]]]].
  - apply family_S.
  - apply family_H1.
  - apply family_H0.
  - rewrite QShield_typed. apply family_Q; try lia; constructor.
  - rewrite QH1_typed. apply family_Q; try lia; constructor.
Qed.

Lemma mixed_return_family c : mixed_return c -> exists d, c -->+ d /\ ReturnFamily d.
Proof.
  intros [d Hstep Htarget]. exists d. split; [exact Hstep|].
  apply mixed_target_family,Htarget.
Qed.

Lemma K5_return_family a c x h r :
  24<=a -> 13<=c -> c mod 2=1%nat -> 3<=x -> 3<=h ->
  exists d, K5front a c x h r -->+ d /\ ReturnFamily d.
Proof.
  intros Ha Hc Hodd Hx Hh.
  apply mixed_return_family. eapply mixed_return_change.
  2: exact (K5_returns (a-24) (c/2-6) (x-3) (h-3) r).
  unfold K5front. native_eq.
Qed.

Lemma O5_return_family a k x offset r :
  24<=a -> 12<=k -> 3<=x -> (offset=1%nat \/ offset=2) ->
  exists d, O5front a k x offset r -->+ d /\ ReturnFamily d.
Proof.
  intros Ha Hk Hx Hoffset. destruct Hoffset as [Hoffset|Hoffset]; subst offset;
    apply mixed_return_family.
  - eapply mixed_return_change.
    2: exact (O5_returns (a-24) (k-12) (x-3) 0 r).
    unfold O5front. native_eq.
  - eapply mixed_return_change.
    2: exact (O5_returns (a-24) (k-12) (x-3) 1 r).
    unfold O5front. native_eq.
Qed.

Lemma KEmpty_return_family x h s r : 3<=x -> 3<=h -> 3<=s -> s mod 2=1%nat ->
  exists d, KEmptyFront (2*x+6*h+s+4) x h r -->+ d /\ ReturnFamily d.
Proof.
  intros Hx Hh Hs Hodd.
  apply mixed_return_family. eapply mixed_return_change.
  2: exact (KEmpty_returns (x-3) (h-3) (s/2-1) r).
  unfold KEmptyFront. native_eq.
Qed.

Lemma BOddNonempty_return_family c x h r :
  13<=c -> c mod 2=1%nat -> 3<=x -> 3<=h ->
  exists d, BOddNonemptyFront c x h r -->+ d /\ ReturnFamily d.
Proof.
  intros Hc Hodd Hx Hh.
  apply mixed_return_family. eapply mixed_return_change.
  2: exact (BOddNonempty_returns (x-3) (h-3) (c/2-6) r).
  unfold BOddNonemptyFront. native_eq.
Qed.

Lemma BOddEmpty_return_family x h s r : 3<=x -> 3<=h -> 4<=s -> s mod 2=0%nat ->
  exists d, BOddEmptyFront (2*x+6*h+s+7) x h r -->+ d /\ ReturnFamily d.
Proof.
  intros Hx Hh Hs Heven.
  apply mixed_return_family. eapply mixed_return_change.
  2: exact (BOddEmpty_returns (x-3) (h-3) (s/2-2) r).
  unfold BOddEmptyFront. native_eq.
Qed.

Lemma indices_positive indices :
  Forall (fun z => 5<=z) indices -> Forall (fun z => 1<=z) indices.
Proof. induction 1; constructor; auto; lia. Qed.

Lemma q_page_as_front x b indices s v r :
  q_page_output (2*x) b indices s v r =
  q_pages_front (q_page_a (2*x) b indices s) x b indices s v r.
Proof.
  unfold q_page_output,q_pages_front.
  replace (6*(2*x)+4) with (12*x+4) by lia.
  replace (3*(2*x)+1) with (6*x+1) by lia. reflexivity.
Qed.

Lemma q_page_size x b indices s : 3<=x -> 6<=b -> 3<=s ->
  62<=q_page_a (2*x) b indices s.
Proof. unfold q_page_a; lia. Qed.

Lemma q_pages_zero_family a x b indices s v r :
  62<=a -> 3<=x -> 6<=b -> Forall (fun z => 1<=z) indices -> a mod 4=0%nat ->
  exists d, q_pages_front a x b indices s v r -->+ d /\ ReturnFamily d.
Proof.
  intros Ha Hx Hb Hindices Hmod.
  set (k:=a/4-1). assert (Hk : 5<=k) by (unfold k; lia).
  assert (Hform : a=4*k+4) by (unfold k; lia).
  destruct (even_frontier_frame_shield k x b indices s v r Hk ltac:(lia) ltac:(lia) Hindices)
    as [aa [rr [Haa Hreturn]]].
  exists (shield aa (4*k+6) (6*x+2) rr). split.
  - unfold q_pages_front. rewrite Hform. exact Hreturn.
  - apply strong_shield_family; lia.
Qed.

Lemma q_pages_odd_family a x b indices s v r :
  62<=a -> 3<=x -> 6<=b -> Forall (fun z => 1<=z) indices -> a mod 2=1%nat ->
  exists d, q_pages_front a x b indices s v r -->+ d /\ ReturnFamily d.
Proof.
  intros Ha Hx Hb Hindices Hmod.
  set (k:=a/2-1). assert (Hk : 11<=k) by (unfold k; lia).
  assert (Hform : a=2*k+3) by (unfold k; lia).
  destruct (q_pages_odd k x b indices s v r Hk Hx Hb Hindices)
    as [aa [offset [tail [Haa [Hoffset Hreturn]]]]].
  destruct (O5_return_family aa (k+1) x offset tail Haa ltac:(lia) Hx Hoffset)
    as [d [Hnext Hd]].
  exists d. split; [|exact Hd]. rewrite Hform. eapply progress_trans; eauto.
Qed.

Lemma q_pages_two_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  q_page_a (2*x) b indices s mod 4=2 ->
  exists d, q_pages_front (q_page_a (2*x) b indices s) x b indices s v r -->+ d /\ ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices Hmod. set (a:=q_page_a (2*x) b indices s) in *.
  assert (Ha : 62<=a) by (unfold a; apply q_page_size; assumption).
  assert (Hfull : a=4*x+6*b+chain_growth indices+2*s+8) by (unfold a,q_page_a; lia).
  set (k:=a/2-1). assert (Hform : a=2*k+2) by (unfold k; lia).
  assert (Hc : 13<=k+1) by lia.
  assert (Hodd : (k+1) mod 2=1%nat) by lia.
  remember (b/2) as h. assert (Hcases : b=2*h \/ b=2*h+1) by lia.
  destruct Hcases as [Hbf|Hbf]; subst b; assert (Hh : 3<=h) by lia;
    destruct indices as [|z indices].
  - cbn[chain_growth] in Hfull.
    assert (Hsodd : s mod 2=1%nat) by lia.
    assert (Hcounter : k+1=2*x+6*h+s+4) by lia.
    destruct (KEmpty_return_family x h s (frame_body s v r) Hx Hh Hs Hsodd) as [d [Hnext Hd]].
    exists d. split; [|exact Hd]. rewrite Hform. eapply progress_trans.
    + apply q_pages_even_empty; lia.
    + rewrite Hcounter. exact Hnext.
  - pose proof (Forall_inv Hindices) as Hz. change (5<=z) in Hz.
    pose proof (indices_positive _ (Forall_inv_tail Hindices)) as Htail.
    destruct (q_pages_even_nonempty k x h z indices s v r Hx Hh ltac:(lia) Htail)
      as [aa [tail [Haa Hreturn]]].
    destruct (K5_return_family aa (k+1) x h tail Haa Hc Hodd Hx Hh) as [d [Hnext Hd]].
    exists d. split; [|exact Hd]. rewrite Hform. eapply progress_trans; eauto.
  - cbn[chain_growth] in Hfull.
    assert (Hseven : s mod 2=0%nat) by lia. assert (Hs4 : 4<=s) by lia.
    assert (Hcounter : k+1=2*x+6*h+s+7) by lia.
    destruct (BOddEmpty_return_family x h s (frame_body s v r) Hx Hh Hs4 Hseven) as [d [Hnext Hd]].
    exists d. split; [|exact Hd]. rewrite Hform. eapply progress_trans.
    + apply q_pages_bodd_empty; lia.
    + rewrite Hcounter. exact Hnext.
  - destruct (BOddNonempty_return_family (k+1) x h (frame_pages z indices s v r)
      Hc Hodd Hx Hh) as [d [Hnext Hd]].
    exists d. split; [|exact Hd]. rewrite Hform. eapply progress_trans.
    + apply q_pages_bodd_nonempty; lia.
    + exact Hnext.
Qed.

Lemma q_pages_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, q_page_output (2*x) b indices s v r -->+ d /\ ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices. rewrite q_page_as_front.
  pose proof (q_page_size x b indices s Hx Hb Hs) as Ha.
  pose proof (indices_positive _ Hindices) as Hpositive.
  set (a:=q_page_a (2*x) b indices s) in *.
  destruct (Nat.eq_dec (a mod 4) 0) as [Hz|Hz].
  - apply q_pages_zero_family; assumption.
  - destruct (Nat.eq_dec (a mod 4) 2) as [Ht|Ht].
    + apply q_pages_two_family; assumption.
    + apply q_pages_odd_family; try assumption; lia.
Qed.

Lemma Q_even_exit_family x b indices s v r :
  3<=x -> 6<=b -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, Qfront (2*x) (2*b+1) (exit_chain (2*x-1) indices s (v++[Three;Three]) r) -->+ d /\
    ReturnFamily d.
Proof.
  intros Hx Hb Hs Hindices.
  destruct (q_pages_family x b indices s v r Hx Hb Hs Hindices) as [d [Hnext Hd]].
  exists d. split; [|exact Hd]. eapply progress_trans; [apply Q_page_return; lia|exact Hnext].
Qed.

Lemma Q_odd_exit_family a b indices s v r : 3<=a -> 6<=b -> 3<=s ->
  exists d, Qfront (2*a+1) (2*b+1) (exit_chain (2*a) indices s (v++[Three;Three]) r) -->+ d /\
    ReturnFamily d.
Proof.
  intros Ha Hb Hs.
  destruct (Q_odd_shield indices a b s (v++[Three;Three]) r ltac:(lia) ltac:(lia))
    as [aa [rr [Haa [Hd Hreturn]]]].
  exists (shield aa (12*a+10) (2*b+3) rr). split; [exact Hreturn|].
  apply strong_shield_family; lia.
Qed.

Lemma Q_family_return x y indices s v r :
  6<=x -> 13<=y -> 3<=s -> Forall (fun z => 5<=z) indices ->
  exists d, Qfront x y (exit_chain (x-1) indices s (v++[Three;Three]) r) -->+ d /\ ReturnFamily d.
Proof.
  intros Hx Hy Hs Hindices. destruct (mod2 y) as [b Hform|b Hform].
  - replace y with (2*b) by lia.
    exists (Qfront b (3*x) (exit_chain (b-1) ((x-1)::indices) s (v++[Three;Three]) r)).
    split.
    + rewrite <- qframe_exit_chain by lia. apply Q_push.
    + apply family_Q; try lia. constructor; [lia|exact Hindices].
  - replace y with (2*b+1) by lia. destruct (mod2 x) as [a Hfirst|a Hfirst].
    + replace x with (2*a) by lia. apply Q_even_exit_family; try lia; assumption.
    + replace x with (2*a+1) by lia.
      replace (2*a+1-1) with (2*a) by lia. apply Q_odd_exit_family; lia.
Qed.

Lemma return_family_closed c : ReturnFamily c -> exists d, c -->+ d /\ ReturnFamily d.
Proof.
  intro H. destruct H as [a b d r|a b c r|a b r|x y indices s v r Hx Hy Hs Hindices].
  - apply mixed_return_family,S22_returns.
  - apply mixed_return_family,H0_returns.
  - apply mixed_return_family,H1_returns.
  - apply Q_family_return; assumption.
Qed.

Lemma init : exists r, c0 -->* prefix_S22 35 12 8 r.
Proof.
  eexists. unfold prefix_S22,pure_page,counter_pair,page.
  eapply without_counter with (n:=N.to_nat 617635%N).
  eapply multistep_c_spec. vm_compute; reflexivity.
Qed.

(* Main result *)

Lemma nonhalt: ~halts tm c0.
Proof.
  destruct init as [r H].
  eapply multistep_nonhalt with (c':=prefix_S22 35 12 8 r); [exact H|].
  eapply progress_nonhalt with (P:=ReturnFamily).
  - intros c Hc. destruct (return_family_closed c Hc) as [d [Hd HF]].
    exists d. split; assumption.
  - constructor.
Qed.
Print Assumptions nonhalt.
End TM1.
