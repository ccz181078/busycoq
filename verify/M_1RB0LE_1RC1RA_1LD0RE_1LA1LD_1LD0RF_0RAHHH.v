(* 1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA--- halts. *)
From BusyCoq Require Import Individual62 Longitudinal ES_v2 Helper.
Require Import List NArith ZifyNat Lia String.
Import ListNotations.
Open Scope list_scope.
Open Scope sym_scope.

Definition tm : TM := Eval compute in (TM_from_str "1RB0LE_1RC1RA_1LD0RE_1LA1LD_1LD0RF_0RA---").

Module M244.

Definition src_tm : TM := Eval compute in (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA0LE_1RA0LF_0LB---").
Local Notation "c -->* c'" := (c -[ src_tm ]->* c') (at level 40).

Definition permState (q : Q) : Q :=
  match q with
  | A => D
  | B => A
  | C => B
  | D => C
  | E => E
  | F => F
  end.

Lemma perm_src : Perm (flip src_tm) tm permState.
Proof.
  split.
  - intros q s H. destruct q, s; inversion H; reflexivity.
  - intros q s s' d q' H. destruct q, s; inversion H; subst; reflexivity.
Qed.

Lemma halts_iso : halts src_tm (B;; tape0) -> halts tm c0.
Proof.
  intros H.
  apply flip_halts in H.
  change (flip_conf (B;; tape0)) with (B;; tape0) in H.
  exact (perm_halts _ _ _ _ _ perm_src H).
Qed.

Lemma halted_halts c : halted src_tm c -> halts src_tm c.
Proof.
  intros H. exists 0%nat, c. split; [constructor | exact H].
Qed.

Lemma ev_trans c1 c2 c3 : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof.
  induction 1; eauto.
Qed.

Lemma evstep_halts c c' : c -->* c' -> halts src_tm c' -> halts src_tm c.
Proof.
  induction 1 as [c | c c1 c2 H1 _ IH]; [auto |].
  intros H2. apply IH in H2. destruct H2 as [n [ch [Hm Hh]]].
  exists (S n), ch. split; [econstructor; eauto | exact Hh].
Qed.

(* ========================================================================== *)
(* Section 1: Words, Configurations, and 21 Macro Rules                       *)
(* ========================================================================== *)

Definition D_word (n : nat) : list Sym := [1] ++ [1; 1]^^n ++ [0; 0].
Definition S_word (n : nat) : list Sym := [1] ++ [0; 1]^^(1 + n).
Definition PL_word (n : nat) : list Sym :=
  [1; 0]^^(n + 4) ++ [1; 1]^^n ++ S_word 0 ++ S_word 0.

Definition CfgR (l r : side) := l {{A}}> [0; 1; 0; 0] *> r.
Definition CfgL (l r : side) := l <{{B}} [1] *> r.
Definition CfgJ (l r : side) := l <{{C}} [1; 0; 0] *> r.

Ltac norm_cb :=
  unfold CfgR, CfgL, CfgJ, D_word, S_word, PL_word;
  repeat (rewrite lpow_add || rewrite lpow_mul || rewrite Str_app_assoc);
  simpl_tape; simpl_rotate.
Tactic Notation "nsteps" int_or_var(k) := norm_cb; do k step; norm_cb.
Ltac ffollow H := norm_cb; follow H; norm_cb.
Ltac fsteps := norm_cb; repeat (try solve [finish]; try solve [simpl_rotate; finish]; step).

Lemma scanR l r n :
  l {{A}}> [0; 1] *> [1; 1]^^n *> r -->*
  l <* [1; 0]^^n {{A}}> [0; 1] *> r.
Proof.
  gen l. induction n; intros l; [finish|]. simpl_tape.
  do 6 step. follow IHn. simpl_rotate. finish.
Qed.

Lemma scanR1 l r n :
  l {{A}}> [0; 1; 1] *> [1; 1]^^n *> r -->*
  l <* [1; 0]^^n {{A}}> [0; 1; 1] *> r.
Proof. cbn. rewrite lpow_shift21e. exact (scanR l (1 >> r) n). Qed.

Lemma scanB l r n :
  l <* [0; 1]^^n <{{B}} r -->* l <{{B}} [1; 1]^^n *> r.
Proof. shift_rule; steps. Qed.

Lemma scanB0 r n :
  (0 >> [1; 0]^^n *> 0inf) <{{B}} r -->* 0inf <{{B}} [1; 1]^^n *> r.
Proof.
  gen r. induction n; intros r; [finish|]. simpl_tape.
  do 2 step. follow IHn. simpl_rotate. finish.
Qed.

Ltac fscanB := norm_cb; (follow scanB || follow scanB0); norm_cb.

Lemma scanC l r n :
  l <* [1; 0]^^n <{{C}} r -->* l <{{C}} [1; 1]^^n *> r.
Proof. shift_rule; steps. Qed.

Lemma scanPair l r n :
  l {{A}}> [0; 1] *> [0; 1; 0; 1]^^n *> r -->*
  l <* [1; 1; 0; 1]^^n {{A}}> [0; 1] *> r.
Proof.
  gen l. induction n; intros l; [finish|]. simpl_tape.
  do 4 step. follow IHn. simpl_rotate. finish.
Qed.

Lemma ones l r n : l {{A}}> [1]^^n *> r -->* l <* [1]^^n {{A}}> r.
Proof. shift_rule; steps. Qed.

Lemma ones2 l r n : l {{A}}> [1; 1]^^n *> r -->* l <* [1; 1]^^n {{A}}> r.
Proof. shift_rule; steps. Qed.

Lemma ones2_1 l r n : l {{A}}> 1 >> [1; 1]^^n *> r -->* l <* [1; 1]^^n {{A}}> 1 >> r.
Proof.
  gen l. induction n; intros l; [finish|]. simpl_tape.
  do 2 step. follow IHn. simpl_rotate. finish.
Qed.

Ltac fones2 := norm_cb; (follow ones2_1 || follow ones2); norm_cb.

Lemma rule_right l r n : CfgR l (D_word n *> r) -->* CfgR (l <* S_word n) r.
Proof. nsteps 3; ffollow scanR; finish. Qed.

Lemma rule_left l r n : CfgL (l <* S_word n) r -->* CfgL l (D_word n *> r).
Proof. nsteps 5; fscanB; finish. Qed.

Lemma rule_blank l r : CfgR l ([0; 0; 0] *> r) -->* CfgL l (D_word 0 *> D_word 0 *> r).
Proof. norm_cb; steps. Qed.

Lemma rule_even l r n : CfgR l ([1; 1]^^(1 + n) *> [0; 0] *> r) -->*
  CfgL l (D_word (1 + n) *> [1; 0] *> r).
Proof. nsteps 3; ffollow scanR1; nsteps 16; fscanB; finish. Qed.

Lemma rule_restart l r b : CfgL (l <* [1; 1; 1] <* [1; 0]^^(1 + b)) r -->*
  CfgR (l <* [1; 0]^^(1 + b)) r.
Proof.
  replace (l <* [1; 1; 1] <* [1; 0]^^(1 + b)) with (l <* [1; 1] <* S_word b)
    by (unfold S_word; simpl_rotate; reflexivity).
  follow rule_left. nsteps 5; ffollow scanR; finish.
Qed.

Lemma rule_overflow2 r b : CfgL (0inf <* [1; 1] <* [1; 0]^^(1 + b)) r -->*
  CfgR (0inf <* [1; 1]^^(1 + b) <* [1; 0]^^2) ([1] *> r).
Proof.
  nsteps 5; fscanB; nsteps 16; ffollow scanR1;
  nsteps 16; fscanB; nsteps 9; fones2; fsteps.
Qed.

Lemma rule_overflow1 r b n : CfgL (0inf <* [1] <* [1; 0]^^(1 + b)) (D_word n *> r) -->*
  CfgR (0inf <* [1; 1]^^b <* [1; 0]^^(n + 2)) ([1; 0] *> r).
Proof.
  nsteps 5; fscanB; nsteps 7; fones2;
  nsteps 8; ffollow scanR1; nsteps 16; fscanB;
  nsteps 11; ffollow scanR; finish.
Qed.

Lemma rule_collision l r : CfgL (l <* [0; 0; 1; 1; 0; 1]) r -->* CfgJ l ([1; 1; 1; 1] *> r).
Proof. norm_cb; steps. Qed.

Lemma rule_leftJ l r n : CfgJ (l <* S_word n) r -->* CfgL l (D_word (1 + n) *> r).
Proof. nsteps 3; fscanB; finish. Qed.

Lemma rule_turnB l r n : CfgL (l <* [1; 1]) (D_word n *> r) -->*
  CfgR (l <* [1; 0]^^(1 + n)) r.
Proof. nsteps 5; ffollow scanR; finish. Qed.

Lemma rule_turnJ l r b : CfgJ (l <* [1; 1; 1] <* [1; 0]^^b) r -->*
  CfgR (l <* [1; 0]^^(1 + b)) r.
Proof. nsteps 1; fscanB; nsteps 5; ffollow scanR; finish. Qed.

Lemma rule_finishP l r b : CfgL (l <* S_word 0 <* [0; 1] <* [1; 0]^^(1 + b)) r -->*
  CfgJ l (D_word (1 + b) *> r).
Proof. nsteps 4; ffollow scanC; fsteps. Qed.

Lemma rule_defect0 l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgJ l ([1; 1; 1; 1] *> D_word m *> [1] *> r).
Proof. nsteps 15; ffollow scanR1; nsteps 15; ffollow scanC; fsteps. Qed.

Lemma rule_defect1 l r m : CfgR l ([1; 0] *> D_word 1 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgL l (D_word 0 *> D_word 0 *> D_word (1 + m) *> [1] *> r).
Proof. nsteps 17; ffollow scanR1; nsteps 16; fscanB; fsteps. Qed.

Lemma rule_defect2 l r n m : CfgR l ([1; 0] *> D_word (2 + n) *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgR (l <* S_word 0 <* S_word 0 <* [1; 1]^^n <* [1; 0]^^(2 + m)) ([1] *> r).
Proof.
  nsteps 11; fones2; nsteps 8; ffollow scanR1;
  nsteps 16; fscanB; nsteps 11; ffollow scanR; finish.
Qed.

Lemma rule_defect_blank0 l r : CfgR l ([1; 0] *> D_word 0 *> [0; 0] *> r) -->*
  CfgR (l <* S_word 0 <* [1; 0; 0; 1]) r.
Proof. norm_cb; steps. Qed.

Lemma rule_defect_blankS l r n : CfgR l ([1; 0] *> D_word (1 + n) *> [0; 0] *> r) -->*
  CfgR (l <* S_word 0 <* S_word 0 <* [1] <* [1; 1]^^n <* [1; 0]) r.
Proof. nsteps 9; fones2; fsteps. Qed.

Lemma rule_paired l r k n : CfgR l ([1; 0]^^(k * 2) *> D_word n *> r) -->*
  CfgR (l <* S_word 0 <* [1; 1; 0; 1]^^k <* [1; 0]^^n) r.
Proof. nsteps 3; ffollow scanPair; ffollow scanR; finish. Qed.

Lemma rule_emptyR l : CfgR l 0inf -->* CfgL l (D_word 0 *> D_word 0 *> 0inf).
Proof. norm_cb; steps. Qed.

Lemma rule_collide l r : CfgR l ([1; 0] *> D_word 0 *> D_word 0 *> r) -->*
  CfgJ l (D_word 2 *> [1; 0] *> r).
Proof. norm_cb; steps. Qed.

Lemma rule_pairR l r n : CfgR l ([1; 0] *> D_word (2 + n) *> D_word (2 + n) *> r) -->*
  CfgR (l <* PL_word n) ([1; 0] *> r).
Proof.
  nsteps 11; fones2; nsteps 20; ffollow scanR1;
  nsteps 20; fscanB; nsteps 23; ffollow scanR; finish.
Qed.


(* Section 2: Higher-Order CB1 Lemmas & Wrapper Rules                         *)
(* ========================================================================== *)

Lemma nil_lpow n : (@nil Sym)^^n = [].
Proof. induction n; cbn; congruence. Qed.

Lemma lpow_1 (w : list Sym) : w^^1 = w.
Proof. cbn. apply app_nil_r. Qed.

Lemma lpow_Str_app_comm (w : list Sym) k r :
  w^^k *> (w *> r) = w *> (w^^k *> r).
Proof.
  rewrite <- !Str_app_assoc, lpow_shift. reflexivity.
Qed.

Lemma lpow_plus_r (w : list Sym) k :
  w^^(k + 1) = w^^k ++ w.
Proof.
  rewrite lpow_add, lpow_1. reflexivity.
Qed.

Lemma lpow_Str_add (w : list Sym) a b r :
  w^^a *> w^^b *> r = w^^(a + b) *> r.
Proof.
  rewrite <- Str_app_assoc, <- lpow_add. reflexivity.
Qed.

Lemma one_pow_two_mul k : [1]^^(2 * k) = [1; 1]^^k.
Proof.
  replace (2 * k)%nat with (k * 2)%nat by lia.
  rewrite lpow_mul. reflexivity.
Qed.

Lemma D_word_ones n r : D_word n *> r = [1]^^(2 * n + 1) *> [0; 0] *> r.
Proof.
  unfold D_word.
  replace (2 * n + 1)%nat with (1 + 2 * n)%nat by lia.
  rewrite lpow_add, one_pow_two_mul, ?Str_app_assoc.
  reflexivity.
Qed.

Lemma one_D_word n r : [1] *> D_word n *> r = [1; 1]^^(1 + n) *> [0; 0] *> r.
Proof.
  unfold D_word. cbn [Nat.add lpow app Str_app]. rewrite ?Str_app_assoc. reflexivity.
Qed.

Lemma S_word_ones n r : S_word n *> r = [1]^^1 *> [0; 1]^^(1 + n) *> r.
Proof.
  unfold S_word. cbn [lpow app Str_app]. reflexivity.
Qed.

Lemma one_pow_three_mul k : [1]^^(3 * k) = [1; 1; 1]^^k.
Proof.
  replace (3 * k)%nat with (k * 3)%nat by lia.
  rewrite lpow_mul. reflexivity.
Qed.

Lemma zero_one_pow_two_mul k : [0; 1]^^(2 * k) = [0; 1; 0; 1]^^k.
Proof.
  replace (2 * k)%nat with (k * 2)%nat by lia.
  rewrite lpow_mul. reflexivity.
Qed.

Lemma N_div_mod_nat (c d : N) : d <> 0%N ->
  (N.to_nat c = N.to_nat d * N.to_nat (c / d) + N.to_nat (c mod d))%nat /\
  (N.to_nat (c mod d) < N.to_nat d)%nat.
Proof.
  intros Hd.
  pose proof (N.div_mod c d Hd) as H1.
  pose proof (N.mod_lt c d Hd) as H2.
  lia.
Qed.

Lemma rule_right_pow l r n k :
  CfgR l ((D_word n)^^k *> r) -->* CfgR ((S_word n)^^k *> l) r.
Proof.
  gen l. induction k as [|k IH]; intros l; cbn [lpow Str_app]; [apply evstep_refl |].
  rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply IH |].
  rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma rule_left_pow l r n k :
  CfgL ((S_word n)^^k *> l) r -->* CfgL l ((D_word n)^^k *> r).
Proof.
  gen r. induction k as [|k IH]; intros r; cbn [lpow Str_app]; [apply evstep_refl |].
  rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_left |].
  eapply ev_trans; [apply IH |].
  rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Definition call (r s : side) : Prop := forall l, CfgR l r -->* CfgL l s.

Inductive calls : nat -> side -> side -> Prop :=
| calls_O r : calls 0 r r
| calls_S n r s t : call r s -> calls n s t -> calls (S n) r t.

Lemma call_D_pow n k {r s} (H : call r s) :
  call ((D_word n)^^k *> r) ((D_word n)^^k *> s).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right_pow |].
  eapply ev_trans; [apply H |].
  apply rule_left_pow.
Qed.

Lemma calls_D_pow n m {k r s} (H : calls k r s) :
  calls k ((D_word n)^^m *> r) ((D_word n)^^m *> s).
Proof.
  induction H as [r | k r s t H1 _ IH]; [constructor |].
  econstructor; [apply call_D_pow, H1 | exact IH].
Qed.

Lemma call_blank0 : call 0inf ((D_word 0)^^2 *> 0inf).
Proof.
  intros l. cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc. apply rule_emptyR.
Qed.

Lemma calls_blank k : calls k 0inf ((D_word 0)^^(k * 2) *> 0inf).
Proof.
  induction k as [|k IH]; cbn [Nat.mul]; [constructor |].
  replace (S k * 2)%nat with (2 + k * 2)%nat by lia.
  rewrite lpow_add, Str_app_assoc.
  eapply calls_S; [apply call_blank0 |].
  exact (calls_D_pow 0 2 IH).
Qed.

Lemma call_collision0 j r :
  call (D_word j *> [1; 0] *> D_word 0 *> D_word 0 *> r)
       (D_word (1 + j) *> D_word 2 *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_collide |].
  apply rule_leftJ.
Qed.

Lemma calls_collision k j r :
  calls (1 + k)
    (D_word j *> [1; 0] *> (D_word 0)^^((1 + k) * 2) *> r)
    (D_word (1 + j) *> (D_word 3)^^k *> D_word 2 *> [1; 0] *> r).
Proof.
  gen j. induction k as [|k IH]; intros j.
  - change ((1 + 0) * 2)%nat with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
    eapply calls_S; [apply call_collision0 | constructor].
  - replace ((1 + S k) * 2)%nat with (2 + (1 + k) * 2)%nat by lia.
    rewrite lpow_add, !Str_app_assoc.
    replace ((D_word 0)^^2) with (D_word 0 ++ D_word 0)
      by (cbn [lpow]; rewrite ?app_nil_r; reflexivity).
    rewrite ?Str_app_assoc.
    eapply calls_S; [apply call_collision0 |].
    pose proof (calls_D_pow (1 + j) 1 (IH 2%nat)) as H.
    cbn [lpow] in H. rewrite ?app_nil_r in H.
    change (D_word (1 + 2)) with (D_word 3) in H.
    cbn [lpow]. rewrite Str_app_assoc. exact H.
Qed.

Lemma pairsR k n l r :
  CfgR l ([1; 0] *> (D_word (2 + n))^^(k * 2) *> r) -->*
  CfgR ((PL_word n)^^k *> l) ([1; 0] *> r).
Proof.
  gen l. induction k as [|k IH]; intros l; [apply evstep_refl |].
  replace (S k * 2)%nat with (2 + k * 2)%nat by lia.
  rewrite lpow_add, Str_app_assoc.
  replace ((D_word (2 + n))^^2) with (D_word (2 + n) ++ D_word (2 + n))
    by (cbn [lpow]; rewrite ?app_nil_r; reflexivity).
  rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_pairR |].
  eapply ev_trans; [apply IH |].
  rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma loopL {k r s} (H : calls k r s) l b :
  CfgL ([1; 0]^^(1 + b) *> [1; 1; 1]^^k *> l) r -->*
  CfgL ([1; 0]^^(1 + b) *> l) s.
Proof.
  gen l. induction H as [r | k r u t Hc _ IH]; intros l; [apply evstep_refl |].
  cbn [lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_restart |].
  eapply ev_trans; [apply Hc |].
  apply IH.
Qed.

Lemma loopR {k r s} (H : calls k r s) l b :
  CfgR ([1; 0]^^(1 + b) *> [1; 1; 1]^^k *> l) r -->*
  CfgR ([1; 0]^^(1 + b) *> l) s.
Proof.
  gen l. induction H as [r | k r u t Hc _ IH]; intros l; [apply evstep_refl |].
  cbn [lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply Hc |].
  eapply ev_trans; [apply rule_restart |].
  apply IH.
Qed.

Lemma pl_inner_eq n :
  [1; 1]^^(1 + n * 3) ++ S_word 0 = [1; 1; 1]^^(1 + n * 2) ++ [0; 1].
Proof.
  induction n as [|n IH]; [reflexivity |].
  replace (1 + S n * 3)%nat with (3 + (1 + n * 3))%nat by lia.
  replace (1 + S n * 2)%nat with (2 + (1 + n * 2))%nat by lia.
  rewrite (lpow_add _ 3 (1 + n * 3) [1; 1]), (lpow_add _ 2 (1 + n * 2) [1; 1; 1]).
  rewrite <- app_assoc, IH, app_assoc. reflexivity.
Qed.

Lemma pl_decomp n l :
  PL_word (1 + n * 3) *> l =
    [1; 0]^^(5 + n * 3) *> [1; 1; 1]^^(1 + n * 2) *> [0; 1] *> S_word 0 *> l.
Proof.
  unfold PL_word.
  replace (1 + n * 3 + 4)%nat with (5 + n * 3)%nat by lia.
  rewrite ?Str_app_assoc. f_equal.
  rewrite <- Str_app_assoc, pl_inner_eq, Str_app_assoc. reflexivity.
Qed.

Lemma returnP_L {n r s} (H : calls (1 + n * 2) r s) l :
  CfgL (PL_word (1 + n * 3) *> l) r -->* CfgJ l (D_word (5 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  change (5 + n * 3)%nat with (1 + (4 + n * 3))%nat.
  eapply ev_trans; [apply (loopL H) |].
  apply rule_finishP.
Qed.

Lemma loopJ {k r s} (H : calls (1 + k) r s) l b :
  CfgJ ([1; 0]^^b *> [1; 1; 1]^^(1 + k) *> l) r -->*
  CfgL ([1; 0]^^(1 + b) *> l) s.
Proof.
  inversion H as [|m r0 u t Hc Htail]; subst.
  cbn [Nat.add lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_turnJ |].
  eapply ev_trans; [apply Hc |].
  apply (loopL Htail).
Qed.

Lemma returnP_J {n r s} (H : calls (1 + n * 2) r s) l :
  CfgJ (PL_word (1 + n * 3) *> l) r -->* CfgJ l (D_word (6 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  eapply ev_trans; [apply (loopJ H _ (5 + n * 3)) |].
  change (1 + (5 + n * 3))%nat with (6 + n * 3)%nat.
  apply rule_finishP.
Qed.

Lemma calls_split a b {r s} (H : calls (a + b) r s) :
  exists t, calls a r t /\ calls b t s.
Proof.
  gen r. induction a as [|a IH]; intros r H; cbn [Nat.add] in H.
  - exists r. split; [constructor | exact H].
  - inversion H as [|m r0 u s0 Hc Htail]; subst.
    destruct (IH _ Htail) as [t [Ht1 Ht2]].
    exists t. split; [econstructor; eauto | exact Ht2].
Qed.

Lemma returnsP_J k n {r s} (H : calls (k * (1 + n * 2)) r s) l :
  CfgJ ((PL_word (1 + n * 3))^^k *> l) r -->* CfgJ l ((D_word (6 + n * 3))^^k *> s).
Proof.
  gen r s l. induction k as [|k IH]; intros r s H l; cbn [Nat.mul] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
    cbn [lpow]. rewrite Str_app_assoc.
    eapply ev_trans; [apply (returnP_J Hu) |].
    pose proof (calls_D_pow (6 + n * 3) 1 Hv) as Hv'.
    cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
    eapply ev_trans; [apply (IH _ _ Hv') |].
    rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma returnsP_L k n {r s} (H : calls ((1 + k) * (1 + n * 2)) r s) l :
  CfgL ((PL_word (1 + n * 3))^^(1 + k) *> l) r -->*
  CfgJ l ((D_word (6 + n * 3))^^k *> D_word (5 + n * 3) *> s).
Proof.
  cbn [Nat.add Nat.mul] in H.
  destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
  cbn [Nat.add lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply (returnP_L Hu) |].
  pose proof (calls_D_pow (5 + n * 3) 1 Hv) as Hv'.
  cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
  exact (returnsP_J k n Hv' l).
Qed.

Lemma rule_collisionD l r n :
  CfgL ([0; 0; 1; 1; 0; 1] *> l) (D_word n *> r) -->*
  CfgJ l (D_word (2 + n) *> r).
Proof.
  replace (D_word (2 + n) *> r) with ([1; 1; 1; 1] *> D_word n *> r)
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; reflexivity).
  apply rule_collision.
Qed.

Lemma rule_defect0D l r m :
  CfgR l ([1; 0] *> D_word 0 *> D_word m *> r) -->*
  CfgJ l (D_word (2 + m) *> [1; 0] *> r).
Proof.
  replace (D_word m *> r) with ([1] *> [1; 1]^^m *> [0] *> ([0] *> r))
    by (unfold D_word; rewrite ?Str_app_assoc; reflexivity).
  replace (D_word (2 + m) *> [1; 0] *> r)
    with ([1; 1; 1; 1] *> D_word m *> [1] *> ([0] *> r))
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; rewrite ?Str_app_assoc; reflexivity).
  apply rule_defect0.
Qed.

Lemma rule_defect1D l r m :
  CfgR l ([1; 0] *> D_word 1 *> D_word m *> r) -->*
  CfgL l (D_word 0 *> D_word 0 *> D_word (1 + m) *> [1; 0] *> r).
Proof.
  replace (D_word m *> r) with ([1] *> [1; 1]^^m *> [0] *> ([0] *> r))
    by (unfold D_word; rewrite ?Str_app_assoc; reflexivity).
  change ([1; 0] *> r) with ([1] *> ([0] *> r)).
  apply rule_defect1.
Qed.

Lemma rule_defect2D l r n m :
  CfgR l ([1; 0] *> D_word (2 + n) *> D_word m *> r) -->*
  CfgR ([1; 0]^^(2 + m) *> [1; 1]^^n *> S_word 0 *> S_word 0 *> l) ([1; 0] *> r).
Proof.
  replace (D_word m *> r) with ([1] *> [1; 1]^^m *> [0] *> ([0] *> r))
    by (unfold D_word; rewrite ?Str_app_assoc; reflexivity).
  change ([1; 0] *> r) with ([1] *> ([0] *> r)).
  apply rule_defect2.
Qed.

Lemma call_defect0 j m r :
  call (D_word j *> [1; 0] *> D_word 0 *> D_word m *> r)
       (D_word (1 + j) *> D_word (2 + m) *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_defect0D |].
  apply rule_leftJ.
Qed.

Lemma call_defect1 m r :
  call ([1; 0] *> D_word 1 *> D_word m *> r)
       (D_word 0 *> D_word 0 *> D_word (1 + m) *> [1; 0] *> r).
Proof.
  intros l. apply rule_defect1D.
Qed.

Lemma loopR_to_L {k r t} (H : calls (k + 1) r t) l b :
  CfgR ([1; 0]^^(1 + b) *> [1; 1; 1]^^k *> l) r -->*
  CfgL ([1; 0]^^(1 + b) *> l) t.
Proof.
  destruct (calls_split k 1 H) as [s [Hs1 Hs2]].
  inversion Hs2 as [|m s0 u t0 Hc Hz]; subst.
  inversion Hz; subst.
  eapply ev_trans; [apply (loopR Hs1) |].
  apply Hc.
Qed.

Lemma loopR_to_L' {h r t} (Hh : (0 < h)%nat) (Hc : calls h r t) l b :
  CfgR ([1; 0]^^(1 + b) *> [1; 1; 1]^^(h - 1) *> l) r -->*
  CfgL ([1; 0]^^(1 + b) *> l) t.
Proof.
  replace h with ((h - 1) + 1)%nat in Hc by lia.
  exact (loopR_to_L Hc l b).
Qed.

Lemma loopJ' {h r s} (Hh : (0 < h)%nat) (Hc : calls h r s) l b :
  CfgJ ([1; 0]^^b *> [1; 1; 1]^^h *> l) r -->*
  CfgL ([1; 0]^^(1 + b) *> l) s.
Proof.
  replace h with (1 + (h - 1))%nat in Hc |- * by lia.
  exact (loopJ Hc l b).
Qed.

(* ========================================================================== *)
(* Section 3: SymWord, Runs, Digits, RTape & Soundness                        *)
(* ========================================================================== *)

Lemma sym_eqb_eq a b : sym_eqb a b = true -> a = b.
Proof. destruct (sym_eqb_spec a b); congruence. Qed.

Fixpoint beqListSym (xs ys : list Sym) : bool :=
  match xs, ys with
  | [], [] => true
  | a :: xs', b :: ys' => if sym_eqb a b then beqListSym xs' ys' else false
  | _, _ => false
  end.

Lemma beqListSym_eq xs ys : beqListSym xs ys = true -> xs = ys.
Proof.
  gen ys. induction xs as [|a xs IH]; destruct ys as [|b ys]; cbn; try discriminate.
  - reflexivity.
  - destruct (sym_eqb_spec a b); [subst; intros H; f_equal; exact (IH _ H) | discriminate].
Qed.

Inductive SymWord :=
| SW_raw (w : list Sym)
| SW_D (n : N)
| SW_S (n : N)
| SW_PL (n : N).

Definition sw_toList (w : SymWord) : list Sym :=
  match w with
  | SW_raw lw => lw
  | SW_D n => D_word (N.to_nat n)
  | SW_S n => S_word (N.to_nat n)
  | SW_PL n => PL_word (N.to_nat n)
  end.

Definition sw_isEmpty (w : SymWord) : bool :=
  match w with
  | SW_raw [] => true
  | _ => false
  end.

Lemma sw_isEmpty_spec w : sw_isEmpty w = true -> sw_toList w = [].
Proof. destruct w as [[|] | | |]; cbn; congruence. Qed.

Definition sw_beq (w v : SymWord) : bool :=
  match w, v with
  | SW_raw lw, SW_raw lv => beqListSym lw lv
  | SW_D n, SW_D m => N.eqb n m
  | SW_S n, SW_S m => N.eqb n m
  | SW_PL n, SW_PL m => N.eqb n m
  | _, _ => false
  end.

Lemma sw_beq_eq w v : sw_beq w v = true -> sw_toList w = sw_toList v.
Proof.
  destruct w, v; cbn; try discriminate.
  - apply beqListSym_eq.
  - intros H; apply N.eqb_eq in H; subst; reflexivity.
  - intros H; apply N.eqb_eq in H; subst; reflexivity.
  - intros H; apply N.eqb_eq in H; subst; reflexivity.
Qed.

Definition Runs := list (SymWord * N).

Fixpoint runs_denote (xs : Runs) : side :=
  match xs with
  | [] => 0inf
  | (w, n) :: xs' => (sw_toList w)^^(N.to_nat n) *> runs_denote xs'
  end.

Fixpoint plug (xs : Runs) (t : side) : side :=
  match xs with
  | [] => t
  | (w, n) :: xs' => (sw_toList w)^^(N.to_nat n) *> plug xs' t
  end.

Lemma denote_eq_plug_0inf xs : runs_denote xs = plug xs 0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn; congruence.
Qed.

Definition runs_push (w : SymWord) (n : N) (xs : Runs) : Runs :=
  if sw_isEmpty w then xs
  else if N.eqb n 0 then xs
  else
    match xs with
    | (v, m) :: ys =>
      if sw_beq w v then (w, (n + m)%N) :: ys
      else (w, n) :: xs
    | [] => [(w, n)]
    end.

Lemma push_plug w n xs t :
  plug (runs_push w n xs) t = (sw_toList w)^^(N.to_nat n) *> plug xs t.
Proof.
  unfold runs_push.
  destruct (sw_isEmpty w) eqn:He.
  - rewrite (sw_isEmpty_spec w He), nil_lpow. reflexivity.
  - destruct (N.eqb_spec n 0) as [-> | _]; [reflexivity |].
    destruct xs as [|[v m] ys]; [reflexivity |].
    destruct (sw_beq w v) eqn:Hb; [| reflexivity].
    cbn [plug]. rewrite <- (sw_beq_eq w v Hb), N2Nat.inj_add, lpow_add, Str_app_assoc.
    reflexivity.
Qed.

Lemma runs_push_spec w n xs :
  runs_denote (runs_push w n xs) = (sw_toList w)^^(N.to_nat n) *> runs_denote xs.
Proof.
  rewrite !denote_eq_plug_0inf. apply push_plug.
Qed.

Fixpoint put (xs ys : Runs) : Runs :=
  match xs with
  | [] => ys
  | (w, n) :: xs' => runs_push w n (put xs' ys)
  end.

Lemma put_plug xs ys t : plug (put xs ys) t = plug xs (plug ys t).
Proof.
  induction xs as [|[w n] xs IH]; cbn; [reflexivity |].
  rewrite push_plug, IH. reflexivity.
Qed.

Lemma put_spec xs ys : runs_denote (put xs ys) = plug xs (runs_denote ys).
Proof.
  rewrite !denote_eq_plug_0inf. apply put_plug.
Qed.

Fixpoint runs_pop (xs : Runs) : Sym * Runs :=
  match xs with
  | [] => (0, [])
  | (_, N0) :: xs' => runs_pop xs'
  | (SW_raw [], Npos _) :: xs' => runs_pop xs'
  | (SW_raw (b :: rest), Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    (b, runs_push (SW_raw rest) 1 (runs_push (SW_raw (b :: rest)) n xs'))
  | (SW_D k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 (runs_push (SW_D k) n xs')))
  | (SW_S k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    (1, runs_push (SW_raw [0; 1]) (1 + k)%N (runs_push (SW_S k) n xs'))
  | (SW_PL k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    (1, runs_push (SW_raw [0]) 1 (runs_push (SW_raw [1; 0]) (k + 3)%N
          (runs_push (SW_raw [1; 1]) k (runs_push (SW_S 0) 2 (runs_push (SW_PL k) n xs')))))
  end.

Lemma pos_to_nat_succ p : N.to_nat (Npos p) = S (N.to_nat (N.pred (Npos p))).
Proof. lia. Qed.

Lemma runs_pop_spec xs :
  runs_denote xs = fst (runs_pop xs) >> runs_denote (snd (runs_pop xs)).
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_pop runs_denote].
  - apply const_unfold.
  - destruct w as [[|] | | |]; exact IH.
  - destruct w as [[|b rest] | k | k | k]; cbn [runs_pop fst snd].
    + cbn [sw_toList]. rewrite nil_lpow. exact IH.
    + rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      unfold D_word. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + rewrite !runs_push_spec, pos_to_nat_succ, N2Nat.inj_add.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      unfold S_word. rewrite ?Str_app_assoc. reflexivity.
    + rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      cbn [sw_toList lpow app Str_app].
      unfold PL_word.
      replace (N.to_nat k + 4)%nat with (S (N.to_nat (k + 3)%N)) by lia.
      cbn [lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
Qed.

Fixpoint runs_remove (w : list Sym) (xs : Runs) : option Runs :=
  match w with
  | [] => Some xs
  | b :: w' =>
    let '(c, ys) := runs_pop xs in
    if sym_eqb b c then runs_remove w' ys else None
  end.

Lemma runs_remove_spec w xs ys :
  runs_remove w xs = Some ys -> runs_denote xs = w *> runs_denote ys.
Proof.
  gen xs. induction w as [|b w IH]; intros xs H; cbn [runs_remove] in H.
  - inversion H; reflexivity.
  - pose proof (runs_pop_spec xs) as Hp.
    destruct (runs_pop xs) as [c zs]; cbn in Hp.
    destruct (sym_eqb_spec b c); [subst | discriminate].
    rewrite Hp, (IH _ H). reflexivity.
Qed.

Fixpoint all_zero_word (w : list Sym) : bool :=
  match w with
  | [] => true
  | b :: w' => if sym_eqb b 0 then all_zero_word w' else false
  end.

Lemma all_zero_word_spec w : all_zero_word w = true -> w *> 0inf = 0inf.
Proof.
  induction w as [|b w IH]; cbn; [reflexivity |].
  destruct (sym_eqb_spec b 0); [subst | discriminate].
  intros H. rewrite (IH H). symmetry. apply const_unfold.
Qed.

Definition sw_all_zero (w : SymWord) : bool :=
  match w with
  | SW_raw lw => all_zero_word lw
  | _ => false
  end.

Lemma sw_all_zero_pow w n :
  sw_all_zero w = true -> (sw_toList w)^^n *> 0inf = 0inf.
Proof.
  destruct w as [lw | | |]; cbn; try discriminate.
  intros H. induction n as [|n IH]; cbn [lpow Str_app]; [reflexivity |].
  rewrite Str_app_assoc, IH. exact (all_zero_word_spec lw H).
Qed.

Fixpoint runs_zeros (xs : Runs) : bool :=
  match xs with
  | [] => true
  | (w, _) :: xs' => if sw_all_zero w then runs_zeros xs' else false
  end.

Lemma runs_zeros_spec xs : runs_zeros xs = true -> runs_denote xs = 0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn; [reflexivity |].
  destruct (sw_all_zero w) eqn:Hw; [| discriminate].
  intros H. rewrite (IH H). exact (sw_all_zero_pow w (N.to_nat n) Hw).
Qed.

Fixpoint runs_popStrict (xs : Runs) : option (Sym * Runs) :=
  match xs with
  | [] => None
  | (_, N0) :: xs' => runs_popStrict xs'
  | (SW_raw [], Npos _) :: xs' => runs_popStrict xs'
  | (SW_raw (b :: rest), Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    Some (b, runs_push (SW_raw rest) 1 (runs_push (SW_raw (b :: rest)) n xs'))
  | (SW_D k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    Some (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 (runs_push (SW_D k) n xs')))
  | (SW_S k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    Some (1, runs_push (SW_raw [0; 1]) (1 + k)%N (runs_push (SW_S k) n xs'))
  | (SW_PL k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    Some (1, runs_push (SW_raw [0]) 1 (runs_push (SW_raw [1; 0]) (k + 3)%N
          (runs_push (SW_raw [1; 1]) k (runs_push (SW_S 0) 2 (runs_push (SW_PL k) n xs')))))
  end.

Lemma runs_popStrict_spec xs b ys t :
  runs_popStrict xs = Some (b, ys) -> plug xs t = b >> plug ys t.
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_popStrict plug].
  - discriminate.
  - destruct w as [[|] | | |]; exact IH.
  - destruct w as [[|a rest] | k | k | k]; cbn [runs_popStrict sw_toList].
    + rewrite nil_lpow. exact IH.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      unfold D_word. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      cbn [sw_toList lpow app Str_app].
      unfold S_word.
      replace (1 + N.to_nat k)%nat with (N.to_nat (1 + k)%N) by lia.
      rewrite ?Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      cbn [sw_toList lpow app Str_app].
      unfold PL_word.
      replace (N.to_nat k + 4)%nat with (S (N.to_nat (k + 3)%N)) by lia.
      cbn [lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
Qed.

Lemma runs_popStrict_none xs t :
  runs_popStrict xs = None -> plug xs t = t.
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_popStrict plug].
  - reflexivity.
  - destruct w as [[|] | | |]; exact IH.
  - destruct w as [[|a rest] | | |]; try discriminate.
    cbn [sw_toList]. rewrite nil_lpow. exact IH.
Qed.

Fixpoint runs_removeStrict (w : list Sym) (xs : Runs) : option Runs :=
  match w with
  | [] => Some xs
  | b :: w' =>
    match runs_popStrict xs with
    | Some (c, ys) => if sym_eqb b c then runs_removeStrict w' ys else None
    | None => None
    end
  end.

Lemma runs_removeStrict_spec w xs ys t :
  runs_removeStrict w xs = Some ys -> plug xs t = w *> plug ys t.
Proof.
  gen xs. induction w as [|b w IH]; intros xs H; cbn [runs_removeStrict] in H.
  - inversion H; reflexivity.
  - destruct (runs_popStrict xs) as [[c zs]|] eqn:Hp; [| discriminate].
    destruct (sym_eqb_spec b c); [subst | discriminate].
    rewrite (runs_popStrict_spec _ _ _ t Hp), (IH _ H). reflexivity.
Qed.

Fixpoint splitOnesAux (p : N) (w : list Sym) : N * list Sym :=
  match w with
  | [] => (p, [])
  | b :: rest =>
    if sym_eqb b 1 then splitOnesAux (p + 1)%N rest
    else (p, b :: rest)
  end.

Lemma splitOnesAux_spec p w :
  [1]^^(N.to_nat p) ++ w = [1]^^(N.to_nat (fst (splitOnesAux p w))) ++ snd (splitOnesAux p w).
Proof.
  gen p. induction w as [|b rest IH]; intros p; cbn [splitOnesAux]; [reflexivity |].
  destruct (sym_eqb_spec b 1); [subst | reflexivity].
  rewrite <- (IH (p + 1)%N).
  rewrite N2Nat.inj_add. change (N.to_nat 1) with 1%nat.
  rewrite lpow_plus_r, <- app_assoc. reflexivity.
Qed.

Fixpoint takeOnesAux (acc : N) (xs : Runs) : N * Runs :=
  match xs with
  | [] => (acc, [])
  | (_, N0) :: xs' => takeOnesAux acc xs'
  | (SW_raw [], Npos _) :: xs' => takeOnesAux acc xs'
  | (SW_raw w, Npos pk) :: xs' =>
    let '(p, tail) := splitOnesAux 0 w in
    if N.eqb p 0 then (acc, xs)
    else
      match tail with
      | [] => takeOnesAux (acc + Npos pk * p)%N xs'
      | _ :: _ =>
        let k := N.pred (Npos pk) in
        ((acc + p)%N, runs_push (SW_raw tail) 1 (runs_push (SW_raw w) k xs'))
      end
  | (SW_D n, Npos pk) :: xs' =>
    let k := N.pred (Npos pk) in
    ((acc + (2 * n + 1))%N, runs_push (SW_raw [0; 0]) 1 (runs_push (SW_D n) k xs'))
  | (SW_S n, Npos pk) :: xs' =>
    let k := N.pred (Npos pk) in
    ((acc + 1)%N, runs_push (SW_raw [0; 1]) (1 + n)%N (runs_push (SW_S n) k xs'))
  | (SW_PL _, Npos _) :: _ => (acc, xs)
  end.

Lemma takeOnesAux_spec acc xs t :
  [1]^^(N.to_nat acc) *> plug xs t =
    [1]^^(N.to_nat (fst (takeOnesAux acc xs))) *> plug (snd (takeOnesAux acc xs)) t.
Proof.
  gen acc. induction xs as [|[w [|pk]] xs IH]; intros acc; cbn [takeOnesAux plug].
  - reflexivity.
  - destruct w as [[|] | | |]; exact (IH acc).
  - destruct w as [[|a rest] | n | n | n]; cbn [sw_toList].
    + rewrite nil_lpow. exact (IH acc).
    + pose proof (splitOnesAux_spec 0 (a :: rest)) as Hsp.
      destruct (splitOnesAux 0 (a :: rest)) as [p tail]; cbn [fst snd] in Hsp.
      cbn [N.to_nat lpow app] in Hsp.
      destruct (N.eqb_spec p 0) as [-> | _]; [reflexivity |].
      destruct tail as [|b tail'].
      * rewrite ?app_nil_r in Hsp.
        rewrite Hsp, <- lpow_mul, lpow_Str_add, <- N2Nat.inj_mul, <- N2Nat.inj_add.
        exact (IH (acc + Npos pk * p)%N).
      * cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
        change (N.to_nat 1) with 1%nat.
        cbn [sw_toList lpow]. rewrite ?app_nil_r.
        rewrite Hsp at 1.
        rewrite ?Str_app_assoc, lpow_Str_add, <- N2Nat.inj_add.
        reflexivity.
    + cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow]. rewrite ?app_nil_r, Str_app_assoc.
      rewrite D_word_ones, lpow_Str_add.
      replace (N.to_nat acc + (2 * N.to_nat n + 1))%nat
        with (N.to_nat (acc + (2 * n + 1))%N) by lia.
      reflexivity.
    + cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
      cbn [sw_toList lpow]. rewrite Str_app_assoc.
      rewrite S_word_ones, lpow_Str_add.
      replace (N.to_nat acc + 1)%nat with (N.to_nat (acc + 1)%N) by lia.
      replace (1 + N.to_nat n)%nat with (N.to_nat (1 + n)%N) by lia.
      reflexivity.
    + reflexivity.
Qed.

Definition takeOnes (xs : Runs) : N * Runs := takeOnesAux 0 xs.

Lemma takeOnes_spec xs t :
  plug xs t = [1]^^(N.to_nat (fst (takeOnes xs))) *> plug (snd (takeOnes xs)) t.
Proof.
  exact (takeOnesAux_spec 0 xs t).
Qed.

Definition take111 (xs : Runs) : N * Runs :=
  let '(c1, ys) := takeOnes xs in
  let q := (c1 / 3)%N in
  let rem := (c1 mod 3)%N in
  let ys' :=
    if N.eqb rem 2 then runs_push (SW_raw [1; 1]) 1 ys
    else if N.eqb rem 1 then runs_push (SW_raw [1]) 1 ys
    else ys in
  (q, ys').

Lemma take111_spec xs t :
  plug xs t = [1; 1; 1]^^(N.to_nat (fst (take111 xs))) *> plug (snd (take111 xs)) t.
Proof.
  unfold take111.
  pose proof (takeOnes_spec xs t) as H1.
  destruct (takeOnes xs) as [c1 ys]; cbn [fst snd] in H1 |- *.
  destruct (N_div_mod_nat c1 3 ltac:(lia)) as [Hdiv Hmod].
  change (N.to_nat 3) with 3%nat in Hdiv, Hmod.
  rewrite H1, <- one_pow_three_mul.
  destruct (N.eqb_spec (c1 mod 3) 2) as [Hm2 | Hm2].
  - cbn [fst snd]. rewrite push_plug.
    change (sw_toList (SW_raw [1; 1])) with ([1]^^2).
    change (N.to_nat 1) with 1%nat. rewrite lpow_1, <- Str_app_assoc, <- lpow_add.
    replace (3 * N.to_nat (c1 / 3) + 2)%nat with (N.to_nat c1) by lia.
    reflexivity.
  - destruct (N.eqb_spec (c1 mod 3) 1) as [Hm1 | Hm1]; cbn [fst snd].
    + rewrite push_plug.
      change (sw_toList (SW_raw [1])) with [1].
      change (N.to_nat 1) with 1%nat. rewrite <- Str_app_assoc, <- lpow_add.
      replace (3 * N.to_nat (c1 / 3) + 1)%nat with (N.to_nat c1) by lia.
      reflexivity.
    + replace (3 * N.to_nat (c1 / 3))%nat with (N.to_nat c1) by lia.
      reflexivity.
Qed.

Definition take11 (xs : Runs) : N * Runs :=
  let '(c1, ys) := takeOnes xs in
  let q := (c1 / 2)%N in
  let ys' := if N.eqb (c1 mod 2) 1 then runs_push (SW_raw [1]) 1 ys else ys in
  (q, ys').

Lemma take11_spec xs t :
  plug xs t = [1; 1]^^(N.to_nat (fst (take11 xs))) *> plug (snd (take11 xs)) t.
Proof.
  unfold take11.
  pose proof (takeOnes_spec xs t) as H1.
  destruct (takeOnes xs) as [c1 ys]; cbn [fst snd] in H1 |- *.
  destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv Hmod].
  change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
  rewrite H1, <- one_pow_two_mul.
  destruct (N.eqb_spec (c1 mod 2) 1) as [Hm1 | Hm1]; cbn [fst snd].
  - rewrite push_plug.
    change (sw_toList (SW_raw [1])) with [1].
    change (N.to_nat 1) with 1%nat. rewrite <- Str_app_assoc, <- lpow_add.
    replace (2 * N.to_nat (c1 / 2) + 1)%nat with (N.to_nat c1) by lia.
    reflexivity.
  - replace (2 * N.to_nat (c1 / 2))%nat with (N.to_nat c1) by lia.
    reflexivity.
Qed.

Fixpoint take10Fuel (fuel : nat) (acc : N) (xs : Runs) : N * Runs :=
  match fuel with
  | O => (acc, xs)
  | S fuel' =>
    match xs with
    | (SW_raw w, k) :: rest =>
      if beqListSym w [1; 0] then take10Fuel fuel' (acc + k)%N rest
      else
        match runs_remove [1; 0] xs with
        | Some ys => take10Fuel fuel' (acc + 1)%N ys
        | None => (acc, xs)
        end
    | _ => (acc, xs)
    end
  end.

Lemma take10Fuel_spec fuel acc xs :
  [1; 0]^^(N.to_nat acc) *> runs_denote xs =
    [1; 0]^^(N.to_nat (fst (take10Fuel fuel acc xs))) *> runs_denote (snd (take10Fuel fuel acc xs)).
Proof.
  gen acc xs. induction fuel as [|fuel IH]; intros acc xs; [reflexivity |].
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | |]; cbn [take10Fuel]; [| reflexivity | reflexivity | reflexivity].
  destruct (beqListSym lw [1; 0]) eqn:H10.
  - rewrite <- IH. cbn [runs_denote sw_toList].
    rewrite (beqListSym_eq _ _ H10), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
    reflexivity.
  - destruct (runs_remove [1; 0] ((SW_raw lw, k) :: rest)) as [ys|] eqn:Hr; [| reflexivity].
    rewrite <- IH, (runs_remove_spec _ _ _ Hr).
    rewrite N2Nat.inj_add. change (N.to_nat 1) with 1%nat.
    rewrite lpow_plus_r, Str_app_assoc. reflexivity.
Qed.

Definition take10 (xs : Runs) : N * Runs := take10Fuel 64 0 xs.

Lemma take10_spec xs :
  runs_denote xs = [1; 0]^^(N.to_nat (fst (take10 xs))) *> runs_denote (snd (take10 xs)).
Proof. exact (take10Fuel_spec 64 0 xs). Qed.

Lemma zero_then_one_zero_pow k t :
  [0] *> [1; 0]^^k *> t = [0; 1]^^k *> [0] *> t.
Proof.
  induction k as [|k IH]; cbn [lpow app Str_app]; [reflexivity |].
  f_equal; f_equal. exact IH.
Qed.

Definition peelZeroTen (xs : Runs) : option (N * Runs) :=
  match xs with
  | (SW_raw w1, k1) :: (SW_raw w2, k2) :: rest =>
    if beqListSym w1 [0] then
      if N.eqb k1 1 then
        if beqListSym w2 [1; 0] then Some (k2, runs_push (SW_raw [0]) 1 rest)
        else None
      else None
    else None
  | _ => None
  end.

Lemma peelZeroTen_spec xs k2 ys :
  peelZeroTen xs = Some (k2, ys) -> runs_denote xs = [0; 1]^^(N.to_nat k2) *> runs_denote ys.
Proof.
  destruct xs as [|[[w1| | |] k1] [|[[w2| | |] k2'] rest]]; cbn [peelZeroTen]; try discriminate.
  destruct (beqListSym w1 [0]) eqn:Hw1; [| discriminate].
  destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
  destruct (beqListSym w2 [1; 0]) eqn:Hw2; [| discriminate].
  intros H; inversion H; subst; clear H.
  cbn [runs_denote sw_toList].
  rewrite (beqListSym_eq _ _ Hw1), (beqListSym_eq _ _ Hw2), runs_push_spec.
  change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app].
  apply zero_then_one_zero_pow.
Qed.

Fixpoint take01Fuel (fuel : nat) (acc : N) (xs : Runs) : N * Runs :=
  match fuel with
  | O => (acc, xs)
  | S fuel' =>
    match xs with
    | (SW_raw w, k) :: rest =>
      if beqListSym w [0; 1] then take01Fuel fuel' (acc + k)%N rest
      else if beqListSym w [0; 1; 0; 1] then take01Fuel fuel' (acc + k * 2)%N rest
      else
        match peelZeroTen xs with
        | Some (k2, ys) => take01Fuel fuel' (acc + k2)%N ys
        | None =>
          match runs_remove [0; 1] xs with
          | Some ys => take01Fuel fuel' (acc + 1)%N ys
          | None => (acc, xs)
          end
        end
    | _ => (acc, xs)
    end
  end.

Lemma take01Fuel_spec fuel acc xs :
  [0; 1]^^(N.to_nat acc) *> runs_denote xs =
    [0; 1]^^(N.to_nat (fst (take01Fuel fuel acc xs))) *> runs_denote (snd (take01Fuel fuel acc xs)).
Proof.
  gen acc xs. induction fuel as [|fuel IH]; intros acc xs; [reflexivity |].
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | |]; cbn [take01Fuel]; [| reflexivity | reflexivity | reflexivity].
  destruct (beqListSym lw [0; 1]) eqn:H01.
  - rewrite <- IH. cbn [runs_denote sw_toList].
    rewrite (beqListSym_eq _ _ H01), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
    reflexivity.
  - destruct (beqListSym lw [0; 1; 0; 1]) eqn:H0101.
    + rewrite <- IH. cbn [runs_denote sw_toList].
      rewrite (beqListSym_eq _ _ H0101), <- zero_one_pow_two_mul, <- Str_app_assoc, <- lpow_add.
      replace (N.to_nat acc + 2 * N.to_nat k)%nat with (N.to_nat (acc + k * 2)%N) by lia.
      reflexivity.
    + destruct (peelZeroTen ((SW_raw lw, k) :: rest)) as [[k2 ys]|] eqn:Hpz.
      * rewrite <- IH, (peelZeroTen_spec _ _ _ Hpz), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
        reflexivity.
      * destruct (runs_remove [0; 1] ((SW_raw lw, k) :: rest)) as [ys|] eqn:Hr; [| reflexivity].
        rewrite <- IH, (runs_remove_spec _ _ _ Hr).
        rewrite N2Nat.inj_add. change (N.to_nat 1) with 1%nat.
        rewrite lpow_plus_r, Str_app_assoc. reflexivity.
Qed.

Definition take01 (xs : Runs) : N * Runs := take01Fuel 64 0 xs.

Lemma take01_spec xs :
  runs_denote xs = [0; 1]^^(N.to_nat (fst (take01 xs))) *> runs_denote (snd (take01 xs)).
Proof. exact (take01Fuel_spec 64 0 xs). Qed.

Fixpoint take0101StrictFuel (fuel : nat) (acc : N) (xs : Runs) : N * Runs :=
  match fuel with
  | O => (acc, xs)
  | S fuel' =>
    match xs with
    | (SW_raw w, k) :: rest =>
      if beqListSym w [0; 1; 0; 1] then take0101StrictFuel fuel' (acc + k)%N rest
      else if (if beqListSym w [0; 1] then N.leb 2 k else false) then
        let q := (k / 2)%N in
        let rest' := if N.eqb (k mod 2) 1 then runs_push (SW_raw [0; 1]) 1 rest else rest in
        take0101StrictFuel fuel' (acc + q)%N rest'
      else
        match runs_removeStrict [0; 1; 0; 1] xs with
        | Some ys => take0101StrictFuel fuel' (acc + 1)%N ys
        | None => (acc, xs)
        end
    | _ => (acc, xs)
    end
  end.

Lemma take0101StrictFuel_spec fuel acc xs t :
  [0; 1; 0; 1]^^(N.to_nat acc) *> plug xs t =
    [0; 1; 0; 1]^^(N.to_nat (fst (take0101StrictFuel fuel acc xs))) *> plug (snd (take0101StrictFuel fuel acc xs)) t.
Proof.
  gen acc xs. induction fuel as [|fuel IH]; intros acc xs; [reflexivity |].
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | |]; cbn [take0101StrictFuel]; [| reflexivity | reflexivity | reflexivity].
  destruct (beqListSym lw [0; 1; 0; 1]) eqn:H0101.
  - rewrite <- IH. cbn [plug sw_toList].
    rewrite (beqListSym_eq _ _ H0101), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
    reflexivity.
  - destruct (if beqListSym lw [0; 1] then N.leb 2 k else false) eqn:H01.
    + destruct (beqListSym lw [0; 1]) eqn:Hlw; [| discriminate].
      rewrite <- IH. cbn [plug sw_toList].
      rewrite (beqListSym_eq _ _ Hlw).
      destruct (N_div_mod_nat k 2 ltac:(lia)) as [Hdiv Hmod].
      change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
      destruct (N.eqb_spec (k mod 2) 1) as [Hm1 | Hm1].
      * rewrite push_plug, N2Nat.inj_add, lpow_add, Str_app_assoc.
        rewrite <- (zero_one_pow_two_mul (N.to_nat (k / 2))).
        f_equal.
        cbn [sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat k) with (2 * N.to_nat (k / 2)%N + 1)%nat by lia.
        rewrite lpow_plus_r, Str_app_assoc. reflexivity.
      * rewrite N2Nat.inj_add, lpow_add, Str_app_assoc, <- (zero_one_pow_two_mul (N.to_nat (k / 2))).
        replace (2 * N.to_nat (k / 2))%nat with (N.to_nat k) by lia.
        reflexivity.
    + destruct (runs_removeStrict [0; 1; 0; 1] ((SW_raw lw, k) :: rest)) as [ys|] eqn:Hr; [| reflexivity].
      rewrite <- IH, (runs_removeStrict_spec _ _ _ t Hr).
      rewrite N2Nat.inj_add. change (N.to_nat 1) with 1%nat.
      rewrite lpow_plus_r, Str_app_assoc. reflexivity.
Qed.

Definition take0101Strict (xs : Runs) : N * Runs := take0101StrictFuel 64 0 xs.

Lemma take0101Strict_spec xs t :
  plug xs t = [0; 1; 0; 1]^^(N.to_nat (fst (take0101Strict xs))) *> plug (snd (take0101Strict xs)) t.
Proof. exact (take0101StrictFuel_spec 64 0 xs t). Qed.

Definition takeD (xs : Runs) : option (N * Runs) :=
  match xs with
  | (SW_D n, Npos pk) :: rest => Some (n, runs_push (SW_D n) (N.pred (Npos pk)) rest)
  | (SW_raw (b :: _), Npos _) :: _ =>
    if sym_eqb b 1 then
      let '(c1, ys) := takeOnes xs in
      if N.eqb (c1 mod 2) 1 then
        match runs_remove [0; 0] ys with
        | Some zs => Some ((c1 / 2)%N, zs)
        | None => None
        end
      else None
    else None
  | _ => None
  end.

Lemma takeD_spec xs n ys :
  takeD xs = Some (n, ys) -> runs_denote xs = D_word (N.to_nat n) *> runs_denote ys.
Proof.
  destruct xs as [|[w [|pk]] rest]; cbn [takeD]; try discriminate.
  - destruct w as [[|] | | |]; discriminate.
  - destruct w as [[|b l'] | m | | ]; try discriminate.
    + destruct (sym_eqb b 1); [| discriminate].
      pose proof (takeOnes_spec ((SW_raw (b :: l'), Npos pk) :: rest) 0inf) as H1.
      rewrite <- !denote_eq_plug_0inf in H1.
      destruct (takeOnes ((SW_raw (b :: l'), Npos pk) :: rest)) as [c1 mid]; cbn [fst snd] in H1.
      destruct (N.eqb_spec (c1 mod 2) 1) as [Hm1 | _]; [| discriminate].
      destruct (runs_remove [0; 0] mid) as [zs|] eqn:Hr; [| discriminate].
      intros H; inversion H; subst; clear H.
      destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv _].
      change (N.to_nat 2) with 2%nat in Hdiv.
      rewrite H1, (runs_remove_spec _ _ _ Hr).
      replace (N.to_nat c1) with (1 + 2 * N.to_nat (c1 / 2))%nat by lia.
      rewrite lpow_add, one_pow_two_mul.
      unfold D_word. cbn [lpow app Str_app]. rewrite ?Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      cbn [runs_denote sw_toList].
      rewrite runs_push_spec, pos_to_nat_succ.
      cbn [sw_toList lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Definition takeDStrict (xs : Runs) : option (N * Runs) :=
  match xs with
  | (SW_D n, Npos pk) :: rest => Some (n, runs_push (SW_D n) (N.pred (Npos pk)) rest)
  | (SW_raw (b :: _), Npos _) :: _ =>
    if sym_eqb b 1 then
      let '(c1, ys) := takeOnes xs in
      if N.eqb (c1 mod 2) 1 then
        match runs_removeStrict [0; 0] ys with
        | Some zs => Some ((c1 / 2)%N, zs)
        | None => None
        end
      else None
    else None
  | _ => None
  end.

Lemma takeDStrict_spec xs n ys t :
  takeDStrict xs = Some (n, ys) -> plug xs t = D_word (N.to_nat n) *> plug ys t.
Proof.
  destruct xs as [|[w [|pk]] rest]; cbn [takeDStrict]; try discriminate.
  - destruct w as [[|] | | |]; discriminate.
  - destruct w as [[|b l'] | m | | ]; try discriminate.
    + destruct (sym_eqb b 1); [| discriminate].
      pose proof (takeOnes_spec ((SW_raw (b :: l'), Npos pk) :: rest) t) as H1.
      destruct (takeOnes ((SW_raw (b :: l'), Npos pk) :: rest)) as [c1 mid]; cbn [fst snd] in H1.
      destruct (N.eqb_spec (c1 mod 2) 1) as [Hm1 | _]; [| discriminate].
      destruct (runs_removeStrict [0; 0] mid) as [zs|] eqn:Hr; [| discriminate].
      intros H; inversion H; subst; clear H.
      destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv _].
      change (N.to_nat 2) with 2%nat in Hdiv.
      rewrite H1, (runs_removeStrict_spec _ _ _ t Hr).
      replace (N.to_nat c1) with (1 + 2 * N.to_nat (c1 / 2))%nat by lia.
      rewrite lpow_add, one_pow_two_mul.
      unfold D_word. cbn [lpow app Str_app]. rewrite ?Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      cbn [plug sw_toList].
      rewrite push_plug, pos_to_nat_succ.
      cbn [sw_toList lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Definition takeS (xs : Runs) : option (N * Runs) :=
  match xs with
  | (SW_S n, Npos pk) :: rest => Some (n, runs_push (SW_S n) (N.pred (Npos pk)) rest)
  | (SW_raw _, _) :: _ =>
    match runs_remove [1; 0; 1] xs with
    | Some ys =>
      let '(k01, zs) := take01 ys in
      Some (k01, zs)
    | None => None
    end
  | _ => None
  end.

Lemma takeS_spec xs n ys :
  takeS xs = Some (n, ys) -> runs_denote xs = S_word (N.to_nat n) *> runs_denote ys.
Proof.
  destruct xs as [|[w k] rest]; cbn [takeS]; try discriminate.
  destruct w as [lw | | m | ]; try discriminate.
  - destruct (runs_remove [1; 0; 1] ((SW_raw lw, k) :: rest)) as [mid|] eqn:Hr; [| discriminate].
    pose proof (take01_spec mid) as H01.
    destruct (take01 mid) as [k01 zs]; cbn [fst snd] in H01.
    intros H; inversion H; subst; clear H.
    rewrite (runs_remove_spec _ _ _ Hr), H01.
    unfold S_word. cbn [Nat.add lpow app Str_app]. reflexivity.
  - destruct k as [|pk]; [discriminate |].
    intros H; inversion H; subst; clear H.
    cbn [runs_denote sw_toList].
    rewrite runs_push_spec, pos_to_nat_succ.
    cbn [sw_toList lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Definition Digits := list (N * N).

Fixpoint denD (v : Digits) (t : side) : side :=
  match v with
  | [] => t
  | (n, k) :: xs => (D_word (N.to_nat n))^^(N.to_nat k) *> denD xs t
  end.

Fixpoint denDRev (v : Digits) (t : side) : side :=
  match v with
  | [] => t
  | (n, k) :: xs => denDRev xs ((D_word (N.to_nat n))^^(N.to_nat k) *> t)
  end.

Lemma denDRev_rev_append xs acc t :
  denDRev xs (denD acc t) = denD (rev_append xs acc) t.
Proof.
  gen acc. induction xs as [|[n k] xs IH]; intros acc; [reflexivity |].
  exact (IH ((n, k) :: acc)).
Qed.

Lemma call_denD v {r s} (H : call r s) : call (denD v r) (denD v s).
Proof.
  induction v as [|[n k] v IH]; cbn [denD]; [exact H |].
  apply call_D_pow, IH.
Qed.

Lemma call_denDRev v {r s} (H : call r s) : call (denDRev v r) (denDRev v s).
Proof.
  change (denDRev v r) with (denDRev v (denD [] r)).
  change (denDRev v s) with (denDRev v (denD [] s)).
  rewrite !denDRev_rev_append.
  exact (call_denD _ H).
Qed.

Lemma calls_denD v {k r s} (H : calls k r s) : calls k (denD v r) (denD v s).
Proof.
  induction H as [r | k r s t H1 _ IH]; [constructor |].
  econstructor; [apply call_denD, H1 | exact IH].
Qed.

Lemma calls_denDRev v {k r s} (H : calls k r s) : calls k (denDRev v r) (denDRev v s).
Proof.
  induction H as [r | k r s t H1 _ IH]; [constructor |].
  econstructor; [apply call_denDRev, H1 | exact IH].
Qed.

Definition pushD (n k : N) (ds : Digits) : Digits :=
  if N.eqb k 0 then ds
  else
    match ds with
    | (m, j) :: rest =>
      if N.eqb n m then (m, (k + j)%N) :: rest
      else (n, k) :: ds
    | [] => [(n, k)]
    end.

Lemma denD_pushD n k xs t :
  denD (pushD n k xs) t = (D_word (N.to_nat n))^^(N.to_nat k) *> denD xs t.
Proof.
  unfold pushD.
  destruct (N.eqb_spec k 0) as [-> | _]; [reflexivity |].
  destruct xs as [|[m j] rest]; [reflexivity |].
  destruct (N.eqb_spec n m) as [-> | _]; [| reflexivity].
  cbn [denD]. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma denDRev_pushD n k xs t :
  denDRev (pushD n k xs) t = denDRev xs ((D_word (N.to_nat n))^^(N.to_nat k) *> t).
Proof.
  unfold pushD.
  destruct (N.eqb_spec k 0) as [-> | _]; [reflexivity |].
  destruct xs as [|[m j] rest]; [reflexivity |].
  destruct (N.eqb_spec n m) as [-> | _]; [| reflexivity].
  cbn [denDRev].
  replace (N.to_nat (k + j)%N) with (N.to_nat j + N.to_nat k)%nat by lia.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Fixpoint pushDRevAux (xs acc : Digits) : Digits :=
  match xs with
  | [] => acc
  | (n, k) :: xs' => pushDRevAux xs' (pushD n k acc)
  end.

Lemma denD_pushDRevAux xs acc t :
  denD (pushDRevAux xs acc) t = denDRev xs (denD acc t).
Proof.
  gen acc. induction xs as [|[n k] xs IH]; intros acc; [reflexivity |].
  cbn [pushDRevAux denDRev]. rewrite IH, denD_pushD. reflexivity.
Qed.

Lemma denDRev_pushDRevAux xs acc t :
  denDRev (pushDRevAux xs acc) t = denDRev acc (denD xs t).
Proof.
  gen acc. induction xs as [|[n k] xs IH]; intros acc; [reflexivity |].
  cbn [pushDRevAux denD]. rewrite IH, denDRev_pushD. reflexivity.
Qed.

Record RTape := MkRTape {
  r_raw   : Runs;
  d_front : Digits;
  d_back  : Digits;
  r_tail  : Runs
}.

Definition rt_denote (rt : RTape) : side :=
  plug (r_raw rt) (denD (d_front rt) (denDRev (d_back rt) (runs_denote (r_tail rt)))).

Definition hasD (rt : RTape) : bool :=
  match d_front rt, d_back rt with
  | [], [] => false
  | _, _ => true
  end.

Fixpoint flushDBack (db : Digits) (rt : Runs) : Runs :=
  match db with
  | [] => rt
  | (n, k) :: rest => flushDBack rest (runs_push (SW_D n) k rt)
  end.

Lemma flushDBack_spec db rt :
  runs_denote (flushDBack db rt) = denDRev db (runs_denote rt).
Proof.
  gen rt. induction db as [|[n k] rest IH]; intros rt; [reflexivity |].
  cbn [flushDBack denDRev]. rewrite IH, runs_push_spec. reflexivity.
Qed.

Fixpoint flushDFront (df : Digits) (rt : Runs) : Runs :=
  match df with
  | [] => rt
  | (n, k) :: rest => runs_push (SW_D n) k (flushDFront rest rt)
  end.

Lemma flushDFront_spec df rt :
  runs_denote (flushDFront df rt) = denD df (runs_denote rt).
Proof.
  induction df as [|[n k] rest IH]; [reflexivity |].
  cbn [flushDFront denD]. rewrite runs_push_spec, IH. reflexivity.
Qed.

Definition flushDToTail (df db : Digits) (rt : Runs) : Runs :=
  flushDFront df (flushDBack db rt).

Lemma flushDToTail_spec df db rt :
  runs_denote (flushDToTail df db rt) = denD df (denDRev db (runs_denote rt)).
Proof.
  unfold flushDToTail. rewrite flushDFront_spec, flushDBack_spec. reflexivity.
Qed.

Definition flushAllToTail (rt : RTape) : RTape :=
  MkRTape [] [] [] (put (r_raw rt) (flushDToTail (d_front rt) (d_back rt) (r_tail rt))).

Lemma flushAllToTail_spec rt : rt_denote (flushAllToTail rt) = rt_denote rt.
Proof.
  unfold flushAllToTail, rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
  rewrite put_spec, flushDToTail_spec. reflexivity.
Qed.

Fixpoint absorbRawD (rr : Runs) (df : Digits) : Runs * Digits :=
  match rr with
  | (SW_D n, k) :: rest =>
    match absorbRawD rest df with
    | ([], df') => ([], pushD n k df')
    | (rr', df') => ((SW_D n, k) :: rr', df')
    end
  | _ => (rr, df)
  end.

Lemma absorbRawD_spec rr df t :
  plug (fst (absorbRawD rr df)) (denD (snd (absorbRawD rr df)) t) = plug rr (denD df t).
Proof.
  gen df. induction rr as [|[w k] rest IH]; intros df; [reflexivity |].
  destruct w as [| n | | ]; cbn [absorbRawD]; try reflexivity.
  pose proof (IH df) as H.
  destruct (absorbRawD rest df) as [[|x xs] df']; cbn [fst snd plug sw_toList] in H |- *.
  - rewrite denD_pushD, H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Fixpoint absorbTailD (rt : Runs) (db : Digits) : Runs * Digits :=
  match rt with
  | (SW_D n, k) :: rest => absorbTailD rest (pushD n k db)
  | _ => (rt, db)
  end.

Lemma absorbTailD_spec rt db :
  denDRev (snd (absorbTailD rt db)) (runs_denote (fst (absorbTailD rt db))) =
    denDRev db (runs_denote rt).
Proof.
  gen db. induction rt as [|[w k] rest IH]; intros db; [reflexivity |].
  destruct w as [| n | | ]; cbn [absorbTailD runs_denote sw_toList]; try reflexivity.
  rewrite IH, denDRev_pushD. reflexivity.
Qed.

Definition cleanTailZeros (rt : Runs) : Runs :=
  match rt with
  | (w, _) :: _ => if sw_all_zero w then if runs_zeros rt then [] else rt else rt
  | [] => []
  end.

Lemma cleanTailZeros_spec rt : runs_denote (cleanTailZeros rt) = runs_denote rt.
Proof.
  destruct rt as [|[w k] rest]; [reflexivity |].
  unfold cleanTailZeros.
  destruct (sw_all_zero w); [| reflexivity].
  destruct (runs_zeros ((w, k) :: rest)) eqn:Hz; [| reflexivity].
  symmetry. exact (runs_zeros_spec _ Hz).
Qed.

Definition normRTape (rt : RTape) : RTape :=
  let '(rr1, df1) := absorbRawD (r_raw rt) (d_front rt) in
  let '(rt1, db1) :=
    match rr1 with
    | [] => absorbTailD (r_tail rt) (d_back rt)
    | _ :: _ => (r_tail rt, d_back rt)
    end in
  let rt2 := cleanTailZeros rt1 in
  match df1, db1, rr1 with
  | [], [], _ :: _ =>
    let rt3 := put rr1 rt2 in
    let '(rt4, db4) := absorbTailD rt3 [] in
    MkRTape [] [] db4 (cleanTailZeros rt4)
  | _, _, _ => MkRTape rr1 df1 db1 rt2
  end.

Lemma normRTape_spec rt : rt_denote (normRTape rt) = rt_denote rt.
Proof.
  unfold normRTape.
  pose proof (absorbRawD_spec (r_raw rt) (d_front rt) (denDRev (d_back rt) (runs_denote (r_tail rt)))) as Ha1.
  destruct (absorbRawD (r_raw rt) (d_front rt)) as [rr1 df1]; cbn [fst snd] in Ha1.
  change (plug (r_raw rt) (denD (d_front rt) (denDRev (d_back rt) (runs_denote (r_tail rt))))) with (rt_denote rt) in Ha1.
  destruct rr1 as [|x xs].
  - pose proof (absorbTailD_spec (r_tail rt) (d_back rt)) as Ha2.
    destruct (absorbTailD (r_tail rt) (d_back rt)) as [rt1 db1]; cbn [fst snd] in Ha2.
    destruct df1, db1; unfold rt_denote; cbn [r_raw d_front d_back r_tail plug];
      rewrite cleanTailZeros_spec, Ha2; exact Ha1.
  - destruct df1 as [|y ys].
    + destruct (d_back rt) as [|z zs] eqn:Hdb.
      * pose proof (absorbTailD_spec (put (x :: xs) (cleanTailZeros (r_tail rt))) []) as Ha4.
        destruct (absorbTailD (put (x :: xs) (cleanTailZeros (r_tail rt))) []) as [rt4 db4]; cbn [fst snd] in Ha4.
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD].
        rewrite cleanTailZeros_spec, Ha4, put_spec, cleanTailZeros_spec.
        cbn [denD denDRev] in Ha1. exact Ha1.
      * unfold rt_denote; cbn [r_raw d_front d_back r_tail].
        rewrite cleanTailZeros_spec. exact Ha1.
    + unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite cleanTailZeros_spec. exact Ha1.
Qed.

Fixpoint popDList (xs : Digits) : option (N * Digits) :=
  match xs with
  | [] => None
  | (_, N0) :: rest => popDList rest
  | (n, Npos pk) :: rest => Some (n, pushD n (N.pred (Npos pk)) rest)
  end.

Lemma popDList_denD xs n xs' t :
  popDList xs = Some (n, xs') -> denD xs t = D_word (N.to_nat n) *> denD xs' t.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denD].
  - discriminate.
  - exact IH.
  - intros H; inversion H; subst; clear H.
    rewrite denD_pushD, pos_to_nat_succ. cbn [lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma popDList_denD_none xs t :
  popDList xs = None -> denD xs t = t.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denD].
  - reflexivity.
  - exact IH.
  - discriminate.
Qed.

Lemma popDList_denDRev xs n xs' t :
  popDList xs = Some (n, xs') -> denDRev xs t = denDRev xs' (D_word (N.to_nat n) *> t).
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denDRev].
  - discriminate.
  - exact IH.
  - intros H; inversion H; subst; clear H.
    rewrite denDRev_pushD.
    replace (N.to_nat (Npos pk)) with (N.to_nat (N.pred (Npos pk)) + 1)%nat by lia.
    rewrite lpow_plus_r, Str_app_assoc. reflexivity.
Qed.

Lemma popDList_denDRev_none xs t :
  popDList xs = None -> denDRev xs t = t.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denDRev].
  - reflexivity.
  - exact IH.
  - discriminate.
Qed.

Definition popDFrontOneAux (df db : Digits) : option (N * Digits * Digits) :=
  match popDList df with
  | Some (n, df') => Some (n, df', db)
  | None =>
    match popDList (pushDRevAux db []) with
    | Some (n, df') => Some (n, df', [])
    | None => None
    end
  end.

Lemma popDFrontOneAux_spec df db n df' db' t :
  popDFrontOneAux df db = Some (n, df', db') ->
  denD df (denDRev db t) = D_word (N.to_nat n) *> denD df' (denDRev db' t).
Proof.
  unfold popDFrontOneAux.
  destruct (popDList df) as [[m df1]|] eqn:H1.
  - intros H; inversion H; subst; clear H.
    exact (popDList_denD df _ _ _ H1).
  - destruct (popDList (pushDRevAux db [])) as [[m df1]|] eqn:H2; [| discriminate].
    intros H; inversion H; subst; clear H.
    rewrite (popDList_denD_none df _ H1).
    change (denDRev db t) with (denDRev db (denD [] t)).
    rewrite <- denD_pushDRevAux.
    exact (popDList_denD _ _ _ t H2).
Qed.

Lemma popDFrontOneAux_none df db t :
  popDFrontOneAux df db = None -> denD df (denDRev db t) = t.
Proof.
  unfold popDFrontOneAux.
  destruct (popDList df) as [[m df1]|] eqn:H1; [discriminate |].
  destruct (popDList (pushDRevAux db [])) as [[m df1]|] eqn:H2; [discriminate |].
  intros _. rewrite (popDList_denD_none df _ H1).
  change (denDRev db t) with (denDRev db (denD [] t)).
  rewrite <- denD_pushDRevAux.
  exact (popDList_denD_none _ t H2).
Qed.

Definition popDBackOneAux (df db : Digits) : option (N * Digits * Digits) :=
  match popDList db with
  | Some (n, db') => Some (n, df, db')
  | None =>
    match popDList (pushDRevAux df []) with
    | Some (n, db') => Some (n, [], db')
    | None => None
    end
  end.

Lemma popDBackOneAux_spec df db n df' db' t :
  popDBackOneAux df db = Some (n, df', db') ->
  denD df (denDRev db t) = denD df' (denDRev db' (D_word (N.to_nat n) *> t)).
Proof.
  unfold popDBackOneAux.
  destruct (popDList db) as [[m db1]|] eqn:H1.
  - intros H; inversion H; subst; clear H.
    rewrite (popDList_denDRev db _ _ t H1). reflexivity.
  - destruct (popDList (pushDRevAux df [])) as [[m db1]|] eqn:H2; [| discriminate].
    intros H; inversion H; subst; clear H.
    rewrite (popDList_denDRev_none db t H1).
    change (denD df t) with (denDRev [] (denD df t)).
    rewrite <- denDRev_pushDRevAux.
    exact (popDList_denDRev _ _ _ t H2).
Qed.

Fixpoint sweepDFront (l : Runs) (df : Digits) : Runs :=
  match df with
  | [] => l
  | (n, k) :: xs => sweepDFront (runs_push (SW_S n) k l) xs
  end.

Lemma sweepDFront_spec l df t :
  CfgR (runs_denote l) (denD df t) -->* CfgR (runs_denote (sweepDFront l df)) t.
Proof.
  gen l. induction df as [|[n k] xs IH]; intros l; cbn [sweepDFront denD]; [apply evstep_refl |].
  eapply ev_trans; [apply rule_right_pow |].
  pose proof (IH (runs_push (SW_S n) k l)) as H2.
  rewrite runs_push_spec in H2. exact H2.
Qed.

Definition sweepDBack (l : Runs) (db : Digits) : Runs :=
  sweepDFront l (rev_append db []).

Lemma sweepDBack_spec l db t :
  CfgR (runs_denote l) (denDRev db t) -->* CfgR (runs_denote (sweepDBack l db)) t.
Proof.
  unfold sweepDBack.
  change (denDRev db t) with (denDRev db (denD [] t)).
  rewrite denDRev_rev_append.
  apply sweepDFront_spec.
Qed.

Definition sweepRight (l : Runs) (df db : Digits) : Runs :=
  sweepDBack (sweepDFront l df) db.

Lemma sweepRight_spec l df db t :
  CfgR (runs_denote l) (denD df (denDRev db t)) -->* CfgR (runs_denote (sweepRight l df db)) t.
Proof.
  eapply ev_trans; [apply sweepDFront_spec | apply sweepDBack_spec].
Qed.

Fixpoint sweepLeft (l : Runs) (df : Digits) : Runs * Digits :=
  match l with
  | (SW_S n, k) :: rest => sweepLeft rest (pushD n k df)
  | _ => (l, df)
  end.

Lemma sweepLeft_spec l df t :
  CfgL (runs_denote l) (denD df t) -->*
  CfgL (runs_denote (fst (sweepLeft l df))) (denD (snd (sweepLeft l df)) t).
Proof.
  gen df. induction l as [|[w k] rest IH]; intros df; [apply evstep_refl |].
  destruct w as [| | n | ]; cbn [sweepLeft runs_denote sw_toList]; try apply evstep_refl.
  eapply ev_trans; [apply rule_left_pow |].
  pose proof (IH (pushD n k df)) as H2.
  rewrite denD_pushD in H2. exact H2.
Qed.

Definition popBitRTapeNoNorm (rt : RTape) : Sym * RTape :=
  match runs_popStrict (r_raw rt) with
  | Some (b, rr') => (b, MkRTape rr' (d_front rt) (d_back rt) (r_tail rt))
  | None =>
    match popDFrontOneAux (d_front rt) (d_back rt) with
    | Some (n, df', db') =>
      (1, MkRTape (runs_push (SW_raw [1; 1]) n [(SW_raw [0; 0], 1%N)]) df' db' (r_tail rt))
    | None =>
      let '(b, rt') := runs_pop (r_tail rt) in
      (b, MkRTape [] [] [] rt')
    end
  end.

Lemma popBitRTapeNoNorm_spec rt :
  rt_denote rt = fst (popBitRTapeNoNorm rt) >> rt_denote (snd (popBitRTapeNoNorm rt)).
Proof.
  destruct rt as [rr df db rtail]; unfold popBitRTapeNoNorm, rt_denote; cbn [r_raw d_front d_back r_tail].
  destruct (runs_popStrict rr) as [[b rr']|] eqn:Hps.
  - cbn [fst snd r_raw d_front d_back r_tail].
    exact (runs_popStrict_spec rr b rr' _ Hps).
  - rewrite (runs_popStrict_none rr _ Hps).
    destruct (popDFrontOneAux df db) as [[[n df'] db']|] eqn:Hp.
    + cbn [fst snd r_raw d_front d_back r_tail].
      rewrite (popDFrontOneAux_spec df db n df' db' _ Hp), push_plug.
      cbn [plug sw_toList]. change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]. unfold D_word. rewrite ?Str_app_assoc. reflexivity.
    + rewrite (popDFrontOneAux_none df db _ Hp).
      pose proof (runs_pop_spec rtail) as Hpop.
      destruct (runs_pop rtail) as [b rt']; cbn in Hpop |- *.
      exact Hpop.
Qed.

Definition popBitRTape (rt : RTape) : Sym * RTape :=
  popBitRTapeNoNorm (normRTape rt).

Lemma popBitRTape_spec rt :
  rt_denote rt = fst (popBitRTape rt) >> rt_denote (snd (popBitRTape rt)).
Proof.
  unfold popBitRTape. rewrite <- (normRTape_spec rt).
  exact (popBitRTapeNoNorm_spec (normRTape rt)).
Qed.

Fixpoint peekFirstBitRuns (xs : Runs) : option Sym :=
  match xs with
  | [] => None
  | (_, N0) :: xs' => peekFirstBitRuns xs'
  | (SW_raw [], Npos _) :: xs' => peekFirstBitRuns xs'
  | (SW_raw (b :: _), Npos _) :: _ => Some b
  | (_, Npos _) :: _ => Some 1
  end.

Fixpoint takeBitsRTapeAux (pat : list Sym) (rt : RTape) : option RTape :=
  match pat with
  | [] => Some rt
  | b :: rest =>
    let '(c, rt') := popBitRTapeNoNorm rt in
    if sym_eqb b c then takeBitsRTapeAux rest rt' else None
  end.

Lemma takeBitsRTapeAux_spec pat rt rt' :
  takeBitsRTapeAux pat rt = Some rt' -> rt_denote rt = pat *> rt_denote rt'.
Proof.
  gen rt. induction pat as [|b rest IH]; intros rt H; cbn [takeBitsRTapeAux] in H.
  - inversion H; reflexivity.
  - pose proof (popBitRTapeNoNorm_spec rt) as Hp.
    destruct (popBitRTapeNoNorm rt) as [c rt1]; cbn in Hp.
    destruct (sym_eqb_spec b c); [subst | discriminate].
    rewrite Hp, (IH _ H). reflexivity.
Qed.

Definition takeBitsRTape (pat : list Sym) (rt : RTape) : option RTape :=
  match pat with
  | [] => Some rt
  | b :: _ =>
    match r_raw rt with
    | [] =>
      if hasD rt then
        if sym_eqb b 1 then takeBitsRTapeAux pat rt else None
      else
        match runs_remove pat (r_tail rt) with
        | Some rtail' => Some (MkRTape [] [] [] rtail')
        | None => None
        end
    | _ :: _ =>
      match peekFirstBitRuns (r_raw rt) with
      | Some c => if sym_eqb b c then takeBitsRTapeAux pat rt else None
      | None => takeBitsRTapeAux pat rt
      end
    end
  end.

Lemma hasD_false_nil rr df db rtail : hasD (MkRTape rr df db rtail) = false -> df = [] /\ db = [].
Proof.
  destruct df, db; cbn; intuition discriminate.
Qed.

Lemma takeBitsRTape_spec pat rt rt' :
  takeBitsRTape pat rt = Some rt' -> rt_denote rt = pat *> rt_denote rt'.
Proof.
  destruct pat as [|b rest]; [intros H; inversion H; reflexivity |].
  destruct rt as [[|x xs] df db rtail]; cbn [takeBitsRTape r_raw r_tail].
  - destruct (hasD (MkRTape [] df db rtail)) eqn:Hhd.
    + destruct (sym_eqb b 1); [apply takeBitsRTapeAux_spec | discriminate].
    + destruct (hasD_false_nil [] df db rtail Hhd) as [-> ->].
      destruct (runs_remove (b :: rest) rtail) as [rtail'|] eqn:Hr; [| discriminate].
      intros H; inversion H; subst; clear H.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      exact (runs_remove_spec _ _ _ Hr).
  - destruct (peekFirstBitRuns (x :: xs)) as [c|].
    + destruct (sym_eqb b c); [apply takeBitsRTapeAux_spec | discriminate].
    + apply takeBitsRTapeAux_spec.
Qed.

Definition takeDRTape (rt0 : RTape) : option (N * RTape) :=
  let rt := normRTape rt0 in
  match r_raw rt with
  | _ :: _ =>
    match takeDStrict (r_raw rt) with
    | Some (n, rr') => Some (n, MkRTape rr' (d_front rt) (d_back rt) (r_tail rt))
    | None => None
    end
  | [] =>
    match popDFrontOneAux (d_front rt) (d_back rt) with
    | Some (n, df', db') => Some (n, MkRTape [] df' db' (r_tail rt))
    | None =>
      match takeD (r_tail rt) with
      | Some (n, rtail') => Some (n, MkRTape [] [] [] rtail')
      | None => None
      end
    end
  end.

Lemma takeDRTape_spec rt0 n rt' :
  takeDRTape rt0 = Some (n, rt') -> rt_denote rt0 = D_word (N.to_nat n) *> rt_denote rt'.
Proof.
  unfold takeDRTape. rewrite <- (normRTape_spec rt0).
  generalize (normRTape rt0) as rt; clear rt0; intros [rr df db rtail]; cbn [r_raw d_front d_back r_tail].
  destruct rr as [|x xs].
  - destruct (popDFrontOneAux df db) as [[[m df'] db']|] eqn:Hp.
    + intros H; inversion H; subst; clear H.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
      exact (popDFrontOneAux_spec df db _ _ _ _ Hp).
    + destruct (takeD rtail) as [[m rtail']|] eqn:Ht; [| discriminate].
      intros H; inversion H; subst; clear H.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite (popDFrontOneAux_none df db _ Hp).
      exact (takeD_spec rtail _ _ Ht).
  - destruct (takeDStrict (x :: xs)) as [[m rr']|] eqn:Ht; [| discriminate].
    intros H; inversion H; subst; clear H.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail].
    exact (takeDStrict_spec _ _ _ _ Ht).
Qed.

Fixpoint peelRawD (fuel : nat) (xs : Runs) : Runs :=
  match fuel with
  | O => xs
  | S fuel' =>
    match xs with
    | (SW_raw _, _) :: _ =>
      match takeD xs with
      | Some (n, ys) => runs_push (SW_D n) 1 (peelRawD fuel' ys)
      | None => xs
      end
    | _ => xs
    end
  end.

Lemma peelRawD_spec fuel xs : runs_denote (peelRawD fuel xs) = runs_denote xs.
Proof.
  gen xs. induction fuel as [|fuel IH]; intros xs; [reflexivity |].
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | |]; cbn [peelRawD]; try reflexivity.
  destruct (takeD ((SW_raw lw, k) :: rest)) as [[n ys]|] eqn:Ht; [| reflexivity].
  rewrite runs_push_spec, IH.
  change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow]. rewrite ?app_nil_r.
  symmetry. exact (takeD_spec _ _ _ Ht).
Qed.

Definition normImmTail (xs : Runs) : Runs :=
  match xs with
  | (SW_raw w, k) :: rest =>
    if (if beqListSym w [1; 0] then N.eqb k 1 else false) then
      runs_push (SW_raw [1; 0]) 1 (peelRawD 4 rest)
    else xs
  | _ => xs
  end.

Lemma normImmTail_spec xs : runs_denote (normImmTail xs) = runs_denote xs.
Proof.
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | |]; cbn [normImmTail]; try reflexivity.
  destruct (beqListSym lw [1; 0]) eqn:Hw; [| reflexivity].
  destruct (N.eqb_spec k 1) as [-> | _]; [| reflexivity].
  rewrite runs_push_spec, peelRawD_spec.
  cbn [runs_denote sw_toList]. rewrite (beqListSym_eq _ _ Hw). reflexivity.
Qed.

Definition doCallsD (df db : Digits) (rtail : Runs) (h : N) (allowDefect : bool)
    : option (N * Digits * Digits * Runs) :=
  if N.eqb h 0 then None
  else
    let rtail1 := normImmTail (cleanTailZeros rtail) in
    match rtail1 with
    | [] => Some (h, df, pushD 0 (h * 2)%N db, [])
    | (SW_raw w1, k1) :: (SW_D dn, kd) :: rest =>
      if (if beqListSym w1 [1; 0] then N.eqb k1 1 else false) then
        if N.eqb dn 0 then
          if N.leb 2 kd then
            match popDBackOneAux df db with
            | Some (j, df1, db1) =>
              let avail := (kd / 2)%N in
              let hd := if N.leb h avail then h else avail in
              let rem := (kd - hd * 2)%N in
              Some (hd, df1, pushD 2 1 (pushD 3 (hd - 1)%N (pushD (j + 1)%N 1 db1)),
                    runs_push (SW_raw [1; 0]) 1 (runs_push (SW_D 0) rem rest))
            | None => None
            end
          else if (if allowDefect then N.eqb kd 1 else false) then
            match takeD rest with
            | Some (m, rest') =>
              match popDBackOneAux df db with
              | Some (j, df1, db1) =>
                Some (1%N, df1, pushD (m + 2)%N 1 (pushD (j + 1)%N 1 db1),
                      runs_push (SW_raw [1; 0]) 1 rest')
              | None => None
              end
            | None => None
            end
          else None
        else if N.eqb dn 1 then
          if (if allowDefect then N.ltb 0 kd else false) then
            let afterD1 := runs_push (SW_D 1) (kd - 1)%N rest in
            match takeD afterD1 with
            | Some (m, rest') =>
              Some (1%N, df, pushD (m + 1)%N 1 (pushD 0 2 db),
                    runs_push (SW_raw [1; 0]) 1 rest')
            | None => None
            end
          else None
        else None
      else None
    | _ => None
    end.

Lemma doCallsD_spec df db rtail h allowDefect hd df' db' rtail' :
  doCallsD df db rtail h allowDefect = Some (hd, df', db', rtail') ->
  (0 < N.to_nat hd)%nat /\ (N.to_nat hd <= N.to_nat h)%nat /\
  calls (N.to_nat hd)
    (denD df (denDRev db (runs_denote rtail)))
    (denD df' (denDRev db' (runs_denote rtail'))).
Proof.
  unfold doCallsD.
  destruct (N.eqb_spec h 0) as [-> | Hh0]; [discriminate |].
  rewrite <- (cleanTailZeros_spec rtail), <- (normImmTail_spec (cleanTailZeros rtail)).
  generalize (normImmTail (cleanTailZeros rtail)) as rt1; intros rt1.
  destruct rt1 as [|[w1 k1] rest1].
  - intros H; inversion H; subst hd df' db' rtail'; clear H.
    split; [lia |]. split; [lia |].
    rewrite denDRev_pushD. cbn [runs_denote].
    replace (N.to_nat (h * 2)%N) with (N.to_nat h * 2)%nat by lia.
    exact (calls_denD df (calls_denDRev db (calls_blank (N.to_nat h)))).
  - destruct w1 as [lw1 | | | ]; try discriminate.
    destruct rest1 as [|[w2 kd] rest]; try discriminate.
    destruct w2 as [| dn | | ]; try discriminate.
    destruct (beqListSym lw1 [1; 0]) eqn:Hlw1; [| discriminate].
    destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
    apply beqListSym_eq in Hlw1; subst lw1.
    destruct (N.eqb_spec dn 0) as [-> | Hdn0].
    + destruct (N.leb_spec 2 kd) as [Hkd2 | Hkd2].
      * destruct (popDBackOneAux df db) as [[[j df1] db1]|] eqn:Hpop; [| discriminate].
        intros H; inversion H; subst hd df' db' rtail'; clear H.
        destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
        change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
        set (avail := (kd / 2)%N) in *.
        set (hd0 := if N.leb h avail then h else avail) in *.
        assert (Hhd_pos : (0 < N.to_nat hd0)%nat).
        { subst hd0. destruct (N.leb_spec h avail); lia. }
        assert (Hhd_le_h : (N.to_nat hd0 <= N.to_nat h)%nat).
        { subst hd0. destruct (N.leb_spec h avail); lia. }
        assert (Hhd_le_av : (N.to_nat hd0 <= N.to_nat avail)%nat).
        { subst hd0. destruct (N.leb_spec h avail); lia. }
        split; [exact Hhd_pos |]. split; [exact Hhd_le_h |].
        rewrite (popDBackOneAux_spec df db j df1 db1 _ Hpop).
        rewrite !denDRev_pushD, !runs_push_spec.
        change (N.to_nat 0) with 0%nat.
        change (N.to_nat 1) with 1%nat.
        change (N.to_nat 2) with 2%nat.
        change (N.to_nat 3) with 3%nat.
        cbn [runs_denote sw_toList].
        rewrite !lpow_1.
        replace (N.to_nat kd) with ((1 + N.to_nat (hd0 - 1)%N) * 2 + N.to_nat (kd - hd0 * 2)%N)%nat by lia.
        rewrite lpow_add, Str_app_assoc.
        replace (N.to_nat (j + 1)%N) with (1 + N.to_nat j)%nat by lia.
        replace (N.to_nat hd0) with (1 + N.to_nat (hd0 - 1)%N)%nat by lia.
        exact (calls_denD df1 (calls_denDRev db1
          (calls_collision (N.to_nat (hd0 - 1)%N) (N.to_nat j)
            ((D_word 0)^^(N.to_nat (kd - hd0 * 2)%N) *> runs_denote rest)))).
      * destruct (if allowDefect then N.eqb kd 1 else false) eqn:Hdef; [| discriminate].
        destruct allowDefect; [| discriminate].
        apply N.eqb_eq in Hdef; subst kd.
        destruct (takeD rest) as [[m rest']|] eqn:Htd; [| discriminate].
        destruct (popDBackOneAux df db) as [[[j df1] db1]|] eqn:Hpop; [| discriminate].
        intros H; inversion H; subst hd df' db' rtail'; clear H.
        split; [lia |]. split; [lia |].
        rewrite (popDBackOneAux_spec df db j df1 db1 _ Hpop).
        rewrite !denDRev_pushD, !runs_push_spec.
        cbn [runs_denote sw_toList].
        change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
        rewrite !lpow_1, (takeD_spec rest m rest' Htd).
        replace (N.to_nat (j + 1)%N) with (1 + N.to_nat j)%nat by lia.
        replace (N.to_nat (m + 2)%N) with (2 + N.to_nat m)%nat by lia.
        apply calls_denD, calls_denDRev.
        eapply calls_S; [apply call_defect0 | constructor].
    + destruct (N.eqb_spec dn 1) as [-> | _]; [| discriminate].
      destruct (if allowDefect then N.ltb 0 kd else false) eqn:Hdef; [| discriminate].
      destruct allowDefect; [| discriminate].
      apply N.ltb_lt in Hdef.
      destruct (takeD (runs_push (SW_D 1) (kd - 1)%N rest)) as [[m rest']|] eqn:Htd; [| discriminate].
      intros H; inversion H; subst hd df' db' rtail'; clear H.
      split; [lia |]. split; [lia |].
      rewrite !denDRev_pushD, !runs_push_spec.
      pose proof (runs_push_spec (SW_D 1) (kd - 1)%N rest) as Hp.
      cbn [runs_denote sw_toList] in Hp |- *.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat in *.
      change (N.to_nat 2) with 2%nat.
      rewrite !lpow_1.
      replace (N.to_nat kd) with (1 + N.to_nat (kd - 1)%N)%nat by lia.
      cbn [Nat.add lpow]. rewrite ?app_nil_r, ?Str_app_assoc, <- Hp, (takeD_spec _ _ _ Htd).
      replace (N.to_nat (m + 1)%N) with (1 + N.to_nat m)%nat by lia.
      apply calls_denD, calls_denDRev.
      eapply calls_S; [apply call_defect1 | constructor].
Qed.

(* ========================================================================== *)
(* Section 4: FastState, stepFast, run_pow & Soundness                        *)
(* ========================================================================== *)

Inductive FMode :=
| MR | ML | MJ
| RAW (q : Q) (d : dir).

Record FastState := MkFastState {
  fs_L    : Runs;
  fs_R    : RTape;
  fs_mode : FMode
}.

Definition fs_denote (s : FastState) : Q * tape :=
  match fs_mode s with
  | MR => CfgR (runs_denote (fs_L s)) (rt_denote (fs_R s))
  | ML => CfgL (runs_denote (fs_L s)) (rt_denote (fs_R s))
  | MJ => CfgJ (runs_denote (fs_L s)) (rt_denote (fs_R s))
  | RAW q R => (runs_denote (fs_L s)) {{q}}> (rt_denote (fs_R s))
  | RAW q L => (runs_denote (fs_L s)) <{{q}} (rt_denote (fs_R s))
  end.

Definition rawStep (l : Runs) (rt : RTape) (q : Q) (d : dir) : option FastState :=
  let '(b, l', rt') :=
    match d with
    | L => let '(b, l') := runs_pop l in (b, l', rt)
    | R => let '(b, rt') := popBitRTape rt in (b, l, rt')
    end in
  match src_tm (q, b) with
  | Some (b', L, q') =>
    Some (MkFastState l' (MkRTape (runs_push (SW_raw [b']) 1 (r_raw rt')) (d_front rt') (d_back rt') (r_tail rt')) (RAW q' L))
  | Some (b', R, q') =>
    Some (MkFastState (runs_push (SW_raw [b']) 1 l') rt' (RAW q' R))
  | None => None
  end.

Lemma rawStep_spec l rt q d :
  match rawStep l rt q d with
  | Some s' => fs_denote (MkFastState l rt (RAW q d)) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt (RAW q d)))
  end.
Proof.
  destruct d; unfold rawStep; cbn [fs_denote fs_L fs_R fs_mode].
  - pose proof (runs_pop_spec l) as Hp.
    destruct (runs_pop l) as [b l']; cbn [fst snd] in Hp.
    rewrite Hp; cbn [hd tl].
    destruct (src_tm (q, b)) as [[[b' [|]] q']|] eqn:E.
    + cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_left E) | apply evstep_refl].
    + cbn [fs_denote fs_L fs_R fs_mode].
      rewrite runs_push_spec. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_right E) | apply evstep_refl].
    + apply halted_halts. exact E.
  - pose proof (popBitRTape_spec rt) as Hp.
    destruct (popBitRTape rt) as [b rt']; cbn [fst snd] in Hp.
    rewrite Hp; cbn [hd tl].
    destruct (src_tm (q, b)) as [[[b' [|]] q']|] eqn:E.
    + cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_left E) | apply evstep_refl].
    + cbn [fs_denote fs_L fs_R fs_mode].
      rewrite runs_push_spec. change (N.to_nat 1) with 1%nat.
      cbn [sw_toList lpow app Str_app].
      eapply evstep_step; [exact (step_right E) | apply evstep_refl].
    + apply halted_halts. exact E.
Qed.

Definition toRawAndStep (l : Runs) (rt : RTape) (m : FMode) : option FastState :=
  match m with
  | MR => rawStep l (MkRTape (runs_push (SW_raw [0; 1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) A R
  | ML => rawStep l (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) B L
  | MJ => rawStep l (MkRTape (runs_push (SW_raw [1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) C L
  | RAW q d => rawStep l rt q d
  end.

Lemma toRawAndStep_spec l rt m :
  match toRawAndStep l rt m with
  | Some s' => fs_denote (MkFastState l rt m) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt m))
  end.
Proof.
  destruct m as [| | | q d]; unfold toRawAndStep.
  - pose proof (rawStep_spec l (MkRTape (runs_push (SW_raw [0; 1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) A R) as H.
    replace (fs_denote (MkFastState l (MkRTape (runs_push (SW_raw [0; 1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) (RAW A R)))
      with (fs_denote (MkFastState l rt MR)) in H.
    + exact H.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgR, rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app]. reflexivity.
  - pose proof (rawStep_spec l (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) B L) as H.
    replace (fs_denote (MkFastState l (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) (RAW B L)))
      with (fs_denote (MkFastState l rt ML)) in H.
    + exact H.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgL, rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app]. reflexivity.
  - pose proof (rawStep_spec l (MkRTape (runs_push (SW_raw [1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) C L) as H.
    replace (fs_denote (MkFastState l (MkRTape (runs_push (SW_raw [1; 0; 0]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) (RAW C L)))
      with (fs_denote (MkFastState l rt MJ)) in H.
    + exact H.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgJ, rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app]. reflexivity.
  - apply rawStep_spec.
Qed.

Definition stepRawA0Scan (l : Runs) (rt : RTape) : option FastState :=
  match takeBitsRTape [0; 1; 1; 1] rt with
  | Some rt1 =>
    match r_raw rt1 with
    | [] =>
      if negb (hasD rt1) then
        let '(k, rtail') := take11 (r_tail rt1) in
        Some (MkFastState (runs_push (SW_raw [1; 0]) (k + 1)%N l) (MkRTape [(SW_raw [0; 1], 1%N)] [] [] rtail') (RAW A R))
      else
        Some (MkFastState (runs_push (SW_raw [1; 0]) 1 l) (MkRTape [(SW_raw [0; 1], 1%N)] (d_front rt1) (d_back rt1) (r_tail rt1)) (RAW A R))
    | _ :: _ =>
      let '(k, rr') := take11 (r_raw rt1) in
      Some (MkFastState (runs_push (SW_raw [1; 0]) (k + 1)%N l) (MkRTape (runs_push (SW_raw [0; 1]) 1 rr') (d_front rt1) (d_back rt1) (r_tail rt1)) (RAW A R))
    end
  | None =>
    match takeBitsRTape [0; 1; 0; 1; 0; 1] rt with
    | Some rt1 =>
      match r_raw rt1 with
      | [] =>
        if negb (hasD rt1) then
          let '(k, rtail') := take0101Strict (r_tail rt1) in
          Some (MkFastState (runs_push (SW_raw [1; 1; 0; 1]) (k + 1)%N l) (MkRTape [(SW_raw [0; 1], 1%N)] [] [] rtail') (RAW A R))
        else
          Some (MkFastState (runs_push (SW_raw [1; 1; 0; 1]) 1 l) (MkRTape [(SW_raw [0; 1], 1%N)] (d_front rt1) (d_back rt1) (r_tail rt1)) (RAW A R))
      | _ :: _ =>
        let '(k, rr') := take0101Strict (r_raw rt1) in
        Some (MkFastState (runs_push (SW_raw [1; 1; 0; 1]) (k + 1)%N l) (MkRTape (runs_push (SW_raw [0; 1]) 1 rr') (d_front rt1) (d_back rt1) (r_tail rt1)) (RAW A R))
      end
    | None => rawStep l rt A R
    end
  end.

Lemma stepRawA0Scan_spec l rt :
  match stepRawA0Scan l rt with
  | Some s' => fs_denote (MkFastState l rt (RAW A R)) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt (RAW A R)))
  end.
Proof.
  unfold stepRawA0Scan.
  destruct (takeBitsRTape [0; 1; 1; 1] rt) as [rt1|] eqn:H1.
  - pose proof (takeBitsRTape_spec [0; 1; 1; 1] rt rt1 H1) as Hrt.
    destruct rt1 as [[|x xs] df db rtail]; cbn [r_raw d_front d_back r_tail].
    + destruct (hasD (MkRTape [] df db rtail)) eqn:Hhd; cbn [negb].
      * cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug sw_toList].
        change (N.to_nat 1) with 1%nat. cbn [lpow app Str_app].
        exact (scanR (runs_denote l) (denD df (denDRev db (runs_denote rtail))) 1%nat).
      * destruct (hasD_false_nil [] df db rtail Hhd) as [-> ->].
        pose proof (take11_spec rtail 0inf) as Ht11.
        rewrite <- !denote_eq_plug_0inf in Ht11.
        destruct (take11 rtail) as [k rtail']; cbn [fst snd] in Ht11.
        cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev sw_toList].
        rewrite Ht11.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat (k + 1)%N) with (S (N.to_nat k)) by lia.
        exact (scanR (runs_denote l) (runs_denote rtail') (S (N.to_nat k))).
    + pose proof (take11_spec (x :: xs) (denD df (denDRev db (runs_denote rtail)))) as Ht11.
      destruct (take11 (x :: xs)) as [k rr']; cbn [fst snd] in Ht11.
      cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail sw_toList].
      rewrite Ht11, push_plug. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (N.to_nat (k + 1)%N) with (S (N.to_nat k)) by lia.
      exact (scanR (runs_denote l) (plug rr' (denD df (denDRev db (runs_denote rtail)))) (S (N.to_nat k))).
  - destruct (takeBitsRTape [0; 1; 0; 1; 0; 1] rt) as [rt1|] eqn:H2; [| apply rawStep_spec].
    pose proof (takeBitsRTape_spec [0; 1; 0; 1; 0; 1] rt rt1 H2) as Hrt.
    destruct rt1 as [[|x xs] df db rtail]; cbn [r_raw d_front d_back r_tail].
    + destruct (hasD (MkRTape [] df db rtail)) eqn:Hhd; cbn [negb].
      * cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug sw_toList].
        change (N.to_nat 1) with 1%nat. cbn [lpow app Str_app].
        exact (scanPair (runs_denote l) (denD df (denDRev db (runs_denote rtail))) 1%nat).
      * destruct (hasD_false_nil [] df db rtail Hhd) as [-> ->].
        pose proof (take0101Strict_spec rtail 0inf) as Ht.
        rewrite <- !denote_eq_plug_0inf in Ht.
        destruct (take0101Strict rtail) as [k rtail']; cbn [fst snd] in Ht.
        cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev sw_toList].
        rewrite Ht.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat (k + 1)%N) with (S (N.to_nat k)) by lia.
        exact (scanPair (runs_denote l) (runs_denote rtail') (S (N.to_nat k))).
    + pose proof (take0101Strict_spec (x :: xs) (denD df (denDRev db (runs_denote rtail)))) as Ht.
      destruct (take0101Strict (x :: xs)) as [k rr']; cbn [fst snd] in Ht.
      cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt, runs_push_spec.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail sw_toList].
      rewrite Ht, push_plug. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (N.to_nat (k + 1)%N) with (S (N.to_nat k)) by lia.
      exact (scanPair (runs_denote l) (plug rr' (denD df (denDRev db (runs_denote rtail)))) (S (N.to_nat k))).
Qed.

Definition stepRaw (l : Runs) (rt : RTape) (q : Q) (d : dir) : option FastState :=
  match q, d with
  | A, R =>
    match takeBitsRTape [0; 1; 0; 0] rt with
    | Some rt' => Some (MkFastState l rt' MR)
    | None =>
      match r_raw rt with
      | (SW_raw w, k) :: rr' =>
        if beqListSym w [1] then
          Some (MkFastState (runs_push (SW_raw [1]) k l) (MkRTape rr' (d_front rt) (d_back rt) (r_tail rt)) (RAW A R))
        else stepRawA0Scan l rt
      | [] =>
        if negb (hasD rt) then
          match r_tail rt with
          | (SW_raw w, k) :: rtail' =>
            if beqListSym w [1] then
              Some (MkFastState (runs_push (SW_raw [1]) k l) (MkRTape [] [] [] rtail') (RAW A R))
            else stepRawA0Scan l rt
          | _ => stepRawA0Scan l rt
          end
        else stepRawA0Scan l rt
      | _ => stepRawA0Scan l rt
      end
    end
  | B, L =>
    match takeBitsRTape [1] rt with
    | Some rt' => Some (MkFastState l rt' ML)
    | None =>
      let '(k, l') := take01 l in
      if N.eqb k 0 then rawStep l rt B L
      else Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1]) k (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) (RAW B L))
    end
  | C, L =>
    match takeBitsRTape [1; 0; 0] rt with
    | Some rt' => Some (MkFastState l rt' MJ)
    | None =>
      let '(k, l') := take10 l in
      if N.eqb k 0 then rawStep l rt C L
      else Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1]) k (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) (RAW C L))
    end
  | _, _ => rawStep l rt q d
  end.

Lemma stepRaw_spec l rt q d :
  match stepRaw l rt q d with
  | Some s' => fs_denote (MkFastState l rt (RAW q d)) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt (RAW q d)))
  end.
Proof.
  destruct q, d; try apply rawStep_spec.
  - (* A, R *)
    cbn [stepRaw].
    destruct (takeBitsRTape [0; 1; 0; 0] rt) as [rt'|] eqn:Hmr.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgR.
      rewrite (takeBitsRTape_spec _ _ _ Hmr). apply evstep_refl.
    + destruct rt as [[|[w k] rr'] df db rtail]; cbn [r_raw d_front d_back r_tail].
      * destruct (hasD (MkRTape [] df db rtail)) eqn:Hhd; cbn [negb]; [apply stepRawA0Scan_spec |].
        destruct (hasD_false_nil [] df db rtail Hhd) as [-> ->].
        destruct rtail as [|[w k] rtail']; [apply stepRawA0Scan_spec |].
        destruct w as [lw | | | ]; [| apply stepRawA0Scan_spec | apply stepRawA0Scan_spec | apply stepRawA0Scan_spec].
        destruct (beqListSym lw [1]) eqn:Hw1; [| apply stepRawA0Scan_spec].
        cbn [fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev runs_denote sw_toList].
        rewrite (beqListSym_eq _ _ Hw1), runs_push_spec. cbn [sw_toList].
        apply ones.
      * destruct w as [lw | | | ]; [| apply stepRawA0Scan_spec | apply stepRawA0Scan_spec | apply stepRawA0Scan_spec].
        destruct (beqListSym lw [1]) eqn:Hw1; [| apply stepRawA0Scan_spec].
        cbn [fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug sw_toList].
        rewrite (beqListSym_eq _ _ Hw1), runs_push_spec. cbn [sw_toList].
        apply ones.
  - (* B, L *)
    cbn [stepRaw].
    destruct (takeBitsRTape [1] rt) as [rt'|] eqn:Hml.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgL.
      rewrite (takeBitsRTape_spec _ _ _ Hml). apply evstep_refl.
    + pose proof (take01_spec l) as Ht.
      destruct (take01 l) as [k l']; cbn [fst snd] in Ht.
      destruct (N.eqb_spec k 0) as [-> | _]; [apply rawStep_spec |].
      cbn [fs_denote fs_L fs_R fs_mode]. rewrite Ht.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. cbn [sw_toList]. apply scanB.
  - (* C, L *)
    cbn [stepRaw].
    destruct (takeBitsRTape [1; 0; 0] rt) as [rt'|] eqn:Hmj.
    + cbn [fs_denote fs_L fs_R fs_mode]. unfold CfgJ.
      rewrite (takeBitsRTape_spec _ _ _ Hmj). apply evstep_refl.
    + pose proof (take10_spec l) as Ht.
      destruct (take10 l) as [k l']; cbn [fst snd] in Ht.
      destruct (N.eqb_spec k 0) as [-> | _]; [apply rawStep_spec |].
      cbn [fs_denote fs_L fs_R fs_mode]. rewrite Ht.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite push_plug. cbn [sw_toList]. apply scanC.
Qed.

Definition stepMR_D (l : Runs) (df db : Digits) (rtail : Runs) : FastState :=
  let doOne :=
    match doCallsD df db rtail 1 true with
    | Some (hd, df', db', rtail') =>
      if N.eqb hd 1 then MkFastState l (MkRTape [] df' db' rtail') ML
      else MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    | None => MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    end in
  match l with
  | (SW_raw _, _) :: _ =>
    let '(b1, l1) := take10 l in
    if N.eqb b1 0 then doOne
    else
      let '(c111, l2) := take111 l1 in
      if N.eqb c111 0 then doOne
      else
        match doCallsD df db rtail (c111 + 1)%N true with
        | Some (hd, df', db', rtail') =>
          let rem := (c111 - (hd - 1))%N in
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) rem l2) in
          MkFastState l' (MkRTape [] df' db' rtail') ML
        | None => MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
        end
  | _ => doOne
  end.

Lemma stepMR_D_spec l df db rtail :
  fs_denote (MkFastState l (MkRTape [] df db rtail) MR) -->*
  fs_denote (stepMR_D l df db rtail).
Proof.
  unfold stepMR_D.
  set (doOne :=
    match doCallsD df db rtail 1 true with
    | Some (hd, df', db', rtail') =>
      if N.eqb hd 1 then MkFastState l (MkRTape [] df' db' rtail') ML
      else MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    | None => MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    end).
  assert (HdoOne : fs_denote (MkFastState l (MkRTape [] df db rtail) MR) -->* fs_denote doOne).
  { subst doOne.
    destruct (doCallsD df db rtail 1 true) as [[[[hd df'] db'] rtail']|] eqn:Hdc.
    - destruct (N.eqb_spec hd 1) as [-> | _].
      + destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [_ [_ Hc]].
        change (N.to_nat 1) with 1%nat in Hc.
        inversion Hc as [|m r0 u t Hcall Hz]; subst.
        inversion Hz; subst.
        exact (Hcall (runs_denote l)).
      + apply sweepRight_spec.
    - apply sweepRight_spec. }
  destruct l as [|[w k] rest]; [exact HdoOne |].
  destruct w as [lw | | | ]; try exact HdoOne.
  pose proof (take10_spec ((SW_raw lw, k) :: rest)) as H10.
  destruct (take10 ((SW_raw lw, k) :: rest)) as [b1 l1]; cbn [fst snd] in H10.
  destruct (N.eqb_spec b1 0) as [-> | Hb1]; [exact HdoOne |].
  pose proof (take111_spec l1 0inf) as H111.
  rewrite <- !denote_eq_plug_0inf in H111.
  destruct (take111 l1) as [c111 l2]; cbn [fst snd] in H111.
  destruct (N.eqb_spec c111 0) as [-> | Hc0]; [exact HdoOne |].
  destruct (doCallsD df db rtail (c111 + 1)%N true) as [[[[hd df'] db'] rtail']|] eqn:Hdc;
    [| apply sweepRight_spec].
  destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hpos [Hle Hcalls]].
  cbn [fs_denote fs_L fs_R fs_mode].
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
  rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
  replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
  replace (N.to_nat c111) with ((N.to_nat hd - 1) + N.to_nat (c111 - (hd - 1))%N)%nat at 1 by lia.
  rewrite <- (lpow_Str_add [1; 1; 1]).
  exact (loopR_to_L' Hpos Hcalls
    ([1; 1; 1]^^(N.to_nat (c111 - (hd - 1))%N) *> runs_denote l2)
    (N.to_nat (b1 - 1)%N)).
Qed.

Definition stepMR_imm (l rt1 : Runs) : option FastState :=
  match takeD rt1 with
  | None =>
    let '(k0, rt2) := take10 rt1 in
    let k10 := (1 + k0)%N in
    if (if N.leb 2 k10 then N.eqb (k10 mod 2) 0 else false) then
      match takeD rt2 with
      | Some (dn, rt3) =>
        let kp := (k10 / 2)%N in
        let l' := runs_push (SW_raw [1; 0]) dn (runs_push (SW_raw [1; 1; 0; 1]) kp (runs_push (SW_S 0) 1 l)) in
        Some (MkFastState l' (MkRTape [] [] [] rt3) MR)
      | None => None
      end
    else None
  | Some (a, rt2) =>
    match takeD rt2 with
    | Some (m, rt3) =>
      if (if N.leb 2 a then N.eqb m a else false) then
        let '(tot, rt4) :=
          match rt3 with
          | (SW_D a', kex) :: rt3' => if N.eqb a' a then ((2 + kex)%N, rt3') else (2%N, rt3)
          | _ => (2%N, rt3)
          end in
        let kp := (tot / 2)%N in
        let n := (a - 2)%N in
        let rt5 := if N.eqb (tot mod 2) 1 then runs_push (SW_D a) 1 rt4 else rt4 in
        Some (MkFastState (runs_push (SW_PL n) kp l) (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1 rt5)) MR)
      else if N.eqb a 0 then
        Some (MkFastState l (MkRTape [] [((m + 2)%N, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 rt3)) MJ)
      else if N.eqb a 1 then
        Some (MkFastState l (MkRTape [] (pushD 0 2 [((m + 1)%N, 1%N)]) [] (runs_push (SW_raw [1; 0]) 1 rt3)) ML)
      else
        let l' := runs_push (SW_raw [1; 0]) (m + 2)%N (runs_push (SW_raw [1; 1]) (a - 2)%N (runs_push (SW_S 0) 2 l)) in
        Some (MkFastState l' (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1 rt3)) MR)
    | None =>
      match runs_remove [0; 0] rt2 with
      | Some rt3 =>
        if N.eqb a 0 then
          Some (MkFastState (runs_push (SW_raw [1; 0; 0; 1]) 1 (runs_push (SW_S 0) 1 l)) (MkRTape [] [] [] rt3) MR)
        else
          let l' := runs_push (SW_raw [1; 0]) 1 (runs_push (SW_raw [1; 1]) (a - 1)%N (runs_push (SW_raw [1]) 1 (runs_push (SW_S 0) 2 l))) in
          Some (MkFastState l' (MkRTape [] [] [] rt3) MR)
      | None =>
        let '(c1, rt3) := takeOnes rt2 in
        if N.eqb (c1 mod 2) 1 then
          match runs_remove [0] rt3 with
          | Some rt4 =>
            let mv := (c1 / 2)%N in
            if N.eqb a 0 then
              Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_raw [1; 1; 1; 1]) 1 (runs_push (SW_D mv) 1 (runs_push (SW_raw [1]) 1 rt4)))) MJ)
            else if N.eqb a 1 then
              Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_D 0) 2 (runs_push (SW_D (mv + 1)%N) 1 (runs_push (SW_raw [1]) 1 rt4)))) ML)
            else
              let l' := runs_push (SW_raw [1; 0]) (mv + 2)%N (runs_push (SW_raw [1; 1]) (a - 2)%N (runs_push (SW_S 0) 2 l)) in
              Some (MkFastState l' (MkRTape [] [] [] (runs_push (SW_raw [1]) 1 rt4)) MR)
          | None => None
          end
        else None
      end
    end
  end.

Lemma stepMR_imm_pair_helper l a rt3 tot rt4 :
  (2 <= a)%N ->
  D_word (N.to_nat a) *> D_word (N.to_nat a) *> runs_denote rt3 =
    (D_word (N.to_nat a))^^(N.to_nat tot) *> runs_denote rt4 ->
  CfgR (runs_denote l) ([1; 0] *> D_word (N.to_nat a) *> D_word (N.to_nat a) *> runs_denote rt3) -->*
  fs_denote (MkFastState (runs_push (SW_PL (a - 2)%N) (tot / 2)%N l)
    (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1
      (if N.eqb (tot mod 2) 1 then runs_push (SW_D a) 1 rt4 else rt4))) MR).
Proof.
  intros Ha2 Htr. rewrite Htr.
  cbn [fs_denote fs_L fs_R fs_mode].
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
  rewrite !runs_push_spec. cbn [sw_toList].
  change (N.to_nat 1) with 1%nat. rewrite lpow_1.
  destruct (N_div_mod_nat tot 2 ltac:(lia)) as [Hdiv Hmod].
  change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
  assert (Ha : (2 + N.to_nat (a - 2)%N = N.to_nat a)%nat) by lia.
  destruct (N.eqb_spec (tot mod 2) 1) as [Hm1 | Hm1].
  - rewrite runs_push_spec. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    replace (N.to_nat tot) with (N.to_nat (tot / 2)%N * 2 + 1)%nat by lia.
    rewrite lpow_plus_r, Str_app_assoc, <- Ha.
    apply pairsR.
  - replace (N.to_nat tot) with (N.to_nat (tot / 2)%N * 2)%nat by lia.
    rewrite <- Ha. apply pairsR.
Qed.

Lemma stepMR_imm_spec l rt1 s' :
  stepMR_imm l rt1 = Some s' ->
  CfgR (runs_denote l) ([1; 0] *> runs_denote rt1) -->* fs_denote s'.
Proof.
  unfold stepMR_imm.
  destruct (takeD rt1) as [[a rt2]|] eqn:Htd1.
  - rewrite (takeD_spec _ _ _ Htd1).
    destruct (takeD rt2) as [[m rt3]|] eqn:Htd2.
    + rewrite (takeD_spec _ _ _ Htd2).
      destruct (if N.leb 2 a then N.eqb m a else false) eqn:Hpair.
      * destruct (N.leb_spec 2 a) as [Ha2 | _]; [| discriminate].
        apply N.eqb_eq in Hpair; subst m.
        destruct rt3 as [|[w3 kex] rt3'].
        { intros H; inversion H; subst; clear H.
          apply (stepMR_imm_pair_helper l a [] 2%N []); [exact Ha2 |].
          change (N.to_nat 2) with 2%nat. cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc. reflexivity. }
        destruct w3 as [| a' | | ].
        2:{ destruct (N.eqb_spec a' a) as [<- | _].
            - intros H; inversion H; subst; clear H.
              apply (stepMR_imm_pair_helper l a' ((SW_D a', kex) :: rt3') (2 + kex)%N rt3'); [exact Ha2 |].
              cbn [runs_denote sw_toList].
              replace (N.to_nat (2 + kex)%N) with (2 + N.to_nat kex)%nat by lia.
              cbn [Nat.add lpow]. rewrite ?Str_app_assoc. reflexivity.
            - intros H; inversion H; subst; clear H.
              apply (stepMR_imm_pair_helper l a ((SW_D a', kex) :: rt3') 2%N ((SW_D a', kex) :: rt3')); [exact Ha2 |].
              change (N.to_nat 2) with 2%nat. cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc. reflexivity. }
        all: intros H; inversion H; subst; clear H;
             apply (stepMR_imm_pair_helper l a _ 2%N _); [exact Ha2 |];
             change (N.to_nat 2) with 2%nat; cbn [lpow]; rewrite ?app_nil_r, Str_app_assoc; reflexivity.
      * destruct (N.eqb_spec a 0) as [-> | Ha0].
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite runs_push_spec. change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          cbn [sw_toList]. rewrite !lpow_1.
          replace (N.to_nat (m + 2)%N) with (2 + N.to_nat m)%nat by lia.
          apply rule_defect0D. }
        destruct (N.eqb_spec a 1) as [-> | Ha1].
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denDRev].
          rewrite denD_pushD, runs_push_spec. cbn [denD sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat (m + 1)%N) with (1 + N.to_nat m)%nat by lia.
          apply rule_defect1D. }
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat a) with (2 + N.to_nat (a - 2)%N)%nat by lia.
          replace (N.to_nat (m + 2)%N) with (2 + N.to_nat m)%nat by lia.
          apply rule_defect2D. }
    + destruct (runs_remove [0; 0] rt2) as [rt3|] eqn:Hr00.
      * rewrite (runs_remove_spec _ _ _ Hr00).
        destruct (N.eqb_spec a 0) as [-> | Ha0].
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          rewrite !lpow_1. apply rule_defect_blank0. }
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat a) with (1 + N.to_nat (a - 1)%N)%nat by lia.
          apply rule_defect_blankS. }
      * pose proof (takeOnes_spec rt2 0inf) as H1.
        rewrite <- !denote_eq_plug_0inf in H1.
        destruct (takeOnes rt2) as [c1 rt3]; cbn [fst snd] in H1.
        destruct (N.eqb_spec (c1 mod 2) 1) as [Hm1 | _]; [| discriminate].
        destruct (runs_remove [0] rt3) as [rt4|] eqn:Hr0; [| discriminate].
        destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv _].
        change (N.to_nat 2) with 2%nat in Hdiv.
        assert (Hrt2 : runs_denote rt2 = [1] *> [1; 1]^^(N.to_nat (c1 / 2)%N) *> [0] *> runs_denote rt4).
        { rewrite H1, (runs_remove_spec _ _ _ Hr0).
          replace (N.to_nat c1) with (1 + 2 * N.to_nat (c1 / 2)%N)%nat by lia.
          rewrite lpow_add, one_pow_two_mul. cbn [lpow app Str_app]. rewrite ?Str_app_assoc. reflexivity. }
        rewrite Hrt2.
        destruct (N.eqb_spec a 0) as [-> | Ha0].
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          rewrite !lpow_1. apply rule_defect0. }
        destruct (N.eqb_spec a 1) as [-> | Ha1].
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat (c1 / 2 + 1)%N) with (1 + N.to_nat (c1 / 2)%N)%nat by lia.
          apply rule_defect1. }
        { intros H; inversion H; subst; clear H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat a) with (2 + N.to_nat (a - 2)%N)%nat by lia.
          replace (N.to_nat (c1 / 2 + 2)%N) with (2 + N.to_nat (c1 / 2)%N)%nat by lia.
          apply rule_defect2. }
  - pose proof (take10_spec rt1) as H10.
    destruct (take10 rt1) as [k0 rt2]; cbn [fst snd] in H10.
    destruct (if N.leb 2 (1 + k0)%N then N.eqb ((1 + k0) mod 2)%N 0 else false) eqn:Hcond; [| discriminate].
    destruct (N.leb 2 (1 + k0)%N); [| discriminate].
    apply N.eqb_eq in Hcond.
    destruct (takeD rt2) as [[dn rt3]|] eqn:Htd2; [| discriminate].
    intros H; inversion H; subst; clear H.
    destruct (N_div_mod_nat (1 + k0)%N 2 ltac:(lia)) as [Hdiv _].
    change (N.to_nat 2) with 2%nat in Hdiv.
    cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
    rewrite H10, (takeD_spec _ _ _ Htd2), !runs_push_spec. cbn [sw_toList].
    change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    change ([1; 0] *> [1; 0]^^(N.to_nat k0) *> D_word (N.to_nat dn) *> runs_denote rt3)
      with ([1; 0]^^(1 + N.to_nat k0) *> D_word (N.to_nat dn) *> runs_denote rt3).
    replace (1 + N.to_nat k0)%nat with (N.to_nat ((1 + k0) / 2)%N * 2)%nat by lia.
    apply rule_paired.
Qed.

Definition stepMR_tailNoImm (l rt : Runs) : option FastState :=
  match runs_remove [0; 0; 0] rt with
  | Some rt1 => Some (MkFastState l (MkRTape [] [(0%N, 2%N)] [] rt1) ML)
  | None =>
    let '(c1, rt1) := takeOnes rt in
    if N.eqb c1 0 then None
    else if N.eqb (c1 mod 2) 0 then
      match runs_remove [0; 0] rt1 with
      | Some rt2 =>
        Some (MkFastState l (MkRTape [] [((c1 / 2)%N, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 rt2)) ML)
      | None => None
      end
    else
      match runs_remove [0; 0] rt1 with
      | Some rt2 =>
        Some (MkFastState (runs_push (SW_S (c1 / 2)%N) 1 l) (MkRTape [] [] [] rt2) MR)
      | None => None
      end
  end.

Lemma stepMR_tailNoImm_spec l rt s' :
  stepMR_tailNoImm l rt = Some s' ->
  CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'.
Proof.
  unfold stepMR_tailNoImm.
  destruct (runs_remove [0; 0; 0] rt) as [rt1|] eqn:Hr0.
  - intros H; inversion H; subst; clear H.
    rewrite (runs_remove_spec _ _ _ Hr0).
    cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
    change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
    apply rule_blank.
  - pose proof (takeOnes_spec rt 0inf) as H1.
    rewrite <- !denote_eq_plug_0inf in H1.
    destruct (takeOnes rt) as [c1 rt1]; cbn [fst snd] in H1.
    destruct (N.eqb_spec c1 0) as [-> | Hc0]; [discriminate |].
    destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv Hmod].
    change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
    destruct (N.eqb_spec (c1 mod 2) 0) as [Heven | Hodd].
    + destruct (runs_remove [0; 0] rt1) as [rt2|] eqn:Hr00; [| discriminate].
      intros H; inversion H; subst; clear H.
      cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite H1, (runs_remove_spec _ _ _ Hr00), runs_push_spec. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
      replace (N.to_nat c1) with (2 * (1 + (N.to_nat (c1 / 2)%N - 1)))%nat by lia.
      rewrite one_pow_two_mul.
      replace (N.to_nat (c1 / 2)%N) with (1 + (N.to_nat (c1 / 2)%N - 1))%nat at 2 by lia.
      apply rule_even.
    + destruct (runs_remove [0; 0] rt1) as [rt2|] eqn:Hr00; [| discriminate].
      intros H; inversion H; subst; clear H.
      cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite H1, (runs_remove_spec _ _ _ Hr00), runs_push_spec. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (N.to_nat c1) with (2 * N.to_nat (c1 / 2)%N + 1)%nat by lia.
      rewrite <- D_word_ones.
      apply rule_right.
Qed.

Definition stepMR_tailRest (l rt : Runs) : option FastState :=
  match runs_remove [1; 0] rt with
  | Some rt1 =>
    match stepMR_imm l rt1 with
    | Some s' => Some s'
    | None => stepMR_tailNoImm l rt
    end
  | None => stepMR_tailNoImm l rt
  end.

Lemma stepMR_tailRest_spec l rt s' :
  stepMR_tailRest l rt = Some s' ->
  CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'.
Proof.
  unfold stepMR_tailRest.
  destruct (runs_remove [1; 0] rt) as [rt1|] eqn:Hr; [| apply stepMR_tailNoImm_spec].
  destruct (stepMR_imm l rt1) as [st1|] eqn:Him; [| apply stepMR_tailNoImm_spec].
  intros H; inversion H; subst; clear H.
  rewrite (runs_remove_spec _ _ _ Hr).
  exact (stepMR_imm_spec l rt1 s' Him).
Qed.

Definition stepMR_tail (l rt : Runs) : option FastState :=
  match rt with
  | [] => Some (MkFastState l (MkRTape [] [(0%N, 2%N)] [] []) ML)
  | (SW_raw w1, k1) :: (SW_D nd, kd) :: rest =>
    if (if beqListSym w1 [1; 0] then if N.eqb k1 1 then if N.leb 2 nd then N.leb 2 kd else false else false else false) then
      let kp := (kd / 2)%N in
      let n := (nd - 2)%N in
      let rest' := if N.eqb (kd mod 2) 1 then runs_push (SW_D nd) 1 rest else rest in
      Some (MkFastState (runs_push (SW_PL n) kp l) (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1 rest')) MR)
    else stepMR_tailRest l rt
  | _ => stepMR_tailRest l rt
  end.

Lemma stepMR_tail_spec l rt s' :
  stepMR_tail l rt = Some s' ->
  CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'.
Proof.
  destruct rt as [|[w1 k1] rest1].
  - cbn [stepMR_tail]. intros H; inversion H; subst; clear H.
    cbn [fs_denote fs_L fs_R fs_mode runs_denote].
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev runs_denote].
    change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
    apply rule_emptyR.
  - destruct w1 as [lw1 | | | ]; try apply stepMR_tailRest_spec.
    destruct rest1 as [|[w2 kd] rest]; try apply stepMR_tailRest_spec.
    destruct w2 as [| nd | | ]; try apply stepMR_tailRest_spec.
    cbn [stepMR_tail].
    destruct (if beqListSym lw1 [1; 0] then if N.eqb k1 1 then if N.leb 2 nd then N.leb 2 kd else false else false else false) eqn:Hcond;
      [| apply stepMR_tailRest_spec].
    destruct (beqListSym lw1 [1; 0]) eqn:Hlw1; [| discriminate].
    destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
    destruct (N.leb_spec 2 nd) as [Hnd2 | _]; [| discriminate].
    destruct (N.leb_spec 2 kd) as [Hkd2 | _]; [| discriminate].
    apply beqListSym_eq in Hlw1; subst lw1.
    intros H; inversion H; subst; clear H.
    cbn [fs_denote fs_L fs_R fs_mode runs_denote sw_toList].
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
    rewrite !runs_push_spec. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
    destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
    change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
    assert (Hnd : (2 + N.to_nat (nd - 2)%N = N.to_nat nd)%nat) by lia.
    destruct (N.eqb_spec (kd mod 2) 1) as [Hm1 | Hm1].
    + rewrite runs_push_spec. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2 + 1)%nat by lia.
      rewrite lpow_plus_r, Str_app_assoc, <- Hnd.
      apply pairsR.
    + replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2)%nat by lia.
      rewrite <- Hnd. apply pairsR.
Qed.

Definition stepMR (l : Runs) (rt : RTape) : option FastState :=
  let flush_step rt0 :=
    let rt1 := flushAllToTail rt0 in
    match stepMR_tail l (r_tail rt1) with
    | Some s' => Some s'
    | None => toRawAndStep l rt1 MR
    end in
  match r_raw rt with
  | [] =>
    if hasD rt then Some (stepMR_D l (d_front rt) (d_back rt) (r_tail rt))
    else
      match stepMR_tail l (r_tail rt) with
      | Some s' => Some s'
      | None => toRawAndStep l rt MR
      end
  | [(SW_raw w, k)] =>
    if (if beqListSym w [1] then N.eqb k 1 else false) then
      match popDFrontOneAux (d_front rt) (d_back rt) with
      | Some (n, df', db') =>
        let rtail' := runs_push (SW_raw [1; 0]) 1 (flushDToTail df' db' (r_tail rt)) in
        Some (MkFastState l (MkRTape [] [((n + 1)%N, 1%N)] [] rtail') ML)
      | None => flush_step rt
      end
    else flush_step rt
  | _ => flush_step rt
  end.

Lemma flush_step_MR_spec l rt :
  let rt1 := flushAllToTail rt in
  match match stepMR_tail l (r_tail rt1) with
        | Some s' => Some s'
        | None => toRawAndStep l rt1 MR
        end with
  | Some s' => fs_denote (MkFastState l rt MR) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MR))
  end.
Proof.
  cbv zeta.
  assert (Hfeq : fs_denote (MkFastState l rt MR) = fs_denote (MkFastState l (flushAllToTail rt) MR)).
  { cbn [fs_denote fs_L fs_R fs_mode]. rewrite flushAllToTail_spec. reflexivity. }
  rewrite Hfeq.
  destruct (stepMR_tail l (r_tail (flushAllToTail rt))) as [s'|] eqn:Hst.
  - pose proof (stepMR_tail_spec l (r_tail (flushAllToTail rt)) s' Hst) as H.
    cbn [fs_denote fs_L fs_R fs_mode].
    unfold flushAllToTail at 1; unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
    exact H.
  - apply toRawAndStep_spec.
Qed.

Lemma stepMR_spec l rt :
  match stepMR l rt with
  | Some s' => fs_denote (MkFastState l rt MR) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MR))
  end.
Proof.
  unfold stepMR.
  destruct rt as [rr df db rtail]; cbn [r_raw d_front d_back r_tail].
  destruct rr as [|[w k] rr'].
  - destruct (hasD (MkRTape [] df db rtail)) eqn:Hhd.
    + apply stepMR_D_spec.
    + destruct (hasD_false_nil [] df db rtail Hhd) as [-> ->].
      destruct (stepMR_tail l rtail) as [s'|] eqn:Hst; [| apply toRawAndStep_spec].
      cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      exact (stepMR_tail_spec l rtail s' Hst).
  - destruct w as [lw | | | ];
      [| apply flush_step_MR_spec | apply flush_step_MR_spec | apply flush_step_MR_spec].
    destruct rr' as [|x xs]; [| apply flush_step_MR_spec].
    destruct (if beqListSym lw [1] then N.eqb k 1 else false) eqn:Hc;
      [| apply flush_step_MR_spec].
    destruct (beqListSym lw [1]) eqn:Hlw; [| discriminate].
    apply N.eqb_eq in Hc; subst k.
    apply beqListSym_eq in Hlw; subst lw.
    destruct (popDFrontOneAux df db) as [[[n df'] db']|] eqn:Hp;
      [| apply flush_step_MR_spec].
    cbn [fs_denote fs_L fs_R fs_mode].
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev sw_toList].
    rewrite (popDFrontOneAux_spec df db n df' db' _ Hp).
    rewrite runs_push_spec, flushDToTail_spec. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite !lpow_1, one_D_word.
    replace (N.to_nat (n + 1)%N) with (1 + N.to_nat n)%nat by lia.
    apply rule_even.
Qed.

Lemma flush_if_raw_denote rt :
  let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
  rt_denote rt = denD (d_front rt1) (denDRev (d_back rt1) (runs_denote (r_tail rt1))).
Proof.
  destruct (r_raw rt) eqn:Hrr.
  - unfold rt_denote; rewrite Hrr; reflexivity.
  - rewrite <- flushAllToTail_spec; reflexivity.
Qed.

Definition availPLCount (cnt step_h : N) (rt1 : RTape) : N :=
  match r_tail rt1 with
  | [] => cnt
  | _ =>
    match normImmTail (cleanTailZeros (r_tail rt1)) with
    | (SW_raw w, k1) :: (SW_D dn, k0) :: _ =>
      if (if beqListSym w [1; 0] then if N.eqb k1 1 then if N.eqb dn 0 then hasD rt1 else false else false else false) then
        let av := ((k0 / 2) / step_h)%N in
        if N.leb cnt av then cnt else av
      else 0%N
    | _ => 0%N
    end
  end.

Definition unfoldPL1 (pl_n cnt : N) (lrest : Runs) : Runs :=
  runs_push (SW_raw [1; 0]) (pl_n + 4)%N
    (runs_push (SW_raw [1; 1]) pl_n
      (runs_push (SW_S 0) 2 (runs_push (SW_PL pl_n) cnt lrest))).

Lemma unfoldPL1_spec pl_n cnt lrest :
  runs_denote (unfoldPL1 pl_n cnt lrest) =
  runs_denote ((SW_PL pl_n, (cnt + 1)%N) :: lrest).
Proof.
  unfold unfoldPL1.
  rewrite !runs_push_spec.
  cbn [runs_denote sw_toList].
  change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
  replace (N.to_nat (cnt + 1)%N) with (S (N.to_nat cnt)) by lia.
  replace (N.to_nat (pl_n + 4)%N) with (N.to_nat pl_n + 4)%nat by lia.
  cbn [lpow]. unfold PL_word.
  rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
Qed.

Definition stepML_PL (pl_n cnt : N) (lrest : Runs) (rt : RTape) : FastState :=
  let fallback := MkFastState (unfoldPL1 pl_n cnt lrest) rt ML in
  if (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) then
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    let n := ((pl_n - 1) / 3)%N in
    let step_h := (1 + n * 2)%N in
    let cnt1 := (cnt + 1)%N in
    let mc := availPLCount cnt1 step_h rt1 in
    if (if N.eqb mc 0 then true else N.ltb cnt1 mc) then fallback
    else
      let req := (mc * step_h)%N in
      match doCallsD (d_front rt1) (d_back rt1) (r_tail rt1) req false with
      | Some (hd, df', db', rtail') =>
        if N.eqb hd req then
          let df'' := pushD (6 + n * 3)%N (mc - 1)%N (pushD (5 + n * 3)%N 1 df') in
          MkFastState (runs_push (SW_PL pl_n) (cnt1 - mc)%N lrest) (MkRTape [] df'' db' rtail') MJ
        else fallback
      | None => fallback
      end
  else fallback.

Lemma stepML_PL_spec pl_n cnt lrest rt :
  fs_denote (MkFastState ((SW_PL pl_n, (cnt + 1)%N) :: lrest) rt ML) -->*
  fs_denote (stepML_PL pl_n cnt lrest rt).
Proof.
  unfold stepML_PL.
  assert (Hfb : fs_denote (MkFastState ((SW_PL pl_n, (cnt + 1)%N) :: lrest) rt ML) -->*
                fs_denote (MkFastState (unfoldPL1 pl_n cnt lrest) rt ML)).
  { cbn [fs_denote fs_L fs_R fs_mode]. rewrite unfoldPL1_spec. apply evstep_refl. }
  destruct (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) eqn:Hc1; [| exact Hfb].
  destruct (N.leb_spec 1 pl_n) as [Hpl1 | _]; [| discriminate].
  apply N.eqb_eq in Hc1.
  set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
  pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
  set (n := ((pl_n - 1) / 3)%N).
  set (step_h := (1 + n * 2)%N).
  set (cnt1 := (cnt + 1)%N).
  set (mc := availPLCount cnt1 step_h rt1).
  destruct (if N.eqb mc 0 then true else N.ltb cnt1 mc) eqn:Hmc; [exact Hfb |].
  destruct (N.eqb_spec mc 0) as [_ | Hmc0]; [discriminate |].
  destruct (N.ltb_spec cnt1 mc) as [_ | Hmc_le]; [discriminate |].
  destruct (doCallsD (d_front rt1) (d_back rt1) (r_tail rt1) (mc * step_h)%N false) as [[[[hd df'] db'] rtail']|] eqn:Hdc;
    [| exact Hfb].
  destruct (N.eqb_spec hd (mc * step_h)%N) as [-> | _]; [| exact Hfb].
  destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [_ [_ Hcalls]].
  destruct (N_div_mod_nat (pl_n - 1)%N 3 ltac:(lia)) as [Hdiv _].
  change (N.to_nat 3) with 3%nat in Hdiv.
  assert (Hpln : N.to_nat pl_n = (1 + N.to_nat n * 3)%nat) by (subst n; lia).
  rewrite N2Nat.inj_mul in Hcalls.
  replace (N.to_nat mc) with (1 + N.to_nat (mc - 1)%N)%nat in Hcalls by lia.
  replace (N.to_nat step_h) with (1 + N.to_nat n * 2)%nat in Hcalls by (subst step_h; lia).
  cbn [fs_denote fs_L fs_R fs_mode runs_denote sw_toList].
  rewrite Hrt1, runs_push_spec.
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug sw_toList].
  rewrite !denD_pushD.
  change (N.to_nat 1) with 1%nat. rewrite lpow_1.
  replace (N.to_nat cnt1) with ((1 + N.to_nat (mc - 1)%N) + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
  rewrite lpow_add, Str_app_assoc, Hpln.
  replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
  replace (N.to_nat (5 + n * 3)%N) with (5 + N.to_nat n * 3)%nat by lia.
  exact (returnsP_L (N.to_nat (mc - 1)%N) (N.to_nat n) Hcalls _).
Qed.

Definition stepMJ_PL (pl_n cnt : N) (lrest : Runs) (rt : RTape) : FastState :=
  let fallback := MkFastState (unfoldPL1 pl_n cnt lrest) rt MJ in
  if (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) then
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    let n := ((pl_n - 1) / 3)%N in
    let step_h := (1 + n * 2)%N in
    let cnt1 := (cnt + 1)%N in
    let mc := availPLCount cnt1 step_h rt1 in
    if (if N.eqb mc 0 then true else N.ltb cnt1 mc) then fallback
    else
      let req := (mc * step_h)%N in
      match doCallsD (d_front rt1) (d_back rt1) (r_tail rt1) req false with
      | Some (hd, df', db', rtail') =>
        if N.eqb hd req then
          let df'' := pushD (6 + n * 3)%N mc df' in
          MkFastState (runs_push (SW_PL pl_n) (cnt1 - mc)%N lrest) (MkRTape [] df'' db' rtail') MJ
        else fallback
      | None => fallback
      end
  else fallback.

Lemma stepMJ_PL_spec pl_n cnt lrest rt :
  fs_denote (MkFastState ((SW_PL pl_n, (cnt + 1)%N) :: lrest) rt MJ) -->*
  fs_denote (stepMJ_PL pl_n cnt lrest rt).
Proof.
  unfold stepMJ_PL.
  assert (Hfb : fs_denote (MkFastState ((SW_PL pl_n, (cnt + 1)%N) :: lrest) rt MJ) -->*
                fs_denote (MkFastState (unfoldPL1 pl_n cnt lrest) rt MJ)).
  { cbn [fs_denote fs_L fs_R fs_mode]. rewrite unfoldPL1_spec. apply evstep_refl. }
  destruct (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) eqn:Hc1; [| exact Hfb].
  destruct (N.leb_spec 1 pl_n) as [Hpl1 | _]; [| discriminate].
  apply N.eqb_eq in Hc1.
  set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
  pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
  set (n := ((pl_n - 1) / 3)%N).
  set (step_h := (1 + n * 2)%N).
  set (cnt1 := (cnt + 1)%N).
  set (mc := availPLCount cnt1 step_h rt1).
  destruct (if N.eqb mc 0 then true else N.ltb cnt1 mc) eqn:Hmc; [exact Hfb |].
  destruct (N.eqb_spec mc 0) as [_ | Hmc0]; [discriminate |].
  destruct (N.ltb_spec cnt1 mc) as [_ | Hmc_le]; [discriminate |].
  destruct (doCallsD (d_front rt1) (d_back rt1) (r_tail rt1) (mc * step_h)%N false) as [[[[hd df'] db'] rtail']|] eqn:Hdc;
    [| exact Hfb].
  destruct (N.eqb_spec hd (mc * step_h)%N) as [-> | _]; [| exact Hfb].
  destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [_ [_ Hcalls]].
  destruct (N_div_mod_nat (pl_n - 1)%N 3 ltac:(lia)) as [Hdiv _].
  change (N.to_nat 3) with 3%nat in Hdiv.
  assert (Hpln : N.to_nat pl_n = (1 + N.to_nat n * 3)%nat) by (subst n; lia).
  rewrite N2Nat.inj_mul in Hcalls.
  replace (N.to_nat step_h) with (1 + N.to_nat n * 2)%nat in Hcalls by (subst step_h; lia).
  cbn [fs_denote fs_L fs_R fs_mode runs_denote sw_toList].
  rewrite Hrt1, runs_push_spec.
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug sw_toList].
  rewrite denD_pushD.
  replace (N.to_nat cnt1) with (N.to_nat mc + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
  rewrite lpow_add, Str_app_assoc, Hpln.
  replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
  exact (returnsP_J (N.to_nat mc) (N.to_nat n) Hcalls _).
Qed.

Definition stepML_raw (l : Runs) (rt : RTape) : option FastState :=
  let '(b1, l1) := take10 l in
  if N.eqb b1 0 then None
  else
    let '(c111, l2) := take111 l1 in
    if negb (N.eqb c111 0) then
      match r_raw rt with
      | [] =>
        match doCallsD (d_front rt) (d_back rt) (r_tail rt) c111 true with
        | Some (hd, df', db', rtail') =>
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - hd)%N l2) in
          Some (MkFastState l' (MkRTape [] df' db' rtail') ML)
        | None =>
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
          Some (MkFastState l' rt MR)
        end
      | _ :: _ =>
        let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
        Some (MkFastState l' rt MR)
      end
    else
      match runs_remove [1; 1] l1 with
      | Some l2 =>
        if runs_zeros l2 then
          let l' := runs_push (SW_raw [1; 0]) 2 (runs_push (SW_raw [1; 1]) b1 []) in
          Some (MkFastState l' (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) MR)
        else None
      | None =>
        match runs_remove [1] l1 with
        | Some l2 =>
          if runs_zeros l2 then
            match takeDRTape rt with
            | Some (dn, rt') =>
              let l' := runs_push (SW_raw [1; 0]) (dn + 2)%N (runs_push (SW_raw [1; 1]) (b1 - 1)%N []) in
              Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 0]) 1 (r_raw rt')) (d_front rt') (d_back rt') (r_tail rt')) MR)
            | None => None
            end
          else None
        | None => None
        end
      end.

Lemma stepML_raw_spec l rt s' :
  stepML_raw l rt = Some s' ->
  fs_denote (MkFastState l rt ML) -->* fs_denote s'.
Proof.
  unfold stepML_raw.
  pose proof (take10_spec l) as H10.
  destruct (take10 l) as [b1 l1]; cbn [fst snd] in H10.
  destruct (N.eqb_spec b1 0) as [-> | Hb1]; [discriminate |].
  pose proof (take111_spec l1 0inf) as H111.
  rewrite <- !denote_eq_plug_0inf in H111.
  destruct (take111 l1) as [c111 l2]; cbn [fst snd] in H111.
  destruct (N.eqb_spec c111 0) as [Hc0 | Hc0]; cbn [negb].
  - destruct (runs_remove [1; 1] l1) as [l3|] eqn:Hr11.
    + destruct (runs_zeros l3) eqn:Hz; [| discriminate].
      intros H; inversion H; subst; clear H.
      cbn [fs_denote fs_L fs_R fs_mode].
      rewrite H10, (runs_remove_spec _ _ _ Hr11), (runs_zeros_spec _ Hz), !runs_push_spec.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail runs_denote sw_toList].
      rewrite push_plug. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      rewrite lpow_1.
      replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
      apply rule_overflow2.
    + destruct (runs_remove [1] l1) as [l3|] eqn:Hr1; [| discriminate].
      destruct (runs_zeros l3) eqn:Hz; [| discriminate].
      destruct (takeDRTape rt) as [[dn rt']|] eqn:Htd; [| discriminate].
      intros H; inversion H; subst; clear H.
      cbn [fs_denote fs_L fs_R fs_mode].
      rewrite H10, (runs_remove_spec _ _ _ Hr1), (runs_zeros_spec _ Hz), (takeDRTape_spec _ _ _ Htd), !runs_push_spec.
      unfold rt_denote; cbn [r_raw d_front d_back r_tail runs_denote sw_toList].
      rewrite push_plug. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
      replace (N.to_nat (dn + 2)%N) with (N.to_nat dn + 2)%nat by lia.
      apply rule_overflow1.
  - assert (Hrestart :
      fs_denote (MkFastState l rt ML) -->*
      fs_denote (MkFastState (runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2)) rt MR)).
    { cbn [fs_denote fs_L fs_R fs_mode].
      rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
      replace (N.to_nat c111) with (1 + N.to_nat (c111 - 1)%N)%nat at 1 by lia.
      rewrite <- (lpow_Str_add [1; 1; 1]), lpow_1.
      replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
      apply rule_restart. }
    destruct rt as [[|x xs] df db rtail]; cbn [r_raw d_front d_back r_tail].
    + destruct (doCallsD df db rtail c111 true) as [[[[hd df'] db'] rtail']|] eqn:Hdc.
      * intros H; inversion H; subst; clear H.
        destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [_ [Hle Hcalls]].
        cbn [fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
        rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
        replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
        replace (N.to_nat c111) with (N.to_nat hd + N.to_nat (c111 - hd)%N)%nat at 1 by lia.
        rewrite <- (lpow_Str_add [1; 1; 1]).
        exact (loopL Hcalls _ (N.to_nat (b1 - 1)%N)).
      * intros H; inversion H; subst; clear H. exact Hrestart.
    + intros H; inversion H; subst; clear H. exact Hrestart.
Qed.

Definition stepML_col (l : Runs) (rt : RTape) : option FastState :=
  match runs_remove [0; 0; 1; 1; 0; 1] l with
  | Some l' =>
    match takeDRTape rt with
    | Some (dn, rt') =>
      let rt1 := match r_raw rt' with [] => rt' | _ :: _ => flushAllToTail rt' end in
      Some (MkFastState l' (MkRTape [] (pushD (dn + 2)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) MJ)
    | None =>
      Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1; 1; 1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) MJ)
    end
  | None => toRawAndStep l rt ML
  end.

Lemma stepML_col_spec l rt :
  match stepML_col l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML_col.
  destruct (runs_remove [0; 0; 1; 1; 0; 1] l) as [l'|] eqn:Hr; [| apply toRawAndStep_spec].
  destruct (takeDRTape rt) as [[dn rt']|] eqn:Htd.
  - set (rt1 := match r_raw rt' with [] => rt' | _ :: _ => flushAllToTail rt' end).
    pose proof (flush_if_raw_denote rt') as Hrt1; fold rt1 in Hrt1.
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_remove_spec _ _ _ Hr), (takeDRTape_spec _ _ _ Htd), Hrt1.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
    rewrite denD_pushD. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    replace (N.to_nat (dn + 2)%N) with (2 + N.to_nat dn)%nat by lia.
    apply rule_collisionD.
  - cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_remove_spec _ _ _ Hr).
    unfold rt_denote; cbn [r_raw d_front d_back r_tail].
    rewrite push_plug. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    apply rule_collision.
Qed.

Definition stepML_tail (l : Runs) (rt : RTape) : option FastState :=
  match takeS l with
  | Some (sn, l') =>
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    Some (MkFastState l' (MkRTape [] (pushD sn 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) ML)
  | None =>
    match runs_remove [1; 1] l with
    | Some l' =>
      match takeDRTape rt with
      | Some (dn, rt') => Some (MkFastState (runs_push (SW_raw [1; 0]) (dn + 1)%N l') rt' MR)
      | None => stepML_col l rt
      end
    | None => stepML_col l rt
    end
  end.

Lemma stepML_tail_spec l rt :
  match stepML_tail l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML_tail.
  destruct (takeS l) as [[sn l']|] eqn:Hts.
  - set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
    pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (takeS_spec _ _ _ Hts), Hrt1.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
    rewrite denD_pushD. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    apply rule_left.
  - destruct (runs_remove [1; 1] l) as [l'|] eqn:Hr11; [| apply stepML_col_spec].
    destruct (takeDRTape rt) as [[dn rt']|] eqn:Htd; [| apply stepML_col_spec].
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_remove_spec _ _ _ Hr11), (takeDRTape_spec _ _ _ Htd), runs_push_spec.
    cbn [sw_toList].
    replace (N.to_nat (dn + 1)%N) with (1 + N.to_nat dn)%nat by lia.
    apply rule_turnB.
Qed.

Definition stepML (l : Runs) (rt : RTape) : option FastState :=
  match l with
  | (SW_S _, _) :: _ =>
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    let '(l', df') := sweepLeft l (d_front rt1) in
    Some (MkFastState l' (MkRTape [] df' (d_back rt1) (r_tail rt1)) ML)
  | (SW_PL pl_n, Npos pk) :: lrest =>
    Some (stepML_PL pl_n (N.pred (Npos pk)) lrest rt)
  | (SW_raw _, _) :: _ =>
    match stepML_raw l rt with
    | Some s' => Some s'
    | None => stepML_tail l rt
    end
  | _ => stepML_tail l rt
  end.

Lemma stepML_spec l rt :
  match stepML l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  destruct l as [|[w k] lrest]; [apply stepML_tail_spec |].
  destruct w as [lw | dn | sn | pl_n]; cbn [stepML].
  - destruct (stepML_raw ((SW_raw lw, k) :: lrest) rt) as [s'|] eqn:Hsr;
      [exact (stepML_raw_spec _ rt s' Hsr) | apply stepML_tail_spec].
  - apply stepML_tail_spec.
  - set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
    pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
    pose proof (sweepLeft_spec ((SW_S sn, k) :: lrest) (d_front rt1) (denDRev (d_back rt1) (runs_denote (r_tail rt1)))) as Hsl.
    destruct (sweepLeft ((SW_S sn, k) :: lrest) (d_front rt1)) as [l' df']; cbn [fst snd] in Hsl.
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite Hrt1.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
    exact Hsl.
  - destruct k as [|pk]; [apply stepML_tail_spec |].
    replace (Npos pk) with (N.pred (Npos pk) + 1)%N at 1 by lia.
    apply stepML_PL_spec.
Qed.

Definition take10IfRaw (l : Runs) : N * Runs :=
  match l with
  | (SW_raw _, _) :: _ => take10 l
  | _ => (0%N, l)
  end.

Lemma take10IfRaw_spec l :
  runs_denote l = [1; 0]^^(N.to_nat (fst (take10IfRaw l))) *> runs_denote (snd (take10IfRaw l)).
Proof.
  destruct l as [|[[lw | | |] k] rest]; try reflexivity.
  apply take10_spec.
Qed.

Definition stepMJ_turn (l : Runs) (rt : RTape) : option FastState :=
  let '(b, l1) := take10IfRaw l in
  let '(c111, l2) := take111 l1 in
  if N.eqb c111 0 then toRawAndStep l rt MJ
  else
    let b1 := (b + 1)%N in
    match r_raw rt with
    | [] =>
      match doCallsD (d_front rt) (d_back rt) (r_tail rt) c111 true with
      | Some (hd, df', db', rtail') =>
        let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - hd)%N l2) in
        Some (MkFastState l' (MkRTape [] df' db' rtail') ML)
      | None =>
        let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
        Some (MkFastState l' rt MR)
      end
    | _ :: _ =>
      let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
      Some (MkFastState l' rt MR)
    end.

Lemma stepMJ_turn_spec l rt :
  match stepMJ_turn l rt with
  | Some s' => fs_denote (MkFastState l rt MJ) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MJ))
  end.
Proof.
  unfold stepMJ_turn.
  pose proof (take10IfRaw_spec l) as H10.
  destruct (take10IfRaw l) as [b l1]; cbn [fst snd] in H10.
  pose proof (take111_spec l1 0inf) as H111.
  rewrite <- !denote_eq_plug_0inf in H111.
  destruct (take111 l1) as [c111 l2]; cbn [fst snd] in H111.
  destruct (N.eqb_spec c111 0) as [-> | Hc0]; [apply toRawAndStep_spec |].
  assert (Hturn :
    fs_denote (MkFastState l rt MJ) -->*
    fs_denote (MkFastState (runs_push (SW_raw [1; 0]) (b + 1)%N (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2)) rt MR)).
  { cbn [fs_denote fs_L fs_R fs_mode].
    rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
    replace (N.to_nat c111) with (1 + N.to_nat (c111 - 1)%N)%nat at 1 by lia.
    rewrite <- (lpow_Str_add [1; 1; 1]), lpow_1.
    replace (N.to_nat (b + 1)%N) with (1 + N.to_nat b)%nat by lia.
    apply rule_turnJ. }
  destruct rt as [[|x xs] df db rtail]; cbn [r_raw d_front d_back r_tail]; [| exact Hturn].
  destruct (doCallsD df db rtail c111 true) as [[[[hd df'] db'] rtail']|] eqn:Hdc; [| exact Hturn].
  destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hpos [Hle Hcalls]].
  cbn [fs_denote fs_L fs_R fs_mode].
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
  rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
  replace (N.to_nat (b + 1)%N) with (1 + N.to_nat b)%nat by lia.
  replace (N.to_nat c111) with (N.to_nat hd + N.to_nat (c111 - hd)%N)%nat at 1 by lia.
  rewrite <- (lpow_Str_add [1; 1; 1]).
  exact (loopJ' Hpos Hcalls _ (N.to_nat b)).
Qed.

Definition stepMJ (l : Runs) (rt : RTape) : option FastState :=
  match takeS l with
  | Some (sn, l') =>
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    Some (MkFastState l' (MkRTape [] (pushD (sn + 1)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) ML)
  | None =>
    match l with
    | (SW_PL pl_n, Npos pk) :: lrest => Some (stepMJ_PL pl_n (N.pred (Npos pk)) lrest rt)
    | _ => stepMJ_turn l rt
    end
  end.

Lemma stepMJ_spec l rt :
  match stepMJ l rt with
  | Some s' => fs_denote (MkFastState l rt MJ) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MJ))
  end.
Proof.
  unfold stepMJ.
  destruct (takeS l) as [[sn l']|] eqn:Hts.
  - set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
    pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (takeS_spec _ _ _ Hts), Hrt1.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
    rewrite denD_pushD. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    replace (N.to_nat (sn + 1)%N) with (1 + N.to_nat sn)%nat by lia.
    apply rule_leftJ.
  - destruct l as [|[w k] lrest]; [apply stepMJ_turn_spec |].
    destruct w as [| | | pl_n]; try apply stepMJ_turn_spec.
    destruct k as [|pk]; [apply stepMJ_turn_spec |].
    replace (Npos pk) with (N.pred (Npos pk) + 1)%N at 1 by lia.
    apply stepMJ_PL_spec.
Qed.

Definition stepFast (s : FastState) : option FastState :=
  let rt := normRTape (fs_R s) in
  let l := fs_L s in
  match fs_mode s with
  | RAW q d => stepRaw l rt q d
  | MR => stepMR l rt
  | ML => stepML l rt
  | MJ => stepMJ l rt
  end.

Lemma stepFast_spec s :
  match stepFast s with
  | Some s' => fs_denote s -->* fs_denote s'
  | None => halts src_tm (fs_denote s)
  end.
Proof.
  destruct s as [l rt m]; unfold stepFast; cbn [fs_L fs_R fs_mode].
  assert (Hnorm : fs_denote (MkFastState l rt m) = fs_denote (MkFastState l (normRTape rt) m)).
  { destruct m as [| | | q [|]]; cbn [fs_denote fs_L fs_R fs_mode]; rewrite normRTape_spec; reflexivity. }
  rewrite Hnorm.
  destruct m as [| | | q d].
  - apply stepMR_spec.
  - apply stepML_spec.
  - apply stepMJ_spec.
  - apply stepRaw_spec.
Qed.

Fixpoint run_pow (k : nat) (s : FastState) : option FastState :=
  match k with
  | O => stepFast s
  | S k' =>
    match run_pow k' s with
    | Some s1 => run_pow k' s1
    | None => None
    end
  end.

Lemma run_pow_spec k s :
  match run_pow k s with
  | Some s' => fs_denote s -->* fs_denote s'
  | None => halts src_tm (fs_denote s)
  end.
Proof.
  gen s. induction k as [|k IH]; intros s; cbn [run_pow].
  - apply stepFast_spec.
  - pose proof (IH s) as H1.
    destruct (run_pow k s) as [s1|]; [| exact H1].
    pose proof (IH s1) as H2.
    destruct (run_pow k s1) as [s2|].
    + exact (ev_trans _ _ _ H1 H2).
    + exact (evstep_halts _ _ H1 H2).
Qed.

Definition initFastB : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW B R).
Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.

Lemma initFastB_denote : fs_denote initFastB = (B;; tape0).
Proof. reflexivity. Qed.

Lemma run_ok : is_none (run_pow 22 initFastB) = true.
Proof. vm_check_eq. Qed.

Lemma src_halt : halts src_tm (B;; tape0).
Proof.
  rewrite <- initFastB_denote.
  pose proof (run_pow_spec 22 initFastB) as H.
  pose proof run_ok as Hok.
  destruct (run_pow 22 initFastB); [discriminate | exact H].
Qed.

End M244.

Theorem halt : halts tm c0.
Proof. exact (M244.halts_iso M244.src_halt). Qed.
