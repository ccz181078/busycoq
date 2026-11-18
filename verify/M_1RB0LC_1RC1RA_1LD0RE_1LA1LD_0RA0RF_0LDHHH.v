From BusyCoq Require Import Individual62.
Require Import List PeanoNat NArith PArith ZifyNat Lia String.
Import ListNotations.
Open Scope list_scope.
Open Scope sym_scope.

Definition tm : TM := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---".

Module H155900.

Local Infix "/" := Nat.div : nat_scope.
Local Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.

Definition src_tm : TM := Eval compute in (TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---").
Local Notation "c -->* c'" := (c -[ src_tm ]->* c') (at level 40).

Definition permState (q : Q) : Q :=
  match q with
  | A => D | B => A | C => B | D => C | E => E | F => F
  end.

Lemma perm_src : Perm (flip src_tm) tm permState.
Proof.
  split.
  - intros q s H. destruct q, s; cbv in H |- *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q, s; cbv in H |- *; inversion H; subst; reflexivity.
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
Ltac fsteps := norm_cb; repeat ((try solve [finish]); step); try (simpl_rotate; finish).

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

Lemma rule_collision l r : CfgL (l <* [0; 0; 1; 1; 0; 1]) r -->* CfgL l ([1; 1; 1; 1; 1; 1] *> r).
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
  CfgL l (D_word (2 + b) *> r).
Proof. nsteps 4; ffollow scanC; fsteps. Qed.

Lemma rule_defect0 l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgL l ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> r).
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
  CfgL l (D_word 3 *> [1; 0] *> r).
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
       (D_word j *> D_word 3 *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_collide |].
  apply rule_left.
Qed.

Lemma calls_collision k j r :
  calls (1 + k)
    (D_word j *> [1; 0] *> (D_word 0)^^((1 + k) * 2) *> r)
    (D_word j *> (D_word 3)^^(1 + k) *> [1; 0] *> r).
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
    pose proof (calls_D_pow j 1 (IH 3%nat)) as H.
    cbn [lpow] in H. rewrite ?app_nil_r in H.
    replace ((D_word 3)^^(1 + S k)) with (D_word 3 ++ (D_word 3)^^(1 + k)) by reflexivity.
    rewrite Str_app_assoc. exact H.
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
  CfgL (PL_word (1 + n * 3) *> l) r -->* CfgL l (D_word (6 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  change (6 + n * 3)%nat with (2 + (4 + n * 3))%nat.
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
  CfgJ (PL_word (1 + n * 3) *> l) r -->* CfgL l (D_word (7 + n * 3) *> s).
Proof.
  rewrite pl_decomp.
  eapply ev_trans; [apply (loopJ H _ (5 + n * 3)) |].
  change (7 + n * 3)%nat with (2 + (5 + n * 3))%nat.
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

Lemma returnsP_L0 k n {r s} (H : calls (k * (1 + n * 2)) r s) l :
  CfgL ((PL_word (1 + n * 3))^^k *> l) r -->* CfgL l ((D_word (6 + n * 3))^^k *> s).
Proof.
  gen r s l. induction k as [|k IH]; intros r s H l; cbn [Nat.mul] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
    cbn [lpow]. rewrite Str_app_assoc.
    eapply ev_trans; [apply (returnP_L Hu) |].
    pose proof (calls_D_pow (6 + n * 3) 1 Hv) as Hv'.
    cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
    eapply ev_trans; [apply (IH _ _ Hv') |].
    rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma returnsP_J k n {r s} (H : calls ((1 + k) * (1 + n * 2)) r s) l :
  CfgJ ((PL_word (1 + n * 3))^^(1 + k) *> l) r -->*
  CfgL l ((D_word (6 + n * 3))^^k *> D_word (7 + n * 3) *> s).
Proof.
  cbn [Nat.add Nat.mul] in H.
  destruct (calls_split (1 + n * 2) (k * (1 + n * 2)) H) as [u [Hu Hv]].
  cbn [Nat.add lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply (returnP_J Hu) |].
  pose proof (calls_D_pow (7 + n * 3) 1 Hv) as Hv'.
  cbn [lpow] in Hv'. rewrite ?app_nil_r in Hv'.
  exact (returnsP_L0 k n Hv' l).
Qed.

Lemma returnsP_L k n {r s} (H : calls ((1 + k) * (1 + n * 2)) r s) l :
  CfgL ((PL_word (1 + n * 3))^^(1 + k) *> l) r -->*
  CfgL l ((D_word (6 + n * 3))^^(1 + k) *> s).
Proof. exact (returnsP_L0 (1 + k) n H l). Qed.

Lemma rule_collisionD l r n :
  CfgL ([0; 0; 1; 1; 0; 1] *> l) (D_word n *> r) -->*
  CfgL l (D_word (3 + n) *> r).
Proof.
  replace (D_word (3 + n) *> r) with ([1; 1; 1; 1; 1; 1] *> D_word n *> r)
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; reflexivity).
  apply rule_collision.
Qed.

Lemma rule_defect0D l r m :
  CfgR l ([1; 0] *> D_word 0 *> D_word m *> r) -->*
  CfgL l (D_word (3 + m) *> [1; 0] *> r).
Proof.
  replace (D_word m *> r) with ([1] *> [1; 1]^^m *> [0] *> ([0] *> r))
    by (unfold D_word; rewrite ?Str_app_assoc; reflexivity).
  replace (D_word (3 + m) *> [1; 0] *> r)
    with ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> ([0] *> r))
    by (unfold D_word; cbn [Nat.add lpow app Str_app]; rewrite ?Str_app_assoc; reflexivity).
  apply rule_defect0.
Qed.

Lemma rule_defect0' l r m : CfgR l ([1; 0] *> D_word 0 *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgL l (D_word (m + 3) *> [1] *> r).
Proof.
  replace (D_word (m + 3) *> [1] *> r) with ([1; 1; 1; 1; 1; 1] *> D_word m *> [1] *> r)
    by (replace (m + 3)%nat with (3 + m)%nat by lia; unfold D_word; cbn [Nat.add lpow app Str_app]; rewrite ?Str_app_assoc; reflexivity).
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
       (D_word j *> D_word (3 + m) *> [1; 0] *> r).
Proof.
  intros l.
  eapply ev_trans; [apply rule_right |].
  eapply ev_trans; [apply rule_defect0D |].
  apply rule_left.
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


Definition DefWord (a k : nat) : list Sym :=
  [1; 0]^^a ++ [1]^^k ++ [0; 1] ++ S_word 0.

Lemma rule_zeroL_DD r a b :
  CfgL 0inf (D_word a *> D_word b *> r) -->*
  CfgR ([1; 0]^^(b + 2) *> [1; 1]^^a *> 0inf) ([1; 0] *> r).
Proof.
  nsteps 7; fones2;
  nsteps 8; ffollow scanR1; nsteps 16; fscanB;
  nsteps 11; ffollow scanR; finish.
Qed.

Lemma rule_zeroL_D10_0 r :
  CfgL 0inf (D_word 0 *> [1; 0] *> r) -->*
  CfgR (S_word 0 *> 0inf) ([1] *> r).
Proof. fsteps. Qed.

Lemma rule_zeroL_D10_S r a :
  CfgL 0inf (D_word (1 + a) *> [1; 0] *> r) -->*
  CfgR ([1; 0]^^2 *> [1; 1]^^(1 + a) *> 0inf) ([1] *> r).
Proof. nsteps 9; fones2; fsteps. Qed.

Lemma rule_zeroL_1 r :
  CfgL ([1] *> 0inf) r -->* CfgJ 0inf r.
Proof. fsteps. Qed.

Lemma rule_zeroL_J_mid r n :
  CfgJ 0inf (D_word n *> r) -->*
  CfgL 0inf (D_word (1 + n) *> [1; 0] *> r).
Proof.
  nsteps 12; ffollow scanR1;
  nsteps 16; fscanB; finish.
Qed.

Lemma rule_zeroL_J r n :
  CfgJ 0inf (D_word n *> r) -->*
  CfgR ([1; 0]^^2 *> [1; 1]^^(1 + n) *> 0inf) ([1] *> r).
Proof.
  eapply ev_trans; [apply rule_zeroL_J_mid | apply rule_zeroL_D10_S].
Qed.

Lemma calls_trans {a b r s t} (H1 : calls a r s) (H2 : calls b s t) :
  calls (a + b) r t.
Proof.
  induction H1 as [r | n r0 u v Hc _ IH]; cbn [Nat.add]; [exact H2 |].
  econstructor; [exact Hc | exact (IH H2)].
Qed.

Lemma def_to_list_one_two n :
  [1; 1]^^n ++ S_word 0 = [1]^^(2 * n + 1) ++ [0; 1].
Proof.
  rewrite <- one_pow_two_mul, lpow_plus_r.
  unfold S_word. cbn [Nat.add lpow app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma pl_eq_def n : PL_word n = DefWord (n + 4) (2 * n + 1).
Proof.
  unfold PL_word, DefWord. f_equal.
  rewrite !app_assoc. f_equal.
  apply def_to_list_one_two.
Qed.

Lemma rule_defect2D_def l r n m :
  CfgR l ([1; 0] *> D_word (2 + n) *> D_word m *> r) -->*
  CfgR (DefWord (m + 2) (2 * n + 1) *> l) ([1; 0] *> r).
Proof.
  replace (DefWord (m + 2) (2 * n + 1) *> l)
    with ([1; 0]^^(2 + m) *> [1; 1]^^n *> S_word 0 *> S_word 0 *> l).
  - apply rule_defect2D.
  - unfold DefWord. replace (m + 2)%nat with (2 + m)%nat by lia.
    rewrite !Str_app_assoc. f_equal.
    change ([1; 1]^^n *> S_word 0 *> S_word 0 *> l) with ([1; 1]^^n *> (S_word 0 *> (S_word 0 *> l))).
    rewrite <- (Str_app_assoc ([1; 1]^^n) (S_word 0)), def_to_list_one_two, !Str_app_assoc. reflexivity.
Qed.

Lemma rule_defect2_def l r n m :
  CfgR l ([1; 0] *> D_word (2 + n) *> [1] *> [1; 1]^^m *> [0] *> r) -->*
  CfgR (DefWord (m + 2) (2 * n + 1) *> l) ([1] *> r).
Proof.
  replace (DefWord (m + 2) (2 * n + 1) *> l)
    with ([1; 0]^^(2 + m) *> [1; 1]^^n *> S_word 0 *> S_word 0 *> l).
  - apply rule_defect2.
  - unfold DefWord. replace (m + 2)%nat with (2 + m)%nat by lia.
    rewrite !Str_app_assoc. f_equal.
    change ([1; 1]^^n *> S_word 0 *> S_word 0 *> l) with ([1; 1]^^n *> (S_word 0 *> (S_word 0 *> l))).
    rewrite <- (Str_app_assoc ([1; 1]^^n) (S_word 0)), def_to_list_one_two, !Str_app_assoc. reflexivity.
Qed.

Lemma rule_defect_blank0_def l r :
  CfgR l ([1; 0] *> D_word 0 *> [0; 0] *> r) -->*
  CfgR (DefWord 1 0 *> l) r.
Proof.
  replace (DefWord 1 0 *> l) with ([1; 0; 0; 1] *> S_word 0 *> l)
    by (unfold DefWord; cbn [lpow app Str_app]; reflexivity).
  apply rule_defect_blank0.
Qed.

Lemma rule_defect_blankS_def l r a :
  CfgR l ([1; 0] *> D_word (1 + a) *> [0; 0] *> r) -->*
  CfgR (DefWord 1 (2 * (a + 1)) *> l) r.
Proof.
  replace (DefWord 1 (2 * (a + 1)) *> l)
    with ([1; 0] *> [1; 1]^^a *> [1] *> S_word 0 *> S_word 0 *> l).
  - apply rule_defect_blankS.
  - unfold DefWord.
    replace (2 * (a + 1))%nat with (2 * a + 2)%nat by lia.
    rewrite lpow_add, one_pow_two_mul.
    unfold S_word. cbn [Nat.add lpow app Str_app]. rewrite ?app_nil_r, ?Str_app_assoc. reflexivity.
Qed.

Lemma one_zero_pow_one_eq_S a t :
  [1; 0]^^a *> [1; 0; 1] *> t = S_word a *> t.
Proof.
  induction a as [|a IH]; unfold S_word in *; cbn [Nat.add lpow app Str_app] in *; [reflexivity |].
  f_equal; f_equal. exact IH.
Qed.

Lemma def_k1_den a l :
  DefWord a 1 *> l = S_word a *> S_word 0 *> l.
Proof.
  unfold DefWord. cbn [lpow app]. rewrite !Str_app_assoc.
  apply one_zero_pow_one_eq_S.
Qed.

Lemma def_k2_den a l :
  DefWord (a + 1) 2 *> l = S_word a *> S_word 0 *> S_word 0 *> l.
Proof.
  unfold DefWord. rewrite lpow_plus_r. cbn [lpow app].
  rewrite !Str_app_assoc.
  replace ([1; 0] *> [1; 1; 0; 1] *> S_word 0 *> l)
    with ([1; 0; 1] *> S_word 0 *> S_word 0 *> l)
    by (unfold S_word; cbn [Nat.add lpow app Str_app]; reflexivity).
  apply one_zero_pow_one_eq_S.
Qed.

Lemma rule_paired_1_0 l r :
  CfgR l ([1; 0]^^2 *> D_word 0 *> r) -->* CfgR (DefWord 0 2 *> l) r.
Proof.
  change ([1; 0]^^2) with ([1; 0]^^(1 * 2)).
  replace (DefWord 0 2 *> l) with ([1; 0]^^0 *> [1; 1; 0; 1]^^1 *> S_word 0 *> l)
    by (unfold DefWord; cbn [lpow app Str_app]; reflexivity).
  apply (rule_paired l r 1 0).
Qed.

Lemma rule_paired_1_S l r dn :
  CfgR l ([1; 0]^^2 *> D_word (dn + 1) *> r) -->*
  CfgR (S_word dn *> S_word 0 *> S_word 0 *> l) r.
Proof.
  change ([1; 0]^^2) with ([1; 0]^^(1 * 2)).
  rewrite <- def_k2_den.
  replace (DefWord (dn + 1) 2 *> l)
    with ([1; 0]^^(dn + 1) *> [1; 1; 0; 1]^^1 *> S_word 0 *> l)
    by (unfold DefWord; cbn [lpow app]; rewrite !Str_app_assoc; reflexivity).
  apply (rule_paired l r 1 (dn + 1)).
Qed.

Lemma def_split_three a k d l :
  (3 * d <= k)%nat ->
  DefWord a k *> l =
    [1; 0]^^a *> [1; 1; 1]^^d *> [1]^^(k - 3 * d) *> [0; 1] *> S_word 0 *> l.
Proof.
  intros Hle. unfold DefWord.
  replace k with (3 * d + (k - 3 * d))%nat at 1 by lia.
  rewrite (lpow_add _ (3 * d) (k - 3 * d) [1]), one_pow_three_mul.
  rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma def_k0_ML {a} (Ha : (1 <= a)%nat) l r :
  CfgL (DefWord a 0 *> l) r -->* CfgL l (D_word (1 + a) *> r).
Proof.
  replace a with (1 + (a - 1))%nat by lia.
  unfold DefWord. cbn [lpow app]. rewrite !Str_app_assoc.
  replace (1 + (1 + (a - 1)))%nat with (2 + (a - 1))%nat by lia.
  apply rule_finishP.
Qed.

Lemma def_k1_ML a l r :
  CfgL (DefWord a 1 *> l) r -->* CfgL l (D_word 0 *> D_word a *> r).
Proof.
  rewrite def_k1_den.
  eapply ev_trans; [apply rule_left | apply rule_left].
Qed.

Lemma def_k2_ML {a} (Ha : (1 <= a)%nat) l r :
  CfgL (DefWord a 2 *> l) r -->* CfgL l (D_word 0 *> D_word 0 *> D_word (a - 1) *> r).
Proof.
  replace a with ((a - 1) + 1)%nat at 1 by lia.
  rewrite def_k2_den.
  eapply ev_trans; [apply rule_left |].
  eapply ev_trans; [apply rule_left | apply rule_left].
Qed.

Lemma def_k1_MJ a l r :
  CfgJ (DefWord a 1 *> l) r -->* CfgL l (D_word 0 *> D_word (a + 1) *> r).
Proof.
  rewrite def_k1_den. replace (a + 1)%nat with (1 + a)%nat by lia.
  eapply ev_trans; [apply rule_leftJ | apply rule_left].
Qed.

Lemma def_k2_MJ {a} (Ha : (1 <= a)%nat) l r :
  CfgJ (DefWord a 2 *> l) r -->* CfgL l (D_word 0 *> D_word 0 *> D_word a *> r).
Proof.
  replace a with ((a - 1) + 1)%nat at 1 by lia.
  rewrite def_k2_den.
  replace (D_word a) with (D_word (1 + (a - 1))) by (f_equal; lia).
  eapply ev_trans; [apply rule_leftJ |].
  eapply ev_trans; [apply rule_left | apply rule_left].
Qed.

Lemma def_02_ML dn l r :
  CfgL (DefWord 0 2 *> l) (D_word dn *> r) -->* CfgR (DefWord (dn + 1) 0 *> l) r.
Proof.
  replace (DefWord 0 2 *> l) with ([1; 1] *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; cbn [lpow app Str_app]; reflexivity).
  replace (DefWord (dn + 1) 0 *> l) with ([1; 0]^^(1 + dn) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; replace (dn + 1)%nat with (1 + dn)%nat by lia; cbn [lpow app]; rewrite !Str_app_assoc; reflexivity).
  apply rule_turnB.
Qed.

Lemma def_loopL {a k hd} (Ha : (1 <= a)%nat) (H3 : (3 * hd <= k)%nat) {r s} (Hc : calls hd r s) l :
  CfgL (DefWord a k *> l) r -->* CfgL (DefWord a (k - 3 * hd) *> l) s.
Proof.
  rewrite (def_split_three a k hd l H3).
  replace a with (1 + (a - 1))%nat by lia.
  replace (DefWord (1 + (a - 1)) (k - 3 * hd) *> l)
    with ([1; 0]^^(1 + (a - 1)) *> [1]^^(k - 3 * hd) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; rewrite !Str_app_assoc; reflexivity).
  exact (loopL Hc _ (a - 1)).
Qed.

Lemma def_restart {a k} (Ha : (1 <= a)%nat) (Hk : (3 <= k)%nat) l r :
  CfgL (DefWord a k *> l) r -->* CfgR (DefWord a (k - 3) *> l) r.
Proof.
  assert (H3 : (3 * 1 <= k)%nat) by lia.
  rewrite (def_split_three a k 1 l H3).
  replace a with (1 + (a - 1))%nat by lia.
  change ([1; 1; 1]^^1) with ([1; 1; 1] ++ []). rewrite app_nil_r.
  replace (k - 3 * 1)%nat with (k - 3)%nat by lia.
  replace (DefWord (1 + (a - 1)) (k - 3) *> l)
    with ([1; 0]^^(1 + (a - 1)) *> [1]^^(k - 3) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; rewrite !Str_app_assoc; reflexivity).
  apply rule_restart.
Qed.

Lemma def_turnJ {a k} (Hk : (3 <= k)%nat) l r :
  CfgJ (DefWord a k *> l) r -->* CfgR (DefWord (a + 1) (k - 3) *> l) r.
Proof.
  assert (H3 : (3 * 1 <= k)%nat) by lia.
  rewrite (def_split_three a k 1 l H3).
  change ([1; 1; 1]^^1) with ([1; 1; 1] ++ []). rewrite app_nil_r.
  replace (k - 3 * 1)%nat with (k - 3)%nat by lia.
  replace (DefWord (a + 1) (k - 3) *> l)
    with ([1; 0]^^(1 + a) *> [1]^^(k - 3) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; replace (a + 1)%nat with (1 + a)%nat by lia; rewrite !Str_app_assoc; reflexivity).
  apply rule_turnJ.
Qed.

Lemma def_step_ML_part {a k hd} (Ha : (1 <= a)%nat) (Hlt : (hd < k / 3)%nat)
    {r s} (Hc : calls hd r s) l :
  CfgL (DefWord a k *> l) r -->* CfgR (DefWord a (k - 3 * (hd + 1)) *> l) s.
Proof.
  assert (Hdiv : (k = 3 * (k / 3) + k mod 3)%nat) by (apply Nat.div_mod; lia).
  assert (H3 : (3 * hd <= k)%nat) by lia.
  assert (Hrem3 : (3 <= k - 3 * hd)%nat) by lia.
  eapply ev_trans; [exact (def_loopL Ha H3 Hc l) |].
  replace (k - 3 * (hd + 1))%nat with (k - 3 * hd - 3)%nat by lia.
  exact (def_restart Ha Hrem3 l s).
Qed.

Lemma def_loopJ_to_rem {a k} (Hk : (3 <= k)%nat) {r s} (Hc : calls (k / 3) r s) l :
  CfgJ (DefWord a k *> l) r -->* CfgL (DefWord (a + 1) (k mod 3) *> l) s.
Proof.
  assert (Hdiv : (k = 3 * (k / 3) + k mod 3)%nat) by (apply Nat.div_mod; lia).
  assert (Hmod : (k mod 3 < 3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hpos : (0 < k / 3)%nat) by lia.
  assert (H3 : (3 * (k / 3) <= k)%nat) by lia.
  rewrite (def_split_three a k (k / 3) l H3).
  replace (k - 3 * (k / 3))%nat with (k mod 3)%nat by lia.
  replace (DefWord (a + 1) (k mod 3) *> l)
    with ([1; 0]^^(1 + a) *> [1]^^(k mod 3) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; replace (a + 1)%nat with (1 + a)%nat by lia; rewrite !Str_app_assoc; reflexivity).
  exact (loopJ' Hpos Hc _ a).
Qed.

Lemma def_step_MJ_part {a k hd} (Hk : (3 <= k)%nat) (Hlt : (hd < k / 3)%nat)
    {r s} (Hc : calls hd r s) l :
  CfgJ (DefWord a k *> l) r -->* CfgR (DefWord (a + 1) (k - 3 - 3 * hd) *> l) s.
Proof.
  assert (Hdiv : (k = 3 * (k / 3) + k mod 3)%nat) by (apply Nat.div_mod; lia).
  assert (H3 : (3 * hd <= k - 3)%nat) by lia.
  eapply ev_trans; [exact (def_turnJ Hk l r) |].
  rewrite (def_split_three (a + 1) (k - 3) hd l H3).
  replace (a + 1)%nat with (1 + a)%nat by lia.
  replace (DefWord (1 + a) (k - 3 - 3 * hd) *> l)
    with ([1; 0]^^(1 + a) *> [1]^^(k - 3 - 3 * hd) *> [0; 1] *> S_word 0 *> l)
    by (unfold DefWord; rewrite !Str_app_assoc; reflexivity).
  exact (loopR Hc _ a).
Qed.

Lemma rule_mr_a0_DEF {la lk} (Hla : (1 <= la)%nat) (Hlk : (3 <= lk)%nat) m l r :
  CfgR (DefWord la lk *> l) ([1; 0] *> D_word 0 *> D_word m *> r) -->*
  CfgR (S_word (m + 3) *> DefWord la (lk - 3) *> l) ([1; 0] *> r).
Proof.
  eapply ev_trans; [apply rule_defect0D |].
  replace (3 + m)%nat with (m + 3)%nat by lia.
  eapply ev_trans; [exact (def_restart Hla Hlk l _) |].
  apply rule_right.
Qed.

Lemma rule_mr_a0_S_DEF {la lk} (Hla : (1 <= la)%nat) (Hlk : (3 <= lk)%nat) sn m l r :
  CfgR (S_word sn *> DefWord la lk *> l) ([1; 0] *> D_word 0 *> D_word m *> r) -->*
  CfgR (S_word (m + 3) *> S_word sn *> DefWord la (lk - 3) *> l) ([1; 0] *> r).
Proof.
  eapply ev_trans; [apply rule_defect0D |].
  replace (3 + m)%nat with (m + 3)%nat by lia.
  eapply ev_trans; [apply rule_left |].
  eapply ev_trans; [exact (def_restart Hla Hlk l _) |].
  eapply ev_trans; [apply rule_right | apply rule_right].
Qed.

(* ========================================================================== *)
(* Section 3: Compressed Macro Tape Engine (Digits, SymWord, Runs, RTape)     *)
(* ========================================================================== *)

Lemma pos_to_nat_succ p : N.to_nat (Npos p) = S (N.to_nat (N.pred (Npos p))).
Proof. lia. Qed.

Definition mod2_1 (x : N) : bool :=
  match x with Npos (xI _) | Npos xH => true | _ => false end.

Lemma mod2_1_eq x : mod2_1 x = N.eqb (x mod 2)%N 1.
Proof.
  destruct x as [|[p|p|]]; unfold mod2_1; symmetry.
  - apply N.eqb_neq; lia.
  - change (Npos (xI p)) with (2 * Npos p + 1)%N. apply N.eqb_eq; lia.
  - change (Npos (xO p)) with (2 * Npos p)%N. apply N.eqb_neq; lia.
  - reflexivity.
Qed.

Definition mod2_0 (x : N) : bool :=
  match x with Npos (xI _) | Npos xH => false | _ => true end.

Lemma mod2_0_eq x : mod2_0 x = N.eqb (x mod 2)%N 0.
Proof.
  destruct x as [|[p|p|]]; unfold mod2_0; symmetry.
  - reflexivity.
  - change (Npos (xI p)) with (2 * Npos p + 1)%N. apply N.eqb_neq; lia.
  - change (Npos (xO p)) with (2 * Npos p)%N. apply N.eqb_eq; lia.
  - reflexivity.
Qed.

Definition mul2 (x : N) : N :=
  match x with N0 => N0 | Npos p => Npos (xO p) end.

Lemma mul2_eq x : mul2 x = (x * 2)%N.
Proof. change (mul2 x) with (2 * x)%N. lia. Qed.

Definition capDiv (cnt k0 step_h : N) : N :=
  let half := N.div2 k0 in
  if N.leb (step_h * cnt) half then cnt
  else if N.ltb half step_h then 0%N
  else if N.eqb step_h 1 then half
  else (half / step_h)%N.

Fixpoint beqListSym (xs ys : list Sym) : bool :=
  match xs, ys with
  | [], [] => true
  | a :: xs', b :: ys' => if sym_eqb a b then beqListSym xs' ys' else false
  | _, _ => false
  end.

Lemma beqListSym_eq xs ys : beqListSym xs ys = true -> xs = ys.
Proof.
  gen ys. induction xs as [|a xs IH]; intros [|b ys] H; cbn [beqListSym] in H; try discriminate; [reflexivity |].
  destruct (sym_eqb_spec a b); [subst | discriminate].
  f_equal. exact (IH _ H).
Qed.

Definition Digits := list (N * N).

Fixpoint beqDigits (xs ys : Digits) : bool :=
  match xs, ys with
  | [], [] => true
  | (n1, k1) :: xs', (n2, k2) :: ys' =>
    if N.eqb n1 n2 then if N.eqb k1 k2 then beqDigits xs' ys' else false else false
  | _, _ => false
  end.

Lemma beqDigits_eq xs ys : beqDigits xs ys = true -> xs = ys.
Proof.
  gen ys. induction xs as [|[n1 k1] xs IH]; intros [|[n2 k2] ys] H; cbn [beqDigits] in H; try discriminate; [reflexivity |].
  destruct (N.eqb_spec n1 n2) as [<- | _]; [| discriminate].
  destruct (N.eqb_spec k1 k2) as [<- | _]; [| discriminate].
  f_equal. exact (IH _ H).
Qed.

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

Lemma rev_append_eq {A} (xs ys : list A) :
  rev_append xs ys = rev_append xs [] ++ ys.
Proof.
  gen ys. induction xs as [|x xs IH]; intros ys; cbn [rev_append]; [reflexivity |].
  rewrite (IH (x :: ys)), (IH [x]), <- app_assoc. reflexivity.
Qed.

Lemma denD_app xs ys t : denD (xs ++ ys) t = denD xs (denD ys t).
Proof.
  induction xs as [|[n k] xs IH]; cbn [app denD]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma denDRev_app xs ys t : denDRev (xs ++ ys) t = denDRev ys (denDRev xs t).
Proof.
  gen t. induction xs as [|[n k] xs IH]; intros t; cbn [app denDRev]; [reflexivity |].
  apply IH.
Qed.

Lemma denD_rev_append_nil xs t : denD (rev_append xs []) t = denDRev xs t.
Proof.
  change t with (denD [] t) at 2. symmetry. apply denDRev_rev_append.
Qed.

Lemma denDRev_rev_append_nil xs t : denDRev (rev_append xs []) t = denD xs t.
Proof.
  gen t. induction xs as [|[n k] xs IH]; intros t; cbn [rev_append denD]; [reflexivity |].
  rewrite rev_append_eq, denDRev_app; cbn [denDRev]. rewrite IH. reflexivity.
Qed.

Lemma call_denD v {r s} (H : call r s) : call (denD v r) (denD v s).
Proof.
  induction v as [|[n k] v IH]; cbn [denD]; [exact H |].
  apply call_D_pow, IH.
Qed.

Lemma call_denDRev v {r s} (H : call r s) : call (denDRev v r) (denDRev v s).
Proof.
  rewrite <- !denD_rev_append_nil.
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

Fixpoint digitsToList (ds : Digits) : list Sym :=
  match ds with
  | [] => []
  | (n, k) :: rest => (D_word (N.to_nat n))^^(N.to_nat k) ++ digitsToList rest
  end.

Definition digitsRevToList (ds : Digits) : list Sym :=
  digitsToList (pushDRevAux ds []).

Lemma digitsToList_plug ds t : digitsToList ds *> t = denD ds t.
Proof.
  induction ds as [|[n k] rest IH]; cbn [digitsToList denD]; [reflexivity |].
  rewrite Str_app_assoc, IH. reflexivity.
Qed.

Lemma digitsRevToList_plug ds t : digitsRevToList ds *> t = denDRev ds t.
Proof.
  unfold digitsRevToList. rewrite digitsToList_plug, denD_pushDRevAux. reflexivity.
Qed.

Lemma digitsToList_pushD n k xs :
  digitsToList (pushD n k xs) = (D_word (N.to_nat n))^^(N.to_nat k) ++ digitsToList xs.
Proof.
  unfold pushD.
  destruct (N.eqb_spec k 0) as [-> | _]; [reflexivity |].
  destruct xs as [|[m j] rest]; [cbn [digitsToList]; rewrite app_nil_r; reflexivity |].
  destruct (N.eqb_spec n m) as [-> | _]; [| reflexivity].
  cbn [digitsToList]. rewrite N2Nat.inj_add, lpow_add, <- app_assoc. reflexivity.
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
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denD]; [discriminate | exact IH |].
  intros H; inversion H; subst; clear H.
  rewrite denD_pushD, pos_to_nat_succ. cbn [lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma popDList_denD_none xs t :
  popDList xs = None -> denD xs t = t.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denD]; [reflexivity | exact IH | discriminate].
Qed.

Lemma popDList_denDRev xs n xs' t :
  popDList xs = Some (n, xs') -> denDRev xs t = denDRev xs' (D_word (N.to_nat n) *> t).
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denDRev]; [discriminate | exact IH |].
  intros H; inversion H; subst; clear H.
  rewrite denDRev_pushD.
  replace (N.to_nat (Npos pk)) with (N.to_nat (N.pred (Npos pk)) + 1)%nat by lia.
  rewrite lpow_plus_r, Str_app_assoc. reflexivity.
Qed.

Lemma popDList_denDRev_none xs t :
  popDList xs = None -> denDRev xs t = t.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList denDRev]; [reflexivity | exact IH | discriminate].
Qed.

Lemma popDList_digitsToList xs n xs' :
  popDList xs = Some (n, xs') -> digitsToList xs = D_word (N.to_nat n) ++ digitsToList xs'.
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList digitsToList]; [discriminate | exact IH |].
  intros H; inversion H; subst; clear H.
  rewrite digitsToList_pushD, pos_to_nat_succ. cbn [lpow]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma popDList_none_nil xs :
  popDList xs = None -> digitsToList xs = [].
Proof.
  induction xs as [|[m [|pk]] rest IH]; cbn [popDList digitsToList]; [reflexivity | exact IH | discriminate].
Qed.

Inductive SymWord :=
| SW_raw (w : list Sym)
| SW_D (n : N)
| SW_S (n : N)
| SW_PL (n : N)
| SW_DEF (a k : N)
| SW_DF (ds : Digits)
| SW_DB (ds : Digits).

Definition sw_toList (w : SymWord) : list Sym :=
  match w with
  | SW_raw lw => lw
  | SW_D n => D_word (N.to_nat n)
  | SW_S n => S_word (N.to_nat n)
  | SW_PL n => PL_word (N.to_nat n)
  | SW_DEF a k => DefWord (N.to_nat a) (N.to_nat k)
  | SW_DF ds => digitsToList ds
  | SW_DB ds => digitsRevToList ds
  end.

Definition sw_isEmpty (w : SymWord) : bool :=
  match w with
  | SW_raw [] => true
  | _ => false
  end.

Lemma sw_isEmpty_spec w : sw_isEmpty w = true -> sw_toList w = [].
Proof. destruct w as [[|] | | | | | |]; cbn; congruence. Qed.

Definition sw_beq (w v : SymWord) : bool :=
  match w, v with
  | SW_raw lw, SW_raw lv => beqListSym lw lv
  | SW_D n, SW_D m => N.eqb n m
  | SW_S n, SW_S m => N.eqb n m
  | SW_PL n, SW_PL m => N.eqb n m
  | SW_DEF a1 k1, SW_DEF a2 k2 => if N.eqb a1 a2 then N.eqb k1 k2 else false
  | SW_DF d1, SW_DF d2 => beqDigits d1 d2
  | SW_DB d1, SW_DB d2 => beqDigits d1 d2
  | _, _ => false
  end.

Lemma sw_beq_eq w v : sw_beq w v = true -> w = v.
Proof.
  destruct w, v; cbn [sw_beq]; try discriminate.
  - intros H; f_equal; exact (beqListSym_eq _ _ H).
  - intros H; apply N.eqb_eq in H; congruence.
  - intros H; apply N.eqb_eq in H; congruence.
  - intros H; apply N.eqb_eq in H; congruence.
  - destruct (N.eqb_spec a a0) as [<- | _]; [| discriminate].
    intros H; apply N.eqb_eq in H; congruence.
  - intros H; f_equal; exact (beqDigits_eq _ _ H).
  - intros H; f_equal; exact (beqDigits_eq _ _ H).
Qed.

Definition Runs := list (SymWord * N).

Fixpoint plug (xs : Runs) (t : side) : side :=
  match xs with
  | [] => t
  | (w, n) :: xs' => (sw_toList w)^^(N.to_nat n) *> plug xs' t
  end.

Fixpoint runs_denote (xs : Runs) : side :=
  match xs with
  | [] => 0inf
  | (w, n) :: xs' => (sw_toList w)^^(N.to_nat n) *> runs_denote xs'
  end.

Lemma denote_eq_plug_0inf xs : runs_denote xs = plug xs 0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn [runs_denote plug]; [reflexivity |].
  rewrite IH. reflexivity.
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
    rewrite <- (sw_beq_eq w v Hb).
    cbn [plug]. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma runs_push_spec w n xs :
  runs_denote (runs_push w n xs) = (sw_toList w)^^(N.to_nat n) *> runs_denote xs.
Proof.
  rewrite !denote_eq_plug_0inf. apply push_plug.
Qed.

Definition pushPL (n kp : N) (xs : Runs) : Runs :=
  if N.eqb kp 0 then xs
  else
    match xs with
    | (SW_PL m, j) :: ys =>
      if N.eqb n m then (SW_PL m, (kp + j)%N) :: ys
      else (SW_PL n, kp) :: xs
    | _ => (SW_PL n, kp) :: xs
    end.

Lemma pushPL_spec n kp xs :
  runs_denote (pushPL n kp xs) = (PL_word (N.to_nat n))^^(N.to_nat kp) *> runs_denote xs.
Proof.
  unfold pushPL.
  destruct (N.eqb_spec kp 0) as [-> | _]; [reflexivity |].
  destruct xs as [|[v j] ys]; [reflexivity |].
  destruct v; try reflexivity.
  destruct (N.eqb_spec n n0) as [-> | _]; [| reflexivity].
  cbn [runs_denote sw_toList]. rewrite N2Nat.inj_add, lpow_add, Str_app_assoc. reflexivity.
Qed.

Definition pushDEF1 (a k : N) (xs : Runs) : Runs :=
  match xs with
  | (SW_DEF a' k', j) :: ys =>
    if (if N.eqb a a' then N.eqb k k' else false) then (SW_DEF a' k', (1 + j)%N) :: ys
    else (SW_DEF a k, 1%N) :: xs
  | _ => (SW_DEF a k, 1%N) :: xs
  end.

Lemma pushDEF1_spec a k xs :
  runs_denote (pushDEF1 a k xs) = DefWord (N.to_nat a) (N.to_nat k) *> runs_denote xs.
Proof.
  unfold pushDEF1.
  destruct xs as [|[v j] ys].
  - cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
  - destruct v; try (cbn [runs_denote sw_toList]; change (N.to_nat 1) with 1%nat; rewrite lpow_1; reflexivity).
    destruct (N.eqb_spec a a0) as [<- | _].
    + destruct (N.eqb_spec k k0) as [<- | _].
      * cbn [runs_denote sw_toList].
        replace (N.to_nat (1 + j)%N) with (S (N.to_nat j)) by lia.
        cbn [lpow]. rewrite Str_app_assoc. reflexivity.
      * cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
    + cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
Qed.

Definition pushS1 (n : N) (xs : Runs) : Runs :=
  match xs with
  | (SW_S m, j) :: ys =>
    if N.eqb n m then (SW_S m, (1 + j)%N) :: ys
    else (SW_S n, 1%N) :: xs
  | _ => (SW_S n, 1%N) :: xs
  end.

Lemma pushS1_spec n xs :
  runs_denote (pushS1 n xs) = S_word (N.to_nat n) *> runs_denote xs.
Proof.
  unfold pushS1.
  destruct xs as [|[v j] ys].
  - cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
  - destruct v; try (cbn [runs_denote sw_toList]; change (N.to_nat 1) with 1%nat; rewrite lpow_1; reflexivity).
    destruct (N.eqb_spec n n0) as [<- | _].
    + cbn [runs_denote sw_toList].
      replace (N.to_nat (1 + j)%N) with (S (N.to_nat j)) by lia.
      cbn [lpow]. rewrite Str_app_assoc. reflexivity.
    + cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
Qed.

Fixpoint put (xs ys : Runs) : Runs :=
  match xs with
  | [] => ys
  | (w, n) :: xs' => runs_push w n (put xs' ys)
  end.

Lemma put_plug xs ys t : plug (put xs ys) t = plug xs (plug ys t).
Proof.
  induction xs as [|[w n] xs IH]; cbn [put plug]; [reflexivity |].
  rewrite push_plug, IH. reflexivity.
Qed.

Lemma put_spec xs ys : runs_denote (put xs ys) = plug xs (runs_denote ys).
Proof.
  rewrite !denote_eq_plug_0inf. apply put_plug.
Qed.

Definition unpackDFHead (xs : Runs) : Runs :=
  match xs with
  | (SW_DF ds, N0) :: rest => rest
  | (SW_DF ds, Npos pk) :: rest =>
    let k' := N.pred (Npos pk) in
    let rest1 := if N.eqb k' 0 then rest else (SW_DF ds, k') :: rest in
    match ds with
    | [] => rest1
    | (n, kd) :: ds' =>
      let rest2 := match ds' with [] => rest1 | _ :: _ => (SW_DF ds', 1%N) :: rest1 end in
      runs_push (SW_D n) kd rest2
    end
  | _ => xs
  end.

Lemma opt_run_plug w k rest t :
  plug (if N.eqb k 0 then rest else (w, k) :: rest) t = (sw_toList w)^^(N.to_nat k) *> plug rest t.
Proof.
  destruct (N.eqb_spec k 0) as [-> | _]; reflexivity.
Qed.

Lemma opt_df_plug ds' rest1 t :
  plug (match ds' with [] => rest1 | _ :: _ => (SW_DF ds', 1%N) :: rest1 end) t =
  digitsToList ds' *> plug rest1 t.
Proof.
  destruct ds' as [|x xs]; [reflexivity |].
  cbn [plug sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity.
Qed.

Lemma unpackDFHead_plug xs t : plug (unpackDFHead xs) t = plug xs t.
Proof.
  destruct xs as [|[w [|pk]] rest]; try reflexivity.
  - destruct w; reflexivity.
  - destruct w as [| | | | | ds |]; try reflexivity.
    cbn [unpackDFHead plug sw_toList].
    rewrite pos_to_nat_succ. cbn [lpow].
    destruct ds as [|[n kd] ds'].
    + rewrite opt_run_plug; cbn [sw_toList digitsToList]. rewrite nil_lpow. reflexivity.
    + rewrite push_plug, opt_df_plug, opt_run_plug; cbn [sw_toList digitsToList].
      rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma unpackDFHead_spec xs : runs_denote (unpackDFHead xs) = runs_denote xs.
Proof. rewrite !denote_eq_plug_0inf. apply unpackDFHead_plug. Qed.

Definition unpackDHead (xs : Runs) : Runs :=
  match xs with
  | (SW_DF ds, k) :: rest => unpackDFHead ((SW_DF ds, k) :: rest)
  | (SW_DB ds, N0) :: rest => rest
  | (SW_DB ds, Npos pk) :: rest =>
    let k' := N.pred (Npos pk) in
    let rest1 := if N.eqb k' 0 then rest else (SW_DB ds, k') :: rest in
    match pushDRevAux ds [] with
    | [] => rest1
    | (n, kd) :: ds' =>
      let rest2 := match ds' with [] => rest1 | _ :: _ => (SW_DF ds', 1%N) :: rest1 end in
      runs_push (SW_D n) kd rest2
    end
  | _ => xs
  end.

Lemma unpackDHead_plug xs t : plug (unpackDHead xs) t = plug xs t.
Proof.
  destruct xs as [|[w [|pk]] rest]; try reflexivity.
  - destruct w; try reflexivity; apply unpackDFHead_plug.
  - destruct w as [| | | | | ds | ds]; try reflexivity.
    + apply unpackDFHead_plug.
    + cbn [unpackDHead plug sw_toList]. unfold digitsRevToList.
      rewrite pos_to_nat_succ. cbn [lpow].
      destruct (pushDRevAux ds []) as [|[n kd] ds'] eqn:Hrev.
      * rewrite opt_run_plug; cbn [sw_toList]. unfold digitsRevToList; rewrite Hrev.
        cbn [digitsToList]. rewrite nil_lpow. reflexivity.
      * rewrite push_plug, opt_df_plug, opt_run_plug; cbn [sw_toList].
        unfold digitsRevToList; rewrite Hrev; cbn [digitsToList].
        rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma unpackDHead_spec xs : runs_denote (unpackDHead xs) = runs_denote xs.
Proof. rewrite !denote_eq_plug_0inf. apply unpackDHead_plug. Qed.

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
  | (SW_DEF N0 N0, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    (0, runs_push (SW_raw [1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF 0 0) n xs')))
  | (SW_DEF N0 (Npos pk), Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    let k := N.pred (Npos pk) in
    (1, runs_push (SW_raw [1]) k (runs_push (SW_raw [0; 1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF 0 (Npos pk)) n xs'))))
  | (SW_DEF (Npos pa) k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    let a := N.pred (Npos pa) in
    (1, runs_push (SW_raw [0]) 1 (runs_push (SW_raw [1; 0]) a (runs_push (SW_raw [1]) k
          (runs_push (SW_raw [0; 1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF (Npos pa) k) n xs'))))))
  | (SW_DF ds, Npos p) :: xs' =>
    match popDList ds with
    | None => runs_pop xs'
    | Some (k, ds') =>
      let n := N.pred (Npos p) in
      let xs1 := if N.eqb n 0 then xs' else (SW_DF ds, n) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 xs2))
    end
  | (SW_DB ds, Npos p) :: xs' =>
    match popDList (pushDRevAux ds []) with
    | None => runs_pop xs'
    | Some (k, ds') =>
      let n := N.pred (Npos p) in
      let xs1 := if N.eqb n 0 then xs' else (SW_DB ds, n) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 xs2))
    end
  end.

Lemma runs_pop_spec xs :
  runs_denote xs = fst (runs_pop xs) >> runs_denote (snd (runs_pop xs)).
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_pop runs_denote].
  - cbn [fst snd runs_denote]. apply const_unfold.
  - destruct w as [[|] | | | | [|pa] [|pk] | |]; exact IH.
  - destruct w as [[|b rest] | k | k | k | [|pa] [|pk] | ds | ds].
    + cbn [runs_pop sw_toList]. rewrite nil_lpow. exact IH.
    + cbn [runs_pop fst snd sw_toList].
      rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + cbn [runs_pop fst snd sw_toList].
      rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app].
      unfold D_word. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + cbn [runs_pop fst snd sw_toList].
      rewrite !runs_push_spec, pos_to_nat_succ.
      cbn [sw_toList lpow app Str_app]. unfold S_word.
      replace (1 + N.to_nat k)%nat with (N.to_nat (1 + k)%N) by lia.
      rewrite ?Str_app_assoc. reflexivity.
    + cbn [runs_pop fst snd sw_toList].
      rewrite !runs_push_spec, pos_to_nat_succ.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      cbn [sw_toList lpow app Str_app]. unfold PL_word.
      replace (N.to_nat k + 4)%nat with (S (N.to_nat (k + 3)%N)) by lia.
      cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + cbn [runs_pop fst snd].
      rewrite !runs_push_spec; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + cbn [runs_pop fst snd].
      rewrite !runs_push_spec; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pk).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + cbn [runs_pop fst snd].
      rewrite !runs_push_spec; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pa).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + cbn [runs_pop fst snd].
      rewrite !runs_push_spec; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pa), ?(pos_to_nat_succ pk).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + cbn [runs_pop sw_toList].
      destruct (popDList ds) as [[k ds']|] eqn:Hpop.
      * cbn [fst snd]. rewrite !runs_push_spec, !denote_eq_plug_0inf, opt_df_plug, opt_run_plug.
        cbn [sw_toList]. rewrite (pos_to_nat_succ p). cbn [lpow].
        rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. unfold D_word.
        cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
    + cbn [runs_pop sw_toList]. unfold digitsRevToList.
      destruct (popDList (pushDRevAux ds [])) as [[k ds']|] eqn:Hpop.
      * cbn [fst snd]. rewrite !runs_push_spec, !denote_eq_plug_0inf, opt_df_plug, opt_run_plug.
        cbn [sw_toList]. unfold digitsRevToList. rewrite (pos_to_nat_succ p). cbn [lpow].
        rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. unfold D_word.
        cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
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
    destruct (runs_pop xs) as [c zs]; cbn [fst snd] in Hp.
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
  destruct w as [lw | | | | | |]; cbn; try discriminate.
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
  | (SW_DEF N0 N0, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    Some (0, runs_push (SW_raw [1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF 0 0) n xs')))
  | (SW_DEF N0 (Npos pk), Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    let k := N.pred (Npos pk) in
    Some (1, runs_push (SW_raw [1]) k (runs_push (SW_raw [0; 1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF 0 (Npos pk)) n xs'))))
  | (SW_DEF (Npos pa) k, Npos p) :: xs' =>
    let n := N.pred (Npos p) in
    let a := N.pred (Npos pa) in
    Some (1, runs_push (SW_raw [0]) 1 (runs_push (SW_raw [1; 0]) a (runs_push (SW_raw [1]) k
          (runs_push (SW_raw [0; 1]) 1 (runs_push (SW_S 0) 1 (runs_push (SW_DEF (Npos pa) k) n xs'))))))
  | (SW_DF ds, Npos p) :: xs' =>
    match popDList ds with
    | None => runs_popStrict xs'
    | Some (k, ds') =>
      let n := N.pred (Npos p) in
      let xs1 := if N.eqb n 0 then xs' else (SW_DF ds, n) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      Some (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 xs2))
    end
  | (SW_DB ds, Npos p) :: xs' =>
    match popDList (pushDRevAux ds []) with
    | None => runs_popStrict xs'
    | Some (k, ds') =>
      let n := N.pred (Npos p) in
      let xs1 := if N.eqb n 0 then xs' else (SW_DB ds, n) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      Some (1, runs_push (SW_raw [1; 1]) k (runs_push (SW_raw [0; 0]) 1 xs2))
    end
  end.

Lemma runs_popStrict_spec xs b ys t :
  runs_popStrict xs = Some (b, ys) -> plug xs t = b >> plug ys t.
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_popStrict plug].
  - discriminate.
  - destruct w as [[|] | | | | [|pa] [|pk] | |]; exact IH.
  - destruct w as [[|a rest] | k | k | k | [|pa] [|pk] | ds | ds]; cbn [runs_popStrict sw_toList].
    + rewrite nil_lpow. exact IH.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app].
      rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow app Str_app].
      unfold D_word. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      cbn [sw_toList lpow app Str_app]. unfold S_word.
      replace (1 + N.to_nat k)%nat with (N.to_nat (1 + k)%N) by lia.
      rewrite ?Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      cbn [sw_toList lpow app Str_app]. unfold PL_word.
      replace (N.to_nat k + 4)%nat with (S (N.to_nat (k + 3)%N)) by lia.
      cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pk).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pa).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + intros H; inversion H; subst; clear H.
      rewrite !push_plug; unfold sw_toList, DefWord.
      rewrite ?(pos_to_nat_succ p), ?(pos_to_nat_succ pa), ?(pos_to_nat_succ pk).
      change (N.to_nat 0) with 0%nat; change (N.to_nat 1) with 1%nat.
      cbn [lpow app Str_app]; rewrite ?app_nil_r, ?Str_app_assoc; cbn [Str_app]; rewrite ?Str_app_assoc; cbn [Str_app]; reflexivity.
    + destruct (popDList ds) as [[k ds']|] eqn:Hpop.
      * intros H; inversion H; subst; clear H.
        rewrite !push_plug, opt_df_plug, opt_run_plug, (pos_to_nat_succ p).
        cbn [sw_toList lpow]. rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. unfold D_word.
        cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
    + unfold digitsRevToList.
      destruct (popDList (pushDRevAux ds [])) as [[k ds']|] eqn:Hpop.
      * intros H; inversion H; subst; clear H.
        rewrite !push_plug, opt_df_plug, opt_run_plug, (pos_to_nat_succ p).
        cbn [sw_toList lpow]. unfold digitsRevToList.
        rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. unfold D_word.
        cbn [lpow app Str_app]. rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
Qed.

Lemma runs_popStrict_none xs t :
  runs_popStrict xs = None -> plug xs t = t.
Proof.
  induction xs as [|[w [|p]] xs IH]; cbn [runs_popStrict plug].
  - reflexivity.
  - destruct w as [[|] | | | | [|pa] [|pk] | |]; exact IH.
  - destruct w as [[|a rest] | | | | [|pa] [|pk] | ds | ds]; try discriminate.
    + cbn [sw_toList]. rewrite nil_lpow. exact IH.
    + destruct (popDList ds) as [[k ds']|] eqn:Hpop; [discriminate |].
      cbn [sw_toList]. rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
    + destruct (popDList (pushDRevAux ds [])) as [[k ds']|] eqn:Hpop; [discriminate |].
      cbn [sw_toList]. unfold digitsRevToList. rewrite (popDList_none_nil _ Hpop), nil_lpow. exact IH.
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
      | [] => takeOnesAux (acc + p * Npos pk)%N xs'
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
  | (SW_DEF _ _, Npos _) :: _ => (acc, xs)
  | (SW_DF ds, Npos pk) :: xs' =>
    match popDList ds with
    | None => takeOnesAux acc xs'
    | Some (n, ds') =>
      let k := N.pred (Npos pk) in
      let xs1 := if N.eqb k 0 then xs' else (SW_DF ds, k) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      ((acc + (2 * n + 1))%N, runs_push (SW_raw [0; 0]) 1 xs2)
    end
  | (SW_DB ds, Npos pk) :: xs' =>
    match popDList (pushDRevAux ds []) with
    | None => takeOnesAux acc xs'
    | Some (n, ds') =>
      let k := N.pred (Npos pk) in
      let xs1 := if N.eqb k 0 then xs' else (SW_DB ds, k) :: xs' in
      let xs2 := match ds' with [] => xs1 | _ :: _ => (SW_DF ds', 1%N) :: xs1 end in
      ((acc + (2 * n + 1))%N, runs_push (SW_raw [0; 0]) 1 xs2)
    end
  end.

Lemma takeOnesAux_spec acc xs t :
  [1]^^(N.to_nat acc) *> plug xs t =
    [1]^^(N.to_nat (fst (takeOnesAux acc xs))) *> plug (snd (takeOnesAux acc xs)) t.
Proof.
  gen acc. induction xs as [|[w [|pk]] xs IH]; intros acc; cbn [takeOnesAux plug].
  - reflexivity.
  - destruct w as [[|] | | | | | |]; exact (IH acc).
  - destruct w as [[|a rest] | n | n | n | a k0 | ds | ds]; cbn [sw_toList].
    + rewrite nil_lpow. exact (IH acc).
    + pose proof (splitOnesAux_spec 0 (a :: rest)) as Hsp.
      destruct (splitOnesAux 0 (a :: rest)) as [p tail]; cbn [fst snd] in Hsp.
      cbn [N.to_nat lpow app] in Hsp.
      destruct (N.eqb_spec p 0) as [-> | _]; [reflexivity |].
      destruct tail as [|b tail'].
      * rewrite ?app_nil_r in Hsp.
        rewrite Hsp, <- lpow_mul, lpow_Str_add.
        replace (N.to_nat acc + N.to_nat (Npos pk) * N.to_nat p)%nat
          with (N.to_nat (acc + p * Npos pk)%N) by lia.
        exact (IH (acc + p * Npos pk)%N).
      * cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
        change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow]. rewrite ?app_nil_r.
        rewrite Hsp at 1. rewrite ?Str_app_assoc, lpow_Str_add, <- N2Nat.inj_add.
        reflexivity.
    + cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
      change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow]. rewrite ?app_nil_r, Str_app_assoc.
      rewrite D_word_ones, lpow_Str_add.
      replace (N.to_nat acc + (2 * N.to_nat n + 1))%nat with (N.to_nat (acc + (2 * n + 1))%N) by lia.
      reflexivity.
    + cbn [fst snd]. rewrite !push_plug, pos_to_nat_succ.
      cbn [sw_toList lpow]. rewrite Str_app_assoc, S_word_ones, lpow_Str_add.
      replace (N.to_nat acc + 1)%nat with (N.to_nat (acc + 1)%N) by lia.
      replace (1 + N.to_nat n)%nat with (N.to_nat (1 + n)%N) by lia.
      reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct (popDList ds) as [[n ds']|] eqn:Hpop.
      * cbn [fst snd]. rewrite push_plug, opt_df_plug, opt_run_plug, pos_to_nat_succ.
        cbn [sw_toList lpow]. rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. rewrite lpow_1, !Str_app_assoc, D_word_ones, lpow_Str_add.
        replace (N.to_nat acc + (2 * N.to_nat n + 1))%nat with (N.to_nat (acc + (2 * n + 1))%N) by lia.
        reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact (IH acc).
    + unfold digitsRevToList.
      destruct (popDList (pushDRevAux ds [])) as [[n ds']|] eqn:Hpop.
      * cbn [fst snd]. rewrite push_plug, opt_df_plug, opt_run_plug, pos_to_nat_succ.
        cbn [sw_toList lpow]. unfold digitsRevToList. rewrite (popDList_digitsToList _ _ _ Hpop).
        change (N.to_nat 1) with 1%nat. rewrite lpow_1, !Str_app_assoc, D_word_ones, lpow_Str_add.
        replace (N.to_nat acc + (2 * N.to_nat n + 1))%nat with (N.to_nat (acc + (2 * n + 1))%N) by lia.
        reflexivity.
      * rewrite (popDList_none_nil _ Hpop), nil_lpow. exact (IH acc).
Qed.

Definition takeOnes (xs : Runs) : N * Runs := takeOnesAux 0 xs.

Lemma takeOnes_spec xs t :
  plug xs t = [1]^^(N.to_nat (fst (takeOnes xs))) *> plug (snd (takeOnes xs)) t.
Proof. exact (takeOnesAux_spec 0 xs t). Qed.

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
  let q := (N.div2 c1) in
  let ys' := if (mod2_1 c1) then runs_push (SW_raw [1]) 1 ys else ys in
  (q, ys').

Lemma take11_spec xs t :
  plug xs t = [1; 1]^^(N.to_nat (fst (take11 xs))) *> plug (snd (take11 xs)) t.
Proof.
  unfold take11.
  pose proof (takeOnes_spec xs t) as H1.
  destruct (takeOnes xs) as [c1 ys]; cbn [fst snd] in H1 |- *.
  rewrite N.div2_div, mod2_1_eq.
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
  destruct w as [lw | | | | | |]; cbn [take10Fuel]; try reflexivity.
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
  destruct xs as [|[[w1| | | | | |] k1] [|[[w2| | | | | |] k2'] rest]]; cbn [peelZeroTen]; try discriminate.
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
      else if beqListSym w [0; 1; 0; 1] then take01Fuel fuel' (acc + mul2 k)%N rest
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
  destruct w as [lw | | | | | |]; cbn [take01Fuel]; try reflexivity.
  destruct (beqListSym lw [0; 1]) eqn:H01.
  - rewrite <- IH. cbn [runs_denote sw_toList].
    rewrite (beqListSym_eq _ _ H01), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
    reflexivity.
  - destruct (beqListSym lw [0; 1; 0; 1]) eqn:H0101.
    + rewrite <- IH, mul2_eq. cbn [runs_denote sw_toList].
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
        let q := (N.div2 k) in
        let rest' := if (mod2_1 k) then runs_push (SW_raw [0; 1]) 1 rest else rest in
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
  destruct w as [lw | | | | | |]; cbn [take0101StrictFuel]; try reflexivity.
  destruct (beqListSym lw [0; 1; 0; 1]) eqn:H0101.
  - rewrite <- IH. cbn [plug sw_toList].
    rewrite (beqListSym_eq _ _ H0101), <- Str_app_assoc, <- lpow_add, <- N2Nat.inj_add.
    reflexivity.
  - destruct (if beqListSym lw [0; 1] then N.leb 2 k else false) eqn:H01.
    + destruct (beqListSym lw [0; 1]) eqn:Hlw; [| discriminate].
      rewrite <- IH, N.div2_div, mod2_1_eq. cbn [plug sw_toList].
      rewrite (beqListSym_eq _ _ Hlw).
      destruct (N_div_mod_nat k 2 ltac:(lia)) as [Hdiv Hmod].
      change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
      destruct (N.eqb_spec (k mod 2) 1) as [Hm1 | Hm1].
      * rewrite push_plug, N2Nat.inj_add, lpow_add, Str_app_assoc.
        rewrite <- (zero_one_pow_two_mul (N.to_nat (k / 2))).
        f_equal. cbn [sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
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
  let xs0 := unpackDHead xs in
  match xs0 with
  | (SW_D n, Npos pk) :: rest => Some (n, runs_push (SW_D n) (N.pred (Npos pk)) rest)
  | (SW_raw (b :: _), Npos _) :: _ =>
    if sym_eqb b 1 then
      let '(c1, ys) := takeOnes xs0 in
      if (mod2_1 c1) then
        match runs_remove [0; 0] ys with
        | Some zs => Some ((N.div2 c1), zs)
        | None => None
        end
      else None
    else None
  | _ => None
  end.

Lemma takeD_spec xs n ys :
  takeD xs = Some (n, ys) -> runs_denote xs = D_word (N.to_nat n) *> runs_denote ys.
Proof.
  unfold takeD. rewrite <- (unpackDHead_spec xs).
  generalize (unpackDHead xs) as xs0; clear xs; intros xs.
  destruct xs as [|[w [|pk]] rest]; try discriminate.
  - destruct w as [[|] | | | | | |]; discriminate.
  - destruct w as [[|b l'] | m | | | | |]; try discriminate.
    + destruct (sym_eqb b 1); [| discriminate].
      pose proof (takeOnes_spec ((SW_raw (b :: l'), Npos pk) :: rest) 0inf) as H1.
      rewrite <- !denote_eq_plug_0inf in H1.
      destruct (takeOnes ((SW_raw (b :: l'), Npos pk) :: rest)) as [c1 mid]; cbn [fst snd] in H1.
      rewrite mod2_1_eq, N.div2_div.
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
      if (mod2_1 c1) then
        match runs_removeStrict [0; 0] ys with
        | Some zs => Some ((N.div2 c1), zs)
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
  - destruct w as [[|] | | | | | |]; discriminate.
  - destruct w as [[|b l'] | m | | | | |]; try discriminate.
    + destruct (sym_eqb b 1); [| discriminate].
      pose proof (takeOnes_spec ((SW_raw (b :: l'), Npos pk) :: rest) t) as H1.
      destruct (takeOnes ((SW_raw (b :: l'), Npos pk) :: rest)) as [c1 mid]; cbn [fst snd] in H1.
      rewrite mod2_1_eq, N.div2_div.
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
  destruct w as [lw | | m | | | |]; try discriminate.
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

Definition flushDBack (db : Digits) (rt : Runs) : Runs :=
  match db with
  | [] => rt
  | [(n0, k0)] => runs_push (SW_D n0) k0 rt
  | [(n1, k1); (n0, k0)] => runs_push (SW_D n0) k0 (runs_push (SW_D n1) k1 rt)
  | _ => (SW_DB db, 1%N) :: rt
  end.

Lemma flushDBack_spec db rt :
  runs_denote (flushDBack db rt) = denDRev db (runs_denote rt).
Proof.
  destruct db as [|[n0 k0] [|[n1 k1] [|p3 rest]]].
  - reflexivity.
  - cbn [flushDBack denDRev]. rewrite runs_push_spec. reflexivity.
  - cbn [flushDBack denDRev]. rewrite !runs_push_spec. reflexivity.
  - cbn [flushDBack runs_denote sw_toList]. change (N.to_nat 1) with 1%nat.
    rewrite lpow_1, digitsRevToList_plug. reflexivity.
Qed.

Definition flushDFront (df : Digits) (rt : Runs) : Runs :=
  match df with
  | [] => rt
  | [(n0, k0)] => runs_push (SW_D n0) k0 rt
  | [(n1, k1); (n2, k2)] => runs_push (SW_D n1) k1 (runs_push (SW_D n2) k2 rt)
  | (n1, k1) :: (n2, k2) :: rest =>
    runs_push (SW_D n1) k1 (runs_push (SW_D n2) k2 ((SW_DF rest, 1%N) :: rt))
  end.

Lemma flushDFront_spec df rt :
  runs_denote (flushDFront df rt) = denD df (runs_denote rt).
Proof.
  destruct df as [|[n1 k1] [|[n2 k2] [|p3 rest]]].
  - reflexivity.
  - cbn [flushDFront denD]. rewrite runs_push_spec. reflexivity.
  - cbn [flushDFront denD]. rewrite !runs_push_spec. reflexivity.
  - cbn [flushDFront denD]. rewrite !runs_push_spec.
    cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat.
    rewrite lpow_1, digitsToList_plug. reflexivity.
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
  destruct w as [| n | | | | |]; cbn [absorbRawD]; try reflexivity.
  pose proof (IH df) as H.
  destruct (absorbRawD rest df) as [[|x xs] df']; cbn [fst snd plug sw_toList] in H |- *.
  - rewrite denD_pushD, H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Fixpoint leLen (n : nat) (ds : Digits) : bool :=
  match ds with
  | [] => true
  | _ :: xs =>
    match n with
    | O => false
    | S n' => leLen n' xs
    end
  end.

Fixpoint appendDigits (xs ys : Digits) : Digits :=
  match xs with
  | [] => ys
  | (n, k) :: xs' => pushD n k (appendDigits xs' ys)
  end.

Lemma denD_appendDigits xs ys t :
  denD (appendDigits xs ys) t = denD xs (denD ys t).
Proof.
  induction xs as [|[n k] xs IH]; cbn [appendDigits denD]; [reflexivity |].
  rewrite denD_pushD, IH. reflexivity.
Qed.

Fixpoint absorbTailFast (df db : Digits) (rt : Runs) : Digits * Digits * Runs :=
  match rt with
  | (SW_D n, k) :: rest => absorbTailFast df (pushD n k db) rest
  | (SW_DF df2, k) :: rest =>
    if N.eqb k 1 then
      match df, db with
      | [], [] => absorbTailFast df2 [] rest
      | _, _ =>
        if andb (leLen 16 df) (leLen 16 db) then
          let df' := appendDigits df (appendDigits (pushDRevAux db []) df2) in
          absorbTailFast df' [] rest
        else (df, db, (SW_DF df2, 1%N) :: rest)
      end
    else (df, db, rt)
  | (SW_DB db2, k) :: rest =>
    if N.eqb k 1 then
      match db with
      | [] => absorbTailFast df db2 rest
      | _ :: _ =>
        if andb (leLen 16 df) (leLen 16 db) then
          let df' := appendDigits df (pushDRevAux db []) in
          absorbTailFast df' db2 rest
        else (df, db, (SW_DB db2, 1%N) :: rest)
      end
    else (df, db, rt)
  | _ => (df, db, rt)
  end.

Lemma absorbTailFast_spec df db rt :
  let '(df', db', rt') := absorbTailFast df db rt in
  denD df' (denDRev db' (runs_denote rt')) = denD df (denDRev db (runs_denote rt)).
Proof.
  gen df db. induction rt as [|[w k] rest IH]; intros df db; [reflexivity |].
  destruct w as [| n | | | | df2 | db2]; cbn [absorbTailFast]; try reflexivity.
  - pose proof (IH df (pushD n k db)) as H.
    destruct (absorbTailFast df (pushD n k db) rest) as [[df' db'] rt'].
    rewrite H, denDRev_pushD. reflexivity.
  - destruct (N.eqb_spec k 1) as [-> | _]; [| reflexivity].
    destruct df as [|a df0], db as [|b db0].
    + pose proof (IH df2 [] ) as H.
      destruct (absorbTailFast df2 [] rest) as [[df' db'] rt'].
      rewrite H. cbn [denD denDRev runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsToList_plug. reflexivity.
    + destruct (andb (leLen 16 []) (leLen 16 (b :: db0))); [| reflexivity].
      pose proof (IH (appendDigits [] (appendDigits (pushDRevAux (b :: db0) []) df2)) []) as H.
      destruct (absorbTailFast (appendDigits [] (appendDigits (pushDRevAux (b :: db0) []) df2)) [] rest) as [[df' db'] rt'].
      rewrite H, !denD_appendDigits, denD_pushDRevAux.
      cbn [denD denDRev runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsToList_plug. reflexivity.
    + destruct (andb (leLen 16 (a :: df0)) (leLen 16 [])); [| reflexivity].
      pose proof (IH (appendDigits (a :: df0) (appendDigits (pushDRevAux [] []) df2)) []) as H.
      destruct (absorbTailFast (appendDigits (a :: df0) (appendDigits (pushDRevAux [] []) df2)) [] rest) as [[df' db'] rt'].
      rewrite H, !denD_appendDigits, denD_pushDRevAux.
      cbn [denD denDRev runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsToList_plug. reflexivity.
    + destruct (andb (leLen 16 (a :: df0)) (leLen 16 (b :: db0))); [| reflexivity].
      pose proof (IH (appendDigits (a :: df0) (appendDigits (pushDRevAux (b :: db0) []) df2)) []) as H.
      destruct (absorbTailFast (appendDigits (a :: df0) (appendDigits (pushDRevAux (b :: db0) []) df2)) [] rest) as [[df' db'] rt'].
      rewrite H, !denD_appendDigits, denD_pushDRevAux.
      cbn [denD denDRev runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsToList_plug. reflexivity.
  - destruct (N.eqb_spec k 1) as [-> | _]; [| reflexivity].
    destruct db as [|b db0].
    + pose proof (IH df db2) as H.
      destruct (absorbTailFast df db2 rest) as [[df' db'] rt'].
      rewrite H. cbn [denDRev runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsRevToList_plug. reflexivity.
    + destruct (andb (leLen 16 df) (leLen 16 (b :: db0))); [| reflexivity].
      pose proof (IH (appendDigits df (pushDRevAux (b :: db0) [])) db2) as H.
      destruct (absorbTailFast (appendDigits df (pushDRevAux (b :: db0) [])) db2 rest) as [[df' db'] rt'].
      rewrite H, denD_appendDigits, denD_pushDRevAux.
      cbn [denD runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, digitsRevToList_plug. reflexivity.
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
  let '(df2, db2, rt1) :=
    match rr1 with
    | [] => absorbTailFast df1 (d_back rt) (r_tail rt)
    | _ :: _ => (df1, d_back rt, r_tail rt)
    end in
  let rt2 := cleanTailZeros rt1 in
  match df2, db2, rr1 with
  | [], [], _ :: _ =>
    let rt3 := put rr1 rt2 in
    let '(df4, db4, rt4) := absorbTailFast [] [] rt3 in
    MkRTape [] df4 db4 (cleanTailZeros rt4)
  | _, _, _ => MkRTape rr1 df2 db2 rt2
  end.

Lemma normRTape_spec rt : rt_denote (normRTape rt) = rt_denote rt.
Proof.
  unfold normRTape.
  pose proof (absorbRawD_spec (r_raw rt) (d_front rt) (denDRev (d_back rt) (runs_denote (r_tail rt)))) as Ha1.
  destruct (absorbRawD (r_raw rt) (d_front rt)) as [rr1 df1]; cbn [fst snd] in Ha1.
  change (plug (r_raw rt) (denD (d_front rt) (denDRev (d_back rt) (runs_denote (r_tail rt))))) with (rt_denote rt) in Ha1.
  destruct rr1 as [|x xs].
  - pose proof (absorbTailFast_spec df1 (d_back rt) (r_tail rt)) as Ha2.
    destruct (absorbTailFast df1 (d_back rt) (r_tail rt)) as [[df2 db2] rt1].
    destruct df2, db2; unfold rt_denote; cbn [r_raw d_front d_back r_tail plug];
      rewrite cleanTailZeros_spec, Ha2; exact Ha1.
  - destruct df1 as [|y ys].
    + destruct (d_back rt) as [|z zs] eqn:Hdb.
      * pose proof (absorbTailFast_spec [] [] (put (x :: xs) (cleanTailZeros (r_tail rt)))) as Ha4.
        destruct (absorbTailFast [] [] (put (x :: xs) (cleanTailZeros (r_tail rt)))) as [[df4 db4] rt4].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
        rewrite cleanTailZeros_spec, Ha4; cbn [denD denDRev].
        rewrite put_spec, cleanTailZeros_spec.
        cbn [denD denDRev] in Ha1. exact Ha1.
      * unfold rt_denote; cbn [r_raw d_front d_back r_tail].
        rewrite cleanTailZeros_spec. exact Ha1.
    + unfold rt_denote; cbn [r_raw d_front d_back r_tail].
      rewrite cleanTailZeros_spec. exact Ha1.
Qed.

Fixpoint splitHalfAux (fast slow acc : Digits) : Digits * Digits :=
  match fast, slow with
  | _ :: _ :: fast', x :: slow' => splitHalfAux fast' slow' (x :: acc)
  | _, _ => (rev_append acc [], rev_append slow [])
  end.

Lemma splitHalfAux_denDRev slow fast acc t :
  denDRev (rev_append acc slow) t =
  denD (snd (splitHalfAux fast slow acc)) (denDRev (fst (splitHalfAux fast slow acc)) t).
Proof.
  gen fast acc. induction slow as [|x slow IH]; intros fast acc.
  - destruct fast as [|a [|b fast']]; reflexivity.
  - destruct fast as [|a [|b fast']]; cbn [splitHalfAux fst snd].
    + rewrite (rev_append_eq acc (x :: slow)), denDRev_app, denD_rev_append_nil. reflexivity.
    + rewrite (rev_append_eq acc (x :: slow)), denDRev_app, denD_rev_append_nil. reflexivity.
    + exact (IH fast' (x :: acc)).
Qed.

Lemma splitHalfAux_denD slow fast acc t :
  denD (rev_append acc slow) t =
  denD (fst (splitHalfAux fast slow acc)) (denDRev (snd (splitHalfAux fast slow acc)) t).
Proof.
  gen fast acc. induction slow as [|x slow IH]; intros fast acc.
  - destruct fast as [|a [|b fast']]; reflexivity.
  - destruct fast as [|a [|b fast']]; cbn [splitHalfAux fst snd].
    + rewrite (rev_append_eq acc (x :: slow)), denD_app, denDRev_rev_append_nil. reflexivity.
    + rewrite (rev_append_eq acc (x :: slow)), denD_app, denDRev_rev_append_nil. reflexivity.
    + exact (IH fast' (x :: acc)).
Qed.

Definition popDFrontOneAux (df db : Digits) : option (N * Digits * Digits) :=
  match popDList df with
  | Some (n, df') => Some (n, df', db)
  | None =>
    match db with
    | [] => None
    | _ :: _ =>
      let '(keep, rev_slow) := splitHalfAux db db [] in
      match popDList rev_slow with
      | Some (n, df') => Some (n, df', keep)
      | None =>
        match popDList (rev_append keep []) with
        | Some (n, df') => Some (n, df', [])
        | None => None
        end
      end
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
  - rewrite (popDList_denD_none df _ H1).
    destruct db as [|b db0]; [discriminate |].
    pose proof (splitHalfAux_denDRev (b :: db0) (b :: db0) [] t) as Hsp.
    cbn [rev_append] in Hsp.
    destruct (splitHalfAux (b :: db0) (b :: db0) []) as [keep rev_slow]; cbn [fst snd] in Hsp.
    rewrite Hsp.
    destruct (popDList rev_slow) as [[m df1]|] eqn:H2.
    + intros H; inversion H; subst; clear H.
      exact (popDList_denD rev_slow _ _ _ H2).
    + rewrite (popDList_denD_none rev_slow _ H2), <- denD_rev_append_nil.
      destruct (popDList (rev_append keep [])) as [[m df1]|] eqn:H3; [| discriminate].
      intros H; inversion H; subst; clear H.
      exact (popDList_denD _ _ _ t H3).
Qed.

Lemma popDFrontOneAux_none df db t :
  popDFrontOneAux df db = None -> denD df (denDRev db t) = t.
Proof.
  unfold popDFrontOneAux.
  destruct (popDList df) as [[m df1]|] eqn:H1; [discriminate |].
  rewrite (popDList_denD_none df _ H1).
  destruct db as [|b db0]; [reflexivity |].
  pose proof (splitHalfAux_denDRev (b :: db0) (b :: db0) [] t) as Hsp.
  cbn [rev_append] in Hsp.
  destruct (splitHalfAux (b :: db0) (b :: db0) []) as [keep rev_slow]; cbn [fst snd] in Hsp.
  rewrite Hsp.
  destruct (popDList rev_slow) as [[m df1]|] eqn:H2; [discriminate |].
  rewrite (popDList_denD_none rev_slow _ H2), <- denD_rev_append_nil.
  destruct (popDList (rev_append keep [])) as [[m df1]|] eqn:H3; [discriminate |].
  intros _. exact (popDList_denD_none _ t H3).
Qed.

Definition popDBackOneAux (df db : Digits) : option (N * Digits * Digits) :=
  match popDList db with
  | Some (n, db') => Some (n, df, db')
  | None =>
    match df with
    | [] => None
    | _ :: _ =>
      let '(keep, rev_slow) := splitHalfAux df df [] in
      match popDList rev_slow with
      | Some (n, db') => Some (n, keep, db')
      | None =>
        match popDList (rev_append keep []) with
        | Some (n, db') => Some (n, [], db')
        | None => None
        end
      end
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
  - rewrite (popDList_denDRev_none db t H1).
    destruct df as [|a df0]; [discriminate |].
    pose proof (splitHalfAux_denD (a :: df0) (a :: df0) [] t) as Hsp.
    cbn [rev_append] in Hsp.
    destruct (splitHalfAux (a :: df0) (a :: df0) []) as [keep rev_slow]; cbn [fst snd] in Hsp.
    rewrite Hsp.
    destruct (popDList rev_slow) as [[m db1]|] eqn:H2.
    + intros H; inversion H; subst; clear H.
      rewrite (popDList_denDRev rev_slow _ _ t H2). reflexivity.
    + rewrite (popDList_denDRev_none rev_slow t H2), <- denDRev_rev_append_nil.
      destruct (popDList (rev_append keep [])) as [[m db1]|] eqn:H3; [| discriminate].
      intros H; inversion H; subst; clear H.
      exact (popDList_denDRev _ _ _ t H3).
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
  unfold sweepDBack. rewrite <- denD_rev_append_nil. apply sweepDFront_spec.
Qed.

Definition sweepRight (l : Runs) (df db : Digits) : Runs :=
  sweepDBack (sweepDFront l df) db.

Lemma sweepRight_spec l df db t :
  CfgR (runs_denote l) (denD df (denDRev db t)) -->* CfgR (runs_denote (sweepRight l df db)) t.
Proof.
  eapply ev_trans; [apply sweepDFront_spec | apply sweepDBack_spec].
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
  | (SW_DEF N0 N0, Npos _) :: _ => Some 0
  | (SW_DF [], Npos _) :: xs' => peekFirstBitRuns xs'
  | (SW_DB [], Npos _) :: xs' => peekFirstBitRuns xs'
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
  destruct w as [lw | | | | | |]; cbn [peelRawD]; try reflexivity.
  destruct (takeD ((SW_raw lw, k) :: rest)) as [[n ys]|] eqn:Ht; [| reflexivity].
  rewrite runs_push_spec, IH.
  change (N.to_nat 1) with 1%nat. cbn [sw_toList lpow]. rewrite ?app_nil_r.
  symmetry. exact (takeD_spec _ _ _ Ht).
Qed.

Definition normImmTail (xs : Runs) : Runs :=
  match xs with
  | (SW_raw w, k) :: rest =>
    if (if beqListSym w [1; 0] then N.eqb k 1 else false) then
      match rest with
      | (SW_raw _, _) :: _ => runs_push (SW_raw [1; 0]) 1 (peelRawD 4 rest)
      | (SW_DF _, _) :: _ => runs_push (SW_raw [1; 0]) 1 (unpackDHead rest)
      | (SW_DB _, _) :: _ => runs_push (SW_raw [1; 0]) 1 (unpackDHead rest)
      | _ => xs
      end
    else xs
  | _ => xs
  end.

Lemma normImmTail_spec xs : runs_denote (normImmTail xs) = runs_denote xs.
Proof.
  destruct xs as [|[w k] rest]; [reflexivity |].
  destruct w as [lw | | | | | |]; cbn [normImmTail]; try reflexivity.
  destruct (beqListSym lw [1; 0]) eqn:Hw; [| reflexivity].
  destruct (N.eqb_spec k 1) as [-> | _]; [| reflexivity].
  destruct rest as [|[w2 k2] rest2]; [reflexivity |].
  destruct w2 as [lw2 | | | | | ds | ds]; try reflexivity.
  - rewrite runs_push_spec, peelRawD_spec.
    cbn [runs_denote sw_toList]. rewrite (beqListSym_eq _ _ Hw). reflexivity.
  - rewrite runs_push_spec, unpackDHead_spec.
    cbn [runs_denote sw_toList]. rewrite (beqListSym_eq _ _ Hw). reflexivity.
  - rewrite runs_push_spec, unpackDHead_spec.
    cbn [runs_denote sw_toList]. rewrite (beqListSym_eq _ _ Hw). reflexivity.
Qed.

(* ========================================================================== *)
(* Section 4: FastState, stepFast, run_pow & Soundness                        *)
(* ========================================================================== *)

Lemma opt_run_denote w k rest :
  runs_denote (if N.eqb k 0 then rest else (w, k) :: rest) =
  (sw_toList w)^^(N.to_nat k) *> runs_denote rest.
Proof. rewrite !denote_eq_plug_0inf. apply opt_run_plug. Qed.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof. congruence. Qed.

Lemma triple_inj {A B C} {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} :
  (a1, b1, c1) = (a2, b2, c2) -> a1 = a2 /\ b1 = b2 /\ c1 = c2.
Proof. intros H; repeat split; congruence. Qed.

Lemma quad_inj {A B C D} {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} :
  (a1, b1, c1, d1) = (a2, b2, c2, d2) -> a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2.
Proof. intros H; repeat split; congruence. Qed.

Lemma quint_inj {A B C D E} {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D} {e1 e2 : E} :
  (a1, b1, c1, d1, e1) = (a2, b2, c2, d2, e2) ->
  a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2 /\ e1 = e2.
Proof. intros H; repeat split; congruence. Qed.

Ltac inj_some H := cbv beta iota zeta in H; apply some_inj in H; subst.
Ltac inj_triple H := cbv beta iota zeta in H; destruct (triple_inj H) as [<- [<- <-]]; clear H.
Ltac inj_quad H := cbv beta iota zeta in H; destruct (quad_inj H) as [<- [<- [<- <-]]]; clear H.
Ltac inj_quint H := cbv beta iota zeta in H; destruct (quint_inj H) as [<- [<- [<- [<- <-]]]]; clear H.

Lemma N_div_mod_3 (x : N) :
  N.to_nat x = (3 * N.to_nat (x / 3)%N + N.to_nat (x mod 3)%N)%nat /\
  (N.to_nat (x mod 3)%N < 3)%nat /\
  N.to_nat (x / 3)%N = (N.to_nat x / 3)%nat /\
  N.to_nat (x mod 3)%N = (N.to_nat x mod 3)%nat.
Proof.
  destruct (N_div_mod_nat x 3 ltac:(lia)) as [Hdiv Hmod].
  change (N.to_nat 3) with 3%nat in Hdiv, Hmod.
  assert (HdivN : (N.to_nat x = 3 * (N.to_nat x / 3) + N.to_nat x mod 3)%nat)
    by (apply Nat.div_mod; lia).
  assert (HmodN : (N.to_nat x mod 3 < 3)%nat)
    by (apply Nat.mod_upper_bound; lia).
  lia.
Qed.

Lemma leftS_run n k l r :
  CfgL ((S_word n)^^k *> l) r -->* CfgL l ((D_word n)^^k *> r).
Proof.
  revert r. induction k as [|k IH]; intros r; [apply evstep_refl |].
  cbn [lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_left |].
  eapply ev_trans; [apply IH |].
  rewrite lpow_Str_app_comm, <- Str_app_assoc. apply evstep_refl.
Qed.

Lemma leftJ_S_run n k l r :
  CfgJ ((S_word n)^^(1 + k) *> l) r -->*
  CfgL l ((D_word n)^^k *> D_word (1 + n) *> r).
Proof.
  cbn [Nat.add lpow]. rewrite Str_app_assoc.
  eapply ev_trans; [apply rule_leftJ |].
  apply leftS_run.
Qed.

Lemma iter_succ_r {A} (f : A -> A) n x :
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  induction n as [|n IH]; [reflexivity | exact (f_equal f IH)].
Qed.

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
        destruct w as [lw | | | | | |]; try apply stepRawA0Scan_spec.
        destruct (beqListSym lw [1]) eqn:Hw1; [| apply stepRawA0Scan_spec].
        cbn [fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev runs_denote sw_toList].
        rewrite (beqListSym_eq _ _ Hw1), runs_push_spec. cbn [sw_toList].
        apply ones.
      * destruct w as [lw | | | | | |]; try apply stepRawA0Scan_spec.
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

Definition doCallsDSlow (df db : Digits) (rtail : Runs) (h : N) (allowDefect : bool)
    : option (N * Digits * Digits * Runs) :=
  let rtail1 := normImmTail (cleanTailZeros rtail) in
  match rtail1 with
  | [] => Some (h, df, pushD 0 (mul2 h) db, [])
  | (SW_raw w1, k1) :: (SW_D dn, kd) :: rest =>
    if (if beqListSym w1 [1; 0] then N.eqb k1 1 else false) then
      if N.eqb dn 0 then
        if N.leb 2 kd then
          match popDBackOneAux df db with
          | Some (j, df1, db1) =>
            let avail := (N.div2 kd) in
            let hd := if N.leb h avail then h else avail in
            let rem := (kd - mul2 hd)%N in
            Some (hd, df1, pushD 3 hd (pushD j 1 db1),
                  runs_push (SW_raw [1; 0]) 1 (runs_push (SW_D 0) rem rest))
          | None => None
          end
        else if (if allowDefect then N.eqb kd 1 else false) then
          match takeD rest with
          | Some (m, rest') =>
            match popDBackOneAux df db with
            | Some (j, df1, db1) =>
              Some (1%N, df1, pushD (m + 3)%N 1 (pushD j 1 db1),
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

Lemma doCallsDSlow_spec df db rtail h allowDefect hd df' db' rtail' :
  h <> 0%N ->
  doCallsDSlow df db rtail h allowDefect = Some (hd, df', db', rtail') ->
  (0 < N.to_nat hd)%nat /\ (N.to_nat hd <= N.to_nat h)%nat /\
  calls (N.to_nat hd)
    (denD df (denDRev db (runs_denote rtail)))
    (denD df' (denDRev db' (runs_denote rtail'))).
Proof.
  intros Hh0. unfold doCallsDSlow.
  rewrite <- (cleanTailZeros_spec rtail), <- (normImmTail_spec (cleanTailZeros rtail)).
  generalize (normImmTail (cleanTailZeros rtail)) as rt1; intros rt1.
  destruct rt1 as [|[w1 k1] rest1].
  - intros H; inversion H; subst hd df' db' rtail'; clear H.
    split; [lia |]. split; [lia |].
    rewrite denDRev_pushD, mul2_eq. cbn [runs_denote].
    replace (N.to_nat (h * 2)%N) with (N.to_nat h * 2)%nat by lia.
    exact (calls_denD df (calls_denDRev db (calls_blank (N.to_nat h)))).
  - destruct w1 as [lw1 | | | | | |]; try discriminate.
    destruct rest1 as [|[w2 kd] rest]; try discriminate.
    destruct w2 as [| dn | | | | |]; try discriminate.
    destruct (beqListSym lw1 [1; 0]) eqn:Hlw1; [| discriminate].
    destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
    apply beqListSym_eq in Hlw1; subst lw1.
    destruct (N.eqb_spec dn 0) as [-> | Hdn0].
    + destruct (N.leb_spec 2 kd) as [Hkd2 | Hkd2].
      * destruct (popDBackOneAux df db) as [[[j df1] db1]|] eqn:Hpop; [| discriminate].
        rewrite N.div2_div.
        intros H; inversion H; subst hd df' db' rtail'; clear H.
        rewrite mul2_eq.
        destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
        change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
        set (avail := (kd / 2)%N) in *.
        set (hd0 := if N.leb h avail then h else avail) in *.
        assert (Hhd_pos : (0 < N.to_nat hd0)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
        assert (Hhd_le_h : (N.to_nat hd0 <= N.to_nat h)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
        assert (Hhd_le_av : (N.to_nat hd0 <= N.to_nat avail)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
        split; [exact Hhd_pos |]. split; [exact Hhd_le_h |].
        rewrite (popDBackOneAux_spec df db j df1 db1 _ Hpop).
        rewrite !denDRev_pushD, !runs_push_spec.
        change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
        change (N.to_nat 2) with 2%nat. change (N.to_nat 3) with 3%nat.
        cbn [runs_denote sw_toList]. rewrite !lpow_1.
        replace (N.to_nat kd) with ((1 + N.to_nat (hd0 - 1)%N) * 2 + N.to_nat (kd - hd0 * 2)%N)%nat by lia.
        rewrite lpow_add, Str_app_assoc.
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
        replace (N.to_nat (m + 3)%N) with (3 + N.to_nat m)%nat by lia.
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

Definition doCallsD (df db : Digits) (rtail : Runs) (h : N) (allowDefect : bool)
    : option (N * Digits * Digits * Runs) :=
  if N.eqb h 0 then None
  else
    match rtail with
    | [] => Some (h, df, pushD 0 (mul2 h) db, [])
    | (SW_raw w1, k1) :: (SW_D dn, kd) :: rest =>
      if (if beqListSym w1 [1; 0] then if N.eqb k1 1 then if N.eqb dn 0 then N.leb 2 kd else false else false else false) then
        match popDBackOneAux df db with
        | Some (j, df1, db1) =>
          let avail := (N.div2 kd) in
          let hd := if N.leb h avail then h else avail in
          let rem := (kd - mul2 hd)%N in
          let rtail' :=
            if N.eqb rem 0 then runs_push (SW_raw [1; 0]) 1 (unpackDFHead rest)
            else (SW_raw [1; 0], 1%N) :: (SW_D 0, rem) :: rest in
          Some (hd, df1, pushD 3 hd (pushD j 1 db1), rtail')
        | None => None
        end
      else doCallsDSlow df db rtail h allowDefect
    | _ => doCallsDSlow df db rtail h allowDefect
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
  destruct rtail as [|[w1 k1] rest1].
  - intros H; inversion H; subst hd df' db' rtail'; clear H.
    split; [lia |]. split; [lia |].
    rewrite denDRev_pushD, mul2_eq. cbn [runs_denote].
    replace (N.to_nat (h * 2)%N) with (N.to_nat h * 2)%nat by lia.
    exact (calls_denD df (calls_denDRev db (calls_blank (N.to_nat h)))).
  - destruct w1 as [lw1 | | | | | |]; try (apply (doCallsDSlow_spec _ _ _ _ _ _ _ _ _ Hh0)).
    destruct rest1 as [|[w2 kd] rest]; try (apply (doCallsDSlow_spec _ _ _ _ _ _ _ _ _ Hh0)).
    destruct w2 as [| dn | | | | |]; try (apply (doCallsDSlow_spec _ _ _ _ _ _ _ _ _ Hh0)).
    destruct (if beqListSym lw1 [1; 0] then if N.eqb k1 1 then if N.eqb dn 0 then N.leb 2 kd else false else false else false) eqn:Hfast;
      [| apply (doCallsDSlow_spec _ _ _ _ _ _ _ _ _ Hh0)].
    destruct (beqListSym lw1 [1; 0]) eqn:Hlw1; [| discriminate].
    destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
    destruct (N.eqb_spec dn 0) as [-> | _]; [| discriminate].
    destruct (N.leb_spec 2 kd) as [Hkd2 | _]; [| discriminate].
    apply beqListSym_eq in Hlw1; subst lw1.
    destruct (popDBackOneAux df db) as [[[j df1] db1]|] eqn:Hpop; [| discriminate].
    rewrite N.div2_div.
    intros H; inversion H; subst hd df' db' rtail'; clear H.
    rewrite !mul2_eq.
    destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
    change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
    set (avail := (kd / 2)%N) in *.
    set (hd0 := if N.leb h avail then h else avail) in *.
    assert (Hhd_pos : (0 < N.to_nat hd0)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
    assert (Hhd_le_h : (N.to_nat hd0 <= N.to_nat h)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
    assert (Hhd_le_av : (N.to_nat hd0 <= N.to_nat avail)%nat) by (subst hd0; destruct (N.leb_spec h avail); lia).
    split; [exact Hhd_pos |]. split; [exact Hhd_le_h |].
    set (rem := (kd - hd0 * 2)%N).
    assert (Hrt' :
      runs_denote (if N.eqb rem 0 then runs_push (SW_raw [1; 0]) 1 (unpackDFHead rest)
                   else (SW_raw [1; 0], 1%N) :: (SW_D 0, rem) :: rest) =
      [1; 0] *> (D_word 0)^^(N.to_nat rem) *> runs_denote rest).
    { destruct (N.eqb_spec rem 0) as [-> | _].
      - rewrite runs_push_spec, unpackDFHead_spec.
        change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
        cbn [sw_toList lpow Str_app]. reflexivity.
      - cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity. }
    rewrite Hrt', (popDBackOneAux_spec df db j df1 db1 _ Hpop), !denDRev_pushD.
    change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
    change (N.to_nat 2) with 2%nat. change (N.to_nat 3) with 3%nat.
    cbn [runs_denote sw_toList]. rewrite !lpow_1.
    replace (N.to_nat kd) with ((1 + N.to_nat (hd0 - 1)%N) * 2 + N.to_nat rem)%nat by (subst rem; lia).
    rewrite lpow_add, Str_app_assoc.
    replace (N.to_nat hd0) with (1 + N.to_nat (hd0 - 1)%N)%nat by lia.
    exact (calls_denD df1 (calls_denDRev db1
      (calls_collision (N.to_nat (hd0 - 1)%N) (N.to_nat j)
        ((D_word 0)^^(N.to_nat rem) *> runs_denote rest)))).
Qed.

Fixpoint doCallsDUpto (fuel : nat) (done : N) (df db : Digits) (rtail : Runs) (req : N)
    : N * Digits * Digits * Runs :=
  match fuel with
  | O => (done, df, db, rtail)
  | S fuel' =>
    if N.eqb req 0 then (done, df, db, rtail)
    else
      match doCallsD df db rtail req true with
      | Some (hd, df', db', rtail') =>
        let done' := (done + hd)%N in
        if N.eqb hd req then (done', df', db', rtail')
        else doCallsDUpto fuel' done' df' db' rtail' (req - hd)%N
      | None => (done, df, db, rtail)
      end
  end.

Lemma doCallsDUpto_spec fuel done df db rtail req done' df' db' rtail' :
  doCallsDUpto fuel done df db rtail req = (done', df', db', rtail') ->
  (N.to_nat done <= N.to_nat done')%nat /\
  (N.to_nat done' <= N.to_nat done + N.to_nat req)%nat /\
  calls (N.to_nat done' - N.to_nat done)
    (denD df (denDRev db (runs_denote rtail)))
    (denD df' (denDRev db' (runs_denote rtail'))).
Proof.
  revert done df db rtail req.
  induction fuel as [|fuel IH]; intros done df db rtail req H; cbn [doCallsDUpto] in H.
  - inversion H; subst; clear H.
    split; [lia |]. split; [lia |].
    replace (N.to_nat done' - N.to_nat done')%nat with 0%nat by lia. constructor.
  - destruct (N.eqb_spec req 0) as [Hreq0 | Hreq0]; [subst req |].
    + inversion H; subst; clear H.
      split; [lia |]. split; [lia |].
      replace (N.to_nat done' - N.to_nat done')%nat with 0%nat by lia. constructor.
    + destruct (doCallsD df db rtail req true) as [[[[hd df1] db1] rtail1]|] eqn:Hdc.
      * destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hpos [Hle Hc1]].
        destruct (N.eqb_spec hd req) as [-> | Hneq].
        { inversion H; subst; clear H.
          split; [lia |]. split; [lia |].
          replace (N.to_nat (done + req)%N - N.to_nat done)%nat with (N.to_nat req) by lia.
          exact Hc1. }
        { destruct (IH (done + hd)%N df1 db1 rtail1 (req - hd)%N H) as [Hle1 [Hle2 Hc2]].
          split; [lia |]. split; [lia |].
          replace (N.to_nat done' - N.to_nat done)%nat
            with (N.to_nat hd + (N.to_nat done' - N.to_nat (done + hd)%N))%nat by lia.
          exact (calls_trans Hc1 Hc2). }
      * inversion H; subst; clear H.
        split; [lia |]. split; [lia |].
        replace (N.to_nat done' - N.to_nat done')%nat with 0%nat by lia. constructor.
Qed.

Lemma doCallsDUpto_0_spec fuel df db rtail req hd df' db' rtail' :
  doCallsDUpto fuel 0 df db rtail req = (hd, df', db', rtail') ->
  (N.to_nat hd <= N.to_nat req)%nat /\
  calls (N.to_nat hd)
    (denD df (denDRev db (runs_denote rtail)))
    (denD df' (denDRev db' (runs_denote rtail'))).
Proof.
  intros H.
  destruct (doCallsDUpto_spec _ _ _ _ _ _ _ _ _ _ H) as [_ [Hle Hc]].
  change (N.to_nat 0) with 0%nat in Hle, Hc.
  rewrite Nat.sub_0_r in Hc.
  split; [lia | exact Hc].
Qed.

Definition stepMR_D (l : Runs) (df db : Digits) (rtail : Runs) : FastState :=
  let doOne (_ : unit) :=
    match doCallsD df db rtail 1 true with
    | Some (hd, df', db', rtail') =>
      if N.eqb hd 1 then MkFastState l (MkRTape [] df' db' rtail') ML
      else MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    | None => MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    end in
  match l with
  | (SW_raw _, _) :: _ =>
    let '(b1, l1) := take10 l in
    if N.eqb b1 0 then doOne tt
    else
      let '(c111, l2) := take111 l1 in
      if N.eqb c111 0 then doOne tt
      else
        let '(hd, df', db', rtail') := doCallsDUpto 16 0 df db rtail (c111 + 1)%N in
        if N.eqb hd 0 then MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
        else
          let used := (hd - 1)%N in
          let rem := (c111 - used)%N in
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) rem l2) in
          MkFastState l' (MkRTape [] df' db' rtail') ML
  | _ => doOne tt
  end.

Lemma stepMR_D_spec l df db rtail :
  fs_denote (MkFastState l (MkRTape [] df db rtail) MR) -->*
  fs_denote (stepMR_D l df db rtail).
Proof.
  unfold stepMR_D.
  set (doOne := fun _ : unit =>
    match doCallsD df db rtail 1 true with
    | Some (hd, df', db', rtail') =>
      if N.eqb hd 1 then MkFastState l (MkRTape [] df' db' rtail') ML
      else MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    | None => MkFastState (sweepRight l df db) (MkRTape [] [] [] rtail) MR
    end).
  assert (HdoOne : fs_denote (MkFastState l (MkRTape [] df db rtail) MR) -->* fs_denote (doOne tt)).
  { subst doOne; cbv beta.
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
  destruct w as [lw | | | | | |]; try exact HdoOne.
  pose proof (take10_spec ((SW_raw lw, k) :: rest)) as H10.
  destruct (take10 ((SW_raw lw, k) :: rest)) as [b1 l1]; cbn [fst snd] in H10.
  destruct (N.eqb_spec b1 0) as [-> | Hb1]; [exact HdoOne |].
  pose proof (take111_spec l1 0inf) as H111.
  rewrite <- !denote_eq_plug_0inf in H111.
  destruct (take111 l1) as [c111 l2]; cbn [fst snd] in H111.
  destruct (N.eqb_spec c111 0) as [-> | Hc0]; [exact HdoOne |].
  destruct (doCallsDUpto 16 0 df db rtail (c111 + 1)%N) as [[[hd df'] db'] rtail'] eqn:Hdc.
  destruct (N.eqb_spec hd 0) as [-> | Hhd0]; [apply sweepRight_spec |].
  destruct (doCallsDUpto_0_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hle Hcalls].
  assert (Hpos : (0 < N.to_nat hd)%nat) by lia.
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

Definition trySweepMR_a0 (m : N) (l : Runs) : option Runs :=
  match l with
  | (SW_DEF la lk, Npos pcl) :: lrest =>
    if (if N.leb 1 la then N.leb 3 lk else false) then
      let cl := N.pred (Npos pcl) in
      let l0 := if N.eqb cl 0 then lrest else (SW_DEF la lk, cl) :: lrest in
      Some (pushS1 (m + 3)%N (pushDEF1 la (lk - 3)%N l0))
    else None
  | (SW_PL pln, Npos pcl) :: lrest =>
    if N.leb 1 pln then
      let cl := N.pred (Npos pcl) in
      let l0 := if N.eqb cl 0 then lrest else (SW_PL pln, cl) :: lrest in
      Some (pushS1 (m + 3)%N (pushDEF1 (pln + 4)%N (2 * pln - 2)%N l0))
    else None
  | (SW_S sn, k1) :: (SW_DEF la lk, Npos pcl) :: lrest =>
    if (if N.eqb k1 1 then if N.leb 1 la then N.leb 3 lk else false else false) then
      let cl := N.pred (Npos pcl) in
      let l0 := if N.eqb cl 0 then lrest else (SW_DEF la lk, cl) :: lrest in
      Some (pushS1 (m + 3)%N (pushS1 sn (pushDEF1 la (lk - 3)%N l0)))
    else None
  | (SW_S sn, k1) :: (SW_PL pln, Npos pcl) :: lrest =>
    if (if N.eqb k1 1 then N.leb 1 pln else false) then
      let cl := N.pred (Npos pcl) in
      let l0 := if N.eqb cl 0 then lrest else (SW_PL pln, cl) :: lrest in
      Some (pushS1 (m + 3)%N (pushS1 sn (pushDEF1 (pln + 4)%N (2 * pln - 2)%N l0)))
    else None
  | _ => None
  end.

Lemma trySweepMR_a0_spec m l l' r :
  trySweepMR_a0 m l = Some l' ->
  CfgR (runs_denote l) ([1; 0] *> D_word 0 *> D_word (N.to_nat m) *> r) -->*
  CfgR (runs_denote l') ([1; 0] *> r).
Proof.
  destruct l as [|[w1 k1] rest1]; [discriminate |].
  destruct w1 as [| | sn | pln | la lk | |]; try discriminate.
  - (* SW_S sn :: ... *)
    destruct rest1 as [|[w2 k2] lrest]; [discriminate |].
    destruct w2 as [| | | pln | la lk | |]; try discriminate.
    + (* SW_S :: SW_PL *)
      destruct k2 as [|pcl]; [discriminate |].
      cbv beta iota zeta delta [trySweepMR_a0].
      destruct (if N.eqb k1 1 then N.leb 1 pln else false) eqn:Hc; [| discriminate].
      destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
      destruct (N.leb_spec 1 pln) as [Hpln1 | _]; [| discriminate].
      intros H; inj_some H.
      rewrite !pushS1_spec, pushDEF1_spec, opt_run_denote.
      cbn [runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, (pos_to_nat_succ pcl).
      cbn [lpow]. rewrite Str_app_assoc, (pl_eq_def (N.to_nat pln)).
      replace (N.to_nat (m + 3)%N) with (N.to_nat m + 3)%nat by lia.
      replace (N.to_nat (pln + 4)%N) with (N.to_nat pln + 4)%nat by lia.
      replace (N.to_nat (2 * pln - 2)%N) with ((2 * N.to_nat pln + 1) - 3)%nat by lia.
      apply rule_mr_a0_S_DEF; lia.
    + (* SW_S :: SW_DEF *)
      destruct k2 as [|pcl]; [discriminate |].
      cbv beta iota zeta delta [trySweepMR_a0].
      destruct (if N.eqb k1 1 then if N.leb 1 la then N.leb 3 lk else false else false) eqn:Hc; [| discriminate].
      destruct (N.eqb_spec k1 1) as [-> | _]; [| discriminate].
      destruct (N.leb_spec 1 la) as [Hla1 | _]; [| discriminate].
      destruct (N.leb_spec 3 lk) as [Hlk3 | _]; [| discriminate].
      intros H; inj_some H.
      rewrite !pushS1_spec, pushDEF1_spec, opt_run_denote.
      cbn [runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, (pos_to_nat_succ pcl).
      cbn [lpow]. rewrite Str_app_assoc.
      replace (N.to_nat (m + 3)%N) with (N.to_nat m + 3)%nat by lia.
      replace (N.to_nat (lk - 3)%N) with (N.to_nat lk - 3)%nat by lia.
      apply rule_mr_a0_S_DEF; lia.
  - (* SW_PL pln *)
    destruct k1 as [|pcl]; [discriminate |].
    cbv beta iota zeta delta [trySweepMR_a0].
    destruct (N.leb_spec 1 pln) as [Hpln1 | _]; [| discriminate].
    intros H; inj_some H.
    rewrite pushS1_spec, pushDEF1_spec, opt_run_denote.
    cbn [runs_denote sw_toList].
    rewrite (pos_to_nat_succ pcl). cbn [lpow].
    rewrite Str_app_assoc, (pl_eq_def (N.to_nat pln)).
    replace (N.to_nat (m + 3)%N) with (N.to_nat m + 3)%nat by lia.
    replace (N.to_nat (pln + 4)%N) with (N.to_nat pln + 4)%nat by lia.
    replace (N.to_nat (2 * pln - 2)%N) with ((2 * N.to_nat pln + 1) - 3)%nat by lia.
    apply rule_mr_a0_DEF; lia.
  - (* SW_DEF la lk *)
    destruct k1 as [|pcl]; [discriminate |].
    cbv beta iota zeta delta [trySweepMR_a0].
    destruct (if N.leb 1 la then N.leb 3 lk else false) eqn:Hc; [| discriminate].
    destruct (N.leb_spec 1 la) as [Hla1 | _]; [| discriminate].
    destruct (N.leb_spec 3 lk) as [Hlk3 | _]; [| discriminate].
    intros H; inj_some H.
    rewrite pushS1_spec, pushDEF1_spec, opt_run_denote.
    cbn [runs_denote sw_toList].
    rewrite (pos_to_nat_succ pcl). cbn [lpow]. rewrite Str_app_assoc.
    replace (N.to_nat (m + 3)%N) with (N.to_nat m + 3)%nat by lia.
    replace (N.to_nat (lk - 3)%N) with (N.to_nat lk - 3)%nat by lia.
    apply rule_mr_a0_DEF; lia.
Qed.

Fixpoint sweepMRDigits (ds : Digits) (prog hasPend : bool) (pendN : N) (l : Runs)
    : bool * Runs * Digits :=
  match ds with
  | [] => if hasPend then (prog, l, [(pendN, 1%N)]) else (prog, l, [])
  | (nd, N0) :: rest => sweepMRDigits rest prog hasPend pendN l
  | (nd, Npos pkd) :: rest =>
    let kd := Npos pkd in
    if negb hasPend then
      if N.leb 2 nd then
        if N.eqb kd 1 then sweepMRDigits rest prog true nd l
        else
          let kp := (N.div2 kd) in
          let n := (nd - 2)%N in
          sweepMRDigits rest true ((mod2_1 kd)) nd (pushPL n kp l)
      else (prog, l, (nd, kd) :: rest)
    else
      let l1 := pushDEF1 (nd + 2)%N (2 * (pendN - 2) + 1)%N l in
      let kd0 := N.pred kd in
      if N.eqb kd0 0 then sweepMRDigits rest true false 0%N l1
      else if N.leb 2 nd then
        if N.eqb kd0 1 then sweepMRDigits rest true true nd l1
        else
          let kp := (N.div2 kd0) in
          let n := (nd - 2)%N in
          sweepMRDigits rest true ((mod2_1 kd0)) nd (pushPL n kp l1)
      else (true, l1, (nd, kd0) :: rest)
  end.

Definition pend_den (hasPend : bool) (pendN : N) (t : side) : side :=
  if hasPend then D_word (N.to_nat pendN) *> t else t.

Lemma sweepMRDigits_pair_step nd kd rest l (prog : bool) prog' l' dsrem t :
  (2 <= nd)%N -> (2 <= kd)%N ->
  (forall p hp pn l0,
     (hp = true -> (2 <= pn)%N) ->
     sweepMRDigits rest p hp pn l0 = (prog', l', dsrem) ->
     CfgR (runs_denote l0) ([1; 0] *> pend_den hp pn (denD rest t)) -->*
     CfgR (runs_denote l') ([1; 0] *> denD dsrem t)) ->
  sweepMRDigits rest true (mod2_1 kd) nd (pushPL (nd - 2)%N (N.div2 kd) l) = (prog', l', dsrem) ->
  CfgR (runs_denote l) ([1; 0] *> (D_word (N.to_nat nd))^^(N.to_nat kd) *> denD rest t) -->*
  CfgR (runs_denote l') ([1; 0] *> denD dsrem t).
Proof.
  intros Hnd2 Hkd2 IH Hrec.
  assert (Hinv : mod2_1 kd = true -> (2 <= nd)%N) by (intros _; exact Hnd2).
  pose proof (IH true (mod2_1 kd) nd (pushPL (nd - 2)%N (N.div2 kd) l) Hinv Hrec) as Htail.
  rewrite pushPL_spec, N.div2_div, mod2_1_eq in Htail.
  destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
  change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
  assert (Hnd : (2 + N.to_nat (nd - 2)%N = N.to_nat nd)%nat) by lia.
  eapply ev_trans; [| exact Htail].
  unfold pend_den.
  destruct (N.eqb_spec (kd mod 2) 1) as [Hm1 | Hm1].
  - replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2 + 1)%nat by lia.
    rewrite lpow_plus_r, Str_app_assoc, <- Hnd.
    apply pairsR.
  - replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2)%nat by lia.
    rewrite <- Hnd. apply pairsR.
Qed.

Lemma sweepMRDigits_spec ds prog hasPend pendN l prog' l' dsrem t :
  (hasPend = true -> (2 <= pendN)%N) ->
  sweepMRDigits ds prog hasPend pendN l = (prog', l', dsrem) ->
  CfgR (runs_denote l) ([1; 0] *> pend_den hasPend pendN (denD ds t)) -->*
  CfgR (runs_denote l') ([1; 0] *> denD dsrem t).
Proof.
  revert prog hasPend pendN l.
  induction ds as [|[nd [|pkd]] rest IH]; intros prog hasPend pendN l Hpend H.
  - cbn [sweepMRDigits] in H.
    destruct hasPend; inversion H; subst; clear H; cbn [pend_den denD].
    + change (N.to_nat 1) with 1%nat. rewrite lpow_1. apply evstep_refl.
    + apply evstep_refl.
  - cbn [sweepMRDigits denD lpow Str_app] in H |- *.
    exact (IH _ _ _ _ Hpend H).
  - cbv beta iota zeta delta [sweepMRDigits] in H.
    set (kd := Npos pkd) in *.
    destruct hasPend; cbn [negb] in H.
    + (* hasPend = true *)
      specialize (Hpend eq_refl).
      set (l1 := pushDEF1 (nd + 2)%N (2 * (pendN - 2) + 1)%N l) in *.
      set (kd0 := N.pred kd) in *.
      assert (Hstep1 :
        CfgR (runs_denote l) ([1; 0] *> pend_den true pendN (denD ((nd, kd) :: rest) t)) -->*
        CfgR (runs_denote l1) ([1; 0] *> (D_word (N.to_nat nd))^^(N.to_nat kd0) *> denD rest t)).
      { subst l1 kd0 kd. rewrite pushDEF1_spec.
        cbn [pend_den denD]. rewrite (pos_to_nat_succ pkd). cbn [lpow]. rewrite Str_app_assoc.
        replace (N.to_nat pendN) with (2 + N.to_nat (pendN - 2)%N)%nat by lia.
        replace (N.to_nat (nd + 2)%N) with (N.to_nat nd + 2)%nat by lia.
        replace (N.to_nat (2 * (pendN - 2) + 1)%N) with (2 * N.to_nat (pendN - 2)%N + 1)%nat by lia.
        apply rule_defect2D_def. }
      eapply ev_trans; [exact Hstep1 |].
      destruct (N.eqb_spec kd0 0) as [Hkd0 | Hkd0].
      * rewrite Hkd0; change (N.to_nat 0) with 0%nat; cbn [lpow Str_app].
        exact (IH true false 0%N l1 ltac:(discriminate) H).
      * destruct (N.leb_spec 2 nd) as [Hnd2 | _].
        { destruct (N.eqb_spec kd0 1) as [Hkd1 | Hkd1].
          - rewrite Hkd1; change (N.to_nat 1) with 1%nat; rewrite lpow_1.
            exact (IH true true nd l1 (fun _ => Hnd2) H).
          - assert (Hkd0_2 : (2 <= kd0)%N) by lia.
            exact (sweepMRDigits_pair_step nd kd0 rest l1 true prog' l' dsrem t Hnd2 Hkd0_2 IH H). }
        { inj_triple H. cbn [denD]. apply evstep_refl. }
    + (* hasPend = false *)
      cbn [pend_den denD].
      destruct (N.leb_spec 2 nd) as [Hnd2 | _].
      * destruct (N.eqb_spec kd 1) as [Hkd1 | Hkd1].
        { rewrite Hkd1; change (N.to_nat 1) with 1%nat; rewrite lpow_1.
          exact (IH prog true nd l (fun _ => Hnd2) H). }
        { assert (Hkd2 : (2 <= kd)%N) by (subst kd; lia).
          exact (sweepMRDigits_pair_step nd kd rest l prog prog' l' dsrem t Hnd2 Hkd2 IH H). }
      * inj_triple H. cbn [denD]. apply evstep_refl.
Qed.

Definition sweepMRTailStepOne (prog : bool) (l rt : Runs) : bool * bool * Runs * Runs :=
  let rt0 := unpackDHead rt in
  match rt0 with
  | (SW_D _, N0) :: rest => (true, prog, l, rest)
  | (SW_D nd, Npos pkd) :: rest =>
    let kd := Npos pkd in
    if N.leb 2 nd then
      if N.leb 2 kd then
        let kp := (N.div2 kd) in
        let n := (nd - 2)%N in
        let rest' := if (mod2_1 kd) then (SW_D nd, 1%N) :: rest else rest in
        (true, true, pushPL n kp l, rest')
      else
        let rest0 := unpackDHead rest in
        match rest0 with
        | (SW_D m, Npos pkm) :: rest2 =>
          let km := N.pred (Npos pkm) in
          let rest' := if N.eqb km 0 then rest2 else (SW_D m, km) :: rest2 in
          (true, true, pushDEF1 (m + 2)%N (2 * (nd - 2) + 1)%N l, rest')
        | _ => (false, prog, l, (SW_D nd, kd) :: rest0)
        end
    else if (if N.eqb nd 0 then N.leb kd 3 else false) then
      if N.leb 2 kd then
        match trySweepMR_a0 0 l with
        | Some l' =>
          let kd2 := (kd - 2)%N in
          let rest' := if N.eqb kd2 0 then rest else (SW_D 0, kd2) :: rest in
          (true, true, l', rest')
        | None => (false, prog, l, rt0)
        end
      else
        let rest0 := unpackDHead rest in
        match rest0 with
        | (SW_D m, Npos pkm) :: rest2 =>
          match trySweepMR_a0 m l with
          | Some l' =>
            let km := N.pred (Npos pkm) in
            let rest' := if N.eqb km 0 then rest2 else (SW_D m, km) :: rest2 in
            (true, true, l', rest')
          | None => (false, prog, l, (SW_D 0, kd) :: rest0)
          end
        | _ => (false, prog, l, (SW_D 0, kd) :: rest0)
        end
    else (false, prog, l, rt0)
  | _ => (false, prog, l, rt0)
  end.

Lemma sweepMRTailStepOne_spec prog l rt c p l' rt' :
  sweepMRTailStepOne prog l rt = (c, p, l', rt') ->
  CfgR (runs_denote l) ([1; 0] *> runs_denote rt) -->*
  CfgR (runs_denote l') ([1; 0] *> runs_denote rt').
Proof.
  unfold sweepMRTailStepOne.
  rewrite <- (unpackDHead_spec rt).
  generalize (unpackDHead rt) as rt0; clear rt; intros rt0.
  destruct rt0 as [|[[| nd | | | | |] [|pkd]] rest];
    try (intros H; inj_quad H; apply evstep_refl).
  set (kd := Npos pkd) in *.
  destruct (N.leb_spec 2 nd) as [Hnd2 | Hnd2].
  - destruct (N.leb_spec 2 kd) as [Hkd2 | Hkd2].
    + rewrite N.div2_div, mod2_1_eq.
      intros H; inj_quad H.
      rewrite pushPL_spec. cbn [runs_denote sw_toList].
      destruct (N_div_mod_nat kd 2 ltac:(lia)) as [Hdiv Hmod].
      change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
      assert (Hnd : (2 + N.to_nat (nd - 2)%N = N.to_nat nd)%nat) by lia.
      destruct (N.eqb_spec (kd mod 2) 1) as [Hm1 | Hm1].
      * cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2 + 1)%nat by lia.
        rewrite lpow_plus_r, Str_app_assoc, <- Hnd. apply pairsR.
      * replace (N.to_nat kd) with (N.to_nat (kd / 2)%N * 2)%nat by lia.
        rewrite <- Hnd. apply pairsR.
    + assert (Hkd1 : kd = 1%N) by (subst kd; lia).
      rewrite Hkd1 in *.
      cbn [runs_denote sw_toList].
      assert (Hrest0 : runs_denote (unpackDHead rest) = runs_denote rest) by apply unpackDHead_spec.
      rewrite <- Hrest0.
      generalize (unpackDHead rest) as rest0; clear rest Hrest0; intros rest0.
      destruct rest0 as [|[[| m | | | | |] [|pkm]] rest2];
        try (intros H; inj_quad H; cbn [runs_denote sw_toList]; apply evstep_refl).
      intros H; inj_quad H.
      rewrite pushDEF1_spec, opt_run_denote.
      cbn [runs_denote sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite lpow_1, (pos_to_nat_succ pkm).
      cbn [lpow]. rewrite Str_app_assoc.
      replace (N.to_nat nd) with (2 + N.to_nat (nd - 2)%N)%nat by lia.
      replace (N.to_nat (m + 2)%N) with (N.to_nat m + 2)%nat by lia.
      replace (N.to_nat (2 * (nd - 2) + 1)%N) with (2 * N.to_nat (nd - 2)%N + 1)%nat by lia.
      apply rule_defect2D_def.
  - destruct (if N.eqb nd 0 then N.leb kd 3 else false) eqn:Ha0;
      [| intros H; inj_quad H; apply evstep_refl].
    destruct (N.eqb_spec nd 0) as [-> | _]; [| discriminate].
    destruct (N.leb_spec kd 3) as [Hkd3 | _]; [| discriminate].
    destruct (N.leb_spec 2 kd) as [Hkd2 | Hkd2].
    + destruct (trySweepMR_a0 0 l) as [l1|] eqn:Htr;
        [| intros H; inj_quad H; apply evstep_refl].
      intros H; inj_quad H.
      rewrite opt_run_denote. cbn [runs_denote sw_toList].
      change (N.to_nat 0) with 0%nat.
      replace (N.to_nat kd) with (2 + N.to_nat (kd - 2)%N)%nat by lia.
      cbn [Nat.add lpow]. rewrite !Str_app_assoc.
      exact (trySweepMR_a0_spec 0 l l1 _ Htr).
    + assert (Hkd1 : kd = 1%N) by (subst kd; lia).
      rewrite Hkd1 in *.
      cbn [runs_denote sw_toList].
      assert (Hrest0 : runs_denote (unpackDHead rest) = runs_denote rest) by apply unpackDHead_spec.
      rewrite <- Hrest0.
      generalize (unpackDHead rest) as rest0; clear rest Hrest0; intros rest0.
      destruct rest0 as [|[[| m | | | | |] [|pkm]] rest2];
        try (intros H; inj_quad H; cbn [runs_denote sw_toList]; apply evstep_refl).
      destruct (trySweepMR_a0 m l) as [l1|] eqn:Htr;
        [| intros H; inj_quad H; cbn [runs_denote sw_toList]; apply evstep_refl].
      intros H; inj_quad H.
      rewrite opt_run_denote. cbn [runs_denote sw_toList].
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
      rewrite lpow_1, (pos_to_nat_succ pkm). cbn [lpow]. rewrite !Str_app_assoc.
      exact (trySweepMR_a0_spec m l l1 _ Htr).
Qed.

Definition sweepMRTailOne (prog : bool) (l rt : Runs) : bool * bool * Runs * Runs :=
  match rt with
  | (SW_DF ds, k) :: rest =>
    if N.eqb k 1 then
      let '(prog', l', dsrem) := sweepMRDigits ds prog false 0%N l in
      match dsrem with
      | [] => (true, prog', l', rest)
      | (nd, kd) :: ds' =>
        let rt' :=
          match ds' with
          | [] => runs_push (SW_D nd) kd rest
          | _ :: _ => (SW_D nd, kd) :: (SW_DF ds', 1%N) :: rest
          end in
        (true, prog', l', rt')
      end
    else sweepMRTailStepOne prog l rt
  | _ => sweepMRTailStepOne prog l rt
  end.

Lemma sweepMRTailOne_spec prog l rt c p l' rt' :
  sweepMRTailOne prog l rt = (c, p, l', rt') ->
  CfgR (runs_denote l) ([1; 0] *> runs_denote rt) -->*
  CfgR (runs_denote l') ([1; 0] *> runs_denote rt').
Proof.
  destruct rt as [|[w k] rest]; [apply sweepMRTailStepOne_spec |].
  destruct w as [| | | | | ds |]; try apply sweepMRTailStepOne_spec.
  cbn [sweepMRTailOne].
  destruct (N.eqb_spec k 1) as [-> | _]; [| apply sweepMRTailStepOne_spec].
  destruct (sweepMRDigits ds prog false 0%N l) as [[prog1 l1] dsrem] eqn:Hsw.
  pose proof (sweepMRDigits_spec ds prog false 0%N l prog1 l1 dsrem (runs_denote rest) ltac:(discriminate) Hsw) as Hsp.
  cbn [pend_den] in Hsp.
  cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat.
  rewrite lpow_1, digitsToList_plug.
  destruct dsrem as [|[nd kd] [|d2 ds'']]; intros H; inversion H; subst; clear H.
  - cbn [denD] in Hsp. exact Hsp.
  - rewrite runs_push_spec. cbn [sw_toList]. cbn [denD] in Hsp. exact Hsp.
  - cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat.
    rewrite lpow_1, digitsToList_plug. cbn [denD] in Hsp. exact Hsp.
Qed.

Fixpoint sweepMRTailPow (k : nat) (prog : bool) (l rt : Runs) : bool * bool * Runs * Runs :=
  match k with
  | O => sweepMRTailOne prog l rt
  | S k' =>
    let '(c1, p1, l1, r1) := sweepMRTailPow k' prog l rt in
    if c1 then sweepMRTailPow k' p1 l1 r1 else (false, p1, l1, r1)
  end.

Lemma sweepMRTailPow_spec k prog l rt c p l' rt' :
  sweepMRTailPow k prog l rt = (c, p, l', rt') ->
  CfgR (runs_denote l) ([1; 0] *> runs_denote rt) -->*
  CfgR (runs_denote l') ([1; 0] *> runs_denote rt').
Proof.
  revert prog l rt c p l' rt'.
  induction k as [|k IH]; intros prog l rt c p l' rt' H; cbn [sweepMRTailPow] in H.
  - exact (sweepMRTailOne_spec _ _ _ _ _ _ _ H).
  - destruct (sweepMRTailPow k prog l rt) as [[[c1 p1] l1] r1] eqn:H1.
    pose proof (IH _ _ _ _ _ _ _ H1) as Hsp1.
    destruct c1.
    + eapply ev_trans; [exact Hsp1 | exact (IH _ _ _ _ _ _ _ H)].
    + inversion H; subst; exact Hsp1.
Qed.

Definition stepMR_imm (l rt1 : Runs) : option FastState :=
  match takeD rt1 with
  | None =>
    let '(k0, rt2) := take10 rt1 in
    let k10 := (1 + k0)%N in
    if (if N.leb 2 k10 then (mod2_0 k10) else false) then
      match takeD rt2 with
      | Some (dn, rt3) =>
        if N.eqb k10 2 then
          if N.eqb dn 0 then Some (MkFastState (pushDEF1 0 2 l) (MkRTape [] [] [] rt3) MR)
          else Some (MkFastState (pushS1 (dn - 1)%N (runs_push (SW_S 0) 2 l)) (MkRTape [] [] [] rt3) MR)
        else
          let kp := (N.div2 k10) in
          let l' := runs_push (SW_raw [1; 0]) dn (runs_push (SW_raw [1; 1; 0; 1]) kp (runs_push (SW_S 0) 1 l)) in
          Some (MkFastState l' (MkRTape [] [] [] rt3) MR)
      | None => None
      end
    else None
  | Some (a, rt2) =>
    match takeD rt2 with
    | Some (m, rt3) =>
      if (if N.leb 2 a then N.eqb m a else false) then
        let rt3u := unpackDHead rt3 in
        let '(tot, rt4) :=
          match rt3u with
          | (SW_D a', kex) :: rt3' => if N.eqb a' a then ((2 + kex)%N, rt3') else (2%N, rt3u)
          | _ => (2%N, rt3u)
          end in
        let kp := (N.div2 tot) in
        let n := (a - 2)%N in
        let rt5 := if (mod2_1 tot) then runs_push (SW_D a) 1 rt4 else rt4 in
        Some (MkFastState (pushPL n kp l) (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1 rt5)) MR)
      else if N.eqb a 0 then
        Some (MkFastState l (MkRTape [] [((m + 3)%N, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 (unpackDFHead rt3))) ML)
      else if N.eqb a 1 then
        Some (MkFastState l (MkRTape [] (pushD 0 2 [((m + 1)%N, 1%N)]) [] (runs_push (SW_raw [1; 0]) 1 (unpackDFHead rt3))) ML)
      else
        Some (MkFastState (pushDEF1 (m + 2)%N (2 * (a - 2) + 1)%N l)
                (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1 (unpackDFHead rt3))) MR)
    | None =>
      match runs_remove [0; 0] rt2 with
      | Some rt3 =>
        if N.eqb a 0 then Some (MkFastState (pushDEF1 1 0 l) (MkRTape [] [] [] rt3) MR)
        else Some (MkFastState (pushDEF1 1 (2 * a)%N l) (MkRTape [] [] [] rt3) MR)
      | None =>
        let '(c1, rt3) := takeOnes rt2 in
        if (mod2_1 c1) then
          match runs_remove [0] rt3 with
          | Some rt4 =>
            let mv := (N.div2 c1) in
            if N.eqb a 0 then
              Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_D (mv + 3)%N) 1 (runs_push (SW_raw [1]) 1 rt4))) ML)
            else if N.eqb a 1 then
              Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_D 0) 2 (runs_push (SW_D (mv + 1)%N) 1 (runs_push (SW_raw [1]) 1 rt4)))) ML)
            else
              Some (MkFastState (pushDEF1 (mv + 2)%N (2 * (a - 2) + 1)%N l)
                      (MkRTape [] [] [] (runs_push (SW_raw [1]) 1 rt4)) MR)
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
  fs_denote (MkFastState (pushPL (a - 2)%N (N.div2 tot) l)
    (MkRTape [] [] [] (runs_push (SW_raw [1; 0]) 1
      (if mod2_1 tot then runs_push (SW_D a) 1 rt4 else rt4))) MR).
Proof.
  intros Ha2 Htr. rewrite Htr, N.div2_div, mod2_1_eq.
  cbn [fs_denote fs_L fs_R fs_mode].
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
  rewrite pushPL_spec, !runs_push_spec. cbn [sw_toList].
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
        assert (Hrt3u : runs_denote (unpackDHead rt3) = runs_denote rt3) by apply unpackDHead_spec.
        rewrite <- Hrt3u.
        generalize (unpackDHead rt3) as rt3u; clear rt3 Htd2 Hrt3u; intros rt3.
        destruct rt3 as [|[w3 kex] rt3'].
        { intros H; inj_some H.
          apply (stepMR_imm_pair_helper l a [] 2%N []); [exact Ha2 |].
          change (N.to_nat 2) with 2%nat. cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc. reflexivity. }
        destruct w3 as [| a' | | | | |].
        2:{ destruct (N.eqb_spec a' a) as [<- | _].
            - intros H; inj_some H.
              apply (stepMR_imm_pair_helper l a' ((SW_D a', kex) :: rt3') (2 + kex)%N rt3'); [exact Ha2 |].
              cbn [runs_denote sw_toList].
              replace (N.to_nat (2 + kex)%N) with (2 + N.to_nat kex)%nat by lia.
              cbn [Nat.add lpow]. rewrite ?Str_app_assoc. reflexivity.
            - intros H; inj_some H.
              apply (stepMR_imm_pair_helper l a ((SW_D a', kex) :: rt3') 2%N ((SW_D a', kex) :: rt3')); [exact Ha2 |].
              change (N.to_nat 2) with 2%nat. cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc. reflexivity. }
        all: intros H; inj_some H;
             apply (stepMR_imm_pair_helper l a _ 2%N _); [exact Ha2 |];
             change (N.to_nat 2) with 2%nat; cbn [lpow]; rewrite ?app_nil_r, Str_app_assoc; reflexivity.
      * destruct (N.eqb_spec a 0) as [-> | Ha0].
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite runs_push_spec, unpackDFHead_spec. change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          cbn [sw_toList]. rewrite !lpow_1.
          replace (N.to_nat (m + 3)%N) with (3 + N.to_nat m)%nat by lia.
          apply rule_defect0D. }
        destruct (N.eqb_spec a 1) as [-> | Ha1].
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denDRev].
          rewrite denD_pushD, runs_push_spec, unpackDFHead_spec. cbn [denD sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat (m + 1)%N) with (1 + N.to_nat m)%nat by lia.
          apply rule_defect1D. }
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite pushDEF1_spec, runs_push_spec, unpackDFHead_spec. cbn [sw_toList].
          change (N.to_nat 1) with 1%nat. rewrite lpow_1.
          replace (N.to_nat a) with (2 + N.to_nat (a - 2)%N)%nat by lia.
          replace (N.to_nat (m + 2)%N) with (N.to_nat m + 2)%nat by lia.
          replace (N.to_nat (2 * (a - 2) + 1)%N) with (2 * N.to_nat (a - 2)%N + 1)%nat by lia.
          apply rule_defect2D_def. }
    + destruct (runs_remove [0; 0] rt2) as [rt3|] eqn:Hr00.
      * rewrite (runs_remove_spec _ _ _ Hr00).
        destruct (N.eqb_spec a 0) as [-> | Ha0].
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite pushDEF1_spec. change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          apply rule_defect_blank0_def. }
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite pushDEF1_spec. change (N.to_nat 1) with 1%nat.
          replace (N.to_nat a) with (1 + N.to_nat (a - 1)%N)%nat by lia.
          replace (N.to_nat (2 * a)%N) with (2 * (N.to_nat (a - 1)%N + 1))%nat by lia.
          apply rule_defect_blankS_def. }
      * pose proof (takeOnes_spec rt2 0inf) as H1.
        rewrite <- !denote_eq_plug_0inf in H1.
        destruct (takeOnes rt2) as [c1 rt3]; cbn [fst snd] in H1.
        rewrite mod2_1_eq, N.div2_div.
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
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
          rewrite !lpow_1.
          replace (N.to_nat (c1 / 2 + 3)%N) with (N.to_nat (c1 / 2)%N + 3)%nat by lia.
          apply rule_defect0'. }
        destruct (N.eqb_spec a 1) as [-> | Ha1].
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
          replace (N.to_nat (c1 / 2 + 1)%N) with (1 + N.to_nat (c1 / 2)%N)%nat by lia.
          apply rule_defect1. }
        { intros H; inj_some H.
          cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
          rewrite pushDEF1_spec, !runs_push_spec. cbn [sw_toList].
          change (N.to_nat 1) with 1%nat. rewrite lpow_1.
          replace (N.to_nat a) with (2 + N.to_nat (a - 2)%N)%nat by lia.
          replace (N.to_nat (c1 / 2 + 2)%N) with (N.to_nat (c1 / 2)%N + 2)%nat by lia.
          replace (N.to_nat (2 * (a - 2) + 1)%N) with (2 * N.to_nat (a - 2)%N + 1)%nat by lia.
          apply rule_defect2_def. }
  - pose proof (take10_spec rt1) as H10.
    destruct (take10 rt1) as [k0 rt2]; cbn [fst snd] in H10.
    rewrite mod2_0_eq, N.div2_div.
    destruct (if N.leb 2 (1 + k0)%N then N.eqb ((1 + k0) mod 2)%N 0 else false) eqn:Hcond; [| discriminate].
    destruct (N.leb_spec 2 (1 + k0)%N) as [Hk2 | _]; [| discriminate].
    apply N.eqb_eq in Hcond.
    destruct (takeD rt2) as [[dn rt3]|] eqn:Htd2; [| discriminate].
    rewrite H10, (takeD_spec _ _ _ Htd2).
    change ([1; 0] *> [1; 0]^^(N.to_nat k0) *> D_word (N.to_nat dn) *> runs_denote rt3)
      with ([1; 0]^^(1 + N.to_nat k0) *> D_word (N.to_nat dn) *> runs_denote rt3).
    destruct (N.eqb_spec (1 + k0)%N 2) as [Hk10_2 | Hk10_2].
    + replace (1 + N.to_nat k0)%nat with 2%nat by lia.
      destruct (N.eqb_spec dn 0) as [-> | Hdn0].
      * intros H; inj_some H.
        cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
        rewrite pushDEF1_spec. change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
        apply rule_paired_1_0.
      * intros H; inj_some H.
        cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
        rewrite pushS1_spec, runs_push_spec. cbn [sw_toList].
        change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
        cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
        replace (N.to_nat dn) with (N.to_nat (dn - 1)%N + 1)%nat by lia.
        apply rule_paired_1_S.
    + intros H; inj_some H.
      destruct (N_div_mod_nat (1 + k0)%N 2 ltac:(lia)) as [Hdiv _].
      change (N.to_nat 2) with 2%nat in Hdiv.
      cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite !runs_push_spec. cbn [sw_toList].
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      replace (1 + N.to_nat k0)%nat with (N.to_nat ((1 + k0) / 2)%N * 2)%nat by lia.
      apply rule_paired.
Qed.

Definition stepMR_tailNoImm (l rt : Runs) : option FastState :=
  match runs_remove [0; 0; 0] rt with
  | Some rt1 => Some (MkFastState l (MkRTape [] [(0%N, 2%N)] [] rt1) ML)
  | None =>
    let '(c1, rt1) := takeOnes rt in
    if N.eqb c1 0 then None
    else if (mod2_0 c1) then
      match runs_remove [0; 0] rt1 with
      | Some rt2 =>
        let h := (N.div2 c1) in
        Some (MkFastState l (MkRTape [] [(h, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 rt2)) ML)
      | None => None
      end
    else
      match runs_remove [0; 0] rt1 with
      | Some rt2 =>
        let n := (N.div2 c1) in
        Some (MkFastState (pushS1 n l) (MkRTape [] [] [] rt2) MR)
      | None => None
      end
  end.

Lemma stepMR_tailNoImm_spec l rt s' :
  stepMR_tailNoImm l rt = Some s' ->
  CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'.
Proof.
  unfold stepMR_tailNoImm.
  destruct (runs_remove [0; 0; 0] rt) as [rt1|] eqn:Hr0.
  - intros H; inj_some H.
    rewrite (runs_remove_spec _ _ _ Hr0).
    cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
    change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
    apply rule_blank.
  - pose proof (takeOnes_spec rt 0inf) as H1.
    rewrite <- !denote_eq_plug_0inf in H1.
    destruct (takeOnes rt) as [c1 rt1]; cbn [fst snd] in H1.
    rewrite mod2_0_eq, N.div2_div.
    destruct (N.eqb_spec c1 0) as [-> | Hc0]; [discriminate |].
    destruct (N_div_mod_nat c1 2 ltac:(lia)) as [Hdiv Hmod].
    change (N.to_nat 2) with 2%nat in Hdiv, Hmod.
    destruct (N.eqb_spec (c1 mod 2) 0) as [Heven | Hodd].
    + destruct (runs_remove [0; 0] rt1) as [rt2|] eqn:Hr00; [| discriminate].
      intros H; inj_some H.
      cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite H1, (runs_remove_spec _ _ _ Hr00), runs_push_spec. cbn [sw_toList].
      change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
      replace (N.to_nat c1) with (2 * (1 + (N.to_nat (c1 / 2)%N - 1)))%nat by lia.
      rewrite one_pow_two_mul.
      replace (N.to_nat (c1 / 2)%N) with (1 + (N.to_nat (c1 / 2)%N - 1))%nat at 2 by lia.
      apply rule_even.
    + destruct (runs_remove [0; 0] rt1) as [rt2|] eqn:Hr00; [| discriminate].
      intros H; inj_some H.
      cbn [fs_denote fs_L fs_R fs_mode]. unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      rewrite H1, (runs_remove_spec _ _ _ Hr00), pushS1_spec.
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
  | (SW_raw w, k) :: rest =>
    if (if beqListSym w [1; 0] then N.eqb k 1 else false) then
      let '(_, prog, l', rest') := sweepMRTailPow 12 false l rest in
      let rt' := runs_push (SW_raw [1; 0]) 1 rest' in
      if prog then Some (MkFastState l' (MkRTape [] [] [] rt') MR)
      else
        match stepMR_tailRest l' rt' with
        | Some s' => Some s'
        | None => toRawAndStep l' (MkRTape [] [] [] rt') MR
        end
    else
      match stepMR_tailRest l rt with
      | Some s' => Some s'
      | None => toRawAndStep l (MkRTape [] [] [] rt) MR
      end
  | _ =>
    match stepMR_tailRest l rt with
    | Some s' => Some s'
    | None => toRawAndStep l (MkRTape [] [] [] rt) MR
    end
  end.

Lemma stepMR_tailRest_or_raw_spec l rt :
  match match stepMR_tailRest l rt with
        | Some s' => Some s'
        | None => toRawAndStep l (MkRTape [] [] [] rt) MR
        end with
  | Some s' => CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'
  | None => halts src_tm (CfgR (runs_denote l) (runs_denote rt))
  end.
Proof.
  destruct (stepMR_tailRest l rt) as [s'|] eqn:Hsr.
  - exact (stepMR_tailRest_spec l rt s' Hsr).
  - pose proof (toRawAndStep_spec l (MkRTape [] [] [] rt) MR) as Hraw.
    cbn [fs_denote fs_L fs_R fs_mode] in Hraw.
    unfold rt_denote in Hraw; cbn [r_raw d_front d_back r_tail plug denD denDRev] in Hraw.
    exact Hraw.
Qed.

Lemma stepMR_tail_spec l rt :
  match stepMR_tail l rt with
  | Some s' => CfgR (runs_denote l) (runs_denote rt) -->* fs_denote s'
  | None => halts src_tm (CfgR (runs_denote l) (runs_denote rt))
  end.
Proof.
  destruct rt as [|[w k] rest].
  - cbn [stepMR_tail fs_denote fs_L fs_R fs_mode runs_denote].
    unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev runs_denote].
    change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
    cbn [lpow]. rewrite ?app_nil_r, Str_app_assoc.
    apply rule_emptyR.
  - destruct w as [lw | | | | | |]; try (cbn [stepMR_tail]; apply stepMR_tailRest_or_raw_spec).
    cbn [stepMR_tail].
    destruct (if beqListSym lw [1; 0] then N.eqb k 1 else false) eqn:Hc;
      [| apply stepMR_tailRest_or_raw_spec].
    destruct (beqListSym lw [1; 0]) eqn:Hlw; [| discriminate].
    apply N.eqb_eq in Hc; subst k.
    apply beqListSym_eq in Hlw; subst lw.
    destruct (sweepMRTailPow 12 false l rest) as [[[c1 prog] l'] rest'] eqn:Hsw.
    pose proof (sweepMRTailPow_spec 12 false l rest c1 prog l' rest' Hsw) as Hsp.
    set (rt' := runs_push (SW_raw [1; 0]) 1 rest').
    assert (Hrt' : runs_denote rt' = [1; 0] *> runs_denote rest').
    { subst rt'. rewrite runs_push_spec. cbn [sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity. }
    assert (Hinit : runs_denote ((SW_raw [1; 0], 1%N) :: rest) = [1; 0] *> runs_denote rest).
    { cbn [runs_denote sw_toList]. change (N.to_nat 1) with 1%nat. rewrite lpow_1. reflexivity. }
    rewrite Hinit. rewrite <- Hrt' in Hsp.
    destruct prog.
    + cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      exact Hsp.
    + pose proof (stepMR_tailRest_or_raw_spec l' rt') as Hfin.
      destruct (match stepMR_tailRest l' rt' with Some s' => Some s' | None => toRawAndStep l' (MkRTape [] [] [] rt') MR end) as [s'|].
      * exact (ev_trans _ _ _ Hsp Hfin).
      * exact (evstep_halts _ _ Hsp Hfin).
Qed.

Definition stepMR (l : Runs) (rt : RTape) : option FastState :=
  match r_raw rt with
  | [] =>
    if hasD rt then Some (stepMR_D l (d_front rt) (d_back rt) (r_tail rt))
    else stepMR_tail l (r_tail rt)
  | [(SW_raw w, k)] =>
    if (if beqListSym w [1] then N.eqb k 1 else false) then
      match popDFrontOneAux (d_front rt) (d_back rt) with
      | Some (n, df', db') =>
        let rtail' := runs_push (SW_raw [1; 0]) 1 (flushDToTail df' db' (r_tail rt)) in
        Some (MkFastState l (MkRTape [] [((n + 1)%N, 1%N)] [] rtail') ML)
      | None =>
        let rt1 := flushAllToTail rt in
        stepMR_tail l (r_tail rt1)
      end
    else
      let rt1 := flushAllToTail rt in
      stepMR_tail l (r_tail rt1)
  | _ =>
    let rt1 := flushAllToTail rt in
    stepMR_tail l (r_tail rt1)
  end.

Lemma flush_step_MR_spec l rt :
  let rt1 := flushAllToTail rt in
  match stepMR_tail l (r_tail rt1) with
  | Some s' => fs_denote (MkFastState l rt MR) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MR))
  end.
Proof.
  cbv zeta.
  pose proof (stepMR_tail_spec l (r_tail (flushAllToTail rt))) as H.
  assert (Hrt : rt_denote rt = runs_denote (r_tail (flushAllToTail rt))).
  { rewrite <- flushAllToTail_spec. reflexivity. }
  cbn [fs_denote fs_L fs_R fs_mode]. rewrite Hrt. exact H.
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
      cbn [fs_denote fs_L fs_R fs_mode].
      unfold rt_denote; cbn [r_raw d_front d_back r_tail plug denD denDRev].
      apply stepMR_tail_spec.
  - destruct w as [lw | | | | | |]; try apply flush_step_MR_spec.
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

Definition hasDLists (df db : Digits) : bool :=
  match df, db with
  | [], [] => false
  | _, _ => true
  end.

Definition availPLCount (cnt step_h : N) (df db : Digits) (rtail : Runs) : N :=
  match rtail with
  | [] => cnt
  | (SW_raw w, k1) :: (SW_D dn, k0) :: _ =>
    if (if beqListSym w [1; 0] then if N.eqb k1 1 then N.eqb dn 0 else false else false) then
      if hasDLists df db then capDiv cnt k0 step_h else 0%N
    else
      match normImmTail (cleanTailZeros rtail) with
      | [] => cnt
      | (SW_raw w', k1') :: (SW_D dn', k0') :: _ =>
        if (if beqListSym w' [1; 0] then if N.eqb k1' 1 then if N.eqb dn' 0 then hasDLists df db else false else false else false) then
          capDiv cnt k0' step_h
        else 0%N
      | _ => 0%N
      end
  | _ =>
    match normImmTail (cleanTailZeros rtail) with
    | [] => cnt
    | (SW_raw w', k1') :: (SW_D dn', k0') :: _ =>
      if (if beqListSym w' [1; 0] then if N.eqb k1' 1 then if N.eqb dn' 0 then hasDLists df db else false else false else false) then
        capDiv cnt k0' step_h
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

Definition unfoldDEF1 (a k cnt : N) (lrest : Runs) : Runs :=
  runs_push (SW_raw [1; 0]) a
    (runs_push (SW_raw [1]) k
      (runs_push (SW_raw [0; 1]) 1
        (runs_push (SW_S 0) 1 (runs_push (SW_DEF a k) cnt lrest)))).

Lemma unfoldDEF1_spec a k cnt lrest :
  runs_denote (unfoldDEF1 a k cnt lrest) =
  runs_denote ((SW_DEF a k, (cnt + 1)%N) :: lrest).
Proof.
  unfold unfoldDEF1.
  rewrite !runs_push_spec.
  cbn [runs_denote sw_toList].
  change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
  replace (N.to_nat (cnt + 1)%N) with (S (N.to_nat cnt)) by lia.
  cbn [lpow]. unfold DefWord.
  rewrite ?app_nil_r, !Str_app_assoc. reflexivity.
Qed.

Definition modeMLJ (isMJ : bool) (l r : side) : Q * tape :=
  if isMJ then CfgJ l r else CfgL l r.

Inductive DefSweepRes :=
| DSR_done (isMJ' : bool) (df' db' : Digits) (rtail' : Runs)
| DSR_toMR (l' : Runs) (df' db' : Digits) (rtail' : Runs)
| DSR_fail.

Definition handleDefInSweep (a k : N) (isMJ : bool) (df db : Digits) (rtail lBase : Runs)
    : DefSweepRes :=
  if N.eqb a 0 then
    if (if negb isMJ then N.eqb k 2 else false) then
      match popDFrontOneAux df db with
      | Some (dn, df', db') => DSR_toMR (pushDEF1 (dn + 1)%N 0 lBase) df' db' rtail
      | None => DSR_fail
      end
    else DSR_fail
  else if negb isMJ then
    let req := (k / 3)%N in
    let rem := (k mod 3)%N in
    if N.eqb req 0 then
      if N.eqb rem 0 then DSR_done false (pushD (a + 1)%N 1 df) db rtail
      else if N.eqb rem 1 then DSR_done false (pushD 0 1 (pushD a 1 df)) db rtail
      else DSR_done false (pushD 0 2 (pushD (a - 1)%N 1 df)) db rtail
    else
      let '(hd, df', db', rtail') := doCallsDUpto 4 0 df db rtail req in
      if N.eqb hd req then
        if N.eqb rem 0 then DSR_done false (pushD (a + 1)%N 1 df') db' rtail'
        else if N.eqb rem 1 then DSR_done false (pushD 0 1 (pushD a 1 df')) db' rtail'
        else DSR_done false (pushD 0 2 (pushD (a - 1)%N 1 df')) db' rtail'
      else
        DSR_toMR (pushDEF1 a (k - 3 * (hd + 1))%N lBase) df' db' rtail'
  else
    if N.eqb k 0 then DSR_fail
    else if N.eqb k 1 then DSR_done false (pushD 0 1 (pushD (a + 1)%N 1 df)) db rtail
    else if N.eqb k 2 then DSR_done false (pushD 0 2 (pushD a 1 df)) db rtail
    else
      let req := (k / 3)%N in
      let rem := (k mod 3)%N in
      let '(hd, df', db', rtail') := doCallsDUpto 4 0 df db rtail req in
      if N.eqb hd req then
        if N.eqb rem 0 then DSR_done false (pushD (a + 2)%N 1 df') db' rtail'
        else if N.eqb rem 1 then DSR_done false (pushD 0 1 (pushD (a + 1)%N 1 df')) db' rtail'
        else DSR_done false (pushD 0 2 (pushD a 1 df')) db' rtail'
      else
        DSR_toMR (pushDEF1 (a + 1)%N (k - 3 - 3 * hd)%N lBase) df' db' rtail'.

Lemma def_rem_ML_spec a rem df db rtail l :
  (1 <= a)%N -> (N.to_nat rem < 3)%nat ->
  let '(isMJ', df') :=
    if N.eqb rem 0 then (false, pushD (a + 1)%N 1 df)
    else if N.eqb rem 1 then (false, pushD 0 1 (pushD a 1 df))
    else (false, pushD 0 2 (pushD (a - 1)%N 1 df)) in
  CfgL (DefWord (N.to_nat a) (N.to_nat rem) *> l) (denD df (denDRev db (runs_denote rtail))) -->*
  modeMLJ isMJ' l (denD df' (denDRev db (runs_denote rtail))).
Proof.
  intros Ha1 Hrem3.
  assert (Ha : (1 <= N.to_nat a)%nat) by lia.
  destruct (N.eqb_spec rem 0) as [-> | Hr0].
  - cbn [modeMLJ]. rewrite denD_pushD.
    change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    replace (N.to_nat (a + 1)%N) with (1 + N.to_nat a)%nat by lia.
    exact (def_k0_ML Ha _ _).
  - destruct (N.eqb_spec rem 1) as [-> | Hr1].
    + cbn [modeMLJ]. rewrite !denD_pushD.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
      apply def_k1_ML.
    + assert (Hr2 : N.to_nat rem = 2%nat) by lia.
      cbn [modeMLJ]. rewrite Hr2, !denD_pushD.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
      cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
      replace (N.to_nat (a - 1)%N) with (N.to_nat a - 1)%nat by lia.
      exact (def_k2_ML Ha _ _).
Qed.

Lemma handleDefInSweep_spec a k isMJ df db rtail lBase :
  match handleDefInSweep a k isMJ df db rtail lBase with
  | DSR_done isMJ' df' db' rtail' =>
    modeMLJ isMJ (DefWord (N.to_nat a) (N.to_nat k) *> runs_denote lBase)
      (denD df (denDRev db (runs_denote rtail))) -->*
    modeMLJ isMJ' (runs_denote lBase) (denD df' (denDRev db' (runs_denote rtail')))
  | DSR_toMR l' df' db' rtail' =>
    modeMLJ isMJ (DefWord (N.to_nat a) (N.to_nat k) *> runs_denote lBase)
      (denD df (denDRev db (runs_denote rtail))) -->*
    CfgR (runs_denote l') (denD df' (denDRev db' (runs_denote rtail')))
  | DSR_fail => True
  end.
Proof.
  unfold handleDefInSweep.
  destruct (N.eqb_spec a 0) as [-> | Ha0].
  - destruct isMJ; cbn [negb modeMLJ]; [exact I |].
    destruct (N.eqb_spec k 2) as [-> | _]; [| exact I].
    destruct (popDFrontOneAux df db) as [[[dn df'] db']|] eqn:Hp; [| exact I].
    rewrite (popDFrontOneAux_spec df db dn df' db' _ Hp), pushDEF1_spec.
    change (N.to_nat 0) with 0%nat. change (N.to_nat 2) with 2%nat.
    replace (N.to_nat (dn + 1)%N) with (N.to_nat dn + 1)%nat by lia.
    apply def_02_ML.
  - assert (Ha1 : (1 <= a)%N) by lia.
    assert (Ha_nat : (1 <= N.to_nat a)%nat) by lia.
    destruct (N_div_mod_3 k) as [Hk_div [Hk_mod [Hk_q Hk_r]]].
    destruct isMJ; cbn [negb modeMLJ].
    + (* isMJ = true *)
      destruct (N.eqb_spec k 0) as [-> | Hk0]; [exact I |].
      destruct (N.eqb_spec k 1) as [-> | Hk1].
      * cbn [modeMLJ]. rewrite !denD_pushD.
        change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
        replace (N.to_nat (a + 1)%N) with (N.to_nat a + 1)%nat by lia.
        apply def_k1_MJ.
      * destruct (N.eqb_spec k 2) as [-> | Hk2].
        { cbn [modeMLJ]. rewrite !denD_pushD.
          change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
          cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
          exact (def_k2_MJ Ha_nat _ _). }
        { assert (Hk3 : (3 <= N.to_nat k)%nat) by lia.
          destruct (doCallsDUpto 4 0 df db rtail (k / 3)%N) as [[[hd df'] db'] rtail'] eqn:Hdc.
          destruct (doCallsDUpto_0_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hle Hc].
          destruct (N.eqb_spec hd (k / 3)%N) as [-> | Hneq].
          - rewrite Hk_q in Hc.
            pose proof (@def_loopJ_to_rem (N.to_nat a) (N.to_nat k) Hk3 _ _ Hc (runs_denote lBase)) as Hstep1.
            rewrite <- Hk_r in Hstep1.
            replace (N.to_nat a + 1)%nat with (N.to_nat (a + 1)%N) in Hstep1 by lia.
            pose proof (def_rem_ML_spec (a + 1)%N (k mod 3)%N df' db' rtail' (runs_denote lBase) ltac:(lia) Hk_mod) as Hstep2.
            replace (a + 1 - 1)%N with a in Hstep2 by lia.
            replace (a + 1 + 1)%N with (a + 2)%N in Hstep2 by lia.
            destruct (N.eqb (k mod 3)%N 0), (N.eqb (k mod 3)%N 1);
              exact (ev_trans _ _ _ Hstep1 Hstep2).
          - assert (Hlt : (N.to_nat hd < N.to_nat k / 3)%nat) by lia.
            rewrite pushDEF1_spec.
            replace (N.to_nat (a + 1)%N) with (N.to_nat a + 1)%nat by lia.
            replace (N.to_nat (k - 3 - 3 * hd)%N) with (N.to_nat k - 3 - 3 * N.to_nat hd)%nat by lia.
            exact (@def_step_MJ_part (N.to_nat a) (N.to_nat k) (N.to_nat hd) Hk3 Hlt _ _ Hc _). }
    + (* isMJ = false *)
      destruct (N.eqb_spec (k / 3)%N 0) as [Hreq0 | Hreq0].
      * assert (Hk_rem : N.to_nat k = N.to_nat (k mod 3)%N) by lia.
        rewrite Hk_rem.
        pose proof (def_rem_ML_spec a (k mod 3)%N df db rtail (runs_denote lBase) Ha1 Hk_mod) as Hsp.
        destruct (N.eqb (k mod 3)%N 0), (N.eqb (k mod 3)%N 1); exact Hsp.
      * destruct (doCallsDUpto 4 0 df db rtail (k / 3)%N) as [[[hd df'] db'] rtail'] eqn:Hdc.
        destruct (doCallsDUpto_0_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hle Hc].
        destruct (N.eqb_spec hd (k / 3)%N) as [-> | Hneq].
        { assert (H3 : (3 * N.to_nat (k / 3)%N <= N.to_nat k)%nat) by lia.
          pose proof (def_loopL Ha_nat H3 Hc (runs_denote lBase)) as Hstep1.
          replace (N.to_nat k - 3 * N.to_nat (k / 3)%N)%nat with (N.to_nat (k mod 3)%N) in Hstep1 by lia.
          pose proof (def_rem_ML_spec a (k mod 3)%N df' db' rtail' (runs_denote lBase) Ha1 Hk_mod) as Hstep2.
          destruct (N.eqb (k mod 3)%N 0), (N.eqb (k mod 3)%N 1);
            exact (ev_trans _ _ _ Hstep1 Hstep2). }
        { assert (Hlt : (N.to_nat hd < N.to_nat k / 3)%nat) by lia.
          rewrite pushDEF1_spec.
          replace (N.to_nat (k - 3 * (hd + 1))%N) with (N.to_nat k - 3 * (N.to_nat hd + 1))%nat by lia.
          exact (def_step_ML_part Ha_nat Hlt Hc _). }
Qed.

Inductive SweepLeftState :=
| SLS_cont (prog isMJ : bool) (l : Runs) (df db : Digits) (rtail : Runs)
| SLS_stop (prog : bool) (l : Runs) (df db : Digits) (rtail : Runs) (m : FMode).

Definition sls_denote (st : SweepLeftState) : Q * tape :=
  match st with
  | SLS_cont _ isMJ l df db rtail =>
    modeMLJ isMJ (runs_denote l) (denD df (denDRev db (runs_denote rtail)))
  | SLS_stop _ l df db rtail m =>
    fs_denote (MkFastState l (MkRTape [] df db rtail) m)
  end.

Definition sweepLeftOne (prog isMJ : bool) (l : Runs) (df db : Digits) (rtail : Runs)
    : SweepLeftState :=
  match l with
  | (_, N0) :: rest => SLS_cont prog isMJ rest df db rtail
  | (SW_S sn, Npos pk) :: rest =>
    let k1 := Npos pk in
    if negb isMJ then
      SLS_cont true false rest (pushD sn k1 df) db rtail
    else
      let k := N.pred k1 in
      SLS_cont true false rest (pushD sn k (pushD (sn + 1)%N 1 df)) db rtail
  | (SW_PL pl_n, Npos pcnt) :: lrest =>
    let cnt1 := Npos pcnt in
    let cnt := N.pred cnt1 in
    let tryDef (_ : unit) :=
      let lBase := if N.eqb cnt 0 then lrest else (SW_PL pl_n, cnt) :: lrest in
      match handleDefInSweep (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db rtail lBase with
      | DSR_done isMJ' df' db' rtail' =>
        SLS_cont true isMJ' lBase df' db' rtail'
      | DSR_toMR l' df' db' rtail' => SLS_stop true l' df' db' rtail' MR
      | DSR_fail => SLS_stop prog l df db rtail (if isMJ then MJ else ML)
      end in
    if (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) then
      let n := ((pl_n - 1) / 3)%N in
      let step_h := (1 + n * 2)%N in
      let mc := availPLCount cnt1 step_h df db rtail in
      if (if N.eqb mc 0 then true else N.ltb cnt1 mc) then tryDef tt
      else
        let req := (step_h * mc)%N in
        match doCallsD df db rtail req false with
        | Some (hd, df', db', rtail') =>
          if N.eqb hd req then
            let rem := (cnt1 - mc)%N in
            let l' := if N.eqb rem 0 then lrest else (SW_PL pl_n, rem) :: lrest in
            let d6 := (6 + n * 3)%N in
            let df'' :=
              if negb isMJ then pushD d6 mc df'
              else pushD d6 (mc - 1)%N (pushD (7 + n * 3)%N 1 df') in
            SLS_cont true false l' df'' db' rtail'
          else tryDef tt
        | None => tryDef tt
        end
    else tryDef tt
  | (SW_DEF a k, Npos pcnt) :: lrest =>
    let cnt := N.pred (Npos pcnt) in
    let lBase := if N.eqb cnt 0 then lrest else (SW_DEF a k, cnt) :: lrest in
    match handleDefInSweep a k isMJ df db rtail lBase with
    | DSR_done isMJ' df' db' rtail' =>
      SLS_cont true isMJ' lBase df' db' rtail'
    | DSR_toMR l' df' db' rtail' => SLS_stop true l' df' db' rtail' MR
    | DSR_fail => SLS_stop prog l df db rtail (if isMJ then MJ else ML)
    end
  | _ => SLS_stop prog l df db rtail (if isMJ then MJ else ML)
  end.

Lemma sls_stop_same prog isMJ l df db rtail :
  sls_denote (SLS_cont prog isMJ l df db rtail) =
  sls_denote (SLS_stop prog l df db rtail (if isMJ then MJ else ML)).
Proof.
  destruct isMJ; reflexivity.
Qed.

Lemma sweepLeftOne_spec prog isMJ l df db rtail :
  sls_denote (SLS_cont prog isMJ l df db rtail) -->*
  sls_denote (sweepLeftOne prog isMJ l df db rtail).
Proof.
  destruct l as [|[w [|pk]] rest].
  - cbn [sweepLeftOne]. rewrite <- sls_stop_same. apply evstep_refl.
  - destruct w; change (N.to_nat 0) with 0%nat; cbn [sweepLeftOne sls_denote runs_denote lpow Str_app]; apply evstep_refl.
  - destruct w as [lw | dn | sn | pl_n | a k | ds | ds];
      try (cbn [sweepLeftOne]; rewrite <- sls_stop_same; apply evstep_refl).
    + (* SW_S sn *)
      cbv beta iota zeta delta [sweepLeftOne].
      destruct isMJ; cbn [negb sls_denote modeMLJ runs_denote sw_toList].
      * rewrite (pos_to_nat_succ pk), !denD_pushD.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat (sn + 1)%N) with (1 + N.to_nat sn)%nat by lia.
        change (S (N.to_nat (N.pred (Npos pk)))) with (1 + N.to_nat (N.pred (Npos pk)))%nat.
        apply leftJ_S_run.
      * rewrite denD_pushD. apply leftS_run.
    + (* SW_PL pl_n *)
      cbv beta iota zeta delta [sweepLeftOne].
      set (cnt1 := Npos pk).
      set (cnt := N.pred cnt1).
      set (lBase := if N.eqb cnt 0 then rest else (SW_PL pl_n, cnt) :: rest).
      set (tryDef :=
        match handleDefInSweep (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db rtail lBase with
        | DSR_done isMJ' df' db' rtail' => SLS_cont true isMJ' lBase df' db' rtail'
        | DSR_toMR l' df' db' rtail' => SLS_stop true l' df' db' rtail' MR
        | DSR_fail => SLS_stop prog ((SW_PL pl_n, cnt1) :: rest) df db rtail (if isMJ then MJ else ML)
        end).
      assert (Htd : sls_denote (SLS_cont prog isMJ ((SW_PL pl_n, cnt1) :: rest) df db rtail) -->* sls_denote tryDef).
      { subst tryDef.
        pose proof (handleDefInSweep_spec (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db rtail lBase) as Hsp.
        assert (Hlhs :
          runs_denote ((SW_PL pl_n, cnt1) :: rest) =
          DefWord (N.to_nat (pl_n + 4)%N) (N.to_nat (2 * pl_n + 1)%N) *> runs_denote lBase).
        { subst lBase cnt cnt1. rewrite opt_run_denote.
          cbn [runs_denote sw_toList]. rewrite (pos_to_nat_succ pk). cbn [lpow].
          rewrite Str_app_assoc, (pl_eq_def (N.to_nat pl_n)).
          replace (N.to_nat (pl_n + 4)%N) with (N.to_nat pl_n + 4)%nat by lia.
          replace (N.to_nat (2 * pl_n + 1)%N) with (2 * N.to_nat pl_n + 1)%nat by lia.
          reflexivity. }
        destruct (handleDefInSweep (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db rtail lBase) as [isMJ' df' db' rtail' | l' df' db' rtail' |].
        - cbn [sls_denote]. rewrite Hlhs. exact Hsp.
        - cbn [sls_denote fs_denote fs_L fs_R fs_mode].
          unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
          rewrite Hlhs. exact Hsp.
        - rewrite <- sls_stop_same. apply evstep_refl. }
      destruct (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) eqn:Hc1; [| exact Htd].
      destruct (N.leb_spec 1 pl_n) as [Hpl1 | _]; [| discriminate].
      apply N.eqb_eq in Hc1.
      set (n := ((pl_n - 1) / 3)%N).
      set (step_h := (1 + n * 2)%N).
      set (mc := availPLCount cnt1 step_h df db rtail).
      destruct (if N.eqb mc 0 then true else N.ltb cnt1 mc) eqn:Hmc; [exact Htd |].
      destruct (N.eqb_spec mc 0) as [_ | Hmc0]; [discriminate |].
      destruct (N.ltb_spec cnt1 mc) as [_ | Hmc_le]; [discriminate |].
      set (req := (step_h * mc)%N).
      destruct (doCallsD df db rtail req false) as [[[[hd df'] db'] rtail']|] eqn:Hdc; [| exact Htd].
      destruct (N.eqb_spec hd req) as [-> | _]; [| exact Htd].
      destruct (doCallsD_spec _ _ _ _ _ _ _ _ _ Hdc) as [_ [_ Hcalls]].
      destruct (N_div_mod_3 (pl_n - 1)%N) as [Hdiv3 _].
      assert (Hpln : N.to_nat pl_n = (1 + N.to_nat n * 3)%nat) by (subst n; lia).
      cbn [sls_denote]. rewrite opt_run_denote. cbn [runs_denote sw_toList].
      destruct isMJ; cbn [negb modeMLJ].
      * (* MJ *)
        rewrite !denD_pushD.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat cnt1) with ((1 + N.to_nat (mc - 1)%N) + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat (7 + n * 3)%N) with (7 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with ((1 + N.to_nat (mc - 1)%N) * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_J (N.to_nat (mc - 1)%N) (N.to_nat n) Hcalls _).
      * (* ML *)
        rewrite denD_pushD.
        replace (N.to_nat cnt1) with (N.to_nat mc + N.to_nat (cnt1 - mc)%N)%nat at 1 by lia.
        rewrite lpow_add, Str_app_assoc, Hpln.
        replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
        replace (N.to_nat req) with (N.to_nat mc * (1 + N.to_nat n * 2))%nat in Hcalls
          by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
        exact (returnsP_L0 (N.to_nat mc) (N.to_nat n) Hcalls _).
    + (* SW_DEF a k *)
      cbv beta iota zeta delta [sweepLeftOne].
      set (cnt := N.pred (Npos pk)).
      set (lBase := if N.eqb cnt 0 then rest else (SW_DEF a k, cnt) :: rest).
      pose proof (handleDefInSweep_spec a k isMJ df db rtail lBase) as Hsp.
      assert (Hlhs :
        runs_denote ((SW_DEF a k, Npos pk) :: rest) =
        DefWord (N.to_nat a) (N.to_nat k) *> runs_denote lBase).
      { subst lBase cnt. rewrite opt_run_denote. cbn [runs_denote sw_toList].
        rewrite (pos_to_nat_succ pk). cbn [lpow]. rewrite Str_app_assoc. reflexivity. }
      destruct (handleDefInSweep a k isMJ df db rtail lBase) as [isMJ' df' db' rtail' | l' df' db' rtail' |].
      * cbn [sls_denote]. rewrite Hlhs. exact Hsp.
      * cbn [sls_denote fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
        rewrite Hlhs. exact Hsp.
      * rewrite <- sls_stop_same. apply evstep_refl.
Qed.

Fixpoint sweepLeftPow (k : nat) (st : SweepLeftState) : SweepLeftState :=
  match st with
  | SLS_stop _ _ _ _ _ _ => st
  | SLS_cont prog isMJ l df db rtail =>
    match k with
    | O => sweepLeftOne prog isMJ l df db rtail
    | S k' => sweepLeftPow k' (sweepLeftPow k' st)
    end
  end.

Lemma sweepLeftPow_spec k st :
  sls_denote st -->* sls_denote (sweepLeftPow k st).
Proof.
  revert st. induction k as [|k IH]; intros [prog isMJ l df db rtail | prog l df db rtail m]; cbn [sweepLeftPow].
  - apply sweepLeftOne_spec.
  - apply evstep_refl.
  - eapply ev_trans; [apply IH | apply IH].
  - apply evstep_refl.
Qed.

Definition sweepLeftRun (k : nat) (prog isMJ : bool) (l : Runs) (df db : Digits) (rtail : Runs)
    : bool * Runs * Digits * Digits * Runs * FMode :=
  match sweepLeftPow k (SLS_cont prog isMJ l df db rtail) with
  | SLS_cont p m l' df' db' rt' => (p, l', df', db', rt', if m then MJ else ML)
  | SLS_stop p l' df' db' rt' m' => (p, l', df', db', rt', m')
  end.

Lemma sweepLeftRun_spec k prog isMJ l df db rtail p l' df' db' rtail' m' :
  sweepLeftRun k prog isMJ l df db rtail = (p, l', df', db', rtail', m') ->
  modeMLJ isMJ (runs_denote l) (denD df (denDRev db (runs_denote rtail))) -->*
  fs_denote (MkFastState l' (MkRTape [] df' db' rtail') m').
Proof.
  unfold sweepLeftRun.
  pose proof (sweepLeftPow_spec k (SLS_cont prog isMJ l df db rtail)) as Hsp.
  cbn [sls_denote] in Hsp.
  destruct (sweepLeftPow k (SLS_cont prog isMJ l df db rtail)) as [p1 m1 l1 df1 db1 rt1 | p1 l1 df1 db1 rt1 m1];
    intros H; inversion H; subst; clear H.
  - rewrite sls_stop_same in Hsp. cbn [sls_denote] in Hsp. exact Hsp.
  - cbn [sls_denote] in Hsp. exact Hsp.
Qed.

Definition sweepLeftBlankDef1 (a k : N) (isMJ : bool) (df db : Digits)
    : bool * Digits * Digits :=
  let req := (k / 3)%N in
  let rem := (k mod 3)%N in
  let db' := pushD 0 (mul2 req) db in
  if negb isMJ then
    if N.eqb rem 0 then (false, pushD (a + 1)%N 1 df, db')
    else if N.eqb rem 1 then (false, pushD 0 1 (pushD a 1 df), db')
    else (false, pushD 0 2 (pushD (a - 1)%N 1 df), db')
  else
    if N.eqb rem 0 then (false, pushD (a + 2)%N 1 df, db')
    else if N.eqb rem 1 then (false, pushD 0 1 (pushD (a + 1)%N 1 df), db')
    else (false, pushD 0 2 (pushD a 1 df), db').

Lemma sweepLeftBlankDef1_spec a k isMJ df db isMJ' df' db' l :
  (1 <= a)%N -> (isMJ = false \/ (1 <= k)%N) ->
  sweepLeftBlankDef1 a k isMJ df db = (isMJ', df', db') ->
  modeMLJ isMJ (DefWord (N.to_nat a) (N.to_nat k) *> l) (denD df (denDRev db 0inf)) -->*
  modeMLJ isMJ' l (denD df' (denDRev db' 0inf)).
Proof.
  intros Ha1 Hk_or H. unfold sweepLeftBlankDef1 in H.
  assert (Ha_nat : (1 <= N.to_nat a)%nat) by lia.
  destruct (N_div_mod_3 k) as [Hk_div [Hk_mod [Hk_q Hk_r]]].
  set (req := (k / 3)%N) in *.
  set (rem := (k mod 3)%N) in *.
  set (db1 := pushD 0 (mul2 req) db) in *.
  assert (Hcalls : calls (N.to_nat req) (denD df (denDRev db 0inf)) (denD df (denDRev db1 0inf))).
  { subst db1. rewrite denDRev_pushD, mul2_eq.
    replace (N.to_nat (req * 2)%N) with (N.to_nat req * 2)%nat by lia.
    exact (calls_denD df (calls_denDRev db (calls_blank (N.to_nat req)))). }
  change 0inf with (runs_denote []) in *.
  destruct isMJ; cbn [negb] in H.
  - (* isMJ = true *)
    destruct Hk_or as [Hfalse | Hk1]; [discriminate |].
    destruct (N.eqb_spec k 1) as [Hk_eq1 | Hk_ne1].
    + assert (Hreq0 : req = 0%N) by (subst req; lia).
      assert (Hrem1 : rem = 1%N) by (subst rem; lia).
      rewrite Hrem1 in H; cbn [N.eqb] in H.
      inj_triple H.
      subst db1; rewrite Hreq0; cbn [mul2 pushD modeMLJ].
      rewrite Hk_eq1, !denD_pushD.
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite !lpow_1.
      replace (N.to_nat (a + 1)%N) with (N.to_nat a + 1)%nat by lia.
      apply def_k1_MJ.
    + destruct (N.eqb_spec k 2) as [Hk_eq2 | Hk_ne2].
      * assert (Hreq0 : req = 0%N) by (subst req; lia).
        assert (Hrem2 : rem = 2%N) by (subst rem; lia).
        rewrite Hrem2 in H; cbn [N.eqb] in H.
        inj_triple H.
        subst db1; rewrite Hreq0; cbn [mul2 pushD modeMLJ].
        rewrite Hk_eq2, !denD_pushD.
        change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
        cbn [lpow]. rewrite ?app_nil_r, !Str_app_assoc.
        exact (def_k2_MJ Ha_nat _ _).
      * assert (Hk3 : (3 <= N.to_nat k)%nat) by lia.
        subst req; rewrite Hk_q in Hcalls.
        pose proof (@def_loopJ_to_rem (N.to_nat a) (N.to_nat k) Hk3 _ _ Hcalls l) as Hstep1.
        rewrite <- Hk_r in Hstep1.
        replace (N.to_nat a + 1)%nat with (N.to_nat (a + 1)%N) in Hstep1 by lia.
        pose proof (def_rem_ML_spec (a + 1)%N rem df db1 [] l ltac:(lia) Hk_mod) as Hstep2.
        replace (a + 1 - 1)%N with a in Hstep2 by lia.
        replace (a + 1 + 1)%N with (a + 2)%N in Hstep2 by lia.
        destruct (N.eqb rem 0), (N.eqb rem 1); inj_triple H;
          exact (ev_trans _ _ _ Hstep1 Hstep2).
  - (* isMJ = false *)
    assert (H3 : (3 * N.to_nat req <= N.to_nat k)%nat) by (subst req; lia).
    pose proof (def_loopL Ha_nat H3 Hcalls l) as Hstep1.
    replace (N.to_nat k - 3 * N.to_nat req)%nat with (N.to_nat rem) in Hstep1 by (subst req rem; lia).
    pose proof (def_rem_ML_spec a rem df db1 [] l Ha1 Hk_mod) as Hstep2.
    destruct (N.eqb rem 0), (N.eqb rem 1); inj_triple H;
      exact (ev_trans _ _ _ Hstep1 Hstep2).
Qed.

Definition sweepLeftBlankDefLoop (p : positive) (a k : N) (isMJ : bool) (df db : Digits)
    : bool * Digits * Digits :=
  Pos.iter
    (fun '(m, f, b) => sweepLeftBlankDef1 a k m f b)
    (isMJ, df, db)
    p.

Lemma sweepLeftBlankDefNat_spec cnt a k isMJ df db isMJ' df' db' l :
  (1 <= a)%N -> (1 <= k)%N ->
  Nat.iter cnt (fun '(m, f, b) => sweepLeftBlankDef1 a k m f b) (isMJ, df, db) = (isMJ', df', db') ->
  modeMLJ isMJ ((DefWord (N.to_nat a) (N.to_nat k))^^cnt *> l) (denD df (denDRev db 0inf)) -->*
  modeMLJ isMJ' l (denD df' (denDRev db' 0inf)).
Proof.
  intros Ha1 Hk1.
  revert isMJ df db.
  induction cnt as [|cnt IH]; intros isMJ df db H.
  - cbn [Nat.iter] in H; inj_triple H; cbn [lpow Str_app]. apply evstep_refl.
  - rewrite iter_succ_r in H.
    destruct (sweepLeftBlankDef1 a k isMJ df db) as [[m1 df1] db1] eqn:H1.
    cbn [lpow]. rewrite Str_app_assoc.
    eapply ev_trans.
    + exact (sweepLeftBlankDef1_spec a k isMJ df db m1 df1 db1 _ Ha1 (or_intror Hk1) H1).
    + exact (IH m1 df1 db1 H).
Qed.

Lemma sweepLeftBlankDefLoop_spec p a k isMJ df db isMJ' df' db' l :
  (1 <= a)%N -> (1 <= k)%N ->
  sweepLeftBlankDefLoop p a k isMJ df db = (isMJ', df', db') ->
  modeMLJ isMJ ((DefWord (N.to_nat a) (N.to_nat k))^^(Pos.to_nat p) *> l) (denD df (denDRev db 0inf)) -->*
  modeMLJ isMJ' l (denD df' (denDRev db' 0inf)).
Proof.
  unfold sweepLeftBlankDefLoop. rewrite Pos2Nat.inj_iter.
  apply sweepLeftBlankDefNat_spec.
Qed.

Fixpoint sweepLeftBlank (l : Runs) (prog isMJ : bool) (df db : Digits)
    : bool * Runs * Digits * Digits * bool :=
  match l with
  | [] => (prog, [], df, db, isMJ)
  | (_, N0) :: rest => sweepLeftBlank rest prog isMJ df db
  | (SW_S sn, Npos pc) :: rest =>
    let cnt1 := Npos pc in
    if negb isMJ then sweepLeftBlank rest true false (pushD sn cnt1 df) db
    else sweepLeftBlank rest true false (pushD sn (N.pred cnt1) (pushD (sn + 1)%N 1 df)) db
  | (SW_PL pl_n, Npos pc) :: rest =>
    let cnt1 := Npos pc in
    if (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) then
      let n := ((pl_n - 1) / 3)%N in
      let step_h := (1 + n * 2)%N in
      let req := (step_h * cnt1)%N in
      let d6 := (6 + n * 3)%N in
      let df'' :=
        if negb isMJ then pushD d6 cnt1 df
        else pushD d6 (N.pred cnt1) (pushD (7 + n * 3)%N 1 df) in
      sweepLeftBlank rest true false df'' (pushD 0 (mul2 req) db)
    else
      let '(isMJ', df', db') := sweepLeftBlankDefLoop pc (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db in
      sweepLeftBlank rest true isMJ' df' db'
  | (SW_DEF a k, Npos pc) :: rest =>
    if N.leb 1 a then
      if N.leb 1 k then
        let '(isMJ', df', db') := sweepLeftBlankDefLoop pc a k isMJ df db in
        sweepLeftBlank rest true isMJ' df' db'
      else if negb isMJ then
        let '(isMJ', df', db') := sweepLeftBlankDef1 a k false df db in
        let c := N.pred (Npos pc) in
        if N.eqb c 0 then sweepLeftBlank rest true isMJ' df' db'
        else (true, (SW_DEF a k, c) :: rest, df', db', isMJ')
      else (prog, l, df, db, isMJ)
    else (prog, l, df, db, isMJ)
  | _ => (prog, l, df, db, isMJ)
  end.

Lemma sweepLeftBlank_spec l prog isMJ df db prog' l' df' db' isMJ' :
  sweepLeftBlank l prog isMJ df db = (prog', l', df', db', isMJ') ->
  modeMLJ isMJ (runs_denote l) (denD df (denDRev db 0inf)) -->*
  modeMLJ isMJ' (runs_denote l') (denD df' (denDRev db' 0inf)).
Proof.
  revert prog isMJ df db.
  induction l as [|[w [|pc]] rest IH]; intros prog isMJ df db H.
  - cbn [sweepLeftBlank] in H; inj_quint H; apply evstep_refl.
  - destruct w; change (N.to_nat 0) with 0%nat; cbn [sweepLeftBlank runs_denote lpow Str_app] in H |- *; exact (IH _ _ _ _ H).
  - destruct w as [lw | dn | sn | pl_n | a k | ds | ds];
      try (cbv beta iota zeta delta [sweepLeftBlank] in H; inj_quint H; apply evstep_refl).
    + (* SW_S sn *)
      cbv beta iota zeta delta [sweepLeftBlank] in H.
      destruct isMJ; cbn [negb] in H; cbn [modeMLJ runs_denote sw_toList].
      * eapply ev_trans; [| exact (IH _ _ _ _ H)].
        rewrite (pos_to_nat_succ pc), !denD_pushD.
        change (N.to_nat 1) with 1%nat. rewrite lpow_1.
        replace (N.to_nat (sn + 1)%N) with (1 + N.to_nat sn)%nat by lia.
        change (S (N.to_nat (N.pred (Npos pc)))) with (1 + N.to_nat (N.pred (Npos pc)))%nat.
        apply leftJ_S_run.
      * eapply ev_trans; [| exact (IH _ _ _ _ H)].
        rewrite denD_pushD. apply leftS_run.
    + (* SW_PL pl_n *)
      cbv beta iota zeta delta [sweepLeftBlank] in H.
      destruct (if N.leb 1 pl_n then N.eqb ((pl_n - 1) mod 3) 0 else false) eqn:Hc1.
      * destruct (N.leb_spec 1 pl_n) as [Hpl1 | _]; [| discriminate].
        apply N.eqb_eq in Hc1.
        set (n := ((pl_n - 1) / 3)%N) in *.
        set (step_h := (1 + n * 2)%N) in *.
        set (cnt1 := Npos pc) in *.
        set (req := (step_h * cnt1)%N) in *.
        set (db1 := pushD 0 (mul2 req) db) in *.
        assert (Hcalls : calls (N.to_nat req) (denD df (denDRev db 0inf)) (denD df (denDRev db1 0inf))).
        { subst db1. rewrite denDRev_pushD, mul2_eq.
          replace (N.to_nat (req * 2)%N) with (N.to_nat req * 2)%nat by lia.
          exact (calls_denD df (calls_denDRev db (calls_blank (N.to_nat req)))). }
        destruct (N_div_mod_3 (pl_n - 1)%N) as [Hdiv3 _].
        assert (Hpln : N.to_nat pl_n = (1 + N.to_nat n * 3)%nat) by (subst n; lia).
        eapply ev_trans; [| exact (IH _ _ _ _ H)].
        cbn [runs_denote sw_toList]. rewrite Hpln.
        destruct isMJ; cbn [negb modeMLJ].
        { unfold cnt1 in *; rewrite !denD_pushD, (pos_to_nat_succ pc).
          change (N.to_nat 1) with 1%nat. rewrite lpow_1.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat (7 + n * 3)%N) with (7 + N.to_nat n * 3)%nat by lia.
          change (S (N.to_nat (N.pred (Npos pc)))) with (1 + N.to_nat (N.pred (Npos pc)))%nat.
          replace (N.to_nat req) with ((1 + N.to_nat (N.pred (Npos pc))) * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_J (N.to_nat (N.pred (Npos pc))) (N.to_nat n) Hcalls _). }
        { rewrite denD_pushD.
          replace (N.to_nat (6 + n * 3)%N) with (6 + N.to_nat n * 3)%nat by lia.
          replace (N.to_nat req) with (N.to_nat cnt1 * (1 + N.to_nat n * 2))%nat in Hcalls
            by (subst req step_h; rewrite N2Nat.inj_mul, Nat.mul_comm; f_equal; lia).
          exact (returnsP_L0 (N.to_nat cnt1) (N.to_nat n) Hcalls _). }
      * destruct (sweepLeftBlankDefLoop pc (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db) as [[m1 df1] db1] eqn:Hloop.
        eapply ev_trans; [| exact (IH _ _ _ _ H)].
        cbn [runs_denote sw_toList]. rewrite (pl_eq_def (N.to_nat pl_n)).
        replace (N.to_nat pl_n + 4)%nat with (N.to_nat (pl_n + 4)%N) by lia.
        replace (2 * N.to_nat pl_n + 1)%nat with (N.to_nat (2 * pl_n + 1)%N) by lia.
        exact (sweepLeftBlankDefLoop_spec pc (pl_n + 4)%N (2 * pl_n + 1)%N isMJ df db m1 df1 db1 _ ltac:(lia) ltac:(lia) Hloop).
    + (* SW_DEF a k *)
      cbv beta iota zeta delta [sweepLeftBlank] in H.
      destruct (N.leb_spec 1 a) as [Ha1 | _]; [| inj_quint H; apply evstep_refl].
      destruct (N.leb_spec 1 k) as [Hk1 | _].
      * destruct (sweepLeftBlankDefLoop pc a k isMJ df db) as [[m1 df1] db1] eqn:Hloop.
        eapply ev_trans; [| exact (IH _ _ _ _ H)].
        cbn [runs_denote sw_toList].
        exact (sweepLeftBlankDefLoop_spec pc a k isMJ df db m1 df1 db1 _ Ha1 Hk1 Hloop).
      * destruct isMJ; cbn [negb] in H; [inj_quint H; apply evstep_refl |].
        destruct (sweepLeftBlankDef1 a k false df db) as [[m1 df1] db1] eqn:H1.
        set (c := N.pred (Npos pc)) in *.
        pose proof (sweepLeftBlankDef1_spec a k false df db m1 df1 db1
          (runs_denote (if N.eqb c 0 then rest else (SW_DEF a k, c) :: rest))
          Ha1 (or_introl eq_refl) H1) as Hsp1.
        assert (Hlhs :
          runs_denote ((SW_DEF a k, Npos pc) :: rest) =
          DefWord (N.to_nat a) (N.to_nat k) *>
            runs_denote (if N.eqb c 0 then rest else (SW_DEF a k, c) :: rest)).
        { subst c. rewrite opt_run_denote. cbn [runs_denote sw_toList].
          rewrite (pos_to_nat_succ pc). cbn [lpow]. rewrite Str_app_assoc. reflexivity. }
        rewrite Hlhs.
        destruct (N.eqb_spec c 0) as [Hc0 | Hc0].
        { eapply ev_trans; [exact Hsp1 | exact (IH _ _ _ _ H)]. }
        { inj_quint H; exact Hsp1. }
Qed.

Definition sweepLeftFinish (prog : bool) (l' : Runs) (df' db' : Digits) (rtail' : Runs) (m' : FMode)
    : option FastState :=
  if prog then Some (MkFastState l' (MkRTape [] df' db' rtail') m')
  else
    match l' with
    | (SW_PL pl_n, Npos pcnt) :: lrest =>
      Some (MkFastState (unfoldPL1 pl_n (N.pred (Npos pcnt)) lrest) (MkRTape [] df' db' rtail') m')
    | (SW_DEF a k, Npos pcnt) :: lrest =>
      Some (MkFastState (unfoldDEF1 a k (N.pred (Npos pcnt)) lrest) (MkRTape [] df' db' rtail') m')
    | _ => None
    end.

Lemma sweepLeftFinish_spec prog l' df' db' rtail' m' s' :
  sweepLeftFinish prog l' df' db' rtail' m' = Some s' ->
  fs_denote (MkFastState l' (MkRTape [] df' db' rtail') m') = fs_denote s'.
Proof.
  unfold sweepLeftFinish.
  destruct prog; [intros H; inj_some H; reflexivity |].
  destruct l' as [|[[| | | pl_n | a k | |] [|pcnt]] lrest]; try discriminate.
  - intros H; inj_some H.
    destruct m' as [| | | q [|]]; cbn [fs_denote fs_L fs_R fs_mode];
      rewrite unfoldPL1_spec; replace (N.pred (Npos pcnt) + 1)%N with (Npos pcnt) by lia; reflexivity.
  - intros H; inj_some H.
    destruct m' as [| | | q [|]]; cbn [fs_denote fs_L fs_R fs_mode];
      rewrite unfoldDEF1_spec; replace (N.pred (Npos pcnt) + 1)%N with (Npos pcnt) by lia; reflexivity.
Qed.

Definition sweepLeftSuperBody (fuel : nat) (isMJ : bool) (l : Runs) (rt : RTape) : option FastState :=
  let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
  match r_tail rt1 with
  | [] =>
    let '(prog1, l1, df1, db1, isMJ1) := sweepLeftBlank l false isMJ (d_front rt1) (d_back rt1) in
    match l1 with
    | (SW_S _, _) :: _ | (SW_PL _, _) :: _ | (SW_DEF _ _, _) :: _ =>
      let '(prog2, l', df', db', rtail', m') := sweepLeftRun fuel prog1 isMJ1 l1 df1 db1 [] in
      sweepLeftFinish prog2 l' df' db' rtail' m'
    | _ => sweepLeftFinish prog1 l1 df1 db1 [] (if isMJ1 then MJ else ML)
    end
  | _ :: _ =>
    let '(prog2, l', df', db', rtail', m') :=
      sweepLeftRun fuel false isMJ l (d_front rt1) (d_back rt1) (r_tail rt1) in
    sweepLeftFinish prog2 l' df' db' rtail' m'
  end.

Lemma sweepLeftSuperBody_spec fuel isMJ l rt s' :
  sweepLeftSuperBody fuel isMJ l rt = Some s' ->
  fs_denote (MkFastState l rt (if isMJ then MJ else ML)) -->* fs_denote s'.
Proof.
  unfold sweepLeftSuperBody.
  set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
  pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
  assert (Hinit :
    fs_denote (MkFastState l rt (if isMJ then MJ else ML)) =
    modeMLJ isMJ (runs_denote l) (denD (d_front rt1) (denDRev (d_back rt1) (runs_denote (r_tail rt1))))).
  { destruct isMJ; cbn [fs_denote fs_L fs_R fs_mode modeMLJ]; rewrite Hrt1; reflexivity. }
  rewrite Hinit.
  destruct (r_tail rt1) as [|x xs].
  - cbn [runs_denote].
    destruct (sweepLeftBlank l false isMJ (d_front rt1) (d_back rt1)) as [[[[prog1 l1] df1] db1] isMJ1] eqn:Hsb.
    pose proof (sweepLeftBlank_spec l false isMJ (d_front rt1) (d_back rt1) prog1 l1 df1 db1 isMJ1 Hsb) as Hsp1.
    set (runRest :=
      let '(prog2, l', df', db', rtail', m') := sweepLeftRun fuel prog1 isMJ1 l1 df1 db1 [] in
      sweepLeftFinish prog2 l' df' db' rtail' m').
    assert (Hrr : forall Hs : runRest = Some s',
      modeMLJ isMJ1 (runs_denote l1) (denD df1 (denDRev db1 0inf)) -->* fs_denote s').
    { subst runRest.
      destruct (sweepLeftRun fuel prog1 isMJ1 l1 df1 db1 []) as [[[[[prog2 l'] df'] db'] rtail'] m'] eqn:Hrun.
      intros Hs. rewrite <- (sweepLeftFinish_spec _ _ _ _ _ _ _ Hs).
      exact (sweepLeftRun_spec _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun). }
    assert (Hfin : forall Hs : sweepLeftFinish prog1 l1 df1 db1 [] (if isMJ1 then MJ else ML) = Some s',
      modeMLJ isMJ1 (runs_denote l1) (denD df1 (denDRev db1 0inf)) -->* fs_denote s').
    { intros Hs. rewrite <- (sweepLeftFinish_spec _ _ _ _ _ _ _ Hs).
      destruct isMJ1; cbn [modeMLJ fs_denote fs_L fs_R fs_mode];
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug runs_denote]; apply evstep_refl. }
    destruct l1 as [|[w1 k1] l1rest]; [intros Hs; exact (ev_trans _ _ _ Hsp1 (Hfin Hs)) |].
    destruct w1 as [| | | | | |];
      intros Hs; (exact (ev_trans _ _ _ Hsp1 (Hrr Hs)) || exact (ev_trans _ _ _ Hsp1 (Hfin Hs))).
  - destruct (sweepLeftRun fuel false isMJ l (d_front rt1) (d_back rt1) (x :: xs))
      as [[[[[prog2 l'] df'] db'] rtail'] m'] eqn:Hrun.
    intros Hs. rewrite <- (sweepLeftFinish_spec _ _ _ _ _ _ _ Hs).
    exact (sweepLeftRun_spec _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun).
Qed.

Definition sweepLeftSuper (isMJ : bool) (l : Runs) (rt : RTape) : option FastState :=
  match l with
  | (SW_S _, _) :: _ | (SW_PL _, _) :: _ | (SW_DEF _ _, _) :: _ =>
    sweepLeftSuperBody 12 isMJ l rt
  | _ => None
  end.

Lemma sweepLeftSuper_spec isMJ l rt s' :
  sweepLeftSuper isMJ l rt = Some s' ->
  fs_denote (MkFastState l rt (if isMJ then MJ else ML)) -->* fs_denote s'.
Proof.
  destruct l as [|[w k] rest]; [discriminate |].
  destruct w as [| | | | | |]; cbn [sweepLeftSuper]; try discriminate;
    apply sweepLeftSuperBody_spec.
Qed.

Definition stepML_raw (l : Runs) (rt : RTape) : option FastState :=
  let '(b1, l1) := take10 l in
  if N.eqb b1 0 then None
  else
    let '(c111, l2) := take111 l1 in
    if negb (N.eqb c111 0) then
      match r_raw rt with
      | [] =>
        let '(hd, df', db', rtail') := doCallsDUpto 16 0 (d_front rt) (d_back rt) (r_tail rt) c111 in
        if negb (N.eqb hd 0) then
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - hd)%N l2) in
          Some (MkFastState l' (MkRTape [] df' db' rtail') ML)
        else
          let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
          Some (MkFastState l' rt MR)
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
      intros H; inj_some H.
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
      intros H; inj_some H.
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
    + destruct (doCallsDUpto 16 0 df db rtail c111) as [[[hd df'] db'] rtail'] eqn:Hdc.
      destruct (N.eqb_spec hd 0) as [-> | Hhd0]; cbn [negb].
      * intros H; inj_some H; exact Hrestart.
      * intros H; inj_some H.
        destruct (doCallsDUpto_0_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hle Hcalls].
        cbn [fs_denote fs_L fs_R fs_mode].
        unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
        rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
        replace (N.to_nat b1) with (1 + N.to_nat (b1 - 1)%N)%nat by lia.
        replace (N.to_nat c111) with (N.to_nat hd + N.to_nat (c111 - hd)%N)%nat at 1 by lia.
        rewrite <- (lpow_Str_add [1; 1; 1]).
        exact (loopL Hcalls _ (N.to_nat (b1 - 1)%N)).
    + intros H; inj_some H; exact Hrestart.
Qed.

Definition stepML_col (l : Runs) (rt : RTape) : option FastState :=
  match runs_remove [0; 0; 1; 1; 0; 1] l with
  | Some l' =>
    match takeDRTape rt with
    | Some (dn, rt') =>
      let rt1 := match r_raw rt' with [] => rt' | _ :: _ => flushAllToTail rt' end in
      Some (MkFastState l' (MkRTape [] (pushD (dn + 3)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) ML)
    | None =>
      Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1; 1; 1; 1; 1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) ML)
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
    replace (N.to_nat (dn + 3)%N) with (3 + N.to_nat dn)%nat by lia.
    apply rule_collisionD.
  - cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_remove_spec _ _ _ Hr).
    unfold rt_denote; cbn [r_raw d_front d_back r_tail].
    rewrite push_plug. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    apply rule_collision.
Qed.

Definition stepML_afterZero1 (l : Runs) (rt : RTape) : option FastState :=
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

Lemma stepML_afterZero1_spec l rt :
  match stepML_afterZero1 l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML_afterZero1.
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

Definition stepML_tailRest (l : Runs) (rt : RTape) : option FastState :=
  match runs_remove [1] l with
  | Some l1 =>
    if runs_zeros l1 then Some (MkFastState [] rt MJ)
    else stepML_afterZero1 l rt
  | None => stepML_afterZero1 l rt
  end.

Lemma stepML_tailRest_spec l rt :
  match stepML_tailRest l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML_tailRest.
  destruct (runs_remove [1] l) as [l1|] eqn:Hr1; [| apply stepML_afterZero1_spec].
  destruct (runs_zeros l1) eqn:Hz; [| apply stepML_afterZero1_spec].
  cbn [fs_denote fs_L fs_R fs_mode runs_denote].
  rewrite (runs_remove_spec _ _ _ Hr1), (runs_zeros_spec _ Hz).
  apply rule_zeroL_1.
Qed.

Definition stepML_tail (l : Runs) (rt : RTape) : option FastState :=
  if runs_zeros l then
    match takeDRTape rt with
    | Some (a, rt1) =>
      match takeDRTape rt1 with
      | Some (b, rt2) =>
        let l' := runs_push (SW_raw [1; 0]) (b + 2)%N (runs_push (SW_raw [1; 1]) a []) in
        Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 0]) 1 (r_raw rt2)) (d_front rt2) (d_back rt2) (r_tail rt2)) MR)
      | None =>
        match takeBitsRTape [1; 0] rt1 with
        | Some rt2 =>
          let l' :=
            if N.eqb a 0 then [(SW_S 0, 1%N)]
            else runs_push (SW_raw [1; 0]) 2 (runs_push (SW_raw [1; 1]) a []) in
          Some (MkFastState l' (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt2)) (d_front rt2) (d_back rt2) (r_tail rt2)) MR)
        | None => stepML_tailRest l rt
        end
      end
    | None => stepML_tailRest l rt
    end
  else stepML_tailRest l rt.

Lemma stepML_tail_spec l rt :
  match stepML_tail l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML_tail.
  destruct (runs_zeros l) eqn:Hz; [| apply stepML_tailRest_spec].
  destruct (takeDRTape rt) as [[a rt1]|] eqn:Htd1; [| apply stepML_tailRest_spec].
  destruct (takeDRTape rt1) as [[b rt2]|] eqn:Htd2.
  - cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_zeros_spec _ Hz), (takeDRTape_spec _ _ _ Htd1), (takeDRTape_spec _ _ _ Htd2), !runs_push_spec.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail runs_denote sw_toList].
    rewrite push_plug. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    replace (N.to_nat (b + 2)%N) with (N.to_nat b + 2)%nat by lia.
    apply rule_zeroL_DD.
  - destruct (takeBitsRTape [1; 0] rt1) as [rt2|] eqn:Htb; [| apply stepML_tailRest_spec].
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_zeros_spec _ Hz), (takeDRTape_spec _ _ _ Htd1), (takeBitsRTape_spec _ _ _ Htb).
    unfold rt_denote; cbn [r_raw d_front d_back r_tail].
    rewrite push_plug. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. rewrite lpow_1.
    destruct (N.eqb_spec a 0) as [-> | Ha0].
    + cbn [runs_denote sw_toList].
      change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
      apply rule_zeroL_D10_0.
    + rewrite !runs_push_spec. cbn [runs_denote sw_toList].
      change (N.to_nat 2) with 2%nat.
      replace (N.to_nat a) with (1 + N.to_nat (a - 1)%N)%nat by lia.
      apply rule_zeroL_D10_S.
Qed.

Definition stepML (l : Runs) (rt : RTape) : option FastState :=
  match sweepLeftSuper false l rt with
  | Some s' => Some s'
  | None =>
    match l with
    | (SW_raw _, _) :: _ =>
      match stepML_raw l rt with
      | Some s' => Some s'
      | None => stepML_tail l rt
      end
    | _ => stepML_tail l rt
    end
  end.

Lemma stepML_spec l rt :
  match stepML l rt with
  | Some s' => fs_denote (MkFastState l rt ML) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt ML))
  end.
Proof.
  unfold stepML.
  destruct (sweepLeftSuper false l rt) as [s'|] eqn:Hsl.
  - exact (sweepLeftSuper_spec false l rt s' Hsl).
  - destruct l as [|[w k] lrest]; [apply stepML_tail_spec |].
    destruct w as [lw | | | | | |]; try apply stepML_tail_spec.
    destruct (stepML_raw ((SW_raw lw, k) :: lrest) rt) as [s'|] eqn:Hsr;
      [exact (stepML_raw_spec _ rt s' Hsr) | apply stepML_tail_spec].
Qed.

Definition take10IfRaw (l : Runs) : N * Runs :=
  match l with
  | (SW_raw _, _) :: _ => take10 l
  | _ => (0%N, l)
  end.

Lemma take10IfRaw_spec l :
  runs_denote l = [1; 0]^^(N.to_nat (fst (take10IfRaw l))) *> runs_denote (snd (take10IfRaw l)).
Proof.
  destruct l as [|[[lw | | | | | |] k] rest]; try reflexivity.
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
      let '(hd, df', db', rtail') := doCallsDUpto 16 0 (d_front rt) (d_back rt) (r_tail rt) c111 in
      if negb (N.eqb hd 0) then
        let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - hd)%N l2) in
        Some (MkFastState l' (MkRTape [] df' db' rtail') ML)
      else
        let l' := runs_push (SW_raw [1; 0]) b1 (runs_push (SW_raw [1; 1; 1]) (c111 - 1)%N l2) in
        Some (MkFastState l' rt MR)
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
  destruct (doCallsDUpto 16 0 df db rtail c111) as [[[hd df'] db'] rtail'] eqn:Hdc.
  destruct (N.eqb_spec hd 0) as [-> | Hhd0]; cbn [negb]; [exact Hturn |].
  destruct (doCallsDUpto_0_spec _ _ _ _ _ _ _ _ _ Hdc) as [Hle Hcalls].
  assert (Hpos : (0 < N.to_nat hd)%nat) by lia.
  cbn [fs_denote fs_L fs_R fs_mode].
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
  rewrite H10, H111, !runs_push_spec. cbn [sw_toList].
  replace (N.to_nat (b + 1)%N) with (1 + N.to_nat b)%nat by lia.
  replace (N.to_nat c111) with (N.to_nat hd + N.to_nat (c111 - hd)%N)%nat at 1 by lia.
  rewrite <- (lpow_Str_add [1; 1; 1]).
  exact (loopJ' Hpos Hcalls _ (N.to_nat b)).
Qed.

Definition stepMJ_afterZero (l : Runs) (rt : RTape) : option FastState :=
  match takeS l with
  | Some (sn, l') =>
    let rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end in
    Some (MkFastState l' (MkRTape [] (pushD (sn + 1)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) ML)
  | None => stepMJ_turn l rt
  end.

Lemma stepMJ_afterZero_spec l rt :
  match stepMJ_afterZero l rt with
  | Some s' => fs_denote (MkFastState l rt MJ) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MJ))
  end.
Proof.
  unfold stepMJ_afterZero.
  destruct (takeS l) as [[sn l']|] eqn:Hts; [| apply stepMJ_turn_spec].
  set (rt1 := match r_raw rt with [] => rt | _ :: _ => flushAllToTail rt end).
  pose proof (flush_if_raw_denote rt) as Hrt1; fold rt1 in Hrt1.
  cbn [fs_denote fs_L fs_R fs_mode].
  rewrite (takeS_spec _ _ _ Hts), Hrt1.
  unfold rt_denote; cbn [r_raw d_front d_back r_tail plug].
  rewrite denD_pushD. change (N.to_nat 1) with 1%nat. rewrite lpow_1.
  replace (N.to_nat (sn + 1)%N) with (1 + N.to_nat sn)%nat by lia.
  apply rule_leftJ.
Qed.

Definition stepMJ (l : Runs) (rt : RTape) : option FastState :=
  match sweepLeftSuper true l rt with
  | Some s' => Some s'
  | None =>
    if runs_zeros l then
      match takeDRTape rt with
      | Some (n, rt1) =>
        let l' := runs_push (SW_raw [1; 0]) 2 (runs_push (SW_raw [1; 1]) (n + 1)%N []) in
        Some (MkFastState l' (MkRTape (runs_push (SW_raw [1]) 1 (r_raw rt1)) (d_front rt1) (d_back rt1) (r_tail rt1)) MR)
      | None => stepMJ_afterZero l rt
      end
    else stepMJ_afterZero l rt
  end.

Lemma stepMJ_spec l rt :
  match stepMJ l rt with
  | Some s' => fs_denote (MkFastState l rt MJ) -->* fs_denote s'
  | None => halts src_tm (fs_denote (MkFastState l rt MJ))
  end.
Proof.
  unfold stepMJ.
  destruct (sweepLeftSuper true l rt) as [s'|] eqn:Hsl.
  - exact (sweepLeftSuper_spec true l rt s' Hsl).
  - destruct (runs_zeros l) eqn:Hz; [| apply stepMJ_afterZero_spec].
    destruct (takeDRTape rt) as [[n rt1]|] eqn:Htd; [| apply stepMJ_afterZero_spec].
    cbn [fs_denote fs_L fs_R fs_mode].
    rewrite (runs_zeros_spec _ Hz), (takeDRTape_spec _ _ _ Htd), !runs_push_spec.
    unfold rt_denote; cbn [r_raw d_front d_back r_tail runs_denote sw_toList].
    rewrite push_plug. cbn [sw_toList].
    change (N.to_nat 1) with 1%nat. change (N.to_nat 2) with 2%nat.
    rewrite lpow_1.
    replace (N.to_nat (n + 1)%N) with (1 + N.to_nat n)%nat by lia.
    apply rule_zeroL_J.
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
  revert s. induction k as [|k IH]; intros s; cbn [run_pow].
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

Lemma run_ok : is_none (run_pow 19 initFastB) = true.
Proof. vm_check_eq. Qed.

Lemma src_halt : halts src_tm (B;; tape0).
Proof.
  rewrite <- initFastB_denote.
  pose proof (run_pow_spec 19 initFastB) as H.
  pose proof run_ok as Hok.
  destruct (run_pow 19 initFastB); [discriminate | exact H].
Qed.

End H155900.

Theorem halt : halts tm c0.
Proof. exact (H155900.halts_iso H155900.src_halt). Qed.

Print Assumptions halt.
