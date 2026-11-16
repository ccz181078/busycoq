From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import ZifyNat Lia ZArith String List.

(* Native SOBC-TM14.  No state permutation is used. *)
Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1RC0RC_1LD1RF_---1LE_1RF0LF_1RA0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* The native C1 entry and E1 exit surround this F-to-E call.
   Thus the finite words below omit G's leading bit 1. *)
Notation hf := [((F,[]),(E,[]))].
Notation z4 := [0;0;0;0].
Notation a4 := [1;0;0;0].
Notation b4 := [1;0;0;1].
Notation c4 := [0;1;1;0].
Notation d4 := [1;1;1;0].
Notation e4 := [0;0;1;0].

Fixpoint ucount (k:nat) : nat :=
  match k with O => 1 | S k => 4 * ucount k + 1 end.
Definition vcount (k:nat) : nat := 2 * ucount k - 1.

Definition Ufinite (k:nat) : Prop :=
  segRLs tm (hf^^ucount k) []
    ([0;0;0] ++ z4^^k ++ [0])
    ([0;0;1] ++ a4^^k ++ [1]).
Definition Vfinite (k:nat) : Prop :=
  segRLs tm (hf^^vcount k) []
    ([0;0;0] ++ c4 ++ z4^^k)
    ([0;0;1] ++ d4 ++ e4^^k).

Lemma Ufinite_0 : Ufinite 0.
Proof.
  unfold Ufinite. apply BoundedConfig.segRLs_c_spec with (T:=1000).
  reflexivity.
Qed.

Lemma Vfinite_0 : Vfinite 0.
Proof.
  unfold Vfinite, vcount. apply BoundedConfig.segRLs_c_spec with (T:=1000).
  reflexivity.
Qed.

Lemma Ufinite_1 : Ufinite 1.
Proof.
  unfold Ufinite. apply BoundedConfig.segRLs_c_spec with (T:=1000).
  reflexivity.
Qed.

(* One-call bridges.  The right exterior r remains arbitrary. *)
Lemma bridge_L1 :
  segRLs tm hf [] ([0;0;1] ++ [1;1;1;1]) ([0;0;0] ++ z4).
Proof.
  apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity.
Qed.

Lemma bridge_L2 m :
  segRLs tm hf [] ([0;0;1] ++ a4^^(2+m) ++ [0])
    ([0;0;0] ++ c4 ++ z4^^m ++ [0;0;0;1;1]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma bridge_L3_0 m :
  segRLs tm hf [] ([0;0;1] ++ a4^^(1+m) ++ [1;1;1;0])
    ([0;0;0] ++ c4 ++ z4^^m ++ [0;0;1;0]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma bridge_L3_1 m :
  segRLs tm hf [] ([0;0;1] ++ a4^^(1+m) ++ [1;1;1;1])
    ([0;0;0] ++ c4 ++ z4^^m ++ [0;0;1;1]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma bridge_L4_0 m :
  segRLs tm hf [] ([0;0;1] ++ d4 ++ e4^^m ++ [0;0;0;0])
    ([0;0;0] ++ z4^^(1+m) ++ [0;1;1;0]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma bridge_L4_1 m :
  segRLs tm hf [] ([0;0;1] ++ d4 ++ e4^^m ++ [0;0;0;1])
    ([0;0;0] ++ z4^^(1+m) ++ [0;1;1;1]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma bridge_L4_3 m :
  segRLs tm hf [] ([0;0;1] ++ d4 ++ e4^^m ++ [0;0;1;1])
    ([0;0;0] ++ z4^^(1+m) ++ [0;0;0;0]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc.
  Timeout 3 es' m & l r.
Qed.

Lemma word_pow_last (w:list Sym) k : w^^(S k) = w^^k ++ w.
Proof.
  replace (S k) with (k+1) by lia.
  rewrite lpow_add. cbn [lpow]. rewrite app_nil_r. reflexivity.
Qed.

Lemma finite_suffix {n w1 w2} s :
  segRLs tm (hf^^n) [] w1 w2 ->
  segRLs tm (hf^^n) [] (w1++s) (w2++s).
Proof.
  intro H. eapply segRLs_concat; [exact H|constructor].
Qed.

Lemma finite_trans {m n w1 w2 w3} :
  segRLs tm (hf^^m) [] w1 w2 ->
  segRLs tm (hf^^n) [] w2 w3 ->
  segRLs tm (hf^^(m+n)) [] w1 w3.
Proof.
  intros H1 H2. rewrite lpow_add.
  exact (segRLs_trans H1 H2).
Qed.

Lemma ucount_positive k : 1 <= ucount k.
Proof.
  destruct k; cbn [ucount].
  - reflexivity.
  - apply Nat.le_add_l.
Qed.

Ltac norm_word_hyp H :=
  repeat rewrite Nat.add_succ_r in H;
  repeat rewrite Nat.add_0_r in H;
  repeat rewrite word_pow_last in H;
  repeat rewrite <-app_assoc in H;
  cbn [app] in H.

Ltac norm_word_goal :=
  repeat rewrite Nat.add_succ_r;
  repeat rewrite Nat.add_0_r;
  repeat rewrite word_pow_last;
  repeat rewrite <-app_assoc;
  cbn [app].

Lemma Vfinite_step k : Ufinite (S k) -> Vfinite k -> Vfinite (S k).
Proof.
  intros HU HV. unfold Ufinite in HU. unfold Vfinite in HV |- *.
  pose proof (finite_suffix z4 HV) as H1.
  pose proof (bridge_L4_0 k) as H2.
  pose proof (finite_suffix [1;1;0] HU) as H3.
  pose proof (bridge_L3_0 k) as H4.
  pose proof (finite_suffix e4 HV) as H5.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4. norm_word_hyp H5. norm_word_goal.
  pose proof (finite_trans (n:=1) H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans (n:=1) H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  replace (vcount (S k)) with
    ((((vcount k+1)+ucount (S k))+1)+vcount k).
  - exact H12345.
  - pose proof (ucount_positive k). unfold vcount. cbn [ucount]. lia.
Qed.

Lemma Ufinite_step k : Ufinite (S k) -> Vfinite k -> Ufinite (S (S k)).
Proof.
  intros HU HV. unfold Ufinite in HU |- *. unfold Vfinite in HV.
  pose proof (finite_suffix z4 HU) as H1.
  pose proof (bridge_L2 k) as H2.
  replace (2+k) with (S (S k)) in H2 by lia.
  pose proof (finite_suffix [0;0;0;1;1] HV) as H3.
  pose proof (finite_suffix (n:=1) [1] (bridge_L4_1 k)) as H4.
  pose proof (finite_suffix [1;1;1;1] HU) as H5.
  pose proof (finite_suffix (n:=1) [1] (bridge_L3_1 k)) as H6.
  pose proof (finite_suffix [0;0;1;1;1] HV) as H7.
  pose proof (finite_suffix (n:=1) [1] (bridge_L4_3 k)) as H8.
  pose proof (finite_suffix [0;0;0;1] HU) as H9.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4. norm_word_hyp H5. norm_word_hyp H6.
  norm_word_hyp H7. norm_word_hyp H8. norm_word_hyp H9.
  norm_word_goal.
  pose proof (finite_trans (n:=1) H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  pose proof (finite_trans H12345 H6) as H123456.
  pose proof (finite_trans H123456 H7) as H1234567.
  pose proof (finite_trans H1234567 H8) as H12345678.
  pose proof (finite_trans H12345678 H9) as H123456789.
  replace (ucount (S (S k))) with
    ((((((((ucount (S k)+1)+vcount k)+1)+ucount (S k))+1)
       +vcount k)+1)+ucount (S k)).
  - exact H123456789.
  - pose proof (ucount_positive k). unfold vcount. cbn [ucount]. lia.
Qed.

(* Joint induction: each step uses only U(k+1) and V(k). *)
Lemma UVfinite k : Ufinite (S k) /\ Vfinite k.
Proof.
  induction k as [|k [HU HV]].
  - split; [exact Ufinite_1|exact Vfinite_0].
  - split; [apply Ufinite_step|apply Vfinite_step]; assumption.
Qed.

Theorem Ufinite_all k : Ufinite k.
Proof.
  destruct k as [|k].
  - exact Ufinite_0.
  - exact (proj1 (UVfinite k)).
Qed.

Theorem Vfinite_all k : Vfinite k.
Proof. exact (proj2 (UVfinite k)). Qed.

Lemma ucount_power k : 3 * ucount k + 1 = 4^(S k).
Proof.
  induction k as [|k IH].
  - reflexivity.
  - change (3 * (4 * ucount k + 1) + 1 = 4 * 4^(S k)).
    rewrite <-IH. lia.
Qed.

(* Certified prefixes of U(k+2), exposing its middle and last U(k+1)
   subpaths.  These are reachability proofs, not subtraction of endpoints. *)
Theorem U_prefix_M k :
  segRLs tm (hf^^(2 * 4^(S k))) []
    ([0;0;0] ++ z4^^(S (S k)) ++ [0])
    ([0;0;0] ++ z4^^(S k) ++ [0;1;1;1;1]).
Proof.
  pose proof (Ufinite_all (S k)) as HU. unfold Ufinite in HU.
  pose proof (Vfinite_all k) as HV. unfold Vfinite in HV.
  pose proof (finite_suffix z4 HU) as H1.
  pose proof (bridge_L2 k) as H2.
  replace (2+k) with (S (S k)) in H2 by lia.
  pose proof (finite_suffix [0;0;0;1;1] HV) as H3.
  pose proof (finite_suffix (n:=1) [1] (bridge_L4_1 k)) as H4.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4. norm_word_goal.
  pose proof (finite_trans (n:=1) H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  replace (2 * 4^(S k)) with (((ucount (S k)+1)+vcount k)+1).
  - exact H1234.
  - pose proof (ucount_positive k). pose proof (ucount_power k).
    unfold vcount. cbn [ucount]. lia.
Qed.

Theorem U_prefix_L k :
  segRLs tm (hf^^(4^(S (S k)))) []
    ([0;0;0] ++ z4^^(S (S k)) ++ [0])
    ([0;0;0] ++ z4^^(S k) ++ [0;0;0;0;1]).
Proof.
  pose proof (Ufinite_all (S k)) as HU. unfold Ufinite in HU.
  pose proof (Vfinite_all k) as HV. unfold Vfinite in HV.
  pose proof (U_prefix_M k) as H1.
  pose proof (finite_suffix [1;1;1;1] HU) as H2.
  pose proof (finite_suffix (n:=1) [1] (bridge_L3_1 k)) as H3.
  pose proof (finite_suffix [0;0;1;1;1] HV) as H4.
  pose proof (finite_suffix (n:=1) [1] (bridge_L4_3 k)) as H5.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4. norm_word_hyp H5. norm_word_goal.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  replace (4^(S (S k))) with
    ((((2 * 4^(S k)+ucount (S k))+1)+vcount k)+1).
  - exact H12345.
  - pose proof (ucount_positive k). pose proof (ucount_power k).
    pose proof (ucount_power (S k)).
    unfold vcount. cbn [ucount] in *. lia.
Qed.

Theorem U_near_end k :
  segRLs tm (hf^^(ucount (S (S k))-5)) []
    ([0;0;0] ++ z4^^(S (S k)) ++ [0])
    ([0;0;0] ++ z4^^2 ++ a4^^k ++ [1]).
Proof.
  induction k as [|k IH].
  - pose proof (U_prefix_L 0) as H.
    cbn [ucount Nat.mul Nat.add Nat.sub Nat.pow lpow app] in H |- *.
    exact H.
  - pose proof (U_prefix_L (S k)) as H1.
    pose proof (finite_suffix [0;0;0;1] IH) as H2.
    norm_word_hyp H1. norm_word_hyp H2. norm_word_goal.
    pose proof (finite_trans H1 H2) as H12.
    replace (ucount (S (S (S k)))-5) with
      (4^(S (S (S k)))+(ucount (S (S k))-5)).
    + exact H12.
    + pose proof (ucount_positive k).
      pose proof (ucount_power (S (S k))).
      cbn [ucount] in *. lia.
Qed.

Lemma pow4_next k : 4^(S k) = 4 * 4^k.
Proof. reflexivity. Qed.

Lemma near_end_count k : ucount (S (S k))-5 = 16 * ucount k.
Proof. cbn [ucount]. lia. Qed.

Notation seek_tail := [0;0;0;1;0;0;0;1;1;1;1;1].

Lemma seek_top3 k :
  segRLs tm (hf^^(13 * 4^(k+7))) []
    ([0;0;0] ++ z4^^(k+9) ++ [0])
    (([0;0;0] ++ z4^^(k+6) ++ [0]) ++ seek_tail).
Proof.
  pose proof (U_prefix_M (k+7)) as H1.
  pose proof (finite_suffix [1;1;1;1] (U_prefix_L (k+6))) as H2.
  pose proof (finite_suffix [0;0;0;1;1;1;1;1] (U_prefix_L (k+5))) as H3.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  assert (HC : (2 * 4^(S (k+7)) + 4^(S (S (k+6))))
                   + 4^(S (S (k+5))) = 13 * 4^(k+7)).
  { repeat rewrite Nat.add_succ_r. repeat rewrite Nat.add_0_r.
    repeat rewrite pow4_next. nia. }
  rewrite <-HC. norm_word_goal. exact H123.
Qed.

Lemma seek_lower a :
  segRLs tm (hf^^(4^(a+4) + 16 * ucount a)) []
    ([0;0;0] ++ z4^^(a+4) ++ [0])
    ([0;0;0] ++ z4^^2 ++ a4^^(S a) ++ z4 ++ [1]).
Proof.
  pose proof (U_prefix_L (a+2)) as H1.
  pose proof (finite_suffix [0;0;0;0;0;0;0;1] (U_near_end a)) as H2.
  norm_word_hyp H1. norm_word_hyp H2.
  pose proof (finite_trans H1 H2) as H12.
  assert (HC : 4^(S (S (a+2))) + (ucount (S (S a))-5)
                    = 4^(a+4) + 16 * ucount a).
  { rewrite near_end_count. f_equal. f_equal. lia. }
  rewrite <-HC. norm_word_goal. exact H12.
Qed.

Lemma z4_zero_shift k : z4^^k ++ [0] = [0] ++ z4^^k.
Proof.
  induction k as [|k IH]; cbn [lpow app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma z4_zero3_shift k : z4^^k ++ [0;0;0] = [0;0;0] ++ z4^^k.
Proof.
  induction k as [|k IH]; cbn [lpow app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma z4_recut p q :
  z4^^(p+q) ++ [0] = (z4^^p ++ [0]) ++ z4^^q.
Proof.
  rewrite lpow_add. repeat rewrite <-app_assoc.
  rewrite z4_zero_shift. reflexivity.
Qed.

Lemma seek_tail_join q :
  [1] ++ z4^^q ++ seek_tail = a4 ++ z4^^q ++ a4 ++ [1;1;1;1;1].
Proof.
  change ([1] ++ z4^^q ++ ([0;0;0] ++ (a4 ++ [1;1;1;1;1]))
          = a4 ++ z4^^q ++ a4 ++ [1;1;1;1;1]).
  rewrite (app_assoc (z4^^q) [0;0;0]).
  rewrite z4_zero3_shift. repeat rewrite <-app_assoc. reflexivity.
Qed.

(* The universal reset SEEK, with old parameters x=1+a and y=1+b.
   This shifted interface uses only natural-number addition and powers;
   no execution scheduler or fitted count guard is an assumption. *)
Theorem reset_seek_finite a b :
  segRLs tm (hf^^(16 * ucount a + 4^(a+4) + 13 * 4^(a+b+7))) []
    ([0;0;0] ++ z4^^(a+b+9) ++ [0])
    ([0;0;0] ++ z4^^2 ++ a4^^(1+a) ++ z4 ++ a4 ++
      z4^^(2+b) ++ a4 ++ [1;1;1;1;1]).
Proof.
  pose proof (seek_top3 (a+b)) as H1.
  pose proof (finite_suffix (z4^^(b+2) ++ seek_tail) (seek_lower a)) as H2.
  assert (HE : (([0;0;0] ++ z4^^(a+b+6) ++ [0]) ++ seek_tail) =
    (([0;0;0] ++ z4^^(a+4) ++ [0]) ++ (z4^^(b+2) ++ seek_tail))).
  { replace (a+b+6) with ((a+4)+(b+2)) by lia.
    rewrite z4_recut. repeat rewrite <-app_assoc. reflexivity. }
  rewrite HE in H1.
  pose proof (finite_trans H1 H2) as H12.
  assert (HE2 :
    ([0;0;0] ++ z4^^2 ++ a4^^(S a) ++ z4 ++ [1]) ++
        (z4^^(b+2) ++ seek_tail) =
    [0;0;0] ++ z4^^2 ++ a4^^(1+a) ++ z4 ++ a4 ++
        z4^^(2+b) ++ a4 ++ [1;1;1;1;1]).
  { replace (2+b) with (b+2) by lia.
    repeat rewrite <-app_assoc. rewrite seek_tail_join.
    reflexivity. }
  replace (16 * ucount a + 4^(a+4) + 13 * 4^(a+b+7)) with
    (13 * 4^(a+b+7) + (4^(a+4) + 16 * ucount a)) by lia.
  rewrite <-HE2.
  exact H12.
Qed.

(* H keeps the leading bit of its lower callee inside this finite word.
   Exactly one outgoing hf call is retained by H_cycle. *)
Definition hword a b :=
  [0;0;1] ++ d4 ++ e4^^a ++ c4^^b ++ [0;1;1;1;1].

Lemma H_OA a b :
  segRLs tm hf hf (hword a (1+b))
    ([0;0;0] ++ z4^^(1+a) ++ [0;0;0;1] ++ b4^^b ++ a4 ++ [0]).
Proof.
  unfold hword.
  eapply (segRLs_S'
    (w2 := [1;1;1;1;1] ++ [1;1;0;1]^^(1+b) ++
        [1;1;1;1]^^(1+a) ++ [1;1;1])
    (w3 := [0;0;0] ++ z4^^(1+a) ++ [0;0;0;1] ++ b4^^b ++ a4 ++ [0])).
  - unfold segRR. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a b & l r.
  - unfold segLL. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a b & l r.
  - constructor.
Qed.

Lemma H_OB a b :
  segRLs tm hf []
    ([0;0;1] ++ a4^^a ++ b4^^(1+b) ++ a4 ++ [0])
    ([0;0;0] ++ c4 ++ z4^^a ++ c4^^b ++ [0;1;1;1;1]).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc. Timeout 3 es' a b & l r.
Qed.

Lemma run_trans {m n ls1 ls2 w1 w2 w3} :
  segRLs tm (hf^^m) ls1 w1 w2 ->
  segRLs tm (hf^^n) ls2 w2 w3 ->
  segRLs tm (hf^^(m+n)) (ls1++ls2) w1 w3.
Proof.
  intros H1 H2. rewrite lpow_add. exact (segRLs_trans H1 H2).
Qed.

Theorem H_cycle a b :
  segRLs tm (hf^^(4^(a+2))) hf (hword a (1+b)) (hword (1+a) b).
Proof.
  pose proof (H_OA a b) as H1.
  pose proof (Ufinite_all (S a)) as HU. unfold Ufinite in HU.
  pose proof (finite_suffix ([0;0;1] ++ b4^^b ++ a4 ++ [0]) HU) as H2.
  pose proof (H_OB (1+a) b) as H3.
  replace (b4^^(1+b)) with (b4 ++ b4^^b) in H3 by reflexivity.
  pose proof (Vfinite_all (S a)) as HV. unfold Vfinite in HV.
  pose proof (finite_suffix (c4^^b ++ [0;1;1;1;1]) HV) as H4.
  unfold hword in H1 |- *.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4.
  pose proof (run_trans (m:=1) H1 H2) as H12.
  pose proof (run_trans (n:=1) H12 H3) as H123.
  pose proof (run_trans H123 H4) as H1234.
  assert (HC : ((1+ucount (S a))+1)+vcount (S a) = 4^(a+2)).
  { pose proof (ucount_positive (S a)). pose proof (ucount_power (S a)).
    unfold vcount. replace (a+2) with (S (S a)) by lia. lia. }
  rewrite <-HC. norm_word_hyp H1234. norm_word_goal. exact H1234.
Qed.

Definition qcount (j:nat) : nat := match j with O => 0 | S k => ucount k end.

Lemma qcount_S j : qcount (S j) = 4 * qcount j + 1.
Proof. destruct j; reflexivity. Qed.

Theorem H_lift_finite a b j :
  segRLs tm (hf^^(4^(a+2) * qcount j)) (hf^^j)
    (hword a (j+b)) (hword (a+j) b).
Proof.
  revert a. induction j as [|j IH]; intro a.
  - cbn [qcount]. rewrite Nat.mul_0_r, Nat.add_0_r. constructor.
  - pose proof (H_cycle a (j+b)) as H1.
    pose proof (IH (S a)) as H2.
    pose proof (run_trans H1 H2) as H12.
    assert (HC : 4^(a+2) + 4^(S a+2) * qcount j =
                   4^(a+2) * qcount (S j)).
    { rewrite qcount_S.
      replace (S a+2) with (S (a+2)) by lia.
      rewrite pow4_next. nia. }
    rewrite <-HC, (Nat.add_succ_r a j).
    exact H12.
Qed.

Theorem H_lift a b j (r r':side) :
  sideRLs tm (hf^^j) r r' ->
  sideRLs tm (hf^^(4^(a+2) * qcount j))
    (hword a (j+b) *> r) (hword (a+j) b *> r').
Proof.
  intro H. eapply segRLs_sideRLs_concat; [apply H_lift_finite|exact H].
Qed.

Theorem reset_seek a b (r:side) :
  sideRLs tm (hf^^(16 * ucount a + 4^(a+4) + 13 * 4^(a+b+7)))
    (([0;0;0] ++ z4^^(a+b+9) ++ [0]) *> r)
    (([0;0;0] ++ z4^^2 ++ a4^^(1+a) ++ z4 ++ a4 ++
      z4^^(2+b) ++ a4 ++ [1;1;1;1;1]) *> r).
Proof.
  eapply segRLs_sideRLs_concat; [apply reset_seek_finite|constructor].
Qed.

(* Complete normal caller.  Only this caller requires the infinite
   blank LEFT ray; every right side below remains arbitrary. *)
Definition Ncfg n (r:side) :=
  0inf <{{F}} (z4 ++ c4^^n ++ [0;1;1;1;1]) *> r.

Definition Nleft n :=
  [1;1;1;1;1] *> [1;1;0;1]^^(1+n) *> [1;1;0;0] *> 0inf.

Lemma N_out n (r:side) : Ncfg n r -->* Nleft n {{F}}> r.
Proof.
  unfold Ncfg, Nleft. repeat rewrite Str_app_assoc.
  Timeout 3 es' n & r.
Qed.

Definition Nturn n := [1;1;1;1] *> [0;1;1;1]^^(2+n) *> 0inf.

Lemma N_return_1 n (r:side) :
  Nleft n <{{E}} r -->* Nturn n {{C}}> 0 >> r.
Proof.
  unfold Nleft, Nturn. repeat rewrite Str_app_assoc.
  Timeout 3 es' n & r.
Qed.

Lemma N_return_segment n (l r:side) :
  l <* [0;1;1;1]^^(2+n) <* [1;1;1;1] {{C}}> 0 >> r -->*
  l <{{F}} (z4 ++ c4^^(1+n) ++ [0;1;1;1;1]) *> r.
Proof.
  repeat rewrite Str_app_assoc. Timeout 3 es' n & l r.
Qed.

Lemma N_return_2 n (r:side) :
  Nturn n {{C}}> 0 >> r -->* Ncfg (1+n) r.
Proof.
  exact (N_return_segment n 0inf r).
Qed.

Lemma N_return n (r:side) : Nleft n <{{E}} r -->* Ncfg (1+n) r.
Proof. eapply evstep_trans; [apply N_return_1|apply N_return_2]. Qed.

Theorem N_step n (r r':side) :
  sideRL tm (F,[]) (E,[]) r r' -> Ncfg n r -->+ Ncfg (1+n) r'.
Proof.
  intro H. eapply evstep_progress_trans; [apply N_out|].
  eapply progress_evstep_trans; [|apply N_return].
  exact (H (Nleft n)).
Qed.

Theorem N_run m n (r r':side) :
  sideRLs tm (hf^^m) r r' -> Ncfg n r -->* Ncfg (n+m) r'.
Proof.
  revert n r r'. induction m as [|m IH]; intros n r r' H.
  - cbn [lpow] in H. inversion H; subst.
    rewrite Nat.add_0_r. constructor.
  - cbn [lpow app] in H.
    inversion H as [|h1 h2 r0 r1 r2 ls Hcall Hcalls]; subst.
    replace (n+S m) with ((1+n)+m) by lia.
    eapply evstep_trans.
    + apply progress_evstep. apply N_step. exact Hcall.
    + apply IH. exact Hcalls.
Qed.

Theorem N_H_lift n a b j (r r':side) :
  sideRLs tm (hf^^j) r r' ->
  Ncfg n (hword a (j+b) *> r) -->*
  Ncfg (n + 4^(a+2)*qcount j) (hword (a+j) b *> r').
Proof. intro H. apply N_run, H_lift. exact H. Qed.

Lemma H_empty_F a :
  segRLs tm hf hf (hword a 0) ([0;0;0] ++ z4^^(2+a) ++ [0]).
Proof.
  unfold hword.
  eapply (segRLs_S'
    (w2 := [1] ++ [1;1;1;1]^^(2+a) ++ [1;1;1])
    (w3 := [0;0;0] ++ z4^^(2+a) ++ [0])).
  - unfold segRR. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - unfold segLL. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - constructor.
Qed.

Theorem H_empty_batch a :
  segRLs tm (hf^^(1+ucount (a+2))) hf (hword a 0)
    ([0;0;1] ++ a4^^(a+2) ++ [1]).
Proof.
  pose proof (H_empty_F a) as H1.
  replace (2+a) with (a+2) in H1 by lia.
  pose proof (Ufinite_all (a+2)) as H2. unfold Ufinite in H2.
  exact (run_trans (m:=1) H1 H2).
Qed.

(* Native callee pairs are kept literal: P calls C, J calls A.
   No unproved closure of either callee is asserted. *)
Lemma P_F k :
  segRLs tm hf [((C,[]),(F,[]))]
    ([0;0;1] ++ a4^^(1+k)) ([0;0;0] ++ c4 ++ z4^^k).
Proof.
  eapply (segRLs_S'
    (w2 := [1;1;1;1]^^(1+k) ++ [0;1;1])
    (w3 := [0;0;0] ++ c4 ++ z4^^k)).
  - unfold segRR. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' k & l r.
  - unfold segLL. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' k & l r.
  - constructor.
Qed.

Lemma J_F a :
  segRLs tm hf [((A,[]),(F,[]))]
    ([0;0;1] ++ d4 ++ e4^^a) ([0;0;0] ++ z4^^(1+a)).
Proof.
  eapply (segRLs_S'
    (w2 := [1;1;1;1]^^(1+a) ++ [1;1;1])
    (w3 := [0;0;0] ++ z4^^(1+a))).
  - unfold segRR. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - unfold segLL. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - constructor.
Qed.

(* Saturated carry: the guard is encoded by the index 1+k.  The proof
   uses the actual suffix of the U path; no determinism cancellation or
   unproved first-return function is needed. *)
Theorem saturated_bit k :
  segRLs tm (hf^^(4^(1+k))) []
    ([0;0;1] ++ a4^^(1+k) ++ [0])
    ([0;0;1] ++ a4^^(1+k) ++ [1]).
Proof.
  destruct k as [|k].
  - apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity.
  - pose proof (Ufinite_all (S k)) as HU. unfold Ufinite in HU.
    pose proof (Vfinite_all k) as HV. unfold Vfinite in HV.
    pose proof (bridge_L2 k) as H1.
    replace (2+k) with (S (S k)) in H1 by lia.
    pose proof (finite_suffix [0;0;0;1;1] HV) as H2.
    pose proof (finite_suffix (n:=1) [1] (bridge_L4_1 k)) as H3.
    pose proof (finite_suffix [1;1;1;1] HU) as H4.
    pose proof (finite_suffix (n:=1) [1] (bridge_L3_1 k)) as H5.
    pose proof (finite_suffix [0;0;1;1;1] HV) as H6.
    pose proof (finite_suffix (n:=1) [1] (bridge_L4_3 k)) as H7.
    pose proof (finite_suffix [0;0;0;1] HU) as H8.
    norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
    norm_word_hyp H4. norm_word_hyp H5. norm_word_hyp H6.
    norm_word_hyp H7. norm_word_hyp H8.
    pose proof (finite_trans (m:=1) H1 H2) as H12.
    pose proof (finite_trans H12 H3) as H123.
    pose proof (finite_trans H123 H4) as H1234.
    pose proof (finite_trans H1234 H5) as H12345.
    pose proof (finite_trans H12345 H6) as H123456.
    pose proof (finite_trans H123456 H7) as H1234567.
    pose proof (finite_trans H1234567 H8) as H12345678.
    assert (HC : (((((((1+vcount k)+1)+ucount (S k))+1)
                           +vcount k)+1)+ucount (S k)) = 4^(1+S k)).
    { pose proof (ucount_positive k). pose proof (ucount_power (S k)).
      replace (1+S k) with (S (S k)) by lia.
      unfold vcount. cbn [ucount] in *. lia. }
    rewrite <-HC. norm_word_hyp H12345678. norm_word_goal.
    exact H12345678.
Qed.

Theorem saturated_zeros p k :
  segRLs tm (hf^^(4^(1+k) * ucount p)) []
    ([0;0;1] ++ a4^^(1+k) ++ z4^^p ++ [0;0;0;1])
    ([0;0;1] ++ a4^^(1+k+p) ++ b4).
Proof.
  revert k. induction p as [|p IH]; intro k.
  - pose proof (finite_suffix [0;0;1] (saturated_bit k)) as H.
    cbn [ucount]. rewrite Nat.mul_1_r.
    norm_word_hyp H. norm_word_goal. exact H.
  - pose proof (finite_suffix (z4^^p ++ [0;0;0;1])
                  (finite_suffix [0;0;0] (saturated_bit k))) as H1.
    pose proof (IH (S k)) as H2.
    norm_word_hyp H1. norm_word_hyp H2.
    pose proof (finite_trans H1 H2) as H12.
    assert (HC : 4^(1+k) + 4^(1+S k) * ucount p =
                 4^(1+k) * ucount (S p)).
    { change (4^(1+k) + (4 * 4^(1+k)) * ucount p =
                4^(1+k) * (4 * ucount p + 1)). nia. }
    rewrite <-HC.
    replace (1+k+S p) with (1+S k+p) by lia.
    change (segRLs tm (hf^^(4^(1+k)+4^(1+S k)*ucount p)) []
      ([0;0;1] ++ a4^^(1+k) ++ z4 ++ z4^^p ++ [0;0;0;1])
      ([0;0;1] ++ a4^^(1+S k+p) ++ b4)).
    norm_word_hyp H12. norm_word_goal. exact H12.
Qed.

(* A genuine E return is a different native pair, F-to-F.  The finite
   left prefix includes three explicit zeros; instantiation at 0inf is
   postponed until after the arbitrary-exterior scan has been proved. *)
Lemma N_E_return_segment n (l r:side) :
  l <* [1;1;0;0;0;0;0] <* [1;1;0;1]^^(1+n) <* [1;1;1;1;1]
    <{{F}} [0;0;0] *> r -->+
  l <{{F}} (z4 ++ [0;1;1;1;1] ++ [0;0;0] ++ c4^^n ++
            [0;1;1;1;1;0;0]) *> r.
Proof.
  repeat rewrite Str_app_assoc. Timeout 3 es' n & l r.
Qed.

Lemma J_E a :
  segRLs tm [((F,[]),(F,[]))] [((A,[]),(E,[]))]
    ([0;0;1] ++ d4 ++ e4^^a) ([0;0;0] ++ z4^^(1+a)).
Proof.
  eapply (segRLs_S'
    (w2 := [1;1;1;1]^^(1+a) ++ [1;1;1])
    (w3 := [0;0;0] ++ z4^^(1+a))).
  - unfold segRR. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - unfold segLL. intros l r. cbn [to_DH_config].
    repeat rewrite Str_app_assoc. Timeout 3 es' a & l r.
  - constructor.
Qed.

Lemma N_E_return n (r:side) :
  Nleft n <{{F}} [0;0;0] *> r -->+
  Ncfg 0 (([0;0;0] ++ c4^^n ++ [0;1;1;1;1;0;0]) *> r).
Proof.
  pose proof (N_E_return_segment n 0inf r) as H.
  unfold Nleft, Ncfg.
  repeat rewrite Str_app_assoc in H |- *.
  cbn [Str_app lpow] in H |- *.
  repeat rewrite <-const_unfold in H.
  repeat rewrite <-const_unfold.
  exact H.
Qed.

Theorem N_E_reset n (r r':side) :
  sideRL tm (F,[]) (F,[]) r ([0;0;0] *> r') ->
  Ncfg n r -->+
  Ncfg 0 (([0;0;0] ++ c4^^n ++ [0;1;1;1;1;0;0]) *> r').
Proof.
  intro H. eapply evstep_progress_trans; [apply N_out|].
  eapply progress_trans; [exact (H (Nleft n))|apply N_E_return].
Qed.

Lemma C_AZ k :
  segRLs tm [((C,[]),(F,[]))] []
    (a4^^(1+k) ++ z4) (z4^^k ++ [0;0;0;1] ++ a4).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc. Timeout 3 es' k & l r.
Qed.

Lemma C_BAAZ :
  segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ a4 ++ a4 ++ z4) (z4 ++ c4 ++ [0;0;0;1] ++ a4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma A_C0001 :
  segRLs tm [((A,[]),(F,[]))] []
    (c4 ++ [0;0;0;1]) [0;0;0;1;1;1;1;1].
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_B1111 :
  segRLs tm [((C,[]),(F,[]))] [] (b4 ++ [1;1;1;1]) (z4 ++ z4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma A_AZ :
  segRLs tm [((A,[]),(E,[]))] [] (a4 ++ z4) (z4 ++ [1;1;1;1]).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Theorem P_to_J k r w y :
  segRLs tm [((C,[]),(F,[]))] [] w (z4^^r ++ y) ->
  segRLs tm (hf^^(1+vcount (k+r))) []
    ([0;0;1] ++ a4^^(1+k) ++ w)
    ([0;0;1] ++ d4 ++ e4^^(k+r) ++ y).
Proof.
  intro H. pose proof (segRLs_concat (P_F k) H) as H1.
  pose proof (Vfinite_all (k+r)) as H2. unfold Vfinite in H2.
  pose proof (finite_suffix y H2) as H3.
  rewrite lpow_add in H3.
  norm_word_hyp H1. norm_word_hyp H3.
  pose proof (finite_trans (m:=1) H1 H3) as H13.
  norm_word_hyp H13. rewrite lpow_add. norm_word_goal. exact H13.
Qed.

Theorem J_to_P a s w y :
  segRLs tm [((A,[]),(F,[]))] [] w (z4^^s ++ [0] ++ y) ->
  segRLs tm (hf^^(1+ucount (1+a+s))) []
    ([0;0;1] ++ d4 ++ e4^^a ++ w)
    ([0;0;1] ++ a4^^(1+a+s) ++ [1] ++ y).
Proof.
  intro H. pose proof (segRLs_concat (J_F a) H) as H1.
  pose proof (Ufinite_all (1+a+s)) as H2. unfold Ufinite in H2.
  pose proof (finite_suffix y H2) as H3.
  rewrite lpow_add in H3.
  norm_word_hyp H1. norm_word_hyp H3.
  pose proof (finite_trans (m:=1) H1 H3) as H13.
  norm_word_hyp H13. rewrite lpow_add. norm_word_goal. exact H13.
Qed.

Theorem H_advance a p :
  segRLs tm (hf^^(4^(a+3))) []
    (hword a 0 ++ [0;0;0] ++ z4^^(2+p))
    (hword (a+2) 0 ++ [0;0;0] ++ z4^^p).
Proof.
  pose proof Ufinite_0 as HU0. unfold Ufinite in HU0.
  pose proof (finite_suffix ([0;0;0] ++ z4^^(1+p)) HU0) as Hcall.
  pose proof (segRLs_concat (H_empty_batch a) Hcall) as H1.
  pose proof (finite_suffix (n:=1) ([0;0;0] ++ z4^^p)
                (H_OB (a+2) 0)) as H2.
  pose proof (Vfinite_all (a+2)) as HV. unfold Vfinite in HV.
  pose proof (finite_suffix ([0;1;1;1;1;0;0;0] ++ z4^^p) HV) as H3.
  cbn [lpow app] in H1, H2, H3.
  repeat rewrite <-app_assoc in H1.
  repeat rewrite <-app_assoc in H2.
  repeat rewrite <-app_assoc in H3.
  cbn [app] in H1, H2, H3.
  pose proof (finite_trans (n:=1) H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  assert (HC : (1+ucount (a+2))+1+vcount (a+2) = 4^(a+3)).
  { pose proof (ucount_positive (a+2)).
    pose proof (ucount_power (a+2)).
    replace (a+3) with (S (a+2)) by lia. unfold vcount. lia. }
  rewrite <-HC. unfold hword in H123 |- *.
  cbn [lpow app] in H123 |- *.
  repeat rewrite <-app_assoc in H123.
  repeat rewrite <-app_assoc. cbn [app] in H123 |- *. exact H123.
Qed.

Lemma F_AZ_large k :
  segRLs tm hf []
    ([0;0;0] ++ a4^^(1+k) ++ z4)
    ([0;0;0] ++ z4^^k ++ [0;0;0;1] ++ a4).
Proof.
  eapply segRLs_S; [|constructor].
  unfold segRL. intros l r. cbn [to_DH_config].
  repeat rewrite Str_app_assoc. Timeout 3 es' k & l r.
Qed.

Lemma ucount_add a b :
  ucount (a+b+1) = ucount a + 4^(a+1)*ucount b.
Proof.
  pose proof (ucount_power a) as Ha.
  pose proof (ucount_power b) as Hb.
  pose proof (ucount_power (a+b+1)) as Hab.
  replace (S (a+b+1)) with (S a+S b) in Hab by lia.
  rewrite Nat.pow_add_r in Hab.
  replace (a+1) with (S a) by lia. nia.
Qed.

Theorem H_collapse a k :
  segRLs tm (hf^^(1+ucount (a+k+2))) []
    (hword a 0 ++ [0;0;0] ++ a4^^k ++ z4)
    ([0;0;1] ++ a4^^(a+k+2) ++ b4 ++ a4).
Proof.
  destruct k as [|k].
  - pose proof Ufinite_0 as HU0. unfold Ufinite in HU0.
    pose proof (finite_suffix [0;0;0] HU0) as Hcall.
    pose proof (segRLs_concat (H_empty_batch a) Hcall) as H.
    norm_word_hyp H. norm_word_goal. exact H.
  - pose proof (segRLs_concat (H_empty_batch a) (F_AZ_large k)) as H1.
    pose proof (finite_suffix a4 (saturated_zeros k (a+2))) as H2.
    norm_word_hyp H1. norm_word_hyp H2.
    pose proof (finite_trans H1 H2) as H12.
    assert (HC : (1+ucount (a+2))+4^(1+(a+2))*ucount k =
                   1+ucount (a+S k+2)).
    { pose proof (ucount_add (a+2) k) as Hc.
      replace (a+2+k+1) with (a+S k+2) in Hc by lia.
      replace (1+(a+2)) with (a+2+1) by lia. lia. }
    rewrite <-HC.
    replace (a+S k+2) with (1+(a+2)+k) by lia.
    norm_word_hyp H12. norm_word_goal. exact H12.
Qed.

Lemma segment_suffix {ls w1 w2} s :
  segRLs tm ls [] w1 w2 -> segRLs tm ls [] (w1++s) (w2++s).
Proof. intro H. eapply segRLs_concat; [exact H|constructor]. Qed.

Theorem boundary_five a b p :
  segRLs tm (hf^^(4^(a+3)+13*4^(a+b+5))) []
    (hword a 0 ++ [0;0;0] ++ z4^^2 ++ a4^^b ++ z4 ++ a4 ++ z4^^(2+p))
    ([0;0;1] ++ d4 ++ e4^^(a+b+6) ++ a4 ++ z4^^(1+p)).
Proof.
  pose proof (finite_suffix (a4^^b ++ z4 ++ a4 ++ z4^^(2+p))
                (H_advance a 0)) as H1.
  pose proof (finite_suffix (a4 ++ z4^^(2+p)) (H_collapse (a+2) b)) as H2.
  replace (a+2+b+2) with (a+b+4) in H2 by lia.
  pose proof (segment_suffix (z4^^(1+p)) C_BAAZ) as HC3.
  change (segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ a4 ++ a4 ++ z4^^(2+p))
    (z4^^1 ++ (c4 ++ [0;0;0;1] ++ a4 ++ z4^^(1+p)))) in HC3.
  pose proof (P_to_J (a+b+3) 1 _ _ HC3) as H3.
  replace (1+(a+b+3)) with (a+b+4) in H3 by lia.
  replace (a+b+3+1) with (a+b+4) in H3 by lia.
  pose proof (segment_suffix (a4 ++ z4^^(1+p)) A_C0001) as HC4.
  change (segRLs tm [((A,[]),(F,[]))] []
    (c4 ++ [0;0;0;1] ++ a4 ++ z4^^(1+p))
    (z4^^0 ++ [0] ++ ([0;0;1;1;1;1;1] ++ a4 ++ z4^^(1+p)))) in HC4.
  pose proof (J_to_P (a+b+4) 0 _ _ HC4) as H4.
  replace (1+(a+b+4)+0) with (a+b+5) in H4 by lia.
  pose proof (segment_suffix (a4 ++ z4^^(1+p)) C_B1111) as HC5.
  change (segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ [1;1;1;1] ++ a4 ++ z4^^(1+p))
    (z4^^2 ++ (a4 ++ z4^^(1+p)))) in HC5.
  pose proof (P_to_J (a+b+4) 2 _ _ HC5) as H5.
  replace (1+(a+b+4)) with (a+b+5) in H5 by lia.
  replace (a+b+4+2) with (a+b+6) in H5 by lia.
  norm_word_hyp H1. norm_word_hyp H2. norm_word_hyp H3.
  norm_word_hyp H4. norm_word_hyp H5.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  assert (HC : (((4^(a+3)+(1+ucount (a+b+4)))+(1+vcount (a+b+4)))+
                    (1+ucount (a+b+5)))+(1+vcount (a+b+6)) =
                 4^(a+3)+13*4^(a+b+5)).
  { pose proof (ucount_positive (a+b+4)).
    pose proof (ucount_power (a+b+4)).
    replace (a+b+5) with (S (a+b+4)) by lia.
    replace (a+b+6) with (S (S (a+b+4))) by lia.
    unfold vcount. cbn [ucount]. lia. }
  rewrite <-HC. norm_word_hyp H12345. norm_word_goal. exact H12345.
Qed.

Lemma finite_single_side h1 h2 w1 w2 (r:side) :
  segRLs tm [(h1,h2)] [] w1 w2 ->
  sideRL tm h1 h2 (w1 *> r) (w2 *> r).
Proof.
  intro H. assert (HS : sideRLs tm [(h1,h2)] (w1 *> r) (w2 *> r)).
  { eapply segRLs_sideRLs_concat; [exact H|constructor]. }
  inversion HS as [|ha hb rs rt ru ls Hcall Hnil]; subst.
  inversion Hnil; subst. exact Hcall.
Qed.

Theorem J_E_finite a p :
  segRLs tm [((F,[]),(F,[]))] []
    ([0;0;1] ++ d4 ++ e4^^a ++ a4 ++ z4^^(1+p))
    ([0;0;0] ++ z4^^(a+2) ++ [1;1;1;1] ++ z4^^p).
Proof.
  pose proof (segRLs_concat (J_E a) A_AZ) as H.
  pose proof (segment_suffix (z4^^p) H) as HH.
  replace (z4^^(1+p)) with (z4++z4^^p) by reflexivity.
  norm_word_hyp HH. norm_word_goal. exact HH.
Qed.

Theorem J_reset n a p (r:side) :
  Ncfg n (([0;0;1] ++ d4 ++ e4^^a ++ a4 ++ z4^^(1+p)) *> r) -->+
  Ncfg 0 (([0;0;0] ++ c4^^n ++ [0;1;1;1;1;0;0] ++
           z4^^(a+2) ++ [1;1;1;1] ++ z4^^p) *> r).
Proof.
  pose proof (finite_single_side _ _ _ _ r (J_E_finite a p)) as H.
  repeat rewrite Str_app_assoc in H.
  pose proof (N_E_reset n
    (([0;0;1] ++ d4 ++ e4^^a ++ a4 ++ z4^^(1+p)) *> r)
    ((z4^^(a+2) ++ [1;1;1;1] ++ z4^^p) *> r)) as HN.
  repeat rewrite Str_app_assoc in HN. specialize (HN H).
  repeat rewrite Str_app_assoc. exact HN.
Qed.

Theorem boundary_reset n a b p (r:side) :
  Ncfg n ((hword a 0 ++ [0;0;0] ++ z4^^2 ++ a4^^b ++
             z4 ++ a4 ++ z4^^(2+p)) *> r) -->+
  Ncfg 0 (([0;0;0] ++ c4^^(n+4^(a+3)+13*4^(a+b+5)) ++
             [0;1;1;1;1;0;0] ++ z4^^(a+b+8) ++ [1;1;1;1] ++ z4^^p) *> r).
Proof.
  assert (HF : sideRLs tm (hf^^(4^(a+3)+13*4^(a+b+5)))
    ((hword a 0 ++ [0;0;0] ++ z4^^2 ++ a4^^b ++ z4 ++ a4 ++ z4^^(2+p)) *> r)
    (([0;0;1] ++ d4 ++ e4^^(a+b+6) ++ a4 ++ z4^^(1+p)) *> r)).
  { eapply segRLs_sideRLs_concat; [apply boundary_five|constructor]. }
  eapply evstep_progress_trans; [apply N_run; exact HF|].
  replace (n+4^(a+3)+13*4^(a+b+5)) with
    (n+(4^(a+3)+13*4^(a+b+5))) by lia.
  replace (a+b+8) with (a+b+6+2) by lia.
  apply J_reset.
Qed.

Theorem reset_lift j (r r':side) :
  sideRLs tm (hf^^j) r r' ->
  Ncfg 0 (([0;0;0] ++ c4^^(1+j) ++ [0;1;1;1;1]) *> r) -->+
  Ncfg (1+16*qcount j) (hword j 0 *> r').
Proof.
  intro H. pose proof Vfinite_0 as HV. unfold Vfinite in HV.
  pose proof (finite_suffix (c4^^j ++ [0;1;1;1;1]) HV) as HV'.
  pose proof (finite_single_side _ _ _ _ r HV') as HS.
  change (sideRL tm (F,[]) (E,[])
    (([0;0;0] ++ c4^^(1+j) ++ [0;1;1;1;1]) *> r)
    (hword 0 j *> r)) in HS.
  pose proof (N_step 0 _ _ HS) as H1.
  pose proof (N_H_lift 1 0 0 j r r' H) as H2.
  rewrite Nat.add_0_r in H2.
  change (Ncfg 1 (hword 0 j *> r) -->*
    Ncfg (1+16*qcount j) (hword j 0 *> r')) in H2.
  eapply progress_evstep_trans; [exact H1|exact H2].
Qed.

Lemma reset_zero_recut k :
  [0;0] ++ z4^^(1+k) ++ [1;1;1;1] =
  [0;0;0] ++ z4^^k ++ [0;0;0;1;1;1;1].
Proof.
  induction k as [|k IH].
  - reflexivity.
  - change (z4 ++ ([0;0] ++ z4^^(1+k) ++ [1;1;1;1]) =
            z4 ++ ([0;0;0] ++ z4^^k ++ [0;0;0;1;1;1;1])).
    rewrite IH. reflexivity.
Qed.

Lemma reset_suffix_recut k p :
  [0;1;1;1;1;0;0] ++ z4^^(k+1) ++ [1;1;1;1] ++ z4^^p =
  [0;1;1;1;1] ++ [0;0;0] ++ z4^^k ++ [0;0;0;1;1;1;1] ++ z4^^p.
Proof.
  pose proof (f_equal (fun w => [0;1;1;1;1] ++ w ++ z4^^p)
                (reset_zero_recut k)) as H.
  replace (k+1) with (1+k) by lia.
  repeat rewrite <-app_assoc in H.
  cbn [app] in H |- *.
  repeat rewrite <-app_assoc in H. cbn [app] in H. exact H.
Qed.

Definition reset_budget a b := 16*ucount a + 4^(a+4) + 13*4^(a+b+7).
Definition next_a a b := 63+208*ucount a+13*4^(a+b+7).

Lemma reset_budget_next a b : reset_budget a b = 1+next_a a b.
Proof.
  unfold reset_budget, next_a.
  pose proof (ucount_power a) as H.
  replace (a+4) with (S (S (S (S a)))) by lia.
  rewrite (pow4_next (S (S (S a)))), (pow4_next (S (S a))),
          (pow4_next (S a)). lia.
Qed.

(* Keep the positive update index abstract during tape conversion.  Its
   arithmetic equation above is the interface; reducing ucount(next_a)
   would otherwise unfold a large initial successor prefix. *)
Opaque next_a.

Definition invariant a b p (r:side) :=
  Ncfg (1+16*ucount a)
    ((hword (1+a) 0 ++ [0;0;0] ++ z4^^2 ++ a4^^(1+b) ++
      z4 ++ a4 ++ z4^^(2+p)) *> r).

Theorem reset_finish a b p (r:side) :
  Ncfg 0 (([0;0;0] ++ c4^^(2+next_a a b) ++ [0;1;1;1;1;0;0] ++
             z4^^(a+b+10) ++ [1;1;1;1] ++ z4^^p) *> r) -->+
  invariant (next_a a b) a b
    ((a4 ++ [1;1;1;1] ++ b4 ++ [1;1;1] ++ z4^^p) *> r).
Proof.
  pose proof (reset_seek a b (([0;0;1;1;1;1] ++ z4^^p) *> r)) as HS.
  change (sideRLs tm (hf^^reset_budget a b)
    (([0;0;0] ++ z4^^(a+b+9) ++ [0]) *>
      (([0;0;1;1;1;1] ++ z4^^p) *> r))
    (([0;0;0] ++ z4^^2 ++ a4^^(1+a) ++ z4 ++ a4 ++
      z4^^(2+b) ++ a4 ++ [1;1;1;1;1]) *>
      (([0;0;1;1;1;1] ++ z4^^p) *> r))) in HS.
  pose proof (reset_lift (reset_budget a b) _ _ HS) as HL.
  rewrite reset_budget_next in HL.
  replace (a+b+10) with (a+b+9+1) by lia.
  rewrite reset_suffix_recut.
  unfold invariant.
  repeat rewrite Str_app_assoc in HL.
  repeat rewrite Str_app_assoc.
  cbn [Str_app qcount] in HL |- *. exact HL.
Qed.

Theorem invariant_forward a b p (r:side) :
  invariant a b p r -->+
  invariant (next_a a b) a b
    ((a4 ++ [1;1;1;1] ++ b4 ++ [1;1;1] ++ z4^^p) *> r).
Proof.
  pose proof (boundary_reset (1+16*ucount a) (1+a) (1+b) p r) as H.
  replace (1+a+3) with (a+4) in H by lia.
  replace (1+a+(1+b)+5) with (a+b+7) in H by lia.
  replace (1+a+(1+b)+8) with (a+b+10) in H by lia.
  assert (HC : 1+16*ucount a+4^(a+4)+13*4^(a+b+7) = 2+next_a a b).
  { pose proof (reset_budget_next a b). unfold reset_budget in H0. lia. }
  rewrite HC in H.
  eapply progress_trans; [exact H|apply reset_finish].
Qed.

Theorem invariant_nonhalt a b p (r:side) : ~ halts tm (invariant a b p r).
Proof.
  apply (progress_nonhalt_simple tm (nat*nat*nat*side)%type
    (fun i => let '(a,b,p,r) := i in invariant a b p r) (a,b,p,r)).
  intros [[[x y] z] t].
  exists (next_a x y,x,y,([1;0;0;0;1;1;1;1;1;0;0;1;1;1;1] ++ z4^^z) *> t).
  apply invariant_forward.
Qed.

(* Compact native entrance families.  These add no assumptions to the
   closed reset invariant above. *)
Lemma C_D :
  segRLs tm [((C,[]),(F,[]))] [] d4 e4.
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma A_C0011 :
  segRLs tm [((A,[]),(F,[]))] []
    (c4 ++ [0;0;1;1]) ([0;0;0;1] ++ a4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_BAW :
  segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ a4 ++ [1;1;1;1]) (z4 ++ c4 ++ [0;0;1;1]).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_BAA0 :
  segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ a4 ++ a4 ++ [0]) (z4 ++ c4 ++ [0;0;0;1;1]).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma A_CZ :
  segRLs tm [((A,[]),(F,[]))] [] (c4 ++ z4) ([0;0;0;1] ++ d4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_BDZ :
  segRLs tm [((C,[]),(F,[]))] [] (b4 ++ d4 ++ z4) (z4 ++ z4 ++ c4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_BD0011 :
  segRLs tm [((C,[]),(F,[]))] [] (b4 ++ d4 ++ [0;0;1;1]) (z4^^3).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma A_B111 :
  segRLs tm [((A,[]),(E,[]))] [] (b4 ++ [1;1;1]) [0;0;1;1;0;1;1].
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Lemma C_BA6W :
  segRLs tm [((C,[]),(F,[]))] []
    (b4 ++ a4^^6 ++ [1;1;1;1]) (z4 ++ c4 ++ z4^^5 ++ [0;0;1;1]).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Theorem J_zero a :
  segRLs tm (hf^^(2*4^(a+1))) []
    ([0;0;1] ++ d4 ++ e4^^a ++ z4)
    ([0;0;1] ++ d4 ++ e4^^(a+1)).
Proof.
  pose proof (bridge_L4_0 a) as H1.
  pose proof (Ufinite_all (1+a)) as HU. unfold Ufinite in HU.
  pose proof (finite_suffix [1;1;0] HU) as H2.
  pose proof (segRLs_concat (P_F a) C_D) as H3.
  pose proof (Vfinite_all a) as HV. unfold Vfinite in HV.
  pose proof (finite_suffix e4 HV) as H4.
  norm_word_hyp H1. norm_word_hyp H2.
  norm_word_hyp H3. norm_word_hyp H4.
  pose proof (finite_trans (m:=1) H1 H2) as H12.
  pose proof (finite_trans (n:=1) H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  assert (HC : ((1+ucount (1+a))+1)+vcount a = 2*4^(a+1)).
  { pose proof (ucount_positive a). pose proof (ucount_power a).
    replace (a+1) with (S a) by lia.
    unfold vcount. change (1+(4*ucount a+1)+1+(2*ucount a-1) = 2*4^(S a)). lia. }
  rewrite <-HC. norm_word_hyp H1234. norm_word_goal. exact H1234.
Qed.

Theorem J_consume a :
  segRLs tm (hf^^(4^(a+2))) []
    ([0;0;1] ++ d4 ++ e4^^a ++ c4 ++ [0;0;1;1] ++ [1;1;1;1])
    ([0;0;1] ++ d4 ++ e4^^(a+1) ++ c4 ++ [0;0;1;1]).
Proof.
  pose proof A_C0011 as HC1.
  change (segRLs tm [((A,[]),(F,[]))] [] (c4++[0;0;1;1])
    (z4^^0 ++ [0] ++ ([0;0;1] ++ a4))) in HC1.
  pose proof (finite_suffix [1;1;1;1] (J_to_P a 0 _ _ HC1)) as H1.
  pose proof C_BAW as HC2.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++a4++[1;1;1;1])
    (z4^^1 ++ (c4++[0;0;1;1]))) in HC2.
  pose proof (P_to_J a 1 _ _ HC2) as H2.
  norm_word_hyp H1. norm_word_hyp H2.
  pose proof (finite_trans H1 H2) as H12.
  assert (HC : (1+ucount (1+a+0))+(1+vcount (a+1)) = 4^(a+2)).
  { pose proof (ucount_positive (a+1)). pose proof (ucount_power (a+1)).
    replace (1+a+0) with (a+1) by lia.
    replace (a+2) with (S (a+1)) by lia. unfold vcount. lia. }
  rewrite <-HC. norm_word_hyp H12. norm_word_goal. exact H12.
Qed.

Theorem J_consume_many s a :
  segRLs tm (hf^^(4^(a+2)*qcount s)) []
    ([0;0;1] ++ d4 ++ e4^^a ++ c4 ++ [0;0;1;1] ++ [1;1;1;1]^^s)
    ([0;0;1] ++ d4 ++ e4^^(a+s) ++ c4 ++ [0;0;1;1]).
Proof.
  revert a. induction s as [|s IH]; intro a.
  - cbn [qcount]. rewrite Nat.mul_0_r, Nat.add_0_r.
    cbn [lpow]. rewrite app_nil_r. constructor.
  - pose proof (finite_suffix ([1;1;1;1]^^s) (J_consume a)) as H1.
    pose proof (IH (1+a)) as H2.
    replace (a+1) with (1+a) in H1 by lia.
    repeat rewrite <-app_assoc in H1.
    cbn [app] in H1.
    pose proof (finite_trans H1 H2) as H12.
    assert (HC : 4^(a+2)+4^(1+a+2)*qcount s = 4^(a+2)*qcount (S s)).
    { rewrite qcount_S.
      replace (1+a+2) with (S (a+2)) by lia.
      rewrite (pow4_next (a+2)). nia. }
    rewrite <-HC. replace (a+S s) with (1+a+s) by lia.
    cbn [lpow]. repeat rewrite <-app_assoc. cbn [app]. exact H12.
Qed.

Lemma F_AZ_small :
  segRLs tm hf [] ([0;0;0] ++ z4) ([0;0;1] ++ a4).
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). reflexivity. Qed.

Theorem J_terminal a :
  segRLs tm (hf^^(4^(a+2)+3*4^(a+3))) []
    ([0;0;1] ++ d4 ++ e4^^a ++ c4 ++ [0;0;1;1] ++ a4 ++ z4^^2)
    ([0;0;1] ++ d4 ++ e4^^(a+3) ++ a4 ++ z4).
Proof.
  pose proof A_C0011 as HC1.
  change (segRLs tm [((A,[]),(F,[]))] [] (c4++[0;0;1;1])
    (z4^^0 ++ [0] ++ ([0;0;1]++a4))) in HC1.
  pose proof (finite_suffix (a4++z4^^2) (J_to_P a 0 _ _ HC1)) as H1.
  replace (1+a+0) with (a+1) in H1 by lia.
  pose proof (segment_suffix [0;0;0;0;0;0;0] C_BAA0) as HC2.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++a4++a4++z4^^2)
    (z4^^1 ++ (c4++[0;0;0;1]++a4++z4))) in HC2.
  pose proof (P_to_J a 1 _ _ HC2) as H2.
  replace (1+a) with (a+1) in H2 by lia.
  pose proof (segment_suffix (a4++z4) A_C0001) as HC3.
  change (segRLs tm [((A,[]),(F,[]))] [] (c4++[0;0;0;1]++a4++z4)
    (z4^^0 ++ [0] ++ ([0;0;1;1;1;1;1]++a4++z4))) in HC3.
  pose proof (J_to_P (a+1) 0 _ _ HC3) as H3.
  replace (1+(a+1)+0) with (a+2) in H3 by lia.
  pose proof (segment_suffix (a4++z4) C_B1111) as HC4.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++[1;1;1;1]++a4++z4)
    (z4^^2 ++ (a4++z4))) in HC4.
  pose proof (P_to_J (a+1) 2 _ _ HC4) as H4.
  replace (1+(a+1)) with (a+2) in H4 by lia.
  replace (a+1+2) with (a+3) in H4 by lia.
  norm_word_hyp H1. norm_word_hyp H2.
  norm_word_hyp H3. norm_word_hyp H4.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  assert (HC : (((1+ucount (a+1))+(1+vcount (a+1)))+
                 (1+ucount (a+2)))+(1+vcount (a+3)) = 4^(a+2)+3*4^(a+3)).
  { pose proof (ucount_positive (a+1)). pose proof (ucount_power (a+1)).
    replace (a+2) with (S (a+1)) by lia.
    replace (a+3) with (S (S (a+1))) by lia.
    unfold vcount. cbn [ucount]. rewrite (pow4_next (S (a+1))). lia. }
  rewrite <-HC. norm_word_hyp H1234. norm_word_goal. exact H1234.
Qed.

Definition hterminal_count a s :=
  4^(a+3)+4^(a+4)*qcount s+4^(a+s+4)+3*4^(a+s+5).

Theorem H_terminal a s :
  segRLs tm (hf^^hterminal_count a s) []
    (hword a 0 ++ [0;0;0] ++ z4 ++ [1;1;1;1]^^(1+s) ++ a4 ++ z4^^2)
    ([0;0;1] ++ d4 ++ e4^^(a+s+5) ++ a4 ++ z4).
Proof.
  pose proof (segRLs_concat (H_empty_batch a) F_AZ_small) as HH1.
  pose proof (finite_suffix ([1;1;1;1]^^(1+s)++a4++z4^^2) HH1) as H1.
  pose proof (segment_suffix ([1;1;1;1]^^s++a4++z4^^2) C_BAW) as HC2.
  change (segRLs tm [((C,[]),(F,[]))] []
    (b4++a4++[1;1;1;1]^^(1+s)++a4++z4^^2)
    (z4^^1 ++ (c4++[0;0;1;1]++[1;1;1;1]^^s++a4++z4^^2))) in HC2.
  pose proof (P_to_J (a+1) 1 _ _ HC2) as H2.
  replace (1+(a+1)) with (a+2) in H2 by lia.
  replace (a+1+1) with (a+2) in H2 by lia.
  pose proof (finite_suffix (a4++z4^^2) (J_consume_many s (a+2))) as H3.
  replace (a+2+s) with (a+s+2) in H3 by lia.
  replace (a+2+2) with (a+4) in H3 by lia.
  pose proof (J_terminal (a+s+2)) as H4.
  replace (a+s+2+2) with (a+s+4) in H4 by lia.
  replace (a+s+2+3) with (a+s+5) in H4 by lia.
  norm_word_hyp H1. norm_word_hyp H2.
  norm_word_hyp H3. norm_word_hyp H4.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  assert (HC : (1+ucount (a+2))+(1+vcount (a+2)) = 4^(a+3)).
  { pose proof (ucount_positive (a+2)). pose proof (ucount_power (a+2)).
    replace (a+3) with (S (a+2)) by lia. unfold vcount. lia. }
  unfold hterminal_count.
  replace (4^(a+3)+4^(a+4)*qcount s+4^(a+s+4)+3*4^(a+s+5)) with
    ((((1+ucount (a+2))+(1+vcount (a+2)))+4^(a+4)*qcount s)+
     (4^(a+s+4)+3*4^(a+s+5))) by lia.
  norm_word_hyp H1234. norm_word_goal. exact H1234.
Qed.

Definition seed_tail := [0;0;0] ++ z4 ++ a4 ++ z4 ++ [0;1;1;1] ++ [1;1;1;1] ++ a4.
Definition seed_tail40 := [0;0;0] ++ z4 ++ [1;1;1;1]^^4 ++ a4.

Lemma seed_tail_counter : segRLs tm (hf^^40) [] seed_tail seed_tail40.
Proof. apply BoundedConfig.segRLs_c_spec with (T:=1000). native_check_eq. Qed.

Theorem L_repeat n k :
  segRLs tm (hf^^(4^(k+2)*qcount n)) []
    ([0;0;0] ++ z4^^(k+n+1) ++ [0])
    ([0;0;0] ++ z4^^(k+1) ++ [0] ++ [0;0;0;1]^^n).
Proof.
  revert k. induction n as [|n IH]; intro k.
  - cbn [qcount]. rewrite Nat.mul_0_r, Nat.add_0_r.
    cbn [lpow]. rewrite app_nil_r. constructor.
  - pose proof (IH (1+k)) as H1.
    pose proof (finite_suffix ([0;0;0;1]^^n) (U_prefix_L k)) as H2.
    replace (1+k+1) with (S (S k)) in H1 by lia.
    repeat rewrite <-app_assoc in H1.
    repeat rewrite <-app_assoc in H2. cbn [app] in H1, H2.
    pose proof (finite_trans H1 H2) as H12.
    assert (HC : 4^(1+k+2)*qcount n+4^(S (S k)) = 4^(k+2)*qcount (S n)).
    { rewrite qcount_S.
      replace (1+k+2) with (S (k+2)) by lia.
      replace (S (S k)) with (k+2) by lia.
      rewrite (pow4_next (k+2)). nia. }
    rewrite <-HC.
    replace (k+S n+1) with (1+k+n+1) by lia.
    replace (k+1) with (S k) by lia.
    cbn [lpow]. repeat rewrite <-app_assoc. cbn [app]. exact H12.
Qed.

Definition first_seek_count k := 2*4^(k+9)+4^(k+4)*qcount 6+16*ucount k.

Theorem first_seek_finite k :
  segRLs tm (hf^^first_seek_count k) []
    ([0;0;0] ++ z4^^(k+10) ++ [0])
    ([0;0;0] ++ z4^^2 ++ a4^^(k+1) ++ z4 ++ a4^^5 ++ [1;1;1;1;1]).
Proof.
  pose proof (U_prefix_M (k+8)) as H1.
  pose proof (finite_suffix [1;1;1;1] (L_repeat 6 (k+2))) as H2.
  replace (k+2+6+1) with (S (k+8)) in H2 by lia.
  replace (k+2+1) with (k+3) in H2 by lia.
  replace (k+2+2) with (k+4) in H2 by lia.
  repeat rewrite <-app_assoc in H2. cbn [app] in H2.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_suffix (z4 ++ [0;0;0;1]^^6 ++ [1;1;1;1])
                (U_near_end k)) as H3.
  rewrite near_end_count in H3.
  assert (HW : ([0;0;0] ++ z4^^(k+3) ++ [0]) ++
                   [0;0;0;1]^^6 ++ [1;1;1;1] =
                ([0;0;0] ++ z4^^(S (S k)) ++ [0]) ++
                   z4 ++ [0;0;0;1]^^6 ++ [1;1;1;1]).
  { replace (k+3) with (S (S k)+1) by lia.
    pose proof (z4_recut (S (S k)) 1) as HZ.
    pose proof (f_equal (fun w => [0;0;0] ++ w ++ [0;0;0;1]^^6 ++ [1;1;1;1]) HZ) as HE.
    repeat rewrite <-app_assoc in HE.
    repeat rewrite <-app_assoc. cbn [app] in HE |- *. exact HE. }
  repeat rewrite <-app_assoc in HW. cbn [app] in HW.
  rewrite HW in H12.
  repeat rewrite <-app_assoc in H3. cbn [app] in H3.
  pose proof (finite_trans H12 H3) as H123.
  unfold first_seek_count.
  replace (k+9) with (S (k+8)) by lia.
  norm_word_hyp H123. norm_word_goal. exact H123.
Qed.

Theorem P_advance k p :
  segRLs tm (hf^^(2*4^(k+3))) []
    ([0;0;1] ++ a4^^(1+k) ++ b4 ++ d4 ++ z4^^(2+p))
    ([0;0;1] ++ a4^^(k+3) ++ b4 ++ d4 ++ z4^^p).
Proof.
  pose proof (segment_suffix (z4^^(1+p)) C_BDZ) as HC1.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++d4++z4^^(2+p))
    (z4^^2 ++ (c4++z4^^(1+p)))) in HC1.
  pose proof (P_to_J k 2 _ _ HC1) as H1.
  pose proof (segment_suffix (z4^^p) A_CZ) as HC2.
  change (segRLs tm [((A,[]),(F,[]))] [] (c4++z4^^(1+p))
    (z4^^0 ++ [0] ++ ([0;0;1]++d4++z4^^p))) in HC2.
  pose proof (J_to_P (k+2) 0 _ _ HC2) as H2.
  replace (1+(k+2)+0) with (k+3) in H2 by lia.
  norm_word_hyp H1. norm_word_hyp H2.
  pose proof (finite_trans H1 H2) as H12.
  assert (HC : (1+vcount (k+2))+(1+ucount (k+3)) = 2*4^(k+3)).
  { pose proof (ucount_positive (k+2)). pose proof (ucount_power (k+2)).
    replace (k+3) with (S (k+2)) by lia.
    unfold vcount. cbn [ucount]. lia. }
  rewrite <-HC. norm_word_hyp H12. norm_word_goal. exact H12.
Qed.

Definition post_count j :=
  4^(j+3)+4^(j+49)+2731*4^(j+50)+2*4^(j+51)+2*4^(j+53).

Lemma post_count_components j :
  (((((4^(j+3)+(1+ucount (j+48)))+(1+vcount (j+48)))+
      (1+ucount (j+49)))+2*4^(j+51))+2*4^(j+53))+(1+vcount (j+55))
    = post_count j.
Proof.
  assert (Hu5 : ucount 5 = 1365) by reflexivity.
  pose proof (ucount_add (j+49) 5) as Hsum.
  replace (j+49+5+1) with (j+55) in Hsum by lia. rewrite Hu5 in Hsum.
  pose proof (ucount_power (j+48)) as H48.
  replace (S (j+48)) with (j+49) in H48 by lia.
  pose proof (ucount_power (j+49)) as H49.
  replace (S (j+49)) with (j+50) in H49 by lia.
  replace (j+49+1) with (j+50) in Hsum by lia.
  pose proof (ucount_positive (j+48)). pose proof (ucount_positive (j+55)).
  unfold post_count, vcount. lia.
Qed.

Definition post_input j :=
  hword j 0 ++ [0;0;0] ++ z4^^2 ++ a4^^44 ++ z4 ++ a4^^5 ++ [1;1;1;1] ++ b4 ++ [1;1;1].

Ltac flat_word_hyp H :=
  cbn [lpow app] in H;
  repeat rewrite <-app_assoc in H;
  cbn [app] in H.

Ltac flat_word_goal :=
  cbn [lpow app]; repeat rewrite <-app_assoc; cbn [app].

Theorem post_finite j :
  segRLs tm (hf^^post_count j) [] (post_input j)
    ([0;0;1] ++ d4 ++ e4^^(j+55) ++ b4 ++ [1;1;1]).
Proof.
  pose proof (finite_suffix (a4^^44++z4++a4^^5++[1;1;1;1]++b4++[1;1;1])
                (H_advance j 0)) as H1.
  pose proof (finite_suffix (a4^^5++[1;1;1;1]++b4++[1;1;1])
                (H_collapse (j+2) 44)) as H2.
  replace (j+2+44+2) with (j+48) in H2 by lia.
  pose proof (segment_suffix (b4++[1;1;1]) C_BA6W) as HC3.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++a4^^6++[1;1;1;1]++b4++[1;1;1])
    (z4^^1 ++ (c4++z4^^5++[0;0;1;1]++b4++[1;1;1]))) in HC3.
  pose proof (P_to_J (j+47) 1 _ _ HC3) as H3.
  replace (1+(j+47)) with (j+48) in H3 by lia.
  replace (j+47+1) with (j+48) in H3 by lia.
  pose proof (segment_suffix (z4^^4++[0;0;1;1]++b4++[1;1;1]) A_CZ) as HC4.
  change (segRLs tm [((A,[]),(F,[]))] [] (c4++z4^^5++[0;0;1;1]++b4++[1;1;1])
    (z4^^0 ++ [0] ++ ([0;0;1]++d4++z4^^4++[0;0;1;1]++b4++[1;1;1]))) in HC4.
  pose proof (J_to_P (j+48) 0 _ _ HC4) as H4.
  replace (1+(j+48)+0) with (j+49) in H4 by lia.
  pose proof (finite_suffix ([0;0;1;1]++b4++[1;1;1]) (P_advance (j+48) 2)) as H5.
  replace (1+(j+48)) with (j+49) in H5 by lia.
  replace (j+48+3) with (j+51) in H5 by lia.
  pose proof (finite_suffix ([0;0;1;1]++b4++[1;1;1]) (P_advance (j+50) 0)) as H6.
  replace (1+(j+50)) with (j+51) in H6 by lia.
  replace (j+50+3) with (j+53) in H6 by lia.
  pose proof (segment_suffix (b4++[1;1;1]) C_BD0011) as HC7.
  change (segRLs tm [((C,[]),(F,[]))] [] (b4++d4++[0;0;1;1]++b4++[1;1;1])
    (z4^^3 ++ (b4++[1;1;1]))) in HC7.
  pose proof (P_to_J (j+52) 3 _ _ HC7) as H7.
  replace (1+(j+52)) with (j+53) in H7 by lia.
  replace (j+52+3) with (j+55) in H7 by lia.
  flat_word_hyp H1. flat_word_hyp H2. flat_word_hyp H3.
  flat_word_hyp H4. flat_word_hyp H5. flat_word_hyp H6. flat_word_hyp H7.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  pose proof (finite_trans H12345 H6) as H123456.
  pose proof (finite_trans H123456 H7) as H1234567.
  rewrite <-post_count_components. unfold post_input.
  flat_word_hyp H1234567. flat_word_goal. exact H1234567.
Qed.

Lemma prefix_M k :
  segRLs tm (hf^^(2*4^(k+1))) []
    ([0;0;0]++z4^^(k+2)++[0]) ([0;0;0]++z4^^(k+1)++[0;1;1;1;1]).
Proof.
  replace (k+1) with (S k) by lia.
  replace (k+2) with (S (S k)) by lia. apply U_prefix_M.
Qed.

Lemma prefix_L k :
  segRLs tm (hf^^(4^(k+2))) []
    ([0;0;0]++z4^^(k+2)++[0]) ([0;0;0]++z4^^(k+1)++[0;0;0;0;1]).
Proof.
  replace (k+1) with (S k) by lia.
  replace (k+2) with (S (S k)) by lia. apply U_prefix_L.
Qed.

Definition second_tail :=
  [0;0;0;1]++[0;0;0;1]++[1;1;1;1]++[0;0;0;1]++
  [1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[1;1;1;1].
Definition second_top_count k :=
  2*4^(k+56)+3*4^(k+55)+3*4^(k+53)+3*4^(k+51)+4^(k+50).

Theorem second_top k :
  segRLs tm (hf^^second_top_count k) []
    ([0;0;0]++z4^^(k+57)++[0])
    ([0;0;0]++z4^^(k+49)++[0]++second_tail).
Proof.
  pose proof (prefix_M (k+55)) as H1.
  replace (k+55+1) with (k+56) in H1 by lia.
  replace (k+55+2) with (k+57) in H1 by lia.
  pose proof (finite_suffix [1;1;1;1] (prefix_M (k+54))) as H2.
  replace (k+54+1) with (k+55) in H2 by lia.
  replace (k+54+2) with (k+56) in H2 by lia.
  pose proof (finite_suffix ([1;1;1;1]++[1;1;1;1]) (prefix_L (k+53))) as H3.
  replace (k+53+1) with (k+54) in H3 by lia.
  replace (k+53+2) with (k+55) in H3 by lia.
  pose proof (finite_suffix ([0;0;0;1]++[1;1;1;1]++[1;1;1;1]) (prefix_M (k+52))) as H4.
  replace (k+52+1) with (k+53) in H4 by lia.
  replace (k+52+2) with (k+54) in H4 by lia.
  pose proof (finite_suffix ([1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[1;1;1;1]) (prefix_L (k+51))) as H5.
  replace (k+51+1) with (k+52) in H5 by lia.
  replace (k+51+2) with (k+53) in H5 by lia.
  pose proof (finite_suffix ([0;0;0;1]++[1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[1;1;1;1]) (prefix_M (k+50))) as H6.
  replace (k+50+1) with (k+51) in H6 by lia.
  replace (k+50+2) with (k+52) in H6 by lia.
  pose proof (finite_suffix ([1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[1;1;1;1]) (prefix_L (k+49))) as H7.
  replace (k+49+1) with (k+50) in H7 by lia.
  replace (k+49+2) with (k+51) in H7 by lia.
  pose proof (finite_suffix ([0;0;0;1]++[1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[0;0;0;1]++[1;1;1;1]++[1;1;1;1]) (prefix_L (k+48))) as H8.
  replace (k+48+1) with (k+49) in H8 by lia.
  replace (k+48+2) with (k+50) in H8 by lia.
  flat_word_hyp H1. flat_word_hyp H2. flat_word_hyp H3. flat_word_hyp H4.
  flat_word_hyp H5. flat_word_hyp H6. flat_word_hyp H7. flat_word_hyp H8.
  pose proof (finite_trans H1 H2) as H12.
  pose proof (finite_trans H12 H3) as H123.
  pose proof (finite_trans H123 H4) as H1234.
  pose proof (finite_trans H1234 H5) as H12345.
  pose proof (finite_trans H12345 H6) as H123456.
  pose proof (finite_trans H123456 H7) as H1234567.
  pose proof (finite_trans H1234567 H8) as H12345678.
  unfold second_top_count, second_tail.
  replace (2*4^(k+56)+3*4^(k+55)+3*4^(k+53)+3*4^(k+51)+4^(k+50)) with
    (((((((2*4^(k+56)+2*4^(k+55))+4^(k+55))+2*4^(k+53))+
      4^(k+53))+2*4^(k+51))+4^(k+51))+4^(k+50)) by lia.
  flat_word_hyp H12345678. flat_word_goal. exact H12345678.
Qed.

Definition second_result_tail :=
  a4++[1;1;1;1]++a4++[1;1;1;1]++a4++[1;1;1;1]^^2++[1].

Lemma second_tail_split : second_tail = [0;0;0]++second_result_tail.
Proof. reflexivity. Qed.

Lemma second_tail_join p :
  [1]++z4^^p++second_tail = a4++z4^^p++second_result_tail.
Proof.
  rewrite second_tail_split.
  pose proof (f_equal (fun w => [1]++w++second_result_tail) (z4_zero3_shift p)) as H.
  repeat rewrite <-app_assoc in H. cbn [app] in H |- *.
  repeat rewrite <-app_assoc in H. cbn [app] in H. exact H.
Qed.

Definition second_seek_count k := 16*ucount k+post_count (1+k).

Lemma second_seek_count_sum k :
  second_top_count k+(4^(k+4)+16*ucount k) = second_seek_count k.
Proof.
  unfold second_top_count, second_seek_count, post_count.
  replace (1+k+3) with (k+4) by lia.
  replace (1+k+49) with (k+50) by lia.
  replace (1+k+50) with (k+51) by lia.
  replace (1+k+51) with (k+52) by lia.
  replace (1+k+53) with (k+54) by lia.
  replace (k+52) with (S (k+51)) by lia.
  replace (k+53) with (S (S (k+51))) by lia.
  replace (k+54) with (S (S (S (k+51)))) by lia.
  replace (k+55) with (S (S (S (S (k+51))))) by lia.
  replace (k+56) with (S (S (S (S (S (k+51)))))) by lia.
  repeat rewrite pow4_next. lia.
Qed.

Theorem second_seek_finite k :
  segRLs tm (hf^^second_seek_count k) []
    ([0;0;0]++z4^^(k+57)++[0])
    ([0;0;0]++z4^^2++a4^^(1+k)++z4++a4++z4^^45++second_result_tail).
Proof.
  pose proof (second_top k) as H1.
  pose proof (finite_suffix (z4^^45++second_tail) (seek_lower k)) as H2.
  assert (HW : [0;0;0]++z4^^(k+49)++[0]++second_tail =
    ([0;0;0]++z4^^(k+4)++[0])++z4^^45++second_tail).
  { pose proof (f_equal (fun w => [0;0;0]++w++second_tail)
                  (z4_recut (k+4) 45)) as H.
    replace (k+4+45) with (k+49) in H by lia.
    repeat rewrite <-app_assoc in H.
    repeat rewrite <-app_assoc. cbn [app] in H |- *. exact H. }
  rewrite HW in H1.
  pose proof (finite_trans H1 H2) as H12.
  rewrite <-second_seek_count_sum.
  repeat rewrite <-app_assoc in H12.
  rewrite second_tail_join in H12.
  replace (S k) with (1+k) in H12 by lia.
  repeat rewrite <-app_assoc. exact H12.
Qed.

Lemma qcount_power k : 3*qcount k+1 = 4^k.
Proof. destruct k; [reflexivity|apply ucount_power]. Qed.

Lemma qcount_add a b : qcount (a+b) = qcount a+4^a*qcount b.
Proof.
  induction a as [|a IH].
  - cbn [qcount Nat.pow Nat.mul Nat.add]. rewrite Nat.add_0_r. reflexivity.
  - replace (S a+b) with (S (a+b)) by lia.
    rewrite !qcount_S, IH, pow4_next. nia.
Qed.

Lemma qcount_succ_ucount k : qcount (1+k) = ucount k.
Proof. reflexivity. Qed.

Lemma first_entrance_count k :
  1360+4096*qcount k+hterminal_count (k+4) 3 = first_seek_count (k+3).
Proof.
  assert (H3 : qcount 3 = 21) by reflexivity.
  assert (H4 : qcount 4 = 85) by reflexivity.
  assert (H6 : qcount 6 = 1365) by reflexivity.
  pose proof (qcount_add k 4) as Hu. rewrite H4 in Hu.
  replace (k+4) with (S (k+3)) in Hu by lia. cbn [qcount] in Hu.
  pose proof (qcount_power k) as Hp.
  unfold hterminal_count, first_seek_count. rewrite H3, H6.
  replace (k+4+3+4) with (k+11) by lia.
  replace (k+4+3+5) with (k+12) by lia.
  replace (k+4+3) with (k+7) by lia.
  replace (k+4+4) with (k+8) by lia.
  replace (k+3+9) with (k+12) by lia.
  replace (k+3+4) with (k+7) by lia.
  replace (k+8) with (S (k+7)) by lia.
  replace (k+11) with (S (S (S (S (k+7))))) by lia.
  replace (k+12) with (S (S (S (S (S (k+7)))))) by lia.
  repeat rewrite pow4_next. lia.
Qed.

Lemma first_seek_positive k : 1 <= first_seek_count k.
Proof. pose proof (ucount_positive k). unfold first_seek_count. lia. Qed.

Definition second_index k := 15+16*(ucount k-1)+post_count (1+k).

Lemma second_index_eq k : second_seek_count k = 1+second_index k.
Proof.
  pose proof (ucount_positive k). unfold second_seek_count, second_index. lia.
Qed.

Lemma second_seek_count_decompose k :
  second_seek_count k = 16*ucount k+post_count (1+k).
Proof. reflexivity. Qed.

(* From here on concrete entrance parameters remain symbolic. *)
Opaque ucount qcount hterminal_count first_seek_count second_seek_count post_count second_index.

Definition first_index := first_seek_count 43-1.
Lemma first_index_eq : first_seek_count 43 = 1+first_index.
Proof. unfold first_index. pose proof (first_seek_positive 43). lia. Qed.
Opaque first_index.

Theorem J_short_reset n a (r:side) :
  Ncfg n (([0;0;1]++d4++e4^^a++b4++[1;1;1]) *> r) -->+
  Ncfg 0 (([0;0;0]++c4^^n++[0;1;1;1;1;0;0]++
             z4^^(1+a)++[0;0;1;1;0;1;1]) *> r).
Proof.
  pose proof (segRLs_concat (J_E a) A_B111) as HF.
  pose proof (finite_single_side _ _ _ _ r HF) as H.
  repeat rewrite Str_app_assoc in H.
  pose proof (N_E_reset n
    (([0;0;1]++d4++e4^^a++b4++[1;1;1]) *> r)
    ((z4^^(1+a)++[0;0;1;1;0;1;1]) *> r)) as HN.
  repeat rewrite Str_app_assoc in HN. specialize (HN H).
  repeat rewrite Str_app_assoc. exact HN.
Qed.

Lemma second_reset_recut k :
  [0;1;1;1;1;0;0]++z4^^k++[0;0;1;1;0;1;1] =
  [0;1;1;1;1]++[0;0;0]++z4^^k++[0;1;1;0;1;1].
Proof.
  pose proof (f_equal (fun w => [0;1;1;1;1;0;0]++w++[0;1;1;0;1;1])
                (z4_zero_shift k)) as H.
  repeat rewrite <-app_assoc in H. cbn [app] in H |- *.
  repeat rewrite <-app_assoc in H. cbn [app] in H. exact H.
Qed.

Definition entry_tail := a4++[1;1;1;1]++a4++[1;1;1;1]++a4++[1;1;1;1]^^2++d4++[1;1].

Theorem post_to_invariant k (r:side) :
  Ncfg (1+16*ucount k) (post_input (1+k) *> r) -->+
  invariant (second_index k) k 43 (entry_tail *> r).
Proof.
  assert (HF : sideRLs tm (hf^^post_count (1+k)) (post_input (1+k) *> r)
    (([0;0;1]++d4++e4^^(1+k+55)++b4++[1;1;1]) *> r)).
  { eapply segRLs_sideRLs_concat; [apply post_finite|constructor]. }
  pose proof (N_run (post_count (1+k)) (1+16*ucount k) _ _ HF) as HN.
  assert (HC : 1+16*ucount k+post_count (1+k) = 1+second_seek_count k).
  { rewrite second_seek_count_decompose. lia. }
  rewrite HC in HN.
  pose proof (J_short_reset (1+second_seek_count k) (1+k+55) r) as HR.
  replace (1+(1+k+55)) with (k+57) in HR by lia.
  rewrite second_reset_recut in HR.
  assert (HS : sideRLs tm (hf^^second_seek_count k)
    (([0;0;0]++z4^^(k+57)++[0]) *> ([1;1;0;1;1] *> r))
    (([0;0;0]++z4^^2++a4^^(1+k)++z4++a4++z4^^45++second_result_tail) *>
      ([1;1;0;1;1] *> r))).
  { eapply segRLs_sideRLs_concat; [apply second_seek_finite|constructor]. }
  pose proof (reset_lift (second_seek_count k) _ _ HS) as HL.
  repeat rewrite Str_app_assoc in HN.
  repeat rewrite Str_app_assoc in HR.
  repeat rewrite Str_app_assoc in HL.
  assert (Hend : Ncfg (1+16*ucount k) (post_input (1+k) *> r) -->+
    Ncfg (1+16*qcount (second_seek_count k))
      (hword (second_seek_count k) 0 *>
        (([0;0;0]++z4^^2++a4^^(1+k)++z4++a4++z4^^45++second_result_tail) *>
          ([1;1;0;1;1] *> r)))).
  { eapply evstep_progress_trans; [exact HN|].
    eapply progress_trans; [exact HR|].
    repeat rewrite Str_app_assoc. exact HL. }
  rewrite second_index_eq, qcount_succ_ucount in Hend.
  unfold invariant, entry_tail, second_result_tail in Hend |- *.
  repeat rewrite Str_app_assoc in Hend.
  repeat rewrite Str_app_assoc.
  cbn [Str_app] in Hend |- *. exact Hend.
Qed.

Definition seed_word :=
  [0;0;1]++d4++z4++e4^^2++z4++c4^^40++[0;1;1;1;1]++seed_tail.

Lemma seed_zero :
  segRLs tm (hf^^520) [] seed_word (hword 4 40++seed_tail).
Proof.
  pose proof (finite_suffix
    (e4^^2++z4++c4^^40++[0;1;1;1;1]++seed_tail) (J_zero 0)) as H1.
  pose proof (finite_suffix (c4^^40++[0;1;1;1;1]++seed_tail) (J_zero 3)) as H2.
  repeat rewrite <-app_assoc in H1, H2. cbn [app] in H1, H2.
  pose proof (finite_trans H1 H2) as H12.
  change (segRLs tm (hf^^520) [] seed_word (hword 4 40++seed_tail)) in H12.
  exact H12.
Qed.

Definition seed_count := (520+4^6*qcount 40)+hterminal_count 44 3.

Lemma seed_finish :
  segRLs tm (hf^^seed_count) [] (seed_word++z4^^2)
    ([0;0;1]++d4++e4^^52++a4++z4).
Proof.
  pose proof (finite_suffix (z4^^2) seed_zero) as H1.
  pose proof (segRLs_concat (H_lift_finite 4 0 40) seed_tail_counter) as HH2.
  pose proof (finite_suffix (z4^^2) HH2) as H2.
  pose proof (H_terminal 44 3) as H3.
  repeat rewrite <-app_assoc in H1, H2, H3.
  cbn [app] in H1, H2, H3.
  pose proof (finite_trans H1 H2) as H12.
  unfold seed_tail40 in H12. repeat rewrite <-app_assoc in H12. cbn [app] in H12.
  pose proof (finite_trans H12 H3) as H123.
  exact H123.
Qed.

Lemma seed_count_total : 841+seed_count = 1+first_seek_count 43.
Proof.
  pose proof (first_entrance_count 40) as H.
  change (1360+4096*qcount 40+hterminal_count 44 3=first_seek_count 43) in H.
  unfold seed_count. change (841+(520+4096*qcount 40+hterminal_count 44 3)=
    1+first_seek_count 43). lia.
Qed.

Theorem first_reset (r:side) :
  Ncfg 841 ((seed_word++z4^^2) *> r) -->+
  Ncfg 0 (([0;0;0]++c4^^(1+first_seek_count 43)++[0;1;1;1;1;0;0]++
    z4^^54++[1;1;1;1]) *> r).
Proof.
  assert (HF : sideRLs tm (hf^^seed_count) ((seed_word++z4^^2) *> r)
    (([0;0;1]++d4++e4^^52++a4++z4) *> r)).
  { eapply segRLs_sideRLs_concat; [apply seed_finish|constructor]. }
  pose proof (N_run seed_count 841 _ _ HF) as HN.
  rewrite seed_count_total in HN.
  eapply evstep_progress_trans; [exact HN|].
  pose proof (J_reset (1+first_seek_count 43) 52 0 r) as HR.
  repeat rewrite app_nil_r in HR. exact HR.
Qed.

Theorem first_reset_to_post (r:side) :
  Ncfg 0 (([0;0;0]++c4^^(1+first_seek_count 43)++[0;1;1;1;1;0;0]++
    z4^^54++[1;1;1;1]) *> r) -->+
  Ncfg (1+16*ucount first_index) (post_input (1+first_index) *> r).
Proof.
  assert (HS : sideRLs tm (hf^^first_seek_count 43)
    (([0;0;0]++z4^^53++[0]) *> ([0;0;1;1;1;1] *> r))
    (([0;0;0]++z4^^2++a4^^44++z4++a4^^5++[1;1;1;1;1]) *>
      ([0;0;1;1;1;1] *> r))).
  { eapply segRLs_sideRLs_concat; [apply first_seek_finite|constructor]. }
  pose proof (reset_lift (first_seek_count 43) _ _ HS) as HL.
  rewrite first_index_eq, qcount_succ_ucount in HL.
  rewrite first_index_eq.
  unfold post_input.
  repeat rewrite Str_app_assoc in HL.
  repeat rewrite Str_app_assoc.
  cbn [Str_app] in HL |- *. exact HL.
Qed.

(* Finite-prefix certificates imply the counter rule for every side,
   not merely an all-blank right exterior. *)
Lemma Ufinite_side k (r:side) :
  Ufinite k ->
  sideRLs tm (hf^^ucount k)
    (([0;0;0] ++ z4^^k ++ [0]) *> r)
    (([0;0;1] ++ a4^^k ++ [1]) *> r).
Proof.
  intro H. eapply segRLs_sideRLs_concat; [exact H|constructor].
Qed.

Lemma Vfinite_side k (r:side) :
  Vfinite k ->
  sideRLs tm (hf^^vcount k)
    (([0;0;0] ++ c4 ++ z4^^k) *> r)
    (([0;0;1] ++ d4 ++ e4^^k) *> r).
Proof.
  intro H. eapply segRLs_sideRLs_concat; [exact H|constructor].
Qed.

Theorem counter_U k (r:side) :
  sideRLs tm (hf^^ucount k)
    (([0;0;0] ++ z4^^k ++ [0]) *> r)
    (([0;0;1] ++ a4^^k ++ [1]) *> r).
Proof. apply Ufinite_side, Ufinite_all. Qed.

Theorem counter_V k (r:side) :
  sideRLs tm (hf^^vcount k)
    (([0;0;0] ++ c4 ++ z4^^k) *> r)
    (([0;0;1] ++ d4 ++ e4^^k) *> r).
Proof. apply Vfinite_side, Vfinite_all. Qed.

Theorem seed_nonhalt (r:side) :
  ~halts tm (Ncfg 841 ((seed_word++z4^^2) *> r)).
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep. apply first_reset.
  - eapply multistep_nonhalt.
    + apply progress_evstep. apply first_reset_to_post.
    + eapply multistep_nonhalt.
      * apply progress_evstep. apply post_to_invariant.
      * apply invariant_nonhalt.
Qed.

(* A small evaluator only for the finite native entrance.  The large
   counter budgets above remain opaque and are never evaluated. *)
Fixpoint native_chunked tm0 n1 n2 n3 c :=
  match n1 with
  | O => multistep_c tm0 n3 c
  | S n1 =>
      match multistep_c tm0 n2 c with
      | Some c => native_chunked tm0 n1 n2 n3 c
      | None => None
      end
  end.

Lemma native_chunked_spec tm0 n1 n2 n3 c c' :
  native_chunked tm0 n1 n2 n3 c = Some c' <->
  c -[tm0]->> (n1*n2+n3) / c'.
Proof.
  revert c c'. induction n1; cbn [native_chunked]; intros.
  - apply multistep_c_spec.
  - destruct (multistep_c tm0 n2 c) eqn:E.
    + apply multistep_c_spec in E. rewrite IHn1.
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      split; intro H.
      * eapply multistep_trans; eauto 1.
      * eapply rewind_split in H.
        destruct H as [c0' [H1 H2]]. multistep_deterministic. eauto 1.
    + split; [congruence|].
      replace (S n1*n2+n3) with (n2+(n1*n2+n3)) by lia.
      intro H. eapply rewind_split in H.
      destruct H as [c0' [H1 H2]].
      eapply multistep_c_spec in H1. congruence.
Qed.

Definition native_calculated := Eval vm_compute in
  native_chunked tm 3164 3164 433 c0.

Lemma native_calculated_target : native_calculated =
  Some (Ncfg 841 (seed_word *> 0inf)).
Proof.
  vm_compute. repeat rewrite <-const_unfold. reflexivity.
Qed.

Theorem native_init : c0 -->* Ncfg 841 (seed_word *> 0inf).
Proof.
  eapply without_counter.
  eapply native_chunked_spec with (n1:=3164) (n2:=3164) (n3:=433).
  transitivity native_calculated; [native_check_eq|exact native_calculated_target].
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply native_init|].
  replace (seed_word *> 0inf) with ((seed_word++z4^^2) *> 0inf).
  - apply seed_nonhalt.
  - rewrite Str_app_assoc. f_equal.
    cbn [lpow app Str_app]. repeat rewrite <-const_unfold. reflexivity.
Qed.

End TM1.
