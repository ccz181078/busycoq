From BusyCoq Require Import Individual62 Longitudinal.
Require Import ZifyNat Lia ZArith String List.

Import ListNotations.
Open Scope list.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Inductive Column := ColA | ColB | ColC.
Inductive Particle := At | P100 | P110.

Fixpoint copies (x : Column) (n : nat) : list Column :=
  match n with
  | O => []
  | S n' => x :: copies x n'
  end.

Definition qtail (extra : bool) (n : nat) : list Column :=
  if extra then ColC :: copies ColB n else copies ColB n.

Inductive Returns (extra : bool) :
    Particle -> nat -> nat -> list Column -> list Column -> Prop :=
| Ret_At_A a b r r' :
    Returns extra At (2*a) (2*b+1) r r' ->
    Returns extra At a b (ColA::r) (ColA::r')
| Ret_P_A a b r r' :
    Returns extra At (2*a) b r r' ->
    Returns extra P100 a b (ColA::r) (ColC::r')
| Ret_Q_A a b r r' :
    Returns extra At (2*a+1) b r r' ->
    Returns extra P110 a b (ColA::r) (ColB::r')
| Ret_At_B a b r r' :
    Returns extra P100 a (2*b) r r' ->
    Returns extra At a b (ColB::r) (ColA::r')
| Ret_P_B a b r r' :
    Returns extra P100 a b r r' ->
    Returns extra P100 a (S b) (ColB::r) (ColC::r')
| Ret_Q_B a b r r' :
    Returns extra P110 a b r r' ->
    Returns extra P110 a (S b) (ColB::r) (ColB::r')
| Ret_At_C a b r r' :
    Returns extra P110 a (2*b) r r' ->
    Returns extra At a b (ColC::r) (ColA::r')
| Ret_P_C a b r r' :
    Returns extra P110 a b r r' ->
    Returns extra P100 a (S b) (ColC::r) (ColC::r')
| Ret_Q_C a b r r' :
    Returns extra P100 (S a) b r r' ->
    Returns extra P110 a (S b) (ColC::r) (ColB::r')
| Ret_At_edge a b :
    1 <= a -> a <= 2*b+1 ->
    Returns extra At a b []
      (ColA :: copies ColC (a-1) ++ copies ColB (2*b+3-a))
| Ret_P_edge a b :
    a <= b ->
    Returns extra P100 a b []
      (copies ColC a ++ copies ColB (b+2-a))
| Ret_Q_edge a b :
    a <= b ->
    Returns extra P110 a b []
      (copies ColB a ++ ColA :: qtail extra (2*(b-a)+1)).

Definition mass (p : Particle) : nat :=
  match p with At => 1 | P100 | P110 => 2 end.

Definition offset (x y : Particle) : nat :=
  match x,y with
  | At,At => 0 | At,P100 => 1 | At,P110 => 2
  | P100,At | P110,At => 1
  | P100,P100 | P110,P100 => 3
  | P100,P110 | P110,P110 => 4
  end.

Definition Fuel (x : Particle) (b : nat)
    (y : Particle) (c d : nat) : Prop :=
  mass y * (b+c) + offset x y <= d.

Ltac chase_step IH yy cc dd C :=
  let Hfuel := fresh "Hfuel" in
  let s := fresh "s" in
  let Hs := fresh "Hs" in
  lazymatch type of IH with
  | forall (_ : Particle) (_ _ : nat), Fuel ?xx ?bb _ _ _ -> _ =>
      assert (Hfuel : Fuel xx bb yy cc dd) by
        (unfold Fuel in *; cbn [mass offset] in *; lia);
      destruct (IH yy cc dd Hfuel) as [s Hs];
      eexists; eapply C; exact Hs
  end.

Lemma Returns_Bs_P extra n c e tail :
  (exists s, Returns extra P100 c e tail s) ->
  exists s, Returns extra P100 c (n+e) (copies ColB n ++ tail) s.
Proof.
  induction n; cbn; intros H.
  - exact H.
  - destruct (IHn H) as [s Hs].
    exists (ColC::s).
    replace (S n+e) with (S (n+e)) by lia.
    apply Ret_P_B. exact Hs.
Qed.

Lemma Returns_Bs_Q extra n c e tail :
  (exists s, Returns extra P110 c e tail s) ->
  exists s, Returns extra P110 c (n+e) (copies ColB n ++ tail) s.
Proof.
  induction n; cbn; intros H.
  - exact H.
  - destruct (IHn H) as [s Hs].
    exists (ColB::s).
    replace (S n+e) with (S (n+e)) by lia.
    apply Ret_Q_B. exact Hs.
Qed.

Lemma Returns_B_P extra n c d :
  n+c <= d ->
  exists s, Returns extra P100 c d (copies ColB n) s.
Proof.
  intros H.
  replace d with (n+(d-n)) by lia.
  replace (copies ColB n) with (copies ColB n ++ []) by apply app_nil_r.
  apply Returns_Bs_P.
  eexists. apply Ret_P_edge. lia.
Qed.

Lemma Returns_B_Q extra n c d :
  n+c <= d ->
  exists s, Returns extra P110 c d (copies ColB n) s.
Proof.
  intros H.
  replace d with (n+(d-n)) by lia.
  replace (copies ColB n) with (copies ColB n ++ []) by apply app_nil_r.
  apply Returns_Bs_Q.
  eexists. apply Ret_Q_edge. lia.
Qed.

Lemma Returns_CB_PQ extra n m c d :
  (2*n+m+c <= d ->
   exists s, Returns extra P100 c d
     (copies ColC n ++ copies ColB m) s) /\
  (2*n+m+c <= d ->
   exists s, Returns extra P110 c d
     (copies ColC n ++ copies ColB m) s).
Proof.
  revert c d. induction n; intros c d; cbn.
  - split; intro H.
    + apply Returns_B_P. lia.
    + apply Returns_B_Q. lia.
  - split; intro H.
    + destruct d; [lia|].
      destruct (proj2 (IHn c d) ltac:(lia)) as [s Hs].
      exists (ColC::s). apply Ret_P_C. exact Hs.
    + destruct d; [lia|].
      destruct (proj1 (IHn (S c) d) ltac:(lia)) as [s Hs].
      exists (ColB::s). apply Ret_Q_C. exact Hs.
Qed.

Lemma Returns_CB_P extra n m c d :
  2*n+m+c <= d ->
  exists s, Returns extra P100 c d
    (copies ColC n ++ copies ColB m) s.
Proof. apply (proj1 (Returns_CB_PQ extra n m c d)). Qed.

Lemma Returns_CB_Q extra n m c d :
  2*n+m+c <= d ->
  exists s, Returns extra P110 c d
    (copies ColC n ++ copies ColB m) s.
Proof. apply (proj2 (Returns_CB_PQ extra n m c d)). Qed.

Lemma Returns_B_At extra m c d :
  1 <= m -> m-1+c <= 2*d ->
  exists s, Returns extra At c d (copies ColB m) s.
Proof.
  destruct m; intros; [lia|].
  cbn. destruct (Returns_B_P extra m c (2*d) ltac:(lia)) as [s Hs].
  exists (ColA::s). apply Ret_At_B. exact Hs.
Qed.

Lemma Returns_CB_At_S extra n m c d :
  2*n+m+c <= 2*d ->
  exists s, Returns extra At c d
    (copies ColC (S n) ++ copies ColB m) s.
Proof.
  cbn. intros H.
  destruct (Returns_CB_Q extra n m c (2*d) H) as [s Hs].
  exists (ColA::s). apply Ret_At_C. exact Hs.
Qed.

Lemma Returns_CB_At (extra : bool) (n m c d : nat) :
  1 <= m ->
  (n=O -> m-1+c <= 2*d) ->
  (1<=n -> 2*(n-1)+m+c <= 2*d) ->
  exists s, Returns extra At c d
    (copies ColC n ++ copies ColB m) s.
Proof.
  destruct n.
  - cbn. intros. apply Returns_B_At; auto.
  - intros. replace (S n-1) with n in H1 by lia.
    apply Returns_CB_At_S. lia.
Qed.

Lemma Returns_qtail_At (extra : bool) (m c d : nat) :
  1 <= m -> m+c <= 2*d ->
  exists s, Returns extra At c d (qtail extra m) s.
Proof.
  destruct extra; cbn [qtail]; intros.
  - change (ColC :: copies ColB m)
      with (copies ColC 1 ++ copies ColB m).
    apply Returns_CB_At_S. cbn. lia.
  - apply Returns_B_At; lia.
Qed.

Lemma Returns_A_qtail_At (extra : bool) (m c d : nat) :
  1 <= m -> m+2*c <= 2*(2*d+1) ->
  exists s, Returns extra At c d (ColA::qtail extra m) s.
Proof.
  intros.
  destruct (Returns_qtail_At extra m (2*c) (2*d+1)
    ltac:(lia) ltac:(lia)) as [s Hs].
  exists (ColA::s). apply Ret_At_A. exact Hs.
Qed.

Lemma Returns_A_qtail_P (extra : bool) (m c d : nat) :
  1 <= m -> m+2*c <= 2*d ->
  exists s, Returns extra P100 c d (ColA::qtail extra m) s.
Proof.
  intros.
  destruct (Returns_qtail_At extra m (2*c) d
    ltac:(lia) ltac:(lia)) as [s Hs].
  exists (ColC::s). apply Ret_P_A. exact Hs.
Qed.

Lemma Returns_A_qtail_Q (extra : bool) (m c d : nat) :
  1 <= m -> m+(2*c+1) <= 2*d ->
  exists s, Returns extra P110 c d (ColA::qtail extra m) s.
Proof.
  intros.
  destruct (Returns_qtail_At extra m (2*c+1) d
    ltac:(lia) ltac:(lia)) as [s Hs].
  exists (ColB::s). apply Ret_Q_A. exact Hs.
Qed.

Lemma Returns_chase_columns extra x a b r r' :
  Returns extra x a b r r' ->
  forall y c d, Fuel x b y c d ->
  exists r'', Returns extra y c d r' r''.
Proof.
  intro HR.
  induction HR; intros y c d HF; destruct y.
  - chase_step IHHR At (2*c) (2*d+1) Ret_At_A.
  - chase_step IHHR At (2*c) d Ret_P_A.
  - chase_step IHHR At (2*c+1) d Ret_Q_A.
  - chase_step IHHR P110 c (2*d) Ret_At_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_P_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 (S c) d Ret_Q_C.
  - chase_step IHHR P100 c (2*d) Ret_At_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 c d Ret_P_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_Q_B.
  - chase_step IHHR At (2*c) (2*d+1) Ret_At_A.
  - chase_step IHHR At (2*c) d Ret_P_A.
  - chase_step IHHR At (2*c+1) d Ret_Q_A.
  - chase_step IHHR P110 c (2*d) Ret_At_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_P_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 (S c) d Ret_Q_C.
  - chase_step IHHR P100 c (2*d) Ret_At_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 c d Ret_P_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_Q_B.
  - chase_step IHHR At (2*c) (2*d+1) Ret_At_A.
  - chase_step IHHR At (2*c) d Ret_P_A.
  - chase_step IHHR At (2*c+1) d Ret_Q_A.
  - chase_step IHHR P110 c (2*d) Ret_At_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_P_C.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 (S c) d Ret_Q_C.
  - chase_step IHHR P100 c (2*d) Ret_At_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P100 c d Ret_P_B.
  - destruct d; [unfold Fuel in HF; cbn [mass offset] in HF; lia|].
    chase_step IHHR P110 c d Ret_Q_B.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    destruct (Returns_CB_At extra (a-1) (2*b+3-a) (2*c) (2*d+1)
      ltac:(lia) ltac:(lia) ltac:(lia)) as [s Hs].
    exists (ColA::s). apply Ret_At_A. exact Hs.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    destruct (Returns_CB_At extra (a-1) (2*b+3-a) (2*c) d
      ltac:(lia) ltac:(lia) ltac:(lia)) as [s Hs].
    exists (ColC::s). apply Ret_P_A. exact Hs.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    destruct (Returns_CB_At extra (a-1) (2*b+3-a) (2*c+1) d
      ltac:(lia) ltac:(lia) ltac:(lia)) as [s Hs].
    exists (ColB::s). apply Ret_Q_A. exact Hs.
  - apply Returns_CB_At; unfold Fuel in HF; cbn [mass offset] in HF; lia.
  - apply Returns_CB_P; unfold Fuel in HF; cbn [mass offset] in HF; lia.
  - apply Returns_CB_Q; unfold Fuel in HF; cbn [mass offset] in HF; lia.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    destruct a.
    + cbn. apply Returns_A_qtail_At; lia.
    + cbn [copies].
      assert (a <= 2*d) by lia.
      destruct (Returns_A_qtail_P extra (2*(b-S a)+1) c (2*d-a)
        ltac:(lia) ltac:(lia)) as [s Hs].
      destruct (Returns_Bs_P extra a c (2*d-a)
        (ColA::qtail extra (2*(b-S a)+1)) (ex_intro _ s Hs))
        as [t Ht].
      replace (a+(2*d-a)) with (2*d) in Ht by lia.
      exists (ColA::t). apply Ret_At_B. exact Ht.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    assert (a <= d) by lia.
    replace d with (a+(d-a)) by lia.
    apply Returns_Bs_P.
    apply Returns_A_qtail_P; lia.
  - unfold Fuel in HF; cbn [mass offset] in HF.
    assert (a <= d) by lia.
    replace d with (a+(d-a)) by lia.
    apply Returns_Bs_Q.
    apply Returns_A_qtail_Q; lia.
Qed.

Lemma Returns_chase_P extra n r r' :
  Returns extra P100 0 (2*n) r r' ->
  exists r'', Returns extra At 0 (2*n+1) r' r''.
Proof.
  intros H.
  eapply Returns_chase_columns in H.
  - exact H.
  - unfold Fuel. cbn [mass offset]. lia.
Qed.

Lemma Returns_chase_Q extra n r r' :
  Returns extra P110 0 (2*n) r r' ->
  exists r'', Returns extra At 0 (2*n+1) r' r''.
Proof.
  intros H.
  eapply Returns_chase_columns in H.
  - exact H.
  - unfold Fuel. cbn [mass offset]. lia.
Qed.

Lemma Returns_At_closed extra b r r' :
  Returns extra At 0 b r r' ->
  exists r'', Returns extra At 0 b r' r''.
Proof.
  revert b r'. induction r as [|x r IH]; intros b r' HR.
  - inversion HR; lia.
  - destruct x.
    + inversion HR; subst.
      cbn in H0.
      destruct (IH _ _ H0) as [s Hs].
      exists (ColA::s). apply Ret_At_A. exact Hs.
    + inversion HR; subst.
      cbn in H0.
      eapply Returns_chase_columns with
        (y:=At) (c:=O) (d:=2*b+1) in H0.
      2: unfold Fuel; cbn [mass offset]; lia.
      destruct H0 as [s Hs].
      exists (ColA::s). apply Ret_At_A. exact Hs.
    + inversion HR; subst.
      cbn in H0.
      eapply Returns_chase_columns with
        (y:=At) (c:=O) (d:=2*b+1) in H0.
      2: unfold Fuel; cbn [mass offset]; lia.
      destruct H0 as [s Hs].
      exists (ColA::s). apply Ret_At_A. exact Hs.
Qed.

Lemma Returns_init_B extra :
  Returns extra At 0 0 [ColB] [ColA;ColB;ColB].
Proof.
  apply Ret_At_B. cbn.
  apply Ret_P_edge. lia.
Qed.

Lemma Returns_init_ACB extra :
  Returns extra At 0 0 [ColA;ColC;ColB]
    (ColA::ColA::ColB::ColA::qtail extra 3).
Proof.
  apply Ret_At_A.
  apply Ret_At_C.
  change (Returns extra P110 0 (S 1) [ColB]
    (ColB::ColA::qtail extra 3)).
  apply Ret_Q_B.
  apply Ret_Q_edge. lia.
Qed.

Section MachineSoundness.

Variable tm : TM.
Variable extra : bool.
Variable hu hh hp hq : list (DH0*DH0).
Variable wa wb wc : list Sym.

Record MacroRules : Prop := {
  rule_h_A : segRLs tm hh (hh^^2) wa wa;
  rule_h_B : segRLs tm hh hh wb wb;
  rule_h_C : segRLs tm hh hh wc wc;
  rule_u_A : segRLs tm hu (hu++hh) wa wa;
  rule_p_A : segRLs tm hp hu wa wc;
  rule_q_A : segRLs tm hq (hh++hu) wa wb;
  rule_u_B : segRLs tm hu hp wb wa;
  rule_p_B : segRLs tm (hp++hh) hp wb wc;
  rule_q_B : segRLs tm (hq++hh) hq wb wb;
  rule_u_C : segRLs tm hu hq wc wa;
  rule_p_C : segRLs tm (hp++hh) hq wc wc;
  rule_q_C : segRLs tm (hq++hh) (hh++hp) wc wb;
  rule_h_edge : sideRLs tm hh 0inf (wb*>0inf);
  rule_p_edge : sideRLs tm hp 0inf (wb*>wb*>0inf);
  rule_q_edge : sideRLs tm hq 0inf
    (wa*>(if extra then wc*>wb*>0inf else wb*>0inf))
}.

Variable rules : MacroRules.

Definition particle_heads (p : Particle) :=
  match p with At => hu | P100 => hp | P110 => hq end.

Definition packet (p : Particle) (a b : nat) :=
  hh^^a ++ particle_heads p ++ hh^^b.

Definition column_word (x : Column) :=
  match x with ColA => wa | ColB => wb | ColC => wc end.

Fixpoint columns_side (r : list Column) : side :=
  match r with
  | [] => 0inf
  | x::r' => column_word x *> columns_side r'
  end.

Lemma hashes_A n : segRLs tm (hh^^n) (hh^^(2*n)) wa wa.
Proof.
  induction n.
  - constructor.
  - cbn [lpow].
    replace (2*S n) with (2+2*n) by lia.
    rewrite lpow_add.
    eapply segRLs_trans.
    + apply rule_h_A, rules.
    + exact IHn.
Qed.

Lemma hashes_B n : segRLs tm (hh^^n) (hh^^n) wb wb.
Proof.
  induction n.
  - constructor.
  - cbn [lpow].
    eapply segRLs_trans.
    + apply rule_h_B, rules.
    + exact IHn.
Qed.

Lemma hashes_C n : segRLs tm (hh^^n) (hh^^n) wc wc.
Proof.
  induction n.
  - constructor.
  - cbn [lpow].
    eapply segRLs_trans.
    + apply rule_h_C, rules.
    + exact IHn.
Qed.

Lemma packet_u_A a b :
  segRLs tm (packet At a b) (packet At (2*a) (2*b+1)) wa wa.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_A a) (rule_u_A rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_A b)) as H2.
  repeat rewrite app_assoc in H2.
  replace (2*b+1) with (1+2*b) by lia.
  rewrite lpow_add. cbn [lpow].
  repeat rewrite app_assoc.
  repeat rewrite app_nil_r.
  exact H2.
Qed.

Lemma packet_p_A a b :
  segRLs tm (packet P100 a b) (packet At (2*a) b) wa wc.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_A a) (rule_p_A rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_C b)) as H2.
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_q_A a b :
  segRLs tm (packet P110 a b) (packet At (2*a+1) b) wa wb.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_A a) (rule_q_A rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_B b)) as H2.
  repeat rewrite app_assoc in H2.
  rewrite lpow_add. cbn [lpow].
  repeat rewrite app_nil_r.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_u_B a b :
  segRLs tm (packet At a b) (packet P100 a (2*b)) wb wa.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_B a) (rule_u_B rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_A b)) as H2.
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_p_B a b :
  segRLs tm (packet P100 a (S b)) (packet P100 a b) wb wc.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_B a) (rule_p_B rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_C b)) as H2.
  cbn [lpow].
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_q_B a b :
  segRLs tm (packet P110 a (S b)) (packet P110 a b) wb wb.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_B a) (rule_q_B rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_B b)) as H2.
  cbn [lpow].
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_u_C a b :
  segRLs tm (packet At a b) (packet P110 a (2*b)) wc wa.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_C a) (rule_u_C rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_A b)) as H2.
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_p_C a b :
  segRLs tm (packet P100 a (S b)) (packet P110 a b) wc wc.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_C a) (rule_p_C rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_C b)) as H2.
  cbn [lpow].
  repeat rewrite app_assoc in H2.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma packet_q_C a b :
  segRLs tm (packet P110 a (S b)) (packet P100 (S a) b) wc wb.
Proof.
  unfold packet,particle_heads.
  epose proof (segRLs_trans (hashes_C a) (rule_q_C rules)) as H1.
  epose proof (segRLs_trans H1 (hashes_B b)) as H2.
  repeat rewrite app_assoc in H2.
  replace (S a) with (a+1) by lia.
  rewrite lpow_add. cbn [lpow].
  repeat rewrite app_nil_r.
  repeat rewrite app_assoc.
  exact H2.
Qed.

Lemma hash_Bs_edge n :
  sideRLs tm hh (columns_side (copies ColB n))
    (columns_side (copies ColB (S n))).
Proof.
  induction n.
  - cbn [columns_side copies]. apply rule_h_edge, rules.
  - cbn [columns_side copies].
    eapply segRLs_sideRLs_concat.
    + apply rule_h_B, rules.
    + exact IHn.
Qed.

Lemma hashes_Bs n k :
  sideRLs tm (hh^^k) (columns_side (copies ColB n))
    (columns_side (copies ColB (n+k))).
Proof.
  induction k.
  - cbn [lpow]. replace (n+0) with n by lia. apply sideRLseq_O.
  - epose proof (sideRLs_trans IHk (hash_Bs_edge (n+k))) as H.
    replace (S k) with (k+1) by lia.
    rewrite lpow_add. cbn [lpow]. rewrite app_nil_r.
    replace (n+(k+1)) with (S (n+k)) by lia.
    exact H.
Qed.

Lemma hashes_edge n :
  sideRLs tm (hh^^n) 0inf (columns_side (copies ColB n)).
Proof.
  change 0inf with (columns_side (copies ColB 0)).
  replace n with (0+n) at 2 by lia.
  apply hashes_Bs.
Qed.

Lemma packet_p0_Bs_edge a b :
  a <= b ->
  sideRLs tm (packet P100 0 b) (columns_side (copies ColB a))
    (columns_side (copies ColC a ++ copies ColB (b+2-a))).
Proof.
  revert b. induction a; intros b Hab.
  - cbn [packet particle_heads columns_side copies].
    epose proof (sideRLs_trans (rule_p_edge rules) (hashes_Bs 2 b)) as H.
    cbn [lpow] in H. repeat rewrite app_nil_r in H.
    replace (b+2-0) with (2+b) by lia.
    exact H.
  - destruct b; [lia|].
    cbn [copies columns_side].
    eapply segRLs_sideRLs_concat.
    + apply packet_p_B.
    + replace (S b+2-S a) with (b+2-a) by lia.
      apply IHa. lia.
Qed.

Lemma packet_p_edge_spec a b :
  a <= b ->
  sideRLs tm (packet P100 a b) 0inf
    (columns_side (copies ColC a ++ copies ColB (b+2-a))).
Proof.
  intros Hab.
  eapply sideRLs_trans.
  - apply hashes_edge.
  - apply packet_p0_Bs_edge. exact Hab.
Qed.

Lemma hashes_qbase b :
  sideRLs tm (hh^^b)
    (wa*>(if extra then wc*>wb*>0inf else wb*>0inf))
    (columns_side (ColA::qtail extra (2*b+1))).
Proof.
  destruct extra; cbn [qtail columns_side].
  - eapply segRLs_sideRLs_concat.
    + apply hashes_A.
    + eapply segRLs_sideRLs_concat.
      * apply hashes_C.
      * replace (2*b+1) with (1+2*b) by lia.
        change (wb*>0inf) with (columns_side (copies ColB 1)).
        apply hashes_Bs.
  - eapply segRLs_sideRLs_concat.
    + apply hashes_A.
    + replace (2*b+1) with (1+2*b) by lia.
      change (wb*>0inf) with (columns_side (copies ColB 1)).
      apply hashes_Bs.
Qed.

Lemma packet_q0_Bs_edge a b :
  a <= b ->
  sideRLs tm (packet P110 0 b) (columns_side (copies ColB a))
    (columns_side
      (copies ColB a ++ ColA::qtail extra (2*(b-a)+1))).
Proof.
  revert b. induction a; intros b Hab.
  - replace (b-0) with b by lia.
    cbn [copies columns_side].
    unfold packet,particle_heads. cbn [lpow].
    repeat rewrite app_nil_r.
    epose proof (sideRLs_trans (rule_q_edge rules) (hashes_qbase b)) as H.
    cbn [lpow] in H. repeat rewrite app_nil_r in H.
    exact H.
  - destruct b; [lia|].
    cbn [copies columns_side].
    eapply segRLs_sideRLs_concat.
    + apply packet_q_B.
    + replace (S b-S a) with (b-a) by lia.
      apply IHa. lia.
Qed.

Lemma packet_q_edge_spec a b :
  a <= b ->
  sideRLs tm (packet P110 a b) 0inf
    (columns_side
      (copies ColB a ++ ColA::qtail extra (2*(b-a)+1))).
Proof.
  intros Hab.
  eapply sideRLs_trans.
  - apply hashes_edge.
  - apply packet_q0_Bs_edge. exact Hab.
Qed.

Lemma packet_u0_Bs_edge a b :
  1 <= a -> a <= 2*b+1 ->
  sideRLs tm (packet At 0 b) (columns_side (copies ColB a))
    (columns_side
      (ColA::copies ColC (a-1) ++ copies ColB (2*b+3-a))).
Proof.
  destruct a; intros; [lia|].
  cbn [copies columns_side].
  eapply segRLs_sideRLs_concat.
  - apply packet_u_B.
  - replace (S a-1) with a by lia.
    replace (2*b+3-S a) with (2*b+2-a) by lia.
    apply packet_p0_Bs_edge. lia.
Qed.

Lemma packet_u_edge_spec a b :
  1 <= a -> a <= 2*b+1 ->
  sideRLs tm (packet At a b) 0inf
    (columns_side
      (ColA::copies ColC (a-1) ++ copies ColB (2*b+3-a))).
Proof.
  intros Ha Hab.
  eapply sideRLs_trans.
  - apply hashes_edge.
  - apply packet_u0_Bs_edge; assumption.
Qed.

Lemma Returns_spec p a b r r' :
  Returns extra p a b r r' ->
  sideRLs tm (packet p a b) (columns_side r) (columns_side r').
Proof.
  intro H. induction H; cbn [columns_side column_word] in *.
  - eapply segRLs_sideRLs_concat; [apply packet_u_A|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_p_A|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_q_A|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_u_B|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_p_B|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_q_B|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_u_C|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_p_C|exact IHReturns].
  - eapply segRLs_sideRLs_concat; [apply packet_q_C|exact IHReturns].
  - apply packet_u_edge_spec; assumption.
  - apply packet_p_edge_spec; assumption.
  - apply packet_q_edge_spec; assumption.
Qed.

End MachineSoundness.


Section GenericNonhalt.

Variable tm : TM.
Variable extra : bool.
Variable hR hL : DH0.
Variable hh hp hq : list (DH0*DH0).
Variable wa wb wc : list Sym.
Variable rules : MacroRules tm extra [(hR,hL)] hh hp hq wa wb wc.
Variable lhs : side.

Notation cols := (columns_side wa wb wc).

Definition MacroState (r : list Column) :=
  lhs {{{ (hR,R) }}} cols r.

Hypothesis left_restart : forall r,
  lhs {{{ (hL,L) }}} r -[tm]->*
  lhs {{{ (hR,R) }}} r.

Lemma Returns_BigStep r r' :
  Returns extra At 0 0 r r' ->
  MacroState r -[tm]->+ MacroState r'.
Proof.
  intros H.
  eapply Returns_spec with
    (tm:=tm) (hu:=[(hR,hL)]) (hh:=hh) (hp:=hp) (hq:=hq)
    (wa:=wa) (wb:=wb) (wc:=wc) in H.
  cbn [packet particle_heads lpow] in H.
  repeat rewrite app_nil_r in H.
  eapply sideRLs_1 in H.
  unfold MacroState.
  follow10 H.
  apply left_restart.
  exact rules.
Qed.

Lemma macro_nonhalt initial :
  (exists r', Returns extra At 0 0 initial r') ->
  ~halts tm (MacroState initial).
Proof.
  intros Hinitial.
  eapply progress_nonhalt_cond with
    (P:=fun r => exists r', Returns extra At 0 0 r r').
  - intros r [r' Hr].
    destruct (Returns_At_closed extra 0 r r' Hr) as [r'' Hr'].
    exists r'. split.
    + apply Returns_BigStep. exact Hr.
    + exists r''. exact Hr'.
  - exact Hinitial.
Qed.

End GenericNonhalt.


Module TM10c0.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RD---").

Notation hL := (B,<[0;0]).
Notation hR := (A,<[0;0;1;0]).
Notation hh := [((D,<[0;0]),hL)].
Notation hp := [((A,<[0;0;1;1;1]),hL)].
Notation hq := [((D,<[0;0;1;1;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).

Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm false [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.

Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->*
  lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.

Lemma init : c0 -[tm]->* S [ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.

Lemma macro_nonhalt_c0 : ~halts tm (S [ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=false) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_B.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - apply init.
  - apply macro_nonhalt_c0.
Qed.

End TM10c0.


Module TM10c1.

Definition tm := Eval compute in (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RC_0RD---").
Notation hL := (B,<[0;0]).
Notation hR := (A,<[0;0;1;0]).
Notation hh := [((D,<[0;0]),hL)].
Notation hp := [((A,<[0;0;1;1;1]),hL)].
Notation hq := [((D,<[0;0;1;1;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).
Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm false [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.
Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->* lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.
Lemma init : c0 -[tm]->* S [ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.
Lemma macro_nonhalt_c1 : ~halts tm (S [ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=false) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_B.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init|apply macro_nonhalt_c1]. Qed.

End TM10c1.


Module TM10c2.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_0RD---").
Notation hL := (B,<[0;0]).
Notation hR := (A,<[0;0;1;0]).
Notation hh := [((D,<[0;0]),hL)].
Notation hp := [((A,<[0;0;1;1;1]),hL)].
Notation hq := [((D,<[0;0;1;1;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).
Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm false [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.
Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->* lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.
Lemma init : c0 -[tm]->* S [ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.
Lemma macro_nonhalt_c2 : ~halts tm (S [ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=false) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_B.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init|apply macro_nonhalt_c2]. Qed.

End TM10c2.


Module TM10d.

Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA0RF_0RB---").
Notation hL := (B,<[0;0]).
Notation hR := (A,<[0;0;1;0]).
Notation hh := [((D,<[0;0]),hL)].
Notation hp := [((A,<[0;0;1;1;1]),hL)].
Notation hq := [((B,<[0;0;1;0;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).
Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm true [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.
Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->* lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.
Lemma init : c0 -[tm]->* S [ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.
Lemma macro_nonhalt_d : ~halts tm (S [ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=true) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_B.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init|apply macro_nonhalt_d]. Qed.

End TM10d.


Module TM10e.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0RA---").
Notation hL := (A,<[0;0]).
Notation hR := (D,<[0;0;1;0]).
Notation hh := [((C,<[0;0]),hL)].
Notation hp := [((D,<[0;0;1;1;1]),hL)].
Notation hq := [((A,<[0;0;1;0;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).
Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm true [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.
Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->* lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.
Lemma init : c0 -[tm]->* S [ColA;ColC;ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.
Lemma macro_nonhalt_e : ~halts tm (S [ColA;ColC;ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=true) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColA;ColC;ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_ACB.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init|apply macro_nonhalt_e]. Qed.

End TM10e.


Module TM10f.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0LA---").
Notation hL := (A,<[0;0]).
Notation hR := (D,<[0;0;1;0]).
Notation hh := [((C,<[0;0]),hL)].
Notation hp := [((D,<[0;0;1;1;1]),hL)].
Notation hq := [((C,<[0;0;1;1;0]),hL)].
Notation wa := [1;0;1;0].
Notation wb := [1;0;0;0;0].
Notation wc := [1;0;0;1;0].
Notation lhs := (0inf<*<[1;0;1;0]).
Definition S r := MacroState hR wa wb wc lhs r.

Lemma rules : MacroRules tm false [(hR,hL)] hh hp hq wa wb wc.
Proof. constructor; cbn; esc. Qed.
Lemma left_restart r :
  lhs {{{ (hL,L) }}} r -[tm]->* lhs {{{ (hR,R) }}} r.
Proof. esx. Qed.
Lemma init : c0 -[tm]->* S [ColA;ColC;ColB].
Proof. unfold S,MacroState,columns_side,column_word; esx. Qed.
Lemma macro_nonhalt_f : ~halts tm (S [ColA;ColC;ColB]).
Proof.
  eapply macro_nonhalt with
    (tm:=tm) (extra:=false) (hR:=hR) (hL:=hL)
    (hh:=hh) (hp:=hp) (hq:=hq) (wa:=wa) (wb:=wb) (wc:=wc)
    (lhs:=lhs) (initial:=[ColA;ColC;ColB]).
  - exact rules.
  - exact left_restart.
  - eexists. apply Returns_init_ACB.
Qed.
Theorem nonhalt : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply init|apply macro_nonhalt_f]. Qed.

End TM10f.


