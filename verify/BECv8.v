From BusyCoq Require Import Individual62 Longitudinal DivModCases ES_v3.
Require Import Lia Arith String List.

Open Scope list.
Open Scope nat.
Open Scope sym.

Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RC1RD_0RE0LD_1RA0RF_1RE---").

Notation hp := (((F,<[0]),(C,[1])) : DH0*DH0).
Notation ha := (((F,<[0;0]),(C,[1])) : DH0*DH0).
Notation hc := (((A,<[1]),(B,[0])) : DH0*DH0).
Notation hcp := (((A,<[1]),(D,[0])) : DH0*DH0).

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=1000); reflexivity).

Lemma p01: segRLs tm [hp] [hp] [0;1] [0;1]. Proof. esc. Qed.
Lemma a01: segRLs tm [ha] [hp;ha] [0;1] [0;1]. Proof. esc. Qed.
Lemma p00a: segRLs tm [hp] [hc] [0;0] [0;0]. Proof. esc. Qed.
Lemma p00b: segRLs tm [hp] [hcp] [0;0] [0;1]. Proof. esc. Qed.
Lemma c00: segRLs tm [hc] [] [0;0] [1;0]. Proof. esc. Qed.
Lemma c10: segRLs tm [hc] [hc] [1;0] [0;0]. Proof. esc. Qed.
Lemma cp10: segRLs tm [hcp] [hcp] [1;0] [0;0]. Proof. esc. Qed.
Lemma a00: segRLs tm [ha] [hc;hc] [0;0] [0;1;0]. Proof. esc. Qed.
Lemma c01: segRLs tm [hc] [] [0;1] [1;1]. Proof. esc. Qed.
Lemma cp11: segRLs tm [hcp] [hp] [1;1] [0;0]. Proof. esc. Qed.

Lemma boundary0:
  sideRLs tm [ha] ([0;0;1;1] *> 0inf)
    ([0;1;0;1;0;0;0;0;0;1] *> 0inf).
Proof. esc. Qed.

Lemma boundaryS k:
  sideRLs tm [ha]
    ([0;0;1] *> ([0;1]^^(S k) *> ([1] *> 0inf)))
    ([0;1;0;1;0;0;0;1] *> ([0;0]^^k *> ([0;1] *> 0inf))).
Proof.
  change (S k) with (1+k).
  es' k.
Qed.

Inductive bit := B0 | B1.

Fixpoint high (r:list bit) : side :=
  match r with
  | [] => 0inf
  | B0::r => [0;0] *> high r
  | B1::r => [0;1] *> high r
  end.

Fixpoint low (r:list bit) : side :=
  match r with
  | [] => 0inf
  | B0::r => [0;0] *> low r
  | B1::r => [1;0] *> low r
  end.

Fixpoint ones (r:list bit) : nat :=
  match r with
  | [] => 0
  | B0::r => ones r
  | B1::r => S (ones r)
  end.

Definition canonical (a:nat) (r:list bit) : side :=
  [0;1]^^a *> high r.

Inductive inc : list bit -> list bit -> Prop :=
| inc_nil: inc [] [B1]
| inc_0 r: inc (B0::r) (B1::r)
| inc_1 r r': inc r r' -> inc (B1::r) (B0::r').

(* Canonical positive little-endian representations.  This relation does not
   admit redundant zeroes above the highest one.  The
   right-suffix transducer can therefore split on its three genuine cases:
   the final [B1], a [B0] column, or a non-final [B1] column. *)
Inductive pvalue : nat -> list bit -> Prop :=
| pv_one: pvalue 1 [B1]
| pv_0 n r: pvalue n r -> pvalue (2*n) (B0::r)
| pv_1 n r: pvalue n r -> pvalue (1+2*n) (B1::r).

Lemma inc_exists r: exists r', inc r r'.
Proof.
  induction r as [|[|] r IH].
  - exists [B1]; constructor.
  - exists (B1::r); constructor.
  - destruct IH as [r' Hr']; exists (B0::r'); constructor; exact Hr'.
Qed.

Lemma pvalue_inc n r r':
  pvalue n r -> inc r r' -> pvalue (S n) r'.
Proof.
  intros Hv; revert r'.
  induction Hv; intros r' Hi; inversion Hi; subst.
  - inversion H0; subst.
    replace (S 1) with (2*1) by lia. apply pv_0,pv_one.
  - replace (S (2*n)) with (1+2*n) by lia. apply pv_1; exact Hv.
  - replace (S (1+2*n)) with (2*S n) by lia.
    apply pv_0, IHHv; assumption.
Qed.

Lemma pvalue_exists (n:nat):
  n <> 0%nat -> exists r, pvalue n r.
Proof.
  induction n using lt_wf_ind; intros Hnz.
  destruct n; [contradiction|].
  destruct (mod2 n) as [k|k]; subst.
  - destruct k.
    + exists [B1]; constructor.
    + destruct (H (S k) ltac:(lia) ltac:(lia)) as [r Hr].
      exists (B1::r).
      replace (S (S k*2)) with (1+2*S k) by lia.
      constructor; exact Hr.
  - destruct (H (S k) ltac:(lia) ltac:(lia)) as [r Hr].
    exists (B0::r).
    replace (S (1+k*2)) with (2*S k) by lia.
    constructor; exact Hr.
Qed.

Lemma pvalue_pos n r: pvalue n r -> 0 < n.
Proof. intros H; induction H; lia. Qed.

Lemma pvalue_unique (n:nat) r r':
  pvalue n r -> pvalue n r' -> r = r'.
Proof.
  intros H; revert r'.
  induction H; intros r' H'; inversion H'; subst; try reflexivity.
  all: try match goal with
    | Hpos : pvalue ?k ?r |- _ =>
        pose proof (pvalue_pos _ _ Hpos); lia
    end.
  all: assert (n0 = n) by lia; subst n0; f_equal; apply IHpvalue; assumption.
Qed.

Lemma pvalue_pred (n:nat) r:
  0%nat < n -> pvalue (S n) r ->
  exists r', pvalue n r' /\ inc r' r.
Proof.
  intros Hn Hr.
  destruct (pvalue_exists n ltac:(lia)) as [r' Hr'].
  destruct (inc_exists r') as [r'' Hi].
  assert (Hv: pvalue (S n) r'') by (eapply pvalue_inc; eassumption).
  replace r'' with r in * by (eapply pvalue_unique; eassumption).
  exists r'; split; assumption.
Qed.

Inductive incs : nat -> list bit -> list bit -> Prop :=
| incs_0 r: incs 0 r r
| incs_S n r r1 r2: inc r r1 -> incs n r1 r2 -> incs (S n) r r2.

Lemma incs_exists n r: exists r', incs n r r'.
Proof.
  revert r; induction n; intros r.
  - exists r; constructor.
  - destruct (inc_exists r) as [r1 H1].
    destruct (IHn r1) as [r2 H2].
    exists r2; econstructor; eauto.
Qed.

Lemma pvalue_incs k n r r':
  pvalue n r -> incs k r r' -> pvalue (n+k) r'.
Proof.
  intros Hv Hi; revert n Hv.
  induction Hi; intros n0 Hv.
  - replace (n0+0) with n0 by lia; exact Hv.
  - replace (n0+S n) with (S n0+n) by lia.
    apply IHHi. eapply pvalue_inc; eassumption.
Qed.

Lemma hash_end: sideRLs tm [hc] 0inf ([1;0] *> 0inf).
Proof.
  exact (BoundedConfig.sideRLs_c_spec tm [hc] [] [1;0] 1000 eq_refl).
Qed.

Lemma hash_inc r r':
  inc r r' -> sideRLs tm [hc] (low r) (low r').
Proof.
  intros H; induction H; cbn[low].
  - exact hash_end.
  - eapply segRLs_sideRLs_concat; [exact c00|constructor].
  - eapply segRLs_sideRLs_concat; [exact c10|exact IHinc].
Qed.

Lemma hash_inc2 r r1 r2:
  inc r r1 -> inc r1 r2 ->
  sideRLs tm [hc;hc] (low r) (low r2).
Proof.
  intros H1 H2.
  change (sideRLs tm ([hc]++[hc]) (low r) (low r2)).
  eapply sideRLs_trans; [apply hash_inc,H1|apply hash_inc,H2].
Qed.

Lemma percent_even p r r':
  inc r r' ->
  sideRLs tm [hp]
    ([0;1]^^p *> low (B0::r))
    ([0;1]^^p *> low (B0::r')).
Proof.
  intros Hi; induction p; cbn[lpow low].
  - eapply @segRLs_sideRLs_concat with (w1:=[0;0]) (w2:=[0;0]);
      [exact p00a|apply hash_inc,Hi].
  - eapply @segRLs_sideRLs_concat with (w1:=[0;1]) (w2:=[0;1]);
      [exact p01|exact IHp].
Qed.

Lemma at_even p r r':
  incs (p+2) r r' ->
  sideRLs tm [ha]
    ([0;1]^^p *> low (B0::r))
    ([0;1]^^p *> [0;1;0] *> low r').
Proof.
  revert r r'; induction p; intros r r' Hinc; cbn[lpow low] in *.
  - inversion Hinc as [|n0 r0 r1 r2 H1 Htail]; subst.
    inversion Htail as [|n1 r3 r4 r5 H2 Hzero]; subst.
    inversion Hzero; subst.
    eapply @segRLs_sideRLs_concat with (w1:=[0;0]) (w2:=[0;1;0]);
      [exact a00|].
    eapply hash_inc2; eassumption.
  - inversion Hinc as [|n0 r0 r1 r2 H1 Htail]; subst.
    eapply @segRLs_sideRLs_concat with (w1:=[0;1]) (w2:=[0;1]);
      [exact a01|].
    change (sideRLs tm ([hp]++[ha])
      ([0;1]^^p *> low (B0::r))
      ([0;1]^^p *> [0;1;0] *> low r')).
    eapply sideRLs_trans.
    + apply percent_even; exact H1.
    + apply IHp. exact Htail.
Qed.

Lemma shift_low_high r:
  [0] *> low r = high r.
Proof.
  induction r as [|[|] r IH].
  - cbn[low high]. solve_const0_eq.
  - cbn[low high].
    change ([0;0] *> ([0] *> low r) = [0;0] *> high r).
    f_equal. exact IH.
  - cbn[low high].
    change ([0;1] *> ([0] *> low r) = [0;1] *> high r).
    f_equal. exact IH.
Qed.

Lemma reword r:
  [0;1;0] *> low r = [0;1] *> high r.
Proof.
  change ([0;1] *> ([0] *> low r) = [0;1] *> high r).
  f_equal. apply shift_low_high.
Qed.

Lemma at_normal p r r':
  incs (p+2) r r' ->
  sideRLs tm [ha]
    ([0;1]^^p *> low (B0::r))
    ([0;1]^^(S p) *> high r').
Proof.
  intros H.
  pose proof (at_even _ _ _ H) as Hr.
  replace ([0;1]^^S p *> high r')
    with ([0;1]^^p *> [0;1] *> high r').
  2: replace (S p) with (p+1) by lia; rewrite lpow_add,Str_app_assoc; reflexivity.
  rewrite <-reword. exact Hr.
Qed.

Lemma hp_wall p:
  segRLs tm ([hp]^^p) ([hp]^^p) [0;1] [0;1].
Proof. apply segRLs_wall'',p01. Qed.

Lemma percent_end:
  sideRLs tm [hp] 0inf ([0;0;1;0] *> 0inf).
Proof.
  exact (BoundedConfig.sideRLs_c_spec tm [hp] [] [0;0;1;0] 1000 eq_refl).
Qed.

(* A suffix-level presentation of the same table.  A cell records both
   tracks, so [C00,C01,C10,C11] mean [00,01,10,11].  [receives s r r']
   says that the suffix [r] receives one complete signal [s] and returns as
   [r'].  The two [%/00] constructors retain exactly the rule-table
   ambiguity; no backward rule is built into this relation. *)
Inductive signal := SigP | SigC | SigD.
Inductive cell := C00 | C01 | C10 | C11.

Fixpoint cells_side (r:list cell) : side :=
  match r with
  | [] => 0inf
  | C00::r => [0;0] *> cells_side r
  | C01::r => [0;1] *> cells_side r
  | C10::r => [1;0] *> cells_side r
  | C11::r => [1;1] *> cells_side r
  end.

Definition signal_head s :=
  match s with SigP => hp | SigC => hc | SigD => hcp end.

Inductive receives : signal -> list cell -> list cell -> Prop :=
| recv_C_end:
    receives SigC [] [C10]
| recv_C_00 r:
    receives SigC (C00::r) (C10::r)
| recv_C_10 r r':
    receives SigC r r' ->
    receives SigC (C10::r) (C00::r')
| recv_C_01 r:
    receives SigC (C01::r) (C11::r)
| recv_P_end:
    receives SigP [] [C00;C10]
| recv_P_01 r r':
    receives SigP r r' ->
    receives SigP (C01::r) (C01::r')
| recv_P_00_C r r':
    receives SigC r r' ->
    receives SigP (C00::r) (C00::r')
| recv_P_00_D r r':
    receives SigD r r' ->
    receives SigP (C00::r) (C01::r')
| recv_D_10 r r':
    receives SigD r r' ->
    receives SigD (C10::r) (C00::r')
| recv_D_11 r r':
    receives SigP r r' ->
    receives SigD (C11::r) (C00::r').

Lemma receives_spec s r r':
  receives s r r' ->
  sideRLs tm [signal_head s] (cells_side r) (cells_side r').
Proof.
  intros H; induction H; cbn[cells_side signal_head] in *.
  - exact hash_end.
  - eapply segRLs_sideRLs_concat; [exact c00|constructor].
  - eapply segRLs_sideRLs_concat; [exact c10|exact IHreceives].
  - eapply segRLs_sideRLs_concat; [exact c01|constructor].
  - exact percent_end.
  - eapply segRLs_sideRLs_concat; [exact p01|exact IHreceives].
  - eapply segRLs_sideRLs_concat; [exact p00a|exact IHreceives].
  - eapply segRLs_sideRLs_concat; [exact p00b|exact IHreceives].
  - eapply segRLs_sideRLs_concat; [exact cp10|exact IHreceives].
  - eapply segRLs_sideRLs_concat; [exact cp11|exact IHreceives].
Qed.

Inductive receivesPs : nat -> list cell -> list cell -> Prop :=
| recv_Ps_0 r: receivesPs 0 r r
| recv_Ps_S n r r1 r2:
    receives SigP r r1 -> receivesPs n r1 r2 ->
    receivesPs (S n) r r2.

Lemma receivesPs_spec n r r':
  receivesPs n r r' ->
  sideRLs tm ([hp]^^n) (cells_side r) (cells_side r').
Proof.
  intros H; induction H; cbn[lpow].
  - constructor.
  - change (sideRLs tm ([hp]++[hp]^^n) (cells_side r) (cells_side r2)).
    eapply sideRLs_trans.
    + exact (receives_spec SigP r r1 H).
    + exact IHreceivesPs.
Qed.

Fixpoint high_cells (r:list bit) : list cell :=
  match r with
  | [] => []
  | B0::r => C00::high_cells r
  | B1::r => C01::high_cells r
  end.

Lemma high_cells_spec r: cells_side (high_cells r) = high r.
Proof. induction r as [|[|] r IH]; cbn[high_cells cells_side high]; congruence. Qed.

(* The lookahead convention is executable.  A percent first tries the plain
   carry; precisely when that carry cannot return, it tries the collision
   branch.  All recursive calls inspect a proper suffix, including the
   percent restarted by [#'/11]. *)
Fixpoint receiveC (r:list cell) : option (list cell) :=
  match r with
  | [] => Some [C10]
  | C00::r => Some (C10::r)
  | C01::r => Some (C11::r)
  | C10::r =>
      match receiveC r with Some r' => Some (C00::r') | None => None end
  | C11::_ => None
  end
with receiveD (r:list cell) : option (list cell) :=
  match r with
  | C10::r =>
      match receiveD r with Some r' => Some (C00::r') | None => None end
  | C11::r =>
      match receiveP r with Some r' => Some (C00::r') | None => None end
  | _ => None
  end
with receiveP (r:list cell) : option (list cell) :=
  match r with
  | [] => Some [C00;C10]
  | C01::r =>
      match receiveP r with Some r' => Some (C01::r') | None => None end
  | C00::r =>
      match receiveC r with
      | Some r' => Some (C00::r')
      | None =>
          match receiveD r with Some r' => Some (C01::r') | None => None end
      end
  | _ => None
  end.

Lemma receive_functions_sound r:
  (forall r', receiveC r = Some r' -> receives SigC r r') /\
  (forall r', receiveD r = Some r' -> receives SigD r r') /\
  (forall r', receiveP r = Some r' -> receives SigP r r').
Proof.
  induction r as [|c r [IHC [IHD IHP]]].
  - repeat split; intros r' E; cbn[receiveC receiveD receiveP] in E;
      inversion E; constructor.
  - destruct c; cbn[receiveC receiveD receiveP].
    + repeat split; intros r' E; try discriminate.
      * inversion E; constructor.
      * destruct (receiveC r) as [r0|] eqn:E0.
        -- inversion E; subst. apply recv_P_00_C. apply IHC. reflexivity.
        -- destruct (receiveD r) as [r0|] eqn:E1; try discriminate.
           inversion E; subst. apply recv_P_00_D. apply IHD. reflexivity.
    + repeat split; intros r' E; try discriminate.
      * inversion E; constructor.
      * destruct (receiveP r) as [r0|] eqn:E0; try discriminate.
        inversion E; subst. apply recv_P_01. apply IHP. reflexivity.
    + repeat split; intros r' E; try discriminate.
      * destruct (receiveC r) as [r0|] eqn:E0; try discriminate.
        inversion E; subst. apply recv_C_10. apply IHC. reflexivity.
      * destruct (receiveD r) as [r0|] eqn:E0; try discriminate.
        inversion E; subst. apply recv_D_10. apply IHD. reflexivity.
    + repeat split; intros r' E; try discriminate.
      destruct (receiveP r) as [r0|] eqn:E0; try discriminate.
      inversion E; subst. apply recv_D_11. apply IHP. reflexivity.
Qed.

Lemma receiveP_sound r r':
  receiveP r = Some r' -> receives SigP r r'.
Proof. apply (proj2 (proj2 (receive_functions_sound r))). Qed.

Fixpoint receivePs (n:nat) (r:list cell) : option (list cell) :=
  match n with
  | O => Some r
  | S n =>
      match receiveP r with Some r' => receivePs n r' | None => None end
  end.

Lemma receivePs_sound n r r':
  receivePs n r = Some r' -> receivesPs n r r'.
Proof.
  revert r r'; induction n; intros r r2 E; cbn[receivePs] in E.
  - inversion E; constructor.
  - destruct (receiveP r) as [r1|] eqn:E1; try discriminate.
    econstructor; [apply receiveP_sound,E1|apply IHn,E].
Qed.

Lemma receivePs_add a b r r1 r2:
  receivePs a r = Some r1 ->
  receivePs b r1 = Some r2 ->
  receivePs (a+b) r = Some r2.
Proof.
  revert r r1 r2; induction a; intros r r1 r2 E1 E2.
  - cbn[receivePs] in E1; inversion E1; subst; exact E2.
  - cbn[receivePs] in E1.
    destruct (receiveP r) as [u|] eqn:Eu; try discriminate.
    replace (S a+b) with (S (a+b)) by lia.
    cbn[receivePs]. rewrite Eu.
    eapply IHa; eassumption.
Qed.

(* [twice_phase p r s] says that [s] is [r] with one [C00] inserted after
   exactly [p] leading [C01] columns.  This is the relative phase between a
   percent stream and its doubled stream. *)
Inductive twice_phase : nat -> list cell -> list cell -> Prop :=
| twice_phase_0 r: twice_phase 0 r (C00::r)
| twice_phase_S p r s:
    twice_phase p r s -> twice_phase (S p) (C01::r) (C01::s).

Lemma twice_phase_seed r: twice_phase 0 r (C00::r).
Proof. constructor. Qed.

Lemma receivePs_C01 n r r':
  receivePs n r = Some r' ->
  receivePs n (C01::r) = Some (C01::r').
Proof.
  revert r r'; induction n; intros r r' E.
  - cbn[receivePs] in *; inversion E; reflexivity.
  - cbn[receivePs] in *.
    destruct (receiveP r) as [u|] eqn:Eu; try discriminate.
    apply IHn in E.
    cbn[receiveP]. rewrite Eu. exact E.
Qed.

Fixpoint leading01 (r:list cell) : nat :=
  match r with C01::r => S (leading01 r) | _ => 0 end.

Lemma leading01_C01s p r:
  leading01 ((C01::nil)^^p ++ r) = p + leading01 r.
Proof.
  induction p.
  - reflexivity.
  - change
      (S (leading01 ((C01::nil)^^p ++ r)) = S p + leading01 r).
    rewrite IHp. lia.
Qed.

Lemma twice_phase_leading p r s:
  twice_phase p r s -> p <= leading01 r.
Proof. intros H; induction H; cbn[leading01]; lia. Qed.

Lemma receiveD_leading r r':
  receiveD r = Some r' -> leading01 r' = 0%nat.
Proof.
  destruct r as [|c r]; [discriminate|].
  destruct c; cbn[receiveD]; try discriminate.
  - destruct (receiveD r) as [u|]; try discriminate.
    intros E; inversion E; reflexivity.
  - destruct (receiveP r) as [u|]; try discriminate.
    intros E; inversion E; reflexivity.
Qed.

Lemma receiveP_leading r r':
  receiveP r = Some r' -> leading01 r' <= S (leading01 r).
Proof.
  revert r'; induction r as [|c r IH]; intros r' E.
  - cbn[receiveP] in E; inversion E; subst; cbn[leading01]; lia.
  - destruct c; cbn[receiveP leading01] in E.
    + destruct (receiveC r) as [u|] eqn:EC.
      * inversion E; subst; cbn[leading01]; lia.
      * destruct (receiveD r) as [u|] eqn:ED; try discriminate.
        pose proof (receiveD_leading _ _ ED).
        inversion E; subst; cbn[leading01]; lia.
    + destruct (receiveP r) as [u|] eqn:EP; try discriminate.
      inversion E; subst. cbn[leading01]. specialize (IH _ eq_refl). lia.
    + discriminate.
    + discriminate.
Qed.

Lemma receivePs_leading n r r':
  receivePs n r = Some r' -> leading01 r' <= n + leading01 r.
Proof.
  revert r r'; induction n; intros r r' E.
  - cbn[receivePs] in E; inversion E; lia.
  - cbn[receivePs] in E.
    destruct (receiveP r) as [u|] eqn:Eu; try discriminate.
    pose proof (receiveP_leading _ _ Eu).
    pose proof (IHn _ _ E). lia.
Qed.

Lemma receivePs2_inv r r':
  receivePs 2 r = Some r' ->
  exists r1, receiveP r = Some r1 /\ receiveP r1 = Some r'.
Proof.
  cbn[receivePs].
  destruct (receiveP r) as [r1|] eqn:E1; try discriminate.
  destruct (receiveP r1) as [r2|] eqn:E2; try discriminate.
  intros E; inversion E; subst. exists r1; auto.
Qed.

Lemma twice_phase_step_rank p r s r':
  twice_phase p r s ->
  receiveP r = Some r' ->
  exists p' s', receivePs 2 s = Some s' /\
    twice_phase p' r' s' /\
    Nat.min (S p) (leading01 r') <= p'.
Proof.
  intros Hphase; revert r'.
  induction Hphase; intros r' E.
  - destruct r as [|c r].
    + cbn[receiveP receiveC receiveD receivePs] in E.
      inversion E; subst.
      exists 0%nat,[C00;C00;C10]; repeat split; constructor.
    + destruct c; cbn[receiveP] in E.
      * destruct (receiveC r) as [u|] eqn:EC.
        -- inversion E; subst. exists 0%nat,(C00::C00::u).
           repeat split; cbn[receivePs receiveP receiveC leading01];
             try rewrite EC; try constructor; reflexivity.
        -- destruct (receiveD r) as [u|] eqn:ED; try discriminate.
           inversion E; subst. exists 1%nat,(C01::C00::u).
           repeat split; cbn[receivePs receiveP receiveC receiveD leading01];
             try rewrite EC,ED; try constructor; try reflexivity.
           constructor.
      * destruct (receiveP r) as [u|] eqn:EP; try discriminate.
        inversion E; subst. exists 1%nat,(C01::C00::u).
        repeat split; cbn[receivePs receiveP receiveC receiveD leading01];
          try rewrite EP; try constructor; try reflexivity.
        constructor.
      * discriminate.
      * discriminate.
  - cbn[receiveP] in E.
    destruct (receiveP r) as [u|] eqn:Er; try discriminate.
    inversion E; subst.
    destruct (IHHphase _ eq_refl) as (p'&s'&Es'&Hphase'&Hrank).
    exists (S p'),(C01::s'); repeat split.
    + apply receivePs_C01; exact Es'.
    + constructor; exact Hphase'.
    + cbn[leading01].
      destruct (le_dec (S (S p)) (S (leading01 u))).
      * rewrite Nat.min_l by lia; lia.
      * rewrite Nat.min_r by lia; lia.
Qed.

Lemma twice_phase_steps_rank n p r s r':
  twice_phase p r s ->
  receivePs n r = Some r' ->
  exists p' s', receivePs (2*n) s = Some s' /\
    twice_phase p' r' s' /\
    Nat.min (p+n) (leading01 r') <= p'.
Proof.
  revert p r s r'; induction n; intros p r s r' Hphase E.
  - cbn[receivePs] in E; inversion E; subst.
    exists p,s; repeat split; try exact Hphase.
    pose proof (twice_phase_leading _ _ _ Hphase) as Hlead.
    rewrite Nat.add_0_r, Nat.min_l by exact Hlead. exact (Nat.le_refl p).
  - cbn[receivePs] in E.
    destruct (receiveP r) as [r1|] eqn:E1; try discriminate.
    destruct (twice_phase_step_rank _ _ _ _ Hphase E1)
      as (p1&s1&Es1&Hphase1&Hrank1).
    destruct (IHn _ _ _ _ Hphase1 E) as (p2&s2&Es2&Hphase2&Hrank2).
    exists p2,s2; repeat split; try exact Hphase2.
    + replace (2*S n) with (2+2*n) by lia.
      destruct (receivePs2_inv _ _ Es1) as (sa&Ea&Eb).
      change
        (match receiveP s with
         | Some x =>
             match receiveP x with
             | Some y => receivePs (2*n) y
             | None => None
             end
         | None => None
         end = Some s2).
      rewrite Ea,Eb. exact Es2.
    + apply Nat.le_trans with (Nat.min (p1+n) (leading01 r')).
      2: exact Hrank2.
      apply Nat.min_glb.
      * destruct (le_dec (S p) (leading01 r1)) as [Hle|Hgt].
        -- assert (S p <= p1) by
             (apply Nat.le_trans with (Nat.min (S p) (leading01 r1));
              [rewrite Nat.min_l by exact Hle; reflexivity|exact Hrank1]).
           destruct (le_dec (p+S n) (leading01 r')) as [Hm|Hm].
           ++ rewrite Nat.min_l by exact Hm. lia.
           ++ rewrite Nat.min_r by lia.
              pose proof (receivePs_leading _ _ _ E). lia.
        -- assert (Hp1: p1 = leading01 r1).
           { pose proof (twice_phase_leading _ _ _ Hphase1).
             assert (leading01 r1 <= p1) by
               (apply Nat.le_trans with (Nat.min (S p) (leading01 r1));
                [rewrite Nat.min_r by lia; reflexivity|exact Hrank1]).
             lia. }
           pose proof (receivePs_leading _ _ _ E). lia.
      * destruct (le_dec (p+S n) (leading01 r')) as [Hm|Hm].
        -- rewrite Nat.min_l by exact Hm; exact Hm.
        -- rewrite Nat.min_r by lia; exact (Nat.le_refl _).
Qed.

Fixpoint low_cells (r:list bit) : list cell :=
  match r with
  | [] => []
  | B0::r => C00::low_cells r
  | B1::r => C10::low_cells r
  end.

Lemma low_cells_spec r: cells_side (low_cells r) = low r.
Proof. induction r as [|[|] r IH]; cbn[low_cells cells_side low]; congruence. Qed.

Definition normal_cells p r := (C01::nil)^^p ++ C00::low_cells r.

Lemma cells_side_C01s p r:
  cells_side ((C01::nil)^^p ++ r) = [0;1]^^p *> cells_side r.
Proof.
  induction p.
  - reflexivity.
  - change
      ([0;1] *> cells_side ((C01::nil)^^p ++ r) =
       [0;1] *> ([0;1]^^p *> cells_side r)).
    rewrite IHp. reflexivity.
Qed.

Lemma normal_cells_spec p r:
  cells_side (normal_cells p r) = [0;1]^^p *> low (B0::r).
Proof.
  unfold normal_cells.
  rewrite cells_side_C01s.
  cbn[cells_side low]. rewrite low_cells_spec. reflexivity.
Qed.

Lemma twice_phase_normal_unique p r p' s:
  p <= p' ->
  twice_phase p' (normal_cells p r) s ->
  p' = p /\ s = normal_cells p (B0::r).
Proof.
  revert p' s; induction p; intros p' s Hle Hphase.
  - destruct p'; [|cbn[normal_cells lpow] in Hphase; inversion Hphase].
    split; [reflexivity|].
    inversion Hphase; subst. reflexivity.
  - destruct p' as [|p']; [lia|].
    cbn[normal_cells lpow] in Hphase.
    inversion Hphase; subst.
    assert (Hp: p <= p') by lia.
    destruct (IHp _ _ Hp H1) as [-> ->].
    split; reflexivity.
Qed.

Lemma receivePs_double_normal n p q r s t:
  q <= p+n ->
  twice_phase p r s ->
  receivePs n r = Some (normal_cells q t) ->
  receivePs (2*n) s = Some (normal_cells q (B0::t)).
Proof.
  intros Hq Hphase E.
  destruct (twice_phase_steps_rank _ _ _ _ _ Hphase E)
    as (p'&s'&Es'&Hphase'&Hrank).
  assert (Elead: leading01 (normal_cells q t) = q).
  { unfold normal_cells. rewrite leading01_C01s.
    cbn[leading01]. lia. }
  rewrite Elead in Hrank.
  assert (Hp': q <= p') by (rewrite Nat.min_r in Hrank by lia; exact Hrank).
  destruct (twice_phase_normal_unique _ _ _ _ Hp' Hphase') as [-> ->].
  exact Es'.
Qed.

Lemma receiveC_low_cells r r':
  inc r r' -> receiveC (low_cells r) = Some (low_cells r').
Proof.
  intros H; induction H; cbn[low_cells receiveC]; try reflexivity.
  rewrite IHinc. reflexivity.
Qed.

Lemma receiveP_normal p r r':
  inc r r' ->
  receiveP (normal_cells p r) = Some (normal_cells p r').
Proof.
  intros Hinc; unfold normal_cells.
  induction p.
  - change
      (receiveP (C00::low_cells r) = Some (C00::low_cells r')).
    cbn[receiveP]. rewrite (receiveC_low_cells _ _ Hinc). reflexivity.
  - change
      (receiveP (C01::((C01::nil)^^p ++ C00::low_cells r)) =
       Some (C01::((C01::nil)^^p ++ C00::low_cells r'))).
    cbn[receiveP]. rewrite IHp. reflexivity.
Qed.

Lemma pvalue_ones_le n r:
  pvalue n r -> ones r <= n.
Proof. intros H; induction H; cbn[ones]; lia. Qed.

Lemma pvalue_ones_lt n r:
  pvalue n r -> 1 < n -> ones r < n.
Proof.
  intros H; induction H; cbn[ones]; intros; try lia.
  all: try (pose proof (pvalue_ones_le _ _ H); lia).
Qed.

Lemma receivePs_empty n r:
  pvalue n r -> receivePs n [] = Some (normal_cells 0 r).
Proof.
  revert r; induction n using lt_wf_ind; intros r Hv.
  destruct n.
  - pose proof (pvalue_pos _ _ Hv); lia.
  - destruct n.
    + replace r with [B1] by (eapply pvalue_unique; [constructor|exact Hv]).
      reflexivity.
    + destruct (pvalue_pred (S n) r ltac:(lia) Hv) as (u&Hu&Hi).
      specialize (H (S n) ltac:(lia) u Hu).
      replace (S (S n)) with (S n+1) by lia.
      eapply receivePs_add with (r1:=normal_cells 0 u).
      * exact H.
      * cbn[receivePs]. rewrite (receiveP_normal _ _ _ Hi). reflexivity.
Qed.

Lemma receivePs_C01_exact n r r':
  receivePs n r = Some r' ->
  receivePs n (C01::r) = Some (C01::r').
Proof. apply receivePs_C01. Qed.

Lemma normalize_ge n r:
  pvalue n r -> forall m t,
  pvalue m t -> n <= m ->
  receivePs m (high_cells r) = Some (normal_cells (ones r) t).
Proof.
  intros Hn; induction Hn; intros m t Hm Hle.
  - cbn[high_cells ones].
    apply receivePs_C01_exact,receivePs_empty; exact Hm.
  - remember (2*n) as twice eqn:Evalue.
    revert Evalue Hle.
    inversion Hm; subst; intros Evalue Hle.
    + pose proof (pvalue_pos _ _ Hn); lia.
    + assert (Hnm: n <= n0) by lia.
      specialize (IHHn _ _ H Hnm).
      cbn[high_cells ones].
      eapply receivePs_double_normal with (p:=0%nat) (n:=n0).
      * pose proof (pvalue_ones_le _ _ Hn); lia.
      * constructor.
      * exact IHHn.
    + assert (Hnm: n <= n0) by lia.
      specialize (IHHn _ _ H Hnm).
      cbn[high_cells ones].
      assert (Heven:
        receivePs (2*n0) (C00::high_cells r) =
          Some (normal_cells (ones r) (B0::r0))).
      { eapply receivePs_double_normal with (p:=0%nat) (n:=n0).
        - pose proof (pvalue_ones_le _ _ Hn); lia.
        - constructor.
        - exact IHHn. }
      replace (1+2*n0) with (2*n0+1) by lia.
      eapply receivePs_add with (r1:=normal_cells (ones r) (B0::r0)).
      * exact Heven.
      * cbn[receivePs].
        rewrite (receiveP_normal _ _ _ (inc_0 r0)). reflexivity.
  - cbn[high_cells ones].
    apply receivePs_C01_exact.
    eapply IHHn.
    + exact Hm.
    + lia.
Qed.

Inductive unarybits : nat -> list bit -> Prop :=
| unarybits_one: unarybits 0 [B1]
| unarybits_zero k r:
    unarybits k r -> unarybits (S k) (B0::r).

Lemma unarybits_value k r:
  unarybits k r -> pvalue (2^k) r.
Proof.
  intros H; induction H.
  - cbn; constructor.
  - cbn[Nat.pow]. apply pv_0; exact IHunarybits.
Qed.

Lemma pvalue_power n r:
  pvalue n r ->
  (exists k, unarybits k r) \/
  exists t, pvalue (n-1) t /\
    receivePs (n-1) (high_cells r) = Some (normal_cells (ones r) t).
Proof.
  intros H; induction H.
  - left; exists 0%nat; constructor.
  - destruct IHpvalue as [(k&Hpow)|(t&Hm&Hnorm)].
    + left; exists (S k); constructor; exact Hpow.
    + right; exists (B1::t); split.
      * replace (2*n-1) with (1+2*(n-1)) by
          (pose proof (pvalue_pos _ _ H); lia).
        constructor; exact Hm.
      * cbn[high_cells ones].
        replace (2*n-1) with (2*(n-1)+1) by
          (pose proof (pvalue_pos _ _ H); lia).
        eapply receivePs_add with
          (r1:=normal_cells (ones r) (B0::t)).
        -- eapply receivePs_double_normal with (p:=0%nat) (n:=n-1).
           ++ match goal with
              | Hv : pvalue (n-1) _ |- _ =>
                  pose proof (pvalue_pos _ _ Hv);
                  pose proof (pvalue_ones_lt _ _ H ltac:(lia)); lia
              end.
           ++ constructor.
           ++ exact Hnorm.
        -- cbn[receivePs].
           rewrite (receiveP_normal _ _ _ (inc_0 t)). reflexivity.
  - right.
    exists (B0::r); split.
    + replace (1+2*n-1) with (2*n) by lia.
      constructor; exact H.
    + cbn[high_cells ones]. apply receivePs_C01_exact.
      replace (1+2*n-1) with (2*n) by lia.
      apply normalize_ge with (n:=n).
      * exact H.
      * constructor; exact H.
      * lia.
Qed.

Lemma power_ones k r:
  unarybits k r -> ones r = 1%nat.
Proof. intros H; induction H; cbn[ones]; auto. Qed.

Lemma power_high k r:
  unarybits k r -> high r = [0;0]^^k *> ([0;1] *> 0inf).
Proof.
  intros H; induction H; cbn[high lpow].
  - reflexivity.
  - rewrite IHunarybits. reflexivity.
Qed.

Fixpoint bits_value (r:list bit) : nat :=
  match r with
  | [] => 0
  | B0::r => 2 * bits_value r
  | B1::r => 1 + 2 * bits_value r
  end.

Lemma pvalue_bits_value n r:
  pvalue n r -> n = bits_value r.
Proof. intros H; induction H; cbn[bits_value]; lia. Qed.

Lemma pvalue_index_unique n m r:
  pvalue n r -> pvalue m r -> n = m.
Proof.
  intros Hn Hm.
  pose proof (pvalue_bits_value _ _ Hn).
  pose proof (pvalue_bits_value _ _ Hm). lia.
Qed.

Definition power_end k : list cell :=
  match k with
  | O => [C01]
  | S k => C00 :: (C10::nil)^^k ++ [C11]
  end.

Lemma power_end_leading k:
  leading01 (power_end (S k)) = 0%nat.
Proof. reflexivity. Qed.

Lemma receiveP_power_end k:
  receiveP (C00::power_end (S k)) = Some (power_end (S (S k))).
Proof. cbn[power_end receiveP receiveC lpow]. reflexivity. Qed.

(* The exceptional suffixes are exactly the powers of two.  After all but
   the final input percent they expose one finite boundary word.  This is
   the closed signal-stream formula for that word, indexed by its width. *)
Lemma receivePs_power k r:
  unarybits k r ->
  receivePs (2^k-1) (high_cells r) = Some (power_end k).
Proof.
  intros H; induction H.
  - reflexivity.
  - destruct k as [|k].
    + inversion H; subst; reflexivity.
    + destruct (twice_phase_steps_rank (2^(S k)-1) 0
        (high_cells r) (C00::high_cells r) (power_end (S k))
        (twice_phase_seed _) IHunarybits)
        as (p&s&Es&Hphase&Hrank).
      rewrite power_end_leading in Hrank.
      assert (Hp: p = 0%nat).
      { pose proof (twice_phase_leading _ _ _ Hphase).
        rewrite power_end_leading in H0. lia. }
      subst p; inversion Hphase; subst s.
      replace (2^(S (S k))-1) with (2*(2^(S k)-1)+1) by
        (cbn[Nat.pow]; lia).
      eapply receivePs_add with (r1:=C00::power_end (S k)).
      * exact Es.
      * cbn[receivePs]. rewrite receiveP_power_end. reflexivity.
Qed.

Lemma power_middle_side k:
  cells_side ((C10::nil)^^k ++ [C11]) =
    [1] *> ([0;1]^^k *> ([1] *> 0inf)).
Proof.
  induction k.
  - reflexivity.
  - change
      ([1;0] *> cells_side ((C10::nil)^^k ++ [C11]) =
       [1] *> ([0;1] *> ([0;1]^^k *> ([1] *> 0inf)))).
    rewrite IHk. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma power_end_side k:
  cells_side (power_end (S k)) =
    [0;0;1] *> ([0;1]^^k *> ([1] *> 0inf)).
Proof.
  cbn[power_end cells_side]. rewrite power_middle_side.
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma power0:
  sideRLs tm [ha] ([0;1] *> 0inf)
    ([0;1;0;1;0;1;0;1] *> 0inf).
Proof. esc. Qed.

Definition unary_bits k : list bit := (B0::nil)^^k ++ [B1].

Lemma unary_bits_spec k: unarybits k (unary_bits k).
Proof.
  induction k.
  - constructor.
  - cbn[unary_bits lpow] in *. constructor; exact IHk.
Qed.

Definition plus2_bits k : list bit := B0::B1::unary_bits k.

Lemma plus2_bits_value k:
  pvalue (2^(S (S k))+2) (plus2_bits k).
Proof.
  unfold plus2_bits.
  replace (2^(S (S k))+2) with (2*(1+2*(2^k))) by
    (cbn[Nat.pow]; lia).
  apply pv_0,pv_1,unarybits_value,unary_bits_spec.
Qed.

Lemma plus2_bits_high k:
  [0;1]^^2 *> high (plus2_bits k) =
  [0;1;0;1;0;0;0;1] *> ([0;0]^^k *> ([0;1] *> 0inf)).
Proof.
  unfold plus2_bits. cbn[high lpow].
  rewrite (power_high _ _ (unary_bits_spec k)).
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma percent_power_boundary k r:
  unarybits (S k) r ->
  sideRLs tm ([hp]^^(2^(S k)-1)) (high r)
    ([0;0;1] *> ([0;1]^^k *> ([1] *> 0inf))).
Proof.
  intros H.
  pose proof (receivesPs_spec _ _ _
    (receivePs_sound _ _ _ (receivePs_power _ _ H))) as Hr.
  rewrite high_cells_spec,power_end_side in Hr. exact Hr.
Qed.

(* The main transducer lemma.  Its proof is developed below from
   the percent/hash rules; the statement deliberately uses the non-maximal
   split 01^a H(a+1), which removes the v2 rewording case from the invariant. *)
Lemma right_step a r:
  pvalue (S a) r ->
  exists q r',
    q = ones r /\
    pvalue (S (a+q+1)) r' /\
    sideRLs tm (([hp]^^a)++[ha]) (high r)
      ([0;1]^^(S q) *> high r').
Proof.
  intros Hv.
  destruct (pvalue_power _ _ Hv) as [(k&Hpow)|(t&Hpred&Hnorm)].
  - assert (Hnum: S a = 2^k).
    { eapply pvalue_index_unique; [exact Hv|apply unarybits_value,Hpow]. }
    assert (Hones: ones r = 1%nat) by (apply power_ones with k; exact Hpow).
    destruct k as [|k].
    + inversion Hpow; subst r.
      assert (Ha: a = 0%nat) by (cbn[Nat.pow] in Hnum; lia).
      subst a. exists 1%nat,[B1;B1]; repeat split; try reflexivity.
      * replace (S (0+1+1)) with (1+2*1) by lia.
        apply pv_1,pv_one.
      * cbn[lpow high]. exact power0.
    + destruct k as [|k].
      * assert (Ha: a = 1%nat) by (cbn[Nat.pow] in Hnum; lia).
        subst a. exists 1%nat,[B0;B0;B1]; split.
        -- symmetry; exact Hones.
        -- split.
           ++ replace (S (1+1+1)) with (2*(2*1)) by lia.
              apply pv_0,pv_0,pv_one.
           ++ change (sideRLs tm (([hp]^^1)++[ha]) (high r)
                ([0;1]^^2 *> high [B0;B0;B1])).
              eapply sideRLs_trans.
              ** exact (percent_power_boundary 0 r Hpow).
              ** applys_eq boundary0; repeat rewrite Str_app_assoc; reflexivity.
      * assert (Ha: a = 2^(S (S k))-1) by lia.
        exists 1%nat,(plus2_bits k); split.
        -- symmetry; exact Hones.
        -- split.
           ++ replace (S (a+1+1)) with (2^(S (S k))+2) by lia.
              apply plus2_bits_value.
           ++ replace a with (2^(S (S k))-1) by (symmetry; exact Ha).
              eapply sideRLs_trans.
              ** exact (percent_power_boundary (S k) r Hpow).
              ** rewrite plus2_bits_high. apply boundaryS.
  - destruct (incs_exists (ones r+2) t) as [r' Hincs].
    exists (ones r),r'; repeat split; try reflexivity.
    + replace (S (a+ones r+1)) with (a+(ones r+2)) by lia.
      apply pvalue_incs with (r:=t).
      * replace a with (S a-1) by lia. exact Hpred.
      * exact Hincs.
    + pose proof (receivesPs_spec _ _ _
        (receivePs_sound _ _ _ Hnorm)) as Hpercent.
      rewrite high_cells_spec,normal_cells_spec in Hpercent.
      eapply sideRLs_trans.
      * replace a with (S a-1) by lia. exact Hpercent.
      * apply at_normal. exact Hincs.
Qed.

Lemma pass_percent_at q:
  segRLs tm ([hp]^^q++[ha]) ([hp]^^(S q)++[ha])
    [0;1] [0;1].
Proof.
  pose proof (segRLs_trans (hp_wall q) a01) as H.
  applys_eq H; unfold DH0.
  replace (S q) with (q+1) by lia.
  rewrite lpow_add. cbn[lpow]. rewrite app_nil_r,<-app_assoc. reflexivity.
Qed.

Lemma unary_columns q a:
  segRLs tm ([hp]^^q++[ha]) ([hp]^^(q+a)++[ha])
    ([0;1]^^a) ([0;1]^^a).
Proof.
  revert q; induction a; intros q.
  - cbn[lpow]. replace (q+0) with q by lia. apply segRLs_nil.
  - replace (S a) with (1+a) by lia.
    rewrite lpow_add.
    eapply segRLs_concat.
    + apply pass_percent_at.
    + pose proof (IHa (S q)) as H.
      applys_eq H; unfold DH0.
      * replace (q+(1+a)) with (S q+a) by lia.
        replace (S q) with (q+1) by lia.
        repeat rewrite lpow_add. cbn[lpow].
        repeat rewrite app_nil_r. repeat rewrite <-app_assoc. reflexivity.
Qed.

Definition lhs : side := (0inf <* <[1]).
Definition State (a:nat) (r:list bit) :=
  lhs {{{ (fst ha,R) }}} canonical a r.

Lemma left_restart r:
  lhs {{{ (snd ha,L) }}} r -[tm]->*
  lhs {{{ (fst ha,R) }}} r.
Proof. esx. Qed.

Lemma BigStep a r q r':
  q = ones r ->
  pvalue (Datatypes.S (a+q+1)) r' ->
  sideRLs tm (([hp]^^a)++[ha]) (high r)
    ([0;1]^^(Datatypes.S q) *> high r') ->
  State a r -[tm]->+ State (a+q+1) r'.
Proof.
  intros Hq Hv Hright.
  pose proof (unary_columns 0 a) as Hleft.
  cbn[lpow] in Hleft.
  eapply @segRLs_sideRLs_concat with
    (r1:=high r) (r2:=[0;1]^^S q *> high r') in Hleft.
  2: exact Hright.
  eapply sideRLs_1 in Hleft.
  unfold State,canonical.
  assert (Etape:
    [0;1]^^a *> [0;1]^^S q *> high r' =
    [0;1]^^(a+q+1) *> high r').
  {
    replace (a+q+1) with (a+S q) by lia.
    rewrite lpow_add,Str_app_assoc. reflexivity.
  }
  eapply progress_evstep_trans; [exact Hleft|].
  rewrite <-Etape.
  apply left_restart.
Qed.

Inductive good : nat * list bit -> Prop :=
| good_intro a r: pvalue (S a) r -> good (a,r).

Lemma good_step x:
  good x -> exists y,
    State (fst x) (snd x) -[tm]->+ State (fst y) (snd y) /\ good y.
Proof.
  intros H; destruct H as [a r Hv].
  destruct (right_step _ _ Hv) as (q&r'&Hq&Hv'&Hr).
  exists (a+q+1,r'); split.
  - eapply BigStep; eassumption.
  - constructor; exact Hv'.
Qed.

Definition initial_bits := [B0;B1].
Definition start := lhs {{{ (snd ha,L) }}} canonical 1%nat initial_bits.

Lemma seed: good (1%nat,initial_bits).
Proof.
  constructor. cbn[initial_bits].
  change (pvalue (2*1) [B0;B1]).
  apply pv_0,pv_one.
Qed.

Lemma init: start -[tm]->* State 1%nat initial_bits.
Proof. unfold start,State. apply left_restart. Qed.

Lemma macro_nonhalt: ~halts tm (State 1%nat initial_bits).
Proof.
  eapply (progress_nonhalt_cond tm (nat*list bit)%type
    (1%nat,initial_bits)
    (fun x => State (fst x) (snd x)) good).
  - intros x Hx. apply good_step,Hx.
  - exact seed.
Qed.

Theorem nonhalt: ~halts tm start.
Proof. eapply multistep_nonhalt; [exact init|exact macro_nonhalt]. Qed.

Print Assumptions nonhalt.

