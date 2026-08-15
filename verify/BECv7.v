From BusyCoq Require Import Individual62 Longitudinal DivModCases ES_v3.
Require Import ZifyNat Lia ZArith String List.

Open Scope list.
Open Scope nat.
Open Scope sym.

Lemma lpow_pair {A} (x:A) k:
  [x]^^(2*k) = [x;x]^^k.
Proof.
  induction k.
  - reflexivity.
  - replace (2*S k) with (2+2*k) by lia.
    rewrite lpow_add,IHk.
    reflexivity.
Qed.

Inductive RD := LD | D0 | D1.
Inductive HM := hE | hJ | hA | hC | hX | hY.
Notation head := (DH0*DH0)%type.

(* The two numeric fields are deliberately distinct.  In hX, [p] counts the
   11B carry heads to the left of 11Bx/01E and [q] counts the 01B heads to its
   right.  They may only be joined after the separating heads disappear. *)
Inductive RIncs : HM -> nat -> nat -> list RD -> list RD -> Prop :=
| RI_E_L q r r':
    RIncs hE 0 (S q) r r' ->
    RIncs hE 0 q (LD::r) (LD::r')
| RI_E_0 q r r':
    RIncs hJ 0 (S q) r r' ->
    RIncs hE 0 q (D0::r) (LD::r')
| RI_E_1 q r r':
    RIncs hA 0 q r r' ->
    RIncs hE 0 q (D1::r) (LD::r')

| RI_J_L q r r':
    RIncs hE 0 q r r' ->
    RIncs hJ 0 q (LD::r) (LD::r')
| RI_J_0 q r r':
    RIncs hJ 0 q r r' ->
    RIncs hJ 0 q (D0::r) (LD::r')
| RI_J_1 q r r':
    RIncs hA 0 q r r' ->
    RIncs hJ 0 (S q) (D1::r) (LD::r')

| RI_A_L q r r':
    RIncs hE 0 q r r' ->
    RIncs hA 0 q (LD::r) (LD::r')
| RI_A_1 q r r':
    RIncs hA 0 q r r' ->
    RIncs hA 0 (S q) (D1::r) (LD::r')
| RI_A_0_short0 k r r':
    RIncs hC k 0 r r' ->
    RIncs hA 0 (2+k*2) (D0::r) (D0::r')
| RI_A_0_short1 k r r':
    RIncs hC k 0 r r' ->
    RIncs hA 0 (3+k*2) (D0::r) (D1::r')
| RI_A_0_long k i r r':
    RIncs hX i k r r' ->
    RIncs hA 0 (4+k+i*2) (D0::r) (LD::r')
| RI_A_0_longx k r r':
    RIncs hY 0 k r r' ->
    RIncs hA 0 (2+k) (D0::r) (LD::r')

| RI_C_0_0 k r r':
    RIncs hC k 0 r r' ->
    RIncs hC (2+k*2) 0 (D0::r) (D0::r')
| RI_C_0_1 k r r':
    RIncs hC k 0 r r' ->
    RIncs hC (3+k*2) 0 (D0::r) (D1::r')

| RI_X_0_0 q r r':
    RIncs hY 0 (S q) r r' ->
    RIncs hX 1 q (D0::r) (LD::r')
| RI_X_0_1 p q r r':
    RIncs hX p (S q) r r' ->
    RIncs hX (3+p*2) q (D0::r) (LD::r')

| RI_Y_L q r r':
    RIncs hE 0 (S q) r r' ->
    RIncs hY 0 q (LD::r) (LD::r')
| RI_Y_1 q r r':
    RIncs hA 0 q r r' ->
    RIncs hY 0 q (D1::r) (LD::r')

| RI_A_rh0: RIncs hA 0 0 [] [D0;D1]
| RI_A_rh1: RIncs hA 0 1 [] [D1;D1]
| RI_A_rh_0 k r':
    RIncs hA 0 k [] r' ->
    RIncs hA 0 (2+k*2) [] (D0::r')
| RI_A_rh_1 k r':
    RIncs hA 0 k [] r' ->
    RIncs hA 0 (3+k*2) [] (D1::r').


(* The closure proof is mutually strengthened over all six modes.  In
   particular its hX clause quantifies over both [p] and [q]; do not replace
   it by a one-parameter lemma. *)

Fixpoint toRC (r:list RD) : side :=
  match r with
  | [] => 0inf
  | LD::r => [1;1;0] *> toRC r
  | D0::r => [0;0;0] *> toRC r
  | D1::r => [1;0;0] *> toRC r
  end.

Definition mode_heads
    (he hj ha hc hy hb h11b h11bx h01e:head)
    (tp:HM) (p q:nat) : list head :=
  match tp with
  | hE => [he] ++ [hb]^^q
  | hJ => [hj] ++ [hb]^^q
  | hA => [ha] ++ [hb]^^q
  | hC => [hc] ++ [h11b]^^p
  | hX => [hc] ++ [h11b]^^p ++ [h11bx;h01e] ++ [hb]^^q
  | hY => [hy;h01e] ++ [hb]^^q
  end.

(* [tail n r] is the canonical little-endian binary tail for [n+2].
   The two base cases are written separately because every canonical tail
   ends in [D1]. *)
Inductive tail : nat -> list RD -> Prop :=
| tail_0: tail 0 [D0;D1]
| tail_1: tail 1 [D1;D1]
| tail_even k r: tail k r -> tail (2+k*2) (D0::r)
| tail_odd k r: tail k r -> tail (3+k*2) (D1::r).

Lemma tail_nonempty n r: tail n r -> r <> [].
Proof. intros H E; destruct H; congruence. Qed.

(* [route n r c b] records the carry head used while crossing the initial
   D0-run of [r].  [None] means Y; [Some p] means X with exactly [p] 11B
   heads to the left of 11Bx/01E.  The last index is the minimum right-hand
   01B budget. *)
Inductive route : nat -> list RD -> option nat -> nat -> Prop :=
| route_0: route 0 [D0;D1] (Some (1%nat)) 0
| route_1: route 1 [D1;D1] None 1
| route_odd k r:
    tail k r -> route (3+k*2) (D1::r) None (2*k+2)
| route_even_Y k r b:
    route k r None b ->
    route (2+k*2) (D0::r) (Some (1%nat)) (Nat.pred b)
| route_even_X k r p b:
    route k r (Some p) b ->
    route (2+k*2) (D0::r) (Some ((3+p*2)%nat)) (Nat.pred b).

Lemma tail_route n r: tail n r -> exists c b, route n r c b.
Proof.
  intros H; induction H.
  - exists (Some (1%nat)),(0%nat); constructor.
  - exists (None:option nat),(1%nat); constructor.
  - destruct IHtail as ([p|]&b&Hroute).
    + exists (Some ((3+p*2)%nat)),(Nat.pred b); econstructor; eauto.
    + exists (Some (1%nat)),(Nat.pred b); econstructor; eauto.
  - exists (None:option nat),(2*k+2); econstructor; eauto.
Qed.

Lemma route_X_bound n r p b:
  route n r (Some p) b -> p <= 2*n+1.
Proof.
  intros H.
  remember (Some p) as c eqn:E in H.
  revert p E.
  induction H; intros p0 E; inversion E; subst; cbn in *.
  - lia.
  - lia.
  - specialize (IHroute p eq_refl); lia.
Qed.

Lemma route_cost_bound n r c b:
  route n r c b ->
  match c with
  | None => 2+b <= 4*n+6
  | Some p => 4+2*p+b <= 4*n+6
  end.
Proof.
  intros H; induction H; cbn in *.
  - lia.
  - lia.
  - lia.
  - lia.
  - pose proof (route_X_bound _ _ _ _ H) as B.
    cbn in *; lia.
Qed.

Lemma tail_exists n: exists r, tail n r.
Proof.
  induction n using lt_wf_ind.
  destruct n as [|[|n]].
  - exists [D0;D1]; constructor.
  - exists [D1;D1]; constructor.
  - destruct (mod2 n) as [k|k]; subst.
    + destruct (H k) as [r Hr]; [lia|].
      exists (D0::r); constructor; exact Hr.
    + destruct (H k) as [r Hr]; [lia|].
      exists (D1::r); constructor; exact Hr.
Qed.

Lemma tail_at_right n r:
  tail n r -> RIncs hA 0 n [] r.
Proof.
  intros H; induction H; econstructor; eauto.
Qed.

Definition A_complete (n:nat) : Prop :=
  forall r q, tail n r -> 2*n+2 <= q ->
  exists m r',
    tail m r' /\
    RIncs hA 0 q r ([LD]^^length r ++ r') /\
    m < q + length r.

Definition route_run (c:option nat) (b:nat) (r r':list RD) : Prop :=
  match c with
  | None => RIncs hY 0 b r r'
  | Some p => RIncs hX p b r r'
  end.

Lemma route_spec n r c b:
  route n r c b ->
  (forall k, k<n -> A_complete k) ->
  forall d, b <= d ->
  exists m r',
    tail m r' /\
    route_run c d r ([LD]^^length r ++ r') /\
    m < d + length r + 1.
Proof.
  intros Hr HA.
  induction Hr; intros d Hd; cbn[route_run] in *.
  - destruct (tail_exists (S d)) as [r' Htail].
    exists (S d),r'; repeat split; try exact Htail.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Htail).
    + cbn; lia.
  - destruct d as [|d]; [lia|].
    destruct (tail_exists d) as [r' Htail].
    exists d,r'; repeat split; try exact Htail.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Htail).
    + cbn; lia.
  - specialize (HA k ltac:(lia) r d H ltac:(lia)).
    destruct HA as (m&r'&Htail&Hrun&Hbound).
    exists m,r'; repeat split; try exact Htail.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn; lia.
  - assert (HA': forall k0, k0 < k -> A_complete k0).
    { intros k0 Hk; apply HA; lia. }
    specialize (IHHr HA' (S d) ltac:(lia)).
    destruct IHHr as (m&r'&Htail&Hrun&Hbound).
    exists m,r'; repeat split; try exact Htail.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
  - assert (HA': forall k0, k0 < k -> A_complete k0).
    { intros k0 Hk; apply HA; lia. }
    specialize (IHHr HA' (S d) ltac:(lia)).
    destruct IHHr as (m&r'&Htail&Hrun&Hbound).
    exists m,r'; repeat split; try exact Htail.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
Qed.

Lemma A_complete_all n: A_complete n.
Proof.
  induction n using lt_wf_ind.
  unfold A_complete.
  intros r q Htail Hq.
  inversion Htail as [| |k r0 Htail0|k r0 Htail0]; subst.
  - assert (E: q = 2+(q-2)) by lia.
    rewrite E.
    destruct (tail_exists (q-2)) as [r' Hr'].
    exists (q-2),r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - assert (E: q = 2+(q-2)) by lia.
    rewrite E.
    destruct (tail_exists (q-2)) as [r' Hr'].
    exists (q-2),r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - destruct (tail_route _ _ Htail0) as ([p|]&b&Hroute).
    + pose proof (route_cost_bound _ _ _ _ Hroute) as Hcost.
      assert (E: q = 4+(q-(4+2*p))+2*p) by (cbn in Hcost; lia).
      pose proof (route_spec _ _ _ _ Hroute
        (fun k0 Hk => H k0 ltac:(lia))
        (q-(4+2*p)) ltac:(cbn in Hcost; lia)) as Hrun.
      destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
      exists m,r'; repeat split; try exact Hr'.
      * cbn[route_run] in Hrun.
        rewrite E.
        change (RIncs hA 0 (4+(q-(4+2*p))+2*p) (D0::r0)
          (LD :: ([LD]^^length r0 ++ r'))).
        replace (4+(q-(4+2*p))+2*p)
          with (4+(q-(4+2*p))+p*2) by lia.
        apply RI_A_0_long. exact Hrun.
      * cbn in *; lia.
    + pose proof (route_cost_bound _ _ _ _ Hroute) as Hcost.
      assert (E: q = 2+(q-2)) by lia.
      pose proof (route_spec _ _ _ _ Hroute
        (fun k0 Hk => H k0 ltac:(lia))
        (q-2) ltac:(cbn in Hcost; lia)) as Hrun.
      destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
      exists m,r'; repeat split; try exact Hr'.
      * cbn[route_run] in Hrun.
        rewrite E.
        change (RIncs hA 0 (2+(q-2)) (D0::r0)
          (LD :: ([LD]^^length r0 ++ r'))).
        apply RI_A_0_longx. exact Hrun.
      * cbn in *; lia.
  - destruct q as [|q0]; [lia|].
    pose proof (H k ltac:(lia) r0 q0 Htail0 ltac:(lia)) as Hrun.
    destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
    exists m,r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
Qed.

Definition J_complete (n:nat) : Prop :=
  forall r q, tail n r -> 2*n+1 <= q ->
  exists m r',
    tail m r' /\
    RIncs hJ 0 q r ([LD]^^length r ++ r') /\
    m < q + length r.

Lemma J_complete_all n: J_complete n.
Proof.
  induction n using lt_wf_ind.
  unfold J_complete.
  intros r q Htail Hq.
  inversion Htail as [| |k r0 Htail0|k r0 Htail0]; subst.
  - destruct q as [|q0]; [lia|].
    destruct (tail_exists q0) as [r' Hr'].
    exists q0,r'; repeat split; try exact Hr'.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - destruct q as [|[|q0]]; [lia|lia|].
    destruct (tail_exists q0) as [r' Hr'].
    exists q0,r'; repeat split; try exact Hr'.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - pose proof (H k ltac:(lia) r0 q Htail0 ltac:(lia)) as Hrun.
    destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
    exists m,r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
  - destruct q as [|q0]; [lia|].
    pose proof (A_complete_all k r0 q0 Htail0 ltac:(lia)) as Hrun.
    destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
    exists m,r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
Qed.

Definition E_complete (n:nat) : Prop :=
  forall r q, tail n r -> n <= q ->
  exists m r',
    tail m r' /\
    RIncs hE 0 q r ([LD]^^length r ++ r') /\
    m < q + length r.

Lemma E_complete_all n: E_complete n.
Proof.
  unfold E_complete.
  intros r q Htail Hq.
  inversion Htail as [| |k r0 Htail0|k r0 Htail0]; subst.
  - destruct (tail_exists q) as [r' Hr'].
    exists q,r'; repeat split; try exact Hr'.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - destruct q as [|q0]; [lia|].
    destruct (tail_exists q0) as [r' Hr'].
    exists q0,r'; repeat split; try exact Hr'.
    + cbn[lpow]. repeat econstructor. exact (tail_at_right _ _ Hr').
    + cbn; lia.
  - pose proof (J_complete_all k r0 (S q) Htail0 ltac:(lia)) as Hrun.
    destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
    exists m,r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
  - pose proof (A_complete_all k r0 q Htail0 ltac:(lia)) as Hrun.
    destruct Hrun as (m&r'&Hr'&Hrun&Hbound).
    exists m,r'; repeat split; try exact Hr'.
    + cbn[lpow]. econstructor. exact Hrun.
    + cbn in *; lia.
Qed.

Lemma E_L_prefix p a r r':
  RIncs hE 0 (p+a) r r' ->
  RIncs hE 0 p ([LD]^^a ++ r) ([LD]^^a ++ r').
Proof.
  revert p; induction a; intros p Hrun.
  - cbn; replace (p+0) with p in Hrun by lia; exact Hrun.
  - cbn[lpow]. apply RI_E_L.
    apply IHa.
    replace (S p+a) with (p+S a) by lia.
    exact Hrun.
Qed.

Inductive canonical : list RD -> Prop :=
| canonical_intro a n r:
    tail n r -> n<a -> canonical ([LD]^^a ++ r).

Lemma canonical_step r:
  canonical r -> exists r', RIncs hE 0 0 r r' /\ canonical r'.
Proof.
  intros Hcanon; inversion Hcanon as [a n t Htail Hlt]; subst.
  pose proof (E_complete_all n t a Htail ltac:(lia)) as Hrun.
  destruct Hrun as (m&t'&Ht'&Hrun&Hbound).
  exists ([LD]^^(a+length t) ++ t'); split.
  - apply E_L_prefix with (p:=0%nat) in Hrun.
    cbn in Hrun.
    replace ([LD]^^(a+length t) ++ t')
      with ([LD]^^a ++ ([LD]^^length t ++ t')).
    2: rewrite lpow_add,app_assoc; reflexivity.
    exact Hrun.
  - econstructor; eauto.
Qed.


(* Little-endian increment used at the dotted right edge.  The [bin_inc_end]
   case is exactly the creation of a new most-significant D1 column. *)
Inductive bin_inc : list RD -> list RD -> Prop :=
| bin_inc_end: bin_inc [] [D1]
| bin_inc_0 r: bin_inc (D0::r) (D1::r)
| bin_inc_1 r r':
    bin_inc r r' -> bin_inc (D1::r) (D0::r').

Lemma tail_succ n r:
  tail n r -> exists r', tail (S n) r' /\ bin_inc r r'.
Proof.
  intros H; induction H.
  - exists [D1;D1]; split; constructor.
  - exists [D0;D0;D1]; split.
    + replace 2 with (2+0*2) by lia; constructor; constructor.
    + repeat constructor.
  - exists (D1::r); split.
    + replace (S (2+k*2)) with (3+k*2) by lia; constructor; exact H.
    + constructor.
  - destruct IHtail as [r' [Ht Hi]].
    exists (D0::r'); split.
    + replace (S (3+k*2)) with (2+(S k)*2) by lia; constructor; exact Ht.
    + constructor; exact Hi.
Qed.

Lemma tail_unique n r r': tail n r -> tail n r' -> r=r'.
Proof.
  intros H1; revert r'.
  induction H1 as [| |k r Hkr IH|k r Hkr IH]; intros r' H2.
  - inversion H2; subst; try lia; reflexivity.
  - inversion H2; subst; try lia; reflexivity.
  - inversion H2; subst; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal; eauto.
  - inversion H2; subst; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal; eauto.
Qed.

Lemma RIncs_empty_tail q r:
  RIncs hA 0 q [] r -> tail q r.
Proof.
  intros H; remember (@nil RD) as x eqn:E in H.
  induction H; try discriminate.
  - constructor.
  - constructor.
  - inversion E; subst; constructor; apply IHRIncs; reflexivity.
  - inversion E; subst; constructor; apply IHRIncs; reflexivity.
Qed.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).

Ltac cat3 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_]) (w2:=[_;_;_]);
  [|eassumption].

Ltac tr1 :=
  eapply segRLs_trans; [esx|].

Ltac wal :=
  eapply segRLs_wall''; esc.

Ltac rw1 :=
  cbn[lpow];
  repeat rewrite lpow_add;
  repeat rewrite lpow_mul;
  repeat rewrite app_assoc.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0LF_1RE0RA_---0LE").

Notation he := ((E,<[0;1;1]),(D,[1;0])).
Notation ha := ((D,<[0;1;1]),(D,[1;0])).
Notation hj := ((E,<[1;1;1]),(D,[1;0])).
Notation hc := ((D,<[1;1;1]),(C,[0;0])).
Notation hy := ((D,<[1;1;1]),(F,[0;1])).
Notation hb := ((B,<[0;1]),(D,[1;0])).
Notation h11b := ((B,<[1;1]),(C,[0;0])).
Notation h11bx := ((B,<[1;1]),(F,[0;1])).
Notation h01e := ((E,<[0;1]),(D,[1;0])).

Definition toH := mode_heads he hj ha hc hy hb h11b h11bx h01e.

Lemma carry_inc_spec r r':
  bin_inc r r' -> sideRLs tm [h11b] (toRC r) (toRC r').
Proof.
  intros H; induction H; cbn[toRC].
  - esc.
  - eapply segRLs_sideRLs_concat; [|constructor]; esc.
  - eapply segRLs_sideRLs_concat; [|exact IHbin_inc]; esc.
Qed.

Lemma B_inc_spec r r':
  r<>[] -> bin_inc r r' -> sideRLs tm [hb] (toRC r) (toRC r').
Proof.
  intros Hne H; inversion H; subst; cbn[toRC] in *.
  - contradiction.
  - eapply segRLs_sideRLs_concat; [|constructor]; esc.
  - eapply segRLs_sideRLs_concat; [|apply carry_inc_spec; assumption]; esc.
Qed.

Lemma Bs_tail q n r:
  tail n r -> exists r', tail (n+q) r' /\
    sideRLs tm ([hb]^^q) (toRC r) (toRC r').
Proof.
  revert n r; induction q; intros n r Htail.
  - exists r; split; [replace (n+0) with n by lia; exact Htail|constructor].
  - destruct (tail_succ _ _ Htail) as (r1&Htail1&Hinc).
    destruct (IHq _ _ Htail1) as (r'&Htail'&Hrun).
    exists r'; split.
    + replace (n+S q) with (S n+q) by lia; exact Htail'.
    + cbn[lpow]. eapply sideRLs_trans.
      * apply B_inc_spec; [apply tail_nonempty with (n:=n); exact Htail|exact Hinc].
      * exact Hrun.
Qed.

Lemma A_rh_all q r:
  tail q r -> sideRLs tm (toH hA 0 q) 0inf (toRC r).
Proof.
  intros Htail.
  destruct (Bs_tail q 0 [D0;D1] tail_0) as (r'&Htail'&Hrun).
  replace (0+q) with q in Htail' by lia.
  pose proof (tail_unique _ _ _ Htail' Htail) as E; subst r'.
  cbn[toH mode_heads].
  eapply sideRLs_trans; [|exact Hrun]; esc.
Qed.

Close Scope sym.

Lemma RIncs_spec tp p q r r':
  RIncs tp p q r r' ->
  sideRLs tm (toH tp p q) (toRC r) (toRC r').
Proof.
  intro H.
  induction H; cbn[toRC toH mode_heads] in *.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. tr1. wal.
  - cat3. tr1. wal.
  - cat3. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3.
    replace (4+k+i*2) with (3+i*2+1+k) by lia.
    rw1.
    eapply segRLs_trans; [|wal].
    eapply @segRLs_trans with (w2:=[1;0;0]%sym); [|esc].
    tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3.
    rw1.
    eapply segRLs_trans; [|wal].
    rewrite <-(app_assoc _ _ [hb]).
    eapply @segRLs_trans with (w2:=[1;0;0]%sym); [|esc].
    tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - esc.
  - esc.
  - change (sideRLs tm (toH hA 0 (2+k*2)) (toRC []) (toRC (D0::r'))).
    apply A_rh_all. constructor. apply RIncs_empty_tail. exact H.
  - change (sideRLs tm (toH hA 0 (3+k*2)) (toRC []) (toRC (D1::r'))).
    apply A_rh_all. constructor. apply RIncs_empty_tail. exact H.
Qed.

Open Scope sym.

Definition lhs : side := (0inf <* <[S1;S1;S1]).
Definition S (r:list RD) := lhs {{{ (fst he,R) }}} (toRC r).

Lemma left_restart r:
  lhs {{{ (snd he,L) }}} r -[tm]->*
  lhs {{{ (fst he,R) }}} r.
Proof. esx. Qed.

Lemma init:
  c0 -[tm]->* S [LD;D0;D1].
Proof. unfold S; cbn[toRC]; esx. Qed.

Lemma BigStep r r':
  RIncs hE 0 0 r r' ->
  S r -[tm]->+ S r'.
Proof.
  intros Hrun.
  pose proof (RIncs_spec _ _ _ _ _ Hrun) as Hside.
  eapply sideRLs_1 in Hside.
  unfold S.
  eapply progress_evstep_trans; [apply Hside|].
  apply left_restart.
Qed.

Lemma canonical_seed:
  canonical [LD;D0;D1].
Proof.
  change (canonical ([LD]^^1 ++ [D0;D1])).
  econstructor; [constructor|lia].
Qed.

Lemma macro_nonhalt:
  ~halts tm (S [LD;D0;D1]).
Proof.
  eapply progress_nonhalt_cond with (P:=canonical).
  - intros r Hr.
    destruct (canonical_step _ Hr) as (r'&Hrun&Hr').
    exists r'; split; [apply BigStep,Hrun|exact Hr'].
  - exact canonical_seed.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact init.
  - exact macro_nonhalt.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0LB_1RD0LF_1RA1RE_1RE0RD_---0LE").

Notation he := ((E,<[0;1;1]),(C,[1;0])).
Notation ha := ((C,<[0;1;1]),(C,[1;0])).
Notation hj := ((E,<[1;1;1]),(C,[1;0])).
Notation hc := ((C,<[1;1;1]),(B,[0;0])).
Notation hy := ((C,<[1;1;1]),(F,[0;1])).
Notation hb := ((A,<[0;1]),(C,[1;0])).
Notation h11b := ((A,<[1;1]),(B,[0;0])).
Notation h11bx := ((A,<[1;1]),(F,[0;1])).
Notation h01e := ((E,<[0;1]),(C,[1;0])).

Definition toH := mode_heads he hj ha hc hy hb h11b h11bx h01e.

Lemma carry_inc_spec r r':
  bin_inc r r' -> sideRLs tm [h11b] (toRC r) (toRC r').
Proof.
  intros H; induction H; cbn[toRC].
  - esc.
  - eapply segRLs_sideRLs_concat; [|constructor]; esc.
  - eapply segRLs_sideRLs_concat; [|exact IHbin_inc]; esc.
Qed.

Lemma B_inc_spec r r':
  r<>[] -> bin_inc r r' -> sideRLs tm [hb] (toRC r) (toRC r').
Proof.
  intros Hne H; inversion H; subst; cbn[toRC] in *.
  - contradiction.
  - eapply segRLs_sideRLs_concat; [|constructor]; esc.
  - eapply segRLs_sideRLs_concat; [|apply carry_inc_spec; assumption]; esc.
Qed.

Lemma Bs_tail q n r:
  tail n r -> exists r', tail (n+q) r' /\
    sideRLs tm ([hb]^^q) (toRC r) (toRC r').
Proof.
  revert n r; induction q; intros n r Htail.
  - exists r; split; [replace (n+0) with n by lia; exact Htail|constructor].
  - destruct (tail_succ _ _ Htail) as (r1&Htail1&Hinc).
    destruct (IHq _ _ Htail1) as (r'&Htail'&Hrun).
    exists r'; split.
    + replace (n+S q) with (S n+q) by lia; exact Htail'.
    + cbn[lpow]. eapply sideRLs_trans.
      * apply B_inc_spec; [apply tail_nonempty with (n:=n); exact Htail|exact Hinc].
      * exact Hrun.
Qed.

Lemma A_rh_all q r:
  tail q r -> sideRLs tm (toH hA 0 q) 0inf (toRC r).
Proof.
  intros Htail.
  destruct (Bs_tail q 0 [D0;D1] tail_0) as (r'&Htail'&Hrun).
  replace (0+q) with q in Htail' by lia.
  pose proof (tail_unique _ _ _ Htail' Htail) as E; subst r'.
  cbn[toH mode_heads].
  eapply sideRLs_trans; [|exact Hrun]; esc.
Qed.

Close Scope sym.

Lemma RIncs_spec tp p q r r':
  RIncs tp p q r r' ->
  sideRLs tm (toH tp p q) (toRC r) (toRC r').
Proof.
  intro H.
  induction H; cbn[toRC toH mode_heads] in *.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. tr1. wal.
  - cat3. tr1. wal.
  - cat3. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3.
    replace (4+k+i*2) with (3+i*2+1+k) by lia.
    rw1.
    eapply segRLs_trans; [|wal].
    eapply @segRLs_trans with (w2:=[1;0;0]%sym); [|esc].
    tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3.
    rw1.
    eapply segRLs_trans; [|wal].
    rewrite <-(app_assoc _ _ [hb]).
    eapply @segRLs_trans with (w2:=[1;0;0]%sym); [|esc].
    tr1. wal.
  - cat3. rw1. tr1. wal.
  - cat3. rw1. tr1. wal.
  - esc.
  - esc.
  - change (sideRLs tm (toH hA 0 (2+k*2)) (toRC []) (toRC (D0::r'))).
    apply A_rh_all. constructor. apply RIncs_empty_tail. exact H.
  - change (sideRLs tm (toH hA 0 (3+k*2)) (toRC []) (toRC (D1::r'))).
    apply A_rh_all. constructor. apply RIncs_empty_tail. exact H.
Qed.

Open Scope sym.

Definition lhs : side := (0inf <* <[S1;S1;S1]).
Definition S (r:list RD) := lhs {{{ (fst he,R) }}} (toRC r).

Lemma left_restart r:
  lhs {{{ (snd he,L) }}} r -[tm]->*
  lhs {{{ (fst he,R) }}} r.
Proof. esx. Qed.

Lemma init:
  c0 -[tm]->* S [LD;LD;D0;D1].
Proof. unfold S; cbn[toRC]; esx. Qed.

Lemma BigStep r r':
  RIncs hE 0 0 r r' ->
  S r -[tm]->+ S r'.
Proof.
  intros Hrun.
  pose proof (RIncs_spec _ _ _ _ _ Hrun) as Hside.
  eapply sideRLs_1 in Hside.
  unfold S.
  eapply progress_evstep_trans; [apply Hside|].
  apply left_restart.
Qed.

Lemma canonical_seed:
  canonical [LD;LD;D0;D1].
Proof.
  change (canonical ([LD]^^2 ++ [D0;D1])).
  econstructor; [constructor|lia].
Qed.

Lemma macro_nonhalt:
  ~halts tm (S [LD;LD;D0;D1]).
Proof.
  eapply progress_nonhalt_cond with (P:=canonical).
  - intros r Hr.
    destruct (canonical_step _ Hr) as (r'&Hrun&Hr').
    exists r'; split; [apply BigStep,Hrun|exact Hr'].
  - exact canonical_seed.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact init.
  - exact macro_nonhalt.
Qed.

End TM2.


