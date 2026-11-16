From BusyCoq Require Import Individual62 Longitudinal DivModCases.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Inductive RD :=
| D1(a:nat)
| D2(a b:nat)
| D3(a b:nat).

Fixpoint toRC ls :=
match ls with
| [] => 0inf
| D1 a :: r => [0;0;0;1] *> [1;1]^^a *> toRC r
| D2 a b :: r => [0;0;0;1] *> [1;1]^^a *> [1;0;0;0;1] *> [1;1]^^b *> toRC r
| D3 a b :: r => [0;0;0;1] *> [1;1]^^a *> [1;1;0;0;1] *> [1;1]^^b *> toRC r
end.

Inductive RInc: (list RD)->(list RD)->Prop :=
| RInc1 a r r':
  RInc r r' ->
  RInc (D1 a::r) (D1 a::r')
| RInc2 a b r:
  RInc (D2 a b::r) (D3 a b::r)
| RInc3 a b r r' r'':
  RInc r r' ->
  RInc r' r'' ->
  RInc (D3 a (1+b)::r) (D2 (1+a) b::r'')
| RInc3' a b c r r':
  RInc r r' ->
  RInc (D3 a 0::D1 b::D1 c::r) (D1 (1+a)::D3 (1+b) c::r')
| RInc3'1 a b:
  RInc [D3 a 0; D1 b] [D1 (1+a); D3 (1+b) 0]
| RInc3'0 a:
  RInc [D3 a 0] [D1 (1+a); D1 2]
| RInc0:
  RInc [] [D1 0]
.

Inductive RInc': (list RD)->(list RD)->Prop :=
| RInc'1 a b r r' r'0 r'1 r'2:
  RInc r r' ->
  RInc r' r'0 ->
  RInc r'0 r'1 ->
  RInc r'1 r'2 ->
  RInc' (D1 a::D1 (1+b)::r) (D1 (4+a)::D1 b::r'2)
| RInc'2 a b c r r' r'0 r'1 r'2:
  RInc r r' ->
  RInc r' r'0 ->
  RInc r'0 r'1 ->
  RInc r'1 r'2 ->
  RInc' (D1 a::D2 b (2+c)::r) (D1 (4+a)::D2 (1+b) c::r'2)
| RInc'1' a b c r r' r'0 r'1 r'2 r'3 r'4:
  RInc r r' ->
  RInc r' r'0 ->
  RInc r'0 r'1 ->
  RInc r'1 r'2 ->
  RInc r'2 r'3 ->
  RInc r'3 r'4 ->
  RInc' (D1 a::D1 0::D1 b::D1 (2+c)::r) (D1 (6+a)::D2 (2+b) c::r'4)
| RInc'2' a b c d r r' r'0 r'1:
  RInc r r' ->
  RInc r' r'0 ->
  RInc r'0 r'1 ->
  RInc' (D1 a::D2 b 0::D1 c::D1 (1+d)::r) (D1 (4+a)::D1 b::D3 (2+c) d::r'1)
.

Inductive RIncN: nat -> list RD -> list RD -> Prop :=
| RIncN0 x:
  RIncN 0 x x
| RIncNS n x y z:
  RInc x y ->
  RIncN n y z ->
  RIncN (S n) x z.

Inductive RIncPN: nat -> list RD -> list RD -> Prop :=
| RIncPN0 x:
  RIncPN 0 x x
| RIncPNS n x y z:
  RInc' x y ->
  RIncPN n y z ->
  RIncPN (S n) x z.

Lemma RIncN_trans n m x y z:
  RIncN n x y ->
  RIncN m y z ->
  RIncN (n + m) x z.
Proof.
  intros Hn.
  revert m z.
  induction Hn; intros m z0 Hm.
  - exact Hm.
  - simpl.
    econstructor; eauto.
Qed.

Lemma RIncPN_trans n m x y z:
  RIncPN n x y ->
  RIncPN m y z ->
  RIncPN (n + m) x z.
Proof.
  intros Hn.
  revert m z.
  induction Hn; intros m z0 Hm.
  - exact Hm.
  - simpl.
    econstructor; eauto.
Qed.

Lemma RIncPN_snoc n x y z:
  RIncPN n x y ->
  RInc' y z ->
  RIncPN (n + 1) x z.
Proof.
  intros Hn Hstep.
  eapply RIncPN_trans.
  - exact Hn.
  - econstructor; [exact Hstep|constructor].
Qed.

Lemma RIncN_D1 n a x y:
  RIncN n x y ->
  RIncN n (D1 a :: x) (D1 a :: y).
Proof.
  intro H.
  induction H.
  - constructor.
  - econstructor.
    + apply RInc1. exact H.
    + exact IHRIncN.
Qed.

Definition bar (m:nat) := D1 (2 * m - 2)%nat.

Definition tick_budget (n:nat) :=
  match n with
  | O => O
  | Datatypes.S O => Datatypes.S O
  | Datatypes.S (Datatypes.S _) => (2 * n - 3)%nat
  end.

Inductive Producer : list nat -> list RD -> Prop :=
| Producer_units q:
  Producer [] ([D1 0]^^q)
| Producer_cons s c p p' xs:
  (2 <= s)%nat ->
  c <= tick_budget s ->
  RIncN c p (bar s :: p') ->
  Producer xs p' ->
  Forall (fun t => (t <= s)%nat) xs ->
  Producer (s :: xs) p.

Lemma Producer_ready_bar s xs p:
  (2 <= s)%nat ->
  Producer xs p ->
  Forall (fun t => (t <= s)%nat) xs ->
  Producer (s :: xs) (bar s :: p).
Proof.
  intros Hs HP Hle.
  eapply Producer_cons with (c := 0%nat) (p' := p).
  - exact Hs.
  - cbn. lia.
  - constructor.
  - exact HP.
  - exact Hle.
Qed.

Lemma Producer_step xs p:
  Producer xs p ->
  exists p',
    RInc p p' /\ Producer xs p'.
Proof.
  intro HP.
  induction HP as [q|s c p p0 xs Hs Hc Hout Hprod IH Hle].
  - exists ([D1 0]^^(S q)).
    split.
    + induction q as [|q IHq].
      * cbn. apply RInc0.
      * cbn. apply RInc1. exact IHq.
    + constructor.
  - destruct c as [|c'].
    + inversion Hout; subst.
      destruct IH as [p1 [Hstep Hprod1]].
      exists (bar s :: p1).
      split.
      * unfold bar. apply RInc1. exact Hstep.
      * apply Producer_ready_bar; assumption.
    + inversion Hout as [| n x y z Hstep Hrest]; subst.
      exists y.
      split; [exact Hstep|].
      eapply Producer_cons with (c := c') (p' := p0).
      * exact Hs.
      * cbn in Hc |- *. lia.
      * exact Hrest.
      * exact Hprod.
      * exact Hle.
Qed.

Lemma Producer_RIncN_exists xs p n:
  Producer xs p ->
  exists p',
    RIncN n p p' /\ Producer xs p'.
Proof.
  revert xs p.
  induction n as [|n IH]; intros xs p HP.
  - exists p.
    split; [constructor|exact HP].
  - destruct (Producer_step _ _ HP) as [p1 [Hstep HP1]].
    destruct (IH _ _ HP1) as [p2 [Hn HP2]].
    exists p2.
    split.
    + econstructor; eauto.
    + exact HP2.
Qed.

Lemma Producer_output1_exact s xs p N:
  Producer (s :: xs) p ->
  tick_budget s <= N ->
  exists p',
    RIncN N p (bar s :: p') /\ Producer xs p'.
Proof.
  intros HP HN.
  inversion HP as [|s0 c p0 p1 xs0 Hs Hc Hout Hprod Hle]; subst.
  assert (HcN : c <= N) by lia.
  destruct (Producer_RIncN_exists xs p1 (N - c) Hprod) as [p2 [Hpad HP2]].
  exists p2.
  split; [|exact HP2].
  replace N with (c + (N - c))%nat at 1 by lia.
  eapply RIncN_trans.
  - exact Hout.
  - unfold bar. apply RIncN_D1. exact Hpad.
Qed.

Lemma Producer_output2_exact s t xs p N:
  Producer (s :: t :: xs) p ->
  tick_budget s + tick_budget t <= N ->
  exists p',
    RIncN N p (bar s :: bar t :: p') /\ Producer xs p'.
Proof.
  intros HP HN.
  inversion HP as [|s0 c1 p0 p1 xs1 Hs Hc1 Hout1 Hprod1 Hle1]; subst.
  inversion Hprod1 as [|t0 c2 p10 p2 xs2 Ht Hc2 Hout2 Hprod2 Hle2]; subst.
  assert (HcN : c1 + c2 <= N) by lia.
  destruct (Producer_RIncN_exists xs p2 (N - (c1 + c2)) Hprod2) as
    [p3 [Hpad HP3]].
  exists p3.
  split; [|exact HP3].
  replace N with (c1 + (c2 + (N - (c1 + c2))))%nat at 1 by lia.
  eapply RIncN_trans.
  - exact Hout1.
  - eapply RIncN_trans.
    + unfold bar. apply RIncN_D1. exact Hout2.
    + unfold bar. apply RIncN_D1. apply RIncN_D1. exact Hpad.
Qed.

Definition init_tail :=
  bar 2 :: bar 2 :: bar 2 :: D3 1 0 :: [D1 0]^^16.

Definition init_state a :=
  D1 a :: D1 0 :: bar 4 :: bar 4 :: bar 4 :: init_tail.

Lemma RInc_zeros m:
  RInc ([D1 0]^^m) ([D1 0]^^(S m)).
Proof.
  induction m.
  - cbn. apply RInc0.
  - cbn. apply RInc1. exact IHm.
Qed.

Definition d3_ones_tail m :=
  match m with
  | O => [bar 2]
  | Datatypes.S m' => D3 1 0 :: [D1 0]^^m'
  end.

Lemma RInc_d3_ones m:
  RInc (D3 1 0 :: [D1 0]^^m) (bar 2 :: d3_ones_tail m).
Proof.
  destruct m as [|[|m]].
  - unfold bar, d3_ones_tail. cbn.
    apply RInc3'0.
  - unfold bar, d3_ones_tail. cbn.
    apply RInc3'1.
  - unfold bar, d3_ones_tail. cbn.
    eapply RInc3'.
    apply RInc_zeros.
Qed.

Lemma RIncN_zeros n m:
  RIncN n ([D1 0]^^m) ([D1 0]^^(m + n)).
Proof.
  revert m.
  induction n; intros m.
  - replace (m + 0)%nat with m by lia.
    constructor.
  - replace (m + S n)%nat with (S m + n)%nat by lia.
    econstructor.
    + apply RInc_zeros.
    + apply IHn.
Qed.

Lemma tick_budget_two_le b s t:
  (1 <= t <= s)%nat ->
  (s <= b)%nat ->
  (2 <= b)%nat ->
  tick_budget s + tick_budget t <= (4 * b - 6)%nat.
Proof.
  destruct s as [|[|s]]; destruct t as [|[|t]]; cbn; lia.
Qed.

Lemma tick_budget_one_le b s:
  (2 <= s <= b)%nat ->
  (2 <= b)%nat ->
  tick_budget s + 1 <= (4 * b - 6)%nat.
Proof.
  destruct s as [|[|s]]; cbn; lia.
Qed.

Lemma Forall_le_weaken xs a b:
  Forall (fun s => (s <= a)%nat) xs ->
  (a <= b)%nat ->
  Forall (fun s => (s <= b)%nat) xs.
Proof.
  intros Hle Hab.
  induction Hle.
  - constructor.
  - constructor; [lia|exact IHHle].
Qed.

Lemma d3_ordinary_cost_le u v:
  (2 <= v <= u)%nat ->
  (4 * v - 3 <= tick_budget (u + v))%nat.
Proof.
  destruct u as [|[|u]]; destruct v as [|[|v]]; cbn; lia.
Qed.

Lemma tick_budget_two_ordinary_le b s t:
  (1 <= t <= s)%nat ->
  (s <= b)%nat ->
  (2 <= b)%nat ->
  tick_budget s + tick_budget t <= (4 * b - 4)%nat.
Proof.
  intros Hts Hsb Hb.
  pose proof (tick_budget_two_le b s t Hts Hsb Hb).
  lia.
Qed.

Lemma tick_budget_le_4y_minus2 s y:
  (2 <= s <= y)%nat ->
  tick_budget s <= (4 * y - 2)%nat.
Proof.
  destruct s as [|[|s]]; cbn; lia.
Qed.

Lemma RIncN_units_output1 q N:
  (1 <= N)%nat ->
  exists q',
    RIncN N ([D1 0]^^q) (bar 1 :: [D1 0]^^q') /\
    Producer [] ([D1 0]^^q').
Proof.
  intro HN.
  exists (q + N - 1)%nat.
  split.
  - replace (bar 1 :: [D1 0]^^(q + N - 1)) with ([D1 0]^^(S (q + N - 1))).
    + replace (S (q + N - 1)) with (q + N)%nat by lia.
      apply RIncN_zeros.
    + unfold bar. cbn.
      replace (q + N - 1 - 0)%nat with (q + N - 1)%nat by lia.
      reflexivity.
  - constructor.
Qed.

Lemma RIncN_units_output2 q N:
  (2 <= N)%nat ->
  exists q',
    RIncN N ([D1 0]^^q) (bar 1 :: bar 1 :: [D1 0]^^q') /\
    Producer [] ([D1 0]^^q').
Proof.
  intro HN.
  exists (q + N - 2)%nat.
  split.
  - replace (bar 1 :: bar 1 :: [D1 0]^^(q + N - 2)) with
      ([D1 0]^^(S (S (q + N - 2)))).
    + replace (S (S (q + N - 2))) with (q + N)%nat by lia.
      apply RIncN_zeros.
    + unfold bar. cbn.
      replace (q + N - 2 - 0)%nat with (q + N - 2)%nat by lia.
      reflexivity.
  - constructor.
Qed.

Lemma Producer_tail_bound s xs p:
  Producer (s :: xs) p ->
  Forall (fun t => (t <= s)%nat) xs.
Proof.
  intro HP.
  inversion HP; subst; assumption.
Qed.

Lemma Producer_second_ge s t xs p:
  Producer (s :: t :: xs) p ->
  (2 <= t)%nat.
Proof.
  intro HP.
  inversion HP as [|s0 c p0 p1 xs0 Hs Hc Hout Hprod Hle]; subst.
  inversion Hprod; subst; assumption.
Qed.

Lemma Producer_second_tail_bound s t xs p:
  Producer (s :: t :: xs) p ->
  Forall (fun u => (u <= t)%nat) xs.
Proof.
  intro HP.
  inversion HP as [|s0 c p0 p1 xs0 Hs Hc Hout Hprod Hle]; subst.
  inversion Hprod; subst; assumption.
Qed.

Lemma Producer_nil_units p:
  Producer [] p ->
  exists q, p = [D1 0]^^q.
Proof.
  intro HP.
  inversion HP; subst.
  exists q. reflexivity.
Qed.

Lemma Producer_bound_one_units xs p:
  Producer xs p ->
  Forall (fun s => (s <= 1)%nat) xs ->
  exists q, xs = [] /\ p = [D1 0]^^q.
Proof.
  intros HP Hbound.
  destruct xs as [|s xs].
  - destruct (Producer_nil_units _ HP) as [q Hq].
    exists q. split; [reflexivity|exact Hq].
  - inversion Hbound; subst.
    inversion HP; subst.
    lia.
Qed.

Lemma Producer_output2_bounded b xs p N:
  Producer xs p ->
  Forall (fun t => (t <= b)%nat) xs ->
  (2 <= b)%nat ->
  (4 * b - 6 <= N)%nat ->
  exists s t xs' p',
    (1 <= t <= s)%nat /\
    (s <= b)%nat /\
    RIncN N p (bar s :: bar t :: p') /\
    Producer xs' p' /\
    Forall (fun u => (u <= t)%nat) xs'.
Proof.
  intros HP Hbound Hb HN.
  destruct xs as [|s xs].
  - inversion HP; subst.
    destruct (RIncN_units_output2 q N) as [q' [Hout HPtail]]; [lia|].
    exists 1%nat, 1%nat, (@nil nat), ([D1 0]^^q').
    repeat split; try lia; try constructor.
    exact Hout.
  - destruct xs as [|t xs].
    + inversion HP as [|s0 c p0 p1 xs0 Hs Hc Hout Hprod Hle]; subst.
      inversion Hprod; subst.
      inversion Hbound; subst.
      assert (Hrest : 1 <= N - c).
      { pose proof (tick_budget_one_le b s ltac:(lia) Hb). lia. }
      destruct (RIncN_units_output1 q (N - c)) as [q' [Hunit HPtail]]; [exact Hrest|].
      exists s, 1%nat, (@nil nat), ([D1 0]^^q').
      repeat split; try lia; try constructor.
      replace N with (c + (N - c))%nat at 1 by lia.
      eapply RIncN_trans.
      * exact Hout.
      * unfold bar. apply RIncN_D1. exact Hunit.
    + inversion Hbound as [|s_bound xs_bound Hsb Htail_bound]; subst.
      inversion Htail_bound as [|t_bound xs_bound2 Htb Hxs_bound]; subst.
      pose proof (Producer_tail_bound _ _ _ HP) as Htail_le_s.
      inversion Htail_le_s as [|t_le_s xs_le_s Hts Hxs_le_s]; subst.
      pose proof (Producer_second_ge _ _ _ _ HP) as Ht_ge.
      pose proof (Producer_second_tail_bound _ _ _ _ HP) as Hxs_le_t.
      destruct (Producer_output2_exact s t xs p N HP) as [p' [Hout HPtail]].
      * transitivity (4 * b - 6)%nat.
        -- apply tick_budget_two_le; lia.
        -- exact HN.
      * exists s, t, xs, p'.
        repeat split; try lia.
        -- exact Hout.
        -- exact HPtail.
        -- exact Hxs_le_t.
Qed.

Fixpoint q_outputs m :=
  match m with
  | O => [2; 2]
  | Datatypes.S m' => 2 :: q_outputs m'
  end.

Lemma q_outputs_le2 m:
  Forall (fun t => (t <= 2)%nat) (q_outputs m).
Proof.
  induction m.
  - cbn. repeat constructor; lia.
  - cbn. constructor; [lia|exact IHm].
Qed.

Lemma q_outputs_le b m:
  (2 <= b)%nat ->
  Forall (fun t => (t <= b)%nat) (q_outputs m).
Proof.
  intros Hb.
  induction m.
  - cbn. repeat constructor; lia.
  - cbn. constructor; [lia|exact IHm].
Qed.

Lemma Producer_q_outputs m:
  Producer (q_outputs m) (D3 1 0 :: [D1 0]^^m).
Proof.
  induction m as [|m IH].
  - cbn [q_outputs].
    eapply Producer_cons with (c := 1%nat) (p' := [bar 2]).
    + lia.
    + cbn. lia.
    + econstructor.
      * apply RInc_d3_ones.
      * constructor.
    + apply Producer_ready_bar.
      * lia.
      * apply (Producer_units 0%nat).
      * constructor.
    + cbn. constructor; [lia|constructor].
  - cbn [q_outputs].
    eapply Producer_cons with (c := 1%nat) (p' := D3 1 0 :: [D1 0]^^m).
    + lia.
    + cbn. lia.
    + econstructor.
      * apply RInc_d3_ones.
      * constructor.
    + exact IH.
    + apply q_outputs_le2.
Qed.

Definition init_producer_xs := 2 :: 2 :: q_outputs 16.

Definition terminal_outputs u q :=
  match q with
  | O => [u + 1; 2]
  | Datatypes.S q' => (u + 1) :: q_outputs q'
  end.

Lemma terminal_outputs_le b u q:
  (1 <= u)%nat ->
  (u + 1 <= b)%nat ->
  Forall (fun t => (t <= b)%nat) (terminal_outputs u q).
Proof.
  intros Hu Hub.
  destruct q as [|q]; cbn [terminal_outputs].
  - repeat constructor; lia.
  - constructor; [lia|].
    apply q_outputs_le. lia.
Qed.

Lemma RInc_d3_terminal u q:
  (1 <= u)%nat ->
  RInc (D3 (2 * u - 1) 0 :: [D1 0]^^q)
    (bar (u + 1) :: d3_ones_tail q).
Proof.
  intro Hu.
  destruct q as [|[|q]].
  - unfold bar, d3_ones_tail. cbn.
    replace (u + 1 + (u + 1 + 0) - 2)%nat with
      (1 + (u + (u + 0) - 1))%nat by lia.
    apply RInc3'0.
  - unfold bar, d3_ones_tail. cbn.
    replace (u + 1 + (u + 1 + 0) - 2)%nat with
      (1 + (u + (u + 0) - 1))%nat by lia.
    replace 1%nat with (1 + 0)%nat by lia.
    apply RInc3'1.
  - unfold bar, d3_ones_tail. cbn.
    replace (u + 1 + (u + 1 + 0) - 2)%nat with
      (1 + (u + (u + 0) - 1))%nat by lia.
    replace 1%nat with (1 + 0)%nat by lia.
    eapply RInc3'.
    apply RInc_zeros.
Qed.

Lemma Producer_terminal_outputs u q:
  (1 <= u)%nat ->
  Producer (terminal_outputs u q)
    (D3 (2 * u - 1) 0 :: [D1 0]^^q).
Proof.
  intro Hu.
  destruct q as [|q]; cbn [terminal_outputs].
  - eapply Producer_cons with (c := 1%nat) (p' := d3_ones_tail 0).
    + lia.
    + destruct u as [|[|u]]; cbn in Hu |- *; lia.
    + econstructor.
      * apply RInc_d3_terminal. exact Hu.
      * constructor.
    + unfold d3_ones_tail.
      apply Producer_ready_bar.
      * lia.
      * apply (Producer_units 0%nat).
      * constructor.
    + cbn. constructor; [lia|constructor].
  - eapply Producer_cons with (c := 1%nat) (p' := d3_ones_tail (S q)).
    + lia.
    + destruct u as [|[|u]]; cbn in Hu |- *; lia.
    + econstructor.
      * apply RInc_d3_terminal. exact Hu.
      * constructor.
    + unfold d3_ones_tail.
      apply Producer_q_outputs.
    + apply q_outputs_le. lia.
Qed.

Lemma Producer_init_tail:
  Producer (2 :: init_producer_xs) init_tail.
Proof.
  unfold init_producer_xs, init_tail.
  apply Producer_ready_bar.
  - lia.
  - apply Producer_ready_bar.
    + lia.
    + apply Producer_ready_bar.
      * lia.
      * apply Producer_q_outputs.
      * apply q_outputs_le2.
    + constructor; [lia|apply q_outputs_le2].
  - constructor; [lia|constructor; [lia|apply q_outputs_le2]].
Qed.

Definition GoodP x :=
  exists a x0 y z v xs p,
    x = D1 a :: D1 0 :: bar x0 :: bar y :: bar z :: p /\
    (x0 >= y)%nat /\ (y >= z)%nat /\ (z >= 2)%nat /\
    (2 <= v <= z)%nat /\
    Producer (v :: xs) p /\
    Forall (fun s => (s <= v)%nat) xs.

Lemma GoodP_init a:
  GoodP (init_state a).
Proof.
  unfold GoodP.
  exists a.
  exists 4%nat.
  exists 4%nat.
  exists 4%nat.
  exists 2%nat.
  exists init_producer_xs.
  exists init_tail.
  split.
  - unfold init_state. reflexivity.
  - repeat split; try lia.
    + exact Producer_init_tail.
    + cbn. repeat constructor; try lia.
Qed.

Lemma RIncN_split3 x z:
  RIncN 3 x z ->
  exists x1 x2,
    RInc x x1 /\ RInc x1 x2 /\ RInc x2 z.
Proof.
  intro H.
  change 3%nat with (S (S (S 0))) in H.
  repeat match goal with
  | H : RIncN (S _) _ _ |- _ => inversion H; subst; clear H
  end.
  inversion H4; subst.
  repeat eexists; repeat split; eassumption.
Qed.

Lemma RIncN_split2 n x z:
  RIncN (2 + n) x z ->
  exists x1 x2,
    RInc x x1 /\ RInc x1 x2 /\ RIncN n x2 z.
Proof.
  intro H.
  change (2 + n)%nat with (S (S n)) in H.
  repeat match goal with
  | H : RIncN (S _) _ _ |- _ => inversion H; subst; clear H
  end.
  repeat eexists; repeat split; eassumption.
Qed.

Lemma RIncN_split4 n x z:
  RIncN (4 + n) x z ->
  exists x1 x2 x3 x4,
    RInc x x1 /\ RInc x1 x2 /\ RInc x2 x3 /\ RInc x3 x4 /\ RIncN n x4 z.
Proof.
  intro H.
  change (4 + n)%nat with (S (S (S (S n)))) in H.
  repeat match goal with
  | H : RIncN (S _) _ _ |- _ => inversion H; subst; clear H
  end.
  repeat eexists; repeat split; eassumption.
Qed.

Lemma RIncN_split6 n x z:
  RIncN (6 + n) x z ->
  exists x1 x2 x3 x4 x5 x6,
    RInc x x1 /\ RInc x1 x2 /\ RInc x2 x3 /\ RInc x3 x4 /\
    RInc x4 x5 /\ RInc x5 x6 /\ RIncN n x6 z.
Proof.
  intro H.
  change (6 + n)%nat with (S (S (S (S (S (S n)))))) in H.
  repeat match goal with
  | H : RIncN (S _) _ _ |- _ => inversion H; subst; clear H
  end.
  repeat eexists; repeat split; eassumption.
Qed.

Lemma RIncPN_D2_reduce t a b c r r':
  RIncN (4 * t) r r' ->
  RIncPN t
    (D1 a :: D2 b (2 * t + c) :: r)
    (D1 (a + 4 * t) :: D2 (b + t) c :: r').
Proof.
  revert a b r r'.
  induction t as [|t IH]; intros a b r r' Htail.
  - cbn in Htail |- *.
    inversion Htail; subst.
    replace (a + 0)%nat with a by lia.
    replace (b + 0)%nat with b by lia.
    constructor.
  - replace (4 * S t)%nat with (4 + 4 * t)%nat in Htail by lia.
    destruct (RIncN_split4 _ _ _ Htail) as
      [r1 [r2 [r3 [r4 [H1 [H2 [H3 [H4 Hrest]]]]]]]].
    replace (2 * S t + c)%nat with (2 + (2 * t + c))%nat by lia.
    replace (a + 4 * S t)%nat with ((4 + a) + 4 * t)%nat by lia.
    replace (b + S t)%nat with ((1 + b) + t)%nat by lia.
    econstructor.
    + eapply RInc'2; eauto.
    + apply IH.
      exact Hrest.
Qed.

Lemma RIncPN_D1_reduce t a r r':
  RIncN (4 * t) r r' ->
  RIncPN t
    (D1 a :: D1 t :: r)
    (D1 (a + 4 * t) :: D1 0 :: r').
Proof.
  revert a r r'.
  induction t as [|t IH]; intros a r r' Htail.
  - cbn in Htail |- *.
    inversion Htail; subst.
    replace (a + 0)%nat with a by lia.
    constructor.
  - replace (4 * S t)%nat with (4 + 4 * t)%nat in Htail by lia.
    destruct (RIncN_split4 _ _ _ Htail) as
      [r1 [r2 [r3 [r4 [H1 [H2 [H3 [H4 Hrest]]]]]]]].
    replace (a + 4 * S t)%nat with ((4 + a) + 4 * t)%nat by lia.
    econstructor.
    + eapply RInc'1; eauto.
    + apply IH.
      exact Hrest.
Qed.

Lemma RIncN_D3_decr q a r r':
  RIncN (2 * q) r r' ->
  RIncN (2 * q)
    (D3 a q :: r)
    (D3 (a + q) 0 :: r').
Proof.
  revert a r r'.
  induction q as [|q IH]; intros a r r' Hr.
  - cbn in Hr |- *.
    inversion Hr; subst.
    replace (a + 0)%nat with a by lia.
    constructor.
  - replace (2 * S q)%nat with (2 + 2 * q)%nat in Hr by lia.
    destruct (RIncN_split2 _ _ _ Hr) as [r1 [r2 [H1 [H2 Hrest]]]].
    replace (2 * S q)%nat with (2 + 2 * q)%nat by lia.
    econstructor.
    + eapply RInc3; eauto.
    + econstructor.
      * apply RInc2.
      * replace (a + S q)%nat with ((1 + a) + q)%nat by lia.
        apply IH.
        exact Hrest.
Qed.

Lemma RIncN_D3_finish q a c d r r0 r1:
  RIncN (2 * q) r (D1 c :: D1 d :: r0) ->
  RInc r0 r1 ->
  RIncN (2 * q + 1)
    (D3 a q :: r)
    (D1 (a + q + 1) :: D3 (c + 1) d :: r1).
Proof.
  intros Hprep Hstep.
  replace (a + q + 1)%nat with (1 + (a + q))%nat by lia.
  replace (c + 1)%nat with (1 + c)%nat by lia.
  eapply RIncN_trans.
  - apply RIncN_D3_decr.
    exact Hprep.
  - econstructor.
    + apply RInc3'.
      exact Hstep.
    + constructor.
Qed.

Lemma RIncN_D3_producer_start_strong u v xs r:
  (2 <= v)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists s t xs' r',
    (1 <= t <= s)%nat /\
    (s <= v)%nat /\
    RIncN (4 * v - 5)
      (D3 (2 * u) (2 * v - 3) :: r)
      (bar (u + v) :: D3 (2 * s - 1) (2 * t - 2) :: r') /\
    Producer xs' r' /\
    Forall (fun w => (w <= t)%nat) xs' /\
    (t = 1%nat -> exists q, xs' = [] /\ r' = [D1 0]^^(S q)).
Proof.
  intros Hv HP Hbound.
  destruct (Producer_output2_bounded v xs r (4 * v - 6)) as
    [s [t [xs' [rest [Hts [Hsv [Hprep [HPrest Hxs']]]]]]]].
  - exact HP.
  - exact Hbound.
  - exact Hv.
  - lia.
  - destruct t as [|[|t']].
    + lia.
    + destruct (Producer_bound_one_units _ _ HPrest Hxs') as [q [Hxs_nil Hrest]].
      subst xs' rest.
      exists s, 1%nat, (@nil nat), ([D1 0]^^(S q)).
      repeat split; try lia; try constructor.
      * unfold bar in Hprep |- *.
        replace (4 * v - 5)%nat with (2 * (2 * v - 3) + 1)%nat by lia.
        replace (2 * (u + v) - 2)%nat with (2 * u + (2 * v - 3) + 1)%nat by lia.
        change (D3 (2 * s - 1) (2 * 1 - 2) :: [D1 0]^^(S q)) with
          (D3 (2 * s - 1) 0 :: [D1 0]^^(S q)).
        replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
        eapply RIncN_D3_finish.
        -- replace (2 * (2 * v - 3))%nat with (4 * v - 6)%nat by lia.
           exact Hprep.
        -- apply RInc_zeros.
      * exists q. split; reflexivity.
    + destruct (Producer_step _ _ HPrest) as [r' [Hstep HPr']].
      exists s, (S (S t')), xs', r'.
      repeat split; try lia; try assumption.
      * unfold bar in Hprep |- *.
        replace (4 * v - 5)%nat with (2 * (2 * v - 3) + 1)%nat by lia.
        replace (2 * (u + v) - 2)%nat with (2 * u + (2 * v - 3) + 1)%nat by lia.
        replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
        eapply RIncN_D3_finish.
        -- replace (2 * (2 * v - 3))%nat with (4 * v - 6)%nat by lia.
           exact Hprep.
        -- exact Hstep.
Qed.

Lemma RIncN_D3_producer_ordinary_strong u v xs r:
  (1 <= u)%nat ->
  (2 <= v)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists s t xs' r',
    (1 <= t <= s)%nat /\
    (s <= v)%nat /\
    RIncN (4 * v - 3)
      (D3 (2 * u - 1) (2 * v - 2) :: r)
      (bar (u + v) :: D3 (2 * s - 1) (2 * t - 2) :: r') /\
    Producer xs' r' /\
    Forall (fun w => (w <= t)%nat) xs' /\
    (t = 1%nat -> exists q, xs' = [] /\ r' = [D1 0]^^(S q)).
Proof.
  intros Hu Hv HP Hbound.
  destruct (Producer_output2_bounded v xs r (4 * v - 4)) as
    [s [t [xs' [rest [Hts [Hsv [Hprep [HPrest Hxs']]]]]]]].
  - exact HP.
  - exact Hbound.
  - exact Hv.
  - lia.
  - destruct t as [|[|t']].
    + lia.
    + destruct (Producer_bound_one_units _ _ HPrest Hxs') as [q [Hxs_nil Hrest]].
      subst xs' rest.
      exists s, 1%nat, (@nil nat), ([D1 0]^^(S q)).
      repeat split; try lia; try constructor.
      * unfold bar in Hprep |- *.
        replace (4 * v - 3)%nat with (2 * (2 * v - 2) + 1)%nat by lia.
        replace (2 * (u + v) - 2)%nat with
          (2 * u - 1 + (2 * v - 2) + 1)%nat by lia.
        change (D3 (2 * s - 1) (2 * 1 - 2) :: [D1 0]^^(S q)) with
          (D3 (2 * s - 1) 0 :: [D1 0]^^(S q)).
        replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
        eapply RIncN_D3_finish.
        -- replace (2 * (2 * v - 2))%nat with (4 * v - 4)%nat by lia.
           exact Hprep.
        -- apply RInc_zeros.
      * exists q. split; reflexivity.
    + destruct (Producer_step _ _ HPrest) as [r' [Hstep HPr']].
      exists s, (S (S t')), xs', r'.
      repeat split; try lia; try assumption.
      * unfold bar in Hprep |- *.
        replace (4 * v - 3)%nat with (2 * (2 * v - 2) + 1)%nat by lia.
        replace (2 * (u + v) - 2)%nat with
          (2 * u - 1 + (2 * v - 2) + 1)%nat by lia.
        replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
        eapply RIncN_D3_finish.
        -- replace (2 * (2 * v - 2))%nat with (4 * v - 4)%nat by lia.
           exact Hprep.
        -- exact Hstep.
Qed.

Lemma Producer_D3_ordinary_nil u v q:
  (1 <= v <= u)%nat ->
  exists ys,
    Producer ys (D3 (2 * u - 1) (2 * v - 2) :: [D1 0]^^q) /\
    Forall (fun s => (s <= u + v)%nat) ys.
Proof.
  intro Huv.
  destruct v as [|[|v']].
  - lia.
  - exists (terminal_outputs u q).
    split.
    + replace (2 * 1 - 2)%nat with 0%nat by lia.
      apply Producer_terminal_outputs. lia.
    + apply terminal_outputs_le; lia.
  - destruct (RIncN_units_output2 q (4 * S (S v') - 4)) as
      [q0 [Hprep HPrest]]; [lia|].
    destruct (Producer_step _ _ HPrest) as [r' [Hstep HPr']].
    destruct (Producer_nil_units _ HPr') as [q1 Hr'].
    exists ((u + S (S v')) :: terminal_outputs 1 q1).
    split.
    + eapply Producer_cons with
        (c := 4 * S (S v') - 3)
        (p' := D3 1 0 :: [D1 0]^^q1).
      * lia.
      * apply d3_ordinary_cost_le. lia.
      * rewrite <- Hr'.
        unfold bar in Hprep |- *.
        replace (4 * S (S v') - 3)%nat with
          (2 * (2 * S (S v') - 2) + 1)%nat by lia.
        replace (2 * (u + S (S v')) - 2)%nat with
          (2 * u - 1 + (2 * S (S v') - 2) + 1)%nat by lia.
        replace (D3 1 0 :: r') with
          (D3 (2 * 1 - 2 + 1) (2 * 1 - 2) :: r') by (cbn; reflexivity).
        eapply (RIncN_D3_finish
          (2 * S (S v') - 2) (2 * u - 1)
          (2 * 1 - 2) (2 * 1 - 2)
          ([D1 0]^^q) ([D1 0]^^q0) r').
        -- replace (2 * (2 * S (S v') - 2))%nat with
             (4 * S (S v') - 4)%nat by lia.
           exact Hprep.
        -- exact Hstep.
      * apply Producer_terminal_outputs. lia.
      * apply terminal_outputs_le; lia.
    + constructor; [lia|].
      apply terminal_outputs_le; lia.
Qed.

Lemma Producer_D3_ordinary_exists n u v xs r:
  (length xs <= n)%nat ->
  (1 <= v <= u)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists ys,
    Producer ys (D3 (2 * u - 1) (2 * v - 2) :: r) /\
    Forall (fun s => (s <= u + v)%nat) ys.
Proof.
  revert u v xs r.
  induction n as [|n IH]; intros u v xs r Hlen Huv HP Hbound.
  - destruct xs as [|s xs].
    + inversion HP as [q|]; subst.
      apply Producer_D3_ordinary_nil. exact Huv.
    + cbn in Hlen. lia.
  - destruct v as [|[|v']].
    + lia.
    + destruct (Producer_bound_one_units _ _ HP Hbound) as [q [Hxs Hr]].
      subst xs r.
      exists (terminal_outputs u q).
      split.
      * replace (2 * 1 - 2)%nat with 0%nat by lia.
        apply Producer_terminal_outputs. lia.
      * apply terminal_outputs_le; lia.
    + destruct xs as [|s xs].
      * inversion HP as [q|]; subst.
        apply Producer_D3_ordinary_nil. lia.
      * destruct xs as [|t xs].
        -- inversion HP as [|s0 c p0 p1 xs0 Hs Hc Hout Hprod Hle]; subst.
           inversion Hprod as [q|]; subst.
           inversion Hbound as [|s_bound xs_bound Hsv Hnil]; subst.
           assert (Hrest : 1 <= 4 * S (S v') - 4 - c).
           { pose proof (tick_budget_one_le (S (S v')) s ltac:(lia) ltac:(lia)).
             lia. }
           destruct (RIncN_units_output1 q (4 * S (S v') - 4 - c)) as
             [q0 [Hunit HPrest]]; [exact Hrest|].
           assert
             (Hprep :
               RIncN (4 * S (S v') - 4) r
                 (bar s :: bar 1 :: [D1 0]^^q0)).
           { replace (4 * S (S v') - 4)%nat with
               (c + (4 * S (S v') - 4 - c))%nat at 1 by lia.
             eapply RIncN_trans.
             - exact Hout.
             - unfold bar. apply RIncN_D1. exact Hunit.
           }
           destruct (Producer_step _ _ HPrest) as [r' [Hstep HPr']].
           destruct (Producer_nil_units _ HPr') as [q1 Hr'].
           exists ((u + S (S v')) :: terminal_outputs s q1).
           split.
           ** eapply Producer_cons with
                (c := 4 * S (S v') - 3)
                (p' := D3 (2 * s - 1) 0 :: [D1 0]^^q1).
              --- lia.
              --- apply d3_ordinary_cost_le. lia.
              --- rewrite <- Hr'.
                  unfold bar in Hprep |- *.
                  replace (4 * S (S v') - 3)%nat with
                    (2 * (2 * S (S v') - 2) + 1)%nat by lia.
                  replace (2 * (u + S (S v')) - 2)%nat with
                    (2 * u - 1 + (2 * S (S v') - 2) + 1)%nat by lia.
                  change (D3 (2 * s - 1) 0 :: r') with
                    (D3 (2 * s - 1) (2 * 1 - 2) :: r').
                  replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
                  eapply (RIncN_D3_finish
                    (2 * S (S v') - 2) (2 * u - 1)
                    (2 * s - 2) (2 * 1 - 2)
                    r ([D1 0]^^q0) r').
                  +++ replace (2 * (2 * S (S v') - 2))%nat with
                        (4 * S (S v') - 4)%nat by lia.
                      exact Hprep.
                  +++ exact Hstep.
              --- apply Producer_terminal_outputs. lia.
              --- apply terminal_outputs_le; lia.
           ** constructor; [lia|].
              apply terminal_outputs_le; lia.
        -- pose proof HP as HP0.
           inversion Hbound as [|s_bound xs_bound Hsv Htail_bound]; subst.
           inversion Htail_bound as [|t_bound xs_bound2 Htv Hxs_bound]; subst.
           pose proof (Producer_tail_bound _ _ _ HP0) as Htail_le_s.
           inversion Htail_le_s as [|t_le_s xs_le_s Hts Hxs_le_s]; subst.
           pose proof (Producer_second_ge _ _ _ _ HP0) as Ht_ge.
           pose proof (Producer_second_tail_bound _ _ _ _ HP0) as Hxs_le_t.
           destruct (Producer_output2_exact s t xs r (4 * S (S v') - 4) HP0) as
             [rest [Hprep HPrest]].
           ** apply tick_budget_two_ordinary_le; lia.
           ** destruct (Producer_step _ _ HPrest) as [r' [Hstep HPr']].
              destruct (IH s t xs r') as [ys [HPys Hys_bound]].
              --- cbn in Hlen. lia.
              --- lia.
              --- exact HPr'.
              --- exact Hxs_le_t.
              --- exists ((u + S (S v')) :: ys).
                  split.
                  +++ eapply Producer_cons with
                        (c := 4 * S (S v') - 3)
                        (p' := D3 (2 * s - 1) (2 * t - 2) :: r').
                      *** lia.
                      *** apply d3_ordinary_cost_le. lia.
                      *** unfold bar in Hprep |- *.
                          replace (4 * S (S v') - 3)%nat with
                            (2 * (2 * S (S v') - 2) + 1)%nat by lia.
                          replace (2 * (u + S (S v')) - 2)%nat with
                            (2 * u - 1 + (2 * S (S v') - 2) + 1)%nat by lia.
                          replace (2 * s - 1)%nat with (2 * s - 2 + 1)%nat by lia.
                          eapply (RIncN_D3_finish
                            (2 * S (S v') - 2) (2 * u - 1)
                            (2 * s - 2) (2 * t - 2)
                            r rest r').
                          ---- replace (2 * (2 * S (S v') - 2))%nat with
                                 (4 * S (S v') - 4)%nat by lia.
                               exact Hprep.
                          ---- exact Hstep.
                      *** exact HPys.
                      *** eapply Forall_le_weaken.
                          ---- exact Hys_bound.
                          ---- lia.
                  +++ constructor; [lia|].
                      eapply Forall_le_weaken.
                      *** exact Hys_bound.
                      *** lia.
Qed.

Lemma Producer_d3_ones_active q:
  exists xs,
    Producer (2 :: xs) (d3_ones_tail q) /\
    Forall (fun s => (s <= 2)%nat) xs.
Proof.
  destruct q as [|q].
  - exists (@nil nat).
    split.
    + unfold d3_ones_tail.
      apply Producer_ready_bar.
      * lia.
      * apply (Producer_units 0%nat).
      * constructor.
    + constructor.
  - destruct q as [|q].
    + exists [2].
      split.
      * change (Producer (q_outputs 0) (D3 1 0 :: [D1 0]^^0)).
        apply Producer_q_outputs.
      * cbn. constructor; [lia|constructor].
    + exists (q_outputs q).
      split.
      * change (Producer (q_outputs (S q)) (D3 1 0 :: [D1 0]^^(S q))).
        apply Producer_q_outputs.
      * apply q_outputs_le2.
Qed.

Lemma Producer_D3_ordinary_active_exists u v xs r:
  (1 <= v <= u)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists w ys,
    (2 <= w <= u + v)%nat /\
    Producer (w :: ys) (D3 (2 * u - 1) (2 * v - 2) :: r) /\
    Forall (fun s => (s <= w)%nat) ys.
Proof.
  intros Huv HP Hbound.
  destruct v as [|[|v']].
  - lia.
  - destruct (Producer_bound_one_units _ _ HP Hbound) as [q [Hxs Hr]].
    subst xs r.
    destruct q as [|q].
    + exists (u + 1)%nat, [2].
      split; [lia|].
      split.
      * change (Producer (terminal_outputs u 0)
          (D3 (2 * u - 1) (2 * 1 - 2) :: [D1 0]^^0)).
        replace (2 * 1 - 2)%nat with 0%nat by lia.
        apply Producer_terminal_outputs. lia.
      * cbn. constructor; [lia|constructor].
    + exists (u + 1)%nat, (q_outputs q).
      split; [lia|].
      split.
      * change (Producer (terminal_outputs u (S q))
          (D3 (2 * u - 1) (2 * 1 - 2) :: [D1 0]^^(S q))).
        replace (2 * 1 - 2)%nat with 0%nat by lia.
        apply Producer_terminal_outputs. lia.
      * apply q_outputs_le. lia.
  - destruct (RIncN_D3_producer_ordinary_strong u (S (S v')) xs r) as
      [s [t [xs' [r' [Hts [Hsv [Hout [HP' [Hxs' _]]]]]]]]].
    + lia.
    + lia.
    + exact HP.
    + exact Hbound.
    + destruct (Producer_D3_ordinary_exists (length xs') s t xs' r') as
        [ys [HPys Hys_bound]].
      * lia.
      * lia.
      * exact HP'.
      * exact Hxs'.
      * exists (u + S (S v'))%nat, ys.
        split; [lia|].
        split.
        -- eapply Producer_cons with
             (c := 4 * S (S v') - 3)
             (p' := D3 (2 * s - 1) (2 * t - 2) :: r').
           ++ lia.
           ++ apply d3_ordinary_cost_le. lia.
           ++ exact Hout.
           ++ exact HPys.
           ++ eapply Forall_le_weaken.
              ** exact Hys_bound.
              ** lia.
        -- eapply Forall_le_weaken.
           ++ exact Hys_bound.
           ++ lia.
Qed.

Lemma RIncN_D3_ordinary_output1_active u v xs r:
  (1 <= v <= u)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists w ys p',
    (2 <= w <= 2 * v)%nat /\
    RIncN (4 * v - 3)
      (D3 (2 * u - 1) (2 * v - 2) :: r)
      (bar (u + v) :: p') /\
    Producer (w :: ys) p' /\
    Forall (fun s => (s <= w)%nat) ys.
Proof.
  intros Huv HP Hbound.
  destruct v as [|[|v']].
  - lia.
  - destruct (Producer_bound_one_units _ _ HP Hbound) as [q [Hxs Hr]].
    subst xs r.
    destruct (Producer_d3_ones_active q) as [ys [HPys Hys]].
    exists 2%nat, ys, (d3_ones_tail q).
    split; [lia|].
    split.
    + replace (4 * 1 - 3)%nat with 1%nat by lia.
      replace (u + 1)%nat with (u + 1)%nat by lia.
      econstructor.
      * apply RInc_d3_terminal. lia.
      * constructor.
    + split; assumption.
  - destruct (RIncN_D3_producer_ordinary_strong u (S (S v')) xs r) as
      [s [t [xs' [r' [Hts [Hsv [Hout [HP' [Hxs' Hterm]]]]]]]]].
    + lia.
    + lia.
    + exact HP.
    + exact Hbound.
    + destruct (Producer_D3_ordinary_active_exists s t xs' r') as
        [w [ys [Hw [HPys Hys]]]].
      * lia.
      * exact HP'.
      * exact Hxs'.
      * exists w, ys, (D3 (2 * s - 1) (2 * t - 2) :: r').
        repeat split; try lia; try assumption.
Qed.

Lemma RIncN_D3_ordinary_output2_active V u v xs r:
  (2 <= v <= u)%nat ->
  (v <= V)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists z w ys p' C,
    (C <= 8 * V - 6)%nat /\
    (2 <= z <= u + v)%nat /\
    (2 <= w <= z)%nat /\
    RIncN C
      (D3 (2 * u - 1) (2 * v - 2) :: r)
      (bar (u + v) :: bar z :: p') /\
    Producer (w :: ys) p' /\
    Forall (fun s => (s <= w)%nat) ys.
Proof.
  intros Huv HvV HP Hbound.
  destruct (RIncN_D3_producer_ordinary_strong u v xs r) as
    [s [t [xs' [r' [Hts [Hsv [Hout [HP' [Hxs' Hterm]]]]]]]]].
  - lia.
  - lia.
  - exact HP.
  - exact Hbound.
  - destruct t as [|[|t']].
    + lia.
    + destruct (Hterm eq_refl) as [q [Hxs_nil Hr']].
      subst xs' r'.
      destruct (Producer_d3_ones_active (S q)) as [ys [HPys Hys]].
      exists (s + 1)%nat, 2%nat, ys, (d3_ones_tail (S q)),
        (4 * v - 3 + 1)%nat.
      repeat split; try lia.
      * eapply RIncN_trans.
        -- exact Hout.
        -- unfold bar.
           apply RIncN_D1.
           econstructor.
           ++ apply RInc_d3_terminal. lia.
           ++ constructor.
      * exact HPys.
      * exact Hys.
    + destruct (RIncN_D3_ordinary_output1_active s (S (S t')) xs' r') as
        [w [ys [p' [Hw [Hnext [HPys Hys]]]]]].
      * lia.
      * exact HP'.
      * exact Hxs'.
      * exists (s + S (S t'))%nat, w, ys, p',
          (4 * v - 3 + (4 * S (S t') - 3))%nat.
        repeat split; try lia.
        -- eapply RIncN_trans.
           ++ exact Hout.
           ++ unfold bar. apply RIncN_D1. exact Hnext.
        -- exact HPys.
        -- exact Hys.
Qed.

Lemma RIncN_D3_start_output3_active u v xs r:
  (2 <= v <= u)%nat ->
  Producer xs r ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists x y z w ys p' C,
    (C <= 12 * v - 11)%nat /\
    (x = u + v)%nat /\
    (x >= y)%nat /\
    (y >= z)%nat /\
    (z >= 2)%nat /\
    (2 <= w <= z)%nat /\
    RIncN C
      (D3 (2 * u) (2 * v - 3) :: r)
      (bar x :: bar y :: bar z :: p') /\
    Producer (w :: ys) p' /\
    Forall (fun s => (s <= w)%nat) ys.
Proof.
  intros Huv HP Hbound.
  destruct (RIncN_D3_producer_start_strong u v xs r) as
    [s [t [xs' [r' [Hts [Hsv [Hout [HP' [Hxs' Hterm]]]]]]]]].
  - lia.
  - exact HP.
  - exact Hbound.
  - destruct t as [|[|t']].
    + lia.
    + destruct (Hterm eq_refl) as [q [Hxs_nil Hr']].
      subst xs' r'.
      destruct (Producer_d3_ones_active q) as [ys [HPys Hys]].
      exists (u + v)%nat.
      exists (s + 1)%nat.
      exists 2%nat.
      exists 2%nat.
      exists ys.
      exists (d3_ones_tail q).
      exists (4 * v - 5 + 2)%nat.
      repeat split; try lia.
      * assert
          (Hcont :
            RIncN 2
              (D3 (2 * s - 1) 0 :: [D1 0]^^(S q))
              (bar (s + 1) :: bar 2 :: d3_ones_tail q)).
        { change 2%nat with (S (S 0)).
          econstructor.
          - apply RInc_d3_terminal. lia.
          - econstructor.
            + unfold bar. apply RInc1. apply RInc_d3_ones.
            + constructor.
        }
        eapply RIncN_trans.
        -- exact Hout.
        -- unfold bar. apply RIncN_D1. exact Hcont.
      * exact HPys.
      * exact Hys.
    + destruct (RIncN_D3_ordinary_output2_active v s (S (S t')) xs' r') as
        [z [w [ys [p' [C2 [HC2 [Hz [Hw [Hcont [HPys Hys]]]]]]]]]].
      * lia.
      * lia.
      * exact HP'.
      * exact Hxs'.
      * exists (u + v)%nat.
        exists (s + S (S t'))%nat.
        exists z.
        exists w.
        exists ys.
        exists p'.
        exists (4 * v - 5 + C2)%nat.
        repeat split; try lia.
        -- eapply RIncN_trans.
           ++ exact Hout.
           ++ unfold bar. apply RIncN_D1. exact Hcont.
        -- exact HPys.
        -- exact Hys.
Qed.

Lemma Producer_prefix_to_layer a x y z v xs p:
  (x >= y)%nat ->
  (y >= z)%nat ->
  (z >= 2)%nat ->
  (2 <= v <= z)%nat ->
  Producer (v :: xs) p ->
  Forall (fun s => (s <= v)%nat) xs ->
  exists r r3,
    Producer xs r /\
    RIncN 3 r r3 /\
    Producer xs r3 /\
    RIncPN (S ((y - 2) + 1))
      (D1 a :: D1 0 :: bar x :: bar y :: bar z :: p)
      (D1 (a + 4 * y + 2) :: D1 (2 * x + y - 2) ::
       D3 (2 * z) (2 * v - 3) :: r3).
Proof.
  intros Hxy Hyz Hz Hv HP Hxs.
  destruct (Producer_output1_exact v xs p (4 * y - 2)) as [r [Hp_to_r HPr]].
  - exact HP.
  - apply tick_budget_le_4y_minus2. lia.
  - destruct (Producer_RIncN_exists xs r 3 HPr) as [r3 [Hr_r3 HPr3]].
    exists r, r3.
    repeat split; try assumption.
    assert (Htail : RIncN (4 * y - 2) (bar z :: p) (bar z :: bar v :: r)).
    { unfold bar. apply RIncN_D1. exact Hp_to_r. }
    replace (4 * y - 2)%nat with (6 + 4 * (y - 2))%nat in Htail by lia.
    destruct (RIncN_split6 _ _ _ Htail) as
      [t1 [t2 [t3 [t4 [t5 [t6 [H1 [H2 [H3 [H4 [H5 [H6 Hrest]]]]]]]]]]]].
    econstructor.
    + unfold bar.
      replace (2 * y - 2)%nat with (2 + (2 * y - 4))%nat by lia.
      eapply RInc'1'; eauto.
    + eapply RIncPN_snoc.
      * replace (2 * y - 4)%nat with (2 * (y - 2) + 0)%nat by lia.
        apply RIncPN_D2_reduce.
        exact Hrest.
      * destruct (RIncN_split3 _ _ Hr_r3) as [s1 [s2 [G1 [G2 G3]]]].
        replace (a + 4 * y + 2)%nat with
          (4 + ((6 + a) + 4 * (y - 2)))%nat by lia.
        replace (2 * x + y - 2)%nat with
          ((2 + (2 * x - 2)) + (y - 2))%nat by lia.
        unfold bar.
        replace (2 * v - 2)%nat with (1 + (2 * v - 3))%nat by lia.
        replace (2 * z)%nat with (2 + (2 * z - 2))%nat by lia.
        replace (2 + (2 * z - 2) - 2)%nat with (2 * z - 2)%nat by lia.
        eapply RInc'2'; eauto.
Qed.

Lemma GoodP_round x:
  GoodP x ->
  exists n y,
    (1 <= n)%nat /\
    RIncPN n x y /\
    GoodP y.
Proof.
  unfold GoodP.
  intro HG.
  destruct HG as [a [x0 [y0 [z0 [v [xs [p HG]]]]]]].
  destruct HG as [Hx [Hxy [Hyz [Hz [Hv [HP Hxs]]]]]].
  subst x.
  destruct (Producer_prefix_to_layer a x0 y0 z0 v xs p) as
    [r [r3 [HPr [Hr_r3 [HPr3 Hprefix]]]]].
  - exact Hxy.
  - exact Hyz.
  - exact Hz.
  - exact Hv.
  - exact HP.
  - exact Hxs.
  - destruct (RIncN_D3_start_output3_active z0 v xs r3) as
      [x1 [y1 [z1 [w [ys [p1 [C
        [HC [Hx1 [Hx1y1 [Hy1z1 [Hz1 [Hw [Hout [HPw Hys]]]]]]]]]]]]]]].
    + lia.
    + exact HPr3.
    + exact Hxs.
    + set (B := (2 * x0 + y0 - 2)%nat).
  assert (HC4 : (C <= 4 * B)%nat).
  { subst B. lia. }
  destruct (Producer_RIncN_exists (w :: ys) p1 (4 * B - C) HPw) as
    [p2 [Hpad HPpad]].
  assert
    (Htail :
      RIncN (4 * B)
        (D3 (2 * z0) (2 * v - 3) :: r3)
        (bar x1 :: bar y1 :: bar z1 :: p2)).
  { replace (4 * B)%nat with (C + (4 * B - C))%nat at 1 by lia.
    eapply RIncN_trans.
    - exact Hout.
    - unfold bar.
      apply RIncN_D1. apply RIncN_D1. apply RIncN_D1.
      exact Hpad.
  }
  exists (S ((y0 - 2) + 1) + B)%nat.
  exists
    (D1 (a + 4 * y0 + 2 + 4 * B) :: D1 0 ::
     bar x1 :: bar y1 :: bar z1 :: p2).
  split; [lia|].
  split.
  * eapply RIncPN_trans.
    -- exact Hprefix.
    -- apply RIncPN_D1_reduce.
      exact Htail.
  * unfold GoodP.
    exists (a + 4 * y0 + 2 + 4 * B)%nat.
    exists x1.
    exists y1.
    exists z1.
    exists w.
    exists ys.
    exists p2.
    repeat split; try lia; try reflexivity; try assumption.
Qed.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1RD_0RD---_1LA1RB_1RE0LF_0LA0RD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation QR := B.
Notation QR' := E.
Notation QL := A.

Lemma RInc_spec x x':
  RInc x x' ->
  (forall l, l {{QR}}> toRC x -->* l <{{QL}} toRC x').
Proof.
  intro H.
  induction H; intros; cbn[toRC].
  all: repeat (es; er; follow).
Qed.

Definition S' x := 0inf <* <[1] {{QR}}> toRC x.

Lemma RInc'_spec x x':
  RInc' x x' ->
  S' x -->+
  S' x'.
Proof.
  unfold S'.
  intro H.
  induction H; intros; cbn[toRC].
  - eapply RInc_spec in H,H0,H1,H2.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1,H2.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1,H2,H3,H4.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1.
    repeat (es; er; follow).
Qed.

Lemma init:
  c0 -->*
  S' (init_state 48).
Proof.
  unfold init_state, init_tail, bar, S'.
  esx.
Qed.

Lemma RIncPN_spec_plus n x y:
  RIncPN n x y ->
  (1 <= n)%nat ->
  S' x -->+ S' y.
Proof.
  intro Hsteps.
  induction Hsteps as [x|n x y z Hstep Hrest IH]; intro Hpos.
  - lia.
  - destruct n as [|n'].
    + inversion Hrest; subst.
      apply RInc'_spec. exact Hstep.
    + eapply progress_trans.
      * apply RInc'_spec. exact Hstep.
      * apply IH. lia.
Qed.

Lemma GoodP_nonhalt x:
  GoodP x ->
  ~halts tm (S' x).
Proof.
  intro HG.
  eapply progress_nonhalt_cond
    with
      (A := {x : list RD | GoodP x})
      (i0 := exist _ x HG)
      (C := fun x => S' (proj1_sig x))
      (P := fun _ => True).
  - intros [x0 HG0] _.
    destruct (GoodP_round _ HG0) as [n [y [Hn [Hsteps HGy]]]].
    exists (exist _ y HGy).
    split; [|exact I].
    eapply RIncPN_spec_plus; eauto.
  - exact I.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (init_state 48)).
  - apply init.
  - apply GoodP_nonhalt.
    apply GoodP_init.
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RC0LD_0RF1RA_1RD0LE_0LB0RA_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation QR := C.
Notation QR' := D.
Notation QL := B.

Lemma RInc_spec x x':
  RInc x x' ->
  (forall l, l {{QR}}> toRC x -->* l <{{QL}} toRC x').
Proof.
  intro H.
  induction H; intros; cbn[toRC].
  all: repeat (es; er; follow).
Qed.

Definition S' x := 0inf <* <[1] {{QR}}> toRC x.

Lemma RInc'_spec x x':
  RInc' x x' ->
  S' x -->+
  S' x'.
Proof.
  unfold S'.
  intro H.
  induction H; intros; cbn[toRC].
  - eapply RInc_spec in H,H0,H1,H2.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1,H2.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1,H2,H3,H4.
    repeat (es; er; follow).
  - eapply RInc_spec in H,H0,H1.
    repeat (es; er; follow).
Qed.

Lemma init:
  c0 -->*
  S' (init_state 46).
Proof.
  unfold init_state, init_tail, bar, S'.
  esx.
Qed.

Lemma RIncPN_spec_plus n x y:
  RIncPN n x y ->
  (1 <= n)%nat ->
  S' x -->+ S' y.
Proof.
  intro Hsteps.
  induction Hsteps as [x|n x y z Hstep Hrest IH]; intro Hpos.
  - lia.
  - destruct n as [|n'].
    + inversion Hrest; subst.
      apply RInc'_spec. exact Hstep.
    + eapply progress_trans.
      * apply RInc'_spec. exact Hstep.
      * apply IH. lia.
Qed.

Lemma GoodP_nonhalt x:
  GoodP x ->
  ~halts tm (S' x).
Proof.
  intro HG.
  eapply progress_nonhalt_cond
    with
      (A := {x : list RD | GoodP x})
      (i0 := exist _ x HG)
      (C := fun x => S' (proj1_sig x))
      (P := fun _ => True).
  - intros [x0 HG0] _.
    destruct (GoodP_round _ HG0) as [n [y [Hn [Hsteps HGy]]]].
    exists (exist _ y HGy).
    split; [|exact I].
    eapply RIncPN_spec_plus; eauto.
  - exact I.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' (init_state 46)).
  - apply init.
  - apply GoodP_nonhalt.
    apply GoodP_init.
Qed.

End TM2.

