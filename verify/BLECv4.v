From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import String List Arith ZArith Lia ZifyNat.
Import ListNotations.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0RE_0RD0LA_1RE1RA_0LD1RF_0RB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation t := [1;0].
Notation u := [1;0;1].
Notation d := [1;1;0].
Notation w := [1;0;1;1;0].
Notation v := [1;1;0;1;0].
Notation hp := [((B,[0]),(C,[0]))].
Notation hq := [((B,[0]),(A,[0;0]))].
Notation hr := [((B,[0]),(A,[0;0;0;0]))].
Notation hi := [((B,<[0;1;1]),(C,[0;1;0]))].
Notation hc := [((B,[]),(A,[]))].
Definition P n r s := sideRLs tm (hp^^n) r s.
Definition I n r s := sideRLs tm (hi^^n) r s.

Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=500); reflexivity.

Lemma Pd : segRLs tm hp (hp^^2) d u.
Proof. finite_rule. Qed.
Lemma PdQP : segRLs tm hp (hp++hq) d [1;0;0;0].
Proof. finite_rule. Qed.
Lemma PdR : segRLs tm hp hr d (w++[1]).
Proof. finite_rule. Qed.
Lemma Pt : segRLs tm hp hi t t.
Proof. finite_rule. Qed.
Lemma Id : segRLs tm hi hp d d.
Proof. finite_rule. Qed.
Lemma Pw : segRLs tm hp hp w w.
Proof. finite_rule. Qed.
Lemma Iq : segRLs tm hi hq d (d++[1]).
Proof. finite_rule. Qed.
Lemma Pwq : segRLs tm hp hq w (w++[1]).
Proof. finite_rule. Qed.
Lemma Iv : segRLs tm hi hi v v.
Proof. finite_rule. Qed.
Lemma Pv : segRLs tm hp (hi^^2) v w.
Proof. finite_rule. Qed.
Lemma Pdw : segRLs tm hp (hp^^2) (d++w) (w++d).
Proof. finite_rule. Qed.
Lemma Icarry : segRLs tm hi hc [] [].
Proof. finite_rule. Qed.
Lemma Pcarry0 : segRLs tm hp hc [0;0] [0;0].
Proof. finite_rule. Qed.
Lemma Pcarry1 : segRLs tm hp hc t t.
Proof. finite_rule. Qed.
Lemma carry0 : segRLs tm hc [] [0;0] [1;0].
Proof. finite_rule. Qed.
Lemma carry1 : segRLs tm hc hc [1;0] [0;0].
Proof. finite_rule. Qed.
Lemma carry_bit0 : segRLs tm hc [] [0] [1].
Proof. finite_rule. Qed.

Lemma P_add a b r s z : P a r s -> P b s z -> P (a+b) r z.
Proof. unfold P; apply sideRLs_trans_add. Qed.
Lemma I_add a b r s z : I a r s -> I b s z -> I (a+b) r z.
Proof. unfold I; apply sideRLs_trans_add. Qed.
Lemma P_split a b r z : P (a+b) r z -> exists s, P a r s /\ P b s z.
Proof. unfold P; rewrite lpow_add; apply sideRLs_split. Qed.
Lemma I_split a b r z : I (a+b) r z -> exists s, I a r s /\ I b s z.
Proof. unfold I; rewrite lpow_add; apply sideRLs_split. Qed.

Lemma Pws n k : segRLs tm (hp^^n) (hp^^n) (w^^k) (w^^k).
Proof.
  induction k; [apply segRLs_nil|].
  cbn[lpow]; eapply segRLs_concat; [|exact IHk].
  apply segRLs_wall''; exact Pw.
Qed.
Lemma Ivs n k : segRLs tm (hi^^n) (hi^^n) (v^^k) (v^^k).
Proof.
  induction k; [apply segRLs_nil|].
  cbn[lpow]; eapply segRLs_concat; [|exact IHk].
  apply segRLs_wall''; exact Iv.
Qed.
Lemma Pts n : segRLs tm (hp^^n) (hi^^n) t t.
Proof. apply segRLs_wall''; exact Pt. Qed.
Lemma Ids n : segRLs tm (hi^^n) (hp^^n) d d.
Proof. apply segRLs_wall''; exact Id. Qed.

Lemma Pvs n k : segRLs tm (hp^^n) (hi^^(n*2))
  (v^^(n+k)) (w^^n++v^^k).
Proof.
  induction n; [constructor|].
  change (segRLs tm (hp++hp^^n) (hi^^2++hi^^(n*2))
    (v++v^^(n+k)) (w++(w^^n++v^^k))).
  eapply (segRLs_trans (w2:=w++v^^(n+k))).
  - eapply segRLs_concat; [exact Pv|apply Ivs].
  - eapply segRLs_concat; [|exact IHn].
    apply segRLs_wall''; exact Pw.
Qed.

Lemma P_w n k r s : P n r s -> P n (w^^k*>r) (w^^k*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply Pws|exact H]. Qed.
Lemma I_v n k r s : I n r s -> I n (v^^k*>r) (v^^k*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply Ivs|exact H]. Qed.
Lemma P_t n r s : I n r s -> P n (t*>r) (t*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply Pts|exact H]. Qed.
Lemma I_d n r s : P n r s -> I n (d*>r) (d*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [apply Ids|exact H]. Qed.
Lemma P_d r s : P 2 r s -> P 1 (d*>r) (u*>s).
Proof. intro H; eapply segRLs_sideRLs_concat; [exact Pd|exact H]. Qed.

(* G keeps both actual return contracts. Its added bit is not a head change. *)
Inductive G1 : side -> side -> Prop :=
| GP r s : P 1 r s -> G1 r s
| GQ r s : sideRLs tm hq r s -> G1 r (1>>s).
Inductive G : nat -> side -> side -> Prop :=
| G0 r : G 0 r r
| GS n r s z : G1 r s -> G n s z -> G (1+n) r z.

Lemma G_add a b r s z : G a r s -> G b s z -> G (a+b) r z.
Proof. intros H; induction H; intro Hz; [exact Hz|econstructor; eauto]. Qed.
Lemma G_w n r s : G n r s -> P n (w*>r) (w*>s).
Proof.
  intro H; induction H; [constructor|].
  eapply P_add with (a:=1%nat); [|exact IHG].
  destruct H.
  - eapply segRLs_sideRLs_concat; [exact Pw|exact H].
  - change (P 1 (w*>r) ((w++[1])*>s)).
    eapply segRLs_sideRLs_concat; [exact Pwq|exact H].
Qed.
Lemma G_d n r s : G n r s -> I n (d*>r) (d*>s).
Proof.
  intro H; induction H; [constructor|].
  eapply I_add with (a:=1%nat); [|exact IHG].
  destruct H.
  - eapply segRLs_sideRLs_concat; [exact Id|exact H].
  - change (I 1 (d*>r) ((d++[1])*>s)).
    eapply segRLs_sideRLs_concat; [exact Iq|exact H].
Qed.

Lemma P_G n r s : P n r s -> G n r s.
Proof.
  gen r; induction n; intros r H; [inverts H; constructor|].
  destruct (P_split 1 n r s H) as [z [H1 Hn]].
  econstructor; [apply GP, H1|apply IHn, Hn].
Qed.

Lemma column1 b r x s : I 2 r x -> G (1+b) x s ->
  exists z, P b (v*>r) z /\ P 1 (d*>z) (w*>d*>s).
Proof.
  intros Hi Hp.
  assert (H : P (1+(1+b)) (v*>r) (w*>s)).
  { eapply P_add with (a:=1%nat).
    - eapply segRLs_sideRLs_concat; [exact Pv|exact Hi].
    - exact (G_w _ _ _ Hp). }
  replace (1+(1+b)) with (b+2) in H by lia.
  destruct (P_split _ _ _ _ H) as [z [Hz H2]].
  exists z; split; [exact Hz|exact (P_d _ _ H2)].
Qed.

Lemma column_aux a b r x s : I (a*2) r x -> G (a+b) x s ->
  exists z, G b (v^^a*>r) z /\ G a (d*>z) (w^^a*>d*>s).
Proof.
  gen b r x s; induction a; intros b r x s Hi Hp.
  - inverts Hi; exists s; split; [exact Hp|constructor].
  - change (I (2+a*2) r x) in Hi.
    destruct (I_split _ _ _ _ Hi) as [y [Hy Hx]].
    replace (S a+b) with (a+(1+b)) in Hp by lia.
    destruct (IHa _ _ _ _ Hx Hp) as [z [Hz Hs]].
    destruct (column1 b _ _ _ (I_v 2 a _ _ Hy) Hz) as [z' [Hz' H1]].
    exists z'; split; [apply P_G, Hz'|].
    apply P_G; eapply P_add with (a:=1%nat); [exact H1|apply G_w, Hs].
Qed.

(* The order is P^c, insert 1, I^b, G^a. The frame absorbs the G returns. *)
Inductive Run (a b c:nat) (r s:side) : Prop :=
| run x y : P c r x -> I b (1>>x) y -> G a y s -> Run a b c r s.
Definition Suffix a b := Run a b 2.

Lemma column a b r s : Suffix (a+b) (a*2+1) r s ->
  Suffix a b (w^^a*>d*>r) (w^^a*>d*>s).
Proof.
  intros [x y Hp Hi Ha].
  replace (a*2+1) with (1+a*2) in Hi by lia.
  destruct (I_split _ _ _ _ Hi) as [z [H1 Hz]].
  destruct (column_aux _ _ _ _ _ Hz Ha) as [z' [Hb Ha']].
  eapply run with (x:=w^^a*>t*>z) (y:=d*>z').
  - apply P_w; eapply P_add with (a:=1%nat) (b:=1%nat).
    + apply P_d, Hp.
    + change (P 1 (t*>1>>x) (t*>z)); apply P_t, H1.
  - change (I b (1>>((t++d)^^a*>t*>z)) (d*>z')).
    rewrite lpow_rotate'; apply G_d, Hb.
  - exact Ha'.
Qed.

Lemma PdPd b r x s : P 2 r x -> I (1+b) (1>>x) s ->
  exists z, P b (d*>r) z /\ P 1 (d*>z) (w*>s).
Proof.
  intros Hp Hi.
  assert (H:P (1+(1+b)) (d*>r) (t*>s)).
  { eapply P_add with (a:=1%nat); [apply P_d, Hp|apply P_t, Hi]. }
  replace (1+(1+b)) with (b+2) in H by lia.
  destruct (P_split _ _ _ _ H) as [z [Hz H2]].
  exists z; split; [exact Hz|exact (P_d _ _ H2)].
Qed.

Lemma run_w_g a b c r x y z s : G c r x -> P 2 x y ->
  I (1+b) (1>>y) z -> G a z s -> Run (1+a) b c (w*>r) (w*>s).
Proof.
  intros Hg Hp Hi Ha.
  destruct (PdPd _ _ _ _ Hp Hi) as [z' [Hb H1]].
  eapply run with (x:=w*>x) (y:=d*>z').
  - apply G_w, Hg.
  - exact (I_d _ _ _ Hb).
  - apply P_G; eapply P_add with (a:=1%nat); [exact H1|apply G_w, Ha].
Qed.

Lemma run_w a b c r s : Run a (1+b) (c+2) r s ->
  Run (1+a) b c (w*>r) (w*>s).
Proof.
  intros [x y Hp Hi Ha].
  destruct (P_split _ _ _ _ Hp) as [z [Hc H2]].
  eapply run_w_g; [apply P_G, Hc|exact H2|exact Hi|exact Ha].
Qed.

Lemma run_ws j a b c r s : Run a (b+j) (c+j*2) r s ->
  Run (a+j) b c (w^^j*>r) (w^^j*>s).
Proof.
  gen b c; induction j; intros b c H.
  - applys_eq H; flia.
  - change (Run (a+S j) b c (w*>w^^j*>r) (w*>w^^j*>s)).
    replace (a+S j) with (1+(a+j)) by lia.
    apply run_w, IHj; applys_eq H; flia.
Qed.

Lemma column_partial a b j r s : j<=a -> Run (a-j) (b+j) (j*2+2) r s ->
  Suffix a b (w^^j*>r) (w^^j*>s).
Proof.
  intros Hj H; applys_eq (run_ws j (a-j) b 2 r s); try flia.
  applys_eq H; flia.
Qed.

Lemma column_early a b j r x y z s : 0<j -> j<=a ->
  G (j*2) r x -> P 2 x y -> I (b+j) (1>>y) z -> G (a-j) z s ->
  Suffix a b (w^^j*>r) (w^^j*>s).
Proof.
  intros Hj Ha Hg Hp Hi Hs; destruct j as [|j]; [lia|].
  change (Suffix a b (w*>w^^j*>r) (w*>w^^j*>s)); rewrite <-!lpow_shift'.
  apply column_partial; [lia|].
  applys_eq (run_w_g (a-S j) (b+j) (j*2+2) r x y z s); try flia.
  - applys_eq Hg; flia.
  - exact Hp.
  - applys_eq Hi; flia.
  - exact Hs.
Qed.

Inductive Inner j r s : Prop :=
| InnerP : P (j*2+2) r s -> Inner j r s
| InnerG x : 0<j -> G (j*2) r x -> P 2 x s -> Inner j r s.

Lemma inner_column a b j r x y s : j<=a -> Inner j r x ->
  I (b+j) (1>>x) y -> G (a-j) y s ->
  Suffix a b (w^^j*>r) (w^^j*>s).
Proof.
  intros Hj H Hi Hg; destruct H.
  - apply column_partial; [exact Hj|econstructor; eassumption].
  - eapply column_early; eassumption.
Qed.

Definition cfg r := 0inf {{C}}> [0;0;1;0]*>r.
Lemma root_step r s : P 1 r s -> cfg r -->+ cfg (1>>s).
Proof.
  intro H; unfold cfg; es; er.
  follow100 (sideRLs_1 _ _ _ _ _ H); cbn[to_DH_config]; es; er.
Qed.

Lemma root_base r s : Suffix 0 1 r s -> cfg (d*>d*>r) -->+ cfg (d*>d*>s).
Proof.
  intros [x y Hp Hi Ha]; inverts Ha.
  apply root_step, P_d.
  eapply P_add with (a:=1%nat) (b:=1%nat); [apply P_d, Hp|apply P_t, Hi].
Qed.

Inductive Frame : nat -> nat -> list Sym -> Prop :=
| Frame0 : Frame 0 1 (d++d)
| FrameS a b xs : Frame a b xs -> Frame (a+b) (a*2+1) (xs++w^^a++d).

Lemma Frame_phase a b xs : Frame a b xs ->
  (a=b /\ a mod 4=1%nat) \/ (b=a+1 /\ a mod 2=0%nat).
Proof.
  intro H; induction H; [right; split; reflexivity|].
  destruct IHFrame as [[He Hmod]|[He Hmod]]; [right|left]; split; lia.
Qed.

Lemma frame_step a b xs : Frame a b xs -> forall r s,
  Suffix a b r s -> cfg (xs*>r) -->+ cfg (xs*>s).
Proof.
  intro H; induction H; intros r s Hs.
  - apply root_base, Hs.
  - rewrite !Str_app_assoc; apply IHFrame, column, Hs.
Qed.

Inductive Num : nat -> side -> Prop :=
| Num0 : Num 0 0inf
| Num00 n r : Num n r -> Num (n*2) ([0;0]*>r)
| Num10 n r : Num n r -> Num (n*2+1) (t*>r).

Lemma carry_num n r : Num n r -> exists s,
  Num (1+n) s /\ sideRLs tm hc r s.
Proof.
  intro H; induction H.
  - exists (t*>0inf); split; [apply (Num10 0), Num0|es'].
  - exists (t*>r); split; [applys_eq (Num10 _ _ H); flia|].
    eapply segRLs_sideRLs_concat; [exact carry0|constructor].
  - destruct IHNum as [s [Hs Hc]].
    exists ([0;0]*>s); split; [applys_eq (Num00 _ _ Hs); flia|].
    eapply segRLs_sideRLs_concat; [exact carry1|exact Hc].
Qed.

Lemma I_num n r : Num n r -> exists s, Num (1+n) s /\ I 1 r s.
Proof.
  intro H; destruct (carry_num _ _ H) as [s [Hs Hc]]; exists s; split; [exact Hs|].
  exact (segRLs_sideRLs_concat Icarry Hc).
Qed.

Lemma P_num n r : Num n r -> exists s, Num (n+2) s /\ P 1 r s.
Proof.
  intro H; destruct H.
  - exists ([0;0;1;0]*>0inf); split; [apply (Num00 1), (Num10 0), Num0|unfold P; es'].
  - destruct (carry_num _ _ H) as [s [Hs Hc]].
    exists ([0;0]*>s); split; [applys_eq (Num00 _ _ Hs); flia|].
    eapply segRLs_sideRLs_concat; [exact Pcarry0|exact Hc].
  - destruct (carry_num _ _ H) as [s [Hs Hc]].
    exists (t*>s); split; [applys_eq (Num10 _ _ Hs); flia|].
    eapply segRLs_sideRLs_concat; [exact Pcarry1|exact Hc].
Qed.

Lemma I_nums k n r : Num n r -> exists s, Num (n+k) s /\ I k r s.
Proof.
  gen n r; induction k; intros n r H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (I_num _ _ H) as [s [Hs H1]].
    destruct (IHk _ _ Hs) as [z [Hz Hk]].
    exists z; split; [applys_eq Hz; flia|].
    eapply I_add with (a:=1%nat); eassumption.
Qed.

Lemma P_nums k n r : Num n r -> exists s, Num (n+k*2) s /\ P k r s.
Proof.
  gen n r; induction k; intros n r H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (P_num _ _ H) as [s [Hs H1]].
    destruct (IHk _ _ Hs) as [z [Hz Hk]].
    exists z; split; [applys_eq Hz; flia|].
    eapply P_add with (a:=1%nat); eassumption.
Qed.

Lemma G_nums k n r : Num n r -> exists s, Num (n+k*2) s /\ G k r s.
Proof.
  intro H; destruct (P_nums k _ _ H) as [s [Hs Hp]].
  exists s; split; [exact Hs|apply P_G, Hp].
Qed.

(* k pairs followed by a single high bit and the marker 10. *)
Inductive Word : nat -> nat -> list Sym -> Prop :=
| Word0 : Word 0 0 [0;1;0]
| Word1 : Word 0 1 d
| Word00 k n xs : Word k n xs -> Word (1+k) (n*2) ([0;0]++xs)
| Word10 k n xs : Word k n xs -> Word (1+k) (n*2+1) (t++xs).

Lemma Word_bound k n xs : Word k n xs -> n<2^(1+k).
Proof. intro H; induction H; cbn[Nat.add Nat.pow] in *; lia. Qed.

(* A finite counter ends in one bit, without the Word marker 10. *)
Inductive Bin : nat -> nat -> list Sym -> Prop :=
| Bin0 : Bin 0 0 [0]
| Bin1 : Bin 0 1 [1]
| Bin00 k n xs : Bin k n xs -> Bin (1+k) (n*2) ([0;0]++xs)
| Bin10 k n xs : Bin k n xs -> Bin (1+k) (n*2+1) (t++xs).

Lemma Bin_unique k n xs : Bin k n xs -> forall ys, Bin k n ys -> xs=ys.
Proof.
  intro H; induction H; intros ys H';
    inversion H' as [| |k' n' zs H0|k' n' zs H0]; subst; try lia; try reflexivity;
    f_equal; apply IHBin; applys_eq H0; flia.
Qed.

Lemma Bin_bound k n xs : Bin k n xs -> n<2^(1+k).
Proof. intro H; induction H; cbn[Nat.add Nat.pow] in *; lia. Qed.

Lemma Bin_zero k : Bin k 0 ([0;0]^^k++[0]).
Proof. induction k; [constructor|exact (Bin00 _ _ _ IHk)]. Qed.
Lemma Bin_top k : Bin k (2^k) ([0;0]^^k++[1]).
Proof.
  induction k; [constructor|].
  applys_eq (Bin00 _ _ _ IHk); cbn[Nat.pow]; flia.
Qed.
Lemma Bin_one k : 0<k -> Bin k 1 ([1]++[0;0]^^k).
Proof.
  destruct k; [lia|intro H].
  applys_eq (Bin10 _ _ _ (Bin_zero k)).
  rewrite lpow_rotate_list, app_nil_r; reflexivity.
Qed.

Lemma Bin_inc k n xs : Bin k n xs -> n+1<2^(1+k) -> exists ys,
  Bin k (n+1) ys /\ segRLs tm hc [] xs ys.
Proof.
  intro H; induction H; intro Hn.
  - exists [1]; split; [constructor|exact carry_bit0].
  - cbn in Hn; lia.
  - exists (t++xs); split; [apply Bin10, H|].
    eapply segRLs_concat; [exact carry0|constructor].
  - destruct IHBin as [ys [Hy Hc]]; [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists ([0;0]++ys); split; [applys_eq (Bin00 _ _ _ Hy); flia|].
    eapply segRLs_concat; [exact carry1|exact Hc].
Qed.

Lemma I_Bin k n xs : Bin k n xs -> n+1<2^(1+k) -> exists ys,
  Bin k (n+1) ys /\ segRLs tm hi [] xs ys.
Proof.
  intros H Hn; destruct (Bin_inc _ _ _ H Hn) as [ys [Hy Hc]].
  exists ys; split; [exact Hy|exact (segRLs_concat Icarry Hc)].
Qed.

Lemma P_Bin k n xs : Bin k n xs -> 0<k -> n+2<2^(1+k) -> exists ys,
  Bin k (n+2) ys /\ segRLs tm hp [] xs ys.
Proof.
  intro H; destruct H; intros Hk Hn; try lia.
  - destruct (Bin_inc _ _ _ H) as [ys [Hy Hc]];
      [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists ([0;0]++ys); split; [applys_eq (Bin00 _ _ _ Hy); flia|].
    exact (segRLs_concat Pcarry0 Hc).
  - destruct (Bin_inc _ _ _ H) as [ys [Hy Hc]];
      [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists (t++ys); split; [applys_eq (Bin10 _ _ _ Hy); flia|].
    exact (segRLs_concat Pcarry1 Hc).
Qed.

Lemma Bin_repeat h s k : (forall n xs, Bin k n xs -> n+s<2^(1+k) ->
  exists ys, Bin k (n+s) ys /\ segRLs tm h [] xs ys) ->
  forall i n xs, Bin k n xs -> n+i*s<2^(1+k) -> exists ys,
    Bin k (n+i*s) ys /\ segRLs tm (h^^i) [] xs ys.
Proof.
  intros Hstep i; induction i; intros n xs Hw Hn.
  - exists xs; split; [applys_eq Hw; flia|constructor].
  - destruct (Hstep _ _ Hw ltac:(nia)) as [ys [Hy H1]].
    destruct (IHi _ _ Hy ltac:(nia)) as [zs [Hz Hi]].
    exists zs; split; [applys_eq Hz; flia|].
    change (segRLs tm (h++h^^i) ([]++[]) xs zs).
    eapply segRLs_trans; eassumption.
Qed.

Lemma I_Bins k i n xs : Bin k n xs -> n+i<2^(1+k) -> exists ys,
  Bin k (n+i) ys /\ segRLs tm (hi^^i) [] xs ys.
Proof.
  replace (n+i) with (n+i*1) by lia; apply Bin_repeat, I_Bin.
Qed.
Lemma P_Bins k i n xs : Bin k n xs -> 0<k -> n+i*2<2^(1+k) -> exists ys,
  Bin k (n+i*2) ys /\ segRLs tm (hp^^i) [] xs ys.
Proof. intros Hw Hk Hn; apply (Bin_repeat hp 2 k); [intros; apply P_Bin; assumption|exact Hw|exact Hn]. Qed.

Lemma Word_inc k n xs : Word k n xs -> n+1<2^(1+k) -> exists ys,
  Word k (n+1) ys /\ segRLs tm hc [] xs ys.
Proof.
  intro H; induction H; intro Hn.
  - exists d; split; [constructor|finite_rule].
  - cbn in Hn; lia.
  - exists (t++xs); split; [apply Word10, H|].
    eapply segRLs_concat; [exact carry0|constructor].
  - destruct IHWord as [ys [Hy Hc]]; [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists ([0;0]++ys); split; [applys_eq (Word00 _ _ _ Hy); flia|].
    eapply segRLs_concat; [exact carry1|exact Hc].
Qed.

Lemma I_word_inc k n xs r : Word k n xs -> n+1<2^(1+k) -> exists ys,
  Word k (n+1) ys /\ I 1 (xs*>r) (ys*>r).
Proof.
  intros H Hn; destruct (Word_inc _ _ _ H Hn) as [ys [Hy Hc]].
  exists ys; split; [exact Hy|].
  apply (segRLs_sideRLs_concat Icarry).
  eapply segRLs_sideRLs_concat; [exact Hc|constructor].
Qed.

Definition one k := match k with
  | O => d
  | S k => t++[0;0]^^k++[0;1;0]
  end.

Lemma I_overflow_p k r s : P 1 r s ->
  I 1 (t^^k*>d*>r) (one k*>s).
Proof.
  intro H; destruct k as [|k]; [apply I_d, H|].
  unfold I; econstructor; [intros l; cbn[to_DH_config one]|constructor].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H).
  cbn[to_DH_config]; es' k & l s.
Qed.

Lemma I_overflow_q k r s : sideRLs tm hq r s ->
  I 1 (t^^k*>d*>r) (one k*>1>>s).
Proof.
  intro H; destruct k as [|k].
  - change (I 1 (d*>r) ((d++[1])*>s)).
    eapply segRLs_sideRLs_concat; [exact Iq|exact H].
  - unfold I; econstructor; [intros l; cbn[to_DH_config one]|constructor].
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H).
    cbn[to_DH_config]; es' k & l s.
Qed.

Lemma Q_overflow_p k r s : P 1 r s ->
  sideRLs tm hq ([0;0]*>t^^k*>d*>r) ([0;0]^^(1+k)*>t*>s).
Proof.
  intro H; econstructor; [intros l; cbn[to_DH_config]|constructor].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H).
  cbn[to_DH_config]; es' k & l s.
Qed.

Lemma Q_overflow_q k r s : sideRLs tm hq r s ->
  sideRLs tm hq ([0;0]*>t^^k*>d*>r) ([0;0]^^(1+k)*>t*>1>>s).
Proof.
  intro H; econstructor; [intros l; cbn[to_DH_config]|constructor].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H).
  cbn[to_DH_config]; es' k & l s.
Qed.

Lemma Q_R r s : sideRLs tm hq r ([0;0]*>s) -> sideRLs tm hr r s.
Proof.
  intro H; econstructor; [intro l; exact (sideRLs_1 _ _ _ _ _ H l)|constructor].
Qed.

Lemma P_d_second_Q r x s : P 1 r x -> sideRLs tm hq x s ->
  P 1 (d*>r) ([1;0;0;0]*>s).
Proof.
  intros Hp Hq; eapply segRLs_sideRLs_concat; [exact PdQP|].
  eapply sideRLs_trans; [exact Hp|exact Hq].
Qed.

Lemma Q_overflow k r s : G1 r s ->
  sideRLs tm hq ([0;0]*>t^^k*>d*>r) ([0;0]^^(1+k)*>t*>s).
Proof. intro H; destruct H; [apply Q_overflow_p|apply Q_overflow_q]; assumption. Qed.

Lemma Word_zero k : Word k 0 ([0;0]^^k++[0;1;0]).
Proof. induction k; [constructor|exact (Word00 _ _ _ IHk)]. Qed.
Lemma Word_one k : Word k 1 (one k).
Proof. destruct k; [constructor|exact (Word10 _ _ _ (Word_zero k))]. Qed.
Lemma Word_max k n xs : Word k n xs -> n+1=2^(1+k) -> xs=t^^k++d.
Proof.
  intro H; induction H; intro Hn; cbn[Nat.add Nat.pow] in Hn.
  - lia.
  - reflexivity.
  - lia.
  - cbn[lpow]; rewrite IHWord; [reflexivity|cbn[Nat.add Nat.pow]; lia].
Qed.

Lemma Word_before_Q k n xs : Word (1+k) n xs -> n+2=2^(2+k) ->
  xs=[0;0]++t^^k++d.
Proof.
  intros H He; inversion H as [| |k' n' ys Hy|k' n' ys Hy]; subst;
    cbn[Nat.add Nat.pow] in He; try lia.
  rewrite (Word_max _ _ _ Hy ltac:(cbn[Nat.add Nat.pow]; lia)); reflexivity.
Qed.

Lemma I_overflow k r s : G1 r s -> I 1 (t^^k*>d*>r) (one k*>s).
Proof. intro H; destruct H; [apply I_overflow_p|apply I_overflow_q]; assumption. Qed.

Lemma P_word_inc k n xs r : Word k n xs -> 0<k -> n+2<2^(1+k) -> exists ys,
  Word k (n+2) ys /\ P 1 (xs*>r) (ys*>r).
Proof.
  intro H; destruct H; intros Hk Hn; try lia.
  - destruct (Word_inc _ _ _ H) as [ys [Hy Hc]];
      [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists ([0;0]++ys); split; [applys_eq (Word00 _ _ _ Hy); flia|].
    apply (segRLs_sideRLs_concat Pcarry0).
    eapply segRLs_sideRLs_concat; [exact Hc|constructor].
  - destruct (Word_inc _ _ _ H) as [ys [Hy Hc]];
      [cbn[Nat.add Nat.pow] in Hn |- *; lia|].
    exists (t++ys); split; [applys_eq (Word10 _ _ _ Hy); flia|].
    apply (segRLs_sideRLs_concat Pcarry1).
    eapply segRLs_sideRLs_concat; [exact Hc|constructor].
Qed.

Lemma P_word_linear k i n xs r : Word k n xs -> 0<k -> n+i*2<2^(1+k) ->
  exists ys, Word k (n+i*2) ys /\ P i (xs*>r) (ys*>r).
Proof.
  gen n xs; induction i; intros n xs Hw Hk Hbound.
  - exists xs; split; [applys_eq Hw; flia|constructor].
  - destruct (P_word_inc _ _ _ r Hw Hk ltac:(lia)) as [ys [Hy Hp]].
    destruct (IHi _ _ Hy Hk ltac:(lia)) as [zs [Hz Hrest]].
    exists zs; split; [applys_eq Hz; flia|].
    eapply P_add with (a:=1%nat); eassumption.
Qed.

Lemma G_word_odd k r s : G1 r s ->
  G1 (t^^(1+k)*>d*>r) ((t++one k)*>s).
Proof.
  intro H; apply GP, P_t, I_overflow, H.
Qed.

Lemma G_word_even k r s : G1 r s ->
  G1 ([0;0]*>t^^k*>d*>r) (one (1+k)*>s).
Proof.
  intro H; cbn [Nat.add one]; rewrite !Str_app_assoc.
  change (G1 ([0;0]*>t^^k*>d*>r)
    (1>>0>>([0;0]^^k*>0>>t*>s))).
  rewrite lpow_rotate.
  apply GQ; destruct H; [apply Q_overflow_p|apply Q_overflow_q]; assumption.
Qed.

Lemma G_split a b r s : G (a+b) r s -> exists z, G a r z /\ G b z s.
Proof.
  gen r; induction a; intros r H.
  - exists r; split; [constructor|exact H].
  - inversion H as [|n r' z s' H1 Hn]; subst.
    destruct (IHa _ Hn) as [z' [Ha Hb]].
    exists z'; split; [econstructor; eassumption|exact Hb].
Qed.
Lemma G_single r s : G1 r s -> G 1 r s.
Proof. intro H; econstructor; [exact H|constructor]. Qed.
Lemma G_unone r s : G 1 r s -> G1 r s.
Proof.
  intro H; inversion H as [|n r' z s' H1 Hn]; subst; inverts Hn; exact H1.
Qed.

Inductive ICounter k : nat -> nat -> nat -> Prop :=
| ICinc n : n+1<2^(1+k) -> ICounter k n (n+1) 0
| ICov n : n+1=2^(1+k) -> ICounter k n 1 1.

Lemma I_counter k n n' c xs r s : Word k n xs -> ICounter k n n' c ->
  G c r s -> exists ys, Word k n' ys /\ I 1 (xs*>r) (ys*>s).
Proof.
  intros Hw Hc Hg; destruct Hc.
  - inverts Hg; apply I_word_inc; assumption.
  - exists (one k); split; [apply Word_one|].
    rewrite (Word_max _ _ _ Hw H), Str_app_assoc.
    apply I_overflow, G_unone, Hg.
Qed.

Inductive GCounter k : nat -> nat -> nat -> Prop :=
| GCinc n : n+2<2^(1+k) -> GCounter k n (n+2) 0
| GCev n : n+2=2^(1+k) -> GCounter k n 1 1
| GCod n : n+1=2^(1+k) -> GCounter k n 3 1.

Lemma G_counter k n n' c xs r s : Word k n xs -> 0<k -> GCounter k n n' c ->
  G c r s -> exists ys, Word k n' ys /\ G1 (xs*>r) (ys*>s).
Proof.
  intros Hw Hk Hc Hg; destruct Hc.
  - inverts Hg; destruct (P_word_inc _ _ _ s Hw Hk H) as [ys [Hy Hp]].
    exists ys; split; [exact Hy|apply GP, Hp].
  - destruct Hw; try lia.
    + assert (En:n+1=2^(1+k)) by (cbn[Nat.add Nat.pow] in H |- *; lia).
      exists (one (1+k)); split; [apply Word_one|].
      rewrite (Word_max _ _ _ Hw En), !Str_app_assoc.
      apply G_word_even, G_unone, Hg.
    + cbn[Nat.add Nat.pow] in H; lia.
  - destruct k as [|k]; [lia|].
    exists (t++one k); split; [exact (Word10 _ _ _ (Word_one k))|].
    rewrite (Word_max _ _ _ Hw H), !Str_app_assoc.
    apply G_word_odd, G_unone, Hg.
Qed.

Lemma GCounter_odd k n m c : GCounter k n m c -> n mod 2=1%nat -> m mod 2=1%nat.
Proof. intro H; destruct H; cbn[Nat.add Nat.pow] in *; lia. Qed.

Lemma P_counter k n n' c xs r s : Word k n xs -> 0<k -> n mod 2=1%nat ->
  GCounter k n n' c -> G c r s ->
  exists ys, Word k n' ys /\ P 1 (xs*>r) (ys*>s).
Proof.
  intros Hw Hk Hodd Hc Hg; destruct Hc.
  - inverts Hg; apply P_word_inc; assumption.
  - cbn[Nat.add Nat.pow] in H; lia.
  - destruct k as [|k]; [lia|].
    exists (t++one k); split; [exact (Word10 _ _ _ (Word_one k))|].
    rewrite (Word_max _ _ _ Hw H), !Str_app_assoc.
    apply P_t, I_overflow, G_unone, Hg.
Qed.

(* The last index is exactly the number of calls sent to the next block. *)
Inductive CounterRun (step:nat->nat->nat->Prop) : nat -> nat -> nat -> nat -> Prop :=
| Counter0 n : CounterRun step 0 n n 0
| CounterS i n m z c d : step n m c -> CounterRun step i m z d ->
    CounterRun step (1+i) n z (c+d).

Lemma CounterRun_split step i j n m c : CounterRun step (i+j) n m c ->
  exists z c0 c1, c=c0+c1 /\
    CounterRun step i n z c0 /\ CounterRun step j z m c1.
Proof.
  gen n c; induction i; intros n c H.
  - exists n, 0%nat, c; repeat split; [constructor|exact H].
  - inversion H as [|i' n' z m' c0 c1 H0 H1]; subst.
    destruct (IHi _ _ H1) as [x [c2 [c3 [He [H2 H3]]]]].
    exists x, (c0+c2), c3; repeat split; [lia|econstructor; eassumption|exact H3].
Qed.

Lemma CounterRun_add step i j n m z c e : CounterRun step i n m c ->
  CounterRun step j m z e -> CounterRun step (i+j) n z (c+e).
Proof.
  intro H; induction H; intro Hz; [exact Hz|].
  replace (c+d+e) with (c+(d+e)) by lia; econstructor; eauto.
Qed.

Lemma I_counter_run k i n m c xs r s : Word k n xs ->
  CounterRun (ICounter k) i n m c -> G c r s ->
  exists ys, Word k m ys /\ I i (xs*>r) (ys*>s).
Proof.
  intros Hw Hc; revert xs Hw r s; induction Hc; intros xs Hw r s Hg.
  - inverts Hg; exists xs; split; [exact Hw|constructor].
  - destruct (G_split _ _ _ _ Hg) as [z' [Hg1 Hd]].
    destruct (I_counter _ _ _ _ _ _ _ Hw H Hg1) as [ys [Hy Hi]].
    destruct (IHHc _ Hy _ _ Hd) as [zs [Hz Hrest]].
    exists zs; split; [exact Hz|eapply I_add; eassumption].
Qed.

Lemma G_counter_run k i n m c xs r s : Word k n xs -> 0<k ->
  CounterRun (GCounter k) i n m c -> G c r s ->
  exists ys, Word k m ys /\ G i (xs*>r) (ys*>s).
Proof.
  intros Hw Hk Hc; revert xs Hw r s; induction Hc; intros xs Hw r s Hg.
  - inverts Hg; exists xs; split; [exact Hw|constructor].
  - destruct (G_split _ _ _ _ Hg) as [z' [Hg1 Hd]].
    destruct (G_counter _ _ _ _ _ _ _ Hw Hk H Hg1) as [ys [Hy Hi]].
    destruct (IHHc _ Hy _ _ Hd) as [zs [Hz Hrest]].
    exists zs; split; [exact Hz|econstructor; eassumption].
Qed.

Lemma P_counter_run k i n m c xs r s : Word k n xs -> 0<k -> n mod 2=1%nat ->
  CounterRun (GCounter k) i n m c -> G c r s ->
  exists ys, Word k m ys /\ P i (xs*>r) (ys*>s).
Proof.
  intros Hw Hk Hodd Hc; revert xs Hw Hodd r s.
  induction Hc; intros xs Hw Hodd r s Hg.
  - inverts Hg; exists xs; split; [exact Hw|constructor].
  - destruct (G_split _ _ _ _ Hg) as [z' [Hg1 Hd]].
    destruct (P_counter _ _ _ _ _ _ _ Hw Hk Hodd H Hg1) as [ys [Hy Hi]].
    destruct (IHHc _ Hy (GCounter_odd _ _ _ _ H Hodd) _ _ Hd) as [zs [Hz Hrest]].
    exists zs; split; [exact Hz|eapply P_add; eassumption].
Qed.

Lemma ICounter_total k n : n<2^(1+k) -> exists m c,
  ICounter k n m c /\ m<2^(1+k).
Proof.
  intro H; destruct (lt_dec (n+1) (2^(1+k))).
  - exists (n+1), 0%nat; split; [constructor|]; assumption.
  - exists 1%nat, 1%nat; split; [apply ICov; lia|cbn[Nat.add Nat.pow]; lia].
Qed.

Lemma GCounter_total k n : 0<k -> n<2^(1+k) -> exists m c,
  GCounter k n m c /\ m<2^(1+k).
Proof.
  intros Hk H; destruct (lt_dec (n+2) (2^(1+k))).
  - exists (n+2), 0%nat; split; [constructor|]; assumption.
  - destruct (Nat.eq_dec (n+2) (2^(1+k))).
    + exists 1%nat, 1%nat; split; [apply GCev; assumption|cbn[Nat.add Nat.pow]; lia].
    + exists 3%nat, 1%nat; split; [apply GCod; lia|].
      destruct k; [lia|cbn[Nat.add Nat.pow]; lia].
Qed.

Lemma CounterRun_total step bound :
  (forall n, n<bound -> exists m c, step n m c /\ m<bound) ->
  forall i n, n<bound -> exists m c, CounterRun step i n m c /\ m<bound.
Proof.
  intros Hstep i; induction i; intros n Hn.
  - exists n, 0%nat; split; [constructor|exact Hn].
  - destruct (Hstep n Hn) as [m [c [Hc Hm]]].
    destruct (IHi m Hm) as [z [d [Hd Hz]]].
    exists z, (c+d); split; [econstructor; eassumption|exact Hz].
Qed.

Inductive Tail : side -> Prop :=
| TailNum n r : Num n r -> Tail r
| TailWord k n xs r : 0<k -> Word k n xs -> Tail r -> Tail (xs*>r).

Lemma G_total r : Tail r -> forall i, exists s, Tail s /\ G i r s.
Proof.
  intro H; induction H; intro i.
  - destruct (G_nums i _ _ H) as [s [Hs Hg]].
    exists s; split; [econstructor; exact Hs|exact Hg].
  - destruct (CounterRun_total _ _ (fun n => GCounter_total k n H) i n (Word_bound _ _ _ H0))
      as [m [c [Hc Hm]]].
    destruct (IHTail c) as [s [Hs Hg]].
    destruct (G_counter_run _ _ _ _ _ _ _ _ H0 H Hc Hg) as [ys [Hy Hrun]].
    exists (ys*>s); split; [econstructor; eassumption|exact Hrun].
Qed.

Lemma I_total r : Tail r -> forall i, exists s, Tail s /\ I i r s.
Proof.
  intro H; destruct H; intro i.
  - destruct (I_nums i _ _ H) as [s [Hs Hi]].
    exists s; split; [econstructor; exact Hs|exact Hi].
  - destruct (CounterRun_total _ _ (ICounter_total k) i n (Word_bound _ _ _ H0))
      as [m [c [Hc Hm]]].
    destruct (G_total _ H1 c) as [s [Hs Hg]].
    destruct (I_counter_run _ _ _ _ _ _ _ _ H0 Hc Hg) as [ys [Hy Hrun]].
    exists (ys*>s); split; [econstructor; eassumption|exact Hrun].
Qed.

Lemma ICounter_balance k n m c : ICounter k n m c ->
  m+c*(2^(1+k)-1)=n+1.
Proof. intro H; destruct H; lia. Qed.

Lemma ICounterRun_balance k i n m c : CounterRun (ICounter k) i n m c ->
  m+c*(2^(1+k)-1)=n+i.
Proof.
  intro H; induction H; [lia|].
  pose proof (ICounter_balance _ _ _ _ H); nia.
Qed.

Lemma ICounterRun_positive k i n m c : CounterRun (ICounter k) i n m c ->
  0<n -> 0<m.
Proof. intro H; induction H; intro Hn; [exact Hn|apply IHCounterRun; destruct H; lia]. Qed.

Lemma ICounterRun_bound k i n m c : CounterRun (ICounter k) i n m c ->
  n<2^(1+k) -> m<2^(1+k).
Proof.
  intro H; induction H; intro Hn; [exact Hn|apply IHCounterRun].
  destruct H; [assumption|cbn[Nat.add Nat.pow]; lia].
Qed.

Lemma ICounterRun_linear k i n m c : CounterRun (ICounter k) i n m c ->
  n+i<2^(1+k) -> m=n+i /\ c=0%nat.
Proof. intro H; induction H; intro Hbound; [split; lia|destruct H; lia]. Qed.

Definition phi n := n+n mod 2-1.

Lemma phi_odd n : phi (n*2+1)=n*2+1.
Proof. unfold phi; lia. Qed.
Lemma phi_bounds n : 0<n -> 0<phi n /\ phi n<=n /\ n<=phi n+1.
Proof. unfold phi; lia. Qed.

Ltac counter_arith := zify;
  repeat match goal with H : (_ /\ ?x = ?v) \/ (_ /\ ?x = 0%Z) |- _ =>
    assert (x=v) by lia; clear H; subst x end; nia.

Lemma GCounter_positive k n m c : GCounter k n m c -> 0<m.
Proof. intro H; destruct H; lia. Qed.

Lemma GCounter_balance k n m c : 0<k -> 0<n -> GCounter k n m c ->
  phi m+c*((2^k-1)*2)=phi n+2.
Proof.
  intros Hk Hn H; destruct H; unfold phi; cbn[Nat.add Nat.pow Nat.mul] in *; lia.
Qed.

Lemma GCounterRun_balance k i n m c : CounterRun (GCounter k) i n m c ->
  0<k -> 0<n -> phi m+c*((2^k-1)*2)=phi n+i*2.
Proof.
  intro H; induction H; intros Hk Hn; [lia|].
  specialize (IHCounterRun Hk (GCounter_positive _ _ _ _ H)).
  pose proof (GCounter_balance _ _ _ _ Hk Hn H); nia.
Qed.

Lemma GCounterRun_positive k i n m c : CounterRun (GCounter k) i n m c ->
  0<n -> 0<m.
Proof.
  intro H; induction H; intro Hn; [exact Hn|].
  apply IHCounterRun, (GCounter_positive _ _ _ _ H).
Qed.

Lemma GCounterRun_linear k i n m c : CounterRun (GCounter k) i n m c ->
  n+i*2<2^(1+k) -> m=n+i*2 /\ c=0%nat.
Proof.
  intro H; induction H; intro Hbound; [split; lia|].
  destruct H; lia.
Qed.

Lemma GCounterRun_even k i n m c : CounterRun (GCounter k) i n m c ->
  m mod 2=0%nat -> c=0%nat /\ m=n+i*2 /\ n mod 2=0%nat.
Proof.
  intro H; induction H; intro Hm; [repeat split; lia|].
  destruct (IHCounterRun Hm) as [Hc [Hz Hn]].
  destruct H; repeat split; lia.
Qed.

Lemma GCounterRun_bound k i n m c : CounterRun (GCounter k) i n m c ->
  0<k -> n<2^(1+k) -> m<2^(1+k).
Proof.
  intro H; induction H; intros Hk Hn; [exact Hn|].
  apply IHCounterRun; [exact Hk|].
  destruct H; [exact H|cbn[Nat.add Nat.pow]; lia|].
  destruct k; [lia|cbn[Nat.add Nat.pow]; lia].
Qed.

Lemma GCounterRun_saturated k i n m c : CounterRun (GCounter k) i n m c ->
  0<k -> n<2^(1+k) -> 2^(1+k)<=n+i*2 -> m mod 2=1%nat.
Proof.
  intros H Hk Hn Hi; pose proof (GCounterRun_bound _ _ _ _ _ H Hk Hn).
  destruct (Nat.eq_dec (m mod 2) 0%nat); [|lia].
  destruct (GCounterRun_even _ _ _ _ _ H e) as [_ [E _]]; lia.
Qed.

Lemma GCounterRun_odd k i n m c : CounterRun (GCounter k) i n m c ->
  n mod 2=1%nat -> m mod 2=1%nat.
Proof.
  intro H; induction H; intro Hn; [exact Hn|].
  apply IHCounterRun, (GCounter_odd _ _ _ _ H Hn).
Qed.

Lemma GCounterRun_three k i n m c : CounterRun (GCounter k) i n m c ->
  0<i -> n mod 2=1%nat -> 3<=m.
Proof.
  intro H; induction H; intros Hi Hn; [lia|].
  destruct i.
  - inversion H0; subst; destruct H; cbn[Nat.add Nat.pow] in *; lia.
  - apply IHCounterRun; [lia|eapply GCounter_odd; eassumption].
Qed.

(* A Q return may occur only in the early batch absorbed by a retained w. *)
Lemma counter_inner k j n m c xs r s : Word k n xs -> 0<k ->
  (n mod 2=1%nat \/ 2^(1+k)<=n+j*4) ->
  CounterRun (GCounter k) (j*2+2) n m c -> G c r s ->
  exists ys, Word k m ys /\ Inner j (xs*>r) (ys*>s).
Proof.
  intros Hw Hk [Hodd|Hsat] Hc Hg.
  - destruct (P_counter_run _ _ _ _ _ _ _ _ Hw Hk Hodd Hc Hg) as [ys [Hy Hp]].
    exists ys; split; [exact Hy|constructor; exact Hp].
  - destruct (CounterRun_split _ (j*2) 2 _ _ _ Hc)
      as [z [c0 [c1 [He [H0 H1]]]]]; subst c.
    destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg1]].
    destruct (G_counter_run _ _ _ _ _ _ _ _ Hw Hk H0 Hg0) as [zs [Hz Hgz]].
    assert (Hodd:z mod 2=1%nat).
    { eapply GCounterRun_saturated; [exact H0|exact Hk|eapply Word_bound; exact Hw|lia]. }
    destruct (P_counter_run _ _ _ _ _ _ _ _ Hz Hk Hodd H1 Hg1) as [ys [Hy Hp]].
    exists ys; split; [exact Hy|].
    eapply InnerG; [pose proof (Word_bound _ _ _ Hw); nia|exact Hgz|exact Hp].
Qed.

Lemma Word_odd_inv k n xs : Word (1+k) (n*2+1) xs ->
  exists ys, Word k n ys /\ xs=t++ys.
Proof.
  intro H; inversion H; subst; try lia.
  eexists; split; [applys_eq H2; flia|reflexivity].
Qed.

Lemma counter_inner_phase k j n m c : 0<k -> n<2^(1+k) ->
  (n mod 2=1%nat \/ 2^(1+k)<=n+j*4) ->
  CounterRun (GCounter k) (j*2+2) n m c -> m mod 2=1%nat /\ 3<=m.
Proof.
  intros Hk Hn [Hodd|Hsat] Hc.
  - split; [eapply GCounterRun_odd|eapply GCounterRun_three]; eauto; lia.
  - destruct (CounterRun_split _ (j*2) 2 _ _ _ Hc)
      as [z [c0 [c1 [He [H0 H1]]]]].
    assert (Hodd:z mod 2=1%nat).
    { eapply GCounterRun_saturated; eauto; lia. }
    split; [eapply GCounterRun_odd|eapply GCounterRun_three]; eauto; lia.
Qed.

Lemma descent_boundary a b fs k n u z c0 c1 xs r s :
  Frame a b fs -> Word (1+k) n xs -> 0<k ->
  (n mod 2=1%nat \/ 2^(1+(1+k))<=n+a*4) ->
  CounterRun (GCounter (1+k)) (a*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter k) (b+a) u z c1 -> G (c0+c1) r s ->
  exists ys, Word k z ys /\
    cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>ys*>s).
Proof.
  intros Hf Hw Hk Hguard H0 H1 Hg.
  destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg1]].
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) Hguard H0 Hg0)
    as [xs0 [Hw0 Hin]].
  destruct (Word_odd_inv _ _ _ Hw0) as [ys0 [Hy0 E0]]; subst xs0.
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy0 Hk H1 Hg1) as [ys [Hy Hrun]].
  exists ys; split; [exact Hy|].
  rewrite !Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hrun|].
  replace (a-a) with 0%nat by lia; constructor.
Qed.

Lemma descent_inside a b j fs k n u x y z c0 c1 c2 c3 xs r s :
  Frame a b fs -> j<a -> Word (2+k) n xs -> 0<k ->
  (n mod 2=1%nat \/ 2^(1+(2+k))<=n+j*4) -> x mod 2=1%nat ->
  CounterRun (GCounter (2+k)) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter (1+k)) (b+j) u x c1 ->
  CounterRun (GCounter (1+k)) 2 x (y*2+1) c2 ->
  CounterRun (GCounter k) (a-j-1) y z c3 ->
  G (c0+(c1+(c2+c3))) r s ->
  exists ys, Word k z ys /\
    cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>ys*>s).
Proof.
  intros Hf Hj Hw Hk Hguard Hodd H0 H1 H2 H3 Hg.
  destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg']].
  destruct (G_split _ _ _ _ Hg') as [r1 [Hg1 Hg'']].
  destruct (G_split _ _ _ _ Hg'') as [r2 [Hg2 Hg3]].
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) Hguard H0 Hg0)
    as [xs0 [Hw0 Hin]].
  destruct (Word_odd_inv _ _ _ Hw0) as [ys0 [Hy0 E0]]; subst xs0.
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy0 ltac:(lia) H1 Hg1)
    as [xs1 [Hw1 Hrun1]].
  destruct (P_counter_run _ _ _ _ _ _ _ _ Hw1 ltac:(lia) Hodd H2 Hg2)
    as [xs2 [Hw2 Hrun2]].
  destruct (Word_odd_inv _ _ _ Hw2) as [ys2 [Hy2 E2]]; subst xs2.
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy2 Hk H3 Hg3) as [ys [Hy Hrun3]].
  exists ys; split; [exact Hy|].
  rewrite (lpow_add _ j 1), Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hrun1|].
  replace (a-j) with (1+(a-j-1)) by lia.
  eapply G_add with (s:=w*>ys2*>r2).
  - apply P_G, P_d, Hrun2.
  - apply P_G, G_w, Hrun3.
Qed.

(* These identities count the complete suffix, not just its first word. *)
Lemma descent_boundary_balance a b k n u z c0 c1 q :
  0<k -> 0<n -> 0<u ->
  CounterRun (GCounter (1+k)) (a*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter k) (b+a) u z c1 ->
  (phi z+(2^k-1)*(q+(c0+c1)*2))*2+1+q+c0*2+(u-phi u)*2 =
    phi n+(2^(1+k)-1)*q+(a*2+b+1)*4.
Proof.
  intros Hk Hn Hu H0 H1.
  pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) Hn) as E0.
  pose proof (GCounterRun_balance _ _ _ _ _ H1 Hk Hu) as E1.
  pose proof (phi_bounds _ Hu).
  rewrite phi_odd in E0; cbn[Nat.add Nat.pow] in *; nia.
Qed.

Lemma descent_inside_balance a b j k n u x y z c0 c1 c2 c3 q :
  j<a -> 0<k -> 0<n -> 0<u -> 0<y ->
  CounterRun (GCounter (2+k)) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter (1+k)) (b+j) u x c1 ->
  CounterRun (GCounter (1+k)) 2 x (y*2+1) c2 ->
  CounterRun (GCounter k) (a-j-1) y z c3 ->
  (phi z+(2^k-1)*(q+(c0+c1+c2+c3)*2))*4+
    3+q*3+c0*6+(c1+c2)*4+(u-phi u)*2+(y-phi y)*4 =
    phi n+(2^(2+k)-1)*q+(a*2+b+1)*4.
Proof.
  intros Hj Hk Hn Hu Hy H0 H1 H2 H3.
  pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) Hn) as E0.
  pose proof (GCounterRun_balance _ _ _ _ _ H1 ltac:(lia) Hu) as E1.
  pose proof (GCounterRun_balance _ _ _ _ _ H2 ltac:(lia)
    (GCounterRun_positive _ _ _ _ _ H1 Hu)) as E2.
  pose proof (GCounterRun_balance _ _ _ _ _ H3 Hk Hy) as E3.
  pose proof (phi_bounds _ Hu); pose proof (phi_bounds _ Hy).
  assert (Hpow:0<2^k) by lia.
  rewrite phi_odd in E0, E2; cbn[Nat.add Nat.pow] in *.
  counter_arith.
Qed.

Lemma descent_boundary_calls a b k n u z c0 c1 L :
  0<k -> 0<n -> 0<u -> 0<z -> z<2^(1+k) -> 2<=L ->
  (a*2+b+1)*4=2^(2+k)*L ->
  CounterRun (GCounter (1+k)) (a*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter k) (b+a) u z c1 -> L<=c0+c1.
Proof.
  intros Hk Hn Hu Hz Hzb HL Hsize H0 H1.
  pose proof (descent_boundary_balance _ _ _ _ _ _ _ _ 0 Hk Hn Hu H0 H1) as E.
  pose proof (phi_bounds _ Hn); pose proof (phi_bounds _ Hu); pose proof (phi_bounds _ Hz).
  cbn[Nat.add Nat.pow] in *; counter_arith.
Qed.

Lemma descent_inside_calls a b j k n u x y z c0 c1 c2 c3 L :
  j<a -> 0<k -> 0<n -> 0<u -> 0<y -> 0<z -> z<2^(1+k) -> 4<=L ->
  (a*2+b+1)*4=2^(3+k)*L ->
  CounterRun (GCounter (2+k)) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter (1+k)) (b+j) u x c1 ->
  CounterRun (GCounter (1+k)) 2 x (y*2+1) c2 ->
  CounterRun (GCounter k) (a-j-1) y z c3 -> L<=c0+c1+c2+c3.
Proof.
  intros Hj Hk Hn Hu Hy Hz Hzb HL Hsize H0 H1 H2 H3.
  pose proof (descent_inside_balance _ _ _ _ _ _ _ _ _ _ _ _ _ 0
    Hj Hk Hn Hu Hy H0 H1 H2 H3) as E.
  pose proof (phi_bounds _ Hn); pose proof (phi_bounds _ Hu).
  pose proof (phi_bounds _ Hy); pose proof (phi_bounds _ Hz).
  cbn[Nat.add Nat.pow] in *; counter_arith.
Qed.

Lemma counter_inner_total k j n : 0<k -> n<2^(1+k) ->
  (n mod 2=1%nat \/ 2^(1+k)<=n+j*4) ->
  exists u c, 0<u /\ u<2^k /\
    CounterRun (GCounter k) (j*2+2) n (u*2+1) c.
Proof.
  intros Hk Hn Hguard.
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk) (j*2+2) n Hn)
    as [m [c [Hc Hm]]].
  destruct (counter_inner_phase _ _ _ _ _ Hk Hn Hguard Hc) as [Hodd Hthree].
  assert (Em:m=m/2*2+1) by lia.
  exists (m/2), c; repeat split; [lia|cbn[Nat.add Nat.pow] in Hm; lia|].
  rewrite <-Em; exact Hc.
Qed.

Lemma Num_zero n r : Num n r -> n=0%nat -> r=0inf.
Proof.
  intro H; induction H; intro Hn; [reflexivity| |lia].
  rewrite IHNum by lia; cbn; repeat rewrite <-const_unfold; reflexivity.
Qed.

Lemma Num_one n r : Num n r -> n=1%nat -> r=t*>0inf.
Proof.
  intro H; destruct H; intro Hn; try lia.
  rewrite (Num_zero _ _ H ltac:(lia)); reflexivity.
Qed.

Lemma G_zero0 : G1 (d*>0inf) ((t++one 2)*>0inf).
Proof. apply GP; unfold P; es'. Qed.
Lemma G_zero1 : G1 (d*>t*>0inf) (w*>[0;0;1;0]*>0inf).
Proof. apply GP; unfold P; es'. Qed.

Inductive Value : nat -> side -> Prop :=
| ValueNum n r : Num n r -> Value n r
| ValueEnd n r : Num n r -> n<=1 -> Value (n*2+1) (d*>r)
| ValueWord k n xs q r : 0<k -> 0<n -> Word k n xs -> Value q r ->
    Value (phi n+(2^k-1)*q) (xs*>r).

Lemma G_value_one r q : Value q r -> exists s, Value (q+2) s /\ G1 r s.
Proof.
  intro H; induction H.
  - destruct (P_num _ _ H) as [s [Hs Hp]].
    exists s; split; [constructor; exact Hs|constructor; exact Hp].
  - destruct (Nat.eq_dec n 0).
    + rewrite (Num_zero _ _ H e); subst n.
      exists ((t++one 2)*>0inf); split; [|exact G_zero0].
      change (Value (phi 3+(2^3-1)*0) ((t++one 2)*>0inf)).
      econstructor; [lia|lia|exact (Word10 _ _ _ (Word_one 2))|apply ValueNum, Num0].
    + rewrite (Num_one _ _ H ltac:(lia)); assert (n=1%nat) by lia; subst n.
      exists (w*>[0;0;1;0]*>0inf); split; [|exact G_zero1].
      change (Value (phi 3+(2^1-1)*2) (w*>[0;0;1;0]*>0inf)).
      econstructor; [lia|lia|exact (Word10 _ _ _ Word1)|].
      apply ValueNum, (Num00 1), (Num10 0), Num0.
  - destruct (GCounter_total k n H (Word_bound _ _ _ H1)) as [m [c [Hc Hm]]].
    assert (Htail:exists s, Value (q+c*2) s /\ G c r s).
    { assert (c<=1) by (destruct Hc; lia); destruct c as [|[|c]]; [| |lia].
      - exists r; split; [applys_eq H2; flia|constructor].
      - destruct IHValue as [s [Hs Hg]]; exists s; split; [exact Hs|apply G_single, Hg]. }
    destruct Htail as [s [Hs Hg]].
    destruct (G_counter _ _ _ _ _ _ _ H1 H Hc Hg) as [ys [Hy Hrun]].
    exists (ys*>s); split; [|exact Hrun].
    pose proof (GCounter_balance _ _ _ _ H H0 Hc).
    replace (phi n+(2^k-1)*q+2) with (phi m+(2^k-1)*(q+c*2)) by nia.
    econstructor; [exact H|eapply GCounter_positive; eassumption|exact Hy|exact Hs].
Qed.

Lemma G_value r q : Value q r -> forall i, exists s,
  Value (q+i*2) s /\ G i r s.
Proof.
  intros H i; gen r q; induction i; intros r q H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (G_value_one _ _ H) as [s [Hs H1]].
    destruct (IHi _ _ Hs) as [z [Hz Hi]].
    exists z; split; [applys_eq Hz; flia|econstructor; eassumption].
Qed.

Lemma GCounterRun_one i n m c : CounterRun (GCounter 1) (2+i) n m c ->
  0<n -> n<4 -> m=3%nat /\ i+1<=c /\ c<=i+2.
Proof.
  intros H Hn Hbound.
  assert (Hm:m<4) by exact (GCounterRun_bound _ _ _ _ _ H ltac:(lia) Hbound).
  assert (Hthree:3<=m).
  { destruct (Nat.eq_dec (n mod 2) 1%nat) as [Hodd|Heven].
    - eapply GCounterRun_three; eauto; lia.
    - assert (n=2%nat) by lia; subst n.
      inversion H as [|i' n' z m' c0 c1 H0 H1]; subst.
      inversion H0; subst; cbn[Nat.add Nat.pow] in *; try lia.
      eapply GCounterRun_three; [exact H1|lia|reflexivity]. }
  pose proof (GCounterRun_balance _ _ _ _ _ H ltac:(lia) Hn) as E.
  assert (m=3%nat) by lia; subst m.
  unfold phi in E; cbn[Nat.pow] in E; repeat split; lia.
Qed.

Lemma narrow_inside (R:nat->side->Prop) a b j fs k n xs q r : Frame a b fs -> j<a ->
  Word (2+k) n xs -> 0<k -> 0<n ->
  (forall c, exists s, R c s /\ G c r s) ->
  (n mod 2=1%nat \/ 2^(1+(2+k))<=n+j*4) -> 2^(1+k)<=b+j ->
  phi n+(2^(2+k)-1)*q<=(a*2+b+1)*4 ->
  exists z c ys s,
    Word k z ys /\ 0<z /\ R c s /\ G c r s /\
    phi z+(2^k-1)*(q+c*2)<(a*2+b+1)*2 /\
    (z mod 2=0%nat -> (a-j)*2<=z) /\
    (k=1%nat -> 3<=a-j -> z=3%nat) /\
    (forall L, 4<=L -> (a*2+b+1)*4=2^(3+k)*L -> L<=c) /\
    cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>ys*>s).
Proof.
  intros Hf Hj Hw Hk Hn Hv Hguard HB Hcap.
  destruct (counter_inner_total (2+k) j n ltac:(lia) (Word_bound _ _ _ Hw) Hguard)
    as [u [c0 [Hu [Hub H0]]]].
  assert (Hub':u<2^(1+(1+k))) by exact Hub.
  destruct (CounterRun_total _ _ (fun z => GCounter_total (1+k) z ltac:(lia))
    (b+j) u Hub') as [x [c1 [H1 Hxb]]].
  assert (Hodd:x mod 2=1%nat).
  { eapply GCounterRun_saturated; [exact H1|lia|exact Hub'|].
    cbn[Nat.add Nat.pow] in HB |- *; lia. }
  destruct (counter_inner_total (1+k) 0 x ltac:(lia) Hxb (or_introl Hodd))
    as [y [c2 [Hy [Hyb H2]]]].
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk) (a-j-1) y Hyb)
    as [z [c3 [H3 Hzb]]].
  destruct (Hv (c0+(c1+(c2+c3)))) as [s [Hs Hg]].
  destruct (descent_inside _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hf Hj Hw Hk Hguard Hodd H0 H1 H2 H3 Hg) as [ys [Hys Hstep]].
  exists z, (c0+(c1+(c2+c3))), ys, s; repeat split; try assumption.
  - eapply GCounterRun_positive; eassumption.
  - pose proof (descent_inside_balance _ _ _ _ _ _ _ _ _ _ _ _ _ q
      Hj Hk Hn Hu Hy H0 H1 H2 H3) as E.
    replace (c0+c1+c2+c3) with (c0+(c1+(c2+c3))) in E by lia; lia.
  - intro Heven; destruct (GCounterRun_even _ _ _ _ _ H3 Heven) as [_ [He HyEven]].
    lia.
  - intros -> HU.
    replace (a-j-1) with (2+(a-j-3)) in H3 by lia.
    exact (proj1 (GCounterRun_one _ _ _ _ H3 Hy Hyb)).
  - intros L HL Hsize.
    replace (c0+(c1+(c2+c3))) with (c0+c1+c2+c3) by lia.
    exact (descent_inside_calls _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hj Hk Hn Hu Hy
      (GCounterRun_positive _ _ _ _ _ H3 Hy) Hzb HL Hsize H0 H1 H2 H3).
Qed.

Lemma narrow_boundary (R:nat->side->Prop) a b fs k n xs q r : Frame a b fs ->
  Word (1+k) n xs -> 0<k -> 0<n ->
  (forall c, exists s, R c s /\ G c r s) ->
  (n mod 2=1%nat \/ 2^(1+(1+k))<=n+a*4) -> 2^k<=b+a ->
  phi n+(2^(1+k)-1)*q<=(a*2+b+1)*4 ->
  exists z c ys s,
    Word k z ys /\ z mod 2=1%nat /\ R c s /\ G c r s /\
    phi z+(2^k-1)*(q+c*2)<(a*2+b+1)*4 /\
    (forall L, 2<=L -> (a*2+b+1)*4=2^(2+k)*L -> L<=c) /\
    cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>ys*>s).
Proof.
  intros Hf Hw Hk Hn Hv Hguard HB Hcap.
  destruct (counter_inner_total (1+k) a n ltac:(lia) (Word_bound _ _ _ Hw) Hguard)
    as [u [c0 [Hu [Hub H0]]]].
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk) (b+a) u Hub)
    as [z [c1 [H1 Hzb]]].
  destruct (Hv (c0+c1)) as [s [Hs Hg]].
  destruct (descent_boundary _ _ _ _ _ _ _ _ _ _ _ _ Hf Hw Hk Hguard H0 H1 Hg)
    as [ys [Hys Hstep]].
  exists z, (c0+c1), ys, s; repeat split; try assumption.
  - eapply GCounterRun_saturated; [exact H1|exact Hk|exact Hub|].
    cbn[Nat.add Nat.pow]; lia.
  - pose proof (descent_boundary_balance _ _ _ _ _ _ _ _ q Hk Hn Hu H0 H1); lia.
  - intros L HL Hsize.
    exact (descent_boundary_calls _ _ _ _ _ _ _ _ _ Hk Hn Hu
      (GCounterRun_positive _ _ _ _ _ H1 Hu) Hzb HL Hsize H0 H1).
Qed.

(* A saturated first word makes the d call expose one narrower word.
   The k=0 case deliberately keeps d; it is not declared a normal word. *)
Lemma odd_d k n m c xs r s : Word (1+k) n xs -> n mod 2=1%nat ->
  CounterRun (GCounter (1+k)) 2 n (m*2+1) c -> G c r s ->
  exists ys, Word k m ys /\ forall i z, G i (ys*>s) z ->
    P (1+i) (d*>xs*>r) (w*>z).
Proof.
  intros Hw Hodd Hc Hg.
  destruct (P_counter_run _ _ _ _ _ _ _ _ Hw ltac:(lia) Hodd Hc Hg)
    as [zs [Hz Hp]].
  destruct (Word_odd_inv _ _ _ Hz) as [ys [Hy E]]; subst zs.
  exists ys; split; [exact Hy|intros i z Hrun].
  eapply P_add with (a:=1%nat); [apply P_d, Hp|apply G_w, Hrun].
Qed.

Lemma odd_d_value (R:nat->side->Prop) k n xs q r i : Word (1+k) n xs -> 0<k ->
  n mod 2=1%nat -> (forall c, exists s, R (q+c*2) s /\ G c r s) ->
  exists z c ys s,
    Word k z ys /\ 0<z /\ R (q+c*2) s /\
    (phi z+(2^k-1)*(q+c*2))*2<=phi n+(2^(1+k)-1)*q+3+i*4 /\
    (z mod 2=0%nat -> 2+i*2<=z) /\
    (k=1%nat -> 2<=i -> z=3%nat) /\
    P (1+i) (d*>xs*>r) (w*>ys*>s) /\
    exists child, P 1 (d*>xs*>r) (w*>child) /\ G i child (ys*>s).
Proof.
  intros Hw Hk Hodd Hv.
  destruct (counter_inner_total (1+k) 0 n ltac:(lia) (Word_bound _ _ _ Hw)
    (or_introl Hodd)) as [u [c0 [Hu [Hub H0]]]].
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk) i u Hub)
    as [z [c1 [H1 Hzb]]].
  destruct (Hv (c0+c1)) as [s [Hs Hg]].
  destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg1]].
  destruct (odd_d _ _ _ _ _ _ _ Hw Hodd H0 Hg0) as [ys0 [Hy0 Hloop]].
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy0 Hk H1 Hg1) as [ys [Hy Hrun]].
  exists z, (c0+c1), ys, s; repeat split; try assumption.
  - eapply GCounterRun_positive; eassumption.
  - pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) ltac:(lia)) as E0.
    pose proof (GCounterRun_balance _ _ _ _ _ H1 Hk Hu) as E1.
    pose proof (phi_bounds _ Hu); rewrite phi_odd in E0.
    cbn[Nat.add Nat.pow] in *; counter_arith.
  - intro Heven; destruct (GCounterRun_even _ _ _ _ _ H1 Heven) as [_ [He HuEven]]; lia.
  - intros -> Hi; replace i with (2+(i-2)) in H1 by lia.
    exact (proj1 (GCounterRun_one _ _ _ _ H1 Hu Hub)).
  - exact (Hloop _ _ Hrun).
  - exists (ys0*>r0); split; [apply Hloop; constructor|exact Hrun].
Qed.

Lemma two_inside a b j fs n u c0 c1 xs r s z : Frame a b fs -> j<a ->
  Word 2 n xs -> (n mod 2=1%nat \/ 8<=n+j*4) ->
  CounterRun (GCounter 2) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter 1) (b+j) u 3 c1 ->
  G (c0+(c1+2)) r s -> G (a-j-1) (d*>s) z ->
  cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>z).
Proof.
  intros Hf Hj Hw Hguard H0 H1 Hg Hz.
  destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg']].
  destruct (G_split _ _ _ _ Hg') as [r1 [Hg1 Hg2]].
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) Hguard H0 Hg0)
    as [xs0 [Hw0 Hin]].
  destruct (Word_odd_inv _ _ _ Hw0) as [ys0 [Hy0 E0]]; subst xs0.
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy0 ltac:(lia) H1 Hg1)
    as [ys [Hy Hrun]].
  rewrite (Word_max _ _ _ Hy eq_refl) in Hrun.
  rewrite (lpow_add _ j 1), Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hrun|].
  replace (a-j) with (1+(a-j-1)) by lia.
  eapply G_add with (s:=w*>d*>s).
  - apply P_G, P_d, G_w, Hg2.
  - apply P_G, G_w, Hz.
Qed.

Lemma two_boundary a b fs n u c0 c1 xs r s : Frame a b fs ->
  Word 2 n xs -> (n mod 2=1%nat \/ 8<=n+a*4) ->
  CounterRun (GCounter 2) (a*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter 1) (b+a) u 3 c1 -> G (c0+c1) r s ->
  cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>w*>s).
Proof.
  intros Hf Hw Hguard H0 H1 Hg.
  destruct (descent_boundary _ _ _ _ _ _ _ _ _ _ _ _ Hf Hw ltac:(lia) Hguard H0 H1 Hg)
    as [ys [Hy Hstep]].
  rewrite (Word_max _ _ _ Hy eq_refl) in Hstep; exact Hstep.
Qed.

Lemma one_boundary a b fs n c xs r s z : Frame a b fs ->
  Word 1 n xs -> (n mod 2=1%nat \/ 4<=n+a*4) ->
  CounterRun (GCounter 1) (a*2+2) n 3 c ->
  G c r s -> G (b+a) (d*>s) z ->
  cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>z).
Proof.
  intros Hf Hw Hguard Hc Hg Hz.
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) Hguard Hc Hg)
    as [ys [Hy Hin]].
  rewrite (Word_max _ _ _ Hy eq_refl) in Hin.
  rewrite !Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hz|].
  replace (a-a) with 0%nat by lia; constructor.
Qed.

Lemma counter_one_loop i : CounterRun (GCounter 1) i 3 3 i.
Proof.
  induction i; [constructor|].
  eapply CounterS with (c:=1%nat); [apply GCod; reflexivity|exact IHi].
Qed.

Lemma counter_one_start i : CounterRun (GCounter 1) (1+i) 1 3 i.
Proof.
  eapply CounterS with (c:=0%nat); [apply GCinc; cbn; lia|apply counter_one_loop].
Qed.

Lemma one_neighbor b j fs xs r s z out : Frame (1+j) b fs -> Word 1 1 xs ->
  G (j*2+1) r s -> G (b+j) (d*>s) (w*>z) -> G 2 z out ->
  cfg (fs*>w^^j*>xs*>r) -->+ cfg ((fs++w^^(1+j)++d)*>out).
Proof.
  intros Hf Hw Hg Hz Hout.
  assert (Hc:CounterRun (GCounter 1) (j*2+2) 1 3 (j*2+1)).
  { applys_eq (counter_one_start (j*2+1)); flia. }
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) (or_introl eq_refl) Hc Hg)
    as [ys [Hy Hin]].
  rewrite (Word_max _ _ _ Hy eq_refl) in Hin.
  rewrite (Nat.add_comm 1 j), (lpow_add _ j 1), !Str_app_assoc.
  apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hz|].
  replace (1+j-j) with 1%nat by lia.
  apply P_G, P_d, G_w, Hout.
Qed.

Lemma Num_odd_inv n r : Num (n*2+1) r -> exists s, Num n s /\ r=t*>s.
Proof.
  intro H; inversion H; subst; try lia.
  eexists; split; [applys_eq H1; flia|reflexivity].
Qed.

Lemma P_odd_end k n r : Num n r -> exists s,
  Num (n+(1+k)*2) s /\ P (1+k) (d*>t*>r) (w*>s).
Proof.
  intro H; destruct (I_nums 2 _ _ H) as [x [Hx Hi]].
  destruct (G_nums k _ _ Hx) as [s [Hs Hg]].
  exists s; split; [applys_eq Hs; flia|].
  eapply P_add with (a:=1%nat); [apply P_d, P_t, Hi|apply G_w, Hg].
Qed.

Lemma pure_odd_boundary a b xs n r : Frame a b xs -> Num n r -> exists s,
  Num (n+(a*2+b+1)*2) s /\
  cfg (xs*>w^^a*>t*>r) -->+ cfg ((xs++w^^a++d)*>s).
Proof.
  intros Hf Hn; destruct (I_nums (a*2+2) _ _ Hn) as [x [Hx Hi]].
  destruct (G_nums (b+a) _ _ Hx) as [s [Hs Hg]].
  exists s; split; [applys_eq Hs; flia|].
  rewrite !Str_app_assoc; apply (frame_step _ _ _ Hf), column_partial; [lia|].
  eapply run with (x:=t*>x) (y:=d*>s).
  - apply P_t, Hi.
  - apply G_d, Hg.
  - replace (a-a) with 0%nat by lia; constructor.
Qed.

Lemma pure_three a b j xs n r : Frame a b xs -> j<a -> Num n r -> exists s,
  Num (n+a*2+b+1) s /\
  cfg (xs*>w^^j*>t*>t*>r) -->+ cfg (xs*>w^^(j+1)*>s).
Proof.
  intros Hf Hj Hn.
  destruct (I_nums (j*2+2) _ _ (Num10 _ _ Hn)) as [x [Hx Hi]].
  replace (n*2+1+(j*2+2)) with ((n+j+1)*2+1) in Hx by lia.
  destruct (Num_odd_inv _ _ Hx) as [x' [Hx' Ex]]; subst x.
  destruct (I_nums (b+j) _ _ Hx') as [y [Hy HyI]].
  destruct (P_odd_end (a-j-1) _ _ Hy) as [s [Hs Hp]].
  exists s; split; [applys_eq Hs; flia|].
  rewrite (lpow_add _ j 1), Str_app_assoc.
  apply (frame_step _ _ _ Hf), column_partial; [lia|].
  eapply run with (x:=t*>t*>x') (y:=d*>t*>y).
  - apply P_t, Hi.
  - apply G_d, P_G, P_t, HyI.
  - apply P_G; applys_eq Hp; flia.
Qed.

Lemma G_zero n r : Num n r -> n<=1 -> exists s,
  Value (n*2+3) s /\ G1 (d*>r) s.
Proof.
  intros H Hn; replace (n*2+3) with (n*2+1+2) by lia.
  apply G_value_one, ValueEnd; assumption.
Qed.

Lemma one_prefix k : [1]++[0;0]^^k++t = one k.
Proof.
  destruct k; [reflexivity|cbn[one lpow]].
  rewrite lpow_rotate_list; reflexivity.
Qed.

Lemma P_d_first_Q k r s : G1 r s ->
  P 1 (d*>[0;0]*>t^^k*>d*>r) (w*>one k*>s).
Proof.
  intro H; rewrite <-one_prefix, !Str_app_assoc.
  change (P 1 (d*>[0;0]*>t^^k*>d*>r)
    ((w++[1])*>[0;0]^^k*>t*>s)).
  eapply segRLs_sideRLs_concat; [exact PdR|apply Q_R].
  destruct H.
  - exact (Q_overflow_p k _ _ H).
  - exact (Q_overflow_q k _ _ H).
Qed.

Lemma P_d_last_Q k n xs r s : Word (1+k) n xs -> n+4=2^(2+k) -> G1 r s ->
  P 1 (d*>xs*>r) ([1;0;0;0]*>[0;0]^^(1+k)*>t*>s).
Proof.
  intros Hw He Hg.
  destruct (P_word_inc _ _ _ r Hw ltac:(lia) ltac:(cbn[Nat.add Nat.pow] in *; lia))
    as [ys [Hy Hp]].
  eapply P_d_second_Q; [exact Hp|].
  rewrite (Word_before_Q _ _ _ Hy ltac:(lia)), !Str_app_assoc.
  apply Q_overflow, Hg.
Qed.

Lemma Num_zeros k n r : Num n r -> Num (n*2^k) ([0;0]^^k*>r).
Proof.
  intro H; induction k.
  - cbn[lpow Nat.pow]; applys_eq H; flia.
  - cbn[lpow]; applys_eq (Num00 _ _ IHk); cbn[Nat.pow]; nia.
Qed.

(* Keep the last existing w, so that both late Q returns remain visible. *)
Lemma column_late a b j r x y s : j<a ->
  G (j*2+2) r x -> G (b+j) (d*>x) y -> G (a-j) (d*>y) s ->
  Suffix a b (w^^(1+j)*>r) (w^^j*>s).
Proof.
  intros Hj H0 H1 H2.
  rewrite (Nat.add_comm 1 j), (lpow_add _ j 1), Str_app_assoc.
  apply column_partial; [lia|].
  eapply run with (x:=w*>x) (y:=d*>y).
  - apply G_w, H0.
  - change (I (b+j) (d*>d*>x) (d*>y)); apply G_d, H1.
  - exact H2.
Qed.

Lemma late_first_Q a b j fs k n xs r r1 s out :
  Frame a b fs -> j<a -> 0<b+j -> Word (1+k) n xs ->
  n+j*4+6=2^(2+k) -> G1 r r1 ->
  G (b+j+1) (one k*>r1) s -> G (a-j-1) (d*>s) out ->
  cfg (fs*>w^^(1+j)*>xs*>r) -->+ cfg (fs*>w^^(1+j)*>out).
Proof.
  intros Hf Hj Hb Hw He Htail Hmid Hout.
  destruct (P_word_linear (1+k) (j*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in *; nia)) as [ys [Hy Hpre]].
  rewrite (Word_before_Q _ _ _ Hy ltac:(nia)), !Str_app_assoc in Hpre.
  replace (b+j+1) with ((b+j-1)+2) in Hmid by lia.
  destruct (G_split _ _ _ _ Hmid) as [z [Hz H2]].
  apply (frame_step _ _ _ Hf).
  change (Suffix a b (w^^(1+j)*>xs*>r) (w*>w^^j*>out)).
  rewrite <-lpow_shift'; eapply column_late; [exact Hj|apply P_G, Hpre| |].
  - replace (b+j) with (1+(b+j-1)) by lia.
    eapply G_add; [apply P_G, P_d_first_Q, Htail|apply P_G, G_w, Hz].
  - replace (a-j) with (1+(a-j-1)) by lia.
    eapply G_add; [apply P_G, P_d, G_w, H2|apply P_G, G_w, Hout].
Qed.

Lemma late_second_Q a b j fs k n xs q r :
  Frame a b fs -> j<a -> 0<b+j -> Word (1+k) n xs ->
  n+j*4+8=2^(2+k) -> Num q r -> exists out,
  Num ((q*2+5)*2^(2+k)+(b+j-1)+(a-j)*2) out /\
  cfg (fs*>w^^(1+j)*>xs*>r) -->+ cfg (fs*>w^^(1+j)*>out).
Proof.
  intros Hf Hj Hb Hw He Hr.
  destruct (P_word_linear (1+k) (j*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in *; nia)) as [ys [Hy Hpre]].
  destruct (P_num _ _ Hr) as [r1 [Hr1 Htail]].
  pose proof (P_d_last_Q _ _ _ _ _ Hy ltac:(nia) (GP _ _ Htail)) as Hfirst.
  assert (Hnum:Num (((q*2+5)*2^(2+k))*2+1)
    ([1;0;0;0]*>[0;0]^^(1+k)*>t*>r1)).
  { applys_eq (Num10 _ _ (Num00 _ _ (Num_zeros (1+k) _ _ (Num10 _ _ Hr1))));
      cbn[Nat.add Nat.pow]; nia. }
  destruct (G_nums (b+j-1) _ _ Hnum) as [s [Hs Hmid]].
  replace ((q*2+5)*2^(2+k)*2+1+(b+j-1)*2)
    with (((q*2+5)*2^(2+k)+(b+j-1))*2+1) in Hs by lia.
  destruct (Num_odd_inv _ _ Hs) as [s1 [Hs1 ->]].
  destruct (P_odd_end (a-j-1) _ _ Hs1) as [out [Hnumout Hout]].
  exists out; split; [applys_eq Hnumout; flia|].
  apply (frame_step _ _ _ Hf).
  change (Suffix a b (w^^(1+j)*>xs*>r) (w*>w^^j*>out)).
  rewrite <-lpow_shift'; eapply column_late; [exact Hj|apply P_G, Hpre| |].
  - replace (b+j) with (1+(b+j-1)) by lia.
    eapply G_add; [apply P_G, Hfirst|exact Hmid].
  - apply P_G; applys_eq Hout; flia.
Qed.

Lemma late_first_Q_boundary a fs k xs q r : Frame a (a+1) fs -> 2<=a ->
  a*6+4=2^(2+k) -> Word (1+k) (a*2+2) xs -> Num q r -> exists ys s,
  Word k (a+3) ys /\ Num (q+4) s /\
  cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>ys*>s).
Proof.
  intros Hf Ha Hpow Hw Hr.
  assert (Hk:0<k) by (destruct k; [cbn in Hpow; lia|lia]).
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk)
    (a*2+1) 1 (Word_bound _ _ _ (Word_one k))) as [z [c [Hc Hz]]].
  assert (Hodd:z mod 2=1%nat) by (eapply GCounterRun_odd; [exact Hc|reflexivity]).
  pose proof (GCounterRun_balance _ _ _ _ _ Hc Hk ltac:(lia)) as E.
  assert (Epow:(2^k-1)*2=a*3) by (cbn[Nat.add Nat.pow] in Hpow; lia).
  rewrite Epow in E.
  assert (Ez:z+c*(a*3)=a*4+3) by (unfold phi in E; rewrite Hodd in E; lia).
  assert (Hz':z<a*3+2) by (cbn[Nat.add Nat.pow] in Hz, Hpow; lia).
  assert (Ec:c=1%nat /\ z=a+3).
  { clear -Ez Hz' Ha.
    destruct c as [|[|c]]; [lia|split; lia|nia]. }
  destruct Ec as [-> ->].
  destruct (P_num _ _ Hr) as [r0 [H0 Hp]].
  destruct (P_num _ _ H0) as [s [Hs Hp']].
  destruct (G_counter_run _ _ _ _ _ _ _ _ (Word_one k) Hk Hc (P_G _ _ _ Hp'))
    as [ys [Hy Hg]].
  exists ys, s; split; [exact Hy|]; split; [applys_eq Hs; flia|].
  rewrite !Str_app_assoc.
  applys_eq (late_first_Q a (a+1) (a-1) fs k (a*2+2) xs r r0 (ys*>s) (d*>ys*>s)); try flia.
  - exact Hf.
  - exact Hw.
  - apply GP, Hp.
  - applys_eq Hg; flia.
  - replace (a-(a-1)-1) with 0%nat by lia; constructor.
Qed.

Lemma Word_split k n xs : Word k n xs -> 0<n -> n<>2^k ->
  exists a b z ys, k=1+a+b /\ n=2^a*(z*2+1) /\ Word b z ys /\
    xs=[0;0]^^a++t++ys /\ [1]++xs=one a++ys.
Proof.
  intro H; induction H; intros Hn Hpow; [lia|cbn in Hpow; lia| |].
  - destruct (IHWord ltac:(lia) ltac:(cbn[Nat.add Nat.pow] in Hpow; nia))
      as [a [b [z [ys [Hk [Hv [Hw [Hx Hx']]]]]]]].
    exists (1+a), b, z, ys; repeat split; try lia; try exact Hw.
    + cbn[Nat.add Nat.pow]; nia.
    + cbn[Nat.add lpow]; rewrite Hx; reflexivity.
    + rewrite Hx, <-one_prefix; cbn[Nat.add lpow]; repeat rewrite <-app_assoc; reflexivity.
  - exists 0%nat, k, n, xs; repeat split; try lia; try exact H; reflexivity.
Qed.

(* The E/O splitting rules use the actual factored word, with no restriction
   on the remaining suffix. Any necessary calls there are explicit premises. *)
Lemma split_root a b j fs r k tail n c m e s : Frame a b fs -> j<=a -> 0<k ->
  P (j*2+2) r ([0;0]^^k*>t*>tail) ->
  CounterRun (ICounter k) (b+j) 1 n c ->
  CounterRun (GCounter k) (a-j) n m e -> G (c+e) tail s ->
  exists xs, Word k m xs /\
    cfg (fs*>w^^j*>r) -->+ cfg (fs*>w^^j*>xs*>s).
Proof.
  intros Hf Hj Hk Hp Hc He Hg.
  destruct (G_split _ _ _ _ Hg) as [r0 [Hg0 Hg1]].
  destruct (I_counter_run _ _ _ _ _ _ _ _ (Word_one k) Hc Hg0)
    as [ys [Hy Hi]].
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hy Hk He Hg1) as [xs [Hx Hrun]].
  exists xs; split; [exact Hx|].
  apply (frame_step _ _ _ Hf), column_partial; [exact Hj|].
  eapply run; [exact Hp| |exact Hrun].
  rewrite <-one_prefix, !Str_app_assoc in Hi; exact Hi.
Qed.

Lemma split_d k i n c tail r s : P 2 r ([0;0]^^k*>t*>tail) ->
  CounterRun (ICounter k) i 1 n c -> G c tail s ->
  exists xs, Word (1+k) (n*2+1) xs /\ P (1+i) (d*>r) (xs*>s).
Proof.
  intros Hp Hc Hg.
  destruct (I_counter_run _ _ _ _ _ _ _ _ (Word_one k) Hc Hg) as [ys [Hy Hi]].
  exists (t++ys); split; [apply Word10, Hy|].
  rewrite Str_app_assoc; eapply P_add with (a:=1%nat) (s:=t*>one k*>tail).
  - rewrite <-one_prefix, !Str_app_assoc; apply P_d, Hp.
  - apply P_t, Hi.
Qed.

Lemma split_inside a b j fs r r0 r1 k tail n c s :
  Frame a b fs -> j<a -> Inner j r (t*>r0) -> G (b+j) r0 r1 ->
  P 2 r1 ([0;0]^^k*>t*>tail) ->
  CounterRun (ICounter k) (a-j-1) 1 n c -> G c tail s -> exists xs,
  Word (1+k) (n*2+1) xs /\
  cfg (fs*>w^^j*>r) -->+ cfg (fs*>w^^j*>xs*>s).
Proof.
  intros Hf Hj Hin Hmid Hp Hc Hg.
  destruct (split_d _ _ _ _ _ _ _ Hp Hc Hg) as [xs [Hw Hrun]].
  exists xs; split; [exact Hw|apply (frame_step _ _ _ Hf)].
  eapply inner_column; [lia|exact Hin|apply G_d, Hmid|].
  apply P_G; applys_eq Hrun; flia.
Qed.

Lemma first_Q_inside a b j fs r r0 k tail tail' s :
  Frame a b fs -> j<a -> Inner j r (t*>r0) ->
  G (b+j) r0 ([0;0]*>t^^k*>d*>tail) -> G1 tail tail' ->
  G (a-j-1) (one k*>tail') s ->
  cfg (fs*>w^^j*>r) -->+ cfg (fs*>w^^(j+1)*>s).
Proof.
  intros Hf Hj Hin Hmid Htail Hrest.
  rewrite (lpow_add _ j 1), Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hmid|].
  replace (a-j) with (1+(a-j-1)) by lia.
  eapply G_add; [apply P_G, P_d_first_Q, Htail|apply P_G, G_w, Hrest].
Qed.

Lemma Num_factor n r : Num n r -> 0<n -> exists j q s,
  n=(q*2+1)*2^j /\ Num q s /\ r=[0;0]^^j*>t*>s.
Proof.
  intro H; induction H; intro Hn; [lia| |].
  - destruct (IHNum ltac:(lia)) as [j [q [s [He [Hs Hr]]]]].
    exists (1+j), q, s; split; [cbn[Nat.add Nat.pow]; nia|].
    split; [exact Hs|cbn[Nat.add lpow]; rewrite Hr; reflexivity].
  - exists 0%nat, n, r; repeat split; try lia; try exact H; reflexivity.
Qed.

Lemma P_end_birth n r : Num n r -> exists j q s,
  n+4=(q*2+1)*2^j /\ Num q s /\
  P 1 (d*>r) ((t++one j)*>s).
Proof.
  intro H; destruct (P_nums 2 _ _ H) as [x [Hx Hp]].
  destruct (Num_factor _ _ Hx ltac:(lia)) as [j [q [s [He [Hs Hr]]]]].
  exists j, q, s; split; [exact He|]; split; [exact Hs|].
  rewrite <-one_prefix, !Str_app_assoc; apply P_d.
  rewrite Hr in Hp; exact Hp.
Qed.

Lemma G_end n r i : Num n r -> 0<i -> exists q s,
  Value q s /\ q<=n+i*2+2 /\ G i (d*>r) s.
Proof.
  intros H Hi; destruct i as [|i]; [lia|].
  destruct (P_end_birth _ _ H) as [j [q [s [He [Hs Hp]]]]].
  assert (Hv:Value (3+(2^(1+j)-1)*q) ((t++one j)*>s)).
  { change (Value (phi 3+(2^(1+j)-1)*q) ((t++one j)*>s)).
    econstructor; [lia|lia|exact (Word10 _ _ _ (Word_one j))|apply ValueNum, Hs]. }
  destruct (G_value _ _ Hv i) as [z [Hz Hg]].
  eexists _, z; split; [exact Hz|]; split.
  - assert (3<=2^j+q) by (destruct q as [|[|q]]; nia).
    cbn[Nat.add Nat.pow]; nia.
  - eapply G_add with (a:=1%nat); [apply P_G, Hp|exact Hg].
Qed.

Lemma G_end_word n r i : Num n r -> 0<i -> exists k q z c xs s,
  n+4=(q*2+1)*2^k /\
  CounterRun (GCounter (1+k)) (i-1) 3 z c /\
  Word (1+k) z xs /\ Num (q+c*2) s /\ z mod 2=1%nat /\
  phi z+(2^(1+k)-1)*(q+c*2)<=n+i*2+2 /\
  G i (d*>r) (xs*>s).
Proof.
  intros H Hi; destruct i as [|i]; [lia|].
  destruct (P_end_birth _ _ H) as [k [q [r0 [He [H0 Hp]]]]].
  assert (Hw:Word (1+k) 3 (t++one k)) by exact (Word10 _ _ _ (Word_one k)).
  destruct (CounterRun_total _ _ (fun z => GCounter_total (1+k) z ltac:(lia))
    i 3 (Word_bound _ _ _ Hw)) as [z [c [Hc Hz]]].
  destruct (G_nums c _ _ H0) as [s [Hs Hg]].
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hw ltac:(lia) Hc Hg)
    as [xs [Hx Hrun]].
  exists k, q, z, c, xs, s; split; [exact He|]; split.
  - applys_eq Hc; flia.
  - split; [exact Hx|]; split; [exact Hs|]; split.
    + eapply GCounterRun_odd; [exact Hc|reflexivity].
    + split.
      * pose proof (GCounterRun_balance _ _ _ _ _ Hc ltac:(lia) ltac:(lia)) as E.
        assert (3<=2^k+q) by (destruct q as [|[|q]]; nia).
        change (phi z+c*((2^(1+k)-1)*2)=3+i*2) in E.
        cbn[Nat.add Nat.pow] in E |- *; counter_arith.
      * eapply G_add with (a:=1%nat); [apply P_G, Hp|exact Hrun].
Qed.

(* Pure tails: the two birth cases retain the exact outgoing call counts. *)
Lemma pure_even a b j fs n r : Frame a b fs -> j<=a -> Num (n*2) r ->
  exists k q m c z e xs s,
    0<k /\ n*2+j*4+4=(q*2+1)*2^k /\
    CounterRun (ICounter k) (b+j) 1 m c /\
    CounterRun (GCounter k) (a-j) m z e /\
    Word k z xs /\ Num (q+(c+e)*2) s /\
    cfg (fs*>w^^j*>r) -->+ cfg (fs*>w^^j*>xs*>s).
Proof.
  intros Hf Hj Hn.
  destruct (P_nums (j*2+2) _ _ Hn) as [r0 [H0 Hp]].
  destruct (Num_factor _ _ H0 ltac:(lia)) as [k [q [r1 [He [H1 Er]]]]].
  assert (Hk:0<k) by (destruct k; [cbn[Nat.pow] in He; lia|lia]).
  destruct (CounterRun_total _ _ (ICounter_total k) (b+j) 1
    (Word_bound _ _ _ (Word_one k))) as [m [c [Hc Hm]]].
  destruct (CounterRun_total _ _ (fun z => GCounter_total k z Hk) (a-j) m Hm)
    as [z [e [Hz Hbound]]].
  destruct (G_nums (c+e) _ _ H1) as [s [Hs Hg]]; rewrite Er in Hp.
  destruct (split_root _ _ _ _ _ _ _ _ _ _ _ _ Hf Hj Hk Hp Hc Hz Hg)
    as [xs [Hx Hstep]].
  exists k, q, m, c, z, e; exists xs, s; repeat split; try assumption; try lia.
Qed.

Lemma pure_one a b j fs n r : Frame a b fs -> j<a -> Num n r ->
  exists k q z c xs s,
    0<k /\ n*2+j*4+b*2+6=(q*2+1)*2^k /\
    CounterRun (GCounter (1+k)) (a-j-1) 3 z c /\
    Word (1+k) z xs /\ Num (q+c*2) s /\
    cfg (fs*>w^^j*>t*>[0;0]*>r) -->+ cfg (fs*>w^^j*>xs*>s).
Proof.
  intros Hf Hj Hn.
  destruct (I_nums (j*2+2) _ _ (Num00 _ _ Hn)) as [x [Hx Hi]].
  destruct (G_nums (b+j) _ _ Hx) as [y [Hy Hb]].
  destruct (P_end_birth _ _ Hy) as [k [q [r0 [He [H0 Hp]]]]].
  assert (Hk:0<k) by (destruct k; [cbn[Nat.pow] in He; lia|lia]).
  assert (Hw:Word (1+k) 3 (t++one k)) by exact (Word10 _ _ _ (Word_one k)).
  destruct (CounterRun_total _ _ (fun z => GCounter_total (1+k) z ltac:(lia))
    (a-j-1) 3 (Word_bound _ _ _ Hw)) as [z [c [Hc Hz]]].
  destruct (G_nums c _ _ H0) as [s [Hs Gc]].
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hw ltac:(lia) Hc Gc)
    as [xs [Hxs Hg]].
  exists k, q, z, c, xs, s; repeat split; try assumption; try lia.
  apply (frame_step _ _ _ Hf), column_partial; [lia|].
  eapply run with (x:=t*>x) (y:=d*>y).
  - apply P_t, Hi.
  - apply G_d, Hb.
  - replace (a-j) with (1+(a-j-1)) by lia.
    eapply G_add; [apply P_G, Hp|exact Hg].
Qed.

Lemma late_second_Q_pair a fs k xs q r : Frame a a fs -> 2<=a ->
  a*6+2=2^(2+k) -> Word (1+k) (a*2+2) xs -> Num q r -> exists s,
  Num ((q*3+11)*a+q+3) s /\
  cfg (fs*>w^^(a-1)*>xs*>r) -->+ cfg (fs*>w^^a*>s).
Proof.
  intros Hf Ha Hpow Hw Hr.
  destruct (late_second_Q a a (a-2) fs k _ _ _ _ Hf ltac:(lia) ltac:(lia)
    Hw ltac:(lia) Hr) as [s0 [H0 Hfirst]].
  replace ((q*2+5)*2^(2+k)+(a+(a-2)-1)+(a-(a-2))*2)
    with ((((q*3+8)*a+q+2)*2+1)*2+1) in H0 by nia.
  destruct (Num_odd_inv _ _ H0) as [s1 [H1 ->]].
  destruct (Num_odd_inv _ _ H1) as [s2 [H2 ->]].
  destruct (pure_three a a (a-1) fs _ _ Hf ltac:(lia) H2) as [s [Hs Hsecond]].
  exists s; split; [applys_eq Hs; nia|].
  eapply progress_trans; [applys_eq Hfirst; flia|applys_eq Hsecond; flia].
Qed.

Lemma late_second_Q_recover a fs k xs q r : Frame a a fs -> 5<=a ->
  a*6+2=2^(2+k) ->
  Word (1+k) (a*2+2) xs -> Num q r -> q<=3 ->
  exists K z Q ys s, 0<K /\ K<=4+k /\ Word K z ys /\ Num Q s /\ z mod 2=1%nat /\
    (2^ (2+k)<=2^K -> z=a*4+1) /\
    phi z+(2^K-1)*Q<(a*3+1)*8 /\
    (K=1%nat -> z=3%nat /\ Q<=(a+a)*8) /\
    cfg (fs*>w^^(a-1)*>xs*>r) -->+ cfg ((fs++w^^a++d)*>ys*>s).
Proof.
  intros Hf Ha Hpow Hw Hr Hq.
  assert (Hmod:a mod 4=1%nat) by (destruct (Frame_phase _ _ _ Hf); lia).
  destruct (late_second_Q_pair _ _ _ _ _ _ Hf ltac:(lia) Hpow Hw Hr)
    as [r2 [H2 Hfirst]].
  assert (Ea:a=(a/4)*4+1) by lia.
  replace ((q*3+11)*a+q+3) with (((q*3+11)*(a/4)*2+q*2+7)*2) in H2 by nia.
  destruct (pure_even a a a fs _ _ Hf ltac:(lia) H2)
    as (l&q0&m&c&z&e&ys&r3&Hl&He&Hc&Hz&Hy&H3&Hthird).
  assert (El:l=1%nat).
  { destruct l as [|[|l]]; try lia; cbn[Nat.pow Nat.add] in He; nia. }
  subst l; replace (a-a) with 0%nat in Hz by lia; inversion Hz; subst z e.
  cbn[Nat.add] in H3.
  assert (Hm:0<m) by (eapply ICounterRun_positive; [exact Hc|lia]).
  assert (Hmb:m<4) by exact (Word_bound _ _ _ Hy).
  destruct (CounterRun_total _ _ (fun z => GCounter_total 1 z ltac:(lia))
    (a*2+2) m Hmb) as [z [c1 [Hc1 Hzb]]].
  assert (Hc1':CounterRun (GCounter 1) (2+a*2) m z c1) by (applys_eq Hc1; flia).
  destruct (GCounterRun_one _ _ _ _ Hc1' Hm Hmb) as [-> [Hcl Hcu]].
  destruct (G_nums c1 _ _ H3) as [r4 [H4 Hg]].
  destruct (G_end_word _ _ (a+a) H4 ltac:(lia))
    as (l&q1&z&c2&ys'&s&Ebirth&Hc2&Hy'&Hs&Hodd&Hvalue&Hlast).
  pose proof (ICounterRun_balance _ _ _ _ _ Hc) as Ecount.
  assert (Hbirth:2^l<2^(4+k)).
  { cbn[Nat.pow Nat.add] in He, Ecount, Hpow |- *; nia. }
  exists (1+l), z, (q1+c2*2), ys', s; split; [lia|]; split.
  - apply Nat.pow_lt_mono_r_iff in Hbirth; lia.
  - split; [exact Hy'|]; split; [exact Hs|]; split; [exact Hodd|]; split.
    + intro Hwide; destruct (GCounterRun_linear _ _ _ _ _ Hc2) as [Hz' _];
        [cbn[Nat.add Nat.pow] in Hwide, Hpow |- *; lia|lia].
    + split.
      * cbn[Nat.pow Nat.add] in He, Hvalue, Ecount |- *; nia.
      * split.
        -- intro EK; assert (El:l=0%nat) by lia; subst l.
           pose proof (GCounterRun_three _ _ _ _ _ Hc2 ltac:(lia) eq_refl) as Hzlo.
           pose proof (Word_bound _ _ _ Hy') as Hzhi; cbn[Nat.pow] in Hzhi.
           assert (Ez:z=3%nat) by lia; subst z; split; [reflexivity|].
           pose proof (GCounterRun_balance _ _ _ _ _ Hc2 ltac:(lia) ltac:(lia)) as E2.
           change (3+c2*2=3+(a+a-1)*2) in E2.
           cbn[Nat.pow Nat.add] in He, Ebirth, Ecount; nia.
        -- eapply progress_trans; [exact Hfirst|].
           eapply progress_trans; [exact Hthird|].
           eapply one_boundary; [exact Hf|exact Hy|right; lia|exact Hc1|exact Hg|exact Hlast].
Qed.

Lemma translated_step a j fs k xs r : Frame a a fs -> a=j+1 ->
  a*6+2=2^k -> Bin k (a*2+2) xs ->
  cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^j*>xs*>1>>r).
Proof.
  intros Hf Ha Hpow Hw.
  assert (Hk:0<k) by (destruct k; [cbn in Hpow; lia|lia]).
  destruct (P_Bins k (a*2) _ _ Hw Hk ltac:(cbn[Nat.add Nat.pow]; lia))
    as [ys [Hy Hp]].
  replace (a*2+2+a*2*2) with (2^k) in Hy by lia.
  rewrite (Bin_unique _ _ _ Hy _ (Bin_top k)) in Hp.
  destruct (I_Bins k (a+j) _ _ (Bin_one k Hk) ltac:(cbn[Nat.add Nat.pow]; lia))
    as [zs [Hz Hi]].
  destruct (P_Bin _ _ _ Hz Hk ltac:(cbn[Nat.add Nat.pow]; lia)) as [xs' [Hx Hlast]].
  assert (Ex:xs'=xs).
  { eapply Bin_unique; [exact Hx|applys_eq Hw; flia]. }
  subst xs'; apply (frame_step _ _ _ Hf), column_partial; [lia|].
  eapply run with (x:=[0;0]^^k*>1>>r) (y:=zs*>1>>r).
  - pose proof (segRLs_sideRLs_concat Hp (sideRLseq_O tm r)) as H.
    rewrite Str_app_assoc in H; cbn[Str_app] in H.
    unfold P; applys_eq H; flia.
  - change (I (a+j) (([1]++[0;0]^^k)*>1>>r) (zs*>1>>r)).
    eapply segRLs_sideRLs_concat; [exact Hi|constructor].
  - replace (a-j) with 1%nat by lia; apply P_G.
    eapply segRLs_sideRLs_concat; [exact Hlast|constructor].
Qed.

Lemma translated_nonhalt a j fs k xs r : Frame a a fs -> a=j+1 ->
  a*6+2=2^k -> Bin k (a*2+2) xs -> ~halts tm (cfg (fs*>w^^j*>xs*>r)).
Proof.
  intros Hf Ha Hpow Hw.
  eapply progress_nonhalt with (P:=fun c => exists s, c=cfg (fs*>w^^j*>xs*>s)).
  - intros c [s ->]; eexists; split; [eexists; reflexivity|].
    eapply translated_step; eassumption.
  - exists r; reflexivity.
Qed.

Lemma Word_Bin k n xs : Word k n xs -> exists bs, Bin k n bs /\ xs=bs++t.
Proof.
  intro H; induction H.
  - exists [0]; split; [constructor|reflexivity].
  - exists [1]; split; [constructor|reflexivity].
  - destruct IHWord as [bs [Hb ->]]; exists ([0;0]++bs).
    split; [apply Bin00, Hb|reflexivity].
  - destruct IHWord as [bs [Hb ->]]; exists (t++bs).
    split; [apply Bin10, Hb|reflexivity].
Qed.

Lemma translated_word_nonhalt a j fs k xs r : Frame a a fs -> a=j+1 ->
  a*6+2=2^k -> Word k (a*2+2) xs -> ~halts tm (cfg (fs*>w^^j*>xs*>r)).
Proof.
  intros Hf Ha Hpow Hw; destruct (Word_Bin _ _ _ Hw) as [bs [Hb ->]].
  rewrite Str_app_assoc; eapply translated_nonhalt; eassumption.
Qed.

Fixpoint frame n := match n with
| O => (0%nat,1%nat,d++d)
| S n => let '(a,b,xs) := frame n in (a+b,a*2+1,xs++w^^a++d)
end.

Lemma frame_spec n : let '(a,b,xs) := frame n in Frame a b xs.
Proof.
  induction n; [constructor|cbn[frame]].
  destruct (frame n) as [[a b] xs]; constructor; exact IHn.
Qed.

Lemma Frame_close a b xs : Frame a b xs -> a<=b /\ b<=a+1.
Proof. intro H; induction H; lia. Qed.

Lemma narrow_next_guard a b j fs k z : Frame a b fs -> j<a ->
  2^(1+k)<=b+j -> (z mod 2=0%nat -> (a-j)*2<=z) ->
  z mod 2=1%nat \/ ((a-(j+1))*2+2<=z /\ 2^k-z/2<=(j+1)*2).
Proof.
  intros Hf Hj Hsize Hlower; pose proof (Frame_close _ _ _ Hf).
  destruct (Nat.eq_dec (z mod 2) 1%nat); [left; assumption|].
  right; specialize (Hlower ltac:(lia)); cbn[Nat.add Nat.pow] in Hsize; split; lia.
Qed.

Lemma frame_size n : let '(a,b,_) := frame n in a*2+b+1=2^(n+1).
Proof.
  induction n; [reflexivity|cbn[frame]].
  destruct (frame n) as [[a b] xs].
  replace (S n+1) with (S (n+1)) by lia; cbn[Nat.pow]; lia.
Qed.

Definition prefix n := let '(_,_,xs) := frame n in xs.
Fixpoint word k n := match k with
| O => match n with O => [0;1;0] | _ => d end
| S k => (if Nat.eqb (n mod 2) 0 then [0;0] else t) ++ word k (n/2)
end.

Lemma word_spec k n : n<2^(1+k) -> Word k n (word k n).
Proof.
  gen n; induction k; intros n Hn.
  - destruct n as [|[|n]]; [constructor|constructor|cbn in Hn; lia].
  - cbn[word]; destruct (n mod 2) eqn:E; cbn[Nat.eqb].
    + applys_eq (Word00 k (n/2)); try flia.
      apply IHk; cbn[Nat.add Nat.pow] in Hn |- *; lia.
    + applys_eq (Word10 k (n/2)); try flia.
      apply IHk; cbn[Nat.add Nat.pow] in Hn |- *; lia.
Qed.

(* The root invariant keeps the phase restrictions, not only capacity. *)
Record Level h a b fs : Prop := level {
  level_frame : Frame a b fs;
  level_height : 5<=h;
  level_size : a*2+b+1=2^(h-1)
}.

Lemma Level_bounds h a b fs : Level h a b fs -> 5<=h /\ 5<=a /\ a<=b /\ b<=a+1.
Proof.
  intros [Hf Hh Hsize]; pose proof (Frame_close _ _ _ Hf).
  assert (16<=2^(h-1)) by (change (2^4<=2^(h-1)); apply Nat.pow_le_mono_r; lia).
  repeat split; lia.
Qed.

Lemma Level_next h a b fs : Level h a b fs ->
  Level (1+h) (a+b) (a*2+1) (fs++w^^a++d).
Proof.
  intros [Hf Hh Hsize]; constructor; [constructor; exact Hf|lia|].
  replace (1+h-1) with (1+(h-1)) by lia; cbn[Nat.add Nat.pow]; lia.
Qed.

Definition Narrow a j k n := n mod 2=1%nat \/
  ((a-j)*2+2<=n /\ 2^(1+k)<=n+j*4).
Definition Two a j n := n mod 2=1%nat \/ (a-j)*2+2<=n.

Inductive SinglePhase h a b j : nat -> nat -> nat -> Prop :=
| SN k n q : 3<=k -> k+2<=h -> Narrow a j k n -> SinglePhase h a b j k n q
| S2 n q : Two a j n -> SinglePhase h a b j 2 n q
| S1 n q : (j=a \/ (j+1=a /\ n=1%nat /\ q+1<=(a*2+b+1)*2)) ->
    SinglePhase h a b j 1 n q
| SX k q : (h=k+1 /\ q<=1) \/ (k=h /\ q=0%nat) \/
    (k=h+1 /\ j=a /\ a=b /\ q=0%nat) ->
    SinglePhase h a b j k (a*2+b+1-j) q
| SY k q : h<=k+1 -> k<=h+1 -> (k<h \/ j<a) ->
    SinglePhase h a b j k ((a-j)*2+1) q
| SZ n : n*2=(a*2+b+1)*2+(a-j) -> SinglePhase h a b j (h-1) n 0.

Inductive Single h a b j : side -> Prop :=
| SNum n r : Num n r -> n<=a*8 -> Single h a b j r
| SWord k n q xs r : 0<k -> 0<n -> Word k n xs -> Num q r ->
    SinglePhase h a b j k n q -> phi n+(2^k-1)*q<=(a*2+b+1)*4 ->
    Single h a b j (xs*>r).

Inductive SRoot : (Q*tape)%type -> Prop :=
| sroot h a b j fs r : Level h a b fs -> j<=a -> Single h a b j r ->
    SRoot (cfg (fs*>w^^j*>r)).

Lemma single_odd_phase h a b j k n q : 2<=k -> k<=h+1 -> n mod 2=1%nat ->
  (h<=k+1 -> n=(a-j)*2+1 /\ (k<h \/ j<a)) -> SinglePhase h a b j k n q.
Proof.
  intros Hk Hmax Hodd Hwide.
  destruct (le_dec h (k+1)) as [Hge|Hlt].
  - destruct (Hwide Hge) as [-> Hj]; apply SY; assumption.
  - destruct k as [|[|[|k]]]; try lia.
    + apply S2; left; exact Hodd.
    + apply SN; [lia|lia|left; exact Hodd].
Qed.

Lemma split_capacity k i j m c z e q : 0<k ->
  CounterRun (ICounter k) i 1 m c -> CounterRun (GCounter k) j m z e ->
  phi z+(2^k-1)*(q+(c+e)*2)+c+(m-phi m)=1+i+j*2+(2^k-1)*q.
Proof.
  intros Hk Hi Hg; pose proof (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)) as Hm.
  pose proof (ICounterRun_balance _ _ _ _ _ Hi) as E0.
  pose proof (GCounterRun_balance _ _ _ _ _ Hg Hk Hm) as E1.
  pose proof (phi_bounds _ Hm).
  cbn[Nat.add Nat.pow] in E0; counter_arith.
Qed.

Lemma pure_odd_boundary_closed h a b fs n r : Level h a b fs ->
  Num n r -> n*2+1<=a*8 -> exists c, SRoot c /\
    cfg (fs*>w^^a*>t*>r) -->+ c.
Proof.
  intros Hl Hn Hbound; pose proof (Level_bounds _ _ _ _ Hl) as Hb.
  destruct Hl as [Hf Hh Hsize].
  destruct (pure_odd_boundary _ _ _ _ _ Hf Hn) as [s [Hs Hstep]].
  eexists; split; [|exact Hstep].
  apply (sroot (1+h) (a+b) (a*2+1) 0).
  - apply Level_next; constructor; assumption.
  - lia.
  - apply (SNum _ _ _ _ _ _ Hs); lia.
Qed.

Lemma pure_three_closed h a b j fs n r : Level h a b fs -> j<a ->
  Num n r -> n*4+3<=a*8 -> exists c, SRoot c /\
    cfg (fs*>w^^j*>t*>t*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hbound; pose proof (Level_bounds _ _ _ _ Hl) as Hb.
  destruct Hl as [Hf Hh Hsize].
  destruct (pure_three _ _ _ _ _ _ Hf Hj Hn) as [s [Hs Hstep]].
  eexists; split; [|exact Hstep].
  eapply sroot; [constructor; eassumption|lia|apply (SNum _ _ _ _ _ _ Hs); lia].
Qed.

Lemma pure_one_closed h a b j fs n r : Level h a b fs -> j<a ->
  Num n r -> n*4+1<=a*8 -> exists c, SRoot c /\
    cfg (fs*>w^^j*>t*>[0;0]*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hbound; pose proof (Level_bounds _ _ _ _ Hl) as Hb.
  destruct Hl as [Hf Hh Hsize].
  destruct (pure_one _ _ _ _ _ _ Hf Hj Hn)
    as (k&q&z&c&xs&s&Hk&He&Hc&Hw&Hs&Hstep).
  assert (Hwidth:1+k<=h+1).
  { assert (2^k<2^(h+1)).
    { replace (h+1) with (2+(h-1)) by lia; cbn[Nat.add Nat.pow]; nia. }
    apply Nat.pow_lt_mono_r_iff in H; lia. }
  assert (Hodd:z mod 2=1%nat) by (eapply GCounterRun_odd; [exact Hc|reflexivity]).
  assert (Hphase:SinglePhase h a b j (1+k) z (q+c*2)).
  { apply single_odd_phase; [lia|exact Hwidth|exact Hodd|intro Hwide].
    assert (Hp:2^(h-1)<=2^(1+k)) by (apply Nat.pow_le_mono_r; lia).
    destruct (GCounterRun_linear _ _ _ _ _ Hc) as [Hz _];
      [cbn[Nat.add Nat.pow] in Hp |- *; lia|split; [lia|right; exact Hj]]. }
  assert (Hvalue:phi z+(2^(1+k)-1)*(q+c*2)<=(a*2+b+1)*4).
  { pose proof (GCounterRun_balance _ _ _ _ _ Hc ltac:(lia) ltac:(lia)) as E.
    change (phi z+c*((2^(1+k)-1)*2)=3+(a-j-1)*2) in E.
    clear -E He Hb Hj Hbound.
    cbn[Nat.add Nat.pow] in E |- *; counter_arith. }
  eexists; split; [|exact Hstep].
  eapply sroot; [constructor; eassumption|lia|].
  eapply SWord with (k:=1+k) (n:=z) (q:=q+c*2);
    [lia|lia|exact Hw|exact Hs|exact Hphase|exact Hvalue].
Qed.

Lemma even_birth_phase h a b j fs n k q m c z e : Level h a b fs -> j<=a ->
  n<=a*4 -> 2<=k -> n*2+j*4+4=(q*2+1)*2^k ->
  CounterRun (ICounter k) (b+j) 1 m c -> CounterRun (GCounter k) (a-j) m z e ->
  SinglePhase h a b j k z (q+(c+e)*2).
Proof.
  intros Hl Hj Hn Hk He Hi Hg; pose proof (Level_bounds _ _ _ _ Hl) as Hb.
  destruct Hl as [Hf Hh Hsize].
  assert (Hm:0<m) by (eapply ICounterRun_positive; [exact Hi|lia]).
  assert (Hwidth:k<=h+1).
  { assert (2^k<=2^(h+1)).
    { replace (h+1) with (2+(h-1)) by lia; cbn[Nat.add Nat.pow]; nia. }
    apply Nat.pow_le_mono_r_iff in H; lia. }
  destruct (le_dec h (k+1)) as [Hwide|Hnarrow].
  - assert (Hp:2^(h-1)<=2^k) by (apply Nat.pow_le_mono_r; lia).
    destruct (ICounterRun_linear _ _ _ _ _ Hi) as [Em Ec];
      [cbn[Nat.add Nat.pow]; lia|].
    destruct (GCounterRun_linear _ _ _ _ _ Hg) as [Ez Ee];
      [cbn[Nat.add Nat.pow]; lia|].
    subst m c z e; replace (q+(0+0)*2) with q by lia.
    replace (1+(b+j)+(a-j)*2) with (a*2+b+1-j) by lia; apply SX.
    destruct (Nat.eq_dec h (k+1)) as [Hlo|Hlo].
    + left; split; [exact Hlo|].
      rewrite Hlo in Hsize; replace (k+1-1) with k in Hsize by lia; nia.
    + right; destruct (Nat.eq_dec k h) as [->|Hhi].
      * left; split; [reflexivity|].
        assert (Ep:2^h=2^(h-1)*2).
        { replace h with (1+(h-1)) at 1 by lia; cbn[Nat.add Nat.pow]; lia. }
        nia.
      * right; assert (Ek:k=h+1) by lia; subst k.
        assert (Ep:2^(h+1)=2^(h-1)*4).
        { replace (h+1) with (2+(h-1)) by lia; cbn[Nat.add Nat.pow]; lia. }
        repeat split; try lia; nia.
  - assert (Ht:Two a j z).
    { destruct (Nat.eq_dec (z mod 2) 0%nat) as [Hz|Hz]; [right|left; lia].
      destruct (GCounterRun_even _ _ _ _ _ Hg Hz) as [_ [Ez HmEven]]; lia. }
    destruct (Nat.eq_dec k 2) as [->|Hlarge]; [apply S2, Ht|].
    apply SN; [lia|lia|].
    destruct (Nat.eq_dec (z mod 2) 1%nat) as [Hodd|Hodd]; [left; exact Hodd|].
    assert (Heven:z mod 2=0%nat) by lia.
    assert (Hlower:(a-j)*2+2<=z) by (destruct Ht; lia).
    right; split; [exact Hlower|].
    destruct (le_dec (k+3) h) as [Hsmall|Hedge].
    + assert (Hp:2^(2+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      cbn[Nat.add Nat.pow] in Hp |- *; lia.
    + assert (Ek:k+2=h) by lia.
      rewrite <-Ek in Hsize; replace (k+2-1) with (1+k) in Hsize by lia.
      destruct (ICounterRun_linear _ _ _ _ _ Hi) as [Em Ec]; [lia|].
      destruct (GCounterRun_even _ _ _ _ _ Hg Heven) as [_ [Ez _]]; lia.
Qed.

Lemma even_birth_capacity a b j n k q m c z e : a<=b -> b<=a+1 -> j<=a ->
  n<=a*4 -> 0<k -> n*2+j*4+4=(q*2+1)*2^k ->
  CounterRun (ICounter k) (b+j) 1 m c -> CounterRun (GCounter k) (a-j) m z e ->
  phi z+(2^k-1)*(q+(c+e)*2)<=(a*2+b+1)*4.
Proof.
  intros Hab Hba Hj Hn Hk He Hi Hg.
  pose proof (split_capacity _ _ _ _ _ _ _ q Hk Hi Hg) as E.
  clear Hi Hg; counter_arith.
Qed.

Lemma even_birth_small_root h a b j fs n q m c z e xs s : Level h a b fs -> j<=a ->
  n<=a*4 -> n*2+j*4+4=(q*2+1)*2 ->
  CounterRun (ICounter 1) (b+j) 1 m c -> CounterRun (GCounter 1) (a-j) m z e ->
  Word 1 z xs -> Num (q+(c+e)*2) s -> SRoot (cfg (fs*>w^^j*>xs*>s)).
Proof.
  intros Hl Hj Hn He Hi Hg Hw Hs.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  assert (Hm:0<m) by (eapply ICounterRun_positive; [exact Hi|lia]).
  assert (Hz:0<z) by (eapply GCounterRun_positive; eassumption).
  assert (Hmb:m<4) by (apply (ICounterRun_bound _ _ _ _ _ Hi); cbn; lia).
  pose proof (Word_bound _ _ _ Hw) as Hzb; cbn[Nat.add Nat.pow] in Hzb.
  assert (Hvalue:phi z+(q+(c+e)*2)<=(a*2+b+1)*4).
  { pose proof (even_birth_capacity _ _ _ _ 1 _ _ _ _ _ Hab Hba Hj Hn ltac:(lia) He Hi Hg).
    cbn[Nat.pow] in H; lia. }
  destruct (Nat.eq_dec j a) as [Hedge|Hedge].
  - eapply sroot; [exact Hl|exact Hj|].
    eapply SWord with (k:=1%nat) (n:=z) (q:=q+(c+e)*2);
      [lia|exact Hz|exact Hw|exact Hs|apply S1; left; exact Hedge|cbn[Nat.pow]; lia].
  - destruct (Nat.eq_dec z 3) as [->|Hz3].
    + pose proof (ICounterRun_balance _ _ _ _ _ Hi) as E0.
      pose proof (GCounterRun_balance _ _ _ _ _ Hg ltac:(lia) Hm) as E1.
      pose proof (phi_bounds _ Hm).
      assert (Htail:q+(c+e)*2<=a*8) by
        (change (3+e*2=phi m+(a-j)*2) in E1; cbn[Nat.add Nat.pow] in E0; lia).
      rewrite (Word_max _ _ _ Hw eq_refl); change (SRoot (cfg (fs*>w^^j*>w*>s))).
      assert (En:w^^j*>w*>s=w^^(j+1)*>s) by (rewrite lpow_add, Str_app_assoc; reflexivity).
      rewrite En; eapply sroot; [exact Hl|lia|eapply SNum; eassumption].
    + assert (HU:a-j=1%nat).
      { destruct (le_dec 2 (a-j)) as [Htwo|Htwo]; [|lia].
        assert (Hrun:CounterRun (GCounter 1) (2+(a-j-2)) m z e) by (applys_eq Hg; flia).
        destruct (GCounterRun_one _ _ _ _ Hrun Hm Hmb) as [Ez _]; lia. }
      assert (Ez:z=1%nat).
      { destruct (Nat.eq_dec (z mod 2) 0%nat) as [Heven|Heven]; [|lia].
        destruct (GCounterRun_even _ _ _ _ _ Hg Heven) as [_ [Ez _]]; lia. }
      subst z.
      assert (Htail:q+(c+e)*2+1<=(a*2+b+1)*2).
      { pose proof (split_capacity 1 _ _ _ _ _ _ q ltac:(lia) Hi Hg) as E.
        cbn[Nat.pow phi] in E; lia. }
      eapply sroot; [exact Hl|exact Hj|].
      eapply SWord with (k:=1%nat) (n:=1%nat) (q:=q+(c+e)*2);
        [lia|lia|exact Hw|exact Hs|apply S1; right; repeat split; lia|cbn[Nat.pow]; lia].
Qed.

Lemma pure_even_closed h a b j fs n r : Level h a b fs -> j<=a ->
  Num (n*2) r -> n<=a*4 -> exists c, SRoot c /\ cfg (fs*>w^^j*>r) -->+ c.
Proof.
  intros Hl Hj Hr Hn; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (pure_even _ _ _ _ _ _ (level_frame _ _ _ _ Hl) Hj Hr)
    as (k&q&m&c&z&e&xs&s&Hk&He&Hi&Hg&Hw&Hs&Hstep).
  eexists; split; [|exact Hstep].
  destruct (Nat.eq_dec k 1) as [->|Hlarge].
  - eapply even_birth_small_root; eassumption.
  - eapply sroot; [exact Hl|exact Hj|].
    eapply SWord with (k:=k) (n:=z) (q:=q+(c+e)*2).
    + exact Hk.
    + eapply GCounterRun_positive; [exact Hg|eapply ICounterRun_positive; [exact Hi|lia]].
    + exact Hw.
    + exact Hs.
    + eapply even_birth_phase; eauto; lia.
    + exact (even_birth_capacity _ _ _ _ _ _ _ _ _ _ Hab Hba Hj Hn Hk He Hi Hg).
Qed.

Lemma pure_closed h a b j fs n r : Level h a b fs -> j<=a ->
  Num n r -> n<=a*8 -> exists c, SRoot c /\ cfg (fs*>w^^j*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hbound; destruct Hn as [|n r Hr|n r Hr].
  - eapply pure_even_closed with (n:=0%nat); [exact Hl|exact Hj|constructor|lia].
  - eapply pure_even_closed; [exact Hl|exact Hj|constructor; exact Hr|lia].
  - destruct (Nat.eq_dec j a) as [->|Hinside].
    + eapply pure_odd_boundary_closed; eassumption.
    + destruct Hr as [|n r Hr|n r Hr].
      * pose proof (pure_one_closed h a b j fs 0 _ Hl ltac:(lia) Num0 ltac:(lia)) as H.
        cbn[Str_app] in H |- *; fold (const (0:Sym)) in H |- *.
        repeat rewrite <-const_unfold in H; repeat rewrite <-const_unfold; exact H.
      * eapply pure_one_closed; [exact Hl|lia|exact Hr|lia].
      * eapply pure_three_closed; [exact Hl|lia|exact Hr|lia].
Qed.

Lemma small_single_root h a b j fs k n xs q r : Level h a b fs -> j<=a ->
  0<k -> k+3<=h -> 0<n -> Word k n xs -> Num q r ->
  phi n+(2^k-1)*q<=(a*2+b+1)*2 ->
  (n mod 2=0%nat -> (a-j)*2+2<=n) ->
  (k=1%nat -> j+2<=a -> n=3%nat) -> SRoot (cfg (fs*>w^^j*>xs*>r)).
Proof.
  intros Hl Hj Hk Hwidth Hn Hw Hr Hcap Hlower Hsmall.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (Nat.eq_dec k 1) as [->|Hlarge].
  - pose proof (Word_bound _ _ _ Hw) as Hnb; cbn[Nat.pow] in Hnb, Hcap.
    destruct (Nat.eq_dec j a) as [Hedge|Hedge].
    + eapply sroot; [exact Hl|exact Hj|].
      eapply SWord with (k:=1%nat) (n:=n) (q:=q);
        [lia|exact Hn|exact Hw|exact Hr|apply S1; left; exact Hedge|cbn[Nat.pow]; lia].
    + destruct (Nat.eq_dec n 3) as [->|Hnot].
      * rewrite (Word_max _ _ _ Hw eq_refl).
        change (SRoot (cfg (fs*>w^^j*>w*>r))).
        assert (En:w^^j*>w*>r=w^^(j+1)*>r) by (rewrite lpow_add, Str_app_assoc; reflexivity).
        rewrite En; eapply sroot; [exact Hl|lia|eapply SNum; [exact Hr|unfold phi in Hcap; lia]].
      * assert (Hnear:j+1=a) by (specialize (Hsmall eq_refl); lia).
        assert (En:n=1%nat).
        { destruct (Nat.eq_dec (n mod 2) 0%nat); [specialize (Hlower e)|]; lia. }
        subst n; eapply sroot; [exact Hl|exact Hj|].
        eapply SWord with (k:=1%nat) (n:=1%nat) (q:=q);
          [lia|lia|exact Hw|exact Hr| |cbn[Nat.pow]; lia].
        apply S1; right; repeat split; try lia.
        change (1+(2^1-1)*q<=(a*2+b+1)*2) in Hcap; cbn[Nat.pow] in Hcap.
        lia.
  - eapply sroot; [exact Hl|exact Hj|].
    eapply SWord with (k:=k) (n:=n) (q:=q); try eassumption; [|lia].
    destruct (Nat.eq_dec k 2) as [->|Htwo].
    + apply S2; destruct (Nat.eq_dec (n mod 2) 1%nat); [left|right; apply Hlower]; lia.
    + apply SN; [lia|lia|].
      destruct (Nat.eq_dec (n mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
      right; specialize (Hlower ltac:(lia)); split; [exact Hlower|].
      assert (Hp:2^(2+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia.
Qed.

Lemma narrow_closed h a b j fs k n xs q r : Level h a b fs -> j<=a ->
  3<=k -> k+2<=h -> 0<n -> Word k n xs -> Num q r -> Narrow a j k n ->
  phi n+(2^k-1)*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hk Hwidth Hn Hw Hr Hguard Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  assert (Hinner:n mod 2=1%nat \/ 2^(1+k)<=n+j*4) by (destruct Hguard as [H|[_ H]]; auto).
  assert (Htail:forall c, exists s, Num (q+c*2) s /\ G c r s) by (intro c; apply G_nums, Hr).
  destruct k as [|[|[|k]]]; try lia.
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - assert (HB:2^(2+k)<=b+a).
    { assert (Hp:2^(4+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia. }
    destruct (narrow_boundary (fun c=>Num (q+c*2)) a b fs (2+k) n xs q r
      (level_frame _ _ _ _ Hl) Hw ltac:(lia) Hn Htail Hinner HB Hcap)
      as (z&c&ys&s&Hys&Hodd&Hs&Hg&Hvalue&Hcalls&Hstep).
    eexists; split; [|exact Hstep].
    apply (small_single_root (1+h) (a+b) (a*2+1) 0 _ (2+k) z ys (q+c*2) s);
      try assumption; try lia.
    apply Level_next, Hl.
  - assert (HB:2^(2+k)<=b+j).
    { assert (Hp:2^(4+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia. }
    destruct (narrow_inside (fun c=>Num (q+c*2)) a b j fs (1+k) n xs q r
      (level_frame _ _ _ _ Hl) ltac:(lia) Hw ltac:(lia) Hn Htail Hinner HB Hcap)
      as (z&c&ys&s&Hys&Hz&Hs&Hg&Hvalue&Hlower&Hsmall&Hcalls&Hstep).
    eexists; split; [|exact Hstep].
    apply (small_single_root h a b (j+1) fs (1+k) z ys (q+c*2) s);
      try assumption; try lia.
Qed.

Lemma end_single_root h a b j fs n r : Level h a b fs -> j<a -> Num n r ->
  n+4<(a*2+b+1)*4 -> n+(a-j)*2+2<=(a*2+b+1)*4 ->
  exists s, G (a-j) (d*>r) s /\ SRoot (cfg (fs*>w^^j*>s)).
Proof.
  intros Hl Hj Hr Hbirth Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (G_end_word n r (a-j) Hr ltac:(lia))
    as (k&q&z&c&xs&s&He&Hc&Hw&Hs&Hodd&Hvalue&Hg).
  exists (xs*>s); split; [exact Hg|].
  assert (Hwidth:1+k<=h+1).
  { assert (2^k<2^(h+1)).
    { replace (h+1) with (2+(h-1)) by lia; cbn[Nat.add Nat.pow].
      rewrite <-(level_size _ _ _ _ Hl); nia. }
    apply Nat.pow_lt_mono_r_iff in H; lia. }
  destruct k as [|k].
  - assert (Ez:z=3%nat).
    { pose proof (Word_bound _ _ _ Hw) as Hb; cbn[Nat.pow] in Hb.
      destruct (a-j-1) eqn:Ei; [inversion Hc; lia|].
      pose proof (GCounterRun_three _ _ _ _ _ Hc ltac:(lia) eq_refl); lia. }
    subst z; pose proof (GCounterRun_balance _ _ _ _ _ Hc ltac:(lia) ltac:(lia)) as E.
    assert (Htail:q+c*2<=a*8).
    { change (3+c*2=3+(a-j-1)*2) in E; cbn[Nat.pow] in He; lia. }
    rewrite (Word_max _ _ _ Hw eq_refl); change (SRoot (cfg (fs*>w^^j*>w*>s))).
    assert (En:w^^j*>w*>s=w^^(j+1)*>s) by (rewrite lpow_add, Str_app_assoc; reflexivity).
    rewrite En; eapply sroot; [exact Hl|lia|eapply SNum; eassumption].
  - eapply sroot; [exact Hl|lia|].
    change (phi z+(2^(2+k)-1)*(q+c*2)<=n+(a-j)*2+2) in Hvalue.
    eapply SWord with (k:=2+k) (n:=z) (q:=q+c*2); try eassumption; try lia.
    apply single_odd_phase; try lia.
    intro Hwide; split; [|right; exact Hj].
    assert (Hp:2^(h-1)<=2^(2+k)) by (apply Nat.pow_le_mono_r; lia).
    rewrite <-(level_size _ _ _ _ Hl) in Hp.
    destruct (GCounterRun_linear _ _ _ _ _ Hc) as [Ez _];
      [cbn[Nat.add Nat.pow] in Hp |- *; lia|lia].
Qed.

Lemma two_closed h a b j fs n xs q r : Level h a b fs -> j<=a ->
  0<n -> Word 2 n xs -> Num q r -> Two a j n ->
  phi n+3*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hw Hr Hphase Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (Word_bound _ _ _ Hw) as Hnb; cbn[Nat.pow] in Hnb.
  assert (Hguard:n mod 2=1%nat \/ 8<=n+j*4) by (destruct Hphase; [left|right]; lia).
  destruct (counter_inner_total 2 j n ltac:(lia) Hnb Hguard)
    as (u&c0&Hu&Hub&H0).
  destruct (CounterRun_total _ _ (fun z=>GCounter_total 1 z ltac:(lia)) (b+j) u Hub)
    as (z&c1&H1&Hzb).
  assert (Hrun:CounterRun (GCounter 1) (2+(b+j-2)) u z c1) by (applys_eq H1; flia).
  destruct (GCounterRun_one _ _ _ _ Hrun Hu Hub) as (Ez&Hc1lo&Hc1hi); subst z.
  pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) Hn) as E0.
  rewrite phi_odd in E0; cbn[Nat.pow] in E0.
  assert (Hc0:c0*6<=phi n+j*4+1) by lia.
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - destruct (G_nums (c0+c1) _ _ Hr) as (s&Hs&Hg).
    eexists; split; [|eapply two_boundary; [exact (level_frame _ _ _ _ Hl)|eassumption..]].
    apply (sroot (1+h) (a+b) (a*2+1) 1); [apply Level_next, Hl|lia|].
    eapply SNum; [exact Hs|lia].
  - destruct (G_nums (c0+(c1+2)) _ _ Hr) as (s&Hs&Hg).
    destruct (Nat.eq_dec (j+1) a) as [Hedge|Hedge].
    + assert (Hstep:cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>d*>s)).
      { eapply two_inside; [exact (level_frame _ _ _ _ Hl)|lia|eassumption..|].
        replace (a-j-1) with 0%nat by lia; constructor. }
      eexists; split; [|exact Hstep].
      rewrite Hedge, <-!Str_app_assoc, <-app_assoc.
      apply (sroot (1+h) (a+b) (a*2+1) 0); [apply Level_next, Hl|lia|].
      eapply SNum; [exact Hs|lia].
    + destruct (end_single_root h a b (j+1) fs _ s Hl ltac:(lia) Hs ltac:(lia) ltac:(lia))
        as (out&Hout&Hroot).
      exists (cfg (fs*>w^^(j+1)*>out)); split; [exact Hroot|].
      eapply two_inside; [exact (level_frame _ _ _ _ Hl)|lia|eassumption..|].
      applys_eq Hout; flia.
Qed.

Lemma one_boundary_closed h a b fs n xs q r : Level h a b fs ->
  0<n -> Word 1 n xs -> Num q r -> phi n+q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^a*>xs*>r) -->+ c.
Proof.
  intros Hl Hn Hw Hr Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (Word_bound _ _ _ Hw) as Hnb.
  destruct (CounterRun_total _ _ (fun z=>GCounter_total 1 z ltac:(lia)) (a*2+2) n Hnb)
    as (z&c&Hc&Hzb).
  assert (Hrun:CounterRun (GCounter 1) (2+a*2) n z c) by (applys_eq Hc; flia).
  destruct (GCounterRun_one _ _ _ _ Hrun Hn Hnb) as (Ez&Hclo&Hchi); subst z.
  destruct (G_nums c _ _ Hr) as (s&Hs&Hg).
  destruct (end_single_root (1+h) (a+b) (a*2+1) 0 (fs++w^^a++d) _ s
    (Level_next _ _ _ _ Hl) ltac:(lia) Hs ltac:(lia) ltac:(lia)) as (out&Hout&Hroot).
  exists (cfg ((fs++w^^a++d)*>out)); split; [exact Hroot|].
  eapply one_boundary; [exact (level_frame _ _ _ _ Hl)|exact Hw|right; lia|exact Hc|exact Hg|].
  applys_eq Hout; flia.
Qed.

Lemma one_neighbor_split a b j fs xs r s k n ys tail m c out :
  Frame a b fs -> j+1=a -> Word 1 1 xs -> G (j*2+1) r s ->
  G (b+j) (d*>s) (ys*>tail) -> Word (1+k) n ys -> n mod 2=1%nat ->
  CounterRun (GCounter (1+k)) 2 n (m*2+1) c -> G c tail out ->
  exists zs, Word k m zs /\
    cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>zs*>out).
Proof.
  intros Hf Hj Hw Hg Hmid Hy Hodd Hc Hout.
  destruct (P_counter_run _ _ _ _ _ _ _ _ Hy ltac:(lia) Hodd Hc Hout) as (vs&Hv&Hp).
  destruct (Word_odd_inv _ _ _ Hv) as (zs&Hz&Ev); subst vs.
  assert (Hfirst:CounterRun (GCounter 1) (j*2+2) 1 3 (j*2+1))
    by (applys_eq (counter_one_start (j*2+1)); flia).
  destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) (or_introl eq_refl) Hfirst Hg)
    as (ws&Hws&Hin).
  rewrite (Word_max _ _ _ Hws eq_refl) in Hin.
  exists zs; split; [exact Hz|].
  rewrite (lpow_add _ j 1), Str_app_assoc; apply (frame_step _ _ _ Hf).
  eapply inner_column; [lia|exact Hin|apply G_d, Hmid|].
  replace (a-j) with 1%nat by lia; apply P_G.
  change (P 1 (d*>ys*>tail) (u*>t*>zs*>out)).
  apply P_d; rewrite Str_app_assoc in Hp; exact Hp.
Qed.

Lemma neighbor_birth_root h a b fs q k t m c xs r : Level h a b fs ->
  q+1<=(a*2+b+1)*2 -> q+a*4+2=(t*2+1)*2^k ->
  CounterRun (GCounter (1+k)) (a+b) 3 (m*2+1) c ->
  0<m -> Word k m xs -> Num (t+c*2) r -> SRoot (cfg (fs*>w^^a*>xs*>r)).
Proof.
  intros Hl Hq He Hc Hm Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (GCounterRun_balance _ _ _ _ _ Hc ltac:(lia) ltac:(lia)) as E.
  rewrite phi_odd in E; change (m*2+1+c*((2^(1+k)-1)*2)=3+(a+b)*2) in E.
  assert (Ebal:m+(2^(1+k)-1)*c=a+b+1) by nia.
  assert (Hbirth:q+a*4+2<(a*2+b+1)*4) by lia.
  destruct (Nat.eq_dec k 0) as [->|Hk].
  - pose proof (Word_bound _ _ _ Hw) as Hmb; cbn[Nat.pow] in Hmb.
    assert (m=1%nat) by lia; subst m.
    rewrite (Word_max _ _ _ Hw eq_refl); change (SRoot (cfg (fs*>w^^a*>d*>r))).
    rewrite <-!Str_app_assoc, <-app_assoc.
    apply (sroot (1+h) (a+b) (a*2+1) 0); [apply Level_next, Hl|lia|].
    eapply SNum; [exact Hr|cbn[Nat.pow] in He, Ebal; lia].
  - assert (Hwidth:k<=h).
    { assert (2^k<2^(h+1)).
      { replace (h+1) with (2+(h-1)) by lia; cbn[Nat.add Nat.pow].
        rewrite <-(level_size _ _ _ _ Hl); nia. }
      apply Nat.pow_lt_mono_r_iff in H; lia. }
    assert (Hvalue:phi m+(2^k-1)*(t+c*2)<=(a*2+b+1)*4).
    { pose proof (phi_bounds _ Hm); clear Hc; cbn[Nat.add Nat.pow] in Ebal; counter_arith. }
    eapply sroot; [exact Hl|lia|].
    eapply SWord with (k:=k) (n:=m) (q:=t+c*2); try eassumption; [lia|].
    destruct (le_dec h (k+1)) as [Hwide|Hnarrow].
    + assert (Hp:2^(h-1)<=2^k) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp.
      destruct (GCounterRun_linear _ _ _ _ _ Hc) as [Em Ec];
        [cbn[Nat.add Nat.pow]; lia|].
      subst c; replace (t+0*2) with t by lia.
      replace m with (a*2+b+1-a) by lia; apply SX.
      destruct (Nat.eq_dec h (k+1)) as [Heq|Heq].
      * left; split; [exact Heq|].
        pose proof (level_size _ _ _ _ Hl) as Hsize; rewrite Heq in Hsize.
        replace (k+1-1) with k in Hsize by lia; nia.
      * right; left; assert (Ek:k=h) by lia; split; [exact Ek|].
        assert (Hp':2^k=(a*2+b+1)*2).
        { rewrite Ek; replace h with (1+(h-1)) at 1 by lia; cbn[Nat.add Nat.pow].
          rewrite <-(level_size _ _ _ _ Hl); lia. }
        nia.
    + destruct (Nat.eq_dec k 1) as [->|Hone]; [apply S1; left; reflexivity|].
      destruct (Nat.eq_dec k 2) as [->|Htwo].
      * apply S2; destruct (Nat.eq_dec (m mod 2) 1%nat); [left|right]; lia.
      * apply SN; [lia|lia|].
        destruct (Nat.eq_dec (m mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
        right; split; [lia|].
        assert (Hp:2^(1+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
        rewrite <-(level_size _ _ _ _ Hl) in Hp; lia.
Qed.

Lemma one_neighbor_closed h a b j fs xs q r : Level h a b fs -> j+1=a ->
  Word 1 1 xs -> Num q r -> q+1<=(a*2+b+1)*2 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hw Hr Hq; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (G_nums (j*2+1) _ _ Hr) as (s&Hs&Hg).
  destruct (G_end_word _ _ (b+j) Hs ltac:(lia))
    as (k&t&n&c&ys&tail&He&Hc&Hy&Htail&Hodd&Hvalue&Hmid).
  destruct (counter_inner_total (1+k) 0 n ltac:(lia) (Word_bound _ _ _ Hy) (or_introl Hodd))
    as (m&c'&Hm&Hmb&Hlast).
  destruct (G_nums c' _ _ Htail) as (out&Hout&Hfinal).
  destruct (one_neighbor_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (level_frame _ _ _ _ Hl) Hj Hw Hg Hmid Hy Hodd Hlast Hfinal) as (zs&Hz&Hstep).
  eexists; split; [|exact Hstep]; rewrite Hj.
  eapply neighbor_birth_root with (q:=q) (k:=k) (t:=t) (m:=m) (c:=c+c');
    [exact Hl|exact Hq|lia| |exact Hm|exact Hz|applys_eq Hout; flia].
  pose proof (CounterRun_add _ _ _ _ _ _ _ _ Hc Hlast) as Hrun; applys_eq Hrun; flia.
Qed.

(* A right word carries an explicit sufficient saturation budget. *)
Inductive Atom : nat -> nat -> nat -> side -> Prop :=
| AtomWord k tau n q xs r : 0<k -> 0<n -> Word k n xs -> Num q r ->
    tau<=2^k -> (n mod 2=1%nat \/ 2^(1+k)<=n+tau*2) ->
    Atom k tau (phi n+(2^k-1)*q) (xs*>r)
| AtomEnd q r : Num q r -> q<=1 -> Atom 1 1 (q*2+1) (d*>r).

Inductive Sat L : nat -> side -> Prop :=
| SatWord k n q xs r : 0<k -> k<=L -> Word k n xs -> Num q r ->
    n mod 2=1%nat -> (k=1%nat -> n=3%nat) ->
    Sat L (phi n+(2^k-1)*q) (xs*>r).

Lemma Atom_value k tau x r : Atom k tau x r -> Value x r.
Proof. intro H; destruct H; [eapply ValueWord; eauto using ValueNum|apply ValueEnd; assumption]. Qed.

Lemma Atom_bound k tau x r : Atom k tau x r -> 0<k /\ tau<=2^k.
Proof. intro H; destruct H; split; cbn; lia. Qed.

Lemma Sat_value L x r : Sat L x r -> Value x r.
Proof. intro H; destruct H; eapply ValueWord; eauto using ValueNum; lia. Qed.

Lemma Sat_mono L M x r : Sat L x r -> L<=M -> Sat M x r.
Proof. intros H Hle; destruct H; econstructor; eauto; lia. Qed.

Lemma G_word_data k n xs q r i : 0<k -> Word k n xs -> Num q r ->
  exists m c ys s, CounterRun (GCounter k) i n m c /\
    Word k m ys /\ Num (q+c*2) s /\ G i (xs*>r) (ys*>s).
Proof.
  intros Hk Hw Hr.
  destruct (CounterRun_total _ _ (fun n=>GCounter_total k n Hk) i n (Word_bound _ _ _ Hw))
    as (m&c&Hc&Hmb).
  destruct (G_nums c _ _ Hr) as (s&Hs&Hg).
  destruct (G_counter_run _ _ _ _ _ _ _ _ Hw Hk Hc Hg) as (ys&Hy&Hrun).
  exists m, c, ys, s; repeat split; assumption.
Qed.

Lemma GCounterRun_one_three i n m c : CounterRun (GCounter 1) i n m c -> n=3%nat -> m=3%nat.
Proof. intro H; induction H; intro Hn; [lia|apply IHCounterRun; destruct H; cbn[Nat.pow] in *; lia]. Qed.

Lemma G_sat L x r i : Sat L x r -> exists s, Sat L (x+i*2) s /\ G i r s.
Proof.
  intro Hsat; destruct Hsat as [k n q xs r Hk HL Hw Hr Hodd Hsmall].
  destruct (G_word_data _ _ _ _ _ i Hk Hw Hr) as (m&c&ys&s&Hc&Hy&Hs&Hg).
  exists (ys*>s); split; [|exact Hg].
  pose proof (GCounterRun_balance _ _ _ _ _ Hc Hk ltac:(lia)) as E.
  replace (phi n+(2^k-1)*q+i*2) with (phi m+(2^k-1)*(q+c*2)) by nia.
  econstructor; try eassumption.
  - eapply GCounterRun_odd; eassumption.
  - intro Ek; subst k; eapply GCounterRun_one_three; [exact Hc|apply Hsmall; reflexivity].
Qed.

Lemma G_atom_sat k tau x r i : Atom k tau x r -> 2<=i -> tau<=i ->
  exists s, Sat (Nat.max k 3) (x+i*2) s /\ G i r s.
Proof.
  intros H Hi Htau; destruct H as [k tau n q xs r Hk Hn Hw Hr Htb Hguard|q r Hr Hq].
  - destruct (G_word_data _ _ _ _ _ i Hk Hw Hr) as (m&c&ys&s&Hc&Hy&Hs&Hg).
    exists (ys*>s); split; [|exact Hg].
    pose proof (GCounterRun_balance _ _ _ _ _ Hc Hk Hn) as E.
    replace (phi n+(2^k-1)*q+i*2) with (phi m+(2^k-1)*(q+c*2)) by nia.
    econstructor; try eassumption; [lia| |].
    + destruct Hguard as [Hodd|Hsat].
      * eapply GCounterRun_odd; eassumption.
      * eapply GCounterRun_saturated; [exact Hc|exact Hk|eapply Word_bound; exact Hw|lia].
    + intro Ek; subst k; replace i with (2+(i-2)) in Hc by lia.
      exact (proj1 (GCounterRun_one _ _ _ _ Hc Hn (Word_bound _ _ _ Hw))).
  - assert (Hfirst:exists s, Sat 3 (q*2+3) s /\ G1 (d*>r) s).
    { destruct (Nat.eq_dec q 0%nat) as [->|Hnz].
      - rewrite (Num_zero _ _ Hr eq_refl); exists ((t++one 2)*>0inf); split; [|exact G_zero0].
        change (Sat 3 (phi 3+(2^3-1)*0) ((t++one 2)*>0inf)).
        econstructor; [lia|lia|exact (Word10 _ _ _ (Word_one 2))|constructor|reflexivity|lia].
      - assert (q=1%nat) by lia; subst q; rewrite (Num_one _ _ Hr eq_refl).
        exists (w*>[0;0;1;0]*>0inf); split; [|exact G_zero1].
        change (Sat 3 (phi 3+(2^1-1)*2) (w*>[0;0;1;0]*>0inf)).
        econstructor; [lia|lia|exact (Word10 _ _ _ Word1)| |reflexivity|lia].
        apply (Num00 1), (Num10 0), Num0. }
    destruct Hfirst as (s0&H0&G0); destruct (G_sat _ _ _ (i-1) H0) as (s&Hs&Hg).
    exists s; split; [applys_eq Hs; flia|].
    replace i with (1+(i-1)) by lia; econstructor; eassumption.
Qed.

Lemma sat_single_root h a b j fs x r : Level h a b fs -> j<=a ->
  Sat (h-2) x r -> x<=(a*2+b+1)*2 -> SRoot (cfg (fs*>w^^j*>r)).
Proof.
  intros Hl Hj Hsat Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct Hsat as [k n q xs r Hk HL Hw Hr Hodd Hsmall].
  destruct (Nat.eq_dec k 1) as [->|Hlarge].
  - specialize (Hsmall eq_refl); subst n; destruct (Nat.eq_dec j a) as [Hedge|Hedge].
    + eapply sroot; [exact Hl|exact Hj|].
      eapply SWord with (k:=1%nat) (n:=3%nat) (q:=q); try eassumption; try lia.
      apply S1; left; exact Hedge.
    + rewrite (Word_max _ _ _ Hw eq_refl); change (SRoot (cfg (fs*>w^^j*>w*>r))).
      assert (En:w^^j*>w*>r=w^^(j+1)*>r) by (rewrite lpow_add, Str_app_assoc; reflexivity).
      rewrite En; eapply sroot; [exact Hl|lia|].
      eapply SNum; [exact Hr|cbn[Nat.pow phi] in Hcap; lia].
  - eapply sroot; [exact Hl|exact Hj|].
    eapply SWord with (k:=k) (n:=n) (q:=q); try eassumption; try lia.
    destruct (Nat.eq_dec k 2) as [->|Htwo].
    + apply S2; left; exact Hodd.
    + apply SN; [lia|lia|left; exact Hodd].
Qed.

Lemma d_sat_finish h a b j fs x r : Level h a b fs -> j<=a -> Sat (h-2) x r ->
  x+5<(a*2+b+1)*4 -> x+(a-j)*4+3<=(a*2+b+1)*4 ->
  exists child s, P 1 (d*>r) (w*>child) /\ G (a-j) child s /\
    SRoot (cfg (fs*>w^^j*>s)).
Proof.
  intros Hl Hj Hsat Hbirth Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct Hsat as [k n q xs r Hk HL Hw Hr Hodd Hsmall].
  destruct k as [|k]; [lia|].
  destruct k as [|k].
  - specialize (Hsmall eq_refl); subst n; rewrite (Word_max _ _ _ Hw eq_refl).
    change (exists child s, P 1 (d*>w*>r) (w*>child) /\ G (a-j) child s /\
      SRoot (cfg (fs*>w^^j*>s))).
    destruct (G_nums 2 _ _ Hr) as (r0&H0&G0).
    change (3+(2^1-1)*q+5<(a*2+b+1)*4) in Hbirth.
    change (3+(2^1-1)*q+(a-j)*4+3<=(a*2+b+1)*4) in Hcap.
    cbn[Nat.pow] in Hbirth, Hcap.
    assert (Hfirst:P 1 (d*>w*>r) (w*>d*>r0)) by (apply P_d, G_w, G0).
    destruct (Nat.eq_dec j a) as [->|Hedge].
    + exists (d*>r0), (d*>r0); split; [exact Hfirst|]; split;
        [replace (a-a) with 0%nat by lia; constructor|].
      rewrite <-!Str_app_assoc, <-app_assoc.
      apply (sroot (1+h) (a+b) (a*2+1) 0); [apply Level_next, Hl|lia|].
      eapply SNum; [exact H0|lia].
    + destruct (end_single_root h a b j fs _ r0 Hl ltac:(lia) H0 ltac:(lia) ltac:(lia))
        as (s&Hs&Hroot).
      exists (d*>r0), s; repeat split; assumption.
  - destruct (odd_d_value Num (1+k) n xs q r (a-j) Hw ltac:(lia) Hodd
      (fun c=>G_nums c _ _ Hr)) as (z&c&ys&s&Hy&Hz&Hs&Hvalue&Hlower&Hsmall'&Hp&child&Hfirst&Hrest).
    exists child, (ys*>s); split; [exact Hfirst|]; split; [exact Hrest|].
    change (phi n+(2^(2+k)-1)*q+(a-j)*4+3<=(a*2+b+1)*4) in Hcap.
    change ((phi z+(2^(1+k)-1)*(q+c*2))*2<=phi n+(2^(2+k)-1)*q+3+(a-j)*4) in Hvalue.
    apply (small_single_root h a b j fs (1+k) z ys (q+c*2) s); try assumption; lia.
Qed.

Lemma d_sat_root h a b j fs x r : Level h a b fs -> j<a -> Sat (h-2) x r ->
  x+5<(a*2+b+1)*4 -> x+(a-j)*4<=(a*2+b+1)*4 ->
  exists s, P (a-j) (d*>r) s /\ SRoot (cfg (fs*>w^^j*>s)).
Proof.
  intros Hl Hj Hsat Hbirth Hcap.
  destruct (d_sat_finish h a b (j+1) fs x r Hl ltac:(lia) Hsat Hbirth ltac:(lia))
    as (child&s&Hfirst&Hrest&Hroot).
  exists (w*>s); split.
  - replace (a-j) with (1+(a-(j+1))) by lia.
    eapply P_add; [exact Hfirst|apply G_w, Hrest].
  - rewrite (lpow_add _ j 1), Str_app_assoc in Hroot; exact Hroot.
Qed.

Lemma atom_level_budget h a b fs l tau x r : Level h a b fs -> l+2<=h ->
  Atom l tau x r -> tau<=a*2-1.
Proof.
  intros Hl Hwidth Hr; pose proof (Level_bounds _ _ _ _ Hl).
  pose proof (Atom_bound _ _ _ _ Hr).
  assert (Hp:2^(1+l)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
  rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp; lia.
Qed.

Lemma atom_sat_level h a b fs l tau x r i : Level h a b fs -> l+2<=h ->
  Atom l tau x r -> 2<=i -> tau<=i ->
  exists s, Sat (h-2) (x+i*2) s /\ G i r s.
Proof.
  intros Hl Hwidth Hr Hi Htau; pose proof (level_height _ _ _ _ Hl).
  destruct (G_atom_sat _ _ _ _ _ Hr Hi Htau) as (s&Hs&Hg).
  exists s; split; [eapply Sat_mono; [exact Hs|lia]|exact Hg].
Qed.

Lemma two_count_bounds b j n u c0 c1 : 0<n -> n<8 ->
  (n mod 2=1%nat \/ 8<=n+j*4) ->
  CounterRun (GCounter 2) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter 1) (b+j) u 3 c1 ->
  c0*6<=phi n+j*4+1 /\ b+j-1<=c1 /\ c1<=b+j.
Proof.
  intros Hn Hnb Hguard H0 H1.
  pose proof (counter_inner_phase 2 j n _ _ ltac:(lia) Hnb Hguard H0) as Hphase.
  pose proof (GCounterRun_bound _ _ _ _ _ H0 ltac:(lia) Hnb) as Hub.
  cbn[Nat.pow] in Hub; assert (Hu:0<u) by lia.
  pose proof (phi_bounds _ Hu).
  pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) Hn) as E0.
  pose proof (GCounterRun_balance _ _ _ _ _ H1 ltac:(lia) Hu) as E1.
  rewrite phi_odd in E0; change (3+c1*2=phi u+(b+j)*2) in E1.
  cbn[Nat.pow] in E0; repeat split; lia.
Qed.

Lemma double_two_closed h a b j fs n xs l tau x r u c0 c1 :
  Level h a b fs -> j<=a -> 0<n -> Word 2 n xs -> Two a j n ->
  Atom l tau x r -> l+2<=h ->
  CounterRun (GCounter 2) (j*2+2) n (u*2+1) c0 ->
  CounterRun (GCounter 1) (b+j) u 3 c1 ->
  (j=a \/ tau<=c0+c1+2) -> phi n+3*x<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hw Hphase Hr Hwidth H0 H1 Hbudget Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (Word_bound _ _ _ Hw) as Hnb; cbn[Nat.pow] in Hnb.
  assert (Hguard:n mod 2=1%nat \/ 8<=n+j*4) by (destruct Hphase; [left|right]; lia).
  destruct (two_count_bounds _ _ _ _ _ _ Hn Hnb Hguard H0 H1) as (Hc0&Hc1lo&Hc1hi).
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - pose proof (atom_level_budget _ _ _ _ _ _ _ _ Hl Hwidth Hr) as Htau.
    destruct (atom_sat_level h a b fs l tau x r (c0+c1) Hl Hwidth Hr ltac:(lia) ltac:(lia))
      as (s&Hs&Hg).
    eexists; split; [|eapply two_boundary; [exact (level_frame _ _ _ _ Hl)|eassumption..]].
    apply (sat_single_root (1+h) (a+b) (a*2+1) 1 _ (x+(c0+c1)*2) s);
      [apply Level_next, Hl|lia|eapply Sat_mono; [exact Hs|lia]|lia].
  - destruct (atom_sat_level h a b fs l tau x r (c0+(c1+2)) Hl Hwidth Hr ltac:(lia) ltac:(lia))
      as (s&Hs&Hg).
    destruct (Nat.eq_dec (j+1) a) as [Hedge|Hedge].
    + assert (Hstep:cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>d*>s)).
      { eapply two_inside; [exact (level_frame _ _ _ _ Hl)|lia|eassumption..|].
        replace (a-j-1) with 0%nat by lia; constructor. }
      eexists; split; [|exact Hstep]; rewrite Hedge, <-!Str_app_assoc, <-app_assoc.
      apply (sat_single_root (1+h) (a+b) (a*2+1) 0 _ (x+(c0+(c1+2))*2) s);
        [apply Level_next, Hl|lia|eapply Sat_mono; [exact Hs|lia]|lia].
    + destruct (d_sat_root h a b (j+1) fs _ s Hl ltac:(lia) Hs ltac:(lia) ltac:(lia))
        as (out&Hout&Hroot).
      exists (cfg (fs*>w^^(j+1)*>out)); split; [exact Hroot|].
      eapply two_inside; [exact (level_frame _ _ _ _ Hl)|lia|eassumption..|].
      apply P_G; applys_eq Hout; flia.
Qed.

Lemma double_one_boundary_closed h a b fs n xs l tau x r : Level h a b fs ->
  0<n -> Word 1 n xs -> Atom l tau x r -> l+2<=h -> phi n+x<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^a*>xs*>r) -->+ c.
Proof.
  intros Hl Hn Hw Hr Hwidth Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (Word_bound _ _ _ Hw) as Hnb.
  destruct (CounterRun_total _ _ (fun z=>GCounter_total 1 z ltac:(lia)) (a*2+2) n Hnb)
    as (z&c&Hc&Hzb).
  assert (Hrun:CounterRun (GCounter 1) (2+a*2) n z c) by (applys_eq Hc; flia).
  destruct (GCounterRun_one _ _ _ _ Hrun Hn Hnb) as (Ez&Hclo&Hchi); subst z.
  pose proof (atom_level_budget _ _ _ _ _ _ _ _ Hl Hwidth Hr) as Htau.
  destruct (atom_sat_level h a b fs l tau x r c Hl Hwidth Hr ltac:(lia) ltac:(lia)) as (s&Hs&Hg).
  assert (Hs':Sat ((1+h)-2) (x+c*2) s) by (eapply Sat_mono; [exact Hs|lia]).
  destruct (d_sat_root (1+h) (a+b) (a*2+1) 0 (fs++w^^a++d) _ s
    (Level_next _ _ _ _ Hl) ltac:(lia) Hs' ltac:(lia) ltac:(lia)) as (out&Hout&Hroot).
  exists (cfg ((fs++w^^a++d)*>out)); split; [exact Hroot|].
  eapply one_boundary; [exact (level_frame _ _ _ _ Hl)|exact Hw|right; lia|exact Hc|exact Hg|].
  apply P_G; applys_eq Hout; flia.
Qed.

Lemma double_one_neighbor_closed h a b j fs xs l tau x r : Level h a b fs -> j+1=a ->
  Word 1 1 xs -> Atom l tau x r -> l+2<=h -> 1+x<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hw Hr Hwidth Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (atom_level_budget _ _ _ _ _ _ _ _ Hl Hwidth Hr) as Htau.
  destruct (atom_sat_level h a b fs l tau x r (j*2+1) Hl Hwidth Hr ltac:(lia) ltac:(lia))
    as (s&Hs&Hg).
  assert (Hs':Sat ((1+h)-2) (x+(j*2+1)*2) s) by (eapply Sat_mono; [exact Hs|lia]).
  destruct (d_sat_finish (1+h) (a+b) (a*2+1) 0 (fs++w^^a++d) _ s
    (Level_next _ _ _ _ Hl) ltac:(lia) Hs' ltac:(lia) ltac:(lia))
    as (child&out&Hfirst&Hrest&Hroot).
  assert (Hsplit:G ((b+j-1)+2) child out) by (applys_eq Hrest; flia).
  destruct (G_split _ _ _ _ Hsplit) as (mid&Hbefore&Hafter).
  assert (Hmid:G (b+j) (d*>s) (w*>mid)).
  { apply P_G; replace (b+j) with (1+(b+j-1)) by lia.
    eapply P_add; [exact Hfirst|apply G_w, Hbefore]. }
  exists (cfg ((fs++w^^a++d)*>out)); split; [exact Hroot|].
  replace a with (1+j) by lia; eapply one_neighbor; try eassumption.
  applys_eq (level_frame _ _ _ _ Hl); flia.
Qed.

Inductive DoublePhase h a b j : nat -> nat -> nat -> nat -> Prop :=
| DN k n l tau : 3<=k -> k+2<=h -> Narrow a j k n -> k+l<=h ->
    DoublePhase h a b j k n l tau
| DY l tau : l<=1 -> DoublePhase h a b j (h-1) ((a-j)*2+1) l tau
| D2 n l tau : Two a j n -> l+2<=h -> (j=a \/ tau<=b+j+1) ->
    DoublePhase h a b j 2 n l tau
| D1 n l tau : l+2<=h -> (j=a \/ (j+1=a /\ n=1%nat)) ->
    DoublePhase h a b j 1 n l tau.

Inductive Double h a b j : side -> Prop :=
| DWord k n xs l tau x r : 0<k -> 0<n -> Word k n xs -> Atom l tau x r ->
    DoublePhase h a b j k n l tau -> phi n+(2^k-1)*x<=(a*2+b+1)*4 ->
    Double h a b j (xs*>r).

Inductive DRoot : (Q*tape)%type -> Prop :=
| droot h a b j fs r : Level h a b fs -> j<=a -> Double h a b j r ->
    DRoot (cfg (fs*>w^^j*>r)).

Definition Normal c := SRoot c \/ DRoot c.

Lemma sat_double_root h a b j fs k n xs L x r : Level h a b fs -> j<=a ->
  0<k -> k+3<=h -> 0<n -> Word k n xs -> Sat L x r ->
  k+L<=h -> L+2<=h -> phi n+(2^k-1)*x<=(a*2+b+1)*2 ->
  (n mod 2=0%nat -> (a-j)*2+2<=n) ->
  (k=1%nat -> j+2<=a -> n=3%nat) -> Normal (cfg (fs*>w^^j*>xs*>r)).
Proof.
  intros Hl Hj Hk Hwidth Hn Hw Hr Hrank HL Hcap Hlower Hsmall.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof Hr as Hright; destruct Hright as [l z q ys s Hlpos HlL Hy Hs Hodd Hthree].
  assert (Hat:Atom l 0 (phi z+(2^l-1)*q) (ys*>s)).
  { econstructor; try eassumption; try lia; left; exact Hodd. }
  destruct (Nat.eq_dec k 1) as [->|Hlarge].
  - pose proof (Word_bound _ _ _ Hw) as Hnb; cbn[Nat.pow] in Hnb, Hcap.
    destruct (Nat.eq_dec j a) as [Hedge|Hedge].
    + right; eapply droot; [exact Hl|exact Hj|].
      eapply DWord with (k:=1%nat) (n:=n) (l:=l) (tau:=0%nat);
        try eassumption; try lia.
      apply D1; [lia|left; exact Hedge].
    + destruct (Nat.eq_dec n 3) as [->|Hnot].
      * left; rewrite (Word_max _ _ _ Hw eq_refl).
        change (SRoot (cfg (fs*>w^^j*>w*>ys*>s))).
        assert (En:w^^j*>w*>ys*>s=w^^(j+1)*>ys*>s) by (rewrite lpow_add, Str_app_assoc; reflexivity).
        rewrite En; eapply sat_single_root; [exact Hl|lia|eapply Sat_mono; [exact Hr|lia]|].
        cbn[phi] in Hcap; lia.
      * assert (Hnear:j+1=a) by (specialize (Hsmall eq_refl); lia).
        assert (En:n=1%nat).
        { destruct (Nat.eq_dec (n mod 2) 0%nat); [specialize (Hlower e)|]; lia. }
        subst n; right; eapply droot; [exact Hl|exact Hj|].
        eapply DWord with (k:=1%nat) (n:=1%nat) (l:=l) (tau:=0%nat);
          try eassumption; try lia.
        apply D1; [lia|right; split; [exact Hnear|reflexivity]].
  - right; eapply droot; [exact Hl|exact Hj|].
    eapply DWord with (k:=k) (n:=n) (l:=l) (tau:=0%nat); try eassumption; try lia.
    destruct (Nat.eq_dec k 2) as [->|Htwo].
    + apply D2; [|lia|right; lia].
      destruct (Nat.eq_dec (n mod 2) 1%nat); [left|right; apply Hlower]; lia.
    + apply DN; try lia.
      destruct (Nat.eq_dec (n mod 2) 1%nat) as [Hodd'|Heven]; [left; exact Hodd'|].
      right; specialize (Hlower ltac:(lia)); split; [exact Hlower|].
      assert (Hp:2^(2+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia.
Qed.

Lemma G_atom_ready k tau x r : Atom k tau x r -> forall i, exists s,
  (tau<=i -> 2<=i -> Sat (Nat.max k 3) (x+i*2) s) /\ G i r s.
Proof.
  intros Hr i; destruct (le_dec tau i), (le_dec 2 i).
  - destruct (G_atom_sat _ _ _ _ _ Hr l0 l) as (s&Hs&Hg).
    exists s; split; [intros; exact Hs|exact Hg].
  - destruct (G_value _ _ (Atom_value _ _ _ _ Hr) i) as (s&Hs&Hg).
    exists s; split; [intros; lia|exact Hg].
  - destruct (G_value _ _ (Atom_value _ _ _ _ Hr) i) as (s&Hs&Hg).
    exists s; split; [intros; lia|exact Hg].
  - destruct (G_value _ _ (Atom_value _ _ _ _ Hr) i) as (s&Hs&Hg).
    exists s; split; [intros; lia|exact Hg].
Qed.

Lemma level_call_scale h a b fs k : Level h a b fs -> k<=h ->
  (a*2+b+1)*4=2^(1+k)*2^(h-k).
Proof.
  intros Hl Hk; pose proof (level_height _ _ _ _ Hl).
  rewrite <-Nat.pow_add_r; replace (1+k+(h-k)) with (2+(h-1)) by lia.
  cbn[Nat.add Nat.pow]; rewrite <-(level_size _ _ _ _ Hl); lia.
Qed.

Lemma narrow_calls_saturate h a b fs k l tau x r c : Level h a b fs -> k+2<=h ->
  k+l<=h -> Atom l tau x r ->
  (forall L, 4<=L -> (a*2+b+1)*4=2^(1+k)*L -> L<=c) -> tau<=c /\ 2<=c.
Proof.
  intros Hl Hwidth Hrank Hr Hcalls; pose proof (Atom_bound _ _ _ _ Hr).
  assert (HL:4<=2^(h-k)) by (change (2^2<=2^(h-k)); apply Nat.pow_le_mono_r; lia).
  specialize (Hcalls _ HL (level_call_scale _ _ _ _ k Hl ltac:(lia))).
  assert (Hp:2^l<=2^(h-k)) by (apply Nat.pow_le_mono_r; lia).
  split; lia.
Qed.

Lemma double_narrow_closed h a b j fs k n xs l tau x r : Level h a b fs -> j<=a ->
  3<=k -> k+2<=h -> 0<n -> Word k n xs -> Atom l tau x r -> k+l<=h ->
  Narrow a j k n -> phi n+(2^k-1)*x<=(a*2+b+1)*4 ->
  exists c, Normal c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hk Hwidth Hn Hw Hr Hrank Hguard Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  assert (Hinner:n mod 2=1%nat \/ 2^(1+k)<=n+j*4) by (destruct Hguard as [H|[_ H]]; auto).
  pose proof (G_atom_ready _ _ _ _ Hr) as Htail.
  destruct k as [|[|[|k]]]; try lia.
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - assert (HB:2^(2+k)<=b+a).
    { assert (Hp:2^(4+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia. }
    destruct (narrow_boundary _ a b fs (2+k) n xs x r
      (level_frame _ _ _ _ Hl) Hw ltac:(lia) Hn Htail Hinner HB Hcap)
      as (z&c&ys&s&Hys&Hodd&Hs&Hg&Hvalue&Hcalls&Hstep).
    destruct (narrow_calls_saturate h a b fs (3+k) l tau x r c Hl Hwidth Hrank Hr
      (fun L HL=>Hcalls L ltac:(lia))) as (Htau&Htwo).
    specialize (Hs Htau Htwo); eexists; split; [|exact Hstep].
    apply (sat_double_root (1+h) (a+b) (a*2+1) 0 _ (2+k) z ys (Nat.max l 3) (x+c*2) s);
      try assumption; try lia.
    apply Level_next, Hl.
  - assert (HB:2^(2+k)<=b+j).
    { assert (Hp:2^(4+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
      rewrite <-(level_size _ _ _ _ Hl) in Hp; cbn[Nat.add Nat.pow] in Hp |- *; lia. }
    destruct (narrow_inside _ a b j fs (1+k) n xs x r
      (level_frame _ _ _ _ Hl) ltac:(lia) Hw ltac:(lia) Hn Htail Hinner HB Hcap)
      as (z&c&ys&s&Hys&Hz&Hs&Hg&Hvalue&Hlower&Hsmall&Hcalls&Hstep).
    destruct (narrow_calls_saturate h a b fs (3+k) l tau x r c Hl Hwidth Hrank Hr Hcalls) as (Htau&Htwo).
    specialize (Hs Htau Htwo); eexists; split; [|exact Hstep].
    apply (sat_double_root h a b (j+1) fs (1+k) z ys (Nat.max l 3) (x+c*2) s);
      try assumption; lia.
Qed.

Lemma descent_y_inside_calls a b j k u v y z c1 c2 c3 : j<a -> 0<k ->
  a*2+b+1=2^(2+k) -> 0<u -> 0<y -> 0<z -> z<2^(1+k) ->
  CounterRun (GCounter (2+k)) (j*2+2) ((a-j)*2+1) (u*2+1) 0 ->
  CounterRun (GCounter (1+k)) (b+j) u v c1 ->
  CounterRun (GCounter (1+k)) 2 v (y*2+1) c2 ->
  CounterRun (GCounter k) (a-j-1) y z c3 -> 2<=c1+c2+c3.
Proof.
  intros Hj Hk Hsize Hu Hy Hz Hzb H0 H1 H2 H3.
  pose proof (descent_inside_balance a b j k ((a-j)*2+1) u v y z 0 c1 c2 c3 0
    Hj Hk ltac:(lia) Hu Hy H0 H1 H2 H3) as E.
  pose proof (phi_bounds _ Hu); pose proof (phi_bounds _ Hy); pose proof (phi_bounds _ Hz).
  rewrite phi_odd in E; cbn[Nat.add Nat.pow] in E, Hsize, Hzb.
  clear H0 H1 H2 H3; counter_arith.
Qed.

Lemma double_y_closed h a b j fs xs l tau x r : Level h a b fs -> j<=a ->
  Word (h-1) ((a-j)*2+1) xs -> Atom l tau x r -> l<=1 ->
  phi ((a-j)*2+1)+(2^(h-1)-1)*x<=(a*2+b+1)*4 ->
  exists c, Normal c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hw Hr Hl1 Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (Atom_bound _ _ _ _ Hr) as (Hlpos&Htau).
  assert (El:l=1%nat) by lia; subst l; cbn[Nat.pow] in Htau.
  remember (h-4) as k; assert (Eh:h=4+k) by lia; subst h.
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(3+k)) in Hsize.
  change (Word (3+k) ((a-j)*2+1) xs) in Hw.
  change (phi ((a-j)*2+1)+(2^(3+k)-1)*x<=(a*2+b+1)*4) in Hcap.
  assert (Hguard:((a-j)*2+1) mod 2=1%nat \/ 2^(4+k)<=(a-j)*2+1+j*4) by (left; lia).
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - assert (HB:2^(2+k)<=b+a) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
    destruct (narrow_boundary _ a b fs (2+k) ((a-a)*2+1) xs x r
      (level_frame _ _ _ _ Hl) Hw ltac:(lia) ltac:(lia)
      (G_atom_ready _ _ _ _ Hr) Hguard HB Hcap)
      as (z&c&ys&s&Hys&Hodd&Hs&Hg&Hvalue&Hcalls&Hstep).
    assert (Htwo:2<=c).
    { apply Hcalls; [lia|cbn[Nat.add Nat.pow] in Hsize |- *; lia]. }
    specialize (Hs ltac:(lia) Htwo); eexists; split; [|exact Hstep].
    apply (sat_double_root (1+(4+k)) (a+b) (a*2+1) 0 _ (2+k) z ys 3 (x+c*2) s);
      try assumption; try lia.
    apply Level_next, Hl.
  - destruct (counter_inner_total (3+k) j ((a-j)*2+1) ltac:(lia)
      (Word_bound _ _ _ Hw) Hguard) as (u&c0&Hu&Hub&H0).
    destruct (GCounterRun_linear _ _ _ _ _ H0) as (Eu&Ec0);
      [cbn[Nat.add Nat.pow] in Hsize |- *; lia|].
    assert (Eu':u=a+j+2) by lia; subst u c0.
    destruct (CounterRun_total _ _ (fun v=>GCounter_total (2+k) v ltac:(lia))
      (b+j) (a+j+2) Hub) as (v&c1&H1&Hvb).
    assert (Hodd:v mod 2=1%nat).
    { eapply GCounterRun_saturated; [exact H1|lia|exact Hub|change (2^(3+k)<=a+j+2+(b+j)*2); lia]. }
    destruct (counter_inner_total (2+k) 0 v ltac:(lia) Hvb (or_introl Hodd))
      as (y&c2&Hy&Hyb&H2).
    destruct (CounterRun_total _ _ (fun z=>GCounter_total (1+k) z ltac:(lia))
      (a-j-1) y Hyb) as (z&c3&H3&Hzb).
    assert (Hz:0<z) by (eapply GCounterRun_positive; eassumption).
    assert (Htwo:2<=c1+c2+c3).
    { eapply (descent_y_inside_calls a b j (1+k) (a+j+2) v y z c1 c2 c3); try eassumption; lia. }
    destruct (G_atom_sat _ _ _ _ (c1+(c2+c3)) Hr ltac:(lia) ltac:(lia)) as (s&Hs&Hg).
    destruct (descent_inside a b j fs (1+k) ((a-j)*2+1) (a+j+2) v y z 0 c1 c2 c3 xs r s
      (level_frame _ _ _ _ Hl) ltac:(lia) Hw ltac:(lia) Hguard Hodd H0 H1 H2 H3 Hg)
      as (ys&Hys&Hstep).
    assert (Hvalue:phi z+(2^(1+k)-1)*(x+(c1+(c2+c3))*2)<(a*2+b+1)*2).
    { pose proof (descent_inside_balance a b j (1+k) ((a-j)*2+1) (a+j+2) v y z 0 c1 c2 c3 x
        ltac:(lia) ltac:(lia) ltac:(lia) Hu Hy H0 H1 H2 H3) as E.
      replace (0+c1+c2+c3) with (c1+(c2+c3)) in E by lia.
      change (phi ((a-j)*2+1)+(2^(2+(1+k))-1)*x<=(a*2+b+1)*4) in Hcap; lia. }
    assert (Hlower:z mod 2=0%nat -> (a-j)*2<=z).
    { intro Heven; destruct (GCounterRun_even _ _ _ _ _ H3 Heven) as (_&Ez&He); lia. }
    eexists; split; [|exact Hstep].
    apply (sat_double_root (4+k) a b (j+1) fs (1+k) z ys 3 (x+(c1+(c2+c3))*2) s);
      try assumption; lia.
Qed.

Lemma double_phase_progress h a b j fs k n xs l tau x r : Level h a b fs -> j<=a ->
  0<k -> 0<n -> Word k n xs -> Atom l tau x r -> DoublePhase h a b j k n l tau ->
  phi n+(2^k-1)*x<=(a*2+b+1)*4 ->
  exists c, Normal c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hk Hn Hw Hr Hp Hcap.
  destruct Hp as [k n l tau Hkn Hwidth Hphase Hrank|l tau Hl1|
    n l tau Hphase Hwidth Hbudget|n l tau Hwidth Hpos].
  - eapply double_narrow_closed; eassumption.
  - eapply double_y_closed; eassumption.
  - destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
    pose proof (Word_bound _ _ _ Hw) as Hnb; cbn[Nat.pow] in Hnb.
    assert (Hguard:n mod 2=1%nat \/ 8<=n+j*4) by (destruct Hphase; [left|right]; lia).
    destruct (counter_inner_total 2 j n ltac:(lia) Hnb Hguard) as (u&c0&Hu&Hub&H0).
    destruct (CounterRun_total _ _ (fun z=>GCounter_total 1 z ltac:(lia)) (b+j) u Hub)
      as (z&c1&H1&Hbound).
    assert (Hrun:CounterRun (GCounter 1) (2+(b+j-2)) u z c1) by (applys_eq H1; flia).
    destruct (GCounterRun_one _ _ _ _ Hrun Hu Hub) as (Ez&Hlo&Hhi); subst z.
    destruct (double_two_closed h a b j fs n xs l tau x r u c0 c1 Hl Hj Hn Hw
      Hphase Hr Hwidth H0 H1 ltac:(lia) ltac:(cbn[Nat.pow] in Hcap; lia))
      as (c&Hroot&Hstep).
    exists c; split; [left; exact Hroot|exact Hstep].
  - destruct Hpos as [->|(Hnear&->)].
    + destruct (double_one_boundary_closed _ _ _ _ _ _ _ _ _ _ Hl Hn Hw Hr Hwidth
        ltac:(cbn[Nat.pow] in Hcap; lia)) as (c&Hroot&Hstep).
      exists c; split; [left; exact Hroot|exact Hstep].
    + destruct (double_one_neighbor_closed _ _ _ _ _ _ _ _ _ _ Hl Hnear Hw Hr Hwidth
        ltac:(change (1+(2^1-1)*x<=(a*2+b+1)*4) in Hcap; cbn[Nat.pow] in Hcap; lia)) as (c&Hroot&Hstep).
      exists c; split; [left; exact Hroot|exact Hstep].
Qed.

Lemma double_progress c : DRoot c -> exists c', Normal c' /\ c -->+ c'.
Proof.
  intros [h a b j fs r Hl Hj Hd]; destruct Hd as [k n xs l tau x r Hk Hn Hw Hr Hp Hcap].
  exact (double_phase_progress h a b j fs k n xs l tau x r Hl Hj Hk Hn Hw Hr Hp Hcap).
Qed.

Lemma late_first_Q_boundary_closed k a fs xs q r : Level (2+k) a (a+1) fs ->
  Word (1+k) (a*2+2) xs -> Num q r -> q<=1 ->
  exists c, SRoot c /\ cfg (fs*>w^^a*>xs*>r) -->+ c.
Proof.
  intros Hl Hw Hr Hq; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+(a+1)+1=2^(1+k)) in Hsize.
  assert (Hpow:a*6+4=2^(2+k)) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
  destruct (late_first_Q_boundary _ _ _ _ _ _ (level_frame _ _ _ _ Hl) ltac:(lia) Hpow Hw Hr)
    as (ys&s&Hy&Hs&Hstep).
  assert (Hodd:(a+3) mod 2=1%nat) by (destruct (Frame_phase _ _ _ (level_frame _ _ _ _ Hl)); lia).
  eexists; split; [|exact Hstep].
  apply (small_single_root (1+(2+k)) (a+(a+1)) (a*2+1) 0 _ k (a+3) ys (q+4) s);
    try assumption; try lia.
  - apply Level_next, Hl.
  - unfold phi; rewrite Hodd; cbn[Nat.add Nat.pow] in Hsize; nia.
Qed.

Lemma late_second_Q_recover_closed k a fs xs q r : Level (2+k) a a fs ->
  Word (1+k) (a*2+2) xs -> Num q r -> q<=3 ->
  exists c, SRoot c /\ cfg (fs*>w^^(a-1)*>xs*>r) -->+ c.
Proof.
  intros Hl Hw Hr Hq; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+a+1=2^(1+k)) in Hsize.
  assert (Hpow:a*6+2=2^(2+k)) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
  destruct (late_second_Q_recover _ _ _ _ _ _ (level_frame _ _ _ _ Hl) Ha Hpow Hw Hr Hq)
    as (K&z&Q&ys&s&HK&Hwidth&Hy&Hs&Hodd&Hwide&Hcap&Hsmall&Hstep).
  eexists; split; [|exact Hstep].
  destruct (Nat.eq_dec K 1) as [->|HK1].
  - destruct (Hsmall eq_refl) as [-> Htail].
    rewrite (Word_max _ _ _ Hy eq_refl).
    apply (sroot (1+(2+k)) (a+a) (a*2+1) 1); [apply Level_next, Hl|lia|].
    eapply SNum; eassumption.
  - apply (sroot (1+(2+k)) (a+a) (a*2+1) 0); [apply Level_next, Hl|lia|].
    eapply SWord with (k:=K) (n:=z) (q:=Q); try eassumption; try lia.
    apply single_odd_phase; try lia.
    intro Hwider; split; [|right; lia].
    assert (Hp:2^(2+k)<=2^K) by (apply Nat.pow_le_mono_r; lia).
    specialize (Hwide Hp); lia.
Qed.

Lemma first_Q_x_closed k a j fs xs r : Level (2+k) a a fs -> j*7+4=a*5 ->
  Word (2+k) (a*3+1-j) xs -> Num 0 r ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+a+1=2^(1+k)) in Hsize.
  assert (Hodd:(a*3+1-j) mod 2=1%nat)
    by (destruct (Frame_phase _ _ _ (level_frame _ _ _ _ Hl)); lia).
  destruct (P_word_linear (2+k) (j*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (ys&Hy&Hp).
  remember ((a*3+1-j+j*4+3)/2) as u.
  replace (a*3+1-j+(j*2+2)*2) with (u*2+1) in Hy by lia.
  destruct (Word_odd_inv _ _ _ Hy) as (zs&Hz&->).
  destruct (P_word_linear (1+k) (a+j) u zs r Hz ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (bs&Hb&Hmid).
  assert (Etop:u+(a+j)*2+2=2^(2+k)) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
  rewrite (Word_before_Q _ _ _ Hb Etop), !Str_app_assoc in Hmid.
  destruct (P_num _ _ Hr) as (r1&H1&Htail).
  destruct (P_word_linear k (a-j-1) 1 (one k) r1 (Word_one k) ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (out&Hout&Hlast).
  assert (Hstep:cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>out*>r1)).
  { eapply first_Q_inside; [exact (level_frame _ _ _ _ Hl)|lia| |apply P_G, Hmid|apply GP, Htail|apply P_G, Hlast].
    apply InnerP; rewrite Str_app_assoc in Hp; exact Hp. }
  eexists; split; [|exact Hstep].
  eapply sroot; [exact Hl|lia|].
  eapply SWord with (k:=k) (n:=1+(a-j-1)*2) (q:=2%nat); try eassumption; try lia.
  - apply SN; [lia|lia|left; lia].
  - unfold phi; cbn[Nat.add Nat.pow] in Hsize; nia.
Qed.

Lemma late_first_Q_z_closed k a j fs n xs r : Level (3+k) a (a+1) fs ->
  j*7=a*5 -> n*2=(a*3+2)*2+(a-j) -> Word (2+k) n xs -> Num 0 r ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+(a+1)+1=2^(2+k)) in Hsize.
  destruct (P_num _ _ Hr) as (r1&H1&Htail).
  destruct (G_word_data (1+k) 1 (one (1+k)) 2 r1 (a+1+j)
    ltac:(lia) (Word_one _) H1) as (u&c&ys&s&Hc&Hy&Hs&Hg).
  assert (Hodd:u mod 2=1%nat) by (eapply GCounterRun_odd; [exact Hc|reflexivity]).
  pose proof (Word_bound _ _ _ Hy) as Hub.
  pose proof (GCounterRun_balance _ _ _ _ _ Hc ltac:(lia) ltac:(lia)) as E.
  assert (Ec:c=1%nat).
  { assert (Hper:(2^(1+k)-1)*2=a*3) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
    rewrite Hper in E; unfold phi in E; rewrite Hodd in E.
    assert (Hub':u<a*3+2) by (cbn[Nat.add Nat.pow] in Hsize, Hub; lia).
    clear -E Hub' Hj Ha; cbn in E; destruct c as [|[|c]]; try reflexivity.
    - exfalso; lia.
    - exfalso; cbn[Nat.mul] in E; lia. }
  subst c; change (Num 4 s) in Hs.
  destruct (odd_d_value Num k u ys 4 s (a-j-1) Hy ltac:(lia) Hodd
    (fun c=>G_nums c _ _ Hs)) as (z&e&zs&out&Hz&Hzpos&Hout&Hcap&Hlower&Hsmall&Hp&Hparts).
  assert (Hstep:cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>zs*>out)).
  { rewrite (lpow_add _ j 1), Str_app_assoc.
    applys_eq (late_first_Q a (a+1) (j-1) fs (1+k) n xs r r1 (ys*>s) (w*>zs*>out)); try solve [flia].
    - exact (level_frame _ _ _ _ Hl).
    - exact Hw.
    - cbn[Nat.add Nat.pow] in Hsize |- *; lia.
    - apply GP, Htail.
    - applys_eq Hg; flia.
    - apply P_G; applys_eq Hp; flia. }
  eexists; split; [|exact Hstep].
  apply (small_single_root (3+k) a (a+1) (j+1) fs k z zs (4+e*2) out);
    try assumption; try lia.
  - assert (Hphi:phi u=u) by (unfold phi; rewrite Hodd; lia).
    rewrite Hphi in E, Hcap.
    rewrite Nat.mul_1_l in E.
    change (u+(2^(1+k)-1)*2=1+(a+1+j)*2) in E.
    cbn[Nat.add Nat.pow] in Hsize, E, Hcap; lia.
Qed.

Lemma single_low_descent_closed k a b j fs n xs q r : Level (3+k) a b fs -> j<=a ->
  0<n -> Word (2+k) n xs -> Num q r ->
  (n mod 2=1%nat \/ 2^(3+k)<=n+j*4) ->
  (forall u v c0 c1,
    CounterRun (GCounter (2+k)) (j*2+2) n (u*2+1) c0 ->
    CounterRun (GCounter (1+k)) (b+j) u v c1 -> v mod 2=1%nat) ->
  phi n+(2^(2+k)-1)*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hw Hr Hguard Hready Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (counter_inner_total (2+k) j n ltac:(lia) (Word_bound _ _ _ Hw) Hguard)
    as (u&c0&Hu&Hub&H0).
  destruct (CounterRun_total _ _ (fun z=>GCounter_total (1+k) z ltac:(lia)) (b+j) u Hub)
    as (v&c1&H1&Hvb).
  pose proof (Hready _ _ _ _ H0 H1) as Hodd.
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - destruct (G_nums (c0+c1) _ _ Hr) as (s&Hs&Hg).
    destruct (descent_boundary _ _ _ _ _ _ _ _ _ _ _ _
      (level_frame _ _ _ _ Hl) Hw ltac:(lia) Hguard H0 H1 Hg) as (ys&Hys&Hstep).
    pose proof (descent_boundary_balance a b (1+k) n u v c0 c1 q
      ltac:(lia) Hn Hu H0 H1) as E.
    eexists; split; [|exact Hstep].
    apply (small_single_root (1+(3+k)) (a+b) (a*2+1) 0 _ (1+k) v ys (q+(c0+c1)*2) s);
      try assumption; try lia.
    apply Level_next, Hl.
    cbn[Nat.add Nat.pow] in E, Hcap |- *; lia.
  - destruct (counter_inner_total (1+k) 0 v ltac:(lia) Hvb (or_introl Hodd))
      as (y&c2&Hy&Hyb&H2).
    destruct (CounterRun_total _ _ (fun z=>GCounter_total k z ltac:(lia)) (a-j-1) y Hyb)
      as (z&c3&H3&Hzb).
    destruct (G_nums (c0+(c1+(c2+c3))) _ _ Hr) as (s&Hs&Hg).
    destruct (descent_inside a b j fs k n u v y z c0 c1 c2 c3 xs r s
      (level_frame _ _ _ _ Hl) ltac:(lia) Hw ltac:(lia) Hguard Hodd H0 H1 H2 H3 Hg)
      as (ys&Hys&Hstep).
    pose proof (descent_inside_balance a b j k n u v y z c0 c1 c2 c3 q
      ltac:(lia) ltac:(lia) Hn Hu Hy H0 H1 H2 H3) as E.
    assert (Hz:0<z) by (eapply GCounterRun_positive; eassumption).
    eexists; split; [|exact Hstep].
    apply (small_single_root (3+k) a b (j+1) fs k z ys (q+(c0+(c1+(c2+c3)))*2) s);
      try assumption; try lia.
    intro Heven; destruct (GCounterRun_even _ _ _ _ _ H3 Heven) as (_&Ez&Ec); lia.
Qed.

Lemma single_y_low_closed k a b j fs xs q r : Level (3+k) a b fs -> j<=a ->
  Word (2+k) ((a-j)*2+1) xs -> Num q r ->
  phi ((a-j)*2+1)+(2^(2+k)-1)*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hw Hr Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  eapply single_low_descent_closed; try eassumption; [lia|left; lia|].
  intros u v c0 c1 H0 H1.
  destruct (GCounterRun_linear _ _ _ _ _ H0) as (Eu&Ec0);
    [cbn[Nat.add Nat.pow] in Hsize |- *; lia|].
  eapply GCounterRun_saturated; [exact H1|lia| |];
    change (2^(1+(1+k))) with (2^(2+k)); rewrite <-Hsize; lia.
Qed.

Lemma single_x_low_odd_closed k a b j fs xs q r : Level (3+k) a b fs -> j<=a ->
  (a*2+b+1-j) mod 2=1%nat -> Word (2+k) (a*2+b+1-j) xs -> Num q r ->
  phi (a*2+b+1-j)+(2^(2+k)-1)*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hodd Hw Hr Hcap; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  eapply single_low_descent_closed; try eassumption; [lia|left; exact Hodd|].
  intros u v c0 c1 H0 H1.
  pose proof (GCounterRun_bound _ _ _ _ _ H0 ltac:(lia) (Word_bound _ _ _ Hw)) as Hub.
  pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) ltac:(lia)) as E.
  rewrite phi_odd in E.
  assert (Hphi:phi (a*2+b+1-j)=a*2+b+1-j) by (unfold phi; rewrite Hodd; lia).
  rewrite Hphi in E.
  eapply GCounterRun_saturated; [exact H1|lia| |].
  - cbn[Nat.add Nat.pow] in Hub |- *; lia.
  - change (2^(2+k)<=u+(b+j)*2); rewrite <-Hsize.
    assert (Ep:2^(2+k)-1=a*2+b) by lia; rewrite Ep in E.
    clear -E Hj Ha Hab Hba; destruct c0; cbn[Nat.mul] in E; lia.
Qed.

Lemma single_x_top_closed k a fs xs r : Level (3+k) a a fs ->
  Word (4+k) (a*2+1) xs -> Num 0 r ->
  exists c, SRoot c /\ cfg (fs*>w^^a*>xs*>r) -->+ c.
Proof.
  intros Hl Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+a+1=2^(2+k)) in Hsize.
  destruct (P_word_linear (4+k) (a*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (ys&Hy&Hp).
  replace (a*2+1+(a*2+2)*2) with ((a*3+2)*2+1) in Hy by lia.
  destruct (Word_odd_inv _ _ _ Hy) as (zs&Hz&->).
  destruct (P_word_linear (3+k) (a+a) _ _ r Hz ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (out&Hout&Hmid).
  assert (Hstep:cfg (fs*>w^^a*>xs*>r) -->+ cfg ((fs++w^^a++d)*>out*>r)).
  { rewrite !Str_app_assoc in Hp |- *; apply (frame_step _ _ _ (level_frame _ _ _ _ Hl)).
    rewrite Str_app_assoc.
    eapply inner_column; [lia|apply InnerP, Hp|apply G_d, P_G, Hmid|].
    replace (a-a) with 0%nat by lia; constructor. }
  eexists; split; [|exact Hstep].
  apply (sroot (1+(3+k)) (a+a) (a*2+1) 0); [apply Level_next, Hl|lia|].
  eapply SWord with (k:=3+k) (n:=a*3+2+(a+a)*2) (q:=0%nat);
    try eassumption; try lia.
  - applys_eq (SZ (1+(3+k)) (a+a) (a*2+1) 0 (a*3+2+(a+a)*2)); flia.
  - rewrite Nat.mul_0_r; unfold phi; lia.
Qed.

Lemma single_y_top_odd_closed k a b j fs xs r : Level (3+k) a b fs -> j<a ->
  (a+b*2+j*3+2) mod 2=1%nat -> Word (4+k) ((a-j)*2+1) xs -> Num 0 r ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hodd Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  destruct (P_word_linear (4+k) (j*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (ys&Hy&Hp).
  replace ((a-j)*2+1+(j*2+2)*2) with ((a+j+2)*2+1) in Hy by lia.
  destruct (Word_odd_inv _ _ _ Hy) as (zs&Hz&->).
  destruct (P_word_linear (3+k) (b+j) _ _ r Hz ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (bs&Hb&Hmid).
  replace (a+j+2+(b+j)*2) with (a+b*2+j*3+2) in Hb by lia.
  destruct (P_word_linear (3+k) 2 _ _ r Hb ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (cs&Hc&Htwo).
  remember ((a+b*2+j*3+5)/2) as y.
  replace (a+b*2+j*3+2+2*2) with (y*2+1) in Hc by lia.
  destruct (Word_odd_inv _ _ _ Hc) as (ds&Hd&->).
  destruct (P_word_linear (2+k) (a-j-1) _ _ r Hd ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (out&Hout&Hlast).
  assert (Hstep:cfg (fs*>w^^j*>xs*>r) -->+ cfg (fs*>w^^(j+1)*>out*>r)).
  { rewrite (lpow_add _ j 1), Str_app_assoc; apply (frame_step _ _ _ (level_frame _ _ _ _ Hl)).
    rewrite Str_app_assoc in Hp, Htwo.
    eapply inner_column; [lia|apply InnerP, Hp|apply G_d, P_G, Hmid|].
    replace (a-j) with (1+(a-j-1)) by lia.
    eapply G_add with (s:=w*>ds*>r); [apply P_G, P_d, Htwo|apply P_G, G_w, P_G, Hlast]. }
  eexists; split; [|exact Hstep].
  eapply sroot; [exact Hl|lia|].
  eapply SWord with (k:=2+k) (n:=y+(a-j-1)*2) (q:=0%nat);
    try eassumption; try lia.
  - applys_eq (SZ (3+k) a b (j+1) (y+(a-j-1)*2)); flia.
  - rewrite Nat.mul_0_r; unfold phi; lia.
Qed.

Lemma single_mid_descent_closed k a b j fs n u xs q r : Level (3+k) a b fs -> j<=a ->
  0<n -> n<=a*2+b+1-j -> n+(j*2+2)*2=u*2+1 -> Word (3+k) n xs -> Num q r ->
  (u mod 2=1%nat \/ 2^(3+k)<=u+(b+j)*2) ->
  phi n+(2^(3+k)-1)*q<=(a*2+b+1)*4 ->
  exists c, SRoot c /\ cfg (fs*>w^^j*>xs*>r) -->+ c.
Proof.
  intros Hl Hj Hn Hupper Eu Hw Hr Hready Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  assert (Hguard:n mod 2=1%nat \/ 2^(4+k)<=n+j*4) by (left; lia).
  destruct (counter_inner_total (3+k) j n ltac:(lia) (Word_bound _ _ _ Hw) Hguard)
    as (u0&c0&Hu&Hub&H0).
  destruct (GCounterRun_linear _ _ _ _ _ H0) as (Eu0&Ec0);
    [cbn[Nat.add Nat.pow] in Hsize |- *; lia|].
  assert (Euu:u0=u) by lia; subst u0 c0.
  destruct (CounterRun_total _ _ (fun z=>GCounter_total (2+k) z ltac:(lia)) (b+j) u Hub)
    as (v&c1&H1&Hvb).
  assert (Hodd:v mod 2=1%nat).
  { destruct Hready as [Hodd|Hsat].
    - eapply GCounterRun_odd; eassumption.
    - eapply GCounterRun_saturated; [exact H1|lia|exact Hub|exact Hsat]. }
  destruct (Nat.eq_dec j a) as [->|Hinside].
  - destruct (G_nums c1 _ _ Hr) as (s&Hs&Hg).
    destruct (descent_boundary a b fs (2+k) n u v 0 c1 xs r s
      (level_frame _ _ _ _ Hl) Hw ltac:(lia) Hguard H0 H1 Hg) as (ys&Hys&Hstep).
    pose proof (descent_boundary_balance a b (2+k) n u v 0 c1 q
      ltac:(lia) Hn Hu H0 H1) as E.
    eexists; split; [|exact Hstep].
    apply (sroot (1+(3+k)) (a+b) (a*2+1) 0); [apply Level_next, Hl|lia|].
    eapply SWord with (k:=2+k) (n:=v) (q:=q+c1*2); try eassumption; try lia.
    + apply SN; [lia|lia|left; exact Hodd].
    + change (phi n+(2^(1+(2+k))-1)*q<=(a*2+b+1)*4) in Hcap; lia.
  - destruct (counter_inner_total (2+k) 0 v ltac:(lia) Hvb (or_introl Hodd))
      as (y&c2&Hy&Hyb&H2).
    destruct (CounterRun_total _ _ (fun z=>GCounter_total (1+k) z ltac:(lia)) (a-j-1) y Hyb)
      as (z&c3&H3&Hzb).
    destruct (G_nums (c1+(c2+c3)) _ _ Hr) as (s&Hs&Hg).
    destruct (descent_inside a b j fs (1+k) n u v y z 0 c1 c2 c3 xs r s
      (level_frame _ _ _ _ Hl) ltac:(lia) Hw ltac:(lia) Hguard Hodd H0 H1 H2 H3 Hg)
      as (ys&Hys&Hstep).
    assert (Hz:0<z) by (eapply GCounterRun_positive; eassumption).
    eexists; split; [|exact Hstep].
    eapply sroot; [exact Hl|lia|].
    eapply SWord with (k:=1+k) (n:=z) (q:=q+(c1+(c2+c3))*2); try eassumption; try lia.
    + apply SN; [lia|lia|].
      destruct (Nat.eq_dec (z mod 2) 1%nat) as [Hzo|Hze]; [left; exact Hzo|].
      right; destruct (GCounterRun_even _ _ _ _ _ H3 ltac:(lia)) as (_&Ez&Ec3).
      split; [lia|]; change (2^(2+k)<=z+(j+1)*4); rewrite <-Hsize.
      destruct (le_dec b (j*2+1)) as [Hnear|Hfar]; [lia|].
      assert (Hlin:u+(b+j)*2+4<2^(3+k)) by (cbn[Nat.add Nat.pow] in Hsize |- *; lia).
      destruct (GCounterRun_linear _ _ _ _ _ H1
        ltac:(change (u+(b+j)*2<2^(3+k)); lia)) as (Ev&Ec1).
      destruct (GCounterRun_linear _ _ _ _ _ H2
        ltac:(change (v+4<2^(3+k)); lia)) as (Ey&Ec2); lia.
    + pose proof (descent_inside_balance a b j (1+k) n u v y z 0 c1 c2 c3 q
        ltac:(lia) ltac:(lia) Hn Hu Hy H0 H1 H2 H3) as E.
      change (phi n+(2^(2+(1+k))-1)*q<=(a*2+b+1)*4) in Hcap.
      replace (0+c1+c2+c3) with (c1+(c2+c3)) in E by lia; lia.
Qed.

(* E/O splitting preserves the complete root invariant, including a narrow
   first word absorbed into the frame and zero-width terminal words. *)
Lemma G_word_atom k n xs q r i : 0<k -> 0<n -> Word k n xs -> Num q r ->
  exists m c ys s,
    CounterRun (GCounter k) i n m c /\ Word k m ys /\ Num (q+c*2) s /\
    Atom k (2^k) (phi n+(2^k-1)*q+i*2) (ys*>s) /\ G i (xs*>r) (ys*>s).
Proof.
  intros Hk Hn Hw Hr; destruct (G_word_data _ _ _ _ _ i Hk Hw Hr) as (m&c&ys&s&Hc&Hy&Hs&Hg).
  pose proof (GCounterRun_balance _ _ _ _ _ Hc Hk Hn) as E.
  exists m, c, ys, s; repeat split; try assumption.
  replace (phi n+(2^k-1)*q+i*2) with (phi m+(2^k-1)*(q+c*2)) by nia.
  econstructor; try eassumption; [eapply GCounterRun_positive; eassumption|lia|].
  right; cbn[Nat.add Nat.pow]; lia.
Qed.

Lemma split_O_capacity a b j l K z Q m c : j<a -> 0<l -> 0<K -> 0<z ->
  (2^l*(z*2+1))*2+(2^(2+l+K)-1)*Q <= (a*2+b+1)*4+b*4+j*8+11 ->
  CounterRun (ICounter l) (a-j-1) 1 m c ->
  phi (m*2+1)+(2^(1+l)-1)*(phi z+(2^K-1)*Q+c*2)<(a*2+b+1)*4.
Proof.
  intros Hj Hl HK Hz Hcap Hi.
  pose proof (ICounterRun_balance _ _ _ _ _ Hi) as E.
  assert (Ephi:phi (m*2+1)=m*2+1) by (unfold phi; lia).
  rewrite Ephi.
  assert (Eq:m*2+1+(2^(1+l)-1)*(phi z+(2^K-1)*Q+c*2)=
    (a-j)*2+1+(2^(1+l)-1)*(phi z+(2^K-1)*Q)) by nia.
  rewrite Eq; clear Eq Hi E Ephi.
  pose proof (phi_bounds _ Hz) as Hphi.
  assert (Hp:2<=2^l) by (change (2^1<=2^l); apply Nat.pow_le_mono_r; lia).
  assert (HT:2<=2^K) by (change (2^1<=2^K); apply Nat.pow_le_mono_r; lia).
  assert (Ep:2^(2+l+K)=4*2^l*2^K) by (rewrite !Nat.pow_add_r; cbn[Nat.pow]; lia).
  rewrite Ep in Hcap; cbn[Nat.add Nat.pow].
  assert (Hcoef:2*(2*2^l-1)*(2^K-1)<=4*2^l*2^K-1)
    by (clear -Hp HT; nia).
  assert (HQ:2*(2*2^l-1)*(2^K-1)*Q<=(4*2^l*2^K-1)*Q)
    by (apply Nat.mul_le_mono_r; exact Hcoef).
  assert (Hz':2*(2*2^l-1)*phi z+6<=(2^l*(z*2+1))*2)
    by (clear -Hp Hphi Hz; nia).
  clear Hcoef Ep; nia.
Qed.

Lemma split_head_narrow h a b j fs k m c z e : Level h a b fs -> j<=a ->
  3<=k -> k+2<=h -> CounterRun (ICounter k) (b+j) 1 m c ->
  CounterRun (GCounter k) (a-j) m z e -> Narrow a j k z.
Proof.
  intros Hl Hj Hk Hwidth Hi Hg; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (Nat.eq_dec (z mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
  destruct (GCounterRun_even _ _ _ _ _ Hg ltac:(lia)) as (_&Ez&Hm).
  pose proof (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)) as Hpos.
  right; split; [lia|].
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  destruct (le_dec (k+3) h) as [Hsmall|Hedge].
  - assert (Hp:2^(2+k)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
    cbn[Nat.add Nat.pow] in Hp |- *; lia.
  - assert (Eh:h=k+2) by lia; subst h.
    replace (k+2-1) with (1+k) in Hsize by lia.
    destruct (ICounterRun_linear _ _ _ _ _ Hi ltac:(lia)) as (Em&Ec); lia.
Qed.

Lemma split_E_capacity a b j n l K z q m c v e : 5<=a -> a<=b -> b<=a+1 -> j<=a ->
  0<n -> 0<l -> 0<K -> 0<z -> n+j*4+4=2^l*(z*2+1) ->
  phi n+(2^(1+l+K)-1)*q<=(a*2+b+1)*4 ->
  CounterRun (ICounter l) (b+j) 1 m c -> CounterRun (GCounter l) (a-j) m v e ->
  phi v+(2^l-1)*(phi z+(2^K-1)*q+(c+e)*2)<(a*2+b+1)*4.
Proof.
  intros Ha Hab Hba Hj Hn Hl HK Hz He Hcap Hi Hg.
  pose proof (split_capacity _ _ _ _ _ _ _ (phi z+(2^K-1)*q) Hl Hi Hg) as E.
  pose proof (phi_bounds _ Hn); pose proof (phi_bounds _ Hz).
  assert (Ep:2^(1+l+K)=2*2^l*2^K) by (rewrite !Nat.pow_add_r; cbn[Nat.pow]; lia).
  rewrite Ep in Hcap.
  assert (Hp:2<=2^l) by (change (2^1<=2^l); apply Nat.pow_le_mono_r; lia).
  assert (HQ:2<=2^K) by (change (2^1<=2^K); apply Nat.pow_le_mono_r; lia).
  assert (Hcoef:2*(2^l-1)*(2^K-1)<=(2*2^l*2^K-1))
    by (clear -Hp HQ; nia).
  assert (Hq:2*(2^l-1)*(2^K-1)*q<=(2*2^l*2^K-1)*q)
    by (apply Nat.mul_le_mono_r; exact Hcoef).
  assert (Hz':2*(2^l-1)*phi z<=n+j*4+4) by (clear -He H0; nia).
  assert (Hx:2*((2^l-1)*(phi z+(2^K-1)*q)) <=
    (a*2+b+1)*4+j*4+5) by (clear -Hcap Hq Hz' H; nia).
  clear Hi Hg Ep Hcap Hcoef Hq Hz' He Hp HQ; lia.
Qed.

Lemma split_E_one_capacity a b j n K z q m c e : 5<=a -> a<=b -> b<=a+1 -> j<a ->
  0<n -> 0<K -> 0<z -> n+j*4+4=2*(z*2+1) ->
  phi n+(2^(2+K)-1)*q<=(a*2+b+1)*4 ->
  CounterRun (ICounter 1) (b+j) 1 m c -> CounterRun (GCounter 1) (a-j) m 3 e ->
  phi z+(2^K-1)*q+(c+e)*2<(a*2+b+1)*2.
Proof.
  intros Ha Hab Hba Hj Hn HK Hz He Hcap Hi Hg.
  pose proof (ICounterRun_balance _ _ _ _ _ Hi) as E0.
  pose proof (GCounterRun_balance _ _ _ _ _ Hg ltac:(lia)
    (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia))) as E1.
  pose proof (ICounterRun_bound _ _ _ _ _ Hi ltac:(cbn; lia)) as Hm.
  pose proof (phi_bounds _ Hn); pose proof (phi_bounds _ Hz).
  pose proof (phi_bounds _ (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia))).
  change (3+e*2=phi m+(a-j)*2) in E1.
  cbn[Nat.add Nat.pow] in Hcap, E0, Hm.
  assert (Hp:2<=2^K) by (change (2^1<=2^K); apply Nat.pow_le_mono_r; lia).
  clear Hi Hg; nia.
Qed.

Lemma split_E_absorb_root h a b j fs K z m c e Z C ys Q s :
  Level h a b fs -> j<a -> 0<K -> K+2<=h -> 0<z -> z<2^(1+K) ->
  (K+2=h -> a*2+b+1+j*3+2<=z*4) ->
  CounterRun (ICounter 1) (b+j) 1 m c ->
  CounterRun (GCounter 1) (a-j) m 3 e ->
  CounterRun (GCounter K) (c+e) z Z C -> Word K Z ys -> Num Q s ->
  phi Z+(2^K-1)*Q<=(a*2+b+1)*2 ->
  SRoot (cfg (fs*>w^^(j+1)*>ys*>s)).
Proof.
  intros Hl Hj HK Hwidth Hz Hzbound Hedge Hi Hg Hright Hw Hr Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)) as Hm.
  pose proof (ICounterRun_bound _ _ _ _ _ Hi ltac:(cbn; lia)) as Hmb.
  pose proof (ICounterRun_balance _ _ _ _ _ Hi) as Ei.
  pose proof (GCounterRun_balance _ _ _ _ _ Hg ltac:(lia) Hm) as Eg.
  pose proof (phi_bounds _ Hm) as Hphi.
  change (m+c*3=1+(b+j)) in Ei; change (m<4) in Hmb.
  change (3+e*2=phi m+(a-j)*2) in Eg.
  assert (He:a-j-1<=e) by lia.
  assert (HZ:0<Z) by (eapply GCounterRun_positive; eassumption).
  assert (Hlower:Z mod 2=0%nat -> (a-(j+1))*2+2<=Z).
  { intro Heven; destruct (GCounterRun_even _ _ _ _ _ Hright Heven) as (_&EZ&Hze); lia. }
  destruct (le_dec (K+3) h) as [Hsmall|Hlarge].
  - apply (small_single_root h a b (j+1) fs K Z ys Q s); try assumption; try lia.
    intros -> Hfar.
    replace (c+e) with (2+(c+e-2)) in Hright by lia.
    exact (proj1 (GCounterRun_one _ _ _ _ Hright Hz Hzbound)).
  - assert (EK:K+2=h) by lia; specialize (Hedge EK).
    eapply sroot; [exact Hl|lia|].
    eapply SWord with (k:=K) (n:=Z) (q:=Q); try eassumption; try lia.
    apply SN; [lia|lia|].
    destruct (Nat.eq_dec (Z mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
    right; split; [apply Hlower; lia|].
    destruct (GCounterRun_even _ _ _ _ _ Hright ltac:(lia)) as (_&EZ&Hze).
    pose proof (level_size _ _ _ _ Hl) as Hsize.
    replace (h-1) with (1+K) in Hsize by lia; lia.
Qed.

Lemma split_E_positive_closed h a b j fs n l K z ys q r input :
  Level h a b fs -> j<=a -> 0<n -> 0<l -> l+2<=h -> 0<K -> 0<z ->
  1+l+K<=h -> (l=1%nat -> K+2=h -> a*2+b+1+j*3+2<=z*4) ->
  Word K z ys -> Num q r -> n+j*4+4=2^l*(z*2+1) ->
  phi n+(2^(1+l+K)-1)*q<=(a*2+b+1)*4 ->
  P (j*2+2) input ([0;0]^^l*>t*>ys*>r) ->
  exists out, Normal out /\ cfg (fs*>w^^j*>input) -->+ out.
Proof.
  intros Hl Hj Hn Hlpos Hlwidth HK Hz Hrank Hedge Hy Hr He Hcap Hp.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (CounterRun_total _ _ (ICounter_total l) (b+j) 1
    (Word_bound _ _ _ (Word_one l))) as (m&c&Hi&Hm).
  destruct (CounterRun_total _ _ (fun z => GCounter_total l z Hlpos) (a-j) m Hm)
    as (v&e&Hg&Hv).
  destruct (G_word_atom _ _ _ _ _ (c+e) HK Hz Hy Hr)
    as (Z&C&zs&s&Hright&Hzs&Hs&Hat&Hrun).
  destruct (split_root a b j fs input l _ _ _ _ _ _ (level_frame _ _ _ _ Hl)
    Hj Hlpos Hp Hi Hg Hrun) as (xs&Hx&Hstep).
  exists (cfg (fs*>w^^j*>xs*>zs*>s)); split; [|exact Hstep].
  pose proof (split_E_capacity _ _ _ _ _ _ _ _ _ _ _ _
    Ha Hab Hba Hj Hn Hlpos HK Hz He Hcap Hi Hg) as Htotal.
  assert (Hvpos:0<v) by (eapply GCounterRun_positive; [exact Hg|eapply ICounterRun_positive; eauto; lia]).
  destruct (le_dec 3 l) as [Hlarge|Hsmall].
  - right; eapply droot; [exact Hl|exact Hj|].
    eapply DWord with (k:=l) (n:=v); try eassumption; try lia.
    apply DN; try lia; eapply split_head_narrow; eassumption.
  - destruct l as [|[|[|l]]]; try lia.
    + destruct (Nat.eq_dec j a) as [Hedgej|Hinside].
      * right; eapply droot; [exact Hl|exact Hj|].
        eapply DWord with (k:=1%nat) (n:=v); try eassumption; try lia.
        apply D1; [lia|left; exact Hedgej].
      * destruct (Nat.eq_dec v 3) as [->|Hnot].
        -- left; rewrite (Word_max _ _ _ Hx eq_refl).
           change (SRoot (cfg (fs*>w^^j*>w*>zs*>s))).
           assert (Ew:w^^j*>w*>zs*>s=w^^(j+1)*>zs*>s)
             by (rewrite lpow_add, Str_app_assoc; reflexivity).
           rewrite Ew; apply (split_E_absorb_root h a b j fs K z m c e Z C zs (q+C*2) s);
             try assumption; try lia.
           ++ exact (Word_bound _ _ _ Hy).
           ++ pose proof (split_E_one_capacity a b j n K z q m c e
                Ha Hab Hba ltac:(lia) Hn HK Hz He Hcap Hi Hg) as Hstrong.
              pose proof (GCounterRun_balance _ _ _ _ _ Hright HK Hz); nia.
        -- assert (Hnear:j+1=a).
           { destruct (le_dec (j+2) a) as [Hfar|Hnear]; [|lia].
             replace (a-j) with (2+(a-j-2)) in Hg by lia.
             pose proof (GCounterRun_one _ _ _ _ Hg
               (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)) Hm); lia. }
           assert (Ev:v=1%nat).
           { destruct (Nat.eq_dec (v mod 2) 0%nat) as [Heven|Hodd]; [|cbn in Hv; lia].
             destruct (GCounterRun_even _ _ _ _ _ Hg Heven) as (_&Ev&Hmeven).
             pose proof (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)); cbn in Hv; lia. }
           subst v; right; eapply droot; [exact Hl|exact Hj|].
           eapply DWord with (k:=1%nat) (n:=1%nat); try eassumption; try lia.
           apply D1; [lia|right; split; [exact Hnear|reflexivity]].
    + right; eapply droot; [exact Hl|exact Hj|].
      eapply DWord with (k:=2%nat) (n:=v); try eassumption; try lia.
      apply D2; [|lia|].
      * destruct (Nat.eq_dec (v mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
        right; destruct (GCounterRun_even _ _ _ _ _ Hg ltac:(lia)) as (_&Ev&Hmeven).
        pose proof (ICounterRun_positive _ _ _ _ _ Hi ltac:(lia)); lia.
      * right; pose proof (level_size _ _ _ _ Hl) as Hsize.
        assert (Hpow:2^(K+2)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
        rewrite Nat.pow_add_r in Hpow; cbn[Nat.pow] in Hpow; nia.
Qed.

Lemma split_E_end_closed h a b j fs l q r input : Level h a b fs ->
  0<j -> j<=a -> l+2=h -> Num q r -> q<=1 ->
  P (j*2+2) input ([0;0]^^l*>t*>d*>r) ->
  exists out, DRoot out /\ cfg (fs*>w^^j*>input) -->+ out.
Proof.
  intros Hl Hjpos Hj Hwidth Hr Hq Hp.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  replace (h-1) with (1+l) in Hsize by lia.
  destruct (CounterRun_total _ _ (ICounter_total l) (b+j) 1
    (Word_bound _ _ _ (Word_one l))) as (m&c&Hi&Hm).
  destruct (ICounterRun_linear _ _ _ _ _ Hi ltac:(lia)) as (Em&Ec); subst m c.
  destruct (CounterRun_total _ _ (fun z => GCounter_total l z ltac:(lia)) (a-j) _ Hm)
    as (v&e&Hg&Hv).
  destruct (GCounterRun_linear _ _ _ _ _ Hg ltac:(lia)) as (Ev&Ee); subst e.
  destruct (split_root a b j fs input l _ _ _ _ _ _ (level_frame _ _ _ _ Hl)
    Hj ltac:(lia) Hp Hi Hg (G0 (d*>r))) as (xs&Hx&Hstep).
  exists (cfg (fs*>w^^j*>xs*>d*>r)); split; [|exact Hstep].
  eapply droot; [exact Hl|exact Hj|].
  eapply DWord with (k:=l) (n:=v) (l:=1%nat) (tau:=1%nat) (x:=q*2+1);
    try eassumption; try lia.
  - apply AtomEnd; assumption.
  - apply DN; try lia; eapply split_head_narrow; eassumption || lia.
  - pose proof (phi_bounds v ltac:(lia)); cbn[Nat.add Nat.pow] in Hsize; nia.
Qed.

Lemma split_O_small_budget h a b j fs K z m c Z C : Level h a b fs ->
  j<a -> 0<K -> K+2<=h -> 0<z ->
  (K+2=h -> a*2+b+1+j*3+2<=z*4) ->
  CounterRun (ICounter 1) (a-j-1) 1 m c ->
  CounterRun (GCounter K) c z Z C -> Z mod 2=0%nat ->
  2^(1+K)<=Z+(b+j+1)*2.
Proof.
  intros Hl Hj HK Hwidth Hz Hedge Hi Hg Heven.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  destruct (GCounterRun_even _ _ _ _ _ Hg Heven) as (_&EZ&Hze).
  destruct (le_dec (K+3) h) as [Hsmall|Hlarge].
  - assert (Hp:2^(2+K)<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
    cbn[Nat.add Nat.pow] in Hp |- *; lia.
  - assert (EK:K+2=h) by lia; specialize (Hedge EK).
    replace (h-1) with (1+K) in Hsize by lia.
    pose proof (ICounterRun_balance _ _ _ _ _ Hi) as Ei.
    pose proof (ICounterRun_bound _ _ _ _ _ Hi ltac:(cbn; lia)) as Hm.
    change (m+c*3=1+(a-j-1)) in Ei; change (m<4) in Hm; lia.
Qed.

Lemma split_O_positive_closed h a b j fs l K z ys Q r input r0 r1 :
  Level h a b fs -> j<a -> 0<l -> l+2<=h -> 0<K -> 0<z ->
  1+l+K<=h -> (l=1%nat -> K+2=h -> a*2+b+1+j*3+2<=z*4) ->
  Word K z ys -> Num Q r ->
  (2^l*(z*2+1))*2+(2^(2+l+K)-1)*Q <= (a*2+b+1)*4+b*4+j*8+11 ->
  Inner j input (t*>r0) -> G (b+j) r0 r1 ->
  P 2 r1 ([0;0]^^l*>t*>ys*>r) ->
  exists out, DRoot out /\ cfg (fs*>w^^j*>input) -->+ out.
Proof.
  intros Hl Hj Hlpos Hlwidth HK Hz Hrank Hedge Hy Hr Hcap Hin Hmid Hp.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  destruct (CounterRun_total _ _ (ICounter_total l) (a-j-1) 1
    (Word_bound _ _ _ (Word_one l))) as (m&c&Hi&Hm).
  destruct (G_word_atom _ _ _ _ _ c HK Hz Hy Hr) as (Z&C&zs&s&Hright&Hzs&Hs&Hat&Hrun).
  destruct (split_inside _ _ _ _ _ _ _ _ _ _ _ _ (level_frame _ _ _ _ Hl)
    Hj Hin Hmid Hp Hi Hrun) as (xs&Hx&Hstep).
  exists (cfg (fs*>w^^j*>xs*>zs*>s)); split; [|exact Hstep].
  pose proof (split_O_capacity a b j l K z Q m c Hj Hlpos HK Hz Hcap Hi) as Htotal.
  eapply droot; [exact Hl|lia|].
  destruct (Nat.eq_dec l 1) as [->|Hlarge].
  - assert (Hatom:Atom K (Nat.min (2^K) (b+j+1))
      (phi z+(2^K-1)*Q+c*2) (zs*>s)).
    { pose proof (GCounterRun_balance _ _ _ _ _ Hright HK Hz) as E.
      replace (phi z+(2^K-1)*Q+c*2) with (phi Z+(2^K-1)*(Q+C*2)) by nia.
      econstructor; try eassumption.
      - eapply GCounterRun_positive; eassumption.
      - apply Nat.le_min_l.
      - destruct (Nat.eq_dec (Z mod 2) 1%nat) as [Hodd|Heven]; [left; exact Hodd|].
        right; destruct (le_dec (2^K) (b+j+1)).
        + rewrite Nat.min_l by lia; cbn[Nat.add Nat.pow]; lia.
        + rewrite Nat.min_r by lia.
          eapply split_O_small_budget; try eassumption; try lia. }
    eapply DWord with (k:=2%nat) (n:=m*2+1)
      (l:=K) (tau:=Nat.min (2^K) (b+j+1)); try eassumption; try lia.
    apply D2; [left; lia|lia|right; apply Nat.le_min_r].
  - eapply DWord with (k:=1+l) (n:=m*2+1); try eassumption; try lia.
    destruct (le_dec (l+3) h) as [Hsmall|Hwide].
    + apply DN; try lia; left; lia.
    + assert (El:1+l=h-1) by lia.
      pose proof (level_size _ _ _ _ Hl) as Hsize; rewrite <-El in Hsize.
      destruct (ICounterRun_linear _ _ _ _ _ Hi ltac:(lia)) as (Em&Ec).
      replace (m*2+1) with ((a-j)*2+1) by lia.
      rewrite El; apply DY; lia.
Qed.

Lemma split_O_end_closed h a b j fs l q r input r0 r1 : Level h a b fs ->
  j<a -> l+2=h -> Num q r -> q<=1 ->
  Inner j input (t*>r0) -> G (b+j) r0 r1 ->
  P 2 r1 ([0;0]^^l*>t*>d*>r) ->
  exists out, DRoot out /\ cfg (fs*>w^^j*>input) -->+ out.
Proof.
  intros Hl Hj Hwidth Hr Hq Hin Hmid Hp.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  replace (h-1) with (1+l) in Hsize by lia.
  destruct (CounterRun_total _ _ (ICounter_total l) (a-j-1) 1
    (Word_bound _ _ _ (Word_one l))) as (m&c&Hi&Hm).
  destruct (ICounterRun_linear _ _ _ _ _ Hi ltac:(lia)) as (Em&Ec); subst c.
  destruct (split_inside _ _ _ _ _ _ _ _ _ _ _ _ (level_frame _ _ _ _ Hl)
    Hj Hin Hmid Hp Hi (G0 (d*>r))) as (xs&Hx&Hstep).
  exists (cfg (fs*>w^^j*>xs*>d*>r)); split; [|exact Hstep].
  eapply droot; [exact Hl|lia|].
  eapply DWord with (k:=1+l) (n:=m*2+1) (l:=1%nat) (tau:=1%nat) (x:=q*2+1);
    try eassumption; try lia.
  - apply AtomEnd; assumption.
  - replace (m*2+1) with ((a-j)*2+1) by lia.
    replace (1+l) with (h-1) by lia; apply DY; lia.
  - assert (Ephi:phi (m*2+1)=m*2+1) by (unfold phi; lia).
    rewrite Ephi, <-Hsize; nia.
Qed.

Lemma single_y_split_closed h a b j fs k xs q r : Level h a b fs -> j<a ->
  h<=k+1 -> k<=h -> (a+b*2+j*3+2) mod 2=0%nat ->
  Word (1+k) ((a-j)*2+1) xs -> Num q r ->
  phi ((a-j)*2+1)+(2^(1+k)-1)*q<=(a*2+b+1)*4 ->
  exists out, DRoot out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hmin Hmax Heven Hw Hr Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  assert (Hpow:a*2+b+1<=2^k) by (rewrite Hsize; apply Nat.pow_le_mono_r; lia).
  assert (HX:a+b*2+j*3+6<(a*2+b+1)*2) by lia.
  destruct (P_word_linear (1+k) (j*2+2) _ _ r Hw ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow]; lia)) as (xs0&H0&Hfirst).
  replace ((a-j)*2+1+(j*2+2)*2) with ((a+j+2)*2+1) in H0 by lia.
  destruct (Word_odd_inv _ _ _ H0) as (ys0&Hys0&->).
  destruct (P_word_linear k (b+j) _ _ r Hys0 ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow]; lia)) as (xs1&H1&Hmid).
  replace (a+j+2+(b+j)*2) with (a+b*2+j*3+2) in H1 by lia.
  destruct (P_word_linear k 2 _ _ r H1 ltac:(lia)
    ltac:(cbn[Nat.add Nat.pow]; lia)) as (xs2&H2&Htwo).
  replace (a+b*2+j*3+2+2*2) with (a+b*2+j*3+6) in H2 by lia.
  assert (Hmark:a+b*2+j*3+6<>2^k).
  { destruct (Nat.eq_dec k h) as [->|Hlow].
    - replace h with (1+(h-1)) by lia; cbn[Nat.add Nat.pow]; lia.
    - assert (Ek:k=h-1) by lia; rewrite Ek, <-Hsize; lia. }
  destruct (Word_split _ _ _ H2 ltac:(lia) Hmark) as (l&K&z&ys&Erank&Evalue&Hy&Es&Eone).
  assert (Hlpos:0<l) by (destruct l; [cbn[Nat.pow] in Evalue; lia|lia]).
  assert (Hz:0<z).
  { destruct z as [|z]; [|lia].
    assert (Ep:2^l<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
    clear -Ep Evalue Hsize Hab; cbn[Nat.mul Nat.add] in Evalue; nia. }
  assert (Hlwidth:l+2<=h).
  { destruct (le_dec (l+2) h); [assumption|].
    assert (Ep:2^(h-1)<=2^l) by (apply Nat.pow_le_mono_r; lia).
    clear -Ep Evalue Hsize Hz HX; nia. }
  assert (Hq:q<=1).
  { clear -Hcap Hpow Hj; rewrite phi_odd in Hcap; cbn[Nat.add Nat.pow] in Hcap; nia. }
  rewrite !Str_app_assoc in Hfirst.
  rewrite Es, !Str_app_assoc in Htwo.
  destruct K as [|K].
  - assert (El:l+2=h) by lia.
    assert (Ez:z=1%nat) by (pose proof (Word_bound _ _ _ Hy); cbn in *; lia).
    subst z; pose proof (Word_max _ _ _ Hy eq_refl) as Eys; cbn[lpow List.app] in Eys; subst ys.
    eapply split_O_end_closed; try eassumption; try lia;
      [apply InnerP, Hfirst|apply P_G, Hmid].
  - eapply split_O_positive_closed with (l:=l) (K:=S K) (z:=z) (Q:=q);
      try eassumption; try lia.
    + intros El EK; subst l; cbn[Nat.pow] in Evalue; lia.
    + replace (2+l+S K) with (1+k) by lia; rewrite <-Evalue.
      rewrite phi_odd in Hcap; lia.
    + apply InnerP, Hfirst.
    + apply P_G, Hmid.
Qed.

Lemma single_y_closed k a b j fs K xs q r : Level (3+k) a b fs -> j<=a ->
  3+k<=K+1 -> K<=4+k -> (K<3+k \/ j<a) ->
  Word K ((a-j)*2+1) xs -> Num q r ->
  phi ((a-j)*2+1)+(2^K-1)*q<=(a*2+b+1)*4 ->
  exists out, Normal out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hmin Hmax Hinside Hw Hr Hcap.
  destruct (Nat.eq_dec K (2+k)) as [->|Hnot].
  - destruct (single_y_low_closed _ _ _ _ _ _ _ _ Hl Hj Hw Hr Hcap) as (out&Hout&Hstep).
    exists out; split; [left; exact Hout|exact Hstep].
  - assert (Hj':j<a) by lia.
    destruct (Nat.eq_dec ((a+b*2+j*3+2) mod 2) 1%nat) as [Hodd|Heven].
    + assert (Hodd0:(a+j+2) mod 2=1%nat) by lia.
      destruct (Nat.eq_dec K (3+k)) as [->|Htop].
      * destruct (single_mid_descent_closed k a b j fs ((a-j)*2+1) (a+j+2) xs q r
          Hl Hj ltac:(lia) ltac:(lia) ltac:(lia) Hw Hr (or_introl Hodd0) Hcap)
          as (out&Hout&Hstep).
        exists out; split; [left; exact Hout|exact Hstep].
      * assert (EK:K=4+k) by lia; subst K.
        pose proof (level_size _ _ _ _ Hl) as Hsize.
        change (a*2+b+1=2^(2+k)) in Hsize.
        assert (Eq:q=0%nat) by (clear -Hcap Hsize Hj'; rewrite phi_odd in Hcap;
          cbn[Nat.add Nat.pow] in Hcap, Hsize; nia).
        subst q; destruct (single_y_top_odd_closed _ _ _ _ _ _ _ Hl Hj' Hodd Hw Hr)
          as (out&Hout&Hstep).
        exists out; split; [left; exact Hout|exact Hstep].
    + assert (Heven':(a+b*2+j*3+2) mod 2=0%nat) by lia.
      destruct K as [|K]; [lia|].
      destruct (single_y_split_closed (3+k) a b j fs K xs q r Hl Hj'
        ltac:(lia) ltac:(lia) Heven' Hw Hr Hcap) as (out&Hout&Hstep).
      exists out; split; [right; exact Hout|exact Hstep].
Qed.

Lemma single_even_split_closed h a b j fs k n xs q r : Level h a b fs -> j<=a ->
  h<=k+1 -> k<=h -> 0<n -> n mod 2=0%nat ->
  a*2+b+1<n+j*4+4 -> n+j*4+4<(a*2+b+1)*3 ->
  n+j*4+4<2^(1+k) -> n+j*4+4<>2^k ->
  (k=h -> a*2+b+1-j<=n) -> (k+1=h -> q<=1) ->
  (j=0%nat -> n*2+8<(a*2+b+1)*3) ->
  Word k n xs -> Num q r -> phi n+(2^k-1)*q<=(a*2+b+1)*4 ->
  exists out, Normal out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hmin Hmax Hn Heven Hlower Hupper Hlinear Hmarker Hphase Hq Hzero Hw Hr Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize.
  destruct (P_word_linear k (j*2+2) _ _ r Hw ltac:(lia) ltac:(lia)) as (zs&Hzs&Hp).
  replace (n+(j*2+2)*2) with (n+j*4+4) in Hzs by lia.
  destruct (Word_split _ _ _ Hzs ltac:(lia) Hmarker) as (l&K&z&ys&Erank&Evalue&Hy&Es&Eone).
  assert (Hlpos:0<l) by (destruct l; [cbn[Nat.pow] in Evalue; lia|lia]).
  assert (Hz:0<z).
  { destruct z as [|z]; [|lia].
    assert (Ep:2^l<=2^(h-1)) by (apply Nat.pow_le_mono_r; lia).
    clear -Ep Evalue Hsize Hlower; cbn[Nat.mul Nat.add] in Evalue; nia. }
  assert (Hlwidth:l+2<=h).
  { destruct (le_dec (l+2) h); [assumption|].
    assert (Ep:2^(h-1)<=2^l) by (apply Nat.pow_le_mono_r; lia).
    clear -Ep Evalue Hsize Hz Hupper; nia. }
  rewrite Es, !Str_app_assoc in Hp.
  destruct K as [|K].
  - assert (El:l+2=h) by lia.
    assert (Ez:z=1%nat) by (pose proof (Word_bound _ _ _ Hy); cbn in *; lia).
    subst z; pose proof (Word_max _ _ _ Hy eq_refl) as Eys; cbn[lpow List.app] in Eys; subst ys.
    assert (Hjpos:0<j).
    { destruct j; [|lia]; specialize (Hzero eq_refl).
      replace (h-1) with (1+l) in Hsize by lia.
      cbn[Nat.add Nat.pow] in Hsize; nia. }
    destruct (split_E_end_closed h a b j fs l q r (xs*>r) Hl Hjpos Hj El Hr
      ltac:(apply Hq; lia) Hp) as (out&Hout&Hstep).
    exists out; split; [right; exact Hout|exact Hstep].
  - eapply split_E_positive_closed with (n:=n) (l:=l) (K:=S K) (z:=z) (q:=q);
      try eassumption; try lia.
    + intros El EK; subst l; specialize (Hphase ltac:(lia)); cbn[Nat.pow] in Evalue; lia.
    + replace (1+l+S K) with k by lia; exact Hcap.
Qed.

Lemma single_x_low_closed k a b j fs xs q r : Level (3+k) a b fs -> j<=a ->
  Word (2+k) (a*2+b+1-j) xs -> Num q r -> q<=1 ->
  phi (a*2+b+1-j)+(2^(2+k)-1)*q<=(a*2+b+1)*4 ->
  exists out, Normal out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hw Hr Hq Hcap.
  destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  destruct (Nat.eq_dec ((a*2+b+1-j) mod 2) 1%nat) as [Hodd|Heven].
  - destruct (single_x_low_odd_closed _ _ _ _ _ _ _ _ Hl Hj Hodd Hw Hr Hcap)
      as (out&Hout&Hstep).
    exists out; split; [left; exact Hout|exact Hstep].
  - destruct (le_dec (2^(3+k)) (a*2+b+1-j+j*4+4)) as [Hlate|Hsplit].
    + cbn[Nat.add Nat.pow] in Hlate, Hsize.
      destruct (Nat.eq_dec a b) as [<-|Hnext].
      * assert (Ej:j=a-1) by lia; subst j.
        replace (a*2+a+1-(a-1)) with (a*2+2) in Hw by lia.
        destruct (late_second_Q_recover_closed (1+k) a fs xs q r Hl Hw Hr ltac:(lia))
          as (out&Hout&Hstep).
        exists out; split; [left; exact Hout|exact Hstep].
      * assert (Eb:b=a+1) by lia; subst b.
        assert (Ej:j=a) by lia; subst j.
        replace (a*2+(a+1)+1-a) with (a*2+2) in Hw by lia.
        destruct (late_first_Q_boundary_closed (1+k) a fs xs q r Hl Hw Hr Hq)
          as (out&Hout&Hstep).
        exists out; split; [left; exact Hout|exact Hstep].
    + eapply single_even_split_closed with (h:=3+k) (k:=2+k) (n:=a*2+b+1-j) (q:=q);
        try eassumption; try lia.
      change (a*2+b+1-j+j*4+4<2^(3+k)); lia.
Qed.

(* Complete wide-word classification. Congruences exclude the remaining
   dangerous returns; aligned top markers enter the translated loop. *)
Lemma pow2_mod7 n : 2^n mod 7=1%nat \/ 2^n mod 7=2%nat \/ 2^n mod 7=4%nat.
Proof.
  induction n; [left; reflexivity|].
  rewrite Nat.pow_succ_r, Nat.mul_mod by lia.
  destruct IHn as [H|[H|H]]; rewrite H; cbn; tauto.
Qed.

Lemma CounterRun_unique step :
  (forall n m c m' c', step n m c -> step n m' c' -> m=m' /\ c=c') ->
  forall i n m c, CounterRun step i n m c ->
  forall m' c', CounterRun step i n m' c' -> m=m' /\ c=c'.
Proof.
  intros Hd i n m c H; induction H as [n|i n m z c d Hs Hr IH]; intros z' e H'.
  - inversion H'; subst; split; reflexivity.
  - inversion H' as [|i0 n0 m0 z0 c0 d0 Hs0 Hr0]; subst.
    destruct (Hd _ _ _ _ _ Hs Hs0) as [-> ->].
    destruct (IH _ _ Hr0); split; lia.
Qed.

Lemma GCounterRun_unique k i n m c : CounterRun (GCounter k) i n m c ->
  forall m' c', CounterRun (GCounter k) i n m' c' -> m=m' /\ c=c'.
Proof.
  apply CounterRun_unique; intros * H H'; destruct H; inversion H'; subst; split; lia.
Qed.

Lemma pow2_mod15 n : 2^n mod 15=1%nat \/ 2^n mod 15=2%nat \/
  2^n mod 15=4%nat \/ 2^n mod 15=8%nat.
Proof.
  induction n; [left; reflexivity|].
  rewrite Nat.pow_succ_r, Nat.mul_mod by lia.
  destruct IHn as [H|[H|[H|H]]]; rewrite H; cbn; tauto.
Qed.

Definition RootProgress c := (exists out, Normal out /\ c -->+ out) \/ ~halts tm c.

Lemma split_O_word_closed h a b j fs k x xs q r input r0 :
  Level h a b fs -> j<a -> 0<k -> k+1<=h -> x mod 2=0%nat ->
  2^k<x+4 -> x+4<2^(1+k) ->
  ((x+4)*2=2^k*3 -> k+1=h /\ q<=1) ->
  Word k x xs -> Num q r ->
  (x+4)*2+(2^(1+k)-1)*q<=(a*2+b+1)*4+b*4+j*8+11 ->
  Inner j input (t*>r0) -> G (b+j) r0 (xs*>r) ->
  exists out, DRoot out /\ cfg (fs*>w^^j*>input) -->+ out.
Proof.
  intros Hl Hj Hk Hwidth Heven Hlower Hupper Hend Hw Hr Hcap Hin Hmid.
  destruct (P_word_linear k 2 _ _ r Hw Hk ltac:(lia)) as (zs&Hzs&Hp).
  destruct (Word_split _ _ _ Hzs ltac:(lia) ltac:(lia)) as (l&K&z&ys&Erank&Evalue&Hy&Es&Eone).
  assert (Hlpos:0<l) by (destruct l; [cbn[Nat.pow] in Evalue; lia|lia]).
  assert (Hz:0<z).
  { destruct z as [|z]; [|lia].
    assert (Ep:2^l<=2^k) by (apply Nat.pow_le_mono_r; lia).
    clear -Ep Evalue Hlower; cbn[Nat.mul Nat.add] in Evalue; nia. }
  rewrite Es, !Str_app_assoc in Hp.
  destruct K as [|K].
  - assert (Ez:z=1%nat) by (pose proof (Word_bound _ _ _ Hy); cbn in *; lia).
    subst z; pose proof (Word_max _ _ _ Hy eq_refl) as Eys; cbn[lpow List.app] in Eys; subst ys.
    destruct Hend as (Hkh&Hq).
    { replace k with (1+l) by lia; cbn[Nat.add Nat.pow]; lia. }
    eapply split_O_end_closed; try eassumption; lia.
  - eapply split_O_positive_closed with (l:=l) (K:=S K) (z:=z) (Q:=q);
      try eassumption; try lia.
    replace (2+l+S K) with (1+k) by lia; rewrite <-Evalue; exact Hcap.
Qed.

Lemma single_x_mid_closed k a b j fs xs r : Level (3+k) a b fs -> j<=a ->
  Word (3+k) (a*2+b+1-j) xs -> Num 0 r ->
  RootProgress (cfg (fs*>w^^j*>xs*>r)).
Proof.
  intros Hl Hj Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  pose proof (pow2_mod7 (2+k)) as Hmod; rewrite <-Hsize in Hmod.
  assert (Hcap:phi (a*2+b+1-j)+(2^(3+k)-1)*0<=(a*2+b+1)*4)
    by (rewrite Nat.mul_0_r; unfold phi; lia).
  destruct (Nat.eq_dec ((a*2+b+1-j) mod 2) 0%nat) as [Heven|Hodd].
  - destruct (Nat.eq_dec (a*2+b+1-j+j*4+4) (2^(3+k))) as [Hmark|Hsplit].
    + assert (Eb:b=a /\ a=j+1) by (cbn[Nat.add Nat.pow] in Hmark, Hsize; lia).
      destruct Eb as [-> Ea]; right.
      eapply (translated_word_nonhalt a j fs (3+k) xs r);
        [exact (level_frame _ _ _ _ Hl)|exact Ea| |].
      * cbn[Nat.add Nat.pow] in Hsize |- *; lia.
      * applys_eq Hw; flia.
    + left; eapply single_even_split_closed with (h:=3+k) (k:=3+k)
        (n:=a*2+b+1-j) (q:=0%nat); try eassumption; try lia.
      cbn[Nat.add Nat.pow] in Hsize |- *; lia.
  - remember ((a*2+b+j*3+4)/2) as u.
    assert (Eu:a*2+b+1-j+(j*2+2)*2=u*2+1) by lia.
    destruct (Nat.eq_dec (u mod 2) 1%nat) as [Huodd|Hueven].
    + destruct (single_mid_descent_closed k a b j fs (a*2+b+1-j) u xs 0 r Hl Hj
        ltac:(lia) ltac:(lia) Eu Hw Hr (or_introl Huodd) Hcap) as (out&Hout&Hstep).
      left; exists out; split; [left; exact Hout|exact Hstep].
    + destruct (le_dec (2^(3+k)) (u+(b+j)*2)) as [Hsat|Hlin].
      * destruct (single_mid_descent_closed k a b j fs (a*2+b+1-j) u xs 0 r Hl Hj
          ltac:(lia) ltac:(lia) Eu Hw Hr (or_intror Hsat) Hcap) as (out&Hout&Hstep).
        left; exists out; split; [left; exact Hout|exact Hstep].
      * assert (Hj':j<a) by (cbn[Nat.add Nat.pow] in Hsize, Hlin; lia).
        destruct (le_dec (2^(3+k)) (u+(b+j)*2+4)) as [Hlate|Hearly].
        -- assert (Ecase:b=a /\ j*7+4=a*5).
           { cbn[Nat.add Nat.pow] in Hsize, Hlin, Hlate; destruct Hmod as [Hmod|[Hmod|Hmod]]; lia. }
           destruct Ecase as [-> Ej].
           destruct (first_Q_x_closed (1+k) a j fs xs r Hl Ej ltac:(applys_eq Hw; flia) Hr)
             as (out&Hout&Hstep).
           left; exists out; split; [left; exact Hout|exact Hstep].
        -- destruct (P_word_linear (3+k) (j*2+2) _ _ r Hw ltac:(lia)
             ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)) as (bs&Hbs&Hp).
           rewrite Eu in Hbs; destruct (Word_odd_inv _ _ _ Hbs) as (cs&Hcs&->).
           destruct (P_word_linear (2+k) (b+j) _ _ r Hcs ltac:(lia)
             ltac:(change (u+(b+j)*2<2^(3+k)); lia)) as (ds&Hds&Hmid).
           rewrite Str_app_assoc in Hp.
           destruct (split_O_word_closed (3+k) a b j fs (2+k) (u+(b+j)*2) ds 0 r (xs*>r) (cs*>r)
             Hl Hj' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(change (u+(b+j)*2+4<2^(3+k)); lia)
             ltac:(intro; split; lia) Hds Hr ltac:(rewrite Nat.mul_0_r; lia)
             (InnerP _ _ _ Hp) (P_G _ _ _ Hmid)) as (out&Hout&Hstep).
           left; exists out; split; [right; exact Hout|exact Hstep].
Qed.

Lemma z_middle_bounds a b j n u v c : 5<=a -> a<=b -> b<=a+1 -> j<=a ->
  n*2=(a*2+b+1)*2+(a-j) -> 0<u -> u<a*2+b+1 ->
  v=u+(b+j)*2 -> v<a*2+b+1 -> v mod 2=0%nat ->
  u*2+1+c*((a*2+b)*2)=phi n+(j*2+2)*2 ->
  (n mod 2=1%nat \/ (a*2+b+1)*2<=n+j*4) ->
  ((a*2+b+1) mod 15=1%nat \/ (a*2+b+1) mod 15=2%nat \/
   (a*2+b+1) mod 15=4%nat \/ (a*2+b+1) mod 15=8%nat) ->
  j<a /\ a*2+b+1<(v+4)*2 /\ v+4<a*2+b+1 /\ (v+4)*4<>(a*2+b+1)*3.
Proof.
  intros Ha Hab Hba Hj Hn Hu Hub Ev Hv Hevenv E Hguard Hmod.
  assert (Hphi:phi n<=n) by (unfold phi; lia).
  assert (Hc:c<=1).
  { destruct c as [|[|c]]; try lia; cbn[Nat.mul] in E; nia. }
  assert (Hce:n mod 2=0%nat -> c=1%nat).
  { intro Heven; destruct c; [unfold phi in E; rewrite Heven in E; destruct Hguard; lia|lia]. }
  assert (Hj':j<a) by lia.
  assert (Hlower:a*2+b+1<(v+4)*2) by lia.
  repeat split; try assumption.
  - destruct c as [|[|c]]; try lia;
      destruct (Nat.eq_dec (n mod 2) 0%nat) as [Heven|Hodd];
      try (specialize (Hce Heven); lia);
      unfold phi in E; try rewrite Heven in E;
      destruct Hmod as [Hmod|[Hmod|[Hmod|Hmod]]]; cbn[Nat.mul] in E; lia.
  - destruct c as [|[|c]]; try lia;
      destruct (Nat.eq_dec (n mod 2) 0%nat) as [Heven|Hodd];
      try (specialize (Hce Heven); lia);
      unfold phi in E; try rewrite Heven in E; cbn[Nat.mul] in E; lia.
Qed.

Lemma single_z_guard_closed k a b j fs n xs r : Level (3+k) a b fs -> j<=a ->
  n*2=(a*2+b+1)*2+(a-j) -> Word (2+k) n xs -> Num 0 r ->
  (n mod 2=1%nat \/ 2^(3+k)<=n+j*4) ->
  exists out, Normal out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hn Hw Hr Hguard; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  assert (Hnpos:0<n) by lia.
  assert (Hcap:phi n+(2^(2+k)-1)*0<=(a*2+b+1)*4)
    by (rewrite Nat.mul_0_r; pose proof (phi_bounds _ Hnpos); lia).
  destruct (counter_inner_total (2+k) j n ltac:(lia) (Word_bound _ _ _ Hw) Hguard)
    as (u&c0&Hu&Hub&H0).
  destruct (CounterRun_total _ _ (fun z=>GCounter_total (1+k) z ltac:(lia)) (b+j) u Hub)
    as (v&c1&H1&Hvb).
  destruct (Nat.eq_dec (v mod 2) 1%nat) as [Hodd|Heven].
  - assert (Hready:forall u' v' c0' c1',
      CounterRun (GCounter (2+k)) (j*2+2) n (u'*2+1) c0' ->
      CounterRun (GCounter (1+k)) (b+j) u' v' c1' -> v' mod 2=1%nat).
    { intros * H0' H1'.
      destruct (GCounterRun_unique _ _ _ _ _ H0 _ _ H0') as (Eu&Ec).
      assert (u'=u) by lia; subst u'.
      destruct (GCounterRun_unique _ _ _ _ _ H1 _ _ H1'); lia. }
    destruct (single_low_descent_closed _ _ _ _ _ _ _ _ _ Hl Hj Hnpos Hw Hr Hguard Hready Hcap)
      as (out&Hout&Hstep).
    exists out; split; [left; exact Hout|exact Hstep].
  - destruct (GCounterRun_even _ _ _ _ _ H1 ltac:(lia)) as (->&Ev&Huo).
    pose proof (GCounterRun_balance _ _ _ _ _ H0 ltac:(lia) Hnpos) as E.
    rewrite phi_odd in E.
    pose proof (pow2_mod15 (2+k)) as Hmod; rewrite <-Hsize in Hmod.
    assert (E':u*2+1+c0*((a*2+b)*2)=phi n+(j*2+2)*2) by (rewrite <-Hsize in E; lia).
    assert (Hguard':n mod 2=1%nat \/ (a*2+b+1)*2<=n+j*4)
      by (cbn[Nat.add Nat.pow] in Hguard, Hsize; lia).
    destruct (z_middle_bounds a b j n u v c0 Ha Hab Hba Hj Hn Hu
      ltac:(lia) Ev ltac:(change (v<2^(2+k)) in Hvb; lia) ltac:(lia) E' Hguard' Hmod)
      as (Hj'&Hlower&Hupper&Hend).
    destruct (G_nums c0 _ _ Hr) as (s&Hs&Htail).
    destruct (counter_inner _ _ _ _ _ _ _ _ Hw ltac:(lia) Hguard H0 Htail) as (bs&Hbs&Hin).
    destruct (Word_odd_inv _ _ _ Hbs) as (cs&Hcs&->).
    destruct (G_counter_run _ _ _ _ _ _ _ _ Hcs ltac:(lia) H1 (G0 s)) as (ds&Hds&Hmid).
    rewrite Str_app_assoc in Hin.
    destruct (split_O_word_closed (3+k) a b j fs (1+k) v ds (c0*2) s (xs*>r) (cs*>s)
      Hl Hj' ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(cbn[Nat.add Nat.pow] in Hsize |- *; lia)
      ltac:(change (v+4<2^(2+k)); lia)
      ltac:(intro Heq; cbn[Nat.add Nat.pow] in Hsize, Heq; exfalso; lia)
      Hds Hs ltac:(change ((v+4)*2+(2^(2+k)-1)*(c0*2)<=(a*2+b+1)*4+b*4+j*8+11);
        rewrite <-Hsize; clear -E' Ev Hcap; rewrite Nat.mul_0_r in Hcap; nia)
      Hin Hmid) as (out&Hout&Hstep).
    exists out; split; [right; exact Hout|exact Hstep].
Qed.

Lemma single_z_closed k a b j fs n xs r : Level (3+k) a b fs -> j<=a ->
  n*2=(a*2+b+1)*2+(a-j) -> Word (2+k) n xs -> Num 0 r ->
  exists out, Normal out /\ cfg (fs*>w^^j*>xs*>r) -->+ out.
Proof.
  intros Hl Hj Hn Hw Hr; destruct (Level_bounds _ _ _ _ Hl) as (Hh&Ha&Hab&Hba).
  pose proof (level_size _ _ _ _ Hl) as Hsize; change (a*2+b+1=2^(2+k)) in Hsize.
  destruct (Nat.eq_dec (n mod 2) 1%nat) as [Hodd|Heven].
  - eapply single_z_guard_closed; try eassumption; left; exact Hodd.
  - destruct (le_dec (2^(3+k)) (n+j*4)) as [Hguard|Hlate].
    + eapply single_z_guard_closed; try eassumption; right; exact Hguard.
    + destruct (le_dec (2^(3+k)) (n+j*4+4)) as [Hend|Hsplit].
      * pose proof (pow2_mod7 (2+k)) as Hmod; rewrite <-Hsize in Hmod.
        assert (Ecase:b=a+1 /\ j*7=a*5).
        { cbn[Nat.add Nat.pow] in Hsize, Hlate, Hend;
            destruct Hmod as [Hmod|[Hmod|Hmod]]; lia. }
        destruct Ecase as [-> Ej].
        destruct (late_first_Q_z_closed k a j fs n xs r Hl Ej ltac:(lia) Hw Hr)
          as (out&Hout&Hstep).
        exists out; split; [left; exact Hout|exact Hstep].
      * eapply single_even_split_closed with (h:=3+k) (k:=2+k) (n:=n) (q:=0%nat);
          try eassumption; try lia.
        -- change (n+j*4+4<2^(3+k)); lia.
        -- rewrite Nat.mul_0_r; pose proof (phi_bounds n ltac:(lia)); lia.
Qed.

Lemma root_progress_single c : (exists out, SRoot out /\ c -->+ out) -> RootProgress c.
Proof. intros (out&Hout&Hstep); left; exists out; split; [left; exact Hout|exact Hstep]. Qed.

Lemma single_root_progress c : SRoot c -> RootProgress c.
Proof.
  intros [h a b j fs r Hl Hj Hs].
  pose proof (level_height _ _ _ _ Hl) as Hh.
  destruct h as [|[|[|h]]]; try lia.
  change (Level (3+h) a b fs) in Hl.
  destruct Hs as [n r Hr Hbound|k n q xs r Hk Hn Hw Hr Hp Hcap].
  - apply root_progress_single; eapply pure_closed; eassumption.
  - destruct Hp.
    + apply root_progress_single; eapply narrow_closed; eassumption.
    + apply root_progress_single; eapply two_closed; try eassumption; cbn[Nat.pow] in Hcap; lia.
    + apply root_progress_single; destruct H as [->|(Hnear&En&Hq)].
      * eapply one_boundary_closed; try eassumption; cbn[Nat.pow] in Hcap; lia.
      * subst n; eapply one_neighbor_closed; eassumption.
    + destruct H as [(Ek&Hq)|[(Ek&Eq)|(Ek&Ej&Eb&Eq)]].
      * assert (Ek':k=2+h) by lia; subst k.
        left; eapply single_x_low_closed; eassumption.
      * subst k q; eapply single_x_mid_closed; eassumption.
      * subst k j b q.
        replace (a*2+a+1-a) with (a*2+1) in Hw by lia.
        replace (S (S (S h))+1) with (4+h) in Hw by lia.
        apply root_progress_single; eapply single_x_top_closed; eassumption.
    + left; eapply single_y_closed; try eassumption; lia.
    + replace (S (S (S h))-1) with (2+h) in Hw by lia.
      left; eapply single_z_closed; eassumption.
Qed.

Lemma normal_nonhalt c : Normal c -> ~halts tm c.
Proof.
  intro Hc; eapply progress_nonhalt with (P:=fun c => Normal c \/ ~halts tm c);
    [|left; exact Hc].
  intros x Hx.
  assert (Hp:RootProgress x).
  { destruct Hx as [[Hs|Hd]|Hnh];
      [apply single_root_progress, Hs|left; apply double_progress, Hd|right; exact Hnh]. }
  destruct Hp as [(y&Hy&Hstep)|Hnh].
  - exists y; split; [left; exact Hy|exact Hstep].
  - destruct (no_halted_step tm x) as [y Hstep].
    + intro Hhalt; apply Hnh, halted_halts, Hhalt.
    + exists y; split; [|apply progress_base, Hstep].
      right; intro Hhalt; apply Hnh; eapply halts_step; eassumption.
Qed.

Definition initial := cfg (prefix 3*>t^^4*>0inf).
Lemma init : c0 -->* initial.
Proof.
  apply without_counter with (n:=2669); apply multistep_c_spec.
  vm_compute; repeat f_equal.
  change (0inf=0>>0inf); rewrite <-const_unfold; reflexivity.
Qed.

Lemma initial_level : Level 5 5 5 (prefix 3).
Proof. constructor; [exact (frame_spec 3)|lia|reflexivity]. Qed.

Lemma initial_root : SRoot initial.
Proof.
  apply (sroot 5 5 5 0); [exact initial_level|lia|].
  apply (SNum _ _ _ _ 15); [apply (Num10 7), (Num10 3), (Num10 1), (Num10 0), Num0|lia].
Qed.

Lemma initial2_root : SRoot (cfg (prefix 3*>word 3 11*>[0;0;1;0]*>0inf)).
Proof.
  apply (sroot 5 5 5 0); [exact initial_level|lia|].
  apply (SWord _ _ _ _ 3 11 2 (word 3 11) ([0;0;1;0]*>0inf)); try (cbn; lia).
  - apply word_spec; cbn; lia.
  - apply (Num00 1), (Num10 0), Num0.
  - apply SN; [lia|lia|left; reflexivity].
Qed.

Lemma initial3_root : SRoot (cfg (prefix 3*>word 2 5*>[0;0;1;0;1;0]*>0inf)).
Proof.
  apply (sroot 5 5 5 0); [exact initial_level|lia|].
  apply (SWord _ _ _ _ 2 5 6 (word 2 5) ([0;0;1;0;1;0]*>0inf)); try (cbn; lia).
  - apply word_spec; cbn; lia.
  - apply (Num00 3), (Num10 1), (Num10 0), Num0.
  - apply S2; left; reflexivity.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof. eapply multistep_nonhalt; [exact init|apply normal_nonhalt; left; exact initial_root]. Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RA0LE_0LD1RF_1RC1RB_0RD0LB_0RA---").
Definition rename q := match q with A=>B | B=>A | C=>E | D=>D | E=>C | F=>F end.
Lemma correspondence : Perm TM1.tm tm rename.
Proof. split; intros [] [] * H; cbn in H; inversion H; reflexivity. Qed.

Definition initial := 0inf {{E}}> [0;0;1;0]*>TM1.prefix 3*>
  TM1.word 3 11*>[0;0;1;0]*>0inf.
Lemma init : c0 -[tm]->* initial.
Proof.
  apply without_counter with (n:=4293); apply multistep_c_spec.
  vm_compute; repeat f_equal.
  fold (const (0:Sym)); repeat rewrite <-const_unfold; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  apply (perm_nonhalt' TM1.tm tm rename C _ correspondence).
  apply TM1.normal_nonhalt; left; exact TM1.initial2_root.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RC_0LA1RF_1RD0LE_1LC0RB_0RA0LC_0RD---").
Definition rename q := match q with A=>C | B=>D | C=>E | D=>A | E=>B | F=>F end.
Lemma correspondence : Perm TM1.tm tm rename.
Proof. split; intros [] [] * H; cbn in H; inversion H; reflexivity. Qed.

Definition initial := 0inf {{E}}> [0;0;1;0]*>TM1.prefix 3*>
  TM1.word 2 5*>[0;0;1;0;1;0]*>0inf.
Lemma init : c0 -[tm]->* initial.
Proof.
  apply without_counter with (n:=4091); apply multistep_c_spec.
  vm_compute; repeat f_equal.
  fold (const (0:Sym)); repeat rewrite <-const_unfold; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  apply (perm_nonhalt' TM1.tm tm rename C _ correspondence).
  apply TM1.normal_nonhalt; left; exact TM1.initial3_root.
Qed.
End TM3.
