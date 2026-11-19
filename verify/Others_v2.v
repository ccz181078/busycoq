(* OTHERS_29_20261020.txt, TM23.  Original table and complete E/O streams.
   The non-formal proof is in OTHERS29_TM23_NONHALTING.txt. *)
From BusyCoq Require Import Individual62 Longitudinal.
Require Import ZifyNat Lia String List PeanoNat.

Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation X := [1;1;0;1].
Notation Y := [1;1;1;0;1].
Notation hR := (B,<[0;0;1;1]).
Notation hL := (A,[]).
Notation h := [(hR,hL)].
Notation hf := [((B,[]),hL)].
Notation end0 := ([0;0] *> Y *> 0inf).
Notation end1 := ([0] *> Y *> Y *> 0inf).

(* h includes a real pending D on entry: returning through D supplies
   the X in the informal G=X.F.  It is not an autonomous prepend-X. *)
Lemma digit_even n:
  segRLs tm h [] (X^^(1+n)++[0;0]) (X^^(1+n)++[0]++Y).
Proof.
  eapply segRLs_S with (w2:=X^^(1+n)++[0]++Y).
  - intros l r; esx.
  - constructor.
Qed.

Lemma digit_odd n:
  segRLs tm h h (X^^(1+n)++[0]++Y) (X^^(2+n)++[0;0]).
Proof.
  eapply @segRLs_S' with (w2:=[1;1]++[1;1;0;0]^^(2+n))
    (w3:=X^^(2+n)++[0;0]).
  - intros l r; esx.
  - intros l r; esx.
  - constructor.
Qed.

Lemma F_even n:
  segRLs tm hf [] (X^^(1+n)++[0;0]) (X^^n++[0]++Y).
Proof.
  eapply segRLs_S with (w2:=X^^n++[0]++Y).
  - intros l r; esx.
  - constructor.
Qed.

Lemma F_odd n:
  segRLs tm hf h (X^^n++[0]++Y) (X^^n++[0;0]).
Proof.
  eapply @segRLs_S' with (w2:=[1;1]++[1;1;0;0]^^n)
    (w3:=X^^n++[0;0]).
  - intros l r; esx.
  - intros l r; esx.
  - constructor.
Qed.

(* false=E, true=O.  These constructors encode the WHOLE streams,
   including the four small O cases where the O-to-E split is invalid. *)
Inductive Num : bool -> nat -> side -> Prop :=
| Num_O0: Num true 0 (X *> [0;0] *> end0)
| Num_O1: Num true 1 (X *> [0] *> Y *> end0)
| Num_O2: Num true 2 (X^^2 *> [0;0] *> end1)
| Num_O3: Num true 3 (X^^2 *> [0] *> Y *> end1)
| Num_E_even n r: Num true n r ->
    Num false (n*2) (X^^(1+n) *> [0;0] *> r)
| Num_E_odd n r: Num true n r ->
    Num false (1+n*2) (X^^(1+n) *> [0] *> Y *> r)
| Num_O_even n r: Num false n r ->
    Num true (4+n*2) (X^^(3+n) *> [0;0] *> r)
| Num_O_odd n r: Num false n r ->
    Num true (5+n*2) (X^^(3+n) *> [0] *> Y *> r).

Lemma Num_inc [b n r]:
  Num b n r -> exists r', Num b (1+n) r' /\ sideRLs tm h r r'.
Proof.
  intro H; induction H.
  - exists (X *> [0] *> Y *> end0); split; [constructor|esx].
  - exists (X^^2 *> [0;0] *> end1); split; [constructor|esx].
  - exists (X^^2 *> [0] *> Y *> end1); split; [constructor|esx].
  - exists (X^^3 *> [0;0] *> X *> [0;0] *> X *> [0;0] *> end0).
    split; [apply (Num_O_even 0); apply (Num_E_even 0); constructor|esx].
  - eexists; split; [apply Num_E_odd, H|].
    repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    eapply segRLs_sideRLs_concat; [apply digit_even|constructor].
  - destruct IHNum as [r' [HN HR]].
    exists (X^^(2+n) *> [0;0] *> r'); split.
    + applys_eq (Num_E_even (1+n) r' HN); flia.
    + repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
      eapply segRLs_sideRLs_concat; [apply digit_odd|exact HR].
  - eexists; split; [apply Num_O_odd, H|].
    repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    eapply segRLs_sideRLs_concat; [apply (digit_even (2+n))|constructor].
  - destruct IHNum as [r' [HN HR]].
    exists (X^^(4+n) *> [0;0] *> r'); split.
    + applys_eq (Num_O_even (1+n) r' HN); flia.
    + repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
      eapply segRLs_sideRLs_concat; [apply (digit_odd (2+n))|exact HR].
Qed.

Lemma Num_ex b n: exists r, Num b n r.
Proof.
  induction n as [|n [r H]].
  - destruct b; eexists; [apply Num_O0|apply (Num_E_even 0), Num_O0].
  - destruct (Num_inc H) as [r' [HN HR]]; eauto.
Qed.

Lemma Num_unique [b n r r']:
  Num b n r -> Num b n r' -> r=r'.
Proof.
  intro H; gen r'; induction H; intros r' H'; inverts H'; try lia; try reflexivity.
  all: replace n0 with n in * by lia; erewrite IHNum; [reflexivity|eassumption].
Qed.

Lemma Num_add m b n r:
  Num b n r -> exists r', Num b (n+m) r' /\ sideRLs tm (h^^m) r r'.
Proof.
  gen n r; induction m as [|m IH]; introv H.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (Num_inc H) as [r1 [HN HR]].
    destruct (IH _ _ HN) as [r2 [HN' HR']].
    exists r2; split.
    + applys_eq HN'; flia.
    + change (sideRLs tm (h++h^^m) r r2).
      eapply sideRLs_trans; eauto.
Qed.

Definition CutNum b n d r := Num b n (X^^d *> r).

(* A two-case physical view separates prefix removal from the eight
   constructors of the complete stream. *)
Inductive NumView b : nat -> side -> Prop :=
| NV_even k r:
    Num b (1+k*2) (X^^(1+k) *> [0] *> Y *> r) ->
    NumView b (k*2) (X^^(1+k) *> [0;0] *> r)
| NV_odd k r r': sideRLs tm h r r' ->
    Num b (2+k*2) (X^^(2+k) *> [0;0] *> r') ->
    NumView b (1+k*2) (X^^(1+k) *> [0] *> Y *> r).

Lemma Num_view [b n r]: Num b n r -> NumView b n r.
Proof.
  intro H; destruct H.
  - apply (NV_even true 0); constructor.
  - eapply (NV_odd true 0); [esx|apply Num_O2].
  - apply (NV_even true 1); constructor.
  - eapply (NV_odd true 1) with
      (r':=X *> [0;0] *> X *> [0;0] *> end0).
    + esx.
    + apply (Num_O_even 0), (Num_E_even 0), Num_O0.
  - apply NV_even, Num_E_odd, H.
  - destruct (Num_inc H) as [r' [HN HR]].
    eapply NV_odd; [exact HR|].
    applys_eq (Num_E_even (1+n) r' HN); flia.
  - applys_eq (NV_even true (2+n) r); try flia.
    applys_eq (Num_O_odd n r H); flia.
  - destruct (Num_inc H) as [r' [HN HR]].
    applys_eq (NV_odd true (2+n) r r' HR); try flia.
    applys_eq (Num_O_even (1+n) r' HN); flia.
Qed.

Lemma prefix_cancel (w:list Sym) r r': w *> r = w *> r' -> r=r'.
Proof. induction w; cbn; intro H; [exact H|apply IHw; now injection H]. Qed.

Lemma cut_prefix a d r t:
  d<=a -> X^^d *> r = X^^a *> t -> r=X^^(a-d) *> t.
Proof.
  intros Hd H; apply (prefix_cancel (X^^d)).
  rewrite <-Str_app_assoc, <-lpow_add.
  replace (d+(a-d)) with a by lia; exact H.
Qed.

Lemma CutNum_F b n d r:
  CutNum b n d r -> d*2<=1+n ->
  exists r', CutNum b (1+n) (1+d) r' /\ sideRLs tm hf r r'.
Proof.
  intros H Hd; unfold CutNum in H; apply Num_view in H.
  remember (X^^d *> r) as s eqn:Hs in H; destruct H.
  - assert (Er: r=X^^(1+(k-d)) *> [0;0] *> r0).
    { rewrite (cut_prefix (1+k) d r ([0;0] *> r0)).
      - replace (1+k-d) with (1+(k-d)) by lia; reflexivity.
      - lia.
      - symmetry; exact Hs. }
    subst r; exists (X^^(k-d) *> [0] *> Y *> r0); split.
    + unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add.
      applys_eq H; flia.
    + repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
      eapply segRLs_sideRLs_concat; [apply F_even|constructor].
  - assert (Er: r=X^^(1+k-d) *> [0] *> Y *> r0).
    { apply cut_prefix; [lia|symmetry; exact Hs]. }
    subst r; exists (X^^(1+k-d) *> [0;0] *> r'); split.
    + unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add.
      applys_eq H0; flia.
    + repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
      eapply segRLs_sideRLs_concat; [apply F_odd|exact H].
Qed.

Lemma CutNum_Fs m b n d r:
  CutNum b n d r -> d*2+m<=2+n ->
  exists r', CutNum b (n+m) (d+m) r' /\ sideRLs tm (hf^^m) r r'.
Proof.
  gen n d r; induction m as [|m IH]; intros n d r H Hd.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (CutNum_F _ _ _ _ H ltac:(lia)) as [r1 [HN HR]].
    destruct (IH _ _ _ HN ltac:(lia)) as [r2 [HN' HR']].
    exists r2; split; [applys_eq HN'; flia|].
    change (sideRLs tm (hf++hf^^m) r r2).
    eapply sideRLs_trans; eauto.
Qed.

Definition root (r:side) := 0inf <{{A}} r.

Lemma normal_cycle n r r3:
  sideRLs tm (h^^3) r r3 ->
  root (X^^(3+n) *> [0;0] *> r) -->+
  root (X^^(2+n) *> [0;0] *> r3).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=h) (ls2:=h^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H23) as [r2 [H2 H3]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma normal_end r r3:
  sideRLs tm (h^^3) r r3 ->
  root (X^^2 *> [0;0] *> r) -->+ root (X *> [0] *> X *> r3).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=h) (ls2:=h^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H23) as [r2 [H2 H3]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma normal_odd n r r2:
  sideRLs tm (h^^2) r r2 ->
  root (X^^(2+n) *> [0] *> Y *> r) -->+
  root (X^^(2+n) *> [0;0] *> r2).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H) as [r1 [H1 H2]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2); es; er; finish.
Qed.

Lemma marker_cycle p a r r3:
  sideRLs tm (h^^3) r r3 ->
  root (X^^(1+p) *> [0] *> X^^(4+a) *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+a) *> [0;0] *> r3).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=h) (ls2:=h^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H23) as [r2 [H2 H3]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma Num_normal n b j r:
  Num b j r -> exists r', Num b (j+3+n*3) r' /\
    root (X^^(2+n) *> [0;0] *> r) -->+ root (X *> [0] *> X *> r').
Proof.
  gen j r; induction n as [|n IH]; intros j r H.
  - destruct (Num_add 3 _ _ _ H) as [r' [HN HR]].
    exists r'; split; [applys_eq HN; flia|apply normal_end, HR].
  - destruct (Num_add 3 _ _ _ H) as [r1 [HN HR]].
    destruct (IH _ _ HN) as [r2 [HN' HR']].
    exists r2; split; [applys_eq HN'; flia|].
    eapply progress_trans; [apply normal_cycle, HR|exact HR'].
Qed.

Lemma Num_normal_odd n b j r:
  Num b j r -> exists r', Num b (j+5+n*3) r' /\
    root (X^^(2+n) *> [0] *> Y *> r) -->+ root (X *> [0] *> X *> r').
Proof.
  intro H; destruct (Num_add 2 _ _ _ H) as [r1 [HN HR]].
  destruct (Num_normal n _ _ _ HN) as [r2 [HN' HR']].
  exists r2; split; [applys_eq HN'; flia|].
  eapply progress_trans; [apply normal_odd, HR|exact HR'].
Qed.

Lemma Num_markers m p a b j r:
  Num b j r -> exists r', Num b (j+m*3) r' /\
    root (X^^(1+p) *> [0] *> X^^(1+a+m*3) *> [0;0] *> r) -->*
    root (X^^(1+p+m) *> [0] *> X^^(1+a) *> [0;0] *> r').
Proof.
  gen p j r; induction m as [|m IH]; intros p j r H.
  - exists r; split; [applys_eq H; flia|unfold root; finish].
  - destruct (Num_add 3 _ _ _ H) as [r1 [HN HR]].
    destruct (IH (1+p) _ _ HN) as [r2 [HN' HR']].
    exists r2; split; [applys_eq HN'; flia|].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (marker_cycle p (a+m*3) _ _ HR); flia.
    + applys_eq HR'; flia.
Qed.

Definition pending n (l r:side) :=
  l <* <[0;0;1;1]^^n <* <[0;0;1;0;0;1;1;0;0;1;1] {{B}}> r.

Lemma pending_cycle n l r r3:
  sideRLs tm (hf^^3) r r3 ->
  pending (1+n) l r -->+ pending n l (X *> r3).
Proof.
  intro H; unfold pending.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H23) as [r2 [H2 H3]].
  follow11 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma pending_end l r r3:
  sideRLs tm (hf^^3) r r3 ->
  pending 0 l r -->+ l <{{F}} [1;0] *> Y *> X *> r3.
Proof.
  intro H; unfold pending.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H23) as [r2 [H2 H3]].
  follow11 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma CutNum_prepend b j d k r:
  CutNum b j (d+k) r -> CutNum b j d (X^^k *> r).
Proof. unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; trivial. Qed.

Lemma Num_pending q l b j d r:
  CutNum b j d r -> d*2+q+2<=j ->
  exists r', CutNum b (j+(1+q)*3) (d+(1+q)*2) r' /\
    pending q l r -->+ l <{{F}} [1;0] *> Y *> r'.
Proof.
  gen j d r; induction q as [|q IH]; intros j d r H Hd;
    destruct (CutNum_Fs 3 _ _ _ _ H ltac:(lia)) as [r3 [HN HR]].
  - exists (X *> r3); split; [|apply pending_end, HR].
    applys_eq (CutNum_prepend b (j+3) (d+2) 1 r3); try flia.
    applys_eq HN; flia.
  - assert (HC: CutNum b (j+3) (d+2) (X *> r3)).
    { applys_eq (CutNum_prepend b (j+3) (d+2) 1 r3); try flia.
      applys_eq HN; flia. }
    destruct (IH _ _ _ HC ltac:(lia)) as [r4 [HN' HR']].
    exists r4; split; [applys_eq HN'; flia|].
    eapply progress_trans; [apply pending_cycle, HR|exact HR'].
Qed.

Lemma a3_prepare q r r2:
  sideRLs tm (h^^2) r r2 ->
  root (X^^(1+q) *> [0] *> X^^3 *> [0;0] *> r) -->+
  pending q (0inf <* [1;1]) r2.
Proof.
  intro H; unfold root, pending.
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H) as [r1 [H1 H2]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2); es; er; finish.
Qed.

Lemma a3_finish r r3:
  sideRLs tm (hf^^3) r r3 ->
  0inf <* [1;1] <{{F}} [1;0] *> Y *> r -->+ root (X^^3 *> r3).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H23) as [r2 [H2 H3]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma Num_a3 q b j r:
  Num b j r -> q+2<=j ->
  exists r', CutNum b (j+8+q*3) (2+q*2) r' /\
    root (X^^(1+q) *> [0] *> X^^3 *> [0;0] *> r) -->+ root r'.
Proof.
  intros H Hj; destruct (Num_add 2 _ _ _ H) as [r1 [HN HR]].
  change (CutNum b (j+2) 0 r1) in HN.
  destruct (Num_pending q (0inf <* [1;1]) _ _ _ _ HN ltac:(lia))
    as [r2 [HN' HR']].
  destruct (CutNum_Fs 3 _ _ _ _ HN' ltac:(lia)) as [r3 [HN'' HR'']].
  exists (X^^3 *> r3); split.
  - applys_eq (CutNum_prepend b _ ((1+q)*2) 3 _ HN''); flia.
  - eapply progress_trans; [apply a3_prepare, HR|].
    eapply progress_trans; [exact HR'|apply a3_finish, HR''].
Qed.

Lemma Num_E_even_inv k s:
  Num false (k*2) s ->
  exists r, Num true k r /\ s=X^^(1+k) *> [0;0] *> r.
Proof.
  intro H; destruct (Num_ex true k) as [r Hr]; exists r; split; [exact Hr|].
  eapply Num_unique; [exact H|apply Num_E_even, Hr].
Qed.

Lemma Num_E_odd_inv k s:
  Num false (1+k*2) s ->
  exists r, Num true k r /\ s=X^^(1+k) *> [0] *> Y *> r.
Proof.
  intro H; destruct (Num_ex true k) as [r Hr]; exists r; split; [exact Hr|].
  eapply Num_unique; [exact H|apply Num_E_odd, Hr].
Qed.

Lemma Num_O_even_inv k s:
  Num true (4+k*2) s ->
  exists r, Num false k r /\ s=X^^(3+k) *> [0;0] *> r.
Proof.
  intro H; destruct (Num_ex false k) as [r Hr]; exists r; split; [exact Hr|].
  eapply Num_unique; [exact H|apply Num_O_even, Hr].
Qed.

Lemma Q_normal n s:
  CutNum false (16+n*9) (4+n*2) s ->
  exists r, Num true (20+n*12) r /\ root s -->+ root (X *> [0] *> X *> r).
Proof.
  unfold CutNum; intro H.
  destruct (Nat.Even_Odd_dec n) as [[k Ek]|[k Ek]].
  - assert (HV: Num false ((8+k*9)*2) (X^^(4+n*2) *> s))
      by (applys_eq H; flia).
    destruct (Num_E_even_inv _ _ HV) as [r [HN E]].
    assert (Es: s=X^^(5+k*5) *> [0;0] *> r).
    { rewrite (cut_prefix (1+(8+k*9)) (4+n*2) s ([0;0] *> r));
        [replace (1+(8+k*9)-(4+n*2)) with (5+k*5) by lia; reflexivity|lia|exact E]. }
    destruct (Num_normal (3+k*5) _ _ _ HN) as [r' [HN' HR]].
    exists r'; split; [applys_eq HN'; flia|rewrite Es; exact HR].
  - assert (HV: Num false (1+(12+k*9)*2) (X^^(4+n*2) *> s))
      by (applys_eq H; flia).
    destruct (Num_E_odd_inv _ _ HV) as [r [HN E]].
    assert (Es: s=X^^(7+k*5) *> [0] *> Y *> r).
    { rewrite (cut_prefix (1+(12+k*9)) (4+n*2) s ([0] *> Y *> r));
        [replace (1+(12+k*9)-(4+n*2)) with (7+k*5) by lia; reflexivity|lia|exact E]. }
    destruct (Num_normal_odd (5+k*5) _ _ _ HN) as [r' [HN' HR]].
    exists r'; split; [applys_eq HN'; flia|rewrite Es; exact HR].
Qed.

Lemma Q_finish n s:
  Num true (20+n*12) s ->
  exists r, Num false (17+n*12) r /\
    root (X *> [0] *> X *> s) -->*
    root (X^^(4+n*2) *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  intro H; assert (HV: Num true (4+(8+n*6)*2) s) by (applys_eq H; flia).
  destruct (Num_O_even_inv _ _ HV) as [r [HN E]]; subst s.
  destruct (Num_markers (3+n*2) 0 2 _ _ _ HN) as [r' [HN' HR]].
  exists r'; split; [applys_eq HN'; flia|].
  change (root (X *> [0] *> X^^(12+n*6) *> [0;0] *> r) -->*
    root (X^^(4+n*2) *> [0] *> X^^3 *> [0;0] *> r')).
  applys_eq HR; flia.
Qed.

Lemma Q_step n r:
  Num false (5+n*6) r ->
  exists r', Num false (17+n*12) r' /\
    root (X^^(2+n) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(4+n*2) *> [0] *> X^^3 *> [0;0] *> r').
Proof.
  intro H; destruct (Num_a3 (1+n) _ _ _ H ltac:(lia)) as [r1 [HN HR]].
  assert (HC: CutNum false (16+n*9) (4+n*2) r1) by (applys_eq HN; flia).
  destruct (Q_normal _ _ HC) as [r2 [HN' HR']].
  destruct (Q_finish _ _ HN') as [r3 [HN'' HR'']].
  exists r3; split; [exact HN''|].
  eapply progress_trans; [exact HR|].
  eapply progress_evstep_trans; eassumption.
Qed.

Inductive InLoop : Q*tape -> Prop :=
| in_loop n r: Num false (5+n*6) r ->
    InLoop (root (X^^(2+n) *> [0] *> X^^3 *> [0;0] *> r)).

Lemma loop_progress c: InLoop c -> exists c', InLoop c' /\ c -->+ c'.
Proof.
  intro H; destruct H; destruct (Q_step _ _ H) as [r' [HN HR]].
  eexists; split; [|exact HR].
  applys_eq (in_loop (2+n*2) r'); try flia.
  applys_eq HN; flia.
Qed.

Lemma loop_nonhalt c: InLoop c -> ~halts tm c.
Proof.
  intro H; eapply progress_nonhalt with (P:=InLoop);
    [apply loop_progress|exact H].
Qed.

Definition seed := X^^8 *> [0] *> Y *> X^^4 *> [0] *> Y *>
  X *> [0] *> Y *> X *> [0;0] *> end0.

Lemma seed_num: Num false 15 seed.
Proof. unfold seed; apply (Num_E_odd 7), (Num_O_odd 1), (Num_E_odd 0), Num_O0. Qed.

Lemma init: c0 -->* root (X^^10 *> [0;0] *> seed).
Proof. unfold root, seed; esx. Qed.

Lemma init_first_marker:
  exists r, Num true 42 r /\
    c0 -->* root (X^^8 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct (Num_normal 8 _ _ _ seed_num) as [s [HN HR]].
  destruct (Num_E_even_inv 21 _ HN) as [t [HN' E]]; subst s.
  destruct (Num_markers 7 0 1 _ _ _ HN') as [r [HN'' HR']].
  exists r; split; [exact HN''|].
  follow init; follow100 HR; exact HR'.
Qed.

(* Finite entry: retain the physical cut and the real caller at every
   returning suffix call.  Marker rules reserve the explicitly shown X. *)
Lemma F_to_h r r':
  sideRLs tm hf r r' -> sideRLs tm h r (X *> r').
Proof.
  intro H; econstructor; [|constructor].
  intro l; follow11 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
Qed.

Lemma CutNum_h b n d r:
  CutNum b n d r -> d*2<=1+n ->
  exists r', CutNum b (1+n) d r' /\ sideRLs tm h r r'.
Proof.
  intros H Hd; destruct (CutNum_F _ _ _ _ H Hd) as [s [HN HR]].
  exists (X *> s); split; [|apply F_to_h, HR].
  change (CutNum b (1+n) d (X^^1 *> s)).
  apply CutNum_prepend; applys_eq HN; flia.
Qed.

Lemma a2_prepare q r r1:
  sideRLs tm h r r1 ->
  root (X^^(2+q) *> [0] *> X^^2 *> [0;0] *> r) -->+
  pending q (0inf <* <[1;1;1;0;1;1]) r1.
Proof.
  intro H; unfold root, pending.
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
Qed.

Lemma a2_finish r r3:
  sideRLs tm (hf^^3) r r3 ->
  0inf <* <[1;1;1;0;1;1] <{{F}} [1;0] *> Y *> r -->+
  root (X *> [0;0;0] *> X^^2 *> r3).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^2) H) as [r1 [H1 H23]].
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H23) as [r2 [H2 H3]].
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H3); es; er; finish.
Qed.

Lemma CutNum_hs m b n d r:
  CutNum b n d r -> d*2<=1+n ->
  exists r', CutNum b (n+m) d r' /\ sideRLs tm (h^^m) r r'.
Proof.
  gen n r; induction m as [|m IH]; intros n r H Hd.
  - exists r; split; [applys_eq H; flia|constructor].
  - destruct (CutNum_h _ _ _ _ H Hd) as [r1 [HN HR]].
    destruct (IH _ _ HN ltac:(lia)) as [r2 [HN' HR']].
    exists r2; split; [applys_eq HN'; flia|].
    change (sideRLs tm (h++h^^m) r r2).
    eapply sideRLs_trans; eauto.
Qed.

Lemma CutNum_a2 q b j d r:
  CutNum b j d r -> d*2+q+1<=j ->
  exists r', CutNum b (j+7+q*3) (d+3+q*2) r' /\
    root (X^^(2+q) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X *> [0;0;0] *> r').
Proof.
  intros H Hj; destruct (CutNum_h _ _ _ _ H ltac:(lia)) as [r1 [HN HR]].
  destruct (Num_pending q (0inf <* <[1;1;1;0;1;1]) _ _ _ _ HN ltac:(lia))
    as [r2 [HN' HR']].
  destruct (CutNum_Fs 3 _ _ _ _ HN' ltac:(lia)) as [r3 [HN'' HR'']].
  exists (X^^2 *> r3); split.
  - apply CutNum_prepend; applys_eq HN''; flia.
  - eapply progress_trans; [apply a2_prepare, HR|].
    eapply progress_trans; [exact HR'|apply a2_finish, HR''].
Qed.

Lemma root_000 r:
  root (X *> [0;0;0] *> r) -->+ root (X *> Y *> [0] *> r).
Proof. unfold root; esx. Qed.

Lemma F_marker n r r2:
  sideRLs tm (hf^^2) r r2 ->
  sideRLs tm hf (X^^n *> [0] *> X *> r) (X^^n *> [0] *> X *> r2).
Proof.
  intro H; destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H) as [r1 [H1 H2]].
  econstructor; [|constructor]; intro l.
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H1);
    es; er; follow100 (sideRLs_1 _ _ _ _ _ H2); es; er; finish.
Qed.

Ltac finish_calls H :=
  cbn [lpow app] in H;
  lazymatch type of H with
  | sideRLs _ [] _ _ => inverts H; es; er; finish
  | sideRLs _ (?g :: ?hs) _ _ =>
      let r1:=fresh "r" in let H1:=fresh "HF" in let Hs:=fresh "HFs" in
      destruct (sideRLs_split (ls1:=[g]) (ls2:=hs) H) as [r1 [H1 Hs]];
      es; er; follow100 (sideRLs_1 _ _ _ _ _ H1); finish_calls Hs
  end.

Lemma marker_F_cycle p r r6:
  sideRLs tm (hf^^6) r r6 ->
  root (X^^(1+p) *> [0] *> X *> r) -->+
  root (X^^(2+p) *> [0] *> X *> r6).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma a2_cleanup r r12:
  sideRLs tm (hf^^12) r r12 ->
  root (X *> [0;0;0] *> X *> r) -->+
  root (X^^2 *> [0] *> X *> [0] *> X *> r12).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma F_markers m n r r':
  sideRLs tm (hf^^(m*2)) r r' ->
  sideRLs tm (hf^^m) (X^^n *> [0] *> X *> r) (X^^n *> [0] *> X *> r').
Proof.
  gen r; induction m as [|m IH]; intros r H.
  - inverts H; constructor.
  - replace ((S m)*2) with (2+m*2) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r2 [H2 Hs]].
    change (sideRLs tm (hf++hf^^m)
      (X^^n *> [0] *> X *> r) (X^^n *> [0] *> X *> r')).
    eapply sideRLs_trans; [apply F_marker, H2|apply IH, Hs].
Qed.

Lemma two_marker_cycle p r r12:
  sideRLs tm (hf^^12) r r12 ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X *> r) -->+
  root (X^^(2+p) *> [0] *> X *> [0] *> X *> r12).
Proof. intro H; apply marker_F_cycle; exact (F_markers 6 0 _ _ H). Qed.

Lemma two_markers m p r r':
  sideRLs tm (hf^^(m*12)) r r' ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X *> r) -->*
  root (X^^(1+p+m) *> [0] *> X *> [0] *> X *> r').
Proof.
  gen p r; induction m as [|m IH]; intros p r H.
  - inverts H; replace (1+p+0) with (1+p) by lia; unfold root; finish.
  - replace ((S m)*12) with (12+m*12) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r12 [H12 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + apply two_marker_cycle, H12.
    + applys_eq (IH (1+p) _ Hs); flia.
Qed.

Lemma Num_O_odd_inv k s:
  Num true (5+k*2) s ->
  exists r, Num false k r /\ s=X^^(3+k) *> [0] *> Y *> r.
Proof.
  intro H; destruct (Num_ex false k) as [r Hr]; exists r; split; [exact Hr|].
  eapply Num_unique; [exact H|apply Num_O_odd, Hr].
Qed.

Lemma init_two_markers:
  exists r, Num false 49 r /\
    c0 -->* root (X^^4 *> [0] *> X *> [0] *> X *> [0] *> Y *> r).
Proof.
  destruct init_first_marker as [r [HN HR]].
  destruct (CutNum_a2 6 _ 42 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_O_odd_inv 31 _ HS) as [t [HT ET]].
  assert (Es: s=X^^19 *> [0] *> Y *> t).
  { exact (cut_prefix 34 15 _ _ ltac:(lia) ET). }
  assert (HC: CutNum true 67 16 (X^^18 *> [0] *> Y *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_O_odd 31), HT. }
  destruct (CutNum_Fs 36 _ _ _ _ HC ltac:(lia)) as [u [HU H36]].
  destruct (sideRLs_split (ls1:=hf^^12) (ls2:=hf^^24) H36) as [v [H12 H24]].
  destruct (Num_O_odd_inv 49 _ HU) as [w [HW EW]].
  apply prefix_cancel in EW; subst u.
  exists w; split; [exact HW|].
  follow HR; follow100 HRS; rewrite Es.
  follow100 (a2_cleanup _ _ H12).
  exact (two_markers 2 1 _ _ H24).
Qed.

Lemma c1_prepare p r r1:
  sideRLs tm h r r1 ->
  root (X^^(2+p) *> [0] *> X *> [0] *> X *> [0] *> Y *> r) -->+
  root ([0] *> X^^(2+p) *> [0;0] *> Y *> Y *> r1).
Proof.
  intro H; unfold root.
  es; er; follow100 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
Qed.

Lemma c1_finish p r r4:
  sideRLs tm (hf^^4) r r4 ->
  root ([0] *> X^^(2+p) *> [0;0] *> Y *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> X *> [0] *> X *> [0] *> X *> r4).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_c1 p b j d r:
  CutNum b j d r -> d*2+1<=j ->
  exists r', CutNum b (j+5) (d+3) r' /\
    root (X^^(2+p) *> [0] *> X *> [0] *> X *> [0] *> Y *> r) -->+
    root (X^^(2+p) *> [0;0] *> X *> [0] *> X *> [0] *> r').
Proof.
  intros H Hj; destruct (CutNum_h _ _ _ _ H ltac:(lia)) as [r1 [HN HR]].
  destruct (CutNum_Fs 4 _ _ _ _ HN ltac:(lia)) as [r4 [HN' HR']].
  exists (X *> r4); split.
  - change (CutNum b (j+5) (d+3) (X^^1 *> r4)).
    apply CutNum_prepend; applys_eq HN'; flia.
  - eapply progress_trans; [apply c1_prepare, HR|apply c1_finish, HR'].
Qed.

Lemma init_nested_normal:
  exists r, CutNum false 54 3 r /\
    c0 -->* root (X^^4 *> [0;0] *> X *> [0] *> X *> [0] *> r).
Proof.
  destruct init_two_markers as [r [HN HR]].
  destruct (CutNum_c1 2 _ 49 0 _ HN ltac:(lia)) as [s [HS HRS]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HRS].
Qed.

Lemma normal_calls n r r':
  sideRLs tm (h^^(3+n*3)) r r' ->
  root (X^^(2+n) *> [0;0] *> r) -->+ root (X *> [0] *> X *> r').
Proof.
  gen r; induction n as [|n IH]; intros r H.
  - apply normal_end, H.
  - replace (3+S n*3) with (3+(3+n*3)) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r3 [H3 Hs]].
    eapply progress_trans; [apply normal_cycle, H3|apply IH, Hs].
Qed.

Fixpoint markers (ns:list nat) (r:side) : side :=
  match ns with []=>r | n::ns=>X^^n *> [0] *> X *> markers ns r end.

Lemma F_columns ns m r r':
  sideRLs tm (hf^^(m*2^(length ns))) r r' ->
  sideRLs tm (hf^^m) (markers ns r) (markers ns r').
Proof.
  gen m; induction ns as [|n ns IH]; intros m H.
  - cbn [length Nat.pow] in H; rewrite Nat.mul_1_r in H; exact H.
  - cbn [markers]; apply F_markers, IH.
    applys_eq H; cbn [length Nat.pow]; rewrite Nat.mul_assoc; reflexivity.
Qed.

Lemma h_columns ns m a r r':
  sideRLs tm (hf^^(m*2^(1+length ns))) r r' ->
  sideRLs tm (h^^m) (markers (a::ns) r) (markers ((a+m)::ns) r').
Proof.
  gen a r; induction m as [|m IH]; intros a r H.
  - inverts H; replace (a+0) with a by lia; constructor.
  - change (sideRLs tm (hf^^(2^(1+length ns)+m*2^(1+length ns))) r r') in H.
    rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r1 [H1 Hs]].
    assert (HR: sideRLs tm h (markers (a::ns) r) (markers ((1+a)::ns) r1)).
    { cbn [markers]; apply F_to_h, (F_columns (a::ns) 1).
      cbn [length]; rewrite Nat.mul_1_l; exact H1. }
    change (sideRLs tm (h++h^^m) (markers (a::ns) r) (markers ((a+S m)::ns) r')).
    eapply sideRLs_trans; [exact HR|applys_eq (IH (1+a) _ Hs); flia].
Qed.

Lemma init_three_markers:
  exists r, Num true 45 r /\
    c0 -->* root (X *> [0] *> X^^11 *> [0] *> X *> [0] *> X^^7 *> [0;0] *> r).
Proof.
  destruct init_nested_normal as [r [HN HR]].
  destruct (Num_E_even_inv 27 _ HN) as [t [HT ET]].
  assert (Er: r=X^^25 *> [0;0] *> t).
  { exact (cut_prefix 28 3 _ _ ltac:(lia) ET). }
  assert (HC: CutNum false 54 4 (X^^24 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 27), HT. }
  destruct (CutNum_Fs 36 _ _ _ _ HC ltac:(lia)) as [s [HS H36]].
  destruct (Num_E_even_inv 45 _ HS) as [u [HU EU]].
  assert (Es: s=X^^6 *> [0;0] *> u).
  { exact (cut_prefix 46 40 _ _ ltac:(lia) EU). }
  exists u; split; [exact HU|].
  follow HR; rewrite Er.
  follow100 (normal_calls 2 _ _ (h_columns [0]%nat 9 1 _ _ H36)).
  rewrite Es; unfold root; finish.
Qed.

(* Mixed-column batches retain the separator and the complete child.
   A final even zero-run is an output, never an extra licensed call. *)
Definition sep (e:bool) : list Sym := if e then [0]++Y else [0;0].

Lemma digit_odd_all n:
  segRLs tm h h (X^^n++[0]++Y) (X^^(1+n)++[0;0]).
Proof.
  eapply @segRLs_S' with (w2:=[1;1]++[1;1;0;0]^^(1+n))
    (w3:=X^^(1+n)++[0;0]).
  - intros l r; esx.
  - intros l r; esx.
  - constructor.
Qed.

Lemma F_pair n e:
  segRLs tm (hf^^2) h (X^^(1+n)++sep e) (X^^n++sep e).
Proof.
  destruct e; unfold sep.
  - change (segRLs tm (hf++hf) (h++[]) (X^^(1+n)++[0]++Y) (X^^n++[0]++Y)).
    eapply segRLs_trans; [apply F_odd|apply F_even].
  - change (segRLs tm (hf++hf) ([]++h) (X^^(1+n)++[0;0]) (X^^n++[0;0])).
    eapply segRLs_trans; [apply F_even|apply F_odd].
Qed.

Lemma F_pairs m n e:
  segRLs tm (hf^^(m*2)) (h^^m) (X^^(n+m)++sep e) (X^^n++sep e).
Proof.
  induction m as [|m IH].
  - replace (n+0) with n by lia; constructor.
  - replace (S m*2) with (2+m*2) by lia; rewrite lpow_add.
    change (segRLs tm (hf^^2++hf^^(m*2)) (h++h^^m) (X^^(n+S m)++sep e) (X^^n++sep e)).
    eapply segRLs_trans; [applys_eq (F_pair (n+m) e); flia|exact IH].
Qed.

Lemma h_pair_odd n:
  segRLs tm (h^^2) h (X^^n++[0]++Y) (X^^(1+n)++[0]++Y).
Proof.
  change (segRLs tm (h++h) (h++[]) (X^^n++[0]++Y) (X^^(1+n)++[0]++Y)).
  eapply segRLs_trans; [apply digit_odd_all|apply digit_even].
Qed.

Lemma h_pairs_odd m n:
  segRLs tm (h^^(m*2)) (h^^m) (X^^n++[0]++Y) (X^^(n+m)++[0]++Y).
Proof.
  gen n; induction m as [|m IH]; intro n.
  - replace (n+0) with n by lia; constructor.
  - replace (S m*2) with (2+m*2) by lia; rewrite lpow_add.
    change (segRLs tm (h^^2++h^^(m*2)) (h++h^^m) (X^^n++[0]++Y) (X^^(n+S m)++[0]++Y)).
    eapply segRLs_trans; [apply h_pair_odd|applys_eq (IH (1+n)); flia].
Qed.

Lemma d7_prepare p b r r4:
  sideRLs tm (h^^4) r r4 ->
  root (X^^(1+p) *> [0] *> X^^(2+b) *> [0] *> X *> [0] *> X^^7 *> [0;0] *> r) -->+
  root ([0] *> X^^(1+p) *> [0] *> X^^(2+b) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r4).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma d7_finish p b r r5:
  sideRLs tm (hf^^5) r r5 ->
  root ([0] *> X^^(1+p) *> [0] *> X^^(2+b) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0;0;0] *> Y *> X^^4 *> r5).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_d7 p a b j d r:
  CutNum b j d r -> d*2<=j+1 ->
  exists r', CutNum b (j+9) (d+1) r' /\
    root (X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X *> [0] *> X^^7 *> [0;0] *> r) -->+
    root (X^^(2+p) *> [0] *> X^^(1+a) *> [0;0;0] *> Y *> r').
Proof.
  intros H Hd; destruct (CutNum_hs 4 _ _ _ _ H ltac:(lia)) as [r4 [HN HR]].
  destruct (CutNum_Fs 5 _ _ _ _ HN ltac:(lia)) as [r5 [HN' HR']].
  exists (X^^4 *> r5); split.
  - apply CutNum_prepend; applys_eq HN'; flia.
  - eapply progress_trans; [apply d7_prepare, HR|apply d7_finish, HR'].
Qed.

Lemma init_mixed_columns:
  exists r, CutNum true 54 1 r /\
    c0 -->* root (X^^2 *> [0] *> X^^10 *> [0;0;0] *> Y *> r).
Proof.
  destruct init_three_markers as [r [HN HR]].
  destruct (CutNum_d7 0 9 _ 45 0 _ HN ltac:(lia)) as [s [HS HRS]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HRS].
Qed.
Lemma h_odd_batch m n:
  segRLs tm (h^^(m*2+1)) (h^^(m+1))
    (X^^n++[0]++Y) (X^^(1+n+m)++[0;0]).
Proof.
  rewrite (lpow_add _ (m*2) 1 h), (lpow_add _ m 1 h).
  eapply segRLs_trans; [apply h_pairs_odd|].
  applys_eq (digit_odd_all (n+m)); flia.
Qed.

Lemma marker_calls m p r r':
  sideRLs tm (hf^^(m*6)) r r' ->
  root (X^^(1+p) *> [0] *> X *> r) -->*
  root (X^^(1+p+m) *> [0] *> X *> r').
Proof.
  gen p r; induction m as [|m IH]; intros p r H.
  - inverts H; replace (1+p+0) with (1+p) by lia; unfold root; finish.
  - replace ((S m)*6) with (6+m*6) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r6 [H6 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + apply marker_F_cycle, H6.
    + applys_eq (IH (1+p) _ Hs); flia.
Qed.

Lemma init_double_digit:
  exists r, CutNum true 59 1 r /\
    c0 -->* root (X^^5 *> [0] *> X *> [0;0] *> X^^5 *> [0;0] *> r).
Proof.
  destruct init_mixed_columns as [r [HN HR]].
  destruct (CutNum_hs 5 _ _ _ _ HN ltac:(lia)) as [s [HS H5]].
  assert (H9: sideRLs tm (h^^9) ([0] *> Y *> r) (X^^5 *> [0;0] *> s)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    eapply segRLs_sideRLs_concat; [exact (h_odd_batch 4 0)|exact H5]. }
  assert (H18: sideRLs tm (hf^^18)
    (X^^9 *> [0;0;0] *> Y *> r) ([0;0] *> X^^5 *> [0;0] *> s)).
  { change (sideRLs tm (hf^^18)
      ((X^^9++sep false) *> ([0] *> Y *> r))
      ((X^^0++sep false) *> (X^^5 *> [0;0] *> s))).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 9 0 false)|exact H9]. }
  exists s; split; [exact HS|].
  follow HR; exact (marker_calls 3 1 _ _ H18).
Qed.

Lemma pending_digit_pair n a l r s:
  sideRLs tm (h^^3) r s ->
  pending (2+n) l (X^^(2+a) *> [0;0] *> r) -->+
  pending n l (X^^(1+a) *> [0;0] *> s).
Proof. intro H; unfold pending; finish_calls H. Qed.

Lemma pending_digit_pairs k n a l r s:
  sideRLs tm (h^^(k*3)) r s ->
  pending (n+k*2) l (X^^(2+a+k) *> [0;0] *> r) -->*
  pending n l (X^^(2+a) *> [0;0] *> s).
Proof.
  gen r; induction k as [|k IH]; intros r H.
  - inverts H; replace (2+a+0) with (2+a) by lia.
    replace (n+0*2) with n by lia; unfold pending; finish.
  - replace (S k*3) with (3+k*3) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r3 [H3 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (pending_digit_pair (n+k*2) (1+a+k) l _ _ H3); flia.
    + applys_eq (IH _ Hs); flia.
Qed.

Lemma pending_digit_end a l r s:
  sideRLs tm h r s ->
  pending 0 l (X^^(2+a) *> [0;0] *> r) -->+
  l <{{F}} [1;0] *> Y *> X^^(1+a) *> [0] *> Y *> s.
Proof. intro H; unfold pending; finish_calls H. Qed.

Lemma a1_prepare q r:
  root (X^^(1+q) *> [0] *> X *> [0;0] *> r) -->+
  pending q (0inf <* [1]) r.
Proof. unfold root, pending; esx. Qed.

Lemma a1_digit_finish a r s:
  sideRLs tm h r s ->
  0inf <* [1] <{{F}} [1;0] *> Y *> X^^(1+a) *> [0] *> Y *> r -->+
  root (X *> [0] *> X^^(3+a) *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma a1_double_digit k a r s:
  sideRLs tm (h^^(k*3+2)) r s ->
  root (X^^(1+k*2) *> [0] *> X *> [0;0] *> X^^(2+a+k) *> [0;0] *> r) -->+
  root (X *> [0] *> X^^(3+a) *> [0;0] *> s).
Proof.
  intro H; rewrite (lpow_add _ (k*3) 2 h) in H.
  destruct (sideRLs_split H) as [r0 [Hk H2]].
  destruct (sideRLs_split (ls1:=h) (ls2:=h) H2) as [r1 [H1 Hs]].
  eapply progress_trans; [apply a1_prepare|].
  eapply evstep_progress_trans; [exact (pending_digit_pairs k 0 a _ _ _ Hk)|].
  eapply progress_trans; [apply pending_digit_end, H1|apply a1_digit_finish, Hs].
Qed.

Lemma init_recovered_digit:
  exists r, CutNum true 67 1 r /\
    c0 -->* root (X *> [0] *> X^^4 *> [0;0] *> r).
Proof.
  destruct init_double_digit as [r [HN HR]].
  destruct (CutNum_hs 8 _ _ _ _ HN ltac:(lia)) as [s [HS H8]].
  exists s; split; [exact HS|].
  follow HR; apply progress_evstep; exact (a1_double_digit 2 1 _ _ H8).
Qed.

Lemma init_a1_source:
  exists r, CutNum true 70 1 r /\
    c0 -->* root (X^^2 *> [0] *> X *> [0;0] *> r).
Proof.
  destruct init_recovered_digit as [r [HN HR]].
  destruct (CutNum_hs 3 _ _ _ _ HN ltac:(lia)) as [s [HS H3]].
  assert (HF: sideRLs tm (hf^^6) (X^^3 *> [0;0] *> r) ([0;0] *> s)).
  { change (sideRLs tm (hf^^6) ((X^^3++sep false) *> r) ((X^^0++sep false) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 3 0 false)|exact H3]. }
  exists s; split; [exact HS|].
  follow HR; exact (marker_calls 1 0 _ _ HF).
Qed.

Lemma a1_even_finish a r:
  0inf <* [1] <{{F}} [1;0] *> Y *> X^^a *> [0;0] *> r -->+
  root (X *> [0] *> X^^(1+a) *> [0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma init_odd_digit:
  exists r, Num false 36 r /\
    c0 -->* root (X *> [0] *> X^^35 *> [0] *> Y *> r).
Proof.
  destruct init_a1_source as [r [HN HR]].
  destruct (Num_pending 1 (0inf <* [1]) _ _ _ _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_O_even_inv 36 _ HS) as [t [HT ET]].
  assert (Es: s=X^^34 *> [0;0] *> t).
  { exact (cut_prefix 39 5 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 (a1_prepare 1 r); follow100 HRS.
  rewrite Es; apply progress_evstep, a1_even_finish.
Qed.

Lemma init_E69:
  exists r, Num false 69 r /\
    c0 -->* root (X^^12 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_odd_digit as [r [HN HR]].
  destruct (Num_add 33 _ _ _ HN) as [s [HS H33]].
  assert (HF: sideRLs tm (hf^^66)
    (X^^34 *> [0] *> Y *> r) (X *> [0] *> Y *> s)).
  { change (sideRLs tm (hf^^66) ((X^^34++sep true) *> r) ((X^^1++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 33 1 true)|exact H33]. }
  exists s; split; [exact HS|].
  follow HR; exact (marker_calls 11 0 _ _ HF).
Qed.

(* Six-call marker birth, stopped before its unsupported last bare
   call.  The real T2 caller supplies the separate even-zero exit. *)
Notation Dr := [1;1;0;0].
Notation T2r := [1;1;0;0;1;1;0;0;1;1;0;0;1].

Definition birth a b (r:side) :=
  0inf <* [1] <* Dr^^a <* [1;1] <* Dr^^b <* T2r {{B}}> r.

Lemma birth_prepare p r r3:
  sideRLs tm (hf^^3) r r3 ->
  root (X^^(1+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  birth (1+p) 1 r3.
Proof. intro H; unfold root, birth; finish_calls H. Qed.

Lemma birth_cycle a b r r6:
  sideRLs tm (hf^^6) r r6 ->
  birth (2+a) (1+b) r -->+ birth (1+a) (4+b) r6.
Proof.
  intro H; unfold birth.
  cbn [lpow app] in H.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^5) H) as [r1 [H1 Hs]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls Hs.
Qed.

Lemma birth_cycles k a b r s:
  sideRLs tm (hf^^(k*6)) r s ->
  birth (1+a+k) (1+b) r -->* birth (1+a) (1+b+k*3) s.
Proof.
  gen b r; induction k as [|k IH]; intros b r H.
  - inverts H; replace (1+a+0) with (1+a) by lia.
    replace (1+b+0*3) with (1+b) by lia; unfold birth; finish.
  - replace (S k*6) with (6+k*6) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r6 [H6 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (birth_cycle (a+k) b _ _ H6); flia.
    + applys_eq (IH (3+b) _ Hs); flia.
Qed.

Lemma birth_end b r r2:
  sideRLs tm (hf^^2) r r2 ->
  birth 1 (1+b) r -->+
  0inf <* [1;1;1] <* Dr^^(3+b) <* T2r {{B}}> r2.
Proof.
  intro H; unfold birth.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H) as [r1 [H1 H2]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H2.
Qed.

Lemma birth_zero b r:
  0inf <* [1;1;1] <* Dr^^b <* T2r {{B}}> [0;0] *> r -->+
  root (X *> [0] *> X^^b *> [0] *> X^^2 *> [0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma birth_short p r s:
  sideRLs tm (hf^^(5+p*6)) r ([0;0] *> s) ->
  root (X^^(1+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root (X *> [0] *> X^^(3+p*3) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro H; replace (5+p*6) with (3+(p*6+2)) in H by lia.
  rewrite (lpow_add _ 3 (p*6+2) hf) in H.
  destruct (sideRLs_split H) as [r3 [H3 Hs]].
  rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm H2]].
  eapply progress_trans; [apply birth_prepare, H3|].
  eapply evstep_progress_trans; [exact (birth_cycles p 0 0 _ _ Hm)|].
  eapply progress_trans; [apply birth_end, H2|apply birth_zero].
Qed.

Lemma Num_birth_short p r:
  Num false (3+p*6) r ->
  exists s, Num true (4+p*6) s /\
    root (X^^(1+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X *> [0] *> X^^(3+p*3) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro H; destruct (CutNum_Fs (5+p*6) false (3+p*6) 0 _ H ltac:(lia))
    as [s [HS HF]].
  destruct (Num_E_even_inv (4+p*6) (X^^(5+p*6) *> s)
    ltac:(applys_eq HS; flia)) as [t [HT ET]].
  replace (1+(4+p*6)) with (5+p*6) in ET by lia.
  apply prefix_cancel in ET; subst s.
  exists t; split; [exact HT|apply birth_short, HF].
Qed.

Lemma init_O70:
  exists r, Num true 70 r /\
    c0 -->* root (X *> [0] *> X^^36 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_E69 as [r [HN HR]].
  destruct (Num_birth_short 11 _ HN) as [s [HS HRS]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HRS].
Qed.

Lemma odd2_pair p b r r6:
  sideRLs tm (hf^^6) r r6 ->
  root (X^^(1+p) *> [0] *> X^^(3+b) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0;0] *> X^^2 *> [0] *> X^^3 *> r6).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_odd2_pair p a b j d r:
  CutNum b j d r -> d*2+4<=j ->
  exists s, CutNum b (j+6) (d+3) s /\
    root (X^^(1+p) *> [0] *> X^^(3+a) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(2+p) *> [0] *> X^^(1+a) *> [0;0] *> X^^2 *> [0] *> s).
Proof.
  intros H Hd; destruct (CutNum_Fs 6 _ _ _ _ H ltac:(lia)) as [r6 [HN HR]].
  exists (X^^3 *> r6); split.
  - apply CutNum_prepend; applys_eq HN; flia.
  - apply odd2_pair, HR.
Qed.

Lemma init_even_marked:
  exists r, CutNum true 76 3 r /\
    c0 -->* root (X^^2 *> [0] *> X^^34 *> [0;0] *> X^^2 *> [0] *> r).
Proof.
  destruct init_O70 as [r [HN HR]].
  destruct (CutNum_odd2_pair 0 33 true 70 0 _ HN ltac:(lia)) as [s [HS HRS]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HRS].
Qed.

Lemma marker_hcalls m p a r s:
  sideRLs tm (h^^(m*3)) r s ->
  root (X^^(1+p) *> [0] *> X^^(1+a+m*3) *> [0;0] *> r) -->*
  root (X^^(1+p+m) *> [0] *> X^^(1+a) *> [0;0] *> s).
Proof.
  gen p r; induction m as [|m IH]; intros p r H.
  - inverts H; replace (1+p+0) with (1+p) by lia.
    replace (1+a+0*3) with (1+a) by lia; unfold root; finish.
  - replace (S m*3) with (3+m*3) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r3 [H3 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (marker_cycle p (a+m*3) _ _ H3); flia.
    + applys_eq (IH (1+p) _ Hs); flia.
Qed.

Lemma init_marked_a1:
  exists r, Num false 69 r /\
    c0 -->* root (X^^13 *> [0] *> X *> [0;0] *> X^^35 *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_even_marked as [r [HN HR]].
  destruct (Num_O_even_inv 36 _ HN) as [t [HT ET]].
  assert (Er: r=X^^36 *> [0;0] *> t).
  { exact (cut_prefix 39 3 _ _ ltac:(lia) ET). }
  assert (HC: CutNum true 76 4 (X^^35 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_O_even 36), HT. }
  destruct (CutNum_Fs 66 _ _ _ _ HC ltac:(lia)) as [s [HS H66]].
  destruct (Num_O_even_inv 69 _ HS) as [u [HU EU]].
  assert (Es: s=X^^2 *> [0;0] *> u).
  { exact (cut_prefix 72 70 _ _ ltac:(lia) EU). }
  exists u; split; [exact HU|].
  follow HR; rewrite Er.
  follow (marker_hcalls 11 1 0 _ _ (h_columns [] 33 2 _ _ H66)).
  rewrite Es; unfold root; finish.
Qed.

Notation Lr := [1;1;0;0;1;1;0;0;1;1;0].

Lemma pending_marker_prepare q b l r r2:
  sideRLs tm (h^^2) r r2 ->
  pending q l (X^^(1+b) *> [0] *> X^^3 *> [0;0] *> r) -->+
  pending b (l <* Dr^^q <* Lr) r2.
Proof. intro H; unfold pending; finish_calls H. Qed.

Lemma marked_F_finish l r r9:
  sideRLs tm (hf^^9) r r9 ->
  l <* Lr <{{F}} [1;0] *> Y *> r -->+
  l <{{A}} [0;0] *> X^^4 *> r9.
Proof. intro H; finish_calls H. Qed.

Lemma marked_root_cleanup q r:
  0inf <* [1] <* Dr^^q <{{A}} r -->+
  root ([0] *> X^^q *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_marked_a1 q a b j d r:
  CutNum b j d r -> d*2+a+6<=j ->
  exists s, CutNum b (j+14+a*3) (d+7+a*2) s /\
    root (X^^(1+q) *> [0] *> X *> [0;0] *> X^^(1+a) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root ([0] *> X^^q *> [0;0] *> s).
Proof.
  intros H Hd; destruct (CutNum_hs 2 _ _ _ _ H ltac:(lia)) as [r2 [HN H2]].
  destruct (Num_pending a (0inf <* [1] <* Dr^^q <* Lr) _ _ _ _ HN ltac:(lia))
    as [rm [HM HP]].
  destruct (CutNum_Fs 9 _ _ _ _ HM ltac:(lia)) as [r9 [HS H9]].
  exists (X^^4 *> r9); split.
  - apply CutNum_prepend; applys_eq HS; flia.
  - eapply progress_trans; [apply a1_prepare|].
    eapply progress_trans; [apply pending_marker_prepare, H2|].
    eapply progress_trans; [exact HP|].
    eapply progress_trans; [apply marked_F_finish, H9|apply marked_root_cleanup].
Qed.

Lemma init_leading_zero:
  exists r, Num true 92 r /\
    c0 -->* root ([0] *> X^^12 *> [0;0] *> X^^18 *> [0] *> Y *> r).
Proof.
  destruct init_marked_a1 as [r [HN HR]].
  destruct (CutNum_marked_a1 12 34 false 69 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_E_odd_inv 92 _ HS) as [t [HT ET]].
  assert (Es: s=X^^18 *> [0] *> Y *> t).
  { exact (cut_prefix 93 75 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 HRS; rewrite Es; unfold root; finish.
Qed.

Lemma leading_zero_even q r s:
  sideRLs tm h r s ->
  root ([0] *> X^^(2+q) *> [0;0] *> r) -->+
  root (X^^(2+q) *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_double_even:
  exists r, Num true 93 r /\
    c0 -->* root (X^^12 *> [0;0] *> X^^19 *> [0;0] *> r).
Proof.
  destruct init_leading_zero as [r [HN HR]].
  assert (HC: CutNum false 185 75 (X^^18 *> [0] *> Y *> r)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add;
    apply (Num_E_odd 92), HN. }
  destruct (CutNum_hs 1 _ _ _ _ HC ltac:(lia)) as [s [HS H1]].
  destruct (Num_E_even_inv 93 _ HS) as [t [HT ET]].
  assert (Es: s=X^^19 *> [0;0] *> t).
  { exact (cut_prefix 94 75 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 (leading_zero_even 10 _ _ H1).
  rewrite Es; unfold root; finish.
Qed.

(* Odd short columns create Y markers; pending batches keep their
   true J caller until all returning signals have been discharged. *)
Lemma init_odd_marked:
  exists r, Num true 142 r /\
    c0 -->* root (X^^12 *> [0] *> X^^3 *> [0] *> Y *> r).
Proof.
  destruct init_double_even as [r [HN HR]].
  assert (HC: CutNum false 186 75 (X^^19 *> [0;0] *> r)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add;
    apply (Num_E_even 93), HN. }
  destruct (CutNum_hs 33 _ _ _ _ HC ltac:(lia)) as [s [HS H33]].
  destruct (CutNum_Fs 66 _ _ _ _ HS ltac:(lia)) as [t [HT H66]].
  destruct (Num_E_odd_inv 142 _ HT) as [u [HU EU]].
  assert (Et: t=X^^2 *> [0] *> Y *> u).
  { exact (cut_prefix 143 141 _ _ ltac:(lia) EU). }
  exists u; split; [exact HU|].
  follow HR; follow100 (normal_calls 10 _ _ H33).
  follow (marker_calls 11 0 _ _ H66); rewrite Et; unfold root; finish.
Qed.

Lemma odd_three p r s:
  sideRLs tm (h^^3) r s ->
  root (X^^(1+p) *> [0] *> X^^3 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma Y_h r s:
  sideRLs tm (hf^^2) r s ->
  sideRLs tm h (Y *> r) (X *> [0] *> X *> s).
Proof.
  intro H; econstructor; [|constructor]; intro l; finish_calls H.
Qed.

Lemma Y_hs m r s:
  sideRLs tm (hf^^(2+m*2)) r s ->
  sideRLs tm (h^^(1+m)) (Y *> r) (X^^(1+m) *> [0] *> X *> s).
Proof.
  intro H; rewrite lpow_add in H.
  destruct (sideRLs_split H) as [r2 [H2 Hs]].
  change (sideRLs tm (h++h^^m) (Y *> r) (markers [1+m]%nat s)).
  eapply sideRLs_trans; [apply Y_h,H2|].
  apply (h_columns [] m 1); applys_eq Hs; flia.
Qed.

Lemma init_Y_source:
  exists r, Num true 145 r /\
    c0 -->* root (X^^13 *> [0;0] *> Y *> r).
Proof.
  destruct init_odd_marked as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, (odd_three 11), H3].
Qed.

Lemma init_large_marked:
  exists r, Num false 142 r /\
    c0 -->* root (X^^7 *> [0] *> X^^37 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_Y_source as [r [HN HR]].
  destruct (CutNum_Fs 72 true 145 0 _ HN ltac:(lia)) as [s [HS H72]].
  destruct (Num_O_odd_inv 106 _ HS) as [t [HT ET]].
  assert (Es: s=X^^37 *> [0] *> Y *> t).
  { exact (cut_prefix 109 72 _ _ ltac:(lia) ET). }
  destruct (Num_add 36 _ _ _ HT) as [u [HU H36]].
  assert (HF: sideRLs tm (hf^^72) s (X *> [0] *> Y *> u)).
  { rewrite Es; change (sideRLs tm (hf^^72)
      ((X^^37++sep true) *> t) ((X^^1++sep true) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 36 1 true)|exact H36]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (normal_calls 11 _ _ (Y_hs 35 _ _ H72)).
  follow (marker_calls 6 0 _ _ (F_markers 36 36 _ _ HF)).
  unfold root; finish.
Qed.

Lemma init_nested_a2:
  exists r, Num true 107 r /\
    c0 -->* root (X^^19 *> [0] *> X^^2 *> [0;0] *> X^^35 *> [0] *> X^^39 *> [0;0] *> r).
Proof.
  destruct init_large_marked as [r [HN HR]].
  destruct (CutNum_odd2_pair 6 34 false 142 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_E_even_inv 74 _ HS) as [t [HT ET]].
  assert (Es: s=X^^72 *> [0;0] *> t).
  { exact (cut_prefix 75 3 _ _ ltac:(lia) ET). }
  assert (HC: CutNum false 148 4 (X^^71 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 74), HT. }
  destruct (CutNum_Fs 66 _ _ _ _ HC ltac:(lia)) as [u [HU H66]].
  destruct (Num_E_even_inv 107 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^38 *> [0;0] *> v).
  { exact (cut_prefix 108 70 _ _ ltac:(lia) EV). }
  exists v; split; [exact HV|].
  follow HR; follow100 HRS; rewrite Es.
  follow (marker_hcalls 11 7 1 _ _ (h_columns [] 33 2 _ _ H66)).
  rewrite Eu; unfold root; finish.
Qed.

Lemma pending_marker_cycle n b a l r s:
  sideRLs tm (h^^3) r s ->
  pending (1+n) l (X^^(1+b) *> [0] *> X^^(4+a) *> [0;0] *> r) -->+
  pending n l (X^^(2+b) *> [0] *> X^^(1+a) *> [0;0] *> s).
Proof.
  intro H.
  assert (HF: sideRLs tm (hf^^6) (X^^(3+a) *> [0;0] *> r) (X^^a *> [0;0] *> s)).
  { repeat rewrite <-Str_app_assoc; eapply segRLs_sideRLs_concat;
      [applys_eq (F_pairs 3 a false); flia|exact H]. }
  applys_eq (pending_cycle n l _ _ (F_markers 3 (1+b) _ _ HF)); flia.
Qed.

Lemma pending_marker_cycles k n b a l r s:
  sideRLs tm (h^^(k*3)) r s ->
  pending (n+k) l (X^^(1+b) *> [0] *> X^^(1+a+k*3) *> [0;0] *> r) -->*
  pending n l (X^^(1+b+k) *> [0] *> X^^(1+a) *> [0;0] *> s).
Proof.
  gen b r; induction k as [|k IH]; intros b r H.
  - inverts H; replace (n+0) with n by lia; replace (1+a+0*3) with (1+a) by lia;
      replace (1+b+0) with (1+b) by lia; unfold pending; finish.
  - replace (S k*3) with (3+k*3) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r3 [H3 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (pending_marker_cycle (n+k) b (a+k*3) l _ _ H3); flia.
    + applys_eq (IH (1+b) _ Hs); flia.
Qed.

Lemma init_nested_pending:
  exists r, Num true 144 r /\
    c0 -->* pending 5 (0inf <* <[1;1;1;0;1;1])
      (X^^48 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_nested_a2 as [r [HN HR]].
  assert (HC: CutNum false 214 70 (X^^38 *> [0;0] *> r)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 107), HN. }
  destruct (CutNum_Fs 2 _ _ _ _ HC ltac:(lia)) as [s [HS H2]].
  destruct (Num_E_even_inv 108 _ HS) as [t [HT ET]].
  assert (Es: s=X^^37 *> [0;0] *> t).
  { exact (cut_prefix 109 72 _ _ ltac:(lia) ET). }
  destruct (Num_add 36 _ _ _ HT) as [u [HU H36]].
  exists u; split; [exact HU|].
  follow HR; follow100 (a2_prepare 17 _ _ (h_columns [] 1 35 _ _ H2)).
  rewrite Es; exact (pending_marker_cycles 12 5 35 1 _ _ _ H36).
Qed.

Notation Jr := [1;1;0;0;1;1;0;1;1;1;0].

Lemma pending_marker_short q b l r s:
  sideRLs tm h r s ->
  pending q l (X^^(1+b) *> [0] *> X^^2 *> [0;0] *> r) -->+
  pending b (l <* Dr^^q <* Jr) s.
Proof. intro H; unfold pending; finish_calls H. Qed.

Lemma marked_J_finish l r s:
  sideRLs tm (hf^^6) r s ->
  l <* Dr <* Jr <{{F}} [1;0] *> Y *> r -->+
  l <{{A}} X *> Y *> [0] *> X^^3 *> s.
Proof. intro H; finish_calls H. Qed.

Lemma J_root_cleanup q r s:
  sideRLs tm (hf^^4) r s ->
  0inf <* <[1;1;1;0;1;1] <* Dr^^q <{{A}} X *> Y *> [0] *> X^^3 *> r -->+
  root (X^^(3+q) *> [0] *> X *> [0] *> X^^3 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma marked_J_root q r s:
  sideRLs tm (hf^^10) r s ->
  0inf <* <[1;1;1;0;1;1] <* Dr^^(1+q) <* Jr <{{F}} [1;0] *> Y *> r -->+
  root (X^^(3+q) *> [0] *> X *> [0] *> X^^3 *> s).
Proof.
  intro H; destruct (sideRLs_split (ls1:=hf^^6) (ls2:=hf^^4) H) as [r6 [H6 H4]].
  eapply progress_trans; [|apply J_root_cleanup,H4].
  applys_eq (marked_J_finish (0inf <* <[1;1;1;0;1;1] <* Dr^^q) _ _ H6); flia.
Qed.

Lemma init_after_J:
  exists r, Num false 147 r /\
    c0 -->* root (X^^7 *> [0] *> X *> [0] *> X^^47 *> [0] *> Y *> r).
Proof.
  destruct init_nested_pending as [r [HN HR]].
  destruct (Num_add 1 _ _ _ HN) as [s [HS H1]].
  destruct (Num_pending 47 (0inf <* <[1;1;1;0;1;1] <* Dr^^5 <* Jr)
    true 145 0 _ HS ltac:(lia)) as [t [HT HP]].
  destruct (CutNum_Fs 10 _ _ _ _ HT ltac:(lia)) as [u [HU H10]].
  destruct (Num_O_odd_inv 147 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^44 *> [0] *> Y *> v).
  { exact (cut_prefix 150 106 _ _ ltac:(lia) EV). }
  exists v; split; [exact HV|].
  follow HR; follow100 (pending_marker_short 5 47 (0inf <* <[1;1;1;0;1;1]) _ _ H1).
  follow100 HP; follow100 (marked_J_root 4 _ _ H10).
  rewrite Eu; unfold root; finish.
Qed.

Lemma init_two_marker_odd5:
  exists r, Num false 189 r /\
    c0 -->* root (X^^14 *> [0] *> X *> [0] *> X^^5 *> [0] *> Y *> r).
Proof.
  destruct init_after_J as [r [HN HR]].
  destruct (Num_add 42 _ _ _ HN) as [s [HS H42]].
  assert (HF: sideRLs tm (hf^^84)
    (X^^46 *> [0] *> Y *> r) (X^^4 *> [0] *> Y *> s)).
  { change (sideRLs tm (hf^^84)
      ((X^^46++sep true) *> r) ((X^^4++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 42 4 true)|exact H42]. }
  exists s; split; [exact HS|].
  follow HR; follow (two_markers 7 6 _ _ HF); unfold root; finish.
Qed.

Lemma odd_five_general p b r s:
  sideRLs tm (h^^5) r s ->
  root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^5 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> X^^b *> [0] *> Y *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma odd_five p r s:
  sideRLs tm (h^^5) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^5 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> Y *> Y *> s).
Proof. exact (odd_five_general p 0 r s). Qed.

Lemma YY_h r s:
  sideRLs tm (hf^^4) r s ->
  sideRLs tm h (Y *> Y *> r) (markers [1;0]%nat s).
Proof.
  intro H; cbn [markers]; econstructor; [|constructor]; intro l;
    finish_calls H.
Qed.

Lemma init_three_column:
  exists r, Num true 193 r /\
    c0 -->* root (X^^2 *> [0] *> X^^43 *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_two_marker_odd5 as [r [HN HR]].
  destruct (Num_add 5 _ _ _ HN) as [r5 [HN5 H5]].
  destruct (CutNum_Fs 168 false 194 0 _ HN5 ltac:(lia)) as [s [HS H168]].
  destruct (sideRLs_split (ls1:=hf^^4) (ls2:=hf^^164) H168) as [r4 [H4 H164]].
  assert (H42: sideRLs tm (h^^42) (Y *> Y *> r5) (markers [42;0]%nat s)).
  { change (sideRLs tm (h++h^^41) (Y *> Y *> r5) (markers [42;0]%nat s)).
    eapply sideRLs_trans; [apply YY_h,H4|exact (h_columns [0]%nat 41 1 _ _ H164)]. }
  destruct (CutNum_Fs 24 _ _ _ _ HS ltac:(lia)) as [t [HT H24]].
  destruct (Num_E_even_inv 193 _ HT) as [u [HU EU]].
  assert (Et: t=X^^2 *> [0;0] *> u).
  { exact (cut_prefix 194 192 _ _ ltac:(lia) EU). }
  exists u; split; [exact HU|].
  follow HR; follow100 (odd_five 13 _ _ H5).
  follow100 (normal_calls 13 _ _ H42).
  follow (marker_calls 1 0 _ _ (F_columns [42;0]%nat 6 _ _ H24)).
  rewrite Et; unfold root; finish.
Qed.

Lemma three_even3 p b r s:
  sideRLs tm (hf^^6) r s ->
  root (X^^(1+p) *> [0] *> X^^(3+b) *> [0] *> X *> [0] *>
    X^^3 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0;0] *> X *> [0;0] *> X^^5 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma h_even_batch m n:
  segRLs tm (h^^(1+m*2)) (h^^m)
    (X^^(1+n)++[0;0]) (X^^(1+n+m)++[0]++Y).
Proof.
  rewrite (lpow_add _ 1 (m*2) h).
  change (segRLs tm (h++h^^(m*2)) ([]++h^^m)
    (X^^(1+n)++[0;0]) (X^^(1+n+m)++[0]++Y)).
  eapply segRLs_trans; [apply digit_even|apply h_pairs_odd].
Qed.

Lemma init_three_short:
  exists r, CutNum true 218 1 r /\
    c0 -->* root (X^^16 *> [0] *> X^^2 *> [0;0] *> X^^20 *> [0] *> Y *> r).
Proof.
  destruct init_three_column as [r [HN HR]].
  destruct (CutNum_Fs 6 true 193 0 _ HN ltac:(lia)) as [s [HS H6]].
  assert (HC: CutNum true 199 1 (X^^5 *> s)).
  { apply CutNum_prepend; exact HS. }
  destruct (CutNum_hs 19 _ _ _ _ HC ltac:(lia)) as [t [HT H19]].
  assert (H39: sideRLs tm (h^^39)
    (X *> [0;0] *> X^^5 *> s) (X^^20 *> [0] *> Y *> t)).
  { change (sideRLs tm (h^^39) ((X^^1++[0;0]) *> (X^^5 *> s))
      ((X^^20++[0]++Y) *> t)).
    eapply segRLs_sideRLs_concat; [exact (h_even_batch 19 0)|exact H19]. }
  exists t; split; [exact HT|].
  follow HR; follow100 (three_even3 1 40 _ _ H6).
  exact (marker_hcalls 13 2 1 _ _ H39).
Qed.

Lemma a2_digit_finish a r s:
  sideRLs tm (h^^2) r s ->
  0inf <* <[1;1;1;0;1;1] <{{F}} [1;0] *> Y *> X^^(1+a) *> [0] *> Y *> r -->+
  root (X *> [0;0;0] *> X^^(2+a) *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma a2_double_odd k a r s:
  sideRLs tm (h^^(1+k*3+3)) r s ->
  root (X^^(2+k*2) *> [0] *> X^^2 *> [0;0] *>
    X^^(1+a+k) *> [0] *> Y *> r) -->+
  root (X *> [0;0;0] *> X^^(2+a) *> [0;0] *> s).
Proof.
  intro H; rewrite (lpow_add _ (1+k*3) 3 h), (lpow_add _ 1 (k*3) h) in H.
  destruct (sideRLs_split H) as [r1 [H1 Hs]].
  destruct (sideRLs_split H1) as [r0 [H0 Hk]].
  destruct (sideRLs_split (ls1:=h) (ls2:=h^^2) Hs) as [r2 [H2 H3]].
  assert (HD: sideRLs tm h (X^^(1+a+k) *> [0] *> Y *> r)
    (X^^(2+a+k) *> [0;0] *> r0)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    eapply segRLs_sideRLs_concat; [applys_eq (digit_odd_all (1+a+k)); flia|exact H0]. }
  eapply progress_trans; [apply a2_prepare,HD|].
  eapply evstep_progress_trans; [exact (pending_digit_pairs k 0 a _ _ _ Hk)|].
  eapply progress_trans; [apply pending_digit_end,H2|apply a2_digit_finish,H3].
Qed.

Lemma init_three_return:
  exists r, CutNum true 243 1 r /\
    c0 -->* root (X *> [0;0;0] *> X^^14 *> [0;0] *> r).
Proof.
  destruct init_three_short as [r [HN HR]].
  destruct (CutNum_hs 25 _ _ _ _ HN ltac:(lia)) as [s [HS H25]].
  exists s; split; [exact HS|].
  follow HR; apply progress_evstep; exact (a2_double_odd 7 12 _ _ H25).
Qed.

Lemma two_even2 p r s:
  sideRLs tm (hf^^7) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^2 *> [0;0] *> r) -->+
  root (X^^(6+p) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_O262:
  exists r, Num true 262 r /\ c0 -->* root r.
Proof.
  destruct init_three_return as [r [HN HR]].
  destruct (CutNum_hs 12 _ _ _ _ HN ltac:(lia)) as [s [HS H12]].
  destruct (sideRLs_split (ls1:=h^^6) (ls2:=h^^6) H12) as [r6 [H6 H6']].
  assert (HF: sideRLs tm (hf^^12) (X^^13 *> [0;0] *> r) (X^^7 *> [0;0] *> r6)).
  { change (sideRLs tm (hf^^12) ((X^^13++sep false) *> r) ((X^^7++sep false) *> r6)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 6 7 false)|exact H6]. }
  assert (HF': sideRLs tm (hf^^12) (X^^7 *> [0;0] *> r6) (X *> [0;0] *> s)).
  { change (sideRLs tm (hf^^12) ((X^^7++sep false) *> r6) ((X^^1++sep false) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 6 1 false)|exact H6']. }
  destruct (CutNum_Fs 7 _ _ _ _ HS ltac:(lia)) as [t [HT H7]].
  exists (X^^8 *> t); split; [exact HT|].
  follow HR; follow100 (a2_cleanup _ _ HF).
  follow (two_markers 1 1 _ _ HF').
  apply progress_evstep; exact (two_even2 2 _ _ H7).
Qed.

Lemma init_O522:
  exists r, Num true 522 r /\
    c0 -->* root (X^^88 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_O262 as [r [HN HR]].
  destruct (Num_O_even_inv 129 _ HN) as [s [HS ES]].
  destruct (Num_add 393 _ _ _ HS) as [t [HT H393]].
  destruct (Num_E_even_inv 261 _ HT) as [u [HU EU]].
  destruct (Num_add 261 _ _ _ HU) as [v [HV H261]].
  exists v; split; [exact HV|].
  follow HR; rewrite ES; follow100 (normal_calls 130 _ _ H393).
  rewrite EU; exact (marker_hcalls 87 0 1 _ _ H261).
Qed.

Lemma init_two_odd3:
  exists r, Num false 607 r /\
    c0 -->* root (X^^37 *> [0] *> X *> [0] *> X^^3 *> [0] *> Y *> r).
Proof.
  destruct init_O522 as [r [HN HR]].
  destruct (CutNum_a2 86 true 522 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_O_odd_inv 391 _ HS) as [t [HT ET]].
  assert (Es: s=X^^219 *> [0] *> Y *> t).
  { exact (cut_prefix 394 175 _ _ ltac:(lia) ET). }
  destruct (Num_add 216 _ _ _ HT) as [u [HU H216]].
  assert (HF: sideRLs tm (hf^^432)
    (X^^218 *> [0] *> Y *> t) (X^^2 *> [0] *> Y *> u)).
  { change (sideRLs tm (hf^^432) ((X^^218++sep true) *> t) ((X^^2++sep true) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 216 2 true)|exact H216]. }
  destruct (sideRLs_split (ls1:=hf^^12) (ls2:=hf^^420) HF) as [v [H12 H420]].
  exists u; split; [exact HU|].
  follow HR; follow100 HRS; rewrite Es; follow100 (a2_cleanup _ _ H12).
  follow (two_markers 35 1 _ _ H420); unfold root; finish.
Qed.

Lemma two_odd3 p r s:
  sideRLs tm (h^^3) r s ->
  root (X^^(2+p) *> [0] *> X *> [0] *> X^^3 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> Y *> Y *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_triple_Y:
  exists r, Num false 610 r /\
    c0 -->* root (X^^37 *> [0] *> Y *> Y *> Y *> r).
Proof.
  destruct init_two_odd3 as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  exists s; split; [exact HS|].
  follow HR; apply progress_evstep; exact (two_odd3 35 _ _ H3).
Qed.

Lemma triple_Y_return p r s:
  sideRLs tm (hf^^8) r s ->
  root (X^^(2+p) *> [0] *> Y *> Y *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> X^^2 *> [0] *> X *> [0] *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_three_column_again:
  exists r, Num true 609 r /\
    c0 -->* root (X^^8 *> [0] *> X^^111 *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_triple_Y as [r [HN HR]].
  destruct (CutNum_Fs 8 false 610 0 _ HN ltac:(lia)) as [r8 [HN8 H8]].
  destruct (CutNum_Fs 432 _ _ _ _ HN8 ltac:(lia)) as [s [HS H432]].
  destruct (Num_E_even_inv 525 _ HS) as [t [HT ET]].
  assert (Es: s=X^^86 *> [0;0] *> t).
  { exact (cut_prefix 526 440 _ _ ltac:(lia) ET). }
  destruct (Num_add 84 _ _ _ HT) as [u [HU H84]].
  assert (HF: sideRLs tm (hf^^168) s (X^^2 *> [0;0] *> u)).
  { rewrite Es; change (sideRLs tm (hf^^168)
      ((X^^86++sep false) *> t) ((X^^2++sep false) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 84 2 false)|exact H84]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (triple_Y_return 35 _ _ H8).
  follow100 (normal_calls 35 _ _ (h_columns [0]%nat 108 2 _ _ H432)).
  follow (marker_calls 7 0 _ _ (F_columns [110;0]%nat 42 _ _ HF)).
  unfold root; finish.
Qed.

Lemma h_pair_even n:
  segRLs tm (h^^2) h (X^^(1+n)++[0;0]) (X^^(2+n)++[0;0]).
Proof.
  change (segRLs tm (h++h) ([]++h) (X^^(1+n)++[0;0]) (X^^(2+n)++[0;0])).
  eapply segRLs_trans; [apply digit_even|apply digit_odd].
Qed.

Lemma h_pairs_even m n:
  segRLs tm (h^^(m*2)) (h^^m) (X^^(1+n)++[0;0]) (X^^(1+n+m)++[0;0]).
Proof.
  gen n; induction m as [|m IH]; intro n.
  - replace (1+n+0) with (1+n) by lia; constructor.
  - replace (S m*2) with (2+m*2) by lia; rewrite lpow_add.
    change (segRLs tm (h^^2++h^^(m*2)) (h++h^^m)
      (X^^(1+n)++[0;0]) (X^^(1+n+S m)++[0;0])).
    eapply segRLs_trans; [apply h_pair_even|applys_eq (IH (1+n)); flia].
Qed.

Lemma init_large_a1:
  exists r, CutNum true 737 1 r /\
    c0 -->* root (X *> [0] *> X^^34 *> [0;0] *> r).
Proof.
  destruct init_three_column_again as [r [HN HR]].
  destruct (CutNum_Fs 6 true 609 0 _ HN ltac:(lia)) as [s [HS H6]].
  assert (HC: CutNum true 615 1 (X^^5 *> s)).
  { apply CutNum_prepend; exact HS. }
  destruct (CutNum_hs 54 _ _ _ _ HC ltac:(lia)) as [t [HT H54]].
  assert (H108: sideRLs tm (h^^108)
    (X *> [0;0] *> X^^5 *> s) (X^^55 *> [0;0] *> t)).
  { change (sideRLs tm (h^^108) ((X^^1++[0;0]) *> (X^^5 *> s))
      ((X^^55++[0;0]) *> t)).
    eapply segRLs_sideRLs_concat; [exact (h_pairs_even 54 0)|exact H54]. }
  destruct (CutNum_hs 68 _ _ _ _ HT ltac:(lia)) as [u [HU H68]].
  exists u; split; [exact HU|].
  follow HR; follow100 (three_even3 7 108 _ _ H6).
  follow (marker_hcalls 36 8 0 _ _ H108).
  apply progress_evstep; exact (a1_double_digit 22 31 _ _ H68).
Qed.

Lemma init_E779:
  exists r, Num false 779 r /\
    c0 -->* root (X^^127 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_large_a1 as [r [HN HR]].
  destruct (CutNum_hs 33 _ _ _ _ HN ltac:(lia)) as [s [HS H33]].
  destruct (Num_pending 11 (0inf <* [1]) _ _ _ _ HS ltac:(lia)) as [t [HT HP]].
  destruct (Num_O_even_inv 401 _ HT) as [u [HU EU]].
  assert (Et: t=X^^379 *> [0;0] *> u).
  { exact (cut_prefix 404 25 _ _ ltac:(lia) EU). }
  destruct (Num_add 378 _ _ _ HU) as [v [HV H378]].
  assert (HF: sideRLs tm (hf^^756)
    (X^^379 *> [0] *> Y *> u) (X *> [0] *> Y *> v)).
  { change (sideRLs tm (hf^^756) ((X^^379++sep true) *> u) ((X^^1++sep true) *> v)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 378 1 true)|exact H378]. }
  exists v; split; [exact HV|].
  follow HR; follow (marker_hcalls 11 0 0 _ _ H33).
  follow100 (a1_prepare 11 s); follow100 HP; rewrite Et.
  follow100 (a1_even_finish 379 u).
  follow (marker_calls 126 0 _ _ HF); unfold root; finish.
Qed.

Lemma birth_positive_finish b r s:
  sideRLs tm hf r s ->
  0inf <* [1;1;1] <* Dr^^b <* T2r {{B}}> r -->+
  root (X *> [0] *> X^^b *> [0] *> X^^3 *> s).
Proof.
  intro H; unfold root.
  follow11 (sideRLs_1 _ _ _ _ _ H); es; er; finish.
Qed.

Lemma birth_full p r s:
  sideRLs tm (hf^^(6+p*6)) r s ->
  root (X^^(1+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root (X *> [0] *> X^^(3+p*3) *> [0] *> X^^3 *> s).
Proof.
  intro H; replace (6+p*6) with (3+(p*6+3)) in H by lia.
  rewrite (lpow_add _ 3 (p*6+3) hf) in H.
  destruct (sideRLs_split H) as [r3 [H3 Hs]].
  rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm Hlast]].
  destruct (sideRLs_split (ls1:=hf^^2) (ls2:=hf) Hlast) as [rt [H2 H1]].
  eapply progress_trans; [apply birth_prepare, H3|].
  eapply evstep_progress_trans; [exact (birth_cycles p 0 0 _ _ Hm)|].
  eapply progress_trans; [apply birth_end, H2|apply birth_positive_finish, H1].
Qed.

Lemma CutNum_birth p b j d r:
  CutNum b j d r -> d*2+4+p*6<=j ->
  exists s, CutNum b (j+6+p*6) (d+3+p*6) s /\
    root (X^^(1+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X *> [0] *> X^^(3+p*3) *> [0] *> s).
Proof.
  intros HN Hbound.
  destruct (CutNum_Fs (6+p*6) _ _ _ _ HN ltac:(lia)) as [s [HS HF]].
  exists (X^^3 *> s); split.
  - apply CutNum_prepend; applys_eq HS; flia.
  - exact (birth_full p _ _ HF).
Qed.

Lemma init_O770:
  exists r, Num true 770 r /\
    c0 -->* root (X *> [0] *> X^^381 *> [0] *> X^^12 *> [0] *> Y *> r).
Proof.
  destruct init_E779 as [r [HN HR]].
  destruct (CutNum_birth 126 false 779 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_E_odd_inv 770 _ HS) as [t [HT ET]].
  assert (Es: s=X^^12 *> [0] *> Y *> t).
  { exact (cut_prefix 771 759 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 HRS; rewrite Es; unfold root; finish.
Qed.

Lemma init_two_odd6:
  exists r, Num true 776 r /\
    c0 -->* root (X^^2 *> [0] *> X^^381 *> [0] *> X^^6 *> [0] *> Y *> r).
Proof.
  destruct init_O770 as [r [HN HR]].
  destruct (Num_add 6 _ _ _ HN) as [s [HS H6]].
  assert (HF: sideRLs tm (hf^^12)
    (X^^11 *> [0] *> Y *> r) (X^^5 *> [0] *> Y *> s)).
  { change (sideRLs tm (hf^^12) ((X^^11++sep true) *> r) ((X^^5++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 6 5 true)|exact H6]. }
  exists s; split; [exact HS|].
  follow HR; follow (marker_calls 1 0 _ _ (F_markers 6 380 _ _ HF));
    unfold root; finish.
Qed.

Lemma two_odd6 p b r s:
  sideRLs tm (h^^6) r s ->
  root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^6 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0;0] *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_second_Y:
  exists r, Num true 782 r /\
    c0 -->* root (X^^3 *> [0] *> X^^381 *> [0;0] *> Y *> r).
Proof.
  destruct init_two_odd6 as [r [HN HR]].
  destruct (Num_add 6 _ _ _ HN) as [s [HS H6]].
  exists s; split; [exact HS|].
  follow HR; apply progress_evstep, (two_odd6 1 380), H6.
Qed.

Lemma init_nested_a3:
  exists r, Num false 767 r /\
    c0 -->* root (X^^129 *> [0] *> X^^3 *> [0;0] *> X^^378 *> [0] *> X^^15 *> [0;0] *> r).
Proof.
  destruct init_second_Y as [r [HN HR]].
  destruct (CutNum_Fs 756 true 782 0 _ HN ltac:(lia)) as [s [HS H756]].
  destruct (Num_O_even_inv 767 _ HS) as [t [HT ET]].
  assert (Es: s=X^^14 *> [0;0] *> t).
  { exact (cut_prefix 770 756 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow (marker_hcalls 126 2 2 _ _ (Y_hs 377 _ _ H756)).
  rewrite Es; unfold root; finish.
Qed.

Lemma init_nested_a3_pending:
  exists r, Num false 781 r /\
    c0 -->* pending 124 (0inf <* [1;1]) (X^^384 *> [0] *> X *> [0;0] *> r).
Proof.
  destruct init_nested_a3 as [r [HN HR]].
  destruct (Num_add 2 _ _ _ HN) as [s [HS H2]].
  assert (HF: sideRLs tm (hf^^4)
    (X^^14 *> [0;0] *> r) (X^^12 *> [0;0] *> s)).
  { change (sideRLs tm (hf^^4) ((X^^14++sep false) *> r) ((X^^12++sep false) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 2 12 false)|exact H2]. }
  destruct (Num_add 12 _ _ _ HS) as [t [HT H12]].
  exists t; split; [exact HT|].
  follow HR; follow100 (a3_prepare 128 _ _ (h_columns [] 2 378 _ _ HF)).
  exact (pending_marker_cycles 4 124 379 0 _ _ _ H12).
Qed.

Notation Kr := <[0;0;1;0;0;1;1;0;0;1;1].

Lemma pending_marker_one q b l r:
  pending q l (X^^(1+b) *> [0] *> X *> [0;0] *> r) -->+
  pending b (l <* Dr^^q <* Kr) r.
Proof. unfold pending; es; er; finish. Qed.

Lemma marked_K_root q r s:
  sideRLs tm (hf^^6) r s ->
  0inf <* [1;1] <* Dr^^q <* Kr <{{F}} [1;0] *> Y *> r -->+
  root (X^^(1+q) *> [0] *> Y *> X^^3 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_double_odd:
  exists r, Num true 969 r /\
    c0 -->* root (X^^125 *> [0] *> Y *> X^^199 *> [0] *> Y *> r).
Proof.
  destruct init_nested_a3_pending as [r [HN HR]].
  destruct (Num_pending 383 (0inf <* [1;1] <* Dr^^124 <* Kr)
    false 781 0 _ HN ltac:(lia)) as [s [HS HP]].
  destruct (CutNum_Fs 6 _ _ _ _ HS ltac:(lia)) as [t [HT H6]].
  destruct (Num_E_odd_inv 969 _ HT) as [u [HU EU]].
  assert (Et: t=X^^196 *> [0] *> Y *> u).
  { exact (cut_prefix 970 774 _ _ ltac:(lia) EU). }
  exists u; split; [exact HU|].
  follow HR; follow100 (pending_marker_one 124 383 (0inf <* [1;1]) r).
  follow100 HP; follow100 (marked_K_root 124 _ _ H6).
  rewrite Et; unfold root; finish.
Qed.

Lemma init_O1543:
  exists r, Num true 1543 r /\
    c0 -->* root (X^^130 *> [0;0] *> Y *> r).
Proof.
  destruct init_double_odd as [r [HN HR]].
  destruct (Num_add 187 _ _ _ HN) as [s [HS H187]].
  assert (H374: sideRLs tm (h^^374)
    (X^^199 *> [0] *> Y *> r) (X^^386 *> [0] *> Y *> s)).
  { change (sideRLs tm (h^^374)
      ((X^^199++[0]++Y) *> r) ((X^^386++[0]++Y) *> s)).
    eapply segRLs_sideRLs_concat; [exact (h_pairs_odd 187 199)|exact H187]. }
  destruct (sideRLs_split (ls1:=h^^2) (ls2:=h^^372) H374) as [r2 [H2 H372]].
  destruct (Num_add 384 _ _ _ HS) as [t [HT H384]].
  assert (HF: sideRLs tm (hf^^768)
    (X^^386 *> [0] *> Y *> s) (X^^2 *> [0] *> Y *> t)).
  { change (sideRLs tm (hf^^768) ((X^^386++sep true) *> s) ((X^^2++sep true) *> t)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 384 2 true)|exact H384]. }
  destruct (Num_add 3 _ _ _ HT) as [u [HU H3]].
  exists u; split; [exact HU|].
  follow HR; follow100 (normal_odd 123 _ _ H2).
  follow100 (normal_calls 123 _ _ H372).
  follow (marker_calls 128 0 _ _ HF).
  apply progress_evstep, (odd_three 128), H3.
Qed.

Lemma init_E1540:
  exists r, Num false 1540 r /\
    c0 -->* root (X^^65 *> [0] *> X^^388 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_O1543 as [r [HN HR]].
  destruct (CutNum_Fs 774 true 1543 0 _ HN ltac:(lia)) as [s [HS H774]].
  destruct (Num_O_odd_inv 1156 _ HS) as [t [HT ET]].
  assert (Es: s=X^^385 *> [0] *> Y *> t).
  { exact (cut_prefix 1159 774 _ _ ltac:(lia) ET). }
  destruct (Num_add 384 _ _ _ HT) as [u [HU H384]].
  assert (HF: sideRLs tm (hf^^768) s (X *> [0] *> Y *> u)).
  { rewrite Es; change (sideRLs tm (hf^^768)
      ((X^^385++sep true) *> t) ((X^^1++sep true) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 384 1 true)|exact H384]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (normal_calls 128 _ _ (Y_hs 386 _ _ H774)).
  follow (marker_calls 64 0 _ _ (F_markers 384 387 _ _ HF)).
  unfold root; finish.
Qed.

Lemma init_large_nested_a2:
  exists r, Num true 1157 r /\
    c0 -->* root (X^^194 *> [0] *> X^^2 *> [0;0] *> X^^386 *> [0] *> X^^387 *> [0;0] *> r).
Proof.
  destruct init_E1540 as [r [HN HR]].
  destruct (CutNum_odd2_pair 64 385 false 1540 0 _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_E_even_inv 773 _ HS) as [t [HT ET]].
  assert (Es: s=X^^771 *> [0;0] *> t).
  { exact (cut_prefix 774 3 _ _ ltac:(lia) ET). }
  assert (HC: CutNum false 1546 4 (X^^770 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 773), HT. }
  destruct (CutNum_Fs 768 _ _ _ _ HC ltac:(lia)) as [u [HU H768]].
  destruct (Num_E_even_inv 1157 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^386 *> [0;0] *> v).
  { exact (cut_prefix 1158 772 _ _ ltac:(lia) EV). }
  exists v; split; [exact HV|].
  follow HR; follow100 HRS; rewrite Es.
  follow (marker_hcalls 128 65 1 _ _ (h_columns [] 384 2 _ _ H768)).
  rewrite Eu; unfold root; finish.
Qed.

Lemma init_large_pending_J:
  exists r, Num true 1542 r /\
    c0 -->* pending 64 (0inf <* <[1;1;1;0;1;1])
      (X^^515 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_large_nested_a2 as [r [HN HR]].
  assert (HC: CutNum false 2314 772 (X^^386 *> [0;0] *> r)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 1157), HN. }
  destruct (CutNum_Fs 2 _ _ _ _ HC ltac:(lia)) as [s [HS H2]].
  destruct (Num_E_even_inv 1158 _ HS) as [t [HT ET]].
  assert (Es: s=X^^385 *> [0;0] *> t).
  { exact (cut_prefix 1159 774 _ _ ltac:(lia) ET). }
  destruct (Num_add 384 _ _ _ HT) as [u [HU H384]].
  exists u; split; [exact HU|].
  follow HR; follow100 (a2_prepare 192 _ _ (h_columns [] 1 386 _ _ H2)).
  rewrite Es; exact (pending_marker_cycles 128 64 386 1 _ _ _ H384).
Qed.

Lemma init_large_after_J:
  exists r, Num false 1547 r /\
    c0 -->* root (X^^66 *> [0] *> X *> [0] *> X^^513 *> [0;0] *> r).
Proof.
  destruct init_large_pending_J as [r [HN HR]].
  destruct (Num_add 1 _ _ _ HN) as [s [HS H1]].
  destruct (Num_pending 514 (0inf <* <[1;1;1;0;1;1] <* Dr^^64 <* Jr)
    true 1543 0 _ HS ltac:(lia)) as [t [HT HP]].
  destruct (CutNum_Fs 10 _ _ _ _ HT ltac:(lia)) as [u [HU H10]].
  destruct (Num_O_even_inv 1547 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^510 *> [0;0] *> v).
  { exact (cut_prefix 1550 1040 _ _ ltac:(lia) EV). }
  exists v; split; [exact HV|].
  follow HR; follow100 (pending_marker_short 64 514 (0inf <* <[1;1;1;0;1;1]) _ _ H1).
  follow100 HP; follow100 (marked_J_root 63 _ _ H10).
  rewrite Eu; unfold root; finish.
Qed.

Lemma init_two_even3:
  exists r, Num false 2057 r /\
    c0 -->* root (X^^151 *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_large_after_J as [r [HN HR]].
  destruct (Num_add 510 _ _ _ HN) as [s [HS H510]].
  assert (HF: sideRLs tm (hf^^1020)
    (X^^512 *> [0;0] *> r) (X^^2 *> [0;0] *> s)).
  { change (sideRLs tm (hf^^1020) ((X^^512++sep false) *> r) ((X^^2++sep false) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 510 2 false)|exact H510]. }
  exists s; split; [exact HS|].
  follow HR; follow (two_markers 85 65 _ _ HF); unfold root; finish.
Qed.

Lemma two_even3 p r s:
  sideRLs tm (hf^^5) r s ->
  root (X^^(2+p) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> Y *> [0;0] *> X^^4 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma odd_zero_return p r s:
  sideRLs tm h r s ->
  root (X^^(2+p) *> [0] *> Y *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0;0] *> X *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_E2513:
  exists r, CutNum false 2513 1 r /\
    c0 -->* root (X^^76 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_two_even3 as [r [HN HR]].
  destruct (CutNum_Fs 5 false 2057 0 _ HN ltac:(lia)) as [s [HS H5]].
  assert (HC: CutNum false 2062 1 (X^^4 *> s)).
  { apply CutNum_prepend; exact HS. }
  destruct (CutNum_hs 1 _ _ _ _ HC ltac:(lia)) as [t [HT H1]].
  destruct (CutNum_hs 225 _ _ _ _ HT ltac:(lia)) as [u [HU H225]].
  assert (H450: sideRLs tm (h^^450)
    (X *> [0;0] *> t) (X^^226 *> [0;0] *> u)).
  { change (sideRLs tm (h^^450) ((X^^1++[0;0]) *> t) ((X^^226++[0;0]) *> u)).
    eapply segRLs_sideRLs_concat; [exact (h_pairs_even 225 0)|exact H225]. }
  destruct (CutNum_hs 225 _ _ _ _ HU ltac:(lia)) as [v [HV Hlast]].
  exists v; split; [exact HV|].
  follow HR; follow100 (two_even3 149 _ _ H5).
  follow100 (odd_zero_return 149 _ _ H1).
  follow100 (normal_calls 149 _ _ H450).
  exact (marker_hcalls 75 0 1 _ _ Hlast).
Qed.

Lemma init_two_even2_large:
  exists r, Num true 2589 r /\
    c0 -->* root (X^^204 *> [0] *> X *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_E2513 as [r [HN HR]].
  destruct (CutNum_a2 74 _ _ _ _ HN ltac:(lia)) as [s [HS HRS]].
  destruct (Num_E_even_inv 1371 _ HS) as [t [HT ET]].
  assert (Es: s=X^^1220 *> [0;0] *> t).
  { exact (cut_prefix 1372 152 _ _ ltac:(lia) ET). }
  assert (HC: CutNum false 2742 153 (X^^1219 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_E_even 1371), HT. }
  destruct (CutNum_Fs 12 _ _ _ _ HC ltac:(lia)) as [u [HU H12]].
  destruct (Num_E_even_inv 1377 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^1213 *> [0;0] *> v).
  { exact (cut_prefix 1378 165 _ _ ltac:(lia) EV). }
  destruct (Num_add 1212 _ _ _ HV) as [w [HW H1212]].
  assert (HF: sideRLs tm (hf^^2424) u (X *> [0;0] *> w)).
  { rewrite Eu; change (sideRLs tm (hf^^2424)
      ((X^^1213++sep false) *> v) ((X^^1++sep false) *> w)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 1212 1 false)|exact H1212]. }
  exists w; split; [exact HW|].
  follow HR; follow100 HRS; rewrite Es.
  follow100 (a2_cleanup _ _ H12); follow (two_markers 202 1 _ _ HF).
  unfold root; finish.
Qed.

Lemma init_O5796:
  exists r, Num true 5796 r /\
    c0 -->* root (X^^967 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_two_even2_large as [r [HN HR]].
  destruct (CutNum_Fs 7 true 2589 0 _ HN ltac:(lia)) as [s [HS H7]].
  destruct (Num_O_even_inv 1296 _ HS) as [t [HT ET]].
  assert (Es: s=X^^1292 *> [0;0] *> t).
  { exact (cut_prefix 1299 7 _ _ ltac:(lia) ET). }
  destruct (Num_add 4500 _ _ _ HT) as [u [HU H4500]].
  destruct (Num_E_even_inv 2898 _ HU) as [v [HV EV]].
  destruct (Num_add 2898 _ _ _ HV) as [w [HW H2898]].
  exists w; split; [exact HW|].
  follow HR; follow100 (two_even2 203 _ _ H7); rewrite Es.
  follow100 (normal_calls 1499 _ _ H4500); rewrite EV.
  exact (marker_hcalls 966 0 1 _ _ H2898).
Qed.

Lemma init_two_even5:
  exists r, Num false 6759 r /\
    c0 -->* root (X^^403 *> [0] *> X *> [0] *> X^^5 *> [0;0] *> r).
Proof.
  destruct init_O5796 as [r [HN HR]].
  destruct (CutNum_a2 965 true 5796 0 _ HN ltac:(apply Nat.leb_le; reflexivity)) as [s [HS HRS]].
  destruct (Num_O_even_inv 4347 _ HS) as [t [HT ET]].
  assert (Es: s=X^^2417 *> [0;0] *> t).
  { exact (cut_prefix 4350 1933 _ _ ltac:(lia) ET). }
  assert (HC: CutNum true 8698 1934 (X^^2416 *> [0;0] *> t)).
  { unfold CutNum; rewrite <-Str_app_assoc, <-lpow_add; apply (Num_O_even 4347), HT. }
  destruct (CutNum_Fs 12 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity)) as [u [HU H12]].
  destruct (Num_O_even_inv 4353 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^2410 *> [0;0] *> v).
  { exact (cut_prefix 4356 1946 _ _ ltac:(lia) EV). }
  destruct (Num_add 2406 _ _ _ HV) as [w [HW H2406]].
  assert (HF: sideRLs tm (hf^^4812) u (X^^4 *> [0;0] *> w)).
  { rewrite Eu; change (sideRLs tm (hf^^4812)
      ((X^^2410++sep false) *> v) ((X^^4++sep false) *> w)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 2406 4 false)|exact H2406]. }
  exists w; split; [exact HW|].
  follow HR; follow100 HRS; rewrite Es.
  follow100 (a2_cleanup _ _ H12); follow (two_markers 401 1 _ _ HF).
  unfold root; finish.
Qed.

Lemma two_even5 p r s:
  sideRLs tm (hf^^7) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^5 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0;0;0;0] *> X^^6 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_zero4:
  exists r, CutNum false 6766 1 r /\
    c0 -->* root (X^^404 *> [0;0;0;0] *> r).
Proof.
  destruct init_two_even5 as [r [HN HR]].
  destruct (CutNum_Fs 7 false 6759 0 _ HN ltac:(apply Nat.leb_le; reflexivity)) as [s [HS H7]].
  exists (X^^6 *> s); split.
  - apply CutNum_prepend; exact HS.
  - follow HR; apply progress_evstep, (two_even5 402), H7.
Qed.

Lemma zero4_prepare p r s:
  sideRLs tm h r s ->
  root (X^^(3+p) *> [0;0;0;0] *> r) -->+
  root (X^^(2+p) *> [0;0] *> X *> [0] *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_birth_E7973:
  exists r, CutNum false 7973 1 r /\
    c0 -->* root (X^^202 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_zero4 as [r [HN HR]].
  destruct (CutNum_hs 1 _ _ _ _ HN ltac:(apply Nat.leb_le; reflexivity)) as [s [HS H1]].
  destruct (CutNum_hs 603 _ _ _ _ HS ltac:(apply Nat.leb_le; reflexivity)) as [t [HT H603]].
  assert (H1206: sideRLs tm (h^^1206)
    (X *> [0] *> Y *> s) (X^^604 *> [0] *> Y *> t)).
  { change (sideRLs tm (h^^1206) ((X^^1++[0]++Y) *> s) ((X^^604++[0]++Y) *> t)).
    eapply segRLs_sideRLs_concat; [exact (h_pairs_odd 603 1)|exact H603]. }
  destruct (CutNum_hs 603 _ _ _ _ HT ltac:(apply Nat.leb_le; reflexivity)) as [u [HU Hlast]].
  assert (HF: sideRLs tm (hf^^1206)
    (X^^604 *> [0] *> Y *> t) (X *> [0] *> Y *> u)).
  { change (sideRLs tm (hf^^1206) ((X^^604++sep true) *> t) ((X^^1++sep true) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 603 1 true)|exact Hlast]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (zero4_prepare 401 _ _ H1).
  follow100 (normal_calls 401 _ _ H1206).
  follow (marker_calls 201 0 _ _ HF); unfold root; finish.
Qed.

Lemma init_O4592:
  exists r, Num true 4592 r /\
    c0 -->* root (X *> [0] *> X^^606 *> [0] *> X^^3383 *> [0] *> Y *> r).
Proof.
  destruct init_birth_E7973 as [r [HN HR]].
  destruct (CutNum_birth 201 false 7973 1 _ HN ltac:(apply Nat.leb_le; reflexivity)) as [s [HS HRS]].
  destruct (Num_E_odd_inv 4592 _ HS) as [t [HT ET]].
  assert (Es: s=X^^3383 *> [0] *> Y *> t).
  { exact (cut_prefix 4593 1210 _ _ ltac:(lia) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 HRS; rewrite Es; unfold root; finish.
Qed.

Lemma init_long_YY:
  exists r, Num true 7975 r /\
    c0 -->* root (X^^565 *> [0] *> X^^605 *> [0] *> Y *> Y *> r).
Proof.
  destruct init_O4592 as [r [HN HR]].
  destruct (Num_add 3378 _ _ _ HN) as [s [HS H3378]].
  assert (HF: sideRLs tm (hf^^6756)
    (X^^3382 *> [0] *> Y *> r) (X^^4 *> [0] *> Y *> s)).
  { change (sideRLs tm (hf^^6756) ((X^^3382++sep true) *> r) ((X^^4++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 3378 4 true)|exact H3378]. }
  destruct (Num_add 5 _ _ _ HS) as [t [HT H5]].
  exists t; split; [exact HT|].
  follow HR; follow (marker_calls 563 0 _ _ (F_markers 3378 605 _ _ HF)).
  apply progress_evstep, (odd_five_general 563 605), H5.
Qed.

Lemma init_nested_birth:
  exists r, Num false 4588 r /\
    c0 -->* root (X^^766 *> [0] *> X^^2 *> [0] *> Y *>
      X^^603 *> [0] *> X^^3386 *> [0] *> Y *> r).
Proof.
  destruct init_long_YY as [r [HN HR]].
  destruct (CutNum_Fs 1206 true 7975 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H1206]].
  destruct (Num_O_odd_inv 4588 _ HS) as [t [HT ET]].
  assert (Es: s=X^^3385 *> [0] *> Y *> t).
  { exact (cut_prefix 4591 1206 _ _ ltac:(lia) ET). }
  assert (HF: sideRLs tm (hf^^1206)
    (X^^604 *> [0] *> Y *> Y *> r)
    (X *> [0] *> Y *> X^^603 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^1206) ((X^^604++sep true) *> (Y *> r))
      ((X^^1++sep true) *> (X^^603 *> [0] *> X *> s))).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 603 1 true)|].
    exact (Y_hs 602 _ _ H1206). }
  exists t; split; [exact HT|].
  follow HR; follow (marker_calls 201 564 _ _ HF).
  rewrite Es; unfold root; finish.
Qed.

Lemma init_nested_birth_short:
  exists r, Num false 7969 r /\
    c0 -->* birth 203 1690 (X^^603 *> [0] *> X^^5 *> [0] *> Y *> r).
Proof.
  destruct init_nested_birth as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  assert (HF6: sideRLs tm (hf^^6)
    (X^^3385 *> [0] *> Y *> r) (X^^3382 *> [0] *> Y *> s)).
  { change (sideRLs tm (hf^^6) ((X^^3385++sep true) *> r) ((X^^3382++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 3 3382 true)|exact H3]. }
  destruct (Num_add 3378 _ _ _ HS) as [t [HT H3378]].
  assert (HF6756: sideRLs tm (hf^^6756)
    (X^^3382 *> [0] *> Y *> s) (X^^4 *> [0] *> Y *> t)).
  { change (sideRLs tm (hf^^6756) ((X^^3382++sep true) *> s) ((X^^4++sep true) *> t)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 3378 4 true)|exact H3378]. }
  exists t; split; [exact HT|].
  follow HR; follow100 (birth_prepare 765 _ _ (F_markers 3 603 _ _ HF6)).
  exact (birth_cycles 563 202 0 _ _ (F_markers 3378 603 _ _ HF6756)).
Qed.

Lemma birth_marker_five a b c r s:
  sideRLs tm (h^^3) r s ->
  birth (2+a) (1+b) (X^^(1+c) *> [0] *> X^^5 *> [0] *> Y *> r) -->+
  root (X^^(2+a) *> [0;0] *> X^^(2+b) *> [0] *>
    X^^(4+c) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof. intro H; unfold birth, root; finish_calls H. Qed.

Lemma init_nested_return:
  exists r, Num false 7972 r /\
    c0 -->* root (X^^203 *> [0;0] *> X^^1691 *> [0] *>
      X^^606 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_nested_birth_short as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  exists s; split; [exact HS|].
  follow HR; apply progress_evstep, (birth_marker_five 201 1689 602), H3.
Qed.

Lemma normal_odd2_spill p u b r s:
  sideRLs tm (hf^^6) r s ->
  root (X^^(3+p) *> [0;0] *> X^^(1+u) *> [0] *>
    X^^(3+b) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> X^^(4+u) *> [0] *>
    X^^(1+b) *> [0;0] *> X^^2 *> [0] *> X^^3 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_nested_spill:
  exists r, CutNum false 7978 3 r /\
    c0 -->* root (X^^202 *> [0;0] *> X^^1694 *> [0] *>
      X^^604 *> [0;0] *> X^^2 *> [0] *> r).
Proof.
  destruct init_nested_return as [r [HN HR]].
  destruct (CutNum_Fs 6 false 7972 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H6]].
  exists (X^^3 *> s); split; [apply CutNum_prepend; exact HS|].
  follow HR; apply progress_evstep, (normal_odd2_spill 200 1690 603), H6.
Qed.

Lemma init_even_exhaustion:
  exists r, CutNum false 9184 1209 r /\
    c0 -->* root (X *> [0] *> X^^2298 *> [0] *> X *> [0;0] *>
      X^^605 *> [0] *> r).
Proof.
  destruct init_nested_spill as [r [HN HR]].
  destruct (Num_E_even_inv 3989 _ HN) as [t [HT ET]].
  assert (Er: r=X^^3987 *> [0;0] *> t).
  { exact (cut_prefix 3990 3 _ _ ltac:(lia) ET). }
  assert (HC: CutNum false 7978 4 (X^^3986 *> [0;0] *> t)).
  { unfold CutNum; applys_eq (Num_E_even 3989 t HT); flia. }
  destruct (CutNum_Fs 1206 false 7978 4 _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H1206]].
  assert (HF: sideRLs tm (hf^^1206)
    (X^^603 *> [0;0] *> X^^2 *> [0] *> X^^3987 *> [0;0] *> t)
    ([0;0] *> X^^605 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^1206)
      ((X^^603++sep false) *> markers [2]%nat (X^^3986 *> [0;0] *> t))
      ((X^^0++sep false) *> markers [605]%nat s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 603 0 false)|].
    exact (h_columns [] 603 2 _ _ H1206). }
  exists (X *> s); split.
  - change (CutNum false 9184 1209 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er; apply progress_evstep.
    exact (normal_calls 200 _ _ (h_columns [] 603 1694 _ _ HF)).
Qed.

Notation Wr := <[1;0;0;1;1;1;1;0;1;1].

Lemma nested_even_prepare b r:
  root (X *> [0] *> X^^(2+b) *> [0] *> X *> [0;0] *> r) -->+
  pending b (0inf <* Wr) r.
Proof. unfold root, pending; esx. Qed.

Lemma W_root_cleanup q r:
  0inf <* Wr <* Dr^^q <{{A}} [0;0] *> r -->+
  root ([0] *> X *> [0] *> X^^q *> [0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma init_mixed_return:
  exists r, CutNum true 13180 3469 r /\
    c0 -->* root ([0] *> X *> [0] *> X^^1169 *> [0] *> Y *> r).
Proof.
  destruct init_even_exhaustion as [r [HN HR]].
  destruct (Num_E_even_inv 4592 _ HN) as [t [HT ET]].
  assert (Er: r=X^^3384 *> [0;0] *> t).
  { exact (cut_prefix 4593 1209 _ _ ltac:(lia) ET). }
  destruct (Num_add 3381 _ _ _ HT) as [u [HU H3381]].
  destruct (Num_add 2 _ _ _ HU) as [v [HV H2]].
  destruct (Num_pending 1731 (0inf <* Wr <* Dr^^1169 <* Lr)
    true 7975 0 _ HV ltac:(apply Nat.leb_le; reflexivity)) as [s [HS HP]].
  destruct (CutNum_Fs 9 _ _ _ _ HS ltac:(apply Nat.leb_le; reflexivity))
    as [w [HW H9]].
  exists (X^^4 *> w); split; [apply CutNum_prepend; exact HW|].
  follow HR; rewrite Er.
  follow100 (nested_even_prepare 2296 (X^^605 *> [0] *> X^^3384 *> [0;0] *> t)).
  follow (pending_marker_cycles 1127 1169 604 2 (0inf <* Wr) _ _ H3381).
  follow100 (pending_marker_prepare 1169 1731 (0inf <* Wr) _ _ H2).
  follow100 HP; follow100 (marked_F_finish (0inf <* Wr <* Dr^^1169) _ _ H9).
  apply progress_evstep, W_root_cleanup.
Qed.

Lemma marker_second_half p r s:
  sideRLs tm (hf^^4) r s ->
  root ([0] *> X^^(1+p) *> [0] *> X *> r) -->+
  root (X^^(2+p) *> [0] *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_post_mixed_odd3:
  exists r, Num false 7171 r /\
    c0 -->* root (X^^390 *> [0] *> X^^3 *> [0] *> Y *>
      X^^3705 *> [0;0] *> r).
Proof.
  destruct init_mixed_return as [r [HN HR]].
  destruct (Num_O_even_inv 6588 _ HN) as [t [HT ET]].
  assert (Er: r=X^^3122 *> [0;0] *> t).
  { exact (cut_prefix 6591 3469 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  destruct (Num_add 1 _ _ _ HT) as [u [HU H1]].
  assert (HF4: sideRLs tm (hf^^4)
    (X^^1168 *> [0] *> Y *> X^^3122 *> [0;0] *> t)
    (X^^1166 *> [0] *> Y *> X^^3123 *> [0;0] *> u)).
  { change (sideRLs tm (hf^^4)
      ((X^^1168++sep true) *> ((X^^3122++[0;0]) *> t))
      ((X^^1166++sep true) *> ((X^^3123++[0;0]) *> u))).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 2 1166 true)|].
    eapply segRLs_sideRLs_concat; [exact (h_pairs_even 1 3121)|exact H1]. }
  destruct (Num_add 582 _ _ _ HU) as [v [HV H582]].
  assert (HF: sideRLs tm (hf^^2328)
    (X^^1166 *> [0] *> Y *> X^^3123 *> [0;0] *> u)
    (X^^2 *> [0] *> Y *> X^^3705 *> [0;0] *> v)).
  { change (sideRLs tm (hf^^2328)
      ((X^^1166++sep true) *> ((X^^3123++[0;0]) *> u))
      ((X^^2++sep true) *> ((X^^3705++[0;0]) *> v))).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 1164 2 true)|].
    eapply segRLs_sideRLs_concat; [exact (h_pairs_even 582 3122)|exact H582]. }
  exists v; split; [exact HV|].
  follow HR; rewrite Er; follow100 (marker_second_half 0 _ _ HF4).
  exact (marker_calls 388 1 _ _ HF).
Qed.

Lemma init_post_mixed_Y:
  exists r, CutNum true 14355 3474 r /\
    c0 -->* root (X^^390 *> [0;0] *> X^^3 *> [0] *> r).
Proof.
  destruct init_post_mixed_odd3 as [r [HN HR]].
  destruct (Num_add 1 _ _ _ HN) as [s [HS H1]].
  assert (H3: sideRLs tm (h^^3)
    (X^^3705 *> [0;0] *> r) (X^^3706 *> [0] *> Y *> s)).
  { change (sideRLs tm (h^^3) ((X^^3705++[0;0]) *> r) ((X^^3706++[0]++Y) *> s)).
    eapply segRLs_sideRLs_concat; [exact (h_even_batch 1 3704)|exact H1]. }
  destruct (Num_add 3 _ _ _ HS) as [t [HT Hlast]].
  assert (HF: sideRLs tm (hf^^6)
    (X^^3706 *> [0] *> Y *> s) (X^^3703 *> [0] *> Y *> t)).
  { change (sideRLs tm (hf^^6) ((X^^3706++sep true) *> s) ((X^^3703++sep true) *> t)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 3 3703 true)|exact Hlast]. }
  exists (X^^3704 *> [0] *> Y *> t); split.
  - unfold CutNum; applys_eq (Num_O_odd 7175 t HT); flia.
  - follow HR; follow100 (odd_three 389 _ _ H3).
    apply progress_evstep; exact (normal_cycle 388 _ _ (Y_hs 2 _ _ HF)).
Qed.

Lemma init_post_mixed_markers:
  exists r, Num false 10874 r /\
    c0 -->* root (X^^423 *> [0] *> X^^1171 *> [0] *> X^^5 *> [0] *> Y *> r).
Proof.
  destruct init_post_mixed_Y as [r [HN HR]].
  destruct (Num_O_odd_inv 7175 _ HN) as [t [HT ET]].
  assert (Er: r=X^^3704 *> [0] *> Y *> t).
  { exact (cut_prefix 7178 3474 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum true 14355 3475 (X^^3703 *> [0] *> Y *> t)).
  { unfold CutNum; applys_eq (Num_O_odd 7175 t HT); flia. }
  destruct (CutNum_Fs 2334 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H2334]].
  destruct (Num_O_odd_inv 8342 _ HS) as [u [HU EU]].
  assert (Es: s=X^^2536 *> [0] *> Y *> u).
  { exact (cut_prefix 8345 5809 _ _ ltac:(apply Nat.leb_le; reflexivity) EU). }
  destruct (Num_add 2532 _ _ _ HU) as [v [HV H2532]].
  assert (HF: sideRLs tm (hf^^5064)
    (X^^2536 *> [0] *> Y *> u) (X^^4 *> [0] *> Y *> v)).
  { change (sideRLs tm (hf^^5064) ((X^^2536++sep true) *> u) ((X^^4++sep true) *> v)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 2532 4 true)|exact H2532]. }
  exists v; split; [exact HV|].
  follow HR; rewrite Er.
  follow100 (normal_calls 388 _ _ (h_columns [] 1167 3 _ _ H2334)); rewrite Es.
  exact (marker_calls 422 0 _ _ (F_markers 2532 1170 _ _ HF)).
Qed.

Lemma marker_T_cycle p b r s:
  sideRLs tm (hf^^6) r s ->
  root (X^^(1+p) *> [0] *> X^^(4+b) *> [0] *> Y *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0] *> Y *> X^^3 *> [0] *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_post_mixed_T:
  exists r, CutNum false 10885 5 r /\
    c0 -->* root (X^^425 *> [0] *> X^^1167 *> [0] *> Y *> X^^3 *> [0] *> r).
Proof.
  destruct init_post_mixed_markers as [r [HN HR]].
  destruct (Num_add 5 _ _ _ HN) as [s [HS H5]].
  destruct (CutNum_Fs 6 false 10879 0 _ HS ltac:(apply Nat.leb_le; reflexivity))
    as [t [HT H6]].
  exists (X *> t); split.
  - change (CutNum false 10885 5 (X^^1 *> t)); apply CutNum_prepend; exact HT.
  - follow HR; follow100 (odd_five_general 422 1170 _ _ H5).
    apply progress_evstep, (marker_T_cycle 423 1166), H6.
Qed.

Lemma normal_cycles m p r s:
  sideRLs tm (h^^(m*3)) r s ->
  root (X^^(2+p+m) *> [0;0] *> r) -->*
  root (X^^(2+p) *> [0;0] *> s).
Proof.
  gen r; induction m as [|m IH]; intros r H.
  - inverts H; replace (2+p+0) with (2+p) by lia; unfold root; finish.
  - replace (S m*3) with (3+m*3) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r3 [H3 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (normal_cycle (p+m) _ _ H3); flia.
    + apply IH, Hs.
Qed.

Lemma init_post_T_odd3:
  exists r, CutNum false 13213 2333 r /\
    c0 -->* root (X^^813 *> [0] *> X^^3 *> [0] *> Y *> X^^1167 *> [0] *> r).
Proof.
  destruct init_post_mixed_T as [r [HN HR]].
  destruct (Num_E_odd_inv 5442 _ HN) as [t [HT ET]].
  assert (Er: r=X^^5438 *> [0] *> Y *> t).
  { exact (cut_prefix 5443 5 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum false 10885 6 (X^^5437 *> [0] *> Y *> t)).
  { unfold CutNum; applys_eq (Num_E_odd 5442 t HT); flia. }
  destruct (CutNum_Fs 2328 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H2328]].
  assert (HF: sideRLs tm (hf^^2328)
    (X^^1166 *> [0] *> Y *> X^^3 *> [0] *> X^^5438 *> [0] *> Y *> t)
    (X^^2 *> [0] *> Y *> X^^1167 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^2328)
      ((X^^1166++sep true) *> markers [3]%nat (X^^5437 *> [0] *> Y *> t))
      ((X^^2++sep true) *> markers [1167]%nat s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 1164 2 true)|].
    exact (h_columns [] 1164 3 _ _ H2328). }
  exists (X *> s); split.
  - change (CutNum false 13213 2333 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er; exact (marker_calls 388 424 _ _ HF).
Qed.

Lemma init_post_T_two_markers:
  exists r, CutNum false 13231 2351 r /\
    c0 -->* root (X^^813 *> [0;0] *> X^^3 *> [0] *> X^^1171 *> [0] *> r).
Proof.
  destruct init_post_T_odd3 as [r [HN HR]].
  destruct (Num_E_odd_inv 6606 _ HN) as [t [HT ET]].
  assert (Er: r=X^^4274 *> [0] *> Y *> t).
  { exact (cut_prefix 6607 2333 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum false 13213 2334 (X^^4273 *> [0] *> Y *> t)).
  { unfold CutNum; applys_eq (Num_E_odd 6606 t HT); flia. }
  destruct (CutNum_Fs 18 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H18]].
  destruct (sideRLs_split (ls1:=hf^^6) (ls2:=hf^^12) H18) as [u [H6 H12]].
  exists (X *> s); split.
  - change (CutNum false 13231 2351 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er.
    follow100 (odd_three 812 _ _ (h_columns [] 3 1167 _ _ H6)).
    apply progress_evstep.
    exact (normal_cycle 811 _ _ (Y_hs 2 _ _ (F_markers 6 1170 _ _ H12))).
Qed.

Lemma init_normal_spill5:
  exists r, Num true 10875 r /\
    c0 -->* root (X^^103 *> [0;0] *> X^^2133 *> [0] *>
      X^^1171 *> [0] *> X^^5 *> [0] *> Y *> r).
Proof.
  destruct init_post_T_two_markers as [r [HN HR]].
  destruct (Num_E_odd_inv 6615 _ HN) as [t [HT ET]].
  assert (Er: r=X^^4265 *> [0] *> Y *> t).
  { exact (cut_prefix 6616 2351 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum false 13231 2352 (X^^4264 *> [0] *> Y *> t)).
  { unfold CutNum; applys_eq (Num_E_odd 6615 t HT); flia. }
  destruct (CutNum_Fs 8520 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H8520]].
  destruct (Num_E_odd_inv 10875 _ HS) as [u [HU EU]].
  assert (Es: s=X^^4 *> [0] *> Y *> u).
  { exact (cut_prefix 10876 10872 _ _ ltac:(apply Nat.leb_le; reflexivity) EU). }
  exists u; split; [exact HU|].
  follow HR; rewrite Er.
  follow (normal_cycles 710 101 _ _ (h_columns [1170]%nat 2130 3 _ _ H8520)).
  rewrite Es; unfold root; finish.
Qed.

Lemma normal_odd5_prepare p u b r s:
  sideRLs tm (h^^5) r s ->
  root (X^^(3+p) *> [0;0] *> X^^(1+u) *> [0] *>
    X^^(5+b) *> [0] *> X^^5 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> X^^(4+u) *> [0] *>
    X^^(4+b) *> [0] *> Y *> Y *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma normal_T_spill p u b r s:
  sideRLs tm (hf^^6) r s ->
  root (X^^(3+p) *> [0;0] *> X^^(1+u) *> [0] *>
    X^^(4+b) *> [0] *> Y *> Y *> r) -->+
  root (X^^(2+p) *> [0;0] *> X^^(4+u) *> [0] *>
    X^^(1+b) *> [0] *> Y *> X^^3 *> [0] *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_normal_transpose:
  exists r, CutNum true 10886 5 r /\
    c0 -->* root (X^^101 *> [0;0] *> X^^2139 *> [0] *>
      X^^1167 *> [0] *> Y *> X^^3 *> [0] *> r).
Proof.
  destruct init_normal_spill5 as [r [HN HR]].
  destruct (Num_add 5 _ _ _ HN) as [s [HS H5]].
  destruct (CutNum_Fs 6 true 10880 0 _ HS ltac:(apply Nat.leb_le; reflexivity))
    as [t [HT H6]].
  exists (X *> t); split.
  - change (CutNum true 10886 5 (X^^1 *> t)); apply CutNum_prepend; exact HT.
  - follow HR; follow100 (normal_odd5_prepare 100 2132 1166 _ _ H5).
    apply progress_evstep, (normal_T_spill 99 2135 1166), H6.
Qed.

Lemma init_normal_transpose_end:
  exists r, CutNum true 11486 605 r /\
    c0 -->* root (X *> [0] *> X^^2440 *> [0] *>
      X^^867 *> [0] *> Y *> X^^303 *> [0] *> r).
Proof.
  destruct init_normal_transpose as [r [HN HR]].
  destruct (Num_O_even_inv 5441 _ HN) as [t [HT ET]].
  assert (Er: r=X^^5439 *> [0;0] *> t).
  { exact (cut_prefix 5444 5 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum true 10886 6 (X^^5438 *> [0;0] *> t)).
  { unfold CutNum; applys_eq (Num_O_even 5441 t HT); flia. }
  destruct (CutNum_Fs 600 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H600]].
  assert (HF: sideRLs tm (hf^^600)
    (X^^1166 *> [0] *> Y *> X^^3 *> [0] *> X^^5439 *> [0;0] *> t)
    (X^^866 *> [0] *> Y *> X^^303 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^600)
      ((X^^1166++sep true) *> markers [3]%nat (X^^5438 *> [0;0] *> t))
      ((X^^866++sep true) *> markers [303]%nat s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 300 866 true)|].
    exact (h_columns [] 300 3 _ _ H600). }
  exists (X *> s); split.
  - change (CutNum true 11486 605 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er.
    apply progress_evstep; exact (normal_calls 99 _ _ (h_columns [] 300 2139 _ _ HF)).
Qed.

Lemma init_second_transpose_odd3:
  exists r, CutNum true 13214 2333 r /\
    c0 -->* root (X^^145 *> [0] *> X^^2440 *> [0] *>
      X^^3 *> [0] *> Y *> X^^1167 *> [0] *> r).
Proof.
  destruct init_normal_transpose_end as [r [HN HR]].
  destruct (Num_O_even_inv 5741 _ HN) as [t [HT ET]].
  assert (Er: r=X^^5139 *> [0;0] *> t).
  { exact (cut_prefix 5744 605 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum true 11486 606 (X^^5138 *> [0;0] *> t)).
  { unfold CutNum; applys_eq (Num_O_even 5741 t HT); flia. }
  destruct (CutNum_Fs 1728 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H1728]].
  assert (HF: sideRLs tm (hf^^1728)
    (X^^866 *> [0] *> Y *> X^^303 *> [0] *> X^^5139 *> [0;0] *> t)
    (X^^2 *> [0] *> Y *> X^^1167 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^1728)
      ((X^^866++sep true) *> markers [303]%nat (X^^5138 *> [0;0] *> t))
      ((X^^2++sep true) *> markers [1167]%nat s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 864 2 true)|].
    exact (h_columns [] 864 303 _ _ H1728). }
  exists (X *> s); split.
  - change (CutNum true 13214 2333 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er.
    exact (marker_calls 144 0 _ _ (F_markers 864 2439 _ _ HF)).
Qed.

Lemma marker_odd3_transpose p b c r s:
  sideRLs tm (hf^^10) r s ->
  root (X^^(1+p) *> [0] *> X^^(3+b) *> [0] *> X^^3 *> [0] *> Y *>
    X^^(1+c) *> [0] *> X *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+b) *> [0] *> Y *> X *> [0] *>
    X^^(5+c) *> [0] *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_second_transpose:
  exists r, CutNum true 13224 2343 r /\
    c0 -->* root (X^^146 *> [0] *> X^^2438 *> [0] *> Y *>
      X *> [0] *> X^^1171 *> [0] *> r).
Proof.
  destruct init_second_transpose_odd3 as [r [HN HR]].
  destruct (Num_O_even_inv 6605 _ HN) as [t [HT ET]].
  assert (Er: r=X^^4275 *> [0;0] *> t).
  { exact (cut_prefix 6608 2333 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum true 13214 2334 (X^^4274 *> [0;0] *> t)).
  { unfold CutNum; applys_eq (Num_O_even 6605 t HT); flia. }
  destruct (CutNum_Fs 10 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H10]].
  exists (X *> s); split.
  - change (CutNum true 13224 2343 (X^^1 *> s)); apply CutNum_prepend; exact HS.
  - follow HR; rewrite Er.
    apply progress_evstep, (marker_odd3_transpose 144 2437 1166), H10.
Qed.

Lemma init_nested_even4:
  exists r, Num false 10876 r /\
    c0 -->* root (X^^857 *> [0] *> X^^305 *> [0] *> Y *>
      X^^2134 *> [0] *> X^^1171 *> [0] *> X^^4 *> [0;0] *> r).
Proof.
  destruct init_second_transpose as [r [HN HR]].
  destruct (Num_O_even_inv 6610 _ HN) as [t [HT ET]].
  assert (Er: r=X^^4270 *> [0;0] *> t).
  { exact (cut_prefix 6613 2343 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  assert (HC: CutNum true 13224 2344 (X^^4269 *> [0;0] *> t)).
  { unfold CutNum; applys_eq (Num_O_even 6610 t HT); flia. }
  destruct (CutNum_Fs 8532 _ _ _ _ HC ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H8532]].
  destruct (Num_O_even_inv 10876 _ HS) as [u [HU EU]].
  assert (Es: s=X^^3 *> [0;0] *> u).
  { exact (cut_prefix 10879 10876 _ _ ltac:(apply Nat.leb_le; reflexivity) EU). }
  assert (HF: sideRLs tm (hf^^4266)
    (X^^2437 *> [0] *> Y *> X *> [0] *> X^^1171 *> [0] *> X^^4270 *> [0;0] *> t)
    (X^^304 *> [0] *> Y *> X^^2134 *> [0] *> X^^1171 *> [0] *> X *> s)).
  { change (sideRLs tm (hf^^4266)
      ((X^^2437++sep true) *> markers [1;1170]%nat (X^^4269 *> [0;0] *> t))
      ((X^^304++sep true) *> markers [2134;1170]%nat s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 2133 304 true)|].
    exact (h_columns [1170]%nat 2133 1 _ _ H8532). }
  exists u; split; [exact HU|].
  follow HR; rewrite Er; follow (marker_calls 711 145 _ _ HF).
  rewrite Es; unfold root; finish.
Qed.

Definition outer_left p a b :=
  0inf <* [1] <* <[1;1;0;1;1] <* Dr^^p <* <[1;1;0;1;1] <*
    Dr^^(1+a) <* <[1;1;0;0;1;1] <* Dr^^(2+b).

Lemma nested_even4_prepare p a b c r s:
  sideRLs tm (h^^3) r s ->
  root (X^^(1+p) *> [0] *> X^^(3+a) *> [0] *> Y *>
    X^^(1+b) *> [0] *> X^^(1+c) *> [0] *> X^^4 *> [0;0] *> r) -->+
  pending c (outer_left p a b <* [1]) s.
Proof. intro H; unfold root, outer_left, pending; finish_calls H. Qed.

Lemma outer_F_finish p a b d r s:
  sideRLs tm h r s ->
  outer_left p a b <* [1] <{{F}} [1;0] *> Y *> X^^d *> [0;0] *> r -->+
  root (X^^(2+p) *> [0] *> X^^a *> [0] *> Y *> X^^(5+b+d) *> [0;0] *> s).
Proof. intro H; unfold root, outer_left; finish_calls H. Qed.

Lemma init_outer_return:
  exists r, Num true 7197 r /\
    c0 -->* root (X^^858 *> [0] *> X^^302 *> [0] *> Y *> X^^6993 *> [0;0] *> r).
Proof.
  destruct init_nested_even4 as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  destruct (Num_pending 1170 (outer_left 856 302 2133 <* [1])
    false 10879 0 _ HS ltac:(apply Nat.leb_le; reflexivity)) as [t [HT HP]].
  destruct (Num_E_even_inv 7196 _ HT) as [u [HU EU]].
  assert (Et: t=X^^4855 *> [0;0] *> u).
  { exact (cut_prefix 7197 2342 _ _ ltac:(apply Nat.leb_le; reflexivity) EU). }
  destruct (Num_add 1 _ _ _ HU) as [v [HV H1]].
  exists v; split; [exact HV|].
  follow HR; follow100 (nested_even4_prepare 856 302 2133 1170 _ _ H3).
  follow100 HP; rewrite Et.
  apply progress_evstep, (outer_F_finish 856 302 2133 4855), H1.
Qed.

Lemma init_final_birth:
  exists r, CutNum false 14694 205 r /\
    c0 -->* root (X^^958 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_outer_return as [r [HN HR]].
  destruct (Num_add 150 _ _ _ HN) as [s [HS H150]].
  assert (HF: sideRLs tm (hf^^600)
    (X^^301 *> [0] *> Y *> X^^6993 *> [0;0] *> r)
    (X *> [0] *> Y *> X^^7143 *> [0;0] *> s)).
  { change (sideRLs tm (hf^^600)
      ((X^^301++sep true) *> ((X^^6993++[0;0]) *> r))
      ((X^^1++sep true) *> ((X^^7143++[0;0]) *> s))).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 300 1 true)|].
    eapply segRLs_sideRLs_concat; [exact (h_pairs_even 150 6992)|exact H150]. }
  exists (X^^7143 *> [0;0] *> s); split.
  - unfold CutNum; applys_eq (Num_E_even 7347 s HS); flia.
  - follow HR; exact (marker_calls 100 857 _ _ HF).
Qed.

Lemma init_final_marked_even:
  exists r, Num true 10221 r /\
    c0 -->* root (X *> [0] *> X^^2874 *> [0] *> X^^4272 *> [0;0] *> r).
Proof.
  destruct init_final_birth as [r [HN HR]].
  destruct (CutNum_birth 957 _ _ _ _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HB]].
  destruct (Num_E_even_inv 10221 _ HS) as [t [HT ET]].
  assert (Es: s=X^^4272 *> [0;0] *> t).
  { exact (cut_prefix 10222 5950 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  exists t; split; [exact HT|].
  follow HR; follow100 HB; rewrite Es; unfold root; finish.
Qed.

Lemma final_marked_first_half p a r s:
  sideRLs tm (h^^2) r s ->
  root (X^^(1+p) *> [0] *> X^^(1+a) *> [0] *> X^^6 *> [0;0] *> r) -->+
  root ([0] *> X^^(1+p) *> [0] *> X^^(1+a) *> [0] *> X^^4 *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_final_leading_zero:
  exists r, Num true 14489 r /\
    c0 -->* root ([0] *> X^^712 *> [0] *> X^^2874 *> [0] *> X^^4 *> [0;0] *> r).
Proof.
  destruct init_final_marked_even as [r [HN HR]].
  destruct (Num_add 4266 _ _ _ HN) as [s [HS H4266]].
  assert (HF: sideRLs tm (hf^^8532)
    (X^^4271 *> [0;0] *> r) (X^^5 *> [0;0] *> s)).
  { change (sideRLs tm (hf^^8532) ((X^^4271++sep false) *> r) ((X^^5++sep false) *> s)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 4266 5 false)|exact H4266]. }
  destruct (Num_add 2 _ _ _ HS) as [t [HT H2]].
  exists t; split; [exact HT|].
  follow HR; follow (marker_calls 711 0 _ _ (F_markers 4266 2873 _ _ HF)).
  apply progress_evstep, (final_marked_first_half 711 2873), H2.
Qed.

Lemma leading_marked_even4_prepare p b r s:
  sideRLs tm (h^^3) r s ->
  root ([0] *> X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^4 *> [0;0] *> r) -->+
  pending b (0inf <* [1;1] <* Dr^^(1+p) <* [1]) s.
Proof. intro H; unfold root, pending; finish_calls H. Qed.

Lemma D1_F_finish p r s:
  sideRLs tm hf r s ->
  0inf <* [1;1] <* Dr^^(1+p) <* [1] <{{F}} [1;0] *> Y *> r -->+
  root (X^^(4+p) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma init_simple_num:
  exists r, Num false 11555 r /\ c0 -->* root (X^^6524 *> [0] *> Y *> r).
Proof.
  destruct init_final_leading_zero as [r [HN HR]].
  destruct (Num_add 3 _ _ _ HN) as [s [HS H3]].
  destruct (Num_pending 2873 (0inf <* [1;1] <* Dr^^712 <* [1])
    true 14492 0 _ HS ltac:(apply Nat.leb_le; reflexivity)) as [t [HT HP]].
  destruct (CutNum_Fs 1 _ _ _ _ HT ltac:(apply Nat.leb_le; reflexivity))
    as [u [HU H1]].
  destruct (Num_O_odd_inv 11555 _ HU) as [v [HV EV]].
  assert (Eu: u=X^^5809 *> [0] *> Y *> v).
  { exact (cut_prefix 11558 5749 _ _ ltac:(apply Nat.leb_le; reflexivity) EV). }
  exists v; split; [exact HV|].
  follow HR; follow100 (leading_marked_even4_prepare 711 2873 _ _ H3).
  follow100 HP; follow100 (D1_F_finish 711 _ _ H1).
  rewrite Eu; unfold root; finish.
Qed.

Lemma marked_even5_half p a r s:
  sideRLs tm (h^^2) r s ->
  root (X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X^^5 *> [0;0] *> r) -->+
  root ([0] *> X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X^^3 *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma leading_marked_even3_prepare p a r s:
  sideRLs tm (h^^2) r s ->
  root ([0] *> X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X^^3 *> [0;0] *> r) -->+
  pending a (0inf <* [1;1] <* Dr^^(1+p) <* <[1;1;0;1;1]) s.
Proof. intro H; unfold root, pending; finish_calls H. Qed.

Lemma marked11011_finish l r s:
  sideRLs tm (hf^^3) r s ->
  l <* <[1;1;0;1;1] <{{F}} [1;0] *> Y *> r -->+
  l <{{A}} [0;0;0;0] *> X^^2 *> s.
Proof. intro H; finish_calls H. Qed.

Lemma D11_zero4_cleanup p r:
  0inf <* [1;1] <* Dr^^p <{{A}} [0;0;0;0] *> r -->+
  root (X^^(1+p) *> [0;0;0;0] *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_marked_even3 p a b j d r:
  CutNum b j d r -> d*2+a<=j ->
  exists s, CutNum b (j+8+a*3) (d+3+a*2) s /\
    root ([0] *> X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(2+p) *> [0;0;0;0] *> s).
Proof.
  intros HN Hd.
  destruct (CutNum_hs 2 _ _ _ _ HN ltac:(lia)) as [s [HS H2]].
  destruct (Num_pending a (0inf <* [1;1] <* Dr^^(1+p) <* <[1;1;0;1;1])
    _ _ _ _ HS ltac:(lia)) as [t [HT HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HT ltac:(lia)) as [u [HU H3]].
  exists (X^^2 *> u); split.
  - apply CutNum_prepend; applys_eq HU; flia.
  - eapply progress_trans; [apply leading_marked_even3_prepare, H2|].
    eapply progress_trans; [exact HP|].
    eapply progress_trans; [apply marked11011_finish, H3|].
    apply D11_zero4_cleanup.
Qed.

Lemma init_high_a1:
  exists r, Num true 31127 r /\
    c0 -->* root (X^^5189 *> [0] *> X *> [0;0] *> r).
Proof.
  destruct init_simple_num as [r [HN HR]].
  destruct (Num_normal_odd 6522 _ _ _ HN) as [s [HS HD]].
  destruct (Num_E_even_inv 15563 _ ltac:(applys_eq HS; flia)) as [t [HT ET]].
  destruct (Num_markers 5188 0 0 _ _ _ HT) as [u [HU HM]].
  exists u; split; [exact HU|].
  follow HR; follow100 HD; rewrite ET; exact HM.
Qed.

Lemma init_high_odd2:
  exists r, Num false 36314 r /\
    c0 -->* root (X^^4324 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_high_a1 as [r [HN HR]].
  destruct (Num_pending 5188 (0inf <* [1]) true 31127 0 _ HN
    ltac:(apply Nat.leb_le; reflexivity)) as [s [HS HP]].
  destruct (Num_O_even_inv 23345 _ ltac:(applys_eq HS; flia)) as [t [HT ET]].
  assert (Es: s=X^^12970 *> [0;0] *> t).
  { exact (cut_prefix 23348 10378 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  destruct (Num_add 12969 _ _ _ HT) as [u [HU H12969]].
  assert (HF: sideRLs tm (hf^^25938)
    (X^^12970 *> [0] *> Y *> t) (X *> [0] *> Y *> u)).
  { change (sideRLs tm (hf^^25938) ((X^^12970++sep true) *> t) ((X^^1++sep true) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 12969 1 true)|exact H12969]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (a1_prepare 5188 r); follow100 HP; rewrite Es.
  follow100 (a1_even_finish 12970 t); exact (marker_calls 4323 0 _ _ HF).
Qed.

Lemma init_high_T:
  exists r, Num true 36313 r /\
    c0 -->* root (X^^865 *> [0] *> X^^12972 *> [0] *> X^^5 *> [0;0] *> r).
Proof.
  destruct init_high_odd2 as [r [HN HR]].
  destruct (CutNum_birth 4323 false 36314 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HB]].
  destruct (Num_E_even_inv 31129 _ ltac:(applys_eq HS; flia)) as [t [HT ET]].
  assert (Es: s=X^^5189 *> [0;0] *> t).
  { exact (cut_prefix 31130 25941 _ _ ltac:(apply Nat.leb_le; reflexivity) ET). }
  destruct (Num_add 5184 _ _ _ HT) as [u [HU H5184]].
  assert (HF: sideRLs tm (hf^^10368)
    (X^^5188 *> [0;0] *> t) (X^^4 *> [0;0] *> u)).
  { change (sideRLs tm (hf^^10368) ((X^^5188++sep false) *> t) ((X^^4++sep false) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 5184 4 false)|exact H5184]. }
  exists u; split; [exact HU|].
  follow HR; follow100 HB; rewrite Es.
  exact (marker_calls 864 0 _ _ (F_markers 5184 12971 _ _ HF)).
Qed.

Lemma init_high_zero4:
  exists r, CutNum true 75233 25943 r /\
    c0 -->* root (X^^866 *> [0;0;0;0] *> r).
Proof.
  destruct init_high_T as [r [HN HR]].
  destruct (Num_add 2 _ _ _ HN) as [s [HS H2]].
  destruct (CutNum_marked_even3 864 12970 true 36315 0 _ HS
    ltac:(apply Nat.leb_le; reflexivity)) as [t [HT HC]].
  exists t; split; [exact HT|].
  follow HR; follow100 (marked_even5_half 864 12970 _ _ H2).
  apply progress_evstep, HC.
Qed.

Lemma d3_ten p b r s:
  sideRLs tm (hf^^10) r s ->
  root (X^^(1+p) *> [0] *> X^^(2+b) *> [0] *> X *> [0] *> X^^2 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(6+b) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_zero4_even q b j d r:
  CutNum b j d r -> d*2<=1+j ->
  exists s, CutNum b (j+7+q*6) d s /\
    root (X^^(4+q*2) *> [0;0;0;0] *> r) -->+
    root (X^^(2+q) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intros HN Hd.
  destruct (CutNum_hs 1 _ _ _ _ HN Hd) as [r1 [HN1 H1]].
  destruct (CutNum_hs (3+q*3) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 H2]].
  assert (HH: sideRLs tm (h^^(6+q*6))
    (X *> [0] *> Y *> r1) (X^^(4+q*3) *> [0] *> Y *> r2)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    change (sideRLs tm (h^^(6+q*6)) ((X^^1++[0]++Y) *> r1)
      ((X^^(4+q*3)++[0]++Y) *> r2)).
    eapply segRLs_sideRLs_concat; [applys_eq (h_pairs_odd (3+q*3) 1); flia|exact H2]. }
  destruct (CutNum_hs (3+q*3) _ _ _ _ HN2 ltac:(lia)) as [s [HS H3]].
  assert (HF: sideRLs tm (hf^^(6+q*6))
    (X^^(4+q*3) *> [0] *> Y *> r2) (X *> [0] *> Y *> s)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    change (sideRLs tm (hf^^(6+q*6)) ((X^^(4+q*3)++sep true) *> r2)
      ((X^^1++sep true) *> s)).
    eapply segRLs_sideRLs_concat; [applys_eq (F_pairs (3+q*3) 1 true); flia|exact H3]. }
  exists s; split; [applys_eq HS; flia|].
  eapply progress_trans; [applys_eq (zero4_prepare (1+q*2) _ _ H1); flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (1+q*2) _ _ ltac:(applys_eq HH; flia)); flia|].
  follow (marker_calls (1+q) 0 _ _ ltac:(applys_eq HF; flia)); unfold root; finish.
Qed.

Lemma CutNum_zero4_odd q b j d r:
  CutNum b j d r -> d*2<=1+j ->
  exists s, CutNum b (j+6+q*6) d s /\
    root (X^^(3+q*2) *> [0;0;0;0] *> r) -->+
    root (X^^(2+q) *> [0] *> X *> [0;0] *> s).
Proof.
  intros HN Hd.
  destruct (CutNum_hs 1 _ _ _ _ HN Hd) as [r1 [HN1 H1]].
  destruct (CutNum_hs (1+q*3) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 H2]].
  assert (HH: sideRLs tm (h^^(2+q*6))
    (X *> [0] *> Y *> r1) (X^^(2+q*3) *> [0] *> Y *> r2)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    change (sideRLs tm (h^^(2+q*6)) ((X^^1++[0]++Y) *> r1)
      ((X^^(2+q*3)++[0]++Y) *> r2)).
    eapply segRLs_sideRLs_concat; [applys_eq (h_pairs_odd (1+q*3) 1); flia|exact H2]. }
  destruct (CutNum_hs 1 _ _ _ _ HN2 ltac:(lia)) as [r3 [HN3 H3]].
  assert (HH3: sideRLs tm (h^^(3+q*6))
    (X *> [0] *> Y *> r1) (X^^(3+q*3) *> [0;0] *> r3)).
  { replace (3+q*6) with ((2+q*6)+1) by lia; rewrite lpow_add.
    eapply sideRLs_trans; [exact HH|].
    repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    change (sideRLs tm h ((X^^(2+q*3)++[0]++Y) *> r2)
      ((X^^(3+q*3)++[0;0]) *> r3)).
    eapply segRLs_sideRLs_concat; [applys_eq (digit_odd_all (2+q*3)); flia|exact H3]. }
  destruct (CutNum_hs (3+q*3) _ _ _ _ HN3 ltac:(lia)) as [s [HS H4]].
  exists s; split; [applys_eq HS; flia|].
  eapply progress_trans; [applys_eq (zero4_prepare (q*2) _ _ H1); flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (q*2) _ _ ltac:(applys_eq HH3; flia)); flia|].
  applys_eq (marker_hcalls (1+q) 0 0 _ _ ltac:(applys_eq H4; flia)); flia.
Qed.

Lemma CutNum_marked_even5 p a b j d r:
  CutNum b j d r -> d*2+a<=j ->
  exists s, CutNum b (j+10+a*3) (d+3+a*2) s /\
    root (X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X^^5 *> [0;0] *> r) -->+
    root (X^^(2+p) *> [0;0;0;0] *> s).
Proof.
  intros HN Hd.
  destruct (CutNum_hs 2 _ _ _ _ HN ltac:(lia)) as [t [HT H2]].
  destruct (CutNum_marked_even3 p a _ _ _ _ HT ltac:(lia)) as [s [HS HC]].
  exists s; split; [applys_eq HS; flia|].
  eapply progress_trans; [apply marked_even5_half, H2|exact HC].
Qed.

Lemma init_next_T:
  exists r, Num false 51880 r /\
    c0 -->* root (X^^1946 *> [0] *> X^^1299 *> [0] *> X^^5 *> [0;0] *> r).
Proof.
  destruct init_high_zero4 as [r [HN HR]].
  destruct (CutNum_zero4_even 431 _ _ _ _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HN0]].
  destruct (CutNum_birth 432 true 77826 25943 _ HS ltac:(apply Nat.leb_le; reflexivity))
    as [t [HT HB]].
  destruct (Num_O_even_inv 40210 _ ltac:(applys_eq HT; flia)) as [u [HU EU]].
  assert (Et: t=X^^11675 *> [0;0] *> u).
  { exact (cut_prefix 40213 28538 _ _ ltac:(apply Nat.leb_le; reflexivity) EU). }
  destruct (Num_add 11670 _ _ _ HU) as [v [HV H11670]].
  assert (HF: sideRLs tm (hf^^23340)
    (X^^11674 *> [0;0] *> u) (X^^4 *> [0;0] *> v)).
  { change (sideRLs tm (hf^^23340) ((X^^11674++sep false) *> u) ((X^^4++sep false) *> v)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 11670 4 false)|exact H11670]. }
  exists v; split; [exact HV|].
  follow HR; follow100 HN0; follow100 HB; rewrite Et.
  exact (marker_calls 1945 0 _ _ (F_markers 11670 1298 _ _ HF)).
Qed.

Lemma init_next_zero4:
  exists r, CutNum false 55781 2597 r /\
    c0 -->* root (X^^1947 *> [0;0;0;0] *> r).
Proof.
  destruct init_next_T as [r [HN HR]].
  destruct (CutNum_marked_even5 1945 1297 false 51880 0 _ HN
    ltac:(apply Nat.leb_le; reflexivity)) as [s [HS HT]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HT].
Qed.

Lemma init_next_a1:
  exists r, CutNum false 61619 2597 r /\
    c0 -->* root (X^^974 *> [0] *> X *> [0;0] *> r).
Proof.
  destruct init_next_zero4 as [r [HN HR]].
  destruct (CutNum_zero4_odd 972 _ _ _ _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HN1]].
  exists s; split; [exact HS|follow HR; apply progress_evstep, HN1].
Qed.

(* A parameterized a1/digit interface and the next finite T/S return. *)
Lemma Num_odd_split b k r:
  Num b ((if b then 5 else 1)+k*2) r ->
  exists s, Num (negb b) k s /\
    r=X^^((if b then 3 else 1)+k) *> [0] *> Y *> s.
Proof. destruct b; [apply Num_O_odd_inv|apply Num_E_odd_inv]. Qed.

Lemma CutNum_a1_odd q b j d k r:
  CutNum b j d r -> d*2+q+2<=j ->
  j+(1+q)*3=(if b then 5 else 1)+k*2 ->
  d+(1+q)*2<(if b then 3 else 1)+k ->
  exists s, Num (negb b) (1+k) s /\
    root (X^^(1+q) *> [0] *> X *> [0;0] *> r) -->+
    root (X *> [0] *> X^^(2+((if b then 3 else 1)+k-(d+(1+q)*2))) *> [0;0] *> s).
Proof.
  intros HN Hd Hj Ha.
  destruct (Num_pending q (0inf <* [1]) _ _ _ _ HN Hd) as [s [HS HP]].
  rewrite Hj in HS; destruct (Num_odd_split b k _ HS) as [t [HT ET]].
  assert (Es: s=X^^(1+((if b then 3 else 1)+k-(d+(1+q)*2)-1)) *> [0] *> Y *> t).
  { rewrite (cut_prefix ((if b then 3 else 1)+k) (d+(1+q)*2) _ _ ltac:(lia) ET).
    replace (1+((if b then 3 else 1)+k-(d+(1+q)*2)-1))
      with ((if b then 3 else 1)+k-(d+(1+q)*2)) by lia; reflexivity. }
  destruct (Num_inc HT) as [u [HU H1]].
  exists u; split; [exact HU|].
  eapply progress_trans; [apply a1_prepare|].
  eapply progress_trans; [exact HP|].
  rewrite Es; applys_eq (a1_digit_finish ((if b then 3 else 1)+k-(d+(1+q)*2)-1) _ _ H1); flia.
Qed.

Lemma YY_hs m r s:
  sideRLs tm (hf^^(4+m*4)) r s ->
  sideRLs tm (h^^(1+m)) (Y *> Y *> r) (markers [1+m;0]%nat s).
Proof.
  intro H; rewrite lpow_add in H.
  destruct (sideRLs_split H) as [t [H4 Hm]].
  change (sideRLs tm (h++h^^m) (Y *> Y *> r) (markers [1+m;0]%nat s)).
  eapply sideRLs_trans; [apply YY_h,H4|].
  applys_eq (h_columns [0]%nat m 1 _ _ Hm); flia.
Qed.

Lemma Num_two_markers m p b a e chi j r:
  Num chi j r -> exists s, Num chi (j+m*6) s /\
    root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^(1+a+m*6) *> sep e *> r) -->*
    root (X^^(1+p+m) *> [0] *> X^^(1+b) *> [0] *> X^^(1+a) *> sep e *> s).
Proof.
  intro HN; destruct (Num_add (m*6) _ _ _ HN) as [s [HS HH]].
  assert (HF: sideRLs tm (hf^^(m*12))
    (X^^(a+m*6) *> sep e *> r) (X^^a *> sep e *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat; [applys_eq (F_pairs (m*6) a e); flia|exact HH]. }
  exists s; split; [exact HS|].
  applys_eq (marker_calls m p _ _ (F_markers (m*6) b _ _ ltac:(applys_eq HF; flia))); flia.
Qed.

Lemma init_second_E2:
  exists r, Num true 59997 r /\
    c0 -->* root (X^^9243 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_next_a1 as [r [HN HR]].
  destruct (CutNum_a1_odd 973 false 61619 2597 32270 _ HN
    ltac:(apply Nat.leb_le; reflexivity) eq_refl ltac:(apply Nat.ltb_lt; reflexivity))
    as [s [HS HA]].
  destruct (Num_markers 9242 0 1 _ _ _ HS) as [t [HT HM]].
  exists t; split; [exact HT|].
  follow HR; follow100 HA; exact HM.
Qed.

Lemma Num_digit_split (b e:bool) k r:
  Num b ((if b then 4 else 0)+(if e then 1 else 0)+k*2) r ->
  exists s, Num (negb b) k s /\
    r=X^^((if b then 3 else 1)+k) *> sep e *> s.
Proof.
  destruct b,e; cbn [negb sep];
    [apply Num_O_odd_inv|apply Num_O_even_inv|apply Num_E_odd_inv|apply Num_E_even_inv].
Qed.

Lemma CutNum_digit_tail (b e:bool) j k d a r:
  CutNum b j d r -> j=(if b then 4 else 0)+(if e then 1 else 0)+k*2 ->
  d+a=(if b then 3 else 1)+k ->
  exists s, Num (negb b) k s /\ r=X^^a *> sep e *> s.
Proof.
  intros HN Hj Ha; rewrite Hj in HN.
  destruct (Num_digit_split b e k _ HN) as [s [HS ET]].
  exists s; split; [exact HS|].
  rewrite (cut_prefix ((if b then 3 else 1)+k) d _ _ ltac:(lia) ET).
  replace ((if b then 3 else 1)+k-d) with a by lia; reflexivity.
Qed.

Lemma root_X_add p a b r:
  root (X^^p *> [0] *> X^^a *> X^^b *> r)=
  root (X^^p *> [0] *> X^^(a+b) *> r).
Proof. rewrite <-(Str_app_assoc (X^^a) (X^^b)), <-lpow_add; reflexivity. Qed.

Lemma Num_a2_cleanup a e b j r:
  Num b j r -> exists s, Num b (j+6) s /\
    root (X *> [0;0;0] *> X^^(7+a) *> sep e *> r) -->+
    root (X^^2 *> [0] *> X *> [0] *> X^^(1+a) *> sep e *> s).
Proof.
  intro HN; destruct (Num_add 6 _ _ _ HN) as [s [HS HH]].
  assert (HF: sideRLs tm (hf^^12)
    (X^^(6+a) *> sep e *> r) (X^^a *> sep e *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat; [applys_eq (F_pairs 6 a e); flia|exact HH]. }
  exists s; split; [exact HS|applys_eq (a2_cleanup _ _ HF); flia].
Qed.

Lemma init_second_odd5:
  exists r, Num false 69235 r /\
    c0 -->* root (X^^4230 *> [0] *> X *> [0] *> X^^5 *> [0] *> Y *> r).
Proof.
  destruct init_second_E2 as [r [HN HR]].
  destruct (CutNum_a2 9241 true 59997 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HA]].
  destruct (CutNum_digit_tail true true _ 43861 _ 25379 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_a2_cleanup 25372 true _ _ _ HT) as [u [HU HC]].
  destruct (Num_two_markers 4228 1 0 4 true _ _ _ HU) as [v [HV HM]].
  exists v; split; [exact HV|].
  follow HR; follow100 HA; rewrite Es; follow100 HC; exact HM.
Qed.

Lemma init_second_D3:
  exists r, Num true 69240 r /\
    c0 -->* root (X^^771 *> [0] *> X^^12691 *> [0] *> X *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_second_odd5 as [r [HN HR]].
  destruct (Num_add 5 _ _ _ HN) as [r5 [HN5 H5]].
  destruct (CutNum_Fs 50760 false 69240 0 _ HN5 ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H50760]].
  destruct (CutNum_digit_tail false false _ 60000 _ 9241 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_add 9240 _ _ _ HT) as [u [HU H9240]].
  assert (HF: sideRLs tm (hf^^18480) s (X *> [0;0] *> u)).
  { rewrite Es; change (sideRLs tm (hf^^18480)
      ((X^^9241++sep false) *> t) ((X^^1++sep false) *> u)).
    eapply segRLs_sideRLs_concat; [exact (F_pairs 9240 1 false)|exact H9240]. }
  exists u; split; [exact HU|].
  follow HR; follow100 (odd_five 4229 _ _ H5).
  follow100 (normal_calls 4229 _ _ (YY_hs 12689 _ _ H50760)).
  follow (marker_calls 770 0 _ _ (F_columns [12690;0]%nat 4620 _ _ HF)).
  unfold root; finish.
Qed.

Lemma init_third_a1:
  exists r, Num false 81933 r /\
    c0 -->* root (X^^16542 *> [0] *> X *> [0;0] *> r).
Proof.
  destruct init_second_D3 as [r [HN HR]].
  destruct (CutNum_Fs 10 true 69240 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS H10]].
  destruct (CutNum_digit_tail true false _ 34623 _ 34616 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_markers 15770 771 0 _ _ _ HT) as [u [HU HM]].
  exists u; split; [exact HU|].
  follow HR; follow100 (d3_ten 770 12689 _ _ H10); rewrite Es.
  rewrite root_X_add; replace (12695+34616) with 47311 by (apply Nat.eqb_eq; reflexivity); exact HM.
Qed.

Lemma init_image_E3:
  exists r, Num false 109375 r /\
    c0 -->* root (X^^14597 *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_third_a1 as [r [HN HR]].
  destruct (CutNum_a1_odd 16541 false 81933 0 65779 _ HN
    ltac:(apply Nat.leb_le; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity)
    ltac:(apply Nat.ltb_lt; reflexivity))
    as [s [HS HA]].
  destruct (Num_markers 10899 0 0 _ _ _ HS) as [t [HT HM]].
  destruct (CutNum_a1_odd 10899 true 98477 0 65586 _ HT
    ltac:(apply Nat.leb_le; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity)
    ltac:(apply Nat.ltb_lt; reflexivity))
    as [u [HU HA2]].
  destruct (Num_markers 14596 0 2 _ _ _ HU) as [v [HV HM2]].
  exists v; split; [exact HV|].
  follow HR; follow100 HA; follow HM; follow100 HA2; exact HM2.
Qed.

Lemma init_image_U:
  exists r, Num false 218758 r /\
    c0 -->* root (X^^36461 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_image_E3 as [r [HN HR]].
  destruct (Num_a3 14596 _ _ _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HA]].
  destruct (CutNum_digit_tail false true _ 76585 _ 47392 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_normal_odd 47390 _ _ _ HT) as [u [HU HD]].
  destruct (CutNum_digit_tail true false _ 109378 0 109381 _ HU
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [v [HV EV]].
  destruct (Num_markers 36460 0 1 _ _ _ HV) as [w [HW HM]].
  exists w; split; [exact HW|].
  follow HR; follow100 HA; rewrite Es; follow100 HD; rewrite EV; exact HM.
Qed.

Lemma init_second_zero4:
  exists r, CutNum true 255224 1 r /\
    c0 -->* root (X^^15193 *> [0;0;0;0] *> r).
Proof.
  destruct init_image_U as [r [HN HR]].
  destruct (CutNum_a2 36459 false 218758 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HA]].
  destruct (CutNum_digit_tail false false _ 164071 _ 91151 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_a2_cleanup 91144 false _ _ _ HT) as [u [HU HC]].
  destruct (Num_two_markers 15190 1 0 4 false _ _ _ HU) as [v [HV HM]].
  destruct (CutNum_Fs 7 true 255217 0 _ HV ltac:(apply Nat.leb_le; reflexivity))
    as [w [HW H7]].
  exists (X^^6 *> w); split; [apply CutNum_prepend, HW|].
  follow HR; follow100 HA; rewrite Es; follow100 HC; follow HM.
  apply progress_evstep, (two_even5 15191), H7.
Qed.

(* The separate B21 even-zero caller: its bare-F guard is exhausted,
   so retain T1 and prove the real return rather than inventing F(00). *)
Notation T1r := <[1;1;0;1;1;0;0;1;1;0;0;1;1].

Lemma two_even4 p r s:
  sideRLs tm (hf^^8) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^4 *> [0;0] *> r) -->+
  root (X^^(8+p) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma birth_last_five b r s:
  sideRLs tm (hf^^5) r s ->
  birth 2 (1+b) r -->+
  0inf <* [1] <* Dr <* [1;1] <* Dr^^(4+b) <* T1r {{B}}> s.
Proof.
  intro H; unfold birth.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^4) H) as [t [H1 H4]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H4.
Qed.

Lemma birth_evenzero b r s:
  sideRLs tm h r s ->
  0inf <* [1] <* Dr <* [1;1] <* Dr^^b <* T1r {{B}}> [0;0] *> r -->+
  root ([0] *> X *> [0;0] *> X^^b *> [0] *> X^^2 *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma birth_underflow p r t s:
  sideRLs tm (hf^^(8+p*6)) r ([0;0] *> t) -> sideRLs tm h t s ->
  root (X^^(2+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root ([0] *> X *> [0;0] *> X^^(4+p*3) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intros H H1; replace (8+p*6) with (3+(p*6+5)) in H by lia.
  rewrite (lpow_add _ 3 (p*6+5) hf) in H.
  destruct (sideRLs_split H) as [r3 [H3 Hs]]; rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm H5]].
  eapply progress_trans; [applys_eq (birth_prepare (1+p) _ _ H3); flia|].
  eapply evstep_progress_trans; [applys_eq (birth_cycles p 1 0 _ _ Hm); flia|].
  eapply progress_trans; [apply birth_last_five, H5|apply birth_evenzero, H1].
Qed.

Lemma Num_birth_evenzero p r:
  Num true (6+p*6) r ->
  exists s, Num false (6+p*6) s /\
    root (X^^(2+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root ([0] *> X *> [0;0] *> X^^(4+p*3) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (CutNum_Fs (8+p*6) true (6+p*6) 0 _ HN ltac:(lia))
    as [s [HS HF]].
  destruct (Num_O_even_inv (5+p*6) _ ltac:(applys_eq HS; flia)) as [t [HT ET]].
  assert (Es: s=[0;0] *> t).
  { applys_eq (cut_prefix (8+p*6) (8+p*6) _ _ ltac:(lia) ltac:(applys_eq ET; flia));
      rewrite Nat.sub_diag; reflexivity. }
  destruct (Num_inc HT) as [u [HU H1]].
  exists u; split; [applys_eq HU; flia|].
  apply (birth_underflow p _ t); [rewrite <-Es; exact HF|exact H1].
Qed.

Lemma zero_X_even2 b r s:
  sideRLs tm h r s ->
  root ([0] *> X *> [0;0] *> X^^b *> [0] *> X^^2 *> [0;0] *> r) -->+
  root (X *> [0] *> X^^(2+b) *> [0] *> X *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.


(* Native initialization continues through the complete B21 family,
   critical E caller, and sourced C return. All counts below are symbolic;
   only the final family parameter is instantiated at the native entry. *)
(* TM23B21Entry: symbolic complete-root composition. *)
Lemma Num_marker_phase m p a e chi j r:
  Num chi j r -> exists s, Num chi (j+m*3) s /\
    root (X^^(1+p) *> [0] *> X^^(1+a+m*3) *> sep e *> r) -->*
    root (X^^(1+p+m) *> [0] *> X^^(1+a) *> sep e *> s).
Proof.
  intro HN; destruct (Num_add (m*3) _ _ _ HN) as [s [HS HH]].
  assert (HF: sideRLs tm (hf^^(m*6))
    (X^^(a+m*3) *> sep e *> r) (X^^a *> sep e *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat; [applys_eq (F_pairs (m*3) a e); flia|exact HH]. }
  exists s; split; [exact HS|applys_eq (marker_calls m p _ _ HF); flia].
Qed.

Lemma root_X_front a b r:
  root (X^^a *> X^^b *> r)=root (X^^(a+b) *> r).
Proof. rewrite <-Str_app_assoc, <-lpow_add; reflexivity. Qed.

Lemma CutNum_root p d chi j r:
  CutNum chi j d r -> exists s, Num chi j s /\
    root (X^^(p+d) *> r)=root (X^^p *> s).
Proof. intro H; exists (X^^d *> r); split; [exact H|symmetry; apply root_X_front]. Qed.

Lemma init_B21_a2:
  exists r, Num false 308395 r /\
    c0 -->* root (X^^48868 *> [0] *> X^^2 *> [0;0] *> r).
Proof.
  destruct init_second_zero4 as [r [HN HR]].
  destruct (CutNum_zero4_odd 7595 _ _ _ _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HZ]].
  destruct (CutNum_a1_odd 7596 true 300800 1 161793 _ HS
    ltac:(apply Nat.leb_le; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity)
    ltac:(apply Nat.ltb_lt; reflexivity)) as [t [HT HA]].
  destruct (Num_markers 48867 0 1 _ _ _ HT) as [u [HU HM]].
  exists u; split; [exact HU|follow HR; follow100 HZ; follow100 HA; exact HM].
Qed.

Lemma init_B21_even4:
  exists r, Num true 357262 r /\
    c0 -->* root (X^^21628 *> [0] *> X *> [0] *> X^^4 *> [0;0] *> r).
Proof.
  destruct init_B21_a2 as [r [HN HR]].
  destruct (CutNum_a2 48866 false 308395 0 _ HN ltac:(apply Nat.leb_le; reflexivity))
    as [s [HS HA]].
  destruct (CutNum_digit_tail false false _ 227500 _ 129766 _ HS
    ltac:(apply Nat.eqb_eq; reflexivity) ltac:(apply Nat.eqb_eq; reflexivity))
    as [t [HT Es]].
  destruct (Num_a2_cleanup 129759 false _ _ _ HT) as [u [HU HC]].
  destruct (Num_two_markers 21626 1 0 3 false _ _ _ HU) as [v [HV HM]].
  exists v; split; [exact HV|].
  follow HR; follow100 HA; rewrite Es; follow100 HC; exact HM.
Qed.

Lemma Num_even4_B21 u v r:
  Num true (10+v*6) r -> exists s, Num true (36+u*6+v*12) s /\
    root (X^^(2+u*2) *> [0] *> X *> [0] *> X^^4 *> [0;0] *> r) -->+
    root (X^^(7+u+v*2) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (CutNum_Fs 8 true (10+v*6) 0 _ HN ltac:(lia))
    as [s [HS H8]].
  destruct (CutNum_root (1+u*2) 8 _ _ _ HS) as [t [HT Es]].
  destruct (CutNum_digit_tail true false _ (7+v*3) 0 (10+v*3) _ HT ltac:(lia) ltac:(lia))
    as [t1 [HN1 Et]].
  destruct (Num_normal (9+u*2+v*3) _ _ _ HN1) as [t2 [HN2 HN0]].
  destruct (CutNum_digit_tail false true _ (18+u*3+v*6) 0 (19+u*3+v*6) _ HN2
    ltac:(lia) ltac:(lia)) as [t3 [HN3 E2]].
  destruct (Num_marker_phase (6+u+v*2) 0 1 true _ _ _ HN3) as [z [HZ HM]].
  exists z; split; [applys_eq HZ; flia|].
  eapply progress_trans; [applys_eq (two_even4 (1+u*2) _ _ H8); flia|].
  replace (8+(1+u*2)) with ((1+u*2)+8) by lia; rewrite Es,Et,root_X_front.
  eapply progress_evstep_trans; [applys_eq HN0; flia|].
  rewrite E2.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(19+u*3+v*6) *> sep true *> t3) -->*
    root (X^^(7+u+v*2) *> [0] *> X^^2 *> [0] *> Y *> z)).
  rewrite root_X_add; applys_eq HM; flia.
Qed.

Lemma init_B21:
  exists r, Num true 779418 r /\
    c0 -->* root (X^^129904 *> [0] *> X^^2 *> [0] *> Y *> r).
Proof.
  destruct init_B21_even4 as [r [HN HR]].
  assert (HN0: Num true (10+59542*6) r).
  { replace (10+59542*6) with 357262 by (apply Nat.eqb_eq; reflexivity); exact HN. }
  destruct (Num_even4_B21 10813 59542 _ HN0) as [s [HS HB]].
  exists s; split.
  - replace 779418 with (36+10813*6+59542*12) by (apply Nat.eqb_eq; reflexivity); exact HS.
  - follow HR; apply progress_evstep.
    replace 21628 with (2+10813*2) by (apply Nat.eqb_eq; reflexivity).
    replace 129904 with (7+10813+59542*2) by (apply Nat.eqb_eq; reflexivity); exact HB.
Qed.

(* TM23B21ReturnKernel: symbolic complete-root composition. *)
Lemma D1_zero4_cleanup r:
  0inf <* [1] <* Dr <{{A}} [0;0;0;0] *> r -->+
  root ([0] *> X *> [0;0;0;0] *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_nested_even a b j d r:
  CutNum b j d r -> d*2+a+2<=j ->
  exists s, CutNum b (j+6+a*3) (d+3+a*2) s /\
    root (X *> [0] *> X^^(2+a) *> [0] *> X *> [0;0] *> r) -->+
    root ([0] *> X *> [0;0;0;0] *> s).
Proof.
  intros HN Hd.
  destruct (Num_pending a (0inf <* Wr) _ _ _ _ HN Hd) as [s [HS HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HS ltac:(lia)) as [t [HT H3]].
  exists (X^^2 *> t); split.
  - apply CutNum_prepend; applys_eq HT; flia.
  - eapply progress_trans; [apply nested_even_prepare|].
    eapply progress_trans; [exact HP|].
    eapply progress_trans; [apply (marked11011_finish (0inf <* [1] <* Dr)), H3|].
    apply D1_zero4_cleanup.
Qed.

Lemma zero_X_zero4 r:
  root ([0] *> X *> [0;0;0;0] *> r) -->+
  root (X *> [0] *> X *> [0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma one_odd1 r s:
  sideRLs tm (hf^^3) r s ->
  root (X *> [0] *> X *> [0] *> Y *> r) -->+
  root (X *> [0] *> X^^2 *> [0] *> X^^2 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_one_odd1 b j d r:
  CutNum b j d r -> d*2+1<=j ->
  exists s, CutNum b (j+3) (d+1) s /\
    root (X *> [0] *> X *> [0] *> Y *> r) -->+
    root (X *> [0] *> X^^2 *> [0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_Fs 3 _ _ _ _ HN ltac:(lia)) as [s [HS H3]].
  exists (X^^2 *> s); split; [apply CutNum_prepend; applys_eq HS; flia|apply one_odd1,H3].
Qed.

Lemma two_even6_second p r s:
  sideRLs tm (hf^^12) r s ->
  root (X^^(2+p) *> [0] *> X^^2 *> [0] *> X^^6 *> [0;0] *> r) -->+
  root (X^^(12+p) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

(* TM23B21Return: symbolic complete-root composition. *)
Lemma Num_B21_return n r:
  Num true (42+n*48) r -> exists s, Num true (151+n*150) s /\
    root (X^^(8+n*8) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(26+n*25) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN.
  destruct (Num_birth_evenzero (6+n*8) _ ltac:(applys_eq HN; flia)) as [r1 [HN1 HB]].
  destruct (Num_inc HN1) as [r2 [HN2 H1]].
  destruct (CutNum_nested_even (22+n*24) _ _ 0 _ HN2 ltac:(lia)) as [r3 [HN3 HE]].
  destruct (CutNum_one_odd1 _ _ _ _ HN3 ltac:(lia)) as [r4 [HN4 HO]].
  destruct (CutNum_digit_tail false false _ (59+n*60) _ (12+n*12) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_two_markers (1+n*2) 0 1 5 false _ _ _ HN5) as [r6 [HN6 HM]].
  destruct (CutNum_Fs 12 _ _ 0 _ HN6 ltac:(lia)) as [r7 [HN7 H12]].
  destruct (CutNum_root (n*2) 12 _ _ _ HN7) as [r8 [HN8 E7]].
  destruct (CutNum_digit_tail true true _ (36+n*36) 0 (39+n*36) _ HN8
    ltac:(lia) ltac:(lia)) as [r9 [HN9 E8]].
  destruct (Num_normal_odd (37+n*38) _ _ _ HN9) as [r10 [HN10 HN0]].
  destruct (CutNum_digit_tail false false _ (76+n*75) 0 (77+n*75) _ HN10
    ltac:(lia) ltac:(lia)) as [r11 [HN11 E10]].
  destruct (Num_markers (25+n*25) 0 2 _ _ _ HN11) as [r12 [HN12 HM2]].
  exists r12; split; [applys_eq HN12; flia|].
  eapply progress_trans; [applys_eq HB; flia|].
  eapply progress_trans; [applys_eq (zero_X_even2 (22+n*24) _ _ H1); flia|].
  eapply progress_trans; [exact HE|].
  eapply progress_trans; [apply zero_X_zero4|].
  eapply progress_trans; [exact HO|].
  rewrite E4; eapply evstep_progress_trans; [applys_eq HM; flia|].
  eapply progress_trans; [applys_eq (two_even6_second (n*2) _ _ H12); flia|].
  replace (12+n*2) with (n*2+12) by lia; rewrite E7,E8,root_X_front.
  eapply progress_evstep_trans; [applys_eq HN0; flia|].
  rewrite E10.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(77+n*75) *> sep false *> r11) -->*
    root (X^^(26+n*25) *> [0] *> X^^3 *> [0;0] *> r12)).
  rewrite root_X_add; applys_eq HM2; flia.
Qed.

Lemma Num_Oa3_odd_return n r:
  Num true (13+n*12) r -> exists s, Num true (35+n*24) s /\
    root (X^^(3+n*2) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(7+n*4) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_a3 (2+n*2) _ _ _ HN ltac:(lia)) as [r1 [HN1 HA]].
  destruct (CutNum_digit_tail true true _ (11+n*9) _ (8+n*5) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_normal_odd (6+n*5) _ _ _ HN2) as [r3 [HN3 HN0]].
  destruct (CutNum_digit_tail false false _ (17+n*12) 0 (18+n*12) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_markers (6+n*4) 0 0 _ _ _ HN4) as [s [HS HM]].
  exists s; split; [applys_eq HS; flia|].
  eapply progress_trans; [applys_eq HA; flia|].
  rewrite E1; eapply progress_evstep_trans; [applys_eq HN0; flia|].
  rewrite E3.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(18+n*12) *> sep false *> r4) -->*
    root (X^^(7+n*4) *> [0] *> X *> [0;0] *> s)).
  rewrite root_X_add; applys_eq HM; flia.
Qed.

Lemma Num_B21_odd_return n r:
  Num true (90+n*96) r -> exists s, Num true (611+n*600) s /\
    root (X^^(16+n*16) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(103+n*100) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_B21_return (1+n*2) _ ltac:(applys_eq HN; flia))
    as [t [HT HB]].
  destruct (Num_Oa3_odd_return (24+n*25) _ ltac:(applys_eq HT; flia)) as [s [HS HA]].
  exists s; split; [applys_eq HS; flia|].
  eapply progress_trans; [applys_eq HB; flia|applys_eq HA; flia].
Qed.

(* TM23OddSourceKernel: symbolic complete-root composition. *)
Lemma CutNum_a1_even q b j d k a r:
  CutNum b j d r -> d*2+q+2<=j ->
  j+(1+q)*3=(if b then 4 else 0)+k*2 ->
  d+(1+q)*2+a=(if b then 3 else 1)+k ->
  exists s, Num (negb b) k s /\
    root (X^^(1+q) *> [0] *> X *> [0;0] *> r) -->+
    root (X *> [0] *> X^^(1+a) *> [0] *> Y *> s).
Proof.
  intros HN Hd Hj Ha.
  destruct (Num_pending q (0inf <* [1]) _ _ _ _ HN Hd) as [s [HS HP]].
  destruct (CutNum_digit_tail b false _ k _ a _ HS ltac:(cbn;lia) Ha) as [t [HT Es]].
  exists t; split; [exact HT|].
  eapply progress_trans; [apply a1_prepare|].
  eapply progress_trans; [exact HP|rewrite Es; apply a1_even_finish].
Qed.

Lemma CutNum_a3 q b j d r:
  CutNum b j d r -> d*2+q+2<=j ->
  exists s, CutNum b (j+8+q*3) (d+2+q*2) s /\
    root (X^^(1+q) *> [0] *> X^^3 *> [0;0] *> r) -->+ root s.
Proof.
  intros HN Hd; destruct (CutNum_hs 2 _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H2]].
  destruct (Num_pending q (0inf <* [1;1]) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HN2 ltac:(lia)) as [r3 [HN3 H3]].
  exists (X^^3 *> r3); split.
  - apply CutNum_prepend; applys_eq HN3; flia.
  - eapply progress_trans; [apply a3_prepare,H2|].
    eapply progress_trans; [exact HP|apply a3_finish,H3].
Qed.

Lemma odd1_prepare q r s:
  sideRLs tm (hf^^3) r s ->
  root (X^^(2+q) *> [0] *> X *> [0] *> Y *> r) -->+
  root (X^^(2+q) *> [0;0] *> X *> [0] *> X^^2 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_odd1 q b j d r:
  CutNum b j d r -> d*2+5+q*6<=j ->
  exists s, CutNum b (j+9+q*6) (d+7+q*6) s /\
    root (X^^(2+q) *> [0] *> X *> [0] *> Y *> r) -->+
    root (X *> [0] *> X^^(5+q*3) *> [0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_Fs 3 _ _ _ _ HN ltac:(lia)) as [r3 [HN3 H3]].
  assert (HC: CutNum b (j+3) (d+2) (X *> r3)).
  { change (CutNum b (j+3) (d+2) (X^^1 *> r3)); apply CutNum_prepend; applys_eq HN3; flia. }
  destruct (CutNum_Fs ((3+q*3)*2) _ _ _ _ HC ltac:(lia)) as [r6 [HN6 HF]].
  assert (HH: sideRLs tm (h^^(3+q*3))
    (X *> [0] *> X^^2 *> r3) (X^^(4+q*3) *> [0] *> X *> r6)).
  { applys_eq (h_columns [] (3+q*3) 1 _ _ HF); flia. }
  exists (X *> r6); split.
  - change (CutNum b (j+9+q*6) (d+7+q*6) (X^^1 *> r6)).
    apply CutNum_prepend; applys_eq HN6; flia.
  - eapply progress_trans; [apply odd1_prepare,H3|].
    eapply progress_evstep_trans; [exact (normal_calls q _ _ HH)|].
    change (root (X^^1 *> [0] *> X^^1 *> X^^(4+q*3) *> [0] *> X *> r6) -->*
      root (X *> [0] *> X^^(5+q*3) *> [0] *> X *> r6)).
    rewrite root_X_add; replace (1+(4+q*3)) with (5+q*3) by lia; unfold root; finish.
Qed.

Lemma nested_even_prepare_front p a r:
  root (X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X *> [0;0] *> r) -->+
  pending a (0inf <* [1] <* Dr^^(1+p) <* <[1;1;0;1;1]) r.
Proof. unfold root,pending; esx. Qed.

Lemma D1s_zero4_cleanup p r:
  0inf <* [1] <* Dr^^(1+p) <{{A}} [0;0;0;0] *> r -->+
  root ([0] *> X^^(1+p) *> [0;0;0;0] *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_nested_even_front p a b j d r:
  CutNum b j d r -> d*2+a+2<=j ->
  exists s, CutNum b (j+6+a*3) (d+3+a*2) s /\
    root (X^^(1+p) *> [0] *> X^^(2+a) *> [0] *> X *> [0;0] *> r) -->+
    root ([0] *> X^^(1+p) *> [0;0;0;0] *> s).
Proof.
  intros HN Hd.
  destruct (Num_pending a (0inf <* [1] <* Dr^^(1+p) <* <[1;1;0;1;1])
    _ _ _ _ HN Hd) as [s [HS HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HS ltac:(lia)) as [t [HT H3]].
  exists (X^^2 *> t); split.
  - apply CutNum_prepend; applys_eq HT; flia.
  - eapply progress_trans; [apply nested_even_prepare_front|].
    eapply progress_trans; [exact HP|].
    eapply progress_trans; [apply marked11011_finish,H3|apply D1s_zero4_cleanup].
Qed.

Lemma leading_zero4 p r:
  root ([0] *> X^^(2+p) *> [0;0;0;0] *> r) -->+
  root (X^^(2+p) *> [0;0;0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_zero4_leading_even u b j d r:
  CutNum b j d r -> d*2<=j+1 ->
  exists s, CutNum b (j+2+u*6) d s /\
    root ([0] *> X^^(2+u*2) *> [0;0;0;0] *> r) -->+
    root (X^^(1+u) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_hs (2+u*3) _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H1]].
  assert (HH: sideRLs tm (h^^(3+u*6)) ([0] *> Y *> r) (X^^(2+u*3) *> [0;0] *> r1)).
  { repeat rewrite <-Str_app_assoc.
    change (sideRLs tm (h^^(3+u*6)) ((X^^0++[0]++Y) *> r)
      ((X^^(2+u*3)++[0;0]) *> r1)).
    eapply segRLs_sideRLs_concat; [applys_eq (h_odd_batch (1+u*3) 0); flia|applys_eq H1;flia]. }
  destruct (CutNum_hs (u*3) _ _ _ _ HN1 ltac:(lia)) as [s [HS H2]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [apply leading_zero4|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (u*2) _ _ ltac:(applys_eq HH;flia)); flia|].
  change (root (X^^1 *> [0] *> X^^1 *> X^^(2+u*3) *> [0;0] *> r1) -->*
    root (X^^(1+u) *> [0] *> X^^3 *> [0;0] *> s)).
  rewrite root_X_add; applys_eq (marker_hcalls u 0 2 _ _ H2); flia.
Qed.

(* TM23OneMod: symbolic complete-root composition. *)
Lemma Num_one_mod6_even v r:
  Num true (35+v*144) r -> exists s, Num true (101+v*360) s /\
    root (X^^(7+v*24) *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(18+v*60) *> [0] *> X *> [0] *> Y *> s).
Proof.
  intro HN.
  destruct (CutNum_a1_even (6+v*24) true (35+v*144) 0 (26+v*108) (15+v*60)
    _ HN ltac:(lia) ltac:(lia) ltac:(lia)) as [r1 [HN1 HA1]].
  destruct (Num_marker_phase (5+v*20) 0 0 true _ _ _ HN1) as [r2 [HN2 HM1]].
  destruct (CutNum_odd1 (4+v*20) _ _ 0 _ HN2 ltac:(lia)) as [r3 [HN3 HO]].
  destruct (CutNum_digit_tail false false _ (37+v*144) _ (7+v*24) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_two_markers (1+v*4) 0 (16+v*60) 0 false _ _ _ HN4) as [r5 [HN5 HM2]].
  destruct (CutNum_nested_even_front (1+v*4) (15+v*60) _ _ 0 _ HN5 ltac:(lia))
    as [r6 [HN6 HE]].
  destruct (CutNum_zero4_leading_even (v*2) _ _ _ _ HN6 ltac:(lia)) as [r7 [HN7 HZ]].
  destruct (CutNum_a3 (v*2) _ _ _ _ HN7 ltac:(lia)) as [r8 [HN8 HA3]].
  destruct (CutNum_digit_tail true false _ (50+v*183) _ (18+v*59) _ HN8
    ltac:(lia) ltac:(lia)) as [r9 [HN9 E8]].
  destruct (Num_normal (16+v*59) _ _ _ HN9) as [r10 [HN10 HN0]].
  destruct (CutNum_digit_tail false true _ (50+v*180) 0 (51+v*180) _ HN10
    ltac:(lia) ltac:(lia)) as [r11 [HN11 E10]].
  destruct (Num_marker_phase (17+v*60) 0 0 true _ _ _ HN11) as [s [HS HM3]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HA1;flia|].
  eapply evstep_progress_trans; [applys_eq HM1;flia|].
  eapply progress_trans; [applys_eq HO;flia|].
  rewrite E3; eapply evstep_progress_trans; [applys_eq HM2;flia|].
  eapply progress_trans; [applys_eq HE;flia|].
  eapply progress_trans; [applys_eq HZ;flia|].
  eapply progress_trans; [applys_eq HA3;flia|].
  rewrite E8; eapply progress_evstep_trans; [applys_eq HN0;flia|].
  rewrite E10.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(51+v*180) *> sep true *> r11) -->*
    root (X^^(18+v*60) *> [0] *> X *> [0] *> Y *> s)).
  rewrite root_X_add; applys_eq HM3;flia.
Qed.

Lemma Num_critical_odd v r:
  Num true (29+v*72) r -> exists s, Num true (47+v*108) s /\
    root (X^^(6+v*12) *> [0] *> X *> [0] *> Y *> r) -->+
    root (X^^(2+v*3) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (CutNum_odd1 (4+v*12) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HO]].
  destruct (CutNum_digit_tail true false _ (29+v*72) _ 1 _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (CutNum_nested_even (15+v*36) _ _ 0 _ HN2 ltac:(lia)) as [r3 [HN3 HE]].
  destruct (CutNum_one_odd1 _ _ _ _ HN3 ltac:(lia)) as [r4 [HN4 HO1]].
  destruct (CutNum_digit_tail false true _ (41+v*90) _ (8+v*18) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_two_markers (1+v*3) 0 1 1 true _ _ _ HN5) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HO;flia|].
  rewrite E1; eapply progress_trans; [applys_eq HE;flia|].
  eapply progress_trans; [apply zero_X_zero4|].
  eapply progress_evstep_trans; [exact HO1|].
  rewrite E4; applys_eq HM;flia.
Qed.

Lemma Num_B21_to_A2 w r:
  Num true (90+w*576) r -> exists s, Num true (47+(21+w*125)*108) s /\
    root (X^^(16+w*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(65+w*375) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (Num_B21_odd_return (w*6) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HB]].
  destruct (Num_one_mod6_even (4+w*25) _ ltac:(applys_eq HN1;flia)) as [r2 [HN2 HO]].
  destruct (Num_critical_odd (21+w*125) _ ltac:(applys_eq HN2;flia)) as [s [HS HC]].
  exists s; split; [exact HS|].
  eapply progress_trans; [applys_eq HB;flia|].
  eapply progress_trans; [applys_eq HO;flia|applys_eq HC;flia].
Qed.

(* TM23KLJ: symbolic complete-root composition. *)
Definition klj a b (l r:side) :=
  l <* Dr^^a <* <[0;0;1] <* Dr^^(1+b) <* T1r {{B}}> r.

Lemma klj_cycle a b l r s:
  sideRLs tm (hf^^6) r s -> klj (1+a) b l r -->+ klj a (1+b) l s.
Proof.
  intro H; unfold klj.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^5) H) as [r1 [H1 H5]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H5.
Qed.

Lemma klj_cycles m a b l r s:
  sideRLs tm (hf^^(m*6)) r s -> klj (a+m) b l r -->* klj a (b+m) l s.
Proof.
  gen b r; induction m as [|m IH]; intros b r H.
  - inverts H; replace (a+0) with a by lia; replace (b+0) with b by lia; unfold klj; finish.
  - replace (S m*6) with (6+m*6) in H by lia; rewrite lpow_add in H.
    destruct (sideRLs_split H) as [r6 [H6 Hs]].
    apply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (klj_cycle (a+m) b l _ _ H6);flia.
    + applys_eq (IH (1+b) _ Hs);flia.
Qed.

Lemma klj_zero b r s:
  sideRLs tm (hf^^6) r s -> klj 0 b (0inf <* [1;1]) r -->+
  0inf <* [1] <* Dr^^(2+b) <* T1r {{B}}> s.
Proof.
  intro H; unfold klj.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^5) H) as [r1 [H1 H5]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H5.
Qed.

Lemma a2_odd_prepare p r s:
  sideRLs tm (hf^^4) r s ->
  root (X^^(2+p) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  klj (1+p) 2 (0inf <* [1;1]) s.
Proof. intro H; unfold root,klj; finish_calls H. Qed.

Lemma klj_finish b r s:
  sideRLs tm (hf^^2) r s ->
  0inf <* [1] <* Dr^^b <* T1r {{B}}> r -->+
  root ([0] *> X^^b *> [0] *> X^^3 *> s).
Proof.
  intro H; unfold root.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf) H) as [r1 [H1 H2]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H2.
Qed.

Lemma a2_odd_calls p r s:
  sideRLs tm (hf^^(18+p*6)) r s ->
  root (X^^(2+p) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root ([0] *> X^^(5+p) *> [0] *> X^^3 *> s).
Proof.
  intro H; replace (18+p*6) with (4+((1+p)*6+(6+2))) in H by lia.
  rewrite (lpow_add _ 4 ((1+p)*6+(6+2))) in H.
  destruct (sideRLs_split H) as [r4 [H4 Hs]]; rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm He]]; rewrite lpow_add in He.
  destruct (sideRLs_split He) as [r6 [H6 H2]].
  eapply progress_trans; [apply a2_odd_prepare,H4|].
  eapply evstep_progress_trans;
    [applys_eq (klj_cycles (1+p) 0 2 (0inf <* [1;1]) _ _ Hm);flia|].
  eapply progress_trans; [apply klj_zero,H6|applys_eq (klj_finish (5+p) _ _ H2);flia].
Qed.

Lemma leading_marker_half p a e r s:
  sideRLs tm (h^^2) r s ->
  root ([0] *> X^^(1+p) *> [0] *> X^^(3+a) *> sep e *> r) -->+
  root (X^^(2+p) *> [0] *> X^^(1+a) *> sep e *> s).
Proof. intro H; destruct e; unfold root,sep; finish_calls H. Qed.

(* TM23A2Return: symbolic complete-root composition. *)
Lemma Num_A2_return p r:
  Num true (47+p*36) r -> exists s, Num false (47+p*36) s /\
    root (X^^(2+p) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(11+p*6) *> [0] *> X *> [0] *> Y *> s).
Proof.
  intro HN; destruct (CutNum_Fs (18+p*6) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HF]].
  destruct (CutNum_digit_tail true true _ (30+p*21) _ (15+p*15) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_add 2 _ _ _ HN2) as [r3 [HN3 H2]].
  destruct (Num_marker_phase (5+p*5) (5+p) 0 true _ _ _ HN3) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [apply a2_odd_calls,HF|].
  rewrite E1.
  change (root (X^^0 *> [0] *> X^^(5+p) *> [0] *> X^^3 *>
    X^^(15+p*15) *> sep true *> r2) -->+
    root (X^^(11+p*6) *> [0] *> X *> [0] *> Y *> s)).
  rewrite <-(Str_app_assoc (X^^3) (X^^(15+p*15))), <-lpow_add.
  eapply progress_evstep_trans;
    [applys_eq (leading_marker_half (4+p) (15+p*15) true _ _ H2);flia|].
  applys_eq HM;flia.
Qed.

(* TM23CriticalE: symbolic complete-root composition. *)
Notation CEleft := (0inf <* <[1;1;1;0;1;1;0;0;1;1;1;1;0;0;1;1]).

Lemma critical_E_front3 r:
  root (X^^3 *> [0;0] *> r) -->+ root ([0] *> X^^2 *> [0] *> Y *> r).
Proof. unfold root; esx. Qed.

Lemma critical_E_prepare a r:
  root ([0] *> X^^2 *> [0] *> Y *> X^^(1+a) *> [0] *> X *> [0;0] *> r) -->+
  pending a CEleft r.
Proof. unfold root,pending; esx. Qed.

Lemma critical_E_finish r s:
  sideRLs tm (hf^^6) r s -> CEleft <{{F}} [1;0] *> Y *> r -->+
  root (X^^3 *> [0] *> X^^3 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma Num_critical_E t r:
  Num false (11+t*6) r -> exists s, CutNum true (40+t*15) (17+t*6) s /\
    root (X^^(5+t) *> [0] *> X *> [0] *> Y *> r) -->+
    root (X^^3 *> [0] *> s).
Proof.
  intro HN; destruct (CutNum_Fs 3 _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 H3]].
  assert (HC: CutNum false (14+t*6) 2 (X *> r1)).
  { change (CutNum false (14+t*6) 2 (X^^1 *> r1));
    apply CutNum_prepend; applys_eq HN1;flia. }
  destruct (CutNum_Fs (12+t*6) _ _ _ _ HC ltac:(lia)) as [r2 [HN2 HF]].
  replace (12+t*6) with ((6+t*3)*2) in HF by lia.
  assert (HH: sideRLs tm (h^^((2+t)*3)) (X *> [0] *> X^^2 *> r1)
    (X^^(7+t*3) *> [0] *> X *> r2)).
  { applys_eq (h_columns [] (6+t*3) 1 _ _ HF);flia. }
  destruct (CutNum_digit_tail false false _ (13+t*6) _ 0 _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E2]].
  destruct (Num_pending (6+t*3) CEleft _ _ 0 _ HN3 ltac:(lia)) as [r4 [HN4 HP]].
  destruct (CutNum_Fs 6 _ _ _ _ HN4 ltac:(lia)) as [r5 [HN5 H6]].
  exists (X^^3 *> r5); split.
  - apply CutNum_prepend; applys_eq HN5;flia.
  - eapply progress_trans; [applys_eq (odd1_prepare (3+t) _ _ H3);flia|].
    eapply evstep_progress_trans; [applys_eq (normal_cycles (2+t) 1 _ _ HH);flia|].
    rewrite E2; eapply progress_trans; [apply critical_E_front3|].
    eapply progress_trans; [applys_eq (critical_E_prepare (6+t*3) r3);flia|].
    eapply progress_trans; [exact HP|apply critical_E_finish,H6].
Qed.

Lemma Num_critical_E_return p r:
  Num false (47+p*36) r -> exists s, Num false (75+p*54) s /\
    root (X^^(11+p*6) *> [0] *> X *> [0] *> Y *> r) -->+
    root (X^^(7+p*3) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_critical_E (6+p*6) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HC]].
  destruct (CutNum_digit_tail true false _ (63+p*45) _ (13+p*9) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_marker_phase (4+p*3) 2 0 false _ _ _ HN2) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_evstep_trans; [applys_eq HC;flia|].
  rewrite E1; applys_eq HM;flia.
Qed.

(* TM23EResurge: symbolic complete-root composition. *)
Lemma Num_E_resurge s r:
  Num false (75+s*108) r -> exists t, Num true (81+s*114) t /\
    root (X^^(7+s*6) *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(12+s*17) *> [0] *> X^^3 *> [0] *> Y *> t).
Proof.
  intro HN; destruct (CutNum_a1_even (6+s*6) false (75+s*108) 0
    (48+s*63) (35+s*51) _ HN ltac:(lia) ltac:(lia) ltac:(lia)) as [r1 [HN1 HA]].
  destruct (Num_marker_phase (11+s*17) 0 2 true _ _ _ HN1) as [t [HT HM]].
  exists t; split; [applys_eq HT;flia|].
  eapply progress_evstep_trans; [applys_eq HA;flia|applys_eq HM;flia].
Qed.

Lemma Num_Y_return s r:
  Num true (81+s*114) r -> exists t, Num false (82+s*114) t /\
    root (X^^(12+s*17) *> [0] *> X^^3 *> [0] *> Y *> r) -->+
    root (X^^(2+s) *> [0] *> X^^(37+s*51) *> [0] *> X^^2 *> [0;0] *> t).
Proof.
  intro HN; destruct (Num_add 3 _ _ _ HN) as [r1 [HN1 H3]].
  destruct (CutNum_Fs (72+s*102) _ _ 0 _ HN1 ltac:(lia)) as [r2 [HN2 HF]].
  replace (72+s*102) with (2+(35+s*51)*2) in HF by lia.
  destruct (CutNum_digit_tail true false _ (76+s*108) _ (7+s*6) _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E2]].
  destruct (Num_two_markers (1+s) 0 (36+s*51) 1 false _ _ _ HN3) as [t [HT HM]].
  assert (HH: sideRLs tm (h^^(36+s*51)) (Y *> r1)
    (X^^(36+s*51) *> [0] *> X *> r2)).
  { applys_eq (Y_hs (35+s*51) _ _ HF);flia. }
  exists t; split; [applys_eq HT;flia|].
  eapply progress_trans; [applys_eq (odd_three (11+s*17) _ _ H3);flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (11+s*17) _ _ ltac:(applys_eq HH;flia));flia|].
  rewrite E2.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(36+s*51) *> [0] *>
    X^^1 *> X^^(7+s*6) *> [0;0] *> r3) -->*
    root (X^^(2+s) *> [0] *> X^^(37+s*51) *> [0] *> X^^2 *> [0;0] *> t)).
  rewrite root_X_add, <-(Str_app_assoc (X^^1) (X^^(7+s*6))), <-lpow_add.
  applys_eq HM;flia.
Qed.

Lemma Num_A2_to_C s r:
  Num true (47+s*72) r -> exists t, Num false (82+s*114) t /\
    root (X^^(2+s*2) *> [0] *> X^^2 *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(2+s) *> [0] *> X^^(37+s*51) *> [0] *> X^^2 *> [0;0] *> t).
Proof.
  intro HN; destruct (Num_A2_return (s*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HA]].
  destruct (Num_critical_E_return (s*2) _ HN1) as [r2 [HN2 HC]].
  destruct (Num_E_resurge s _ ltac:(applys_eq HN2;flia)) as [r3 [HN3 HE]].
  destruct (Num_Y_return s _ HN3) as [t [HT HY]].
  exists t; split; [exact HT|].
  eapply progress_trans; [exact HA|].
  eapply progress_trans; [exact HC|].
  eapply progress_trans; [applys_eq HE;flia|exact HY].
Qed.

Lemma Num_B21_to_C u r:
  Num true (90+(1+u*2)*576) r -> exists t, Num false (82+(219+u*375)*114) t /\
    root (X^^(16+(1+u*2)*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(2+(219+u*375)) *> [0] *> X^^(37+(219+u*375)*51) *>
      [0] *> X^^2 *> [0;0] *> t).
Proof.
  intro HN; destruct (Num_B21_to_A2 (1+u*2) _ HN) as [r1 [HN1 HB]].
  destruct (Num_A2_to_C (219+u*375) _ ltac:(applys_eq HN1;flia)) as [t [HT HC]].
  exists t; split; [exact HT|].
  eapply progress_trans; [exact HB|applys_eq HC;flia].
Qed.

(* TM23CShort: symbolic complete-root composition. *)
Lemma C_short_prepare p b r s:
  sideRLs tm h r s ->
  root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^2 *> [0;0] *> r) -->+
  pending b (0inf <* [1] <* Dr^^(1+p) <* [1]) s.
Proof. intro H; unfold root,pending; finish_calls H. Qed.

Lemma C_short_finish p r s:
  sideRLs tm (hf^^3) r s ->
  0inf <* [1] <* Dr^^(1+p) <* [1] <{{F}} [1;0] *> Y *> r -->+
  root (X^^(4+p) *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_C_short p b chi j d r:
  CutNum chi j d r -> d*2+b+1<=j ->
  exists s, CutNum chi (j+7+b*3) (d+5+b*2) s /\
    root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(4+p) *> s).
Proof.
  intros HN Hd; destruct (CutNum_hs 1 _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H1]].
  destruct (Num_pending b (0inf <* [1] <* Dr^^(1+p) <* [1]) _ _ _ _ HN1 ltac:(lia))
    as [r2 [HN2 HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HN2 ltac:(lia)) as [s [HS H3]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [apply C_short_prepare;applys_eq H1;flia|].
  eapply progress_trans; [exact HP|apply C_short_finish,H3].
Qed.

Lemma Num_C_short t r:
  Num false (82+t*114) r -> exists s, CutNum false (197+t*267) (72+t*101) s /\
    root (X^^(2+t) *> [0] *> X^^(37+t*51) *> [0] *> X^^2 *> [0;0] *> r) -->+ root s.
Proof.
  intro HN; destruct (CutNum_C_short (1+t) (36+t*51) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HC]].
  exists (X^^(5+t) *> r1); split.
  - apply CutNum_prepend; applys_eq HN1;flia.
  - applys_eq HC;flia.
Qed.

Lemma Num_C_even n r:
  Num false (196+n*228) r -> exists s, Num false (406+n*462) s /\
    root (X^^(3+n*2) *> [0] *> X^^(88+n*102) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(69+n*77) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (Num_C_short (1+n*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HC]].
  destruct (CutNum_digit_tail false false _ (232+n*267) _ (60+n*65) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_normal (58+n*65) _ _ _ HN2) as [r3 [HN3 HN0]].
  destruct (CutNum_digit_tail true true _ (202+n*231) 0 (205+n*231) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_marker_phase (68+n*77) 0 1 true _ _ _ HN4) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HC;flia|].
  rewrite E1; eapply progress_evstep_trans; [applys_eq HN0;flia|].
  rewrite E3.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(205+n*231) *> sep true *> r4) -->*
    root (X^^(69+n*77) *> [0] *> X^^2 *> [0] *> Y *> s)).
  rewrite root_X_add; applys_eq HM;flia.
Qed.

Lemma Num_B21_to_Ebirth v r:
  Num true (90+(1+v*4)*576) r -> exists s, Num false (406+(109+v*375)*462) s /\
    root (X^^(16+(1+v*4)*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(69+(109+v*375)*77) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (Num_B21_to_C (v*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HB]].
  destruct (Num_C_even (109+v*375) _ ltac:(applys_eq HN1;flia)) as [s [HS HC]].
  exists s; split; [exact HS|].
  replace (1+v*2*2) with (1+v*4) in HB by lia.
  replace (3+(109+v*375)*2) with (2+(219+v*2*375)) in HC by lia.
  replace (88+(109+v*375)*102) with (37+(219+v*2*375)*51) in HC by lia.
  eapply progress_trans; [exact HB|exact HC].
Qed.



(* E-birth deficit three: retain the actual underflow and zero-Y callers. *)
Notation EBleft := (0inf <* <[1;1;1;0;1;1;1;1]).
Notation ZYleft := (0inf <* <[1;1;1;0;0;1;1]).

Lemma birth_last_three b r s:
  sideRLs tm (hf^^3) r s -> birth 2 (1+b) r -->+
  EBleft <* Dr^^(3+b) <* T1r {{B}}> s.
Proof.
  intro H; unfold birth.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^2) H) as [r1 [H1 H2]].
  follow11 (sideRLs_1 _ _ _ _ _ H1); finish_calls H2.
Qed.

Lemma birth_E_evenzero b r s:
  sideRLs tm h r s ->
  EBleft <* Dr^^b <* T1r {{B}}> [0;0] *> r -->+
  root ([0;0;0] *> Y *> X^^b *> [0] *> X^^2 *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma birth_E_underflow p r t s:
  sideRLs tm (hf^^(6+p*6)) r ([0;0] *> t) -> sideRLs tm h t s ->
  root (X^^(2+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root ([0;0;0] *> Y *> X^^(3+p*3) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intros H H1; replace (6+p*6) with (3+(p*6+3)) in H by lia.
  rewrite (lpow_add _ 3 (p*6+3) hf) in H.
  destruct (sideRLs_split H) as [r3 [H3 Hs]]; rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm Hlast]].
  eapply progress_trans; [applys_eq (birth_prepare (1+p) _ _ H3);flia|].
  eapply evstep_progress_trans; [applys_eq (birth_cycles p 1 0 _ _ Hm);flia|].
  eapply progress_trans; [apply birth_last_three,Hlast|apply birth_E_evenzero,H1].
Qed.

Lemma Num_birth_Edeficit p r:
  Num false (4+p*6) r -> exists s, Num true (6+p*6) s /\
    root (X^^(2+p) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root ([0;0;0] *> Y *> X^^(3+p*3) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (CutNum_Fs (6+p*6) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HF]].
  destruct (CutNum_digit_tail false false _ (5+p*6) _ 0 _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_inc HN2) as [s [HS H1]].
  exists s; split; [applys_eq HS;flia|].
  change (r1=[0;0] *> r2) in E1.
  apply (birth_E_underflow p _ r2); [rewrite <-E1;exact HF|exact H1].
Qed.

Lemma birth_E_prelude b r s:
  sideRLs tm h r s ->
  root ([0;0;0] *> Y *> X^^b *> [0] *> X^^2 *> [0;0] *> r) -->+
  root ([0] *> Y *> X^^(2+b) *> [0] *> X *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma zeroY_even_prepare b r:
  root ([0] *> Y *> X^^(1+b) *> [0] *> X *> [0;0] *> r) -->+
  pending b ZYleft r.
Proof. unfold root,pending; esx. Qed.

Lemma zeroY_even_finish r s:
  sideRLs tm (hf^^4) r s -> ZYleft <{{F}} [1;0] *> Y *> r -->+
  root (X^^4 *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_zeroY_even b chi j d r:
  CutNum chi j d r -> d*2+b+3<=j ->
  exists s, CutNum chi (j+7+b*3) (d+2+b*2) s /\
    root ([0] *> Y *> X^^(1+b) *> [0] *> X *> [0;0] *> r) -->+ root s.
Proof.
  intros HN Hd; destruct (Num_pending b ZYleft _ _ _ _ HN ltac:(lia)) as [r1 [HN1 HP]].
  destruct (CutNum_Fs 4 _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 H4]].
  exists (X^^4 *> r2); split; [apply CutNum_prepend;applys_eq HN2;flia|].
  eapply progress_trans; [apply zeroY_even_prepare|].
  eapply progress_trans; [exact HP|apply zeroY_even_finish,H4].
Qed.

Lemma Num_Ebirth_even_return t r:
  Num false (16+t*12) r -> exists s, Num true (95+t*48) s /\
    root (X^^(4+t*2) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(17+t*8) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_birth_Edeficit (2+t*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HB]].
  destruct (Num_inc HN1) as [r2 [HN2 H1]].
  destruct (CutNum_zeroY_even (10+t*6) _ _ 0 _ HN2 ltac:(lia)) as [r3 [HN3 HZ]].
  destruct (CutNum_digit_tail true false _ (26+t*15) _ (7+t*3) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_normal (5+t*3) _ _ _ HN4) as [r5 [HN5 HN0]].
  destruct (CutNum_digit_tail false false _ (22+t*12) 0 (23+t*12) _ HN5
    ltac:(lia) ltac:(lia)) as [r6 [HN6 E5]].
  destruct (Num_markers (7+t*4) 0 2 _ _ _ HN6) as [r7 [HN7 HM]].
  destruct (Num_a3 (7+t*4) _ _ _ HN7 ltac:(lia)) as [r8 [HN8 HA]].
  destruct (CutNum_digit_tail true false _ (34+t*18) _ (21+t*10) _ HN8
    ltac:(lia) ltac:(lia)) as [r9 [HN9 E8]].
  destruct (Num_normal (19+t*10) _ _ _ HN9) as [r10 [HN10 HN10r]].
  destruct (CutNum_digit_tail false false _ (47+t*24) 0 (48+t*24) _ HN10
    ltac:(lia) ltac:(lia)) as [r11 [HN11 E10]].
  destruct (Num_markers (16+t*8) 0 0 _ _ _ HN11) as [s [HS HM2]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HB;flia|].
  eapply progress_trans; [applys_eq (birth_E_prelude (9+t*6) _ _ H1);flia|].
  eapply progress_trans; [applys_eq HZ;flia|].
  rewrite E3; eapply progress_trans; [applys_eq HN0;flia|].
  rewrite E5.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(23+t*12) *> sep false *> r6) -->+
    root (X^^(17+t*8) *> [0] *> X *> [0;0] *> s)).
  rewrite root_X_add; eapply evstep_progress_trans; [applys_eq HM;flia|].
  eapply progress_trans; [exact HA|].
  rewrite E8; eapply progress_evstep_trans; [applys_eq HN10r;flia|].
  rewrite E10.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(48+t*24) *> sep false *> r11) -->*
    root (X^^(17+t*8) *> [0] *> X *> [0;0] *> s)).
  rewrite root_X_add; applys_eq HM2;flia.
Qed.

Lemma Num_Ebirth_to_C3 v r:
  Num false (40+v*36) r -> exists s, Num true (223+v*168) s /\
    root (X^^(8+v*6) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(6+v*4) *> [0] *> X^^(82+v*60) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_Ebirth_even_return (2+v*3) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HE]].
  destruct (CutNum_a1_even (32+v*24) true _ 0 (143+v*108) (80+v*60)
    _ HN1 ltac:(lia) ltac:(lia) ltac:(lia)) as [r2 [HN2 HA]].
  destruct (Num_marker_phase (26+v*20) 0 2 true _ _ _ HN2) as [r3 [HN3 HM1]].
  destruct (Num_add 3 _ _ _ HN3) as [r4 [HN4 H3]].
  destruct (CutNum_Fs (162+v*120) _ _ 0 _ HN4 ltac:(lia)) as [r5 [HN5 HF]].
  replace (162+v*120) with (2+(80+v*60)*2) in HF by lia.
  destruct (CutNum_digit_tail false false _ (193+v*144) _ (32+v*24) _ HN5
    ltac:(lia) ltac:(lia)) as [r6 [HN6 E5]].
  destruct (Num_two_markers (5+v*4) 0 (81+v*60) 2 false _ _ _ HN6) as [s [HS HM2]].
  assert (HH: sideRLs tm (h^^(81+v*60)) (Y *> r4)
    (X^^(81+v*60) *> [0] *> X *> r5)).
  { applys_eq (Y_hs (80+v*60) _ _ HF);flia. }
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HE;flia|].
  eapply progress_trans; [applys_eq HA;flia|].
  eapply evstep_progress_trans; [applys_eq HM1;flia|].
  eapply progress_trans; [applys_eq (odd_three (26+v*20) _ _ H3);flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (26+v*20) _ _ ltac:(applys_eq HH;flia));flia|].
  rewrite E5.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(81+v*60) *> [0] *>
    X^^1 *> X^^(32+v*24) *> [0;0] *> r6) -->*
    root (X^^(6+v*4) *> [0] *> X^^(82+v*60) *> [0] *> X^^3 *> [0;0] *> s)).
  rewrite root_X_add, <-(Str_app_assoc (X^^1) (X^^(32+v*24))), <-lpow_add.
  applys_eq HM2;flia.
Qed.

Lemma Num_B21_to_C3 w r:
  Num true (90+(1+w*8)*576) r ->
  exists s, Num true (223+(29+46*30+w*125*77)*168) s /\
    root (X^^(16+(1+w*8)*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(6+(29+46*30+w*125*77)*4) *> [0] *>
      X^^(82+(29+46*30+w*125*77)*60) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_B21_to_Ebirth (w*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HB]].
  destruct (Num_Ebirth_to_C3 (29+46*30+w*125*77) _ ltac:(applys_eq HN1;flia)) as [s [HS HE]].
  exists s; split; [exact HS|].
  replace (1+w*2*4) with (1+w*8) in HB by lia.
  replace (8+(29+46*30+w*125*77)*6) with (69+(109+w*2*375)*77) in HE by lia.
  eapply progress_trans; [exact HB|exact HE].
Qed.


(* Complete terminal-three return and the tight normal-Y caller. *)
Lemma C3_prepare p a r s:
  sideRLs tm (h^^2) r s ->
  root (X^^(2+p) *> [0] *> X^^(2+a) *> [0] *> X^^3 *> [0;0] *> r) -->+
  pending a (0inf <* <[1;1;1;0;1;1] <* Dr^^(1+p) <* <[1;1;0;1;1]) s.
Proof. intro H; unfold root,pending; finish_calls H. Qed.

Lemma C3_cleanup p r:
  0inf <* <[1;1;1;0;1;1] <* Dr^^(1+p) <{{A}} [0;0;0;0] *> r -->+
  root (X^^(2+p) *> [0] *> Y *> [0;0] *> r).
Proof. unfold root; esx. Qed.

Lemma CutNum_C3 p a chi j d r:
  CutNum chi j d r -> d*2+a+2<=j ->
  exists s, CutNum chi (j+8+a*3) (d+3+a*2) s /\
    root (X^^(2+p) *> [0] *> X^^(2+a) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(2+p) *> [0] *> Y *> [0;0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_hs 2 _ _ _ _ HN ltac:(lia)) as [r2 [HN2 H2]].
  destruct (Num_pending a (0inf <* <[1;1;1;0;1;1] <* Dr^^(1+p) <* <[1;1;0;1;1])
    _ _ _ _ HN2 ltac:(lia)) as [r3 [HN3 HP]].
  destruct (CutNum_Fs 3 _ _ _ _ HN3 ltac:(lia)) as [r6 [HN6 H3]].
  exists (X^^2 *> r6); split; [apply CutNum_prepend;applys_eq HN6;flia|].
  eapply progress_trans; [apply C3_prepare,H2|].
  eapply progress_trans; [exact HP|].
  eapply progress_trans; [apply marked11011_finish,H3|apply C3_cleanup].
Qed.

Lemma zeroY00_prepare p r s:
  sideRLs tm h r s ->
  root (X^^(2+p) *> [0] *> Y *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0;0] *> X *> [0;0] *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma CutNum_zeroY00_even u chi j d r:
  CutNum chi j d r -> d*2<=j+1 ->
  exists s, CutNum chi (j+2+u*6) d s /\
    root (X^^(2+u*2) *> [0] *> Y *> [0;0] *> r) -->+
    root (X^^(1+u) *> [0] *> X^^3 *> [0] *> Y *> s).
Proof.
  intros HN Hd; destruct (CutNum_hs 1 _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H1]].
  destruct (CutNum_hs (1+u*3) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 H2]].
  assert (HH: sideRLs tm (h^^(3+u*6)) (X *> [0;0] *> r1)
    (X^^(2+u*3) *> [0] *> Y *> r2)).
  { repeat rewrite <-Str_app_assoc; repeat rewrite <-app_assoc.
    change (sideRLs tm (h^^(3+u*6)) ((X^^1++[0;0]) *> r1)
      ((X^^(2+u*3)++[0]++Y) *> r2)).
    eapply segRLs_sideRLs_concat; [applys_eq (h_even_batch (1+u*3) 0);flia|exact H2]. }
  destruct (CutNum_hs (u*3) _ _ _ _ HN2 ltac:(lia)) as [s [HS H3]].
  assert (HF: sideRLs tm (hf^^(u*6))
    (X^^(2+u*3) *> sep true *> r2) (X^^2 *> sep true *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat; [applys_eq (F_pairs (u*3) 2 true);flia|exact H3]. }
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [apply zeroY00_prepare;applys_eq H1;flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (u*2) _ _ ltac:(applys_eq HH;flia));flia|].
  applys_eq (marker_calls u 0 _ _ HF);flia.
Qed.

Lemma CutNum_normalY q chi j d r:
  CutNum chi j d r -> d*2+4+q*6<=j ->
  exists s, CutNum chi (j+6+q*6) (d+5+q*6) s /\
    root (X^^(2+q) *> [0;0] *> Y *> r) -->+
    root (X *> [0] *> X^^(4+q*3) *> [0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_Fs (6+q*6) _ _ _ _ HN ltac:(lia)) as [t [HT HF]].
  assert (HH: sideRLs tm (h^^(3+q*3)) (Y *> r)
    (X^^(3+q*3) *> [0] *> X *> t)).
  { applys_eq (Y_hs (2+q*3) _ _ ltac:(applys_eq HF;flia));flia. }
  exists (X *> t); split.
  - change (CutNum chi (j+6+q*6) (d+5+q*6) (X^^1 *> t)).
    apply CutNum_prepend;applys_eq HT;flia.
  - eapply progress_evstep_trans; [exact (normal_calls q _ _ HH)|].
    change (root (X^^1 *> [0] *> X^^1 *> X^^(3+q*3) *> [0] *> X *> t) -->*
      root (X^^1 *> [0] *> X^^(4+q*3) *> [0] *> X *> t)).
    rewrite root_X_add; replace (1+(3+q*3)) with (4+q*3) by lia; unfold root;finish.
Qed.

Lemma normal_two r s:
  sideRLs tm (h^^2) r s ->
  root (X^^2 *> [0;0] *> r) -->+ root ([0] *> Y *> X *> s).
Proof. intro H; unfold root; finish_calls H. Qed.

Lemma normal_truncated p r s:
  sideRLs tm (h^^(p*3+2)) r s ->
  root (X^^(2+p) *> [0;0] *> r) -->+ root ([0] *> Y *> X *> s).
Proof.
  intro H; rewrite lpow_add in H.
  destruct (sideRLs_split H) as [t [H1 H2]].
  eapply evstep_progress_trans;
    [applys_eq (normal_cycles p 0 _ _ H1);flia|apply normal_two,H2].
Qed.

Lemma Num_tight_odd3_boundary n r:
  Num false (5+n*6) r -> exists s, Num true (9+n*6) s /\
    root (X^^(2+n) *> [0] *> X^^3 *> [0] *> Y *> r) -->+
    root ([0] *> Y *> X^^(6+n*3) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_add 3 _ _ _ HN) as [r1 [HN1 H3]].
  destruct (CutNum_Fs (10+n*6) _ _ 0 _ HN1 ltac:(lia)) as [r2 [HN2 HF]].
  destruct (CutNum_digit_tail false false _ (9+n*6) _ 0 _ HN2
    ltac:(lia) ltac:(lia)) as [s [HS E2]].
  assert (HH: sideRLs tm (h^^(5+n*3)) (Y *> r1)
    (X^^(5+n*3) *> [0] *> X *> r2)).
  { applys_eq (Y_hs (4+n*3) _ _ ltac:(applys_eq HF;flia));flia. }
  exists s; split; [exact HS|].
  eapply progress_trans; [applys_eq (odd_three (1+n) _ _ H3);flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_truncated (1+n) _ _ ltac:(applys_eq HH;flia));flia|].
  change (r2=[0;0] *> s) in E2; rewrite E2.
  rewrite <-(Str_app_assoc (X^^1) (X^^(5+n*3))), <-lpow_add.
  replace (1+(5+n*3)) with (6+n*3) by lia; unfold root;finish.
Qed.

Lemma Num_tight_odd3_odd t r:
  Num false (11+t*12) r -> exists s, Num true (36+t*24) s /\
    root (X^^(3+t*2) *> [0] *> X^^3 *> [0] *> Y *> r) -->+
    root (X^^(7+t*4) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_tight_odd3_boundary (1+t*2) _ ltac:(applys_eq HN;flia))
    as [r1 [HN1 HB]].
  destruct (CutNum_zeroY_even (8+t*6) _ _ 0 _ HN1 ltac:(lia)) as [r2 [HN2 HZ]].
  destruct (CutNum_digit_tail true false _ (21+t*15) _ (6+t*3) _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E2]].
  destruct (Num_normal (4+t*3) _ _ _ HN3) as [r4 [HN4 HN0]].
  destruct (CutNum_digit_tail false false _ (18+t*12) 0 (19+t*12) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_markers (6+t*4) 0 1 _ _ _ HN5) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HB;flia|].
  eapply progress_trans; [applys_eq HZ;flia|].
  rewrite E2; eapply progress_evstep_trans; [applys_eq HN0;flia|].
  rewrite E4.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(19+t*12) *> sep false *> r5) -->*
    root (X^^(7+t*4) *> [0] *> X^^2 *> [0;0] *> s)).
  rewrite root_X_add;applys_eq HM;flia.
Qed.

Lemma Num_C3_two v r:
  Num true (55+v*168) r -> exists s, Num false (83+v*240) s /\
    root (X^^(2+v*4) *> [0] *> X^^(22+v*60) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(4+v*9) *> [0] *> X^^(4+v*6) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (CutNum_C3 (v*4) (20+v*60) _ _ 0 _ HN ltac:(lia))
    as [r1 [HN1 HC]].
  destruct (CutNum_zeroY00_even (v*2) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 HZ]].
  destruct (CutNum_hs 3 _ _ _ _ HN2 ltac:(lia)) as [r3 [HN3 H3]].
  destruct (CutNum_normalY (v*2) _ _ _ _ HN3 ltac:(lia)) as [r4 [HN4 HY]].
  destruct (CutNum_digit_tail true false _ (65+v*186) _ (20+v*54) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_two_markers (3+v*9) 0 (3+v*6) 1 false _ _ _ HN5)
    as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HC;flia|].
  eapply progress_trans; [applys_eq HZ;flia|].
  eapply progress_trans; [applys_eq (odd_three (v*2) _ _ H3);flia|].
  eapply progress_evstep_trans; [exact HY|].
  rewrite E4;applys_eq HM;flia.
Qed.

Lemma Num_C3_odd_source w r:
  Num true (223+w*336) r -> exists s, Num false (689+w*169*6) s /\
    root (X^^(6+w*8) *> [0] *> X^^(82+w*120) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(116+w*169) *> [0] *> X^^3 *> [0] *> Y *> s).
Proof.
  intro HN; destruct (Num_C3_two (1+w*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HC]].
  destruct (CutNum_C_short (12+w*18) (9+w*12) _ _ 0 _ HN1 ltac:(lia))
    as [r2 [HN2 HS0]].
  assert (HN3: CutNum false (357+w*516) (7+w*6) (X^^(16+w*18) *> r2)).
  { apply CutNum_prepend;applys_eq HN2;flia. }
  destruct (CutNum_digit_tail false true _ (178+w*258) _ (172+w*252) _ HN3
    ltac:(lia) ltac:(lia)) as [r3 [HN4 E3]].
  destruct (Num_normal_odd (170+w*252) _ _ _ HN4) as [r4 [HN5 HN0]].
  destruct (CutNum_digit_tail true true _ (344+w*507) 0 (347+w*507) _ HN5
    ltac:(lia) ltac:(lia)) as [r5 [HN6 E4]].
  destruct (Num_marker_phase (115+w*169) 0 2 true _ _ _ HN6) as [s [HS HM]].
  exists s; split; [applys_eq HS;flia|].
  eapply progress_trans; [applys_eq HC;flia|].
  eapply progress_trans; [applys_eq HS0;flia|].
  replace (4+(12+w*18)) with (16+w*18) by lia; rewrite E3.
  eapply progress_evstep_trans; [applys_eq HN0;flia|].
  rewrite E4.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(347+w*507) *> sep true *> r5) -->*
    root (X^^(116+w*169) *> [0] *> X^^3 *> [0] *> Y *> s)).
  rewrite root_X_add;applys_eq HM;flia.
Qed.

Lemma Num_C3_to_even2 z r:
  Num true (559+z*672) r -> exists s, Num true (36+(141+z*169)*24) s /\
    root (X^^(14+z*16) *> [0] *> X^^(202+z*240) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(571+z*676) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_C3_odd_source (1+z*2) _ ltac:(applys_eq HN;flia))
    as [t [HT HC]].
  destruct (Num_tight_odd3_odd (141+z*169) _ ltac:(applys_eq HT;flia)) as [s [HS HE]].
  exists s; split; [exact HS|].
  eapply progress_trans; [applys_eq HC;flia|applys_eq HE;flia].
Qed.

Lemma Num_B21_to_even2 t r:
  Num true (90+(9+t*32)*576) r ->
  exists s, Num true (36+(141+(58+90*30+t*125*77)*169)*24) s /\
    root (X^^(16+(9+t*32)*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(571+(58+90*30+t*125*77)*676) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN; destruct (Num_B21_to_C3 (1+t*4) _ ltac:(applys_eq HN;flia))
    as [r1 [HN1 HB]].
  replace (223+(29+46*30+(1+t*4)*125*77)*168) with
    (559+(58+90*30+t*125*77)*672) in HN1 by lia.
  destruct (Num_C3_to_even2 (58+90*30+t*125*77) _ HN1)
    as [s [HS HC]].
  exists s; split; [exact HS|].
  replace (1+(1+t*4)*8) with (9+t*32) in HB by lia.
  replace (14+(58+90*30+t*125*77)*16) with
    (6+(29+46*30+(1+t*4)*125*77)*4) in HC by lia.
  replace (202+(58+90*30+t*125*77)*240) with
    (82+(29+46*30+(1+t*4)*125*77)*60) in HC by lia.
  eapply progress_trans; [exact HB|exact HC].
Qed.


(* Sourced EVEN2/C2 return; retain every real first X and ordered marker. *)
Lemma CutNum_takeX chi j d r:
  CutNum chi j d r -> d*2<=j ->
  exists s, r=X *> s /\ CutNum chi j (d+1) s.
Proof.
  intros HN Hd; pose proof (Num_view HN) as HV.
  remember (X^^d *> r) as z eqn:Ez in HV; destruct HV.
  - assert (E:r=X^^(1+(k-d)) *> [0;0] *> r0).
    { rewrite (cut_prefix (1+k) d r ([0;0] *> r0) ltac:(lia) (eq_sym Ez)).
      replace (1+k-d) with (1+(k-d)) by lia; reflexivity. }
    exists (X^^(k-d) *> [0;0] *> r0); split; [exact E|].
    unfold CutNum in *; rewrite E in HN.
    change (Num chi (k*2) (X^^d *> X^^1 *> X^^(k-d) *> [0;0] *> r0)) in HN.
    rewrite <-(Str_app_assoc (X^^d) (X^^1)), <-lpow_add in HN;exact HN.
  - assert (E:r=X^^(1+(k-d)) *> [0] *> Y *> r0).
    { rewrite (cut_prefix (1+k) d r ([0] *> Y *> r0) ltac:(lia) (eq_sym Ez)).
      replace (1+k-d) with (1+(k-d)) by lia; reflexivity. }
    exists (X^^(k-d) *> [0] *> Y *> r0); split; [exact E|].
    unfold CutNum in *; rewrite E in HN.
    change (Num chi (1+k*2) (X^^d *> X^^1 *> X^^(k-d) *> [0] *> Y *> r0)) in HN.
    rewrite <-(Str_app_assoc (X^^d) (X^^1)), <-lpow_add in HN;exact HN.
Qed.

Lemma CutNum_even2 q chi j d r:
  CutNum chi j d r -> d*2+q+11<=j ->
  exists s, CutNum chi (j+19+q*3) (d+15+q*2) s /\
    root (X^^(2+q) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^2 *> [0] *> X *> [0] *> s).
Proof.
  intros HN Hd; destruct (CutNum_a2 q _ _ _ _ HN ltac:(lia)) as [r1 [HN1 HA]].
  destruct (CutNum_takeX _ _ _ _ HN1 ltac:(lia)) as [t [E HT]].
  destruct (CutNum_Fs 12 _ _ _ _ HT ltac:(lia)) as [u [HU HF]].
  exists (X *> u); split.
  - change (CutNum chi (j+19+q*3) (d+15+q*2) (X^^1 *> u)).
    apply CutNum_prepend;applys_eq HU;flia.
  - eapply progress_trans;[exact HA|rewrite E;apply a2_cleanup,HF].
Qed.

Lemma C2_three_prepare p r s:
  sideRLs tm (hf^^5) r s ->
  root (X^^(2+p) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r) -->+
  root (X^^(2+p) *> [0] *> Y *> [0;0] *> X^^4 *> s).
Proof. intro H;unfold root;finish_calls H. Qed.

Lemma CutNum_C2_three p chi j d r:
  CutNum chi j d r -> d*2+3<=j ->
  exists s, CutNum chi (j+5) (d+1) s /\
    root (X^^(2+p) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(2+p) *> [0] *> Y *> [0;0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_Fs 5 _ _ _ _ HN ltac:(lia)) as [t [HT HF]].
  exists (X^^4 *> t);split;[apply CutNum_prepend;applys_eq HT;flia|apply C2_three_prepare,HF].
Qed.

Lemma CutNum_zeroY00_odd u chi j d r:
  CutNum chi j d r -> d*2<=j+1 ->
  exists s, CutNum chi (j+7+u*6) d s /\
    root (X^^(3+u*2) *> [0] *> Y *> [0;0] *> r) -->+
    root (X^^(2+u) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_hs 1 _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H1]].
  destruct (CutNum_hs (3+u*3) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 H2]].
  assert (HH:sideRLs tm (h^^(6+u*6)) (X *> [0;0] *> r1)
    (X^^(4+u*3) *> [0;0] *> r2)).
  { repeat rewrite <-Str_app_assoc.
    change (sideRLs tm (h^^(6+u*6)) ((X^^1++[0;0]) *> r1)
      ((X^^(4+u*3)++[0;0]) *> r2)).
    eapply segRLs_sideRLs_concat;[applys_eq (h_pairs_even (3+u*3) 0);flia|exact H2]. }
  destruct (CutNum_hs ((1+u)*3) _ _ _ _ HN2 ltac:(lia)) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[applys_eq (zeroY00_prepare (1+u*2) _ _ H1);flia|].
  eapply progress_evstep_trans;[applys_eq (normal_calls (1+u*2) _ _ ltac:(applys_eq HH;flia));flia|].
  change (root (X^^1 *> [0] *> X^^1 *> X^^(4+u*3) *> [0;0] *> r2) -->*
    root (X^^(2+u) *> [0] *> X^^2 *> [0;0] *> s)).
  rewrite root_X_add;applys_eq (marker_hcalls (1+u) 0 1 _ _ HM);flia.
Qed.

Lemma Num_even2_first t r:
  Num true (60+t*144) r -> exists s, Num false (69+t*168) s /\
    root (X^^(11+t*24) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(5+t*10) *> [0] *> X *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (CutNum_even2 (9+t*24) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HE]].
  destruct (CutNum_digit_tail true false _ (51+t*108) _ (21+t*60) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E]].
  destruct (Num_two_markers (3+t*10) 1 0 2 false _ _ _ HN2) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_evstep_trans;[applys_eq HE;flia|rewrite E;applys_eq HM;flia].
Qed.

Lemma Num_even2_second t r:
  Num true (60+t*144) r -> exists s, CutNum false (109+t*213) (18+t*10) s /\
    root (X^^(11+t*24) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^2 *> [0] *> X *> [0] *> s).
Proof.
  intro HN;destruct (Num_even2_first t _ HN) as [r1 [HN1 H1]].
  destruct (CutNum_C2_three (3+t*10) _ _ 0 _ HN1 ltac:(lia)) as [r2 [HN2 H2]].
  destruct (CutNum_zeroY00_odd (1+t*5) _ _ _ _ HN2 ltac:(lia)) as [r3 [HN3 H3]].
  destruct (CutNum_even2 (1+t*5) _ _ _ _ HN3 ltac:(lia)) as [s [HS H4]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[exact H1|].
  eapply progress_trans;[applys_eq H2;flia|].
  eapply progress_trans;[applys_eq H3;flia|applys_eq H4;flia].
Qed.

Lemma Num_even2_to_C2 s r:
  Num true (348+s*144*12) r -> exists t, Num true (495+s*203*12) t /\
    root (X^^(59+s*288) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(40+s*193) *> [0] *> X *> [0] *> X^^2 *> [0] *> Y *> t).
Proof.
  intro HN;destruct (Num_even2_second (2+s*12) _ ltac:(
    replace (60+(2+s*12)*144) with (348+s*144*12) by lia;exact HN)) as [r1 [HN1 HE]].
  destruct (CutNum_digit_tail false true _ (267+s*213*6) _ (230+s*193*6) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E]].
  destruct (Num_two_markers (38+s*193) 1 0 1 true _ _ _ HN2) as [t [HT HM]].
  exists t;split;[applys_eq HT;flia|].
  eapply progress_evstep_trans;[applys_eq HE;flia|rewrite E;applys_eq HM;flia].
Qed.

Lemma C2_odd_prepare p r s:
  sideRLs tm (hf^^8) r s ->
  root (X^^(3+p) *> [0] *> X *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  klj p 2 (0inf <* <[1;1;1;0;1;1]) s.
Proof. intro H;unfold root,klj;finish_calls H. Qed.

Lemma klj_zero_left b l r s:
  sideRLs tm (hf^^6) r s -> klj 0 b (l <* [1;1]) r -->+
  l <* [1] <* Dr^^(2+b) <* T1r {{B}}> s.
Proof.
  intro H;unfold klj.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^5) H) as [r1 [H1 H5]].
  follow11 (sideRLs_1 _ _ _ _ _ H1);finish_calls H5.
Qed.

Lemma C2_odd_finish b r s:
  sideRLs tm (hf^^6) r s ->
  0inf <* <[1;1;1;0;1] <* Dr^^(1+b) <* T1r {{B}}> r -->+
  root (X *> [0;0;0] *> X^^(1+b) *> [0] *> X^^3 *> s).
Proof.
  intro H;unfold root.
  destruct (sideRLs_split (ls1:=hf) (ls2:=hf^^5) H) as [r1 [H1 H5]].
  follow11 (sideRLs_1 _ _ _ _ _ H1);finish_calls H5.
Qed.

Lemma C2_odd_calls p r s:
  sideRLs tm (hf^^(20+p*6)) r s ->
  root (X^^(3+p) *> [0] *> X *> [0] *> X^^2 *> [0] *> Y *> r) -->+
  root (X *> [0;0;0] *> X^^(4+p) *> [0] *> X^^3 *> s).
Proof.
  intro H;replace (20+p*6) with (8+(p*6+(6+6))) in H by lia.
  rewrite (lpow_add _ 8 (p*6+(6+6))) in H.
  destruct (sideRLs_split H) as [r8 [H8 Hs]];rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [rm [Hm He]];rewrite lpow_add in He.
  destruct (sideRLs_split He) as [r6 [H6 Hf]].
  eapply progress_trans;[apply C2_odd_prepare,H8|].
  eapply evstep_progress_trans;
    [applys_eq (klj_cycles p 0 2 (0inf <* <[1;1;1;0;1;1]) _ _ Hm);flia|].
  eapply progress_trans;
    [apply (klj_zero_left (2+p) (0inf <* <[1;1;1;0])),H6|].
  applys_eq (C2_odd_finish (3+p) _ _ Hf);flia.
Qed.

Lemma CutNum_C2_odd p chi j d r:
  CutNum chi j d r -> d*2+18+p*6<=j ->
  exists s, CutNum chi (j+20+p*6) (d+17+p*6) s /\
    root (X^^(3+p) *> [0] *> X *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X *> [0;0;0] *> X^^(4+p) *> [0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_Fs (20+p*6) _ _ _ _ HN ltac:(lia)) as [t [HT HF]].
  exists (X^^3 *> t);split;[apply CutNum_prepend;applys_eq HT;flia|apply C2_odd_calls,HF].
Qed.

Lemma C2_post_calls b r s:
  sideRLs tm (hf^^24) r s ->
  root (X *> [0;0;0] *> X^^(1+b) *> [0] *> X *> r) -->+
  root (X^^2 *> [0] *> X *> [0] *> X^^(1+b) *> [0] *> X *> s).
Proof. intro H;apply a2_cleanup,F_markers;applys_eq H;flia. Qed.

Lemma CutNum_C2_post b chi j d r:
  CutNum chi j d r -> d*2+24<=j ->
  exists s, CutNum chi (j+24) (d+24) s /\
    root (X *> [0;0;0] *> X^^(1+b) *> [0] *> r) -->+
    root (X^^2 *> [0] *> X *> [0] *> X^^(1+b) *> [0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_takeX _ _ _ _ HN ltac:(lia)) as [t [E HT]].
  destruct (CutNum_Fs 24 _ _ _ _ HT ltac:(lia)) as [u [HU HF]].
  exists (X *> u);split.
  - change (CutNum chi (j+24) (d+24) (X^^1 *> u)).
    apply CutNum_prepend;applys_eq HU;flia.
  - rewrite E;apply C2_post_calls,HF.
Qed.

Lemma Num_three_markers m p b c a e chi j r:
  Num chi j r -> exists s, Num chi (j+m*12) s /\
    root (X^^(1+p) *> [0] *> X^^(1+b) *> [0] *> X^^(1+c) *> [0] *>
      X^^(1+a+m*12) *> sep e *> r) -->*
    root (X^^(1+p+m) *> [0] *> X^^(1+b) *> [0] *> X^^(1+c) *> [0] *>
      X^^(1+a) *> sep e *> s).
Proof.
  intro HN;destruct (Num_add (m*12) _ _ _ HN) as [s [HS HH]].
  assert (HF:sideRLs tm (hf^^(m*24))
    (X^^(a+m*12) *> sep e *> r) (X^^a *> sep e *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat;[applys_eq (F_pairs (m*12) a e);flia|exact HH]. }
  exists s;split;[exact HS|].
  applys_eq (marker_calls m p _ _ (F_markers (m*6) b _ _
    ltac:(applys_eq (F_markers (m*12) c _ _ ltac:(applys_eq HF;flia));flia)));flia.
Qed.

Lemma Num_C2_to_post v r:
  Num true (495+v*812*12) r -> exists s, Num false (486+v*812*12) s /\
    root (X^^(40+v*772) *> [0] *> X *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(11+v*213) *> [0] *> X *> [0] *> X^^(41+v*772) *> [0] *>
      X^^10 *> [0] *> Y *> s).
Proof.
  intro HN;destruct (CutNum_C2_odd (37+v*772) _ _ 0 _ HN ltac:(lia)) as [r1 [HN1 HC]].
  destruct (CutNum_C2_post (40+v*772) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 HP]].
  destruct (CutNum_digit_tail true true _ (378+v*599*12) _ (118+v*213*12) _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E]].
  destruct (Num_three_markers (9+v*213) 1 0 (40+v*772) 9 true _ _ _ HN3) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[applys_eq HC;flia|].
  eapply progress_evstep_trans;[exact HP|rewrite E;applys_eq HM;flia].
Qed.

Lemma Num_even2_to_post v r:
  Num true (348+v*576*12) r -> exists s, Num false (486+v*812*12) s /\
    root (X^^(59+v*288*4) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(11+v*213) *> [0] *> X *> [0] *> X^^(41+v*772) *> [0] *>
      X^^10 *> [0] *> Y *> s).
Proof.
  intro HN;destruct (Num_even2_to_C2 (v*4) _ ltac:(
    replace (348+v*4*144*12) with (348+v*576*12) by lia;exact HN)) as [r1 [HN1 HE]].
  destruct (Num_C2_to_post v _ ltac:(
    replace (495+v*812*12) with (495+v*4*203*12) by lia;exact HN1)) as [s [HS HC]].
  exists s;split;[exact HS|].
  replace (59+v*4*288) with (59+v*288*4) in HE by lia.
  replace (40+v*4*193) with (40+v*772) in HE by lia.
  eapply progress_trans;[exact HE|exact HC].
Qed.

Lemma Num_B21_to_C2post w r:
  Num true (90+(9+(42+w*288)*32)*576) r ->
  exists s, Num false (486+(35+796*300+w*169*125*77)*812*12) s /\
    root (X^^(16+(9+(42+w*288)*32)*96) *> [0] *> X^^2 *> [0] *> Y *> r) -->+
    root (X^^(11+(35+796*300+w*169*125*77)*213) *> [0] *> X *> [0] *>
      X^^(41+(35+796*300+w*169*125*77)*772) *> [0] *> X^^10 *> [0] *> Y *> s).
Proof.
  intro HN;destruct (Num_B21_to_even2 (42+w*288) _ HN) as [r1 [HN1 HB]].
  destruct (Num_even2_to_post (35+796*300+w*169*125*77) _ ltac:(
    replace (348+(35+796*300+w*169*125*77)*576*12) with
      (36+(141+(58+90*30+(42+w*288)*125*77)*169)*24) by lia;exact HN1)) as [s [HS HC]].
  exists s;split;[exact HS|].
  replace (59+(35+796*300+w*169*125*77)*288*4) with
    (571+(58+90*30+(42+w*288)*125*77)*676) in HC by lia.
  eapply progress_trans;[exact HB|exact HC].
Qed.

Lemma init_C2_post:
  exists r, Num false (486+(35+796*300)*812*12) r /\
    c0 -->* root (X^^(11+(35+796*300)*213) *> [0] *> X *> [0] *>
      X^^(41+(35+796*300)*772) *> [0] *> X^^10 *> [0] *> Y *> r).
Proof.
  destruct init_B21 as [r [HN HR]].
  assert (HN0:Num true (90+(9+(42+0*288)*32)*576) r).
  { replace (90+(9+(42+0*288)*32)*576) with 779418 by (apply Nat.eqb_eq;reflexivity);exact HN. }
  destruct (Num_B21_to_C2post 0 _ HN0) as [s [HS HC]].
  rewrite !Nat.mul_0_l,!Nat.add_0_r in HS,HC.
  exists s;split;[exact HS|].
  follow HR;apply progress_evstep.
  replace 129904 with (16+(9+42*32)*96) by (apply Nat.eqb_eq;reflexivity);exact HC.
Qed.


(* The actual terminal10 spill and its ordinary mixed-column batch. *)
Lemma marker_odd10_spill p b r s:
  sideRLs tm (hf^^12) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^(2+b) *> [0] *> X^^10 *> [0] *> Y *> r) -->+
  root (X^^(2+p) *> [0] *> X *> [0] *> X^^(1+b) *> [0;0] *> X *> [0] *> X^^11 *> s).
Proof. intro H;unfold root;finish_calls H. Qed.

Lemma CutNum_odd10_spill p b chi j d r:
  CutNum chi j d r -> d*2+10<=j ->
  exists s, CutNum chi (j+12) (d+1) s /\
    root (X^^(1+p) *> [0] *> X *> [0] *> X^^(2+b) *> [0] *> X^^10 *> [0] *> Y *> r) -->+
    root (X^^(2+p) *> [0] *> X *> [0] *> X^^(1+b) *> [0;0] *> X *> [0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_Fs 12 _ _ _ _ HN ltac:(lia)) as [t [HT HF]].
  exists (X^^11 *> t);split;[apply CutNum_prepend;applys_eq HT;flia|apply marker_odd10_spill,HF].
Qed.

Lemma Num_mixed_pair_batch m p b c a e f chi j r:
  Num chi j r -> exists s, Num chi (j+m*6) s /\
    root (X^^(1+p) *> [0] *> X *> [0] *> X^^(1+b+m*6) *> sep e *>
      X^^(1+c) *> [0] *> X^^(1+a+m*6) *> sep f *> r) -->*
    root (X^^(1+p+m) *> [0] *> X *> [0] *> X^^(1+b) *> sep e *>
      X^^(1+c+m*6) *> [0] *> X^^(1+a) *> sep f *> s).
Proof.
  intro HN;destruct (Num_add (m*6) _ _ _ HN) as [s [HS HH]].
  assert (HF:sideRLs tm (hf^^(m*12))
    (X^^(a+m*6) *> sep f *> r) (X^^a *> sep f *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat;[applys_eq (F_pairs (m*6) a f);flia|exact HH]. }
  assert (HM:sideRLs tm (h^^(m*6))
    (X^^(1+c) *> [0] *> X^^(1+a+m*6) *> sep f *> r)
    (X^^(1+c+m*6) *> [0] *> X^^(1+a) *> sep f *> s)).
  { change (sideRLs tm (h^^(m*6))
      (markers [1+c]%nat (X^^(a+m*6) *> sep f *> r))
      (markers [1+c+m*6]%nat (X^^a *> sep f *> s))).
    apply (h_columns [] (m*6) (1+c));applys_eq HF;cbn [length Nat.pow];flia. }
  assert (HG:sideRLs tm (hf^^(m*12))
    (X^^(b+m*6) *> sep e *> X^^(1+c) *> [0] *> X^^(1+a+m*6) *> sep f *> r)
    (X^^b *> sep e *> X^^(1+c+m*6) *> [0] *> X^^(1+a) *> sep f *> s)).
  { rewrite <-(Str_app_assoc (X^^(b+m*6)) (sep e)), <-(Str_app_assoc (X^^b) (sep e)).
    eapply segRLs_sideRLs_concat;[applys_eq (F_pairs (m*6) b e);flia|exact HM]. }
  exists s;split;[exact HS|].
  applys_eq (marker_calls m p _ _ (F_markers (m*6) 0 _ _ ltac:(applys_eq HG;flia)));flia.
Qed.

Lemma Num_C2_spill v r:
  Num false (486+v*812*12) r -> exists s, Num true (249+v*406*12) s /\
    root (X^^(11+v*213) *> [0] *> X *> [0] *> X^^(41+v*772) *> [0] *> X^^10 *> [0] *> Y *> r) -->+
    root (X^^(12+v*213) *> [0] *> X *> [0] *> X^^(40+v*772) *> [0;0] *> X *> [0] *>
      X^^(249+v*406*12) *> [0;0] *> s).
Proof.
  intro HN;destruct (CutNum_odd10_spill (10+v*213) (39+v*772) _ _ 0 _ HN ltac:(lia)) as [t [HT HC]].
  destruct (CutNum_digit_tail false false _ (249+v*406*12) _ (249+v*406*12) _ HT
    ltac:(lia) ltac:(lia)) as [s [HS E]].
  exists s;split;[exact HS|rewrite E in HC;applys_eq HC;flia].
Qed.

Lemma Num_C2_to_mixed w r:
  Num false (486+(2+w*3)*812*12) r ->
  exists s, Num true (249+(2+w*3)*406*12+(263+w*386)*6) s /\
    root (X^^(11+(2+w*3)*213) *> [0] *> X *> [0] *> X^^(41+(2+w*3)*772) *> [0] *>
      X^^10 *> [0] *> Y *> r) -->+
    root (X^^(701+w*205*5) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1+(263+w*386)*6) *> [0] *> X^^(15+(28+w*41)*300) *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C2_spill (2+w*3) _ HN) as [t [HT HS]].
  destruct (Num_mixed_pair_batch (263+w*386) (11+(2+w*3)*213) 5 0 (14+(28+w*41)*300)
    false false _ _ _ HT) as [s [HN1 HB]].
  exists s;split;[exact HN1|].
  eapply progress_evstep_trans;[exact HS|].
  replace (1+5+(263+w*386)*6) with (40+(2+w*3)*772) in HB by lia.
  replace (1+(14+(28+w*41)*300)+(263+w*386)*6) with
    (249+(2+w*3)*406*12) in HB by lia.
  replace (1+(11+(2+w*3)*213)+(263+w*386)) with (701+w*205*5) in HB by lia.
  exact HB.
Qed.

Lemma Num_C2_mixed_source u r:
  Num false (486+(35+u*300)*812*12) r ->
  exists s, Num true (249+(2+(11+u*100)*3)*406*12+(263+(11+u*100)*386)*6) s /\
    root (X^^(11+(35+u*300)*213) *> [0] *> X *> [0] *> X^^(41+(35+u*300)*772) *> [0] *>
      X^^10 *> [0] *> Y *> r) -->+
    root (X^^(701+(11+u*100)*205*5) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1+(263+(11+u*100)*386)*6) *> [0] *> X^^(15+(28+(11+u*100)*41)*300) *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C2_to_mixed (11+u*100) _ ltac:(
    replace (2+(11+u*100)*3) with (35+u*300) by lia;exact HN)) as [s [HS HC]].
  exists s;split;[exact HS|].
  replace (2+(11+u*100)*3) with (35+u*300) in HC by lia;exact HC.
Qed.

Lemma init_C2_mixed:
  exists r, Num true (249+(2+(11+796*100)*3)*406*12+(263+(11+796*100)*386)*6) r /\
    c0 -->* root (X^^(701+(11+796*100)*205*5) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1+(263+(11+796*100)*386)*6) *> [0] *> X^^(15+(28+(11+796*100)*41)*300) *> [0;0] *> r).
Proof.
  destruct init_C2_post as [r [HN HR]].
  destruct (Num_C2_mixed_source 796 _ HN) as [s [HS HC]].
  exists s;split;[exact HS|follow HR;apply progress_evstep,HC].
Qed.

(* Final native continuation: even6, sourced collapse, and scalar return to Q.
   Each parameter block was checked independently against the frozen module.
   Large native parameters stay in factored nat expressions; only d=33 is
   instantiated after all whole-tape joins and guards are proved. *)
Lemma C_even6_calls p r s:
  sideRLs tm (hf^^9) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X^^6 *> [0;0] *> r) -->+
  root (X^^(10+p) *> s).
Proof. intro H;unfold root;finish_calls H. Qed.

(* Marker routing turns the nine opaque calls into eighteen digit calls,
   hence nine G calls on the complete Num. The terminal reserve is a+1. *)
Lemma Num_C_even6_marked p b a chi j r:
  Num chi j r -> exists s, Num chi (j+9) s /\
    root (X^^(1+p) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^b *> [0] *> X^^(10+a) *> [0;0] *> r) -->+
    root (X^^(10+p+b) *> [0] *> X^^(1+a) *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_add 9 _ _ _ HN) as [s [HS HH]].
  assert (HF:sideRLs tm (hf^^18)
    (X^^(a+9) *> [0;0] *> r) (X^^a *> [0;0] *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat;[apply (F_pairs 9 a false)|exact HH]. }
  assert (HM:sideRLs tm (hf^^9)
    (X^^b *> [0] *> X^^(10+a) *> [0;0] *> r)
    (X^^b *> [0] *> X^^(1+a) *> [0;0] *> s)).
  { replace (10+a) with (1+(a+9)) by lia.
    change (sideRLs tm (hf^^9)
      (X^^b *> [0] *> X *> X^^(a+9) *> [0;0] *> r)
      (X^^b *> [0] *> X *> X^^a *> [0;0] *> s)).
    exact (F_markers 9 b _ _ HF). }
  exists s;split;[exact HS|].
  pose proof (C_even6_calls p _ _ HM) as HC.
  rewrite root_X_front in HC;exact HC.
Qed.

Lemma Num_C2_collapse_first w r:
  Num true ((571+11*1000)+w*(932+16*1000)) r ->
  exists s, Num true ((983+19*1000)+w*(232+29*1000)) s /\
    root (X^^(701+w*1025) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1579+w*2316) *> [0] *> X^^((415+8*1000)+w*(300+12*1000)) *> [0;0] *> r) -->+
    root (X^^((90+5*1000)+w*(441+7*1000)) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C_even6_marked (700+w*1025) (1579+w*2316)
    ((405+8*1000)+w*(300+12*1000)) _ _ _ HN) as [t [HT HE]].
  destruct (Num_markers (2801+w*4100) (2288+w*3341) 2 _ _ _ HT)
    as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (1+(700+w*1025)) with (701+w*1025) in HE by lia.
  replace (10+((405+8*1000)+w*(300+12*1000))) with
    ((415+8*1000)+w*(300+12*1000)) in HE by lia.
  replace (10+(700+w*1025)+(1579+w*2316)) with
    (1+(2288+w*3341)) in HE by lia.
  replace (1+((405+8*1000)+w*(300+12*1000))) with
    (1+2+(2801+w*4100)*3) in HE by lia.
  replace (1+(2288+w*3341)+(2801+w*4100)) with
    ((90+5*1000)+w*(441+7*1000)) in HM by lia.
  eapply progress_evstep_trans;[exact HE|exact HM].
Qed.

(* The actual w=11+100u is odd. Work at w=1+2z before instantiation;
   every complete O/E split and physical Cut is kept in the proof. *)
Lemma Num_C2_collapse_odd z r:
  Num true ((571+11*1000)+(1+z*2)*(932+16*1000)) r ->
  exists s, Num true ((437+98*1000)+z*(928+116*1000)) s /\
    root (X^^(701+(1+z*2)*1025) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1579+(1+z*2)*2316) *> [0] *> X^^((415+8*1000)+(1+z*2)*(300+12*1000)) *> [0;0] *> r) -->+
    root (X^^((407+16*1000)+z*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C2_collapse_first (1+z*2) _ HN) as [r1 [HN1 HC]].
  destruct (CutNum_a3 ((530+12*1000)+z*(882+14*1000)) _ _ 0 _ HN1 ltac:(lia)) as [r2 [HN2 HA]].
  destruct (CutNum_digit_tail true true _ ((404+43*1000)+z*(555+51*1000)) _ ((345+18*1000)+z*(791+21*1000)) _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E2]].
  destruct (Num_normal_odd ((343+18*1000)+z*(791+21*1000)) _ _ _ HN3) as [r4 [HN4 HN0]].
  destruct (CutNum_digit_tail false false _ ((219+49*1000)+z*(464+58*1000)) 0 ((220+49*1000)+z*(464+58*1000)) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_markers ((406+16*1000)+z*(488+19*1000)) 0 2 _ _ _ HN5) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (1+((530+12*1000)+z*(882+14*1000))) with
    ((90+5*1000)+(1+z*2)*(441+7*1000)) in HA by lia.
  replace (2+((343+18*1000)+z*(791+21*1000))) with
    ((345+18*1000)+z*(791+21*1000)) in HN0 by lia.
  replace (1+0+((406+16*1000)+z*(488+19*1000))) with
    ((407+16*1000)+z*(488+19*1000)) in HM by lia.
  eapply progress_trans;[exact HC|].
  eapply progress_trans;[exact HA|].
  rewrite E2;eapply progress_evstep_trans;[exact HN0|].
  rewrite E4.
  change (root (X^^1 *> [0] *> X^^1 *> X^^((220+49*1000)+z*(464+58*1000)) *> [0;0] *> r5) -->*
    root (X^^((407+16*1000)+z*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> s)).
  rewrite root_X_add.
  replace (1+((220+49*1000)+z*(464+58*1000))) with
    (1+2+((406+16*1000)+z*(488+19*1000))*3) by lia.
  exact HM.
Qed.

Lemma Num_C2_collapse_source u r:
  Num true (249+(2+(11+u*100)*3)*406*12+(263+(11+u*100)*386)*6) r ->
  exists s, Num true ((437+98*1000)+(5+u*50)*(928+116*1000)) s /\
    root (X^^(701+(11+u*100)*205*5) *> [0] *> X *> [0] *> X^^6 *> [0;0] *>
      X^^(1+(263+(11+u*100)*386)*6) *> [0] *> X^^(15+(28+(11+u*100)*41)*300) *> [0;0] *> r) -->+
    root (X^^((407+16*1000)+(5+u*50)*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C2_collapse_odd (5+u*50) _ ltac:(
    replace ((571+11*1000)+(1+(5+u*50)*2)*(932+16*1000)) with
      (249+(2+(11+u*100)*3)*406*12+(263+(11+u*100)*386)*6) by lia;
    exact HN)) as [s [HS HC]].
  exists s;split;[exact HS|].
  replace (701+(1+(5+u*50)*2)*1025) with
    (701+(11+u*100)*205*5) in HC by lia.
  replace (1579+(1+(5+u*50)*2)*2316) with
    (1+(263+(11+u*100)*386)*6) in HC by lia.
  replace ((415+8*1000)+(1+(5+u*50)*2)*(300+12*1000)) with
    (15+(28+(11+u*100)*41)*300) in HC by lia.
  exact HC.
Qed.

Lemma init_C2_collapse:
  exists r, Num true ((437+98*1000)+(5+796*50)*(928+116*1000)) r /\
    c0 -->* root (X^^((407+16*1000)+(5+796*50)*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> r).
Proof.
  destruct init_C2_mixed as [r [HN HR]].
  destruct (Num_C2_collapse_source 796 _ HN) as [s [HS HC]].
  exists s;split;[exact HS|].
  follow HR;apply progress_evstep;exact HC.
Qed.

Lemma Num_C_odd n r:
  Num false (82+n*228) r -> exists s, Num false (177+n*462) s /\
    root (X^^(2+n*2) *> [0] *> X^^(37+n*102) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(31+n*77) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C_short (n*2) _ ltac:(applys_eq HN;flia)) as [r1 [HN1 HC]].
  destruct (CutNum_digit_tail false true _ (98+n*267) _ (27+n*65) _ HN1
    ltac:(lia) ltac:(lia)) as [r2 [HN2 E1]].
  destruct (Num_normal_odd (25+n*65) _ _ _ HN2) as [r3 [HN3 HN0]].
  destruct (CutNum_digit_tail true false _ (87+n*231) 0 (90+n*231) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_markers (30+n*77) 0 0 _ _ _ HN4) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (37+n*2*51) with (37+n*102) in HC by lia.
  replace (2+(25+n*65)) with (27+n*65) in HN0 by lia.
  replace (1+0+(30+n*77)) with (31+n*77) in HM by lia.
  eapply progress_trans;[exact HC|].
  rewrite E1;eapply progress_evstep_trans;[exact HN0|].
  rewrite E3.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(90+n*231) *> [0;0] *> r4) -->*
    root (X^^(31+n*77) *> [0] *> X *> [0;0] *> s)).
  rewrite root_X_add.
  replace (1+(90+n*231)) with (1+0+(30+n*77)*3) by lia;exact HM.
Qed.

(* This single symbolic composition accounts for all nine first scalar
   rows. Num_A2_to_C already composes four of those rows. *)
Lemma Num_C2_to_scalar_C u r:
  Num true ((437+98*1000)+(5+u*50)*(928+116*1000)) r ->
  exists s, Num false (177+((577+35*1000)+u*(500+304*1000))*462) s /\
    root (X^^((407+16*1000)+(5+u*50)*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(31+((577+35*1000)+u*(500+304*1000))*77) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_Oa3_odd_return ((922+56*1000)+u*(200+487*1000)) _ ltac:(
    replace (13+((922+56*1000)+u*(200+487*1000))*12) with
      ((437+98*1000)+(5+u*50)*(928+116*1000)) by lia;exact HN)) as [r1 [HN1 H1]].
  destruct (Num_one_mod6_even ((487+9*1000)+u*(200+81*1000)) _ ltac:(
    replace (35+((487+9*1000)+u*(200+81*1000))*144) with
      (35+((922+56*1000)+u*(200+487*1000))*24) by lia;exact HN1)) as [r2 [HN2 H2]].
  destruct (Num_critical_odd ((436+47*1000)+u*(0+406*1000)) _ ltac:(
    replace (29+((436+47*1000)+u*(0+406*1000))*72) with
      (101+((487+9*1000)+u*(200+81*1000))*360) by lia;exact HN2)) as [r3 [HN3 H3]].
  destruct (Num_A2_to_C ((154+71*1000)+u*(0+609*1000)) _ ltac:(
    replace (47+((154+71*1000)+u*(0+609*1000))*72) with
      (47+((436+47*1000)+u*(0+406*1000))*108) by lia;exact HN3)) as [r4 [HN4 H4]].
  destruct (Num_C_odd ((577+35*1000)+u*(500+304*1000)) _ ltac:(
    replace (82+((577+35*1000)+u*(500+304*1000))*228) with
      (82+((154+71*1000)+u*(0+609*1000))*114) by lia;exact HN4)) as [s [HS H5]].
  exists s;split;[exact HS|].
  replace (3+((922+56*1000)+u*(200+487*1000))*2) with
    ((407+16*1000)+(5+u*50)*(488+19*1000)) in H1 by lia.
  replace (7+((487+9*1000)+u*(200+81*1000))*24) with
    (7+((922+56*1000)+u*(200+487*1000))*4) in H2 by lia.
  replace (6+((436+47*1000)+u*(0+406*1000))*12) with
    (18+((487+9*1000)+u*(200+81*1000))*60) in H3 by lia.
  replace (2+((154+71*1000)+u*(0+609*1000))*2) with
    (2+((436+47*1000)+u*(0+406*1000))*3) in H4 by lia.
  replace (2+((577+35*1000)+u*(500+304*1000))*2) with
    (2+((154+71*1000)+u*(0+609*1000))) in H5 by lia.
  replace (37+((577+35*1000)+u*(500+304*1000))*102) with
    (37+((154+71*1000)+u*(0+609*1000))*51) in H5 by lia.
  eapply progress_trans;[exact H1|].
  eapply progress_trans;[exact H2|].
  eapply progress_trans;[exact H3|].
  eapply progress_trans;[exact H4|exact H5].
Qed.

Lemma Num_scalar_a1 a r:
  Num false ((511+26*1000)+a*(264+33*1000)) r -> exists s, Num true ((932+30*1000)+a*(808+38*1000)) s /\
    root (X^^(4420+a*(544+5*1000)) *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(3683+a*4620) *> [0] *> X^^2 *> [0;0] *> s).
Proof.
  intro HN;destruct (CutNum_a1_odd (4419+a*(544+5*1000)) false _ 0 ((885+19*1000)+a*(948+24*1000))
    _ HN ltac:(lia) ltac:(lia) ltac:(lia)) as [t [HT HA]].
  destruct (Num_markers (3682+a*4620) 0 1 _ _ _ HT) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (1+(4419+a*(544+5*1000))) with (4420+a*(544+5*1000)) in HA by lia.
  replace (2+(1+((885+19*1000)+a*(948+24*1000))-(0+(4420+a*(544+5*1000))*2)))
    with (1+1+(3682+a*4620)*3) in HA by lia.
  replace (1+0+(3682+a*4620)) with (3683+a*4620) in HM by lia.
  eapply progress_evstep_trans;[exact HA|exact HM].
Qed.

(* Scalar row11: no changes to the old even2 F-caller proof. *)
Lemma Num_scalar_even2 a r:
  Num true ((932+30*1000)+a*(808+38*1000)) r -> exists s, Num false ((615+34*1000)+a*(428+43*1000)) s /\
    root (X^^(3683+a*4620) *> [0] *> X^^2 *> [0;0] *> r) -->+
    root (X^^(2272+a*2849) *> [0] *> X *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN;destruct (CutNum_even2 (3681+a*4620) _ _ 0 _ HN ltac:(lia)) as [t [HT HE]].
  destruct (CutNum_digit_tail true false _ ((995+20*1000)+a*(334+26*1000)) _ ((621+13*1000)+a*(94+17*1000)) _ HT
    ltac:(lia) ltac:(lia)) as [u [HU E]].
  destruct (Num_two_markers (2270+a*2849) 1 0 0 false _ _ _ HU) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (2+(3681+a*4620)) with (3683+a*4620) in HE by lia.
  replace (1+1+(2270+a*2849)) with (2272+a*2849) in HM by lia.
  replace (1+0+(2270+a*2849)*6) with
    ((621+13*1000)+a*(94+17*1000)) in HM by lia.
  eapply progress_evstep_trans;[exact HE|rewrite E;exact HM].
Qed.

(* Actual R1 phase: keep the leading zero and the emitted XX. *)
Lemma C1_zero4_prepare p r s:
  sideRLs tm (hf^^3) r s ->
  root (X^^(1+p) *> [0] *> X *> [0] *> X *> [0;0] *> r) -->+
  root ([0] *> X^^(1+p) *> [0;0;0;0] *> X^^2 *> s).
Proof. intro H;unfold root;finish_calls H. Qed.

Lemma CutNum_C1_even u chi j d r:
  CutNum chi j d r -> d*2+1<=j ->
  exists s, CutNum chi (j+5+u*6) (d+1) s /\
    root (X^^(2+u*2) *> [0] *> X *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(1+u) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intros HN Hd;destruct (CutNum_Fs 3 _ _ _ _ HN ltac:(lia)) as [t [HT HF]].
  assert (HN1:CutNum chi (j+3) (d+1) (X^^2 *> t)).
  { apply CutNum_prepend;applys_eq HT;flia. }
  destruct (CutNum_zero4_leading_even u _ _ _ _ HN1 ltac:(lia)) as [s [HS HZ]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[applys_eq (C1_zero4_prepare (1+u*2) _ _ HF);flia|exact HZ].
Qed.

(* Rows12--13, on the actual correlated even q/odd b branch only. *)
Lemma Num_scalar_C1_return c r:
  Num false ((615+34*1000)+(2+(c*4))*(428+43*1000)) r ->
  exists s, Num false ((764+290*1000)+c*(800+415*1000)) s /\
    root (X^^(2272+(2+c*4)*2849) *> [0] *> X *> [0] *> X *> [0;0] *> r) -->+
    root (X^^((462+48*1000)+c*(300+69*1000)) *> [0] *> X^^2 *> [0] *> Y *> s).
Proof.
  intro HN;destruct (CutNum_C1_even (1135+(1+c*2)*2849) _ _ 0 _ HN ltac:(lia))
    as [r1 [HN1 H1]].
  destruct (CutNum_a3 (3984+c*(698+5*1000)) _ _ _ _ HN1 ltac:(lia)) as [r2 [HN2 HA]].
  destruct (CutNum_digit_tail false false _ ((670+78*1000)+c*(497+112*1000)) _ ((700+70*1000)+c*(101+101*1000)) _ HN2
    ltac:(lia) ltac:(lia)) as [r3 [HN3 E2]].
  destruct (Num_normal ((698+70*1000)+c*(101+101*1000)) _ _ _ HN3) as [r4 [HN4 HN0]].
  destruct (CutNum_digit_tail true true _ ((381+145*1000)+c*(900+207*1000)) 0 ((384+145*1000)+c*(900+207*1000)) _ HN4
    ltac:(lia) ltac:(lia)) as [r5 [HN5 E4]].
  destruct (Num_marker_phase ((461+48*1000)+c*(300+69*1000)) 0 1 true _ _ _ HN5) as [s [HS HM]].
  exists s;split;[applys_eq HS;flia|].
  replace (2+(1135+(1+c*2)*2849)*2) with (2272+(2+c*4)*2849) in H1 by lia.
  replace (1+(3984+c*(698+5*1000))) with (1+(1135+(1+c*2)*2849)) in HA by lia.
  replace (2+((698+70*1000)+c*(101+101*1000))) with
    ((700+70*1000)+c*(101+101*1000)) in HN0 by lia.
  replace (1+0+((461+48*1000)+c*(300+69*1000))) with
    ((462+48*1000)+c*(300+69*1000)) in HM by lia.
  eapply progress_trans;[exact H1|].
  eapply progress_trans;[exact HA|].
  rewrite E2;eapply progress_evstep_trans;[exact HN0|].
  rewrite E4.
  change (root (X^^1 *> [0] *> X^^1 *> X^^((384+145*1000)+c*(900+207*1000)) *> [0] *> Y *> r5) -->*
    root (X^^((462+48*1000)+c*(300+69*1000)) *> [0] *> X^^2 *> [0] *> Y *> s)).
  rewrite root_X_add.
  replace (1+((384+145*1000)+c*(900+207*1000))) with
    (1+1+((461+48*1000)+c*(300+69*1000))*3) by lia;exact HM.
Qed.

(* Row14 is the already compiled real E-birth underflow theorem. *)
Lemma Num_scalar_to_terminal c r:
  Num false ((511+26*1000)+(2+c*4)*(264+33*1000)) r ->
  exists s, Num true (143+(4038+c*(775+5*1000))*288) s /\
    root (X^^(4420+(2+c*4)*(544+5*1000)) *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(25+(4038+c*(775+5*1000))*48) *> [0] *> X *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_scalar_a1 (2+c*4) _ HN) as [r1 [HN1 H1]].
  destruct (Num_scalar_even2 (2+c*4) _ HN1) as [r2 [HN2 H2]].
  destruct (Num_scalar_C1_return c _ HN2) as [r3 [HN3 H3]].
  destruct (Num_Ebirth_even_return ((229+24*1000)+c*(650+34*1000)) _ ltac:(applys_eq HN3;flia)) as [s [HS H4]].
  exists s;split.
  { replace (143+(4038+c*(775+5*1000))*288) with
      (95+((229+24*1000)+c*(650+34*1000))*48) by lia;exact HS. }
  replace (4+((229+24*1000)+c*(650+34*1000))*2) with
    ((462+48*1000)+c*(300+69*1000)) in H4 by lia.
  replace (17+((229+24*1000)+c*(650+34*1000))*8) with
    (25+(4038+c*(775+5*1000))*48) in H4 by lia.
  eapply progress_trans;[exact H1|].
  eapply progress_trans;[exact H2|].
  eapply progress_trans;[exact H3|exact H4].
Qed.

Lemma CutNum_zero4_leading_odd u b j d r:
  CutNum b j d r -> d*2<=j+1 ->
  exists s, CutNum b (j+6+u*6) d s /\
    root ([0] *> X^^(3+u*2) *> [0;0;0;0] *> r) -->+
    root (X^^(2+u) *> [0] *> X *> [0] *> Y *> s).
Proof.
  intros HN Hd;destruct (CutNum_hs (3+u*3) _ _ _ _ HN ltac:(lia)) as [r1 [HN1 H1]].
  assert (HH:sideRLs tm (h^^(6+u*6)) ([0] *> Y *> r)
    (X^^(3+u*3) *> [0] *> Y *> r1)).
  { repeat rewrite <-Str_app_assoc;repeat rewrite <-app_assoc.
    change (sideRLs tm (h^^(6+u*6)) ((X^^0++[0]++Y) *> r)
      ((X^^(3+u*3)++[0]++Y) *> r1)).
    eapply segRLs_sideRLs_concat;[applys_eq (h_pairs_odd (3+u*3) 0);flia|exact H1]. }
  destruct (CutNum_hs (3+u*3) _ _ _ _ HN1 ltac:(lia)) as [s [HS H2]].
  assert (HF:sideRLs tm (hf^^(6+u*6))
    (X^^(3+u*3) *> sep true *> r1) (sep true *> s)).
  { repeat rewrite <-Str_app_assoc.
    eapply segRLs_sideRLs_concat;[applys_eq (F_pairs (3+u*3) 0 true);flia|exact H2]. }
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[applys_eq (leading_zero4 (1+u*2) r);flia|].
  eapply progress_evstep_trans;
    [applys_eq (normal_calls (1+u*2) _ _ ltac:(applys_eq HH;flia));flia|].
  change (root (X^^1 *> [0] *> X^^1 *> X^^(3+u*3) *> sep true *> r1) -->*
    root (X^^(2+u) *> [0] *> X *> sep true *> s)).
  applys_eq (marker_calls (1+u) 0 _ _ ltac:(applys_eq HF;flia));flia.
Qed.

(* Universal terminal affine entry, not a further numerical trajectory. *)
Lemma Num_terminal_Q v r:
  Num true (143+v*288) r -> exists s, Num false (521+v*1014) s /\
    root (X^^(25+v*48) *> [0] *> X *> [0;0] *> r) -->+
    root (X^^(88+v*169) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (CutNum_a1_even (24+v*48) true _ 0 (107+v*216) (60+v*120)
    _ HN ltac:(lia) ltac:(lia) ltac:(lia)) as [r1 [HN1 H1]].
  destruct (Num_marker_phase (20+v*40) 0 0 true _ _ _ HN1) as [r2 [HN2 H2]].
  destruct (CutNum_odd1 (19+v*40) _ _ 0 _ HN2 ltac:(lia)) as [r3 [HN3 H3]].
  destruct (CutNum_digit_tail false false _ (145+v*288) _ (25+v*48) _ HN3
    ltac:(lia) ltac:(lia)) as [r4 [HN4 E3]].
  destruct (Num_two_markers (4+v*8) 0 (61+v*120) 0 false _ _ _ HN4) as [r5 [HN5 H5]].
  destruct (CutNum_nested_even_front (4+v*8) (60+v*120) _ _ 0 _ HN5 ltac:(lia))
    as [r6 [HN6 H6]].
  destruct (CutNum_zero4_leading_odd (1+v*4) _ _ _ _ HN6 ltac:(lia)) as [r7 [HN7 H7]].
  destruct (CutNum_odd1 (1+v*4) _ _ _ _ HN7 ltac:(lia)) as [r8 [HN8 H8]].
  destruct (CutNum_digit_tail true false _ (189+v*372) _ (56+v*108) _ HN8
    ltac:(lia) ltac:(lia)) as [r9 [HN9 E8]].
  destruct (Num_two_markers (9+v*18) 0 (7+v*12) 1 false _ _ _ HN9) as [r10 [HN10 H10]].
  destruct (CutNum_C_short (9+v*18) (7+v*12) _ _ 0 _ HN10 ltac:(lia)) as [r11 [HN11 H11]].
  assert (HN12:CutNum false (271+v*516) (6+v*6) (X^^(13+v*18) *> r11)).
  { apply CutNum_prepend;applys_eq HN11;flia. }
  destruct (CutNum_digit_tail false true _ (135+v*258) _ (130+v*252) _ HN12
    ltac:(lia) ltac:(lia)) as [r12 [HN13 E11]].
  destruct (Num_normal_odd (128+v*252) _ _ _ HN13) as [r13 [HN14 H12]].
  destruct (CutNum_digit_tail true false _ (260+v*507) 0 (263+v*507) _ HN14
    ltac:(lia) ltac:(lia)) as [r14 [HN15 E13]].
  destruct (Num_markers (87+v*169) 0 2 _ _ _ HN15) as [s [HS H14]].
  exists s;split;[applys_eq HS;flia|].
  eapply progress_trans;[applys_eq H1;flia|].
  eapply evstep_progress_trans;[applys_eq H2;flia|].
  eapply progress_trans;[applys_eq H3;flia|].
  rewrite E3;eapply evstep_progress_trans;[applys_eq H5;flia|].
  eapply progress_trans;[applys_eq H6;flia|].
  eapply progress_trans;[applys_eq H7;flia|].
  eapply progress_trans;[applys_eq H8;flia|].
  rewrite E8;eapply evstep_progress_trans;[applys_eq H10;flia|].
  eapply progress_trans;[applys_eq H11;flia|].
  replace (4+(9+v*18)) with (13+v*18) by lia;rewrite E11.
  eapply progress_evstep_trans;[applys_eq H12;flia|].
  rewrite E13.
  change (root (X^^1 *> [0] *> X^^1 *> X^^(263+v*507) *> [0;0] *> r14) -->*
    root (X^^(88+v*169) *> [0] *> X^^3 *> [0;0] *> s)).
  rewrite root_X_add;applys_eq H14;flia.
Qed.

Lemma Num_C2_to_Q d r:
  Num true ((437+98*1000)+(5+(4+d*24)*50)*(928+116*1000)) r ->
  exists s, Num false (521+(4038+(4352+d*(375+25*1000))*(775+5*1000))*1014) s /\
    root (X^^((407+16*1000)+(5+(4+d*24)*50)*(488+19*1000)) *> [0] *> X^^3 *> [0;0] *> r) -->+
    root (X^^(88+(4038+(4352+d*(375+25*1000))*(775+5*1000))*169) *> [0] *> X^^3 *> [0;0] *> s).
Proof.
  intro HN;destruct (Num_C2_to_scalar_C (4+d*24) _ HN) as [r1 [HN1 H1]].
  destruct (Num_scalar_to_terminal (4352+d*(375+25*1000)) _ ltac:(
    replace ((511+26*1000)+(2+(4352+d*(375+25*1000))*4)*(264+33*1000)) with
      (177+((577+35*1000)+(4+d*24)*(500+304*1000))*462) by lia;exact HN1))
    as [r2 [HN2 H2]].
  destruct (Num_terminal_Q (4038+(4352+d*(375+25*1000))*(775+5*1000)) _ HN2)
    as [s [HS H3]].
  exists s;split;[exact HS|].
  replace (4420+(2+(4352+d*(375+25*1000))*4)*(544+5*1000)) with
    (31+((577+35*1000)+(4+d*24)*(500+304*1000))*77) in H2 by lia.
  eapply progress_trans;[exact H1|].
  eapply progress_trans;[exact H2|exact H3].
Qed.

Lemma Num_C2_to_loop d r:
  Num true ((437+98*1000)+(5+(4+d*24)*50)*(928+116*1000)) r ->
  exists c, root (X^^((407+16*1000)+(5+(4+d*24)*50)*(488+19*1000)) *>
    [0] *> X^^3 *> [0;0] *> r) -->+ c /\ InLoop c.
Proof.
  intro HN;destruct (Num_C2_to_Q d _ HN) as [s [HS HC]].
  eexists;split;[exact HC|].
  replace (88+(4038+(4352+d*(375+25*1000))*(775+5*1000))*169) with
    (2+(86+(4038+(4352+d*(375+25*1000))*(775+5*1000))*169)) by lia.
  apply (in_loop (86+(4038+(4352+d*(375+25*1000))*(775+5*1000))*169)).
  replace (5+(86+(4038+(4352+d*(375+25*1000))*(775+5*1000))*169)*6) with
    (521+(4038+(4352+d*(375+25*1000))*(775+5*1000))*1014) by lia.
  exact HS.
Qed.

Lemma init_loop:
  exists c, c0 -->* c /\ InLoop c.
Proof.
  destruct init_C2_collapse as [r [HN HR]].
  replace 796 with (4+33*24) in HN,HR by lia.
  destruct (Num_C2_to_loop 33 _ HN) as [c [HC HL]].
  exists c;split;[follow HR;apply progress_evstep,HC|exact HL].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  destruct init_loop as [c [HR HL]].
  eapply multistep_nonhalt;[exact HR|apply loop_nonhalt,HL].
Qed.

End TM23.
