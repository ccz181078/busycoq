(* Consolidated from busycoq PR #18, commit 08db4597982005cc1fe3b2838201b97cf2d0fe18.
   Original proof by Dennis Koshta (AI-assisted with Claude Code).
   TM12 follows Sk1_Class2.txt numbering; the mirrored machine is defined directly.
   One boolean computation replaces the 22 separately materialized checkpoints. *)

From BusyCoq Require Import Individual62 LongitudinalHalt Eqb.
Require Import ZifyNat Lia NArith PeanoNat String List.
Open Scope sym_scope.
Open Scope list.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LA_---1LD_1LA1RE_1LC0RF_1RE0RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** * Generic composition of one-call segments *)
Lemma segRR_app {t h1 h2 h3 w1 w2 m1 m2}:
  segRR t h1 h2 w1 m1 -> segRR t h2 h3 w2 m2 -> segRR t h1 h3 (w1 ++ w2) (m2 ++ m1).
Proof.
  unfold segRR. intros H1 H2 l r. destruct h1 as [q1 v1], h2 as [q2 v2], h3 as [q3 v3].
  rewrite Str_app_assoc. eapply evstep_trans. 1: apply H1.
  cbn in *. rewrite Str_app_assoc. apply (H2 (Str_app m1 l) r).
Qed.
Lemma segLL_app {t h1 h2 h3 w1 w2 o1 o2}:
  segLL t h1 h2 w1 o1 -> segLL t h2 h3 w2 o2 -> segLL t h1 h3 (w1 ++ w2) (o2 ++ o1).
Proof.
  unfold segLL. intros H1 H2 l r. destruct h1 as [q1 v1], h2 as [q2 v2], h3 as [q3 v3].
  cbn in *. rewrite Str_app_assoc. eapply evstep_trans. 1: apply (H1 (Str_app w2 l) r).
  rewrite Str_app_assoc. apply H2.
Qed.
Lemma segRR_RL_LL {t h1 h2 h3 h4 w1 w2 m w1' w2'}:
  segRR t h1 h2 w1 m -> segRL t h2 h3 w2 w2' -> segLL t h3 h4 m w1' ->
  segRL t h1 h4 (w1 ++ w2) (w1' ++ w2').
Proof.
  unfold segRR,segRL,segLL. intros H1 H2 H3 l r.
  destruct h1 as [q1 v1], h2 as [q2 v2], h3 as [q3 v3], h4 as [q4 v4]. cbn in *.
  rewrite Str_app_assoc. eapply evstep_progress_trans. 1: apply H1.
  eapply progress_evstep_trans. 1: apply H2.
  rewrite Str_app_assoc. apply H3.
Qed.

(** * Words (all near-first; a unit word is root-first) *)
Definition stack j : list Sym := [1] ++ [1;1;1]^^j.
Definition blk m j : list Sym := [0] ++ [1;0]^^m ++ stack j.
Definition bmid m j : list Sym := [0;1] ++ [0;1;1]^^j ++ [0;1]^^m.
Definition lbw m j : list Sym := [0;1;1]^^j ++ [0;1]^^(S m).
Definition xbmid x : list Sym := [0;0;1] ++ [0;1]^^x.

(** * Block lemmas (found with solve_seg) *)
Lemma blkRR_F m j: segRR tm (F,[]) (F,[]) (blk m j) (bmid m j).
Proof. unfold blk,bmid,stack. solve_seg. Qed.
Lemma blkRR_B m j: segRR tm (B,[]) (F,[]) (blk m j) (bmid m j).
Proof. unfold blk,bmid,stack. solve_seg. Qed.
Lemma blkLL m j: segLL tm (D,[]) (D,[]) (lbw m j) (blk m j).
Proof. unfold blk,lbw,stack. solve_seg. Qed.
Lemma sweepLL: segLL tm (D,[]) (D,[]) [0;1] [0;1].
Proof. solve_seg. Qed.
Lemma leadLL a: segLL tm (A,[]) (D,[]) (bmid a 1) ([0;1]^^a ++ [0;0] ++ [1;0;1]).
Proof. unfold bmid. solve_seg. Qed.
Lemma xbRR x: segRR tm (F,[]) (B,[]) ([0] ++ [1;0]^^x ++ [1;1]) (xbmid x).
Proof. unfold xbmid. solve_seg. Qed.
Lemma xbLL x: segLL tm (D,[]) (A,[]) (xbmid x) ([0] ++ [1;0]^^x ++ [1;1]).
Proof. unfold xbmid. solve_seg. Qed.
Lemma leadstopS a x: segRL tm (F,[]) (D,[]) ([0;1]^^(S a) ++ [0;0] ++ [1;0]^^(S x))
  ([0] ++ [1;0]^^a ++ [1;1;1;1] ++ [0] ++ [1;0]^^x).
Proof. solve_seg. Qed.
Lemma leadstop0 x: segRL tm (F,[]) (D,[]) ([0;0] ++ [1;0]^^(S x)) ([1;1;1] ++ [0] ++ [1;0]^^x).
Proof. solve_seg. Qed.
Lemma stop1 c a: segRL tm (B,[]) (D,[]) ([0;1]^^(S c) ++ [0;0] ++ [1;0]^^(S a))
  ([0] ++ [1;0]^^c ++ [1;1;1;1] ++ [0] ++ [1;0]^^a).
Proof. solve_seg. Qed.
Lemma edge0L x f: sideRL tm (F,[]) (D,[]) (([0] ++ [1;0]^^(S x) ++ [1;1;1]^^f) *> const 0)
  (([0] ++ [1;0]^^x ++ [1;1;1]^^(S f)) *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config. es. Qed.
Lemma edge0E y f: sideRL tm (B,[]) (D,[]) (([0] ++ [1;0]^^(S y) ++ [1;1;1]^^f) *> const 0)
  (([0] ++ [1;0]^^y ++ [1;1;1]^^(S f)) *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config. es. Qed.

(** * Chains of passive blocks *)
Definition blkp (p:nat*nat) := blk (fst p) (snd p).
Definition bmidp (p:nat*nat) := bmid (fst p) (snd p).
Definition lbwp (p:nat*nat) := lbw (fst p) (snd p).
Fixpoint cw (ch:list (nat*nat)) : list Sym := match ch with [] => [] | p::ch => blkp p ++ cw ch end.
Fixpoint cmid (ch:list (nat*nat)) : list Sym := match ch with [] => [] | p::ch => cmid ch ++ bmidp p end.
Fixpoint clbw (ch:list (nat*nat)) : list Sym := match ch with [] => [] | p::ch => clbw ch ++ lbwp p end.

Lemma chainRR ch: segRR tm (F,[]) (F,[]) (cw ch) (cmid ch).
Proof.
  induction ch as [|p ch IH]; cbn [cw cmid].
  - unfold segRR. intros. cbn. finish.
  - exact (segRR_app (blkRR_F (fst p) (snd p)) IH).
Qed.
Lemma chainLL ch: segLL tm (D,[]) (D,[]) (clbw ch) (cw ch).
Proof.
  induction ch as [|p ch IH]; cbn [cw clbw].
  - unfold segLL. intros. cbn. finish.
  - exact (segLL_app IH (blkLL (fst p) (snd p))).
Qed.
Lemma bmid_shift m j: bmid m j ++ [0;1] = [0;1] ++ lbw m j.
Proof. unfold bmid,lbw. rewrite <-!app_assoc. f_equal. f_equal. rewrite lpow_shift. reflexivity. Qed.
Lemma cmid_shift ch: cmid ch ++ [0;1] = [0;1] ++ clbw ch.
Proof.
  induction ch as [|p ch IH]; cbn [cmid clbw]; [reflexivity|].
  unfold bmidp,lbwp. rewrite <-app_assoc, bmid_shift.
  rewrite (app_assoc (cmid ch) [0;1]), IH. rewrite <-app_assoc. reflexivity.
Qed.
Lemma bmid_S m j: bmid (S m) j = [0;1] ++ lbw m j.
Proof. rewrite <-bmid_shift. unfold bmid. cbn [lpow]. rewrite <-!app_assoc. f_equal. f_equal.
  rewrite lpow_shift. reflexivity. Qed.

(** prefix = Y block (entered in B) followed by a chain *)
Definition pw c j ch := blk c j ++ cw ch.
Lemma prefRR c j ch: segRR tm (B,[]) (F,[]) (pw c j ch) (cmid ch ++ bmid c j).
Proof. exact (segRR_app (blkRR_B c j) (chainRR ch)). Qed.
Lemma prefLL c j ch: segLL tm (D,[]) (D,[]) (cmid ch ++ bmid (S c) j) (pw c j ch ++ [0;1]).
Proof.
  rewrite bmid_S, (app_assoc (cmid ch) [0;1]), cmid_shift, <-app_assoc.
  unfold pw.
  refine (segLL_app sweepLL _).
  exact (segLL_app (chainLL ch) (blkLL c j)).
Qed.

(** * Frames *)
Lemma segRL_frame {t h1 h2 w w'} u: segRL t h1 h2 w w' -> segRL t h1 h2 (w ++ u) (w' ++ u).
Proof. unfold segRL. intros H l r. rewrite !Str_app_assoc. apply H. Qed.

(** * Digits.  lead1 a x: m1 = 2a+1 cells, lead 1111, x = 2x+1 cells;
    lead0 a x: m1 = 2a cells, lead 00, x = 2x cells.  For k=1 the "m1" gap is the fuel y. *)
Definition lead1 a x : list Sym := blk a 1 ++ [0] ++ [1;0]^^x.
Definition lead0 a x : list Sym := [0;1]^^a ++ [0;0] ++ [1;0]^^x.
Definition tailw g : list Sym := [1;1] ++ [1;1;1]^^g.

Definition hB : DH0 := (B,[]).
Definition hD : DH0 := (D,[]).
Definition h : list (DH0*DH0) := [(hB,hD)].

Lemma stopK c j ch a x: segRL tm hB hD (pw (S c) j ch ++ lead0 a (S x)) (pw c j ch ++ lead1 a x).
Proof.
  destruct a as [|a].
  - pose proof (segRR_RL_LL (prefRR (S c) j ch) (leadstop0 x) (prefLL c j ch)) as H.
    unfold lead0,lead1. applys_eq H. cbn. rewrite <-!app_assoc. reflexivity.
  - pose proof (segRR_RL_LL (prefRR (S c) j ch) (leadstopS a x) (prefLL c j ch)) as H.
    unfold lead0,lead1. applys_eq H. unfold blk,stack. cbn. rewrite <-!app_assoc. reflexivity.
Qed.

Lemma stopK1 c a: segRL tm hB hD (lead0 (S c) (S a)) (lead1 c a).
Proof. unfold lead0,lead1,blk,stack. solve_seg. Qed.

Definition passK_mid c j ch a x := (xbmid x ++ bmid a 1) ++ (cmid ch ++ bmid (S c) j).
Lemma passK_RR c j ch a x: segRR tm hB hB (pw (S c) j ch ++ lead1 a x ++ [1;1]) (passK_mid c j ch a x).
Proof.
  unfold lead1, passK_mid. rewrite <-!app_assoc.
  pose proof (segRR_app (prefRR (S c) j ch) (segRR_app (blkRR_F a 1) (xbRR x))) as H.
  rewrite <-!app_assoc in H. exact H.
Qed.
Lemma passK_LL c j ch a x: segLL tm hD hD (passK_mid c j ch a x) (pw c j ch ++ lead0 (S a) (S (S x)) ++ [1;1]).
Proof.
  unfold passK_mid.
  pose proof (segLL_app (segLL_app (xbLL x) (leadLL a)) (prefLL c j ch)) as H.
  applys_eq H. unfold lead0. cbn [lpow]. rewrite <-!app_assoc. cbn. reflexivity.
Qed.
Lemma passK c j ch a x: segRLs tm h h (pw (S c) j ch ++ lead1 a x ++ [1;1]) (pw c j ch ++ lead0 (S a) (S (S x)) ++ [1;1]).
Proof.
  unfold h. applys_eq (segRLs_lrcons tm [] [] [] _ _ _ _ _ hB hD hB hD
    (passK_RR c j ch a x) (passK_LL c j ch a x) (segLRs_O _ _) (segRLs_O _ _)).
Qed.

Definition passK1_mid c x := xbmid x ++ bmid c 1.
Lemma passK1_RR c x: segRR tm hB hB (lead1 c x ++ [1;1]) (passK1_mid c x).
Proof. unfold lead1,passK1_mid. rewrite <-!app_assoc. exact (segRR_app (blkRR_B c 1) (xbRR x)). Qed.
Lemma passK1_LL c x: segLL tm hD hD (passK1_mid c x) (lead0 c (S (S x)) ++ [1;1]).
Proof.
  unfold passK1_mid. pose proof (segLL_app (xbLL x) (leadLL c)) as H.
  applys_eq H. unfold lead0. cbn [lpow]. rewrite <-!app_assoc. cbn. reflexivity.
Qed.
Lemma passK1 c x: segRLs tm h h (lead1 c x ++ [1;1]) (lead0 c (S (S x)) ++ [1;1]).
Proof.
  unfold h. applys_eq (segRLs_lrcons tm [] [] [] _ _ _ _ _ hB hD hB hD
    (passK1_RR c x) (passK1_LL c x) (segLRs_O _ _) (segRLs_O _ _)).
Qed.

(** halting call: a k=1 digit with lead 00 and no fuel *)
Lemma halt0 x l r: halts tm (l {{B}}> lead0 0 x *> r).
Proof. unfold lead0. cbn. solve_halt. Qed.

(** * U0 (the unit next to the edge) and the edge 1^(3f) *)
Lemma edge0L0 f: sideRL tm (F,[]) (D,[]) (([0] ++ [1;1;1]^^f) *> const 0)
  (([1;1] ++ [1;1;1]^^f) *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config. es. Qed.
Lemma segRR_sideRL_LL {t h1 h2 h3 h4 w m w' r r'}:
  segRR t h1 h2 w m -> sideRL t h2 h3 r r' -> segLL t h3 h4 m w' ->
  sideRL t h1 h4 (w *> r) (w' *> r').
Proof.
  unfold segRR,sideRL,segLL. intros H1 H2 H3 l.
  destruct h1 as [q1 v1], h2 as [q2 v2], h3 as [q3 v3], h4 as [q4 v4]. cbn in *.
  eapply evstep_progress_trans. 1: apply H1.
  eapply progress_evstep_trans. 1: apply H2.
  apply H3.
Qed.
Definition edgew x f : list Sym := [0] ++ [1;0]^^x ++ [1;1;1]^^f.
(** leadless U0: prefix, then the gap x (2x+1 cells), then the edge *)
Lemma u0L c j ch x f: sideRL tm hB hD ((pw (S c) j ch ++ edgew x f) *> const 0)
  ((pw c j ch ++ edgew x (S f)) *> const 0).
Proof.
  rewrite !Str_app_assoc. destruct x as [|x].
  - pose proof (segRR_sideRL_LL (prefRR (S c) j ch) (edge0L0 f) (prefLL c j ch)) as H.
    applys_eq H. unfold edgew. rewrite <-!Str_app_assoc. f_equal. rewrite <-!app_assoc. reflexivity.
  - pose proof (segRR_sideRL_LL (prefRR (S c) j ch) (edge0L x f) (prefLL c j ch)) as H.
    applys_eq H. unfold edgew. rewrite <-!Str_app_assoc. f_equal. rewrite <-!app_assoc. reflexivity.
Qed.
(** empty U0 *)
Lemma u0E y f: sideRL tm hB hD (edgew (S y) f *> const 0) (edgew y (S f) *> const 0).
Proof. unfold edgew. exact (edge0E y f). Qed.

(** * The root: tail gap 2t+1 and the tail boundary 11 *)
Definition root t (X:side) : Q * tape := const 0 <{{A}} ([0;1]^^t ++ [0;1;1]) *> X.
Definition wmid t : list Sym := [0] ++ [0;1]^^t ++ [0;1;0;1].
Lemma root_in t X: root t X -->* wmid t *> const 0 {{B}}> X.
Proof. unfold root,wmid. es. Qed.
Lemma sweepA: forall l r n, l <* [0;1]^^n <{{A}} r -->* l <{{A}} [0;1]^^n *> r.
Proof. apply (shift_rule_L [] tm [0;1] [0;1] A). intros. es. Qed.
Lemma root_out t X: wmid t *> const 0 <{{D}} X -->* root (S t) X.
Proof.
  unfold root,wmid. simpl_tape. step. follow sweepA. do 4 step.
  apply evstep_refl'. cbn [lpow app Str_app].
  change (0 >> 1 >> 1 >> X) with ([0;1] *> 1 >> X). rewrite lpow_shift'. reflexivity.
Qed.
Lemma root_step t X X': sideRL tm hB hD X X' -> root t X -->+ root (S t) X'.
Proof.
  intros H.
  eapply evstep_progress_trans. 1: apply root_in.
  eapply progress_evstep_trans. 1: apply (H (wmid t *> const 0)).
  apply root_out.
Qed.
Lemma root_steps n: forall t X X', sideRLs tm (h^^n) X X' -> root t X -->* root (n+t) X'.
Proof.
  induction n; intros t X X' H.
  - inverts H. finish.
  - cbn [lpow h app] in H. inverts H.
    eapply evstep_trans. 1: apply progress_evstep, root_step; eassumption.
    replace (S n + t) with (n + S t) by lia. apply IHn. assumption.
Qed.
Lemma root_halt t X: sideRLs_halt tm h X -> halts tm (root t X).
Proof. intros H. eapply halts_evstep. 2: apply root_in. apply (sideRLs_halt_single _ _ _ _ H). Qed.


(** * Uniform touch lemmas.  A unit is [cw bs ++ leadw b a x ++ far]; every touch moves all
    passive walls two cells toward the root, i.e. consumes the two root-most cells [0;1]. *)
Definition hF : DH0 := (F,[]).
Definition leadw (b:bool) a x := if b then lead1 a x else lead0 a x.
Definition uw bs b a x (far:list Sym) := cw bs ++ leadw b a x ++ far.
Definition consume (bs: list (nat*nat)) (a:nat) : option (nat * list (nat*nat) * nat) :=
  match bs with
  | (S c, j) :: r => Some (O, (c,j)::r, a)
  | (O, j) :: r => Some (j, r, a)
  | [] => match a with S a' => Some (O, [], a') | O => None end
  end.
Lemma cw_app l1 l2: cw (l1 ++ l2) = cw l1 ++ cw l2.
Proof. induction l1 as [|p l1 IH]; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma yLL_glue j: segLL tm (D,[]) (D,[]) ([0;1;1]^^j) ([1;1;1]^^j).
Proof. solve_seg. Qed.
Lemma prefLL_glue j ch: segLL tm (D,[]) (D,[]) (cmid ch ++ bmid 0 j) ([1;1;1]^^j ++ cw ch ++ [0;1]).
Proof.
  unfold bmid. cbn [lpow]. rewrite app_nil_r.
  rewrite (app_assoc (cmid ch) [0;1]), cmid_shift, <-app_assoc.
  pose proof (segLL_app sweepLL (segLL_app (chainLL ch) (yLL_glue j))) as H.
  applys_eq H. rewrite <-!app_assoc. reflexivity.
Qed.

(** generic compositions: prefix out (B->F), a core entered in F, prefix back (D->D) *)
Lemma gen_RL {ci co} (HF: segRL tm hF hD ci co) c j ch:
  segRL tm hB hD (pw (S c) j ch ++ ci) (pw c j ch ++ [0;1] ++ co).
Proof.
  pose proof (segRR_RL_LL (prefRR (S c) j ch) HF (prefLL c j ch)) as H.
  applys_eq H. rewrite <-!app_assoc. reflexivity.
Qed.
Lemma gen_RLg {ci co} (HF: segRL tm hF hD ci co) j ch:
  segRL tm hB hD (pw 0 j ch ++ ci) ([1;1;1]^^j ++ cw ch ++ [0;1] ++ co).
Proof.
  pose proof (segRR_RL_LL (prefRR 0 j ch) HF (prefLL_glue j ch)) as H.
  applys_eq H. rewrite <-!app_assoc. reflexivity.
Qed.
Lemma lrcons1 {w1 w2 m}: segRR tm hB hB w1 m -> segLL tm hD hD m w2 -> segRLs tm h h w1 w2.
Proof.
  intros H1 H2. unfold h.
  applys_eq (segRLs_lrcons tm [] [] [] _ _ _ _ _ hB hD hB hD H1 H2 (segLRs_O _ _) (segRLs_O _ _)).
Qed.
Lemma gen_fwd {ci m co} (HR: segRR tm hF hB ci m) (HL: segLL tm hD hD m co) c j ch:
  segRLs tm h h (pw (S c) j ch ++ ci) (pw c j ch ++ [0;1] ++ co).
Proof.
  pose proof (lrcons1 (segRR_app (prefRR (S c) j ch) HR) (segLL_app HL (prefLL c j ch))) as H.
  applys_eq H. rewrite <-!app_assoc. reflexivity.
Qed.
Lemma gen_fwdg {ci m co} (HR: segRR tm hF hB ci m) (HL: segLL tm hD hD m co) j ch:
  segRLs tm h h (pw 0 j ch ++ ci) ([1;1;1]^^j ++ cw ch ++ [0;1] ++ co).
Proof.
  pose proof (lrcons1 (segRR_app (prefRR 0 j ch) HR) (segLL_app HL (prefLL_glue j ch))) as H.
  applys_eq H. rewrite <-!app_assoc. reflexivity.
Qed.
Lemma gen_side {ci co R R'} (HF: sideRL tm hF hD (ci *> R) (co *> R')) c j ch:
  sideRL tm hB hD ((pw (S c) j ch ++ ci) *> R) ((pw c j ch ++ [0;1] ++ co) *> R').
Proof.
  pose proof (segRR_sideRL_LL (prefRR (S c) j ch) HF (prefLL c j ch)) as H.
  applys_eq H; rewrite <-!Str_app_assoc; f_equal; rewrite <-!app_assoc; reflexivity.
Qed.
Lemma gen_sideg {ci co R R'} (HF: sideRL tm hF hD (ci *> R) (co *> R')) j ch:
  sideRL tm hB hD ((pw 0 j ch ++ ci) *> R) (([1;1;1]^^j ++ cw ch ++ [0;1] ++ co) *> R').
Proof.
  pose proof (segRR_sideRL_LL (prefRR 0 j ch) HF (prefLL_glue j ch)) as H.
  applys_eq H; rewrite <-!Str_app_assoc; f_equal; rewrite <-!app_assoc; reflexivity.
Qed.
Lemma segRL_side {t h1 h2 w w'} R: segRL t h1 h2 w w' -> sideRL t h1 h2 (w *> R) (w' *> R).
Proof. unfold segRL,sideRL. intros H l. destruct h1 as [q1 v1], h2 as [q2 v2]. cbn. apply H. Qed.

Ltac injE E := injection E; intros; subst; clear E.
Ltac lnorm2 := unfold uw,leadw,pw; do 3 (rewrite ?cw_app; cbn [cw]); unfold blkp,lead0,lead1,blk,stack,tailw,edgew; cbn [fst snd lpow];
  rewrite ?app_nil_r, ?app_nil_l; repeat rewrite <-app_assoc; cbn [app];
  repeat (rewrite lpow_rotate_list; cbn [app]); try reflexivity.

(** ** cores *)
Lemma cstopF a x far: exists co, segRL tm hF hD (lead0 a (S x) ++ far) co /\ [0;1] ++ co = lead1 a x ++ far.
Proof.
  destruct a as [|a].
  - eexists. split. 1: exact (segRL_frame far (leadstop0 x)). lnorm2.
  - eexists. split. 1: exact (segRL_frame far (leadstopS a x)). lnorm2.
Qed.
Lemma t_stop bs a x far ov bs' a': consume bs a = Some (ov, bs', a') ->
  segRL tm hB hD (uw bs false a (S x) far) ([1;1;1]^^ov ++ uw bs' true a' x far).
Proof.
  destruct (cstopF a x far) as [co [HF HE]].
  destruct bs as [|[[|c] j] r]; cbn [consume]; intros E.
  - destruct a as [|a]; [discriminate|]. injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (segRL_frame far (stopK1 a x)) as H. applys_eq H; lnorm2.
  - injection E as E1 E2 E3; subst ov bs' a'. pose proof (gen_RLg HF j r) as H. rewrite HE in H. applys_eq H; lnorm2.
  - injection E as E1 E2 E3; subst ov bs' a'. pose proof (gen_RL HF c j r) as H. rewrite HE in H. applys_eq H; lnorm2.
Qed.

Definition cpass_mid a x := xbmid x ++ bmid a 1.
Lemma cpassRR a x: segRR tm hF hB (lead1 a x ++ [1;1]) (cpass_mid a x).
Proof. unfold lead1,cpass_mid. rewrite <-!app_assoc. exact (segRR_app (blkRR_F a 1) (xbRR x)). Qed.
Definition cpass_co a x := ([0;1]^^a ++ [0;0] ++ [1;0;1]) ++ ([0] ++ [1;0]^^x ++ [1;1]).
Lemma cpassLL a x: segLL tm hD hD (cpass_mid a x) (cpass_co a x).
Proof. unfold cpass_mid,cpass_co. exact (segLL_app (xbLL x) (leadLL a)). Qed.
Lemma t_pass bs a x ov bs' a': consume bs (S a) = Some (ov, bs', a') ->
  segRLs tm h h (uw bs true a x (tailw 0)) ([1;1;1]^^ov ++ uw bs' false a' (S (S x)) (tailw 0)).
Proof.
  destruct bs as [|[[|c] j] r]; cbn [consume]; intros E; injection E as E1 E2 E3; subst ov bs' a'.
  - pose proof (passK1 a x) as H. applys_eq H; lnorm2.
  - pose proof (gen_fwdg (cpassRR a x) (cpassLL a x) j r) as H. applys_eq H; unfold cpass_co; lnorm2.
  - pose proof (gen_fwd (cpassRR a x) (cpassLL a x) c j r) as H. applys_eq H; unfold cpass_co; lnorm2.
Qed.

(** ** unglue: the glued walls of the far neighbour come in; the first becomes a 00 lead *)
Definition um1 a x : list Sym := [0;0;1;0;1;1;0;1;0;1] ++ [0;1]^^x ++ [1] ++ [0;1]^^a.
Definition um2 a x g : list Sym := [0;0;1;0;1;1;0;1;1;0;1] ++ [1;0;1]^^g ++ [0;1] ++ [0;1]^^x ++ [1] ++ [0;1]^^a.
Definition uco1 a x : list Sym := [0;1]^^a ++ [1;1;1;0;1;0] ++ [1;0]^^x ++ [0;1;0;1;1].
Definition uco2 a x g : list Sym := [0;1]^^a ++ [1;1;1;0;1] ++ [0;1]^^x ++ [1;1;1] ++ [1;1;1]^^g ++ [0;0;1;0;1;1].
Lemma u1RF a x: segRR tm hF hB (lead1 a x ++ tailw 1) (um1 a x).
Proof. unfold lead1,blk,stack,tailw,um1,hF,hB. solve_seg. Qed.
Lemma u1RB a x: segRR tm hB hB (lead1 a x ++ tailw 1) (um1 a x).
Proof. unfold lead1,blk,stack,tailw,um1,hB. solve_seg. Qed.
Lemma u1L a x: segLL tm hD hD (um1 a x) (uco1 a x).
Proof. unfold um1,uco1,hD. solve_seg. Qed.
Lemma u2RF a x g: segRR tm hF hB (lead1 a x ++ tailw (S (S g))) (um2 a x g).
Proof. unfold lead1,blk,stack,tailw,um2,hF,hB. solve_seg. Qed.
Lemma u2RB a x g: segRR tm hB hB (lead1 a x ++ tailw (S (S g))) (um2 a x g).
Proof. unfold lead1,blk,stack,tailw,um2,hB. solve_seg. Qed.
Lemma u2L a x g: segLL tm hD hD (um2 a x g) (uco2 a x g).
Proof. unfold um2,uco2,hD. solve_seg. Qed.

Lemma t_ungl1 bs a x ov bs' a': consume (bs ++ [(a,1%nat)]) (S x) = Some (ov, bs', a') ->
  segRLs tm h h (uw bs true a x (tailw 1)) ([1;1;1]^^ov ++ uw bs' false a' 1 (tailw 0)).
Proof.
  destruct bs as [|[[|c] j] r]; cbn [app consume].
  - destruct a as [|a]; intros E; injection E as E1 E2 E3; subst ov bs' a'.
    + pose proof (lrcons1 (u1RB 0 x) (u1L 0 x)) as H. applys_eq H; unfold uco1; lnorm2.
    + pose proof (lrcons1 (u1RB (S a) x) (u1L (S a) x)) as H. applys_eq H; unfold uco1; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_fwdg (u1RF a x) (u1L a x) j r) as H. applys_eq H; unfold uco1; rewrite ?cw_app; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_fwd (u1RF a x) (u1L a x) c j r) as H. applys_eq H; unfold uco1; rewrite ?cw_app; lnorm2.
Qed.
Lemma t_ungl2 bs a x g ov bs' a': consume (bs ++ [(a,1%nat);(x,S g)]) 0%nat = Some (ov, bs', a') ->
  segRLs tm h h (uw bs true a x (tailw (S (S g)))) ([1;1;1]^^ov ++ uw bs' false a' 1 (tailw 0)).
Proof.
  destruct bs as [|[[|c] j] r]; cbn [app consume].
  - destruct a as [|a]; intros E; injection E as E1 E2 E3; subst ov bs' a'.
    + pose proof (lrcons1 (u2RB 0 x g) (u2L 0 x g)) as H. applys_eq H; unfold uco2; lnorm2.
    + pose proof (lrcons1 (u2RB (S a) x g) (u2L (S a) x g)) as H. applys_eq H; unfold uco2; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_fwdg (u2RF a x g) (u2L a x g) j r) as H. applys_eq H; unfold uco2; rewrite ?cw_app; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_fwd (u2RF a x g) (u2L a x g) c j r) as H. applys_eq H; unfold uco2; rewrite ?cw_app; lnorm2.
Qed.

(** ** the halting call *)
Lemma t_halt x far l r: halts tm (l {{B}}> uw [] false 0 x far *> r).
Proof. unfold uw, leadw. cbn [cw app]. rewrite Str_app_assoc. apply halt0. Qed.

(** ** U0 next to the edge.  Edge class 0: [1;1;1]^^f; class 1: [1] ++ [1;1;1]^^f *)
Definition edge1w f : list Sym := [1] ++ [1;1;1]^^f.
Lemma z_lead bs x f ov bs' a': bs <> [] -> consume bs 0%nat = Some (ov, bs', a') ->
  sideRL tm hB hD ((cw bs ++ edgew x f) *> const 0) (([1;1;1]^^ov ++ cw bs' ++ edgew x (S f)) *> const 0).
Proof.
  intros NE. destruct bs as [|[[|c] j] r]; [congruence| |]; cbn [consume]; intros E; injection E as E1 E2 E3; subst ov bs' a'.
  - destruct x as [|x].
    + pose proof (gen_sideg (edge0L0 f) j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; lnorm2.
    + pose proof (gen_sideg (edge0L x f) j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; lnorm2.
  - destruct x as [|x].
    + pose proof (gen_side (edge0L0 f) c j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; lnorm2.
    + pose proof (gen_side (edge0L x f) c j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; lnorm2.
Qed.
Lemma z_empty y f: sideRL tm hB hD (edgew (S y) f *> const 0) (edgew y (S f) *> const 0).
Proof. apply u0E. Qed.
Lemma z_absorb f: sideRL tm hB hD (edgew 0 (S f) *> const 0) (([1;1] ++ [1;1;1]^^(S f)) *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config, edgew, hB, hD. es. Qed.
Lemma z_stop bs a x f ov bs' a': consume bs a = Some (ov, bs', a') ->
  sideRL tm hB hD (uw bs false a (S x) (edge1w f) *> const 0) (([1;1;1]^^ov ++ uw bs' true a' x (edge1w f)) *> const 0).
Proof. intros E. apply segRL_side, t_stop, E. Qed.
Definition zco a x f : list Sym := [0;1]^^a ++ [1;1;1;0;1] ++ [0;1]^^x ++ [1;1;1]^^f ++ [0;1;1;1].
Lemma z1F a x f: sideRL tm hF hD ((lead1 a x ++ edge1w f) *> const 0) (zco a x f *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config, lead1, blk, stack, edge1w, zco, hF, hD. es. Qed.
Lemma z1B a x f: sideRL tm hB hD ((lead1 a x ++ edge1w f) *> const 0) (zco a x f *> const 0).
Proof. unfold sideRL. intros l. unfold to_DH_config, lead1, blk, stack, edge1w, zco, hB, hD. es. Qed.
Lemma z_1111 bs a x f ov bs' a': consume (bs ++ [(a,1%nat);(x,f)]) 0%nat = Some (ov, bs', a') ->
  sideRL tm hB hD (uw bs true a x (edge1w f) *> const 0) (([1;1;1]^^ov ++ cw bs' ++ edgew 0 1) *> const 0).
Proof.
  unfold uw, leadw. destruct bs as [|[[|c] j] r]; cbn [app consume].
  - destruct a as [|a]; intros E; injection E as E1 E2 E3; subst ov bs' a'.
    + pose proof (z1B 0 x f) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; unfold zco; lnorm2.
    + pose proof (z1B (S a) x f) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; unfold zco; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_sideg (z1F a x f) j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; unfold zco; rewrite ?cw_app; lnorm2.
  - intros E; injection E as E1 E2 E3; subst ov bs' a'.
    pose proof (gen_side (z1F a x f) c j r) as H. applys_eq H; rewrite <-?Str_app_assoc; f_equal; unfold zco; rewrite ?cw_app; lnorm2.
Qed.

(** ** resets at the root *)
Definition NT s g (X:side) : Q * tape := const 0 <{{A}} ([1;0]^^s ++ [1] ++ [0;0] ++ [1;0] ++ tailw g) *> X.
Definition rmid t : list Sym := [0;0;1;0;1;1;0;1;0] ++ [1;0]^^t.
Lemma reset1_in t X: root t ([1;1;1] *> X) -->* rmid t *> const 0 {{B}}> X.
Proof. unfold root,rmid. es. Qed.
Lemma reset1_out t X: rmid t *> const 0 <{{D}} X -->* NT (S t) 0 X.
Proof. unfold rmid,NT,tailw. es. Qed.
Lemma reset1 t X X': sideRL tm hB hD X X' -> root t ([1;1;1] *> X) -->* NT (S t) 0 X'.
Proof.
  intros H. eapply evstep_trans. 1: apply reset1_in.
  eapply evstep_trans. 2: apply reset1_out.
  apply progress_evstep. apply (H (rmid t *> const 0)).
Qed.
Lemma reset1_halt t X: sideRLs_halt tm h X -> halts tm (root t ([1;1;1] *> X)).
Proof. intros H. eapply halts_evstep. 2: apply reset1_in. apply (sideRLs_halt_single _ _ _ _ H). Qed.
Lemma reset2 s g X: NT (S s) g X -->* root 0 ((lead1 s 0 ++ tailw g) *> X).
Proof. unfold NT,root,lead1,blk,stack,tailw. es. Qed.

(** * Records with N fields (computation) and their words *)
Definition cvp (p:N*N) : nat*nat := (N.to_nat (fst p), N.to_nat (snd p)).
Definition cvl (bs:list (N*N)) := map cvp bs.
Record unitN := UN { ubs : list (N*N); ubit : bool; ua : N; ux : N; ug : N }.
Definition uwN u := uw (cvl (ubs u)) (ubit u) (N.to_nat (ua u)) (N.to_nat (ux u)) (tailw (N.to_nat (ug u))).
Fixpoint dwords (us:list unitN) : list Sym := match us with [] => [] | u::us => uwN u ++ dwords us end.
Inductive zN := Z0 (bs:list (N*N)) (x f:N) | ZD (bs:list (N*N)) (b:bool) (a x f:N).
Definition zside z : side := match z with
  | Z0 bs x f => (cw (cvl bs) ++ edgew (N.to_nat x) (N.to_nat f)) *> const 0
  | ZD bs b a x f => uw (cvl bs) b (N.to_nat a) (N.to_nat x) (edge1w (N.to_nat f)) *> const 0 end.
Inductive tailN := TT (t g:N) | NTl (s g:N).
Record cfg := Cfg { ctl : tailN; cus : list unitN; cz : zN }.
Definition denote c : Q * tape := match ctl c with
  | TT t g => root (N.to_nat t) (([1;1;1]^^(N.to_nat g) ++ dwords (cus c)) *> zside (cz c))
  | NTl s g => NT (N.to_nat s) (N.to_nat g) (dwords (cus c) *> zside (cz c)) end.

Definition consumeN (bs:list (N*N)) (a:N) : option (N * list (N*N) * N) :=
  match bs with
  | (c, j) :: r => if N.eqb c 0 then Some (j, r, a) else Some (0%N, (N.pred c, j)::r, a)
  | [] => if N.eqb a 0 then None else Some (0%N, [], N.pred a)
  end.
Lemma consumeN_spec bs a ov bs' a': consumeN bs a = Some (ov, bs', a') ->
  consume (cvl bs) (N.to_nat a) = Some (N.to_nat ov, cvl bs', N.to_nat a').
Proof.
  destruct bs as [|[c j] r]; cbn.
  - destruct (N.eqb_spec a 0); [discriminate|]. intros E; injection E as E1 E2 E3; subst.
    replace (N.to_nat a) with (S (N.to_nat (N.pred a))) by lia. reflexivity.
  - destruct (N.eqb_spec c 0) as [Hc|Hc]; intros E; injection E as E1 E2 E3; subst.
    + reflexivity.
    + unfold cvp; cbn. replace (N.to_nat c) with (S (N.to_nat (N.pred c))) by lia. reflexivity.
Qed.
Arguments consumeN : simpl never.
Lemma cvl_app l1 l2: cvl (l1 ++ l2) = cvl l1 ++ cvl l2.
Proof. apply map_app. Qed.

(** ** one touch *)
Inductive tres := TStop (ov:N) (u:unitN) | TPass (ov:N) (u:unitN) | THalt | TFail.
Definition touchN u : tres :=
  if ubit u then
    if N.eqb (ug u) 0 then
      match consumeN (ubs u) (N.succ (ua u)) with Some (ov,bs',a') => TPass ov (UN bs' false a' (ux u + 2) 0) | None => TFail end
    else if N.eqb (ug u) 1 then
      match consumeN (ubs u ++ [(ua u, 1%N)]) (N.succ (ux u)) with Some (ov,bs',a') => TPass ov (UN bs' false a' 1 0) | None => TFail end
    else
      match consumeN (ubs u ++ [(ua u, 1%N); (ux u, ug u - 1)%N]) 0%N with Some (ov,bs',a') => TPass ov (UN bs' false a' 1 0) | None => TFail end
  else
    match ubs u, N.eqb (ua u) 0 with
    | [], true => THalt
    | _, _ => if N.eqb (ux u) 0 then TFail else
      match consumeN (ubs u) (ua u) with Some (ov,bs',a') => TStop ov (UN bs' true a' (N.pred (ux u)) (ug u)) | None => TFail end
    end.

Ltac nat_of := cbn [cvp fst snd]; rewrite ?N2Nat.inj_succ, ?N2Nat.inj_add, ?N2Nat.inj_pred.

Lemma touchN_stop u ov u': touchN u = TStop ov u' -> segRL tm hB hD (uwN u) ([1;1;1]^^(N.to_nat ov) ++ uwN u').
Proof.
  destruct u as [bs [] a x g]; unfold touchN; cbn [ubit ubs ua ux ug].
  - destruct (N.eqb g 0); [|destruct (N.eqb g 1)];
    match goal with |- context [consumeN ?b ?c] => destruct (consumeN b c) as [[[? ?] ?]|] end; discriminate.
  - intros E. assert (Hx: N.eqb x 0 = false /\ consumeN bs a = Some (ov, ubs u', ua u') /\ ubit u' = true
      /\ ux u' = N.pred x /\ ug u' = g).
    { destruct bs as [|p bs]; [destruct (N.eqb a 0)|]; cbn in E; try discriminate;
      destruct (N.eqb x 0); cbn in E; try discriminate;
      destruct (consumeN _ a) as [[[o b'] a'']|]; try discriminate; injection E as <- <-; cbn; auto. }
    destruct Hx as (Hx & Hc & Hb & Hux & Hg). apply consumeN_spec in Hc.
    unfold uwN. rewrite Hb, Hux, Hg. cbn [ubs ubit ua ux ug].
    apply N.eqb_neq in Hx. replace (N.to_nat x) with (S (N.to_nat (N.pred x))) by lia.
    apply t_stop. exact Hc.
Qed.
Lemma touchN_pass u ov u': touchN u = TPass ov u' -> segRLs tm h h (uwN u) ([1;1;1]^^(N.to_nat ov) ++ uwN u') /\ ug u' = 0%N.
Proof.
  destruct u as [bs [] a x g]; unfold touchN; cbn [ubit ubs ua ux ug].
  - destruct (N.eqb_spec g 0) as [Hg0|Hg0]; [|destruct (N.eqb_spec g 1) as [Hg1|Hg1]].
    + destruct (consumeN bs (N.succ a)) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
      intros E; injection E as <- <-. split; [|reflexivity].
      apply consumeN_spec in Ec. rewrite N2Nat.inj_succ in Ec. subst g.
      unfold uwN; cbn [ubs ubit ua ux ug].
      replace (N.to_nat (x + 2)) with (S (S (N.to_nat x))) by lia. apply t_pass, Ec.
    + destruct (consumeN (bs ++ [(a, 1%N)]) (N.succ x)) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
      intros E; injection E as <- <-. split; [|reflexivity].
      apply consumeN_spec in Ec. rewrite N2Nat.inj_succ, cvl_app in Ec. subst g.
      cbn [cvl map] in Ec. unfold cvp in Ec; cbn [fst snd] in Ec. change (N.to_nat 1) with 1%nat in Ec.
      unfold uwN; cbn [ubs ubit ua ux ug]. apply t_ungl1, Ec.
    + destruct (consumeN (bs ++ [(a, 1%N); (x, g-1)%N]) 0%N) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
      intros E; injection E as <- <-. split; [|reflexivity].
      apply consumeN_spec in Ec. rewrite cvl_app in Ec. cbn [cvl map] in Ec. unfold cvp in Ec; cbn [fst snd] in Ec.
      change (N.to_nat 1) with 1%nat in Ec. change (N.to_nat 0) with 0%nat in Ec.
      unfold uwN; cbn [ubs ubit ua ux ug].
      replace (N.to_nat g) with (S (S (N.to_nat (g-1) - 1))) by lia.
      replace (N.to_nat (g-1)) with (S (N.to_nat (g-1) - 1)) in Ec by lia.
      apply t_ungl2, Ec.
  - intros E. destruct bs as [|p bs]; [destruct (N.eqb a 0)|]; cbn in E; try discriminate;
      destruct (N.eqb x 0); cbn in E; try discriminate;
      destruct (consumeN _ a) as [[[o b'] a'']|]; discriminate.
Qed.
Lemma touchN_halt u: touchN u = THalt -> forall l r, halts tm (l {{B}}> uwN u *> r).
Proof.
  destruct u as [bs [] a x g]; unfold touchN; cbn [ubit ubs ua ux ug].
  - destruct (N.eqb g 0); [|destruct (N.eqb g 1)];
    match goal with |- context [consumeN ?b ?c] => destruct (consumeN b c) as [[[? ?] ?]|] end; discriminate.
  - destruct bs as [|p bs]; [destruct (N.eqb_spec a 0) as [Ha|Ha]|].
    + intros _ l r. unfold uwN; cbn [ubs ubit ua ux ug cvl map]. subst a. apply t_halt.
    + intros E; cbn in E; destruct (N.eqb x 0); cbn in E; try discriminate;
      destruct (consumeN _ a) as [[[o b'] a'']|]; discriminate.
    + intros E; cbn in E; destruct (N.eqb x 0); cbn in E; try discriminate;
      destruct (consumeN _ a) as [[[o b'] a'']|]; discriminate.
Qed.

(** ** U0 touch *)
Inductive zres := ZRet (ov:N) (z:zN) | ZAbs (f:N) | ZFail.
Definition ztouch z : zres := match z with
  | Z0 [] y f => if N.eqb y 0 then (if N.eqb f 0 then ZFail else ZAbs f) else ZRet 0%N (Z0 [] (N.pred y) (N.succ f))
  | Z0 bs x f => match consumeN bs 0%N with Some (ov,bs',_) => ZRet ov (Z0 bs' x (N.succ f)) | None => ZFail end
  | ZD bs false a x f => if N.eqb x 0 then ZFail else
      match consumeN bs a with Some (ov,bs',a') => ZRet ov (ZD bs' true a' (N.pred x) f) | None => ZFail end
  | ZD bs true a x f => match consumeN (bs ++ [(a,1%N);(x,f)]) 0%N with Some (ov,bs',_) => ZRet ov (Z0 bs' 0 1) | None => ZFail end
  end.
Lemma ztouch_ret z ov z': ztouch z = ZRet ov z' -> sideRL tm hB hD (zside z) ([1;1;1]^^(N.to_nat ov) *> zside z').
Proof.
  destruct z as [[|p bs] x f|bs [] a x f]; cbn [ztouch zside].
  - destruct (N.eqb_spec x 0) as [Hx|Hx]; [destruct (N.eqb f 0); discriminate|].
    intros E; injection E as <- <-. cbn [zside cvl map cw app]. change (N.to_nat 0) with 0%nat.
    cbn [lpow Str_app]. rewrite N2Nat.inj_succ.
    replace (N.to_nat x) with (S (N.to_nat (N.pred x))) by lia. apply z_empty.
  - destruct (consumeN (p::bs) 0%N) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
    intros E; injection E as <- <-. apply consumeN_spec in Ec. cbn [zside].
    rewrite <-Str_app_assoc, N2Nat.inj_succ. apply (z_lead _ _ _ _ _ (N.to_nat a'')); [discriminate|exact Ec].
  - destruct (consumeN _ 0%N) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
    intros E; injection E as <- <-. apply consumeN_spec in Ec. rewrite cvl_app in Ec.
    cbn [cvl map] in Ec. unfold cvp in Ec; cbn [fst snd] in Ec. change (N.to_nat 1) with 1%nat in Ec.
    cbn [zside]. rewrite <-Str_app_assoc. change (N.to_nat 0) with 0%nat. change (N.to_nat 1) with 1%nat.
    apply (z_1111 _ _ _ _ _ _ (N.to_nat a'')), Ec.
  - destruct (N.eqb_spec x 0) as [Hx|Hx]; [discriminate|].
    destruct (consumeN bs a) as [[[o b'] a'']|] eqn:Ec; [|discriminate].
    intros E; injection E as <- <-. apply consumeN_spec in Ec. cbn [zside]. rewrite <-Str_app_assoc.
    replace (N.to_nat x) with (S (N.to_nat (N.pred x))) by lia. apply z_stop, Ec.
Qed.
Lemma ztouch_abs z f: ztouch z = ZAbs f -> sideRL tm hB hD (zside z) (([1;1] ++ [1;1;1]^^(N.to_nat f)) *> const 0).
Proof.
  destruct z as [[|p bs] x f'|bs [] a x f']; cbn [ztouch zside].
  - destruct (N.eqb_spec x 0) as [Hx|Hx]; [|discriminate]. destruct (N.eqb_spec f' 0) as [Hf|Hf]; [discriminate|].
    intros E; injection E as <-. subst x. cbn [cvl map cw app].
    replace (N.to_nat f') with (S (N.to_nat f' - 1)) by lia. apply z_absorb.
  - destruct (consumeN (p::bs) 0%N) as [[[o b'] a'']|]; discriminate.
  - destruct (consumeN _ 0%N) as [[[o b'] a'']|]; discriminate.
  - destruct (N.eqb x 0); [discriminate|]. destruct (consumeN bs a) as [[[o b'] a'']|]; discriminate.
Qed.

(** ** one call from the root through the units *)
Inductive cres := CRet (ov:N) (us:list unitN) (z:zN) | CHalt | CFail.
Definition setg u g := UN (ubs u) (ubit u) (ua u) (ux u) g.
Fixpoint callN (us:list unitN) (z:zN) : cres := match us with
  | [] => match ztouch z with ZRet ov z' => CRet ov [] z' | _ => CFail end
  | u :: us1 => match touchN u with
    | TStop ov u' => CRet ov (u' :: us1) z
    | THalt => CHalt
    | TFail => CFail
    | TPass ov u' => match us1 with
      | [] => match ztouch z with
        | ZRet ov2 z' => CRet ov [setg u' ov2] z'
        | ZAbs f => CRet ov [] (ZD (ubs u') (ubit u') (ua u') (ux u') (ug u' + f + 1))
        | ZFail => CFail end
      | _ => match callN us1 z with
        | CRet ov2 us' z' => CRet ov (setg u' ov2 :: us') z'
        | CHalt => CHalt | CFail => CFail end
      end
    end
  end.

Lemma side1 {w w' r r'}: segRLs tm h h w w' -> sideRL tm hB hD r r' -> sideRL tm hB hD (w *> r) (w' *> r').
Proof.
  intros H1 H2. assert (H3: sideRLs tm h r r'). { unfold h. econstructor; [exact H2|constructor]. }
  pose proof (segRLs_sideRLs_concat H1 H3) as H. unfold h in H. inversion H; subst.
  match goal with Hs: sideRLs _ [] _ _ |- _ => inversion Hs; subst end. assumption.
Qed.
Lemma setg_word u g: ug u = 0%N -> uwN u ++ [1;1;1]^^(N.to_nat g) = uwN (setg u g).
Proof. intros E. unfold uwN, setg, uw, tailw. cbn [ubs ubit ua ux ug]. rewrite E. cbn. rewrite <-!app_assoc. reflexivity. Qed.
Lemma abs_word u f: ug u = 0%N -> uwN u ++ [1;1] ++ [1;1;1]^^(N.to_nat f) =
  uw (cvl (ubs u)) (ubit u) (N.to_nat (ua u)) (N.to_nat (ux u)) (edge1w (N.to_nat (ug u + f + 1))).
Proof.
  intros E. unfold uwN, uw, tailw, edge1w. rewrite E. rewrite <-!app_assoc. f_equal. f_equal.
  replace (N.to_nat (0 + f + 1)) with (S (N.to_nat f)) by lia. cbn. reflexivity.
Qed.

Lemma callN_ret us: forall z ov us' z', callN us z = CRet ov us' z' ->
  sideRL tm hB hD (dwords us *> zside z) (([1;1;1]^^(N.to_nat ov) ++ dwords us') *> zside z').
Proof.
  induction us as [|u us1 IH]; intros z ov us' z' E; cbn [callN] in E.
  - destruct (ztouch z) as [o z1|f|] eqn:Ez; try discriminate. injection E as <- <- <-.
    cbn [dwords]. rewrite app_nil_r. cbn [Str_app]. apply ztouch_ret, Ez.
  - destruct (touchN u) as [o u1|o u1| |] eqn:Et; try discriminate.
    + injection E as <- <- <-. apply touchN_stop in Et. cbn [dwords].
      rewrite (app_assoc ([1;1;1]^^(N.to_nat o))), !(Str_app_assoc _ (dwords us1)).
      apply segRL_side, Et.
    + apply touchN_pass in Et. destruct Et as [Ht Hg].
      destruct us1 as [|v us2].
      * destruct (ztouch z) as [o2 z1|f|] eqn:Ez; try discriminate.
        -- injection E as <- <- <-. apply ztouch_ret in Ez. pose proof (side1 Ht Ez) as H.
           cbn [dwords]. rewrite !app_nil_r. applys_eq H; rewrite <-?Str_app_assoc; f_equal.
           rewrite <-!app_assoc, setg_word by exact Hg. reflexivity.
        -- injection E as <- <- <-. apply ztouch_abs in Ez. pose proof (side1 Ht Ez) as H.
           cbn [dwords zside]. rewrite !app_nil_r. applys_eq H; rewrite <-?Str_app_assoc; f_equal.
           rewrite <-!app_assoc, abs_word by exact Hg. reflexivity.
      * destruct (callN (v :: us2) z) as [o2 us3 z1| |] eqn:Ec; try discriminate.
        injection E as <- <- <-. apply IH in Ec. pose proof (side1 Ht Ec) as H.
        cbn [dwords] in *. applys_eq H; rewrite <-?Str_app_assoc; f_equal.
        rewrite <-!app_assoc. f_equal. rewrite app_assoc, setg_word by exact Hg. reflexivity.
Qed.
Lemma callN_halt us: forall z, callN us z = CHalt -> sideRLs_halt tm h (dwords us *> zside z).
Proof.
  induction us as [|u us1 IH]; intros z E; cbn [callN] in E.
  - destruct (ztouch z); discriminate.
  - destruct (touchN u) as [o u1|o u1| |] eqn:Et; try discriminate.
    + apply touchN_pass in Et. destruct Et as [Ht Hg]. destruct us1 as [|v us2].
      * destruct (ztouch z); discriminate.
      * destruct (callN (v :: us2) z) as [o2 us3 z1| |] eqn:Ec; try discriminate.
        apply IH in Ec. cbn [dwords]. rewrite Str_app_assoc.
        exact (segRLs_sideRLs_halt_concat _ _ _ _ _ _ Ht Ec).
    + pose proof (touchN_halt _ Et) as Hh.
      cbn [dwords]. rewrite Str_app_assoc. unfold h. constructor. intros l. cbn. apply Hh.
Qed.

(** ** one increment *)
Inductive ires := IOk (c:cfg) | IHalt | IFail.
Definition inc1 c : ires := match ctl c with
  | TT t g =>
    if N.eqb g 0 then match callN (cus c) (cz c) with
      | CRet ov us' z' => IOk (Cfg (TT (N.succ t) ov) us' z') | CHalt => IHalt | CFail => IFail end
    else if N.eqb g 1 then match callN (cus c) (cz c) with
      | CRet ov us' z' => IOk (Cfg (NTl (N.succ t) ov) us' z') | CHalt => IHalt | CFail => IFail end
    else IFail
  | NTl s g => if N.eqb s 0 then IFail else IOk (Cfg (TT 0 0) (UN [] true (N.pred s) 0 g :: cus c) (cz c))
  end.
Lemma inc1_ok c c': inc1 c = IOk c' -> denote c -->* denote c'.
Proof.
  destruct c as [[t g|s g] us z]; unfold inc1, denote; cbn [ctl cus cz].
  - destruct (N.eqb_spec g 0) as [Hg|Hg]; [|destruct (N.eqb_spec g 1) as [Hg1|Hg1]].
    + destruct (callN us z) as [ov us' z'| |] eqn:E; try discriminate. intros H; injection H as <-.
      apply callN_ret in E. cbn [ctl cus cz]. subst g. cbn [N.to_nat lpow app].
      rewrite N2Nat.inj_succ. apply progress_evstep, root_step, E.
    + destruct (callN us z) as [ov us' z'| |] eqn:E; try discriminate. intros H; injection H as <-.
      apply callN_ret in E. cbn [ctl cus cz]. subst g. change (N.to_nat 1) with 1%nat. cbn [lpow].
      rewrite app_nil_r, Str_app_assoc, N2Nat.inj_succ.
      eapply evstep_trans. 1: apply (reset1 _ _ _ E).
      unfold NT. rewrite <-!Str_app_assoc. apply evstep_refl'. f_equal. f_equal. unfold tailw.
      rewrite <-!app_assoc. reflexivity.
    + discriminate.
  - destruct (N.eqb_spec s 0) as [Hs|Hs]; [discriminate|]. intros H; injection H as <-. cbn [ctl cus cz dwords].
    replace (N.to_nat s) with (S (N.to_nat (N.pred s))) by lia.
    eapply evstep_trans. 1: apply reset2.
    replace ((lead1 (N.to_nat (N.pred s)) 0 ++ tailw (N.to_nat g)) *> (dwords us *> zside z))
      with (([1;1;1]^^(N.to_nat 0) ++ dwords (UN [] true (N.pred s) 0 g :: us)) *> zside z).
    + apply evstep_refl.
    + cbn [dwords N.to_nat lpow app]. rewrite Str_app_assoc. reflexivity.
Qed.
Lemma inc1_halt c: inc1 c = IHalt -> halts tm (denote c).
Proof.
  destruct c as [[t g|s g] us z]; unfold inc1, denote; cbn [ctl cus cz].
  - destruct (N.eqb_spec g 0) as [Hg|Hg]; [|destruct (N.eqb_spec g 1) as [Hg1|Hg1]].
    + destruct (callN us z) as [ov us' z'| |] eqn:E; try discriminate. intros _.
      apply callN_halt in E. subst g. cbn [N.to_nat lpow app]. apply root_halt, E.
    + destruct (callN us z) as [ov us' z'| |] eqn:E; try discriminate. intros _.
      apply callN_halt in E. subst g. change (N.to_nat 1) with 1%nat. cbn [lpow]. rewrite app_nil_r, Str_app_assoc.
      apply reset1_halt, E.
    + discriminate.
  - destruct (N.eqb s 0); discriminate.
Qed.

(** * Batches: n touches of one unit with no structural event, in closed form *)
Ltac fin := try reflexivity; cbn [lpow app]; try lia; try (f_equal; lia); try (f_equal; f_equal; lia); try (f_equal; f_equal; f_equal; lia).
Lemma stop1s {bs a x far ov bs' a'}: consume bs a = Some (ov, bs', a') ->
  segRLs tm h [] (uw bs false a (S x) far) ([1;1;1]^^ov ++ uw bs' true a' x far).
Proof. intros E. unfold h. econstructor; [apply (t_stop _ _ _ _ _ _ _ E)|constructor]. Qed.
Lemma pairK q: forall c j r a x, segRLs tm (h^^(q*2)) (h^^q)
  (uw ((q*2+c, j)::r) false a (S x) (tailw 0)) (uw ((c,j)::r) false (q+a) (S (q+x)) (tailw 0)).
Proof.
  induction q as [|q IH]; intros c j r a x.
  - apply segRLs_O.
  - pose proof (@stop1s ((S (S (q*2+c)), j)::r) a x (tailw 0) 0 ((S (q*2+c), j)::r) a eq_refl) as H1.
    pose proof (t_pass ((S (q*2+c), j)::r) a x 0 ((q*2+c,j)::r) (S a) eq_refl) as H2.
    pose proof (IH c j r (S a) (S x)) as H3.
    pose proof (segRLs_trans H1 (segRLs_trans H2 H3)) as H.
    applys_eq H; fin.
Qed.
Lemma pair1 q: forall a x, segRLs tm (h^^(q*2)) (h^^q)
  (uw [] false (q+a) (S x) (tailw 0)) (uw [] false a (S (q+x)) (tailw 0)).
Proof.
  induction q as [|q IH]; intros a x.
  - apply segRLs_O.
  - pose proof (@stop1s [] (S (q+a)) x (tailw 0) 0 [] (q+a) eq_refl) as H1.
    pose proof (t_pass [] (q+a) x 0 [] (q+a) eq_refl) as H2.
    pose proof (IH a (S x)) as H3.
    pose proof (segRLs_trans H1 (segRLs_trans H2 H3)) as H.
    applys_eq H; fin.
Qed.
Definition b2n (b:bool) : nat := if b then 1 else 0.
Lemma clK0 q rb c j r a x: segRLs tm (h^^(q*2 + b2n rb)) (h^^q)
  (uw ((q*2 + b2n rb + c, j)::r) false a (S x) (tailw 0)) (uw ((c,j)::r) rb (q+a) (q + S x - b2n rb) (tailw 0)).
Proof.
  destruct rb; cbn [b2n].
  - pose proof (pairK q (S c) j r a x) as H1.
    pose proof (@stop1s ((S c, j)::r) (q+a) (q+x) (tailw 0) 0 ((c,j)::r) (q+a) eq_refl) as H2.
    pose proof (segRLs_trans H1 H2) as H. rewrite lpow_add.
    rewrite app_nil_r in H. applys_eq H; fin.
  - pose proof (pairK q c j r a x) as H. applys_eq H; fin.
Qed.
Lemma clK1 q rb c j r a x: segRLs tm (h^^(S (q*2 + b2n rb))) (h^^(S q))
  (uw ((S (q*2 + b2n rb + c), j)::r) true a x (tailw 0)) (uw ((c,j)::r) rb (q + S a) (q + S (S x) - b2n rb) (tailw 0)).
Proof.
  pose proof (t_pass ((S (q*2 + b2n rb + c), j)::r) a x 0 ((q*2 + b2n rb + c, j)::r) (S a) eq_refl) as H1.
  pose proof (clK0 q rb c j r (S a) (S x)) as H2.
  exact (segRLs_trans H1 H2).
Qed.
Lemma cl10 q rb a x: segRLs tm (h^^(q*2 + b2n rb)) (h^^q)
  (uw [] false (q + b2n rb + a) (S x) (tailw 0)) (uw [] rb a (q + S x - b2n rb) (tailw 0)).
Proof.
  destruct rb; cbn [b2n].
  - pose proof (pair1 q (S a) x) as H1.
    pose proof (@stop1s [] (S a) (q+x) (tailw 0) 0 [] a eq_refl) as H2.
    pose proof (segRLs_trans H1 H2) as H. rewrite lpow_add.
    rewrite app_nil_r in H. applys_eq H; fin.
  - pose proof (pair1 q a x) as H. applys_eq H; fin.
Qed.
Lemma cl11 q rb a x: segRLs tm (h^^(S (q*2 + b2n rb))) (h^^(S q))
  (uw [] true (q + b2n rb + a) x (tailw 0)) (uw [] rb a (q + S (S x) - b2n rb) (tailw 0)).
Proof.
  pose proof (t_pass [] (q + b2n rb + a) x 0 [] (q + b2n rb + a) eq_refl) as H1.
  pose proof (cl10 q rb a (S x)) as H2.
  exact (segRLs_trans H1 H2).
Qed.

Definition b2N (b:bool) : N := if b then 1%N else 0%N.
Lemma b2N_nat b: N.to_nat (b2N b) = b2n b.
Proof. destruct b; reflexivity. Qed.
Lemma div2_nat n: N.to_nat n = N.to_nat (N.div2 n) * 2 + b2n (N.odd n).
Proof. rewrite <-b2N_nat. pose proof (N.div2_odd n) as E. unfold b2N. destruct (N.odd n); cbn [N.b2n] in E; lia. Qed.

Definition closedU (n:N) (u:unitN) : option (unitN * N) :=
  if N.eqb n 0 then Some (u, 0%N) else
  match ubs u with
  | (c,j)::r =>
    if negb (ubit u) then
      if N.eqb n 1 then
        if N.eqb (ux u) 0 || N.eqb c 0 then None
        else Some (UN ((N.pred c, j)::r) true (ua u) (N.pred (ux u)) (ug u), 0%N)
      else
        if negb (N.eqb (ug u) 0) || N.eqb (ux u) 0 || N.ltb c n then None
        else Some (UN (((c - n)%N, j)::r) (N.odd n) (N.div2 n + ua u) (N.div2 n + ux u - b2N (N.odd n)) 0, N.div2 n)
    else
      if negb (N.eqb (ug u) 0) || N.ltb c n then None
      else Some (UN (((c - n)%N, j)::r) (N.odd (N.pred n)) (N.div2 (N.pred n) + N.succ (ua u))
             (N.div2 (N.pred n) + N.succ (N.succ (ux u)) - b2N (N.odd (N.pred n))) 0, N.succ (N.div2 (N.pred n)))
  | [] =>
    if negb (ubit u) then
      if N.eqb n 1 then
        if N.eqb (ux u) 0 || N.eqb (ua u) 0 then None
        else Some (UN [] true (N.pred (ua u)) (N.pred (ux u)) (ug u), 0%N)
      else
        if negb (N.eqb (ug u) 0) || N.eqb (ux u) 0 || N.ltb (ua u) (N.div2 n + b2N (N.odd n)) then None
        else Some (UN [] (N.odd n) (ua u - N.div2 n - b2N (N.odd n)) (N.div2 n + ux u - b2N (N.odd n)) 0, N.div2 n)
    else
      if negb (N.eqb (ug u) 0) || N.ltb (ua u) (N.div2 (N.pred n) + b2N (N.odd (N.pred n))) then None
      else Some (UN [] (N.odd (N.pred n)) (ua u - N.div2 (N.pred n) - b2N (N.odd (N.pred n)))
             (N.div2 (N.pred n) + N.succ (N.succ (ux u)) - b2N (N.odd (N.pred n))) 0, N.succ (N.div2 (N.pred n)))
  end.

Ltac bnorm := repeat match goal with
  | H: (_ || _) = false |- _ => apply Bool.orb_false_iff in H; destruct H
  | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
  | H: N.eqb _ _ = true |- _ => apply N.eqb_eq in H
  | H: N.eqb _ _ = false |- _ => apply N.eqb_neq in H
  | H: N.ltb _ _ = false |- _ => apply N.ltb_ge in H
  end.
Ltac dif := match goal with |- context [if ?b then _ else _] => destruct b eqn:G end.
Ltac weq := unfold uwN; cbn [ubs ubit ua ux ug cvl map lpow app]; try unfold cvp; cbn [fst snd]; f_equal; try f_equal; try f_equal; try lia.

Lemma closedU_spec n u u' p: closedU n u = Some (u', p) ->
  segRLs tm (h^^(N.to_nat n)) (h^^(N.to_nat p)) (uwN u) (uwN u').
Proof.
  unfold closedU. destruct (N.eqb_spec n 0) as [Hn|Hn].
  { intros E; injection E as <- <-. subst n. apply segRLs_O. }
  destruct u as [[|[c j] r] [] a x g]; cbn [ubs ubit ua ux ug negb].
  - (* k=1, bit 1 *)
    dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst g.
    pose proof (div2_nat (N.pred n)) as Hd. rewrite <-b2N_nat in Hd.
    pose proof (cl11 (N.to_nat (N.div2 (N.pred n))) (N.odd (N.pred n))
      (N.to_nat (a - N.div2 (N.pred n) - b2N (N.odd (N.pred n)))) (N.to_nat x)) as HH.
    rewrite <-b2N_nat in HH. applys_eq HH; try (f_equal; lia); weq.
  - (* k=1, bit 0 *)
    destruct (N.eqb_spec n 1) as [Hn1|Hn1]; cbn [negb].
    + dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst n.
      assert (Ec: consume [] (N.to_nat a) = Some (0%nat, [], N.to_nat (N.pred a))).
      { unfold consume. replace (N.to_nat a) with (S (N.to_nat (N.pred a))) by lia. reflexivity. }
      pose proof (@stop1s [] _ (N.to_nat (N.pred x)) (tailw (N.to_nat g)) _ _ _ Ec) as HH.
      change (h^^(N.to_nat 1)) with h. change (h^^(N.to_nat 0)) with (@nil (DH0*DH0)).
      applys_eq HH; weq.
    + dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst g.
      pose proof (div2_nat n) as Hd. rewrite <-b2N_nat in Hd.
      pose proof (cl10 (N.to_nat (N.div2 n)) (N.odd n) (N.to_nat (a - N.div2 n - b2N (N.odd n))) (N.to_nat (N.pred x))) as HH.
      rewrite <-b2N_nat in HH. applys_eq HH; try (f_equal; lia); weq.
  - (* k>=2, bit 1 *)
    dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst g.
    pose proof (div2_nat (N.pred n)) as Hd. rewrite <-b2N_nat in Hd.
    pose proof (clK1 (N.to_nat (N.div2 (N.pred n))) (N.odd (N.pred n)) (N.to_nat (c - n)) (N.to_nat j) (cvl r)
      (N.to_nat a) (N.to_nat x)) as HH.
    rewrite <-b2N_nat in HH. applys_eq HH; try (f_equal; lia); weq.
  - (* k>=2, bit 0 *)
    destruct (N.eqb_spec n 1) as [Hn1|Hn1]; cbn [negb].
    + dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst n.
      assert (Ec: consume ((N.to_nat c, N.to_nat j)::cvl r) (N.to_nat a) = Some (0%nat, (N.to_nat (N.pred c), N.to_nat j)::cvl r, N.to_nat a)).
      { unfold consume. replace (N.to_nat c) with (S (N.to_nat (N.pred c))) by lia. reflexivity. }
      pose proof (@stop1s _ _ (N.to_nat (N.pred x)) (tailw (N.to_nat g)) _ _ _ Ec) as HH.
      change (h^^(N.to_nat 1)) with h. change (h^^(N.to_nat 0)) with (@nil (DH0*DH0)).
      applys_eq HH; weq.
    + dif; [discriminate|]. bnorm. intros E; injection E as <- <-. subst g.
      pose proof (div2_nat n) as Hd. rewrite <-b2N_nat in Hd.
      pose proof (clK0 (N.to_nat (N.div2 n)) (N.odd n) (N.to_nat (c - n)) (N.to_nat j) (cvl r) (N.to_nat a) (N.to_nat (N.pred x))) as HH.
      rewrite <-b2N_nat in HH. applys_eq HH; try (f_equal; lia); weq.
Qed.

(** ** U0 in a batch *)
Lemma zLs m: forall c j r x f, sideRLs tm (h^^m) ((cw ((m+c,j)::r) ++ edgew x f) *> const 0)
  ((cw ((c,j)::r) ++ edgew x (m+f)) *> const 0).
Proof.
  induction m as [|m IH]; intros c j r x f.
  - constructor.
  - pose proof (z_lead ((S (m+c), j)::r) x f 0 ((m+c,j)::r) 0 ltac:(discriminate) eq_refl) as H1.
    cbn [lpow app] in H1. unfold h. cbn [lpow app]. econstructor. 1: exact H1.
    replace (S m + f) with (m + S f) by lia. apply IH.
Qed.
Lemma zEs m: forall y f, sideRLs tm (h^^m) (edgew (m+y) f *> const 0) (edgew y (m+f) *> const 0).
Proof.
  induction m as [|m IH]; intros y f.
  - constructor.
  - unfold h. cbn [lpow app]. econstructor. 1: apply (z_empty (m+y) f).
    replace (S m + f) with (m + S f) by lia. apply IH.
Qed.
Definition closedZ (m:N) (z:zN) : option zN :=
  if N.eqb m 0 then Some z else
  match z with
  | Z0 [] y f => if N.ltb y m then None else Some (Z0 [] (y - m) (f + m))
  | Z0 ((c,j)::r) x f => if N.ltb c m then None else Some (Z0 (((c - m)%N, j)::r) x (f + m))
  | ZD _ _ _ _ _ => None
  end.
Lemma closedZ_spec m z z': closedZ m z = Some z' -> sideRLs tm (h^^(N.to_nat m)) (zside z) (zside z').
Proof.
  unfold closedZ. destruct (N.eqb_spec m 0) as [Hm|Hm].
  { intros E; injection E as <-. subst m. constructor. }
  destruct z as [[|[c j] r] x f|bs b a x f]; try discriminate.
  - destruct (N.ltb_spec x m) as [Hx|Hx]; [discriminate|]. intros E; injection E as <-.
    cbn [zside cvl map cw app]. pose proof (zEs (N.to_nat m) (N.to_nat (x - m)) (N.to_nat f)) as H.
    replace (N.to_nat x) with (N.to_nat m + N.to_nat (x - m)) by lia.
    replace (N.to_nat (f + m)) with (N.to_nat m + N.to_nat f) by lia. exact H.
  - destruct (N.ltb_spec c m) as [Hc|Hc]; [discriminate|]. intros E; injection E as <-.
    cbn [zside cvl map]. unfold cvp; cbn [fst snd].
    pose proof (zLs (N.to_nat m) (N.to_nat (c - m)) (N.to_nat j) (cvl r) (N.to_nat x) (N.to_nat f)) as H.
    replace (N.to_nat c) with (N.to_nat m + N.to_nat (c - m)) by lia.
    replace (N.to_nat (f + m)) with (N.to_nat m + N.to_nat f) by lia. exact H.
Qed.

Fixpoint batchL (n:N) (us:list unitN) (z:zN) : option (list unitN * zN) := match us with
  | [] => match closedZ n z with Some z' => Some ([], z') | None => None end
  | u :: us => match closedU n u with
    | Some (u', p) => match batchL p us z with Some (us', z') => Some (u' :: us', z') | None => None end
    | None => None end end.
Lemma batchL_spec us: forall n z us' z', batchL n us z = Some (us', z') ->
  sideRLs tm (h^^(N.to_nat n)) (dwords us *> zside z) (dwords us' *> zside z').
Proof.
  induction us as [|u us IH]; intros n z us' z' E; cbn [batchL] in E.
  - destruct (closedZ n z) as [z1|] eqn:Ez; [|discriminate]. injection E as <- <-. apply closedZ_spec, Ez.
  - destruct (closedU n u) as [[u1 p]|] eqn:Eu; [|discriminate].
    destruct (batchL p us z) as [[us1 z1]|] eqn:Eb; [|discriminate]. injection E as <- <-.
    cbn [dwords]. rewrite !Str_app_assoc.
    exact (segRLs_sideRLs_concat (closedU_spec _ _ _ _ Eu) (IH _ _ _ _ Eb)).
Qed.

(** ** batch-size proposal (untrusted; a port of the accelerated simulator) *)
Definition evt_unit (u:unitN) : N :=
  let own := match ubs u with (c,_)::_ => N.succ c | [] => (2 * ua u + b2N (ubit u))%N end in
  let own := if negb (ubit u) && N.eqb (ux u) 0 then 1%N else own in
  if N.eqb (ug u) 0 then own else N.min own (if ubit u then 1%N else 2%N).
Definition evt_z z : N := match z with Z0 [] y _ => N.succ y | Z0 ((c,_)::_) _ _ => N.succ c | ZD _ _ _ _ _ => 1%N end.
Definition first_inc (C q n : N) : N := (n * 2^q - C mod 2^q)%N.
Fixpoint cval (us:list unitN) (i:N) : N := match us with
  | [] => 0%N | u :: us => ((if ubit u then 2^i else 0) + cval us (N.succ i))%N end.
Fixpoint pmin (us:list unitN) (i C:N) (z:zN) : N := match us with
  | [] => first_inc C i (evt_z z)
  | u :: us => N.min (first_inc C i (evt_unit u)) (pmin us (N.succ i) C z) end.
Definition propose (us:list unitN) (z:zN) : N := N.pred (pmin us 0 (cval us 0) z).

(** ** the checker *)
Definition batch_step c : option cfg := match ctl c with
  | TT t g => if N.eqb g 0 then
      let d := propose (cus c) (cz c) in
      if N.eqb d 0 then None else
      match batchL d (cus c) (cz c) with Some (us', z') => Some (Cfg (TT (t + d) 0) us' z') | None => None end
    else None
  | NTl _ _ => None end.
Lemma batch_step_spec c c': batch_step c = Some c' -> denote c -->* denote c'.
Proof.
  destruct c as [[t g|s g] us z]; unfold batch_step; cbn [ctl cus cz]; [|discriminate].
  destruct (N.eqb_spec g 0) as [Hg|Hg]; [|discriminate]. subst g.
  destruct (N.eqb (propose us z) 0); [discriminate|].
  destruct (batchL (propose us z) us z) as [[us' z']|] eqn:E; [|discriminate]. intros H; injection H as <-.
  apply batchL_spec in E. unfold denote; cbn [ctl cus cz N.to_nat lpow app].
  replace (N.to_nat (t + propose us z)) with (N.to_nat (propose us z) + N.to_nat t) by lia.
  apply root_steps, E.
Qed.
Definition next c : cfg + unit := match batch_step c with
  | Some c' => inl c'
  | None => match inc1 c with IOk c' => inl c' | IHalt => inr tt | IFail => inl c end end.
Lemma next_spec c: match next c with inl c' => denote c -->* denote c' | inr _ => halts tm (denote c) end.
Proof.
  unfold next. destruct (batch_step c) as [c'|] eqn:Eb; [apply batch_step_spec, Eb|].
  destruct (inc1 c) as [c'| |] eqn:Ei.
  - apply inc1_ok, Ei.
  - apply inc1_halt, Ei.
  - apply evstep_refl.
Qed.
Definition c342 := Cfg (NTl 1 1) [] (Z0 [(0%N,3%N)] 0 1).
Definition check fuel := match N_iter_until next (inl c342) fuel with inl _ => false | inr _ => true end.
Theorem check_spec fuel: check fuel = true -> halts tm (denote c342).
Proof.
  pose proof (@N_iter_until_spec cfg unit next (inl c342) fuel
    (fun c => denote c342 -->* denote c) (fun _ => halts tm (denote c342))) as H.
  assert (Hstep: forall c, denote c342 -->* denote c ->
    match next c with inl c' => denote c342 -->* denote c' | inr _ => halts tm (denote c342) end).
  { intros c E. pose proof (next_spec c) as I. destruct (next c).
    - eapply evstep_trans; eauto.
    - eapply halts_evstep; [exact I|exact E]. }
  specialize (H Hstep (evstep_refl _ _)). unfold check.
  destruct (N_iter_until next (inl c342) fuel); [discriminate|]. intros _. exact H.
Qed.


Lemma init: c0 -[tm]->* denote c342.
Proof. unfold denote, c342, NT, zside; cbn. solve_init. Qed.

Theorem halt: halts tm c0.
Proof.
  eapply halts_evstep; [|apply init].
  apply (check_spec 110000). native_check_eq.
Qed.
End TM12.

