(* 1RB0RE_1LC0RA_1LA1LD_0LC1LF_0LB1RB_1RA--- halts (BB(6) holdout #269).

   The halt is at step 584,561,241,995,715,367 (state F reading 1, cell 773,418,931). That number is checked, not
   proved here (es' proves -->* only): an item-level model plus a plain TM for the last 51,588,980,087 steps, a
   direct simulator (mm4h), a plain TM from a window 3.8e6 steps before the halt, and an independent replication
   (Astra, GPT-6) all give it.

   Structure:
   - Item model. At each left-end record the tape is a block (10)^n, a rest block, a list of items and a fixed
     END word; the items form a binary counter. Every item-level rule is a one-sweep theorem (es' windows
     composed as units), and the abstract sweep `step` is proved sound.
   - init100: the blank tape to the record of sweep 100 (512,298 steps, vm_compute).
   - Batched run, sweep 100 to sweep 110,596,984 (vm_compute): 576,009 macro ticks of 192 = 3 * 2^6 sweeps and
     3,156 single sweeps. In a macro tick the low counter levels (cut at the k-th marker item, k = 6..9) take a
     memoized 192-sweep result checked when first met, the long run of plain items of size 2 and everything right
     of it repeat with period 2, and the high levels run in closed-form quiet stretches between their own events.
   - End game: 11 turns, 12 partial sweeps over the items right of the turn region, and the halting leg.
   The model was matched against direct simulation sweep by sweep (3,994 sweeps), against full tape dumps at
   1e9 to 1e13 steps and against the mm4h headers at 1e14 and 1e16. Running `step` alone over the whole run
   reaches the same record at sweep 110,596,984. *)
From BusyCoq Require Import Individual62 ES_v3 Eqb.
Require Import String List Lia NArith.
Import ListNotations.
Set Default Goal Selector "1".

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0RA_1LA1LD_0LC1LF_0LB1RB_1RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** * Local rules (found and proved by es') *)

Lemma MR0 x l r :
  l {{B}}> [1] *> [1;1;1;1;1;1]^^x *> [0] *> r -->* l <* [1;0;0;1;0;0]^^x <* [1;0] {{B}}> r.
Proof. es' x & l r. Qed.
Lemma PR0 l r :
  l <* [1;0;0;1;0;0] <* [1;0] {{B}}> [1;1;1;0] *> r -->* l <* [1;0;0;1;0;0;1;0;1;1;0;0] {{B}}> r.
Proof. es' & l r. Qed.
Lemma LB0' x l r :
  l <* [1;0;0;1;0;0]^^x <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1] *> [1;1;1;1;1;1]^^x *> [0] *> r.
Proof. es' x & l r. Qed.
Lemma LB1' x l r :
  l <* [1;0;0;1;0;0]^^x <{{C}} [0;1] *> r -->* l <{{C}} [0;1] *> [1;1;1;1;1;1]^^x *> r.
Proof. es' x & l r. Qed.
Lemma L10' l r : l <* [1;0] <{{C}} [0;1] *> r -->* l <{{C}} [0;1;0;1] *> r.
Proof. es' & l r. Qed.
Lemma LK' l r :
  l <* [1;0;0;1;0;0;1;0;1;1;0;0] <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1;0] *> [1;1;1;0] *> [1;1;1;1;1;1;1] *> r.
Proof. es' & l r. Qed.

(** * Blocks and their converted forms *)

Definition B6 : list Sym := [1;0;0;1;0;0].
Definition S6 : list Sym := [1;1;1;1;1;1].
Definition K12 : list Sym := [1;0;0;1;0;0;1;0;1;1;0;0].
Definition PH : list Sym := [1;1;1;0].
Definition Mb (x:nat) : list Sym := [1] ++ S6^^x ++ [0].
Definition conv (x:nat) : list Sym := [1;0] ++ B6^^x.    (* converted M(x), nearest cell first *)
Definition T8 : list Sym := [1;0] ++ B6.                  (* converted tail of an M(x>=1) *)

Fixpoint Ms (xs:list nat) : list Sym := match xs with [] => [] | x::xs => Mb x ++ Ms xs end.
(* converted blocks, nearest (= last block) first *)
Fixpoint convs (xs:list nat) : list Sym := match xs with [] => [] | x::xs => convs xs ++ conv x end.

Lemma MR x l r : l {{B}}> Mb x *> r -->* l <* conv x {{B}}> r.
Proof.
  unfold Mb, conv. rewrite !Str_app_assoc. pose proof (MR0 x l r) as H.
  change (l <* [1;0;0;1;0;0]^^x <* [1;0]) with (l <* ([1;0] ++ [1;0;0;1;0;0]^^x)) in H.
  exact H.
Qed.

Lemma MRs xs : forall l r, l {{B}}> Ms xs *> r -->* l <* convs xs {{B}}> r.
Proof.
  induction xs as [|x xs IH]; intros l r; cbn [Ms convs].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply MR|].
    pose proof (IH (l <* conv x) r) as H. rewrite <- Str_app_assoc in H. exact H.
Qed.

Lemma conv_S x : conv (S x) = T8 ++ B6^^x.
Proof. unfold conv, T8. cbn [lpow]. rewrite app_assoc. reflexivity. Qed.

(* rightward over a header after the converted tail of an M(x>=1) *)
Lemma PR l r : l <* T8 {{B}}> PH *> r -->* l <* K12 {{B}}> r.
Proof. unfold T8, PH. exact (PR0 l r). Qed.

(** * One item: rightward, then leftward *)

(* an item  P M(x0) ... M(xk)  with a last block M(S y); [init] = the blocks before the last *)
Definition enc_item (init:list nat) (y:nat) : list Sym := PH ++ Ms init ++ Mb (S y).
(* its converted form left behind by the rightward pass (the tail T8 of the last block goes to the next header) *)
Definition rconv (init:list nat) (y:nat) : list Sym := B6^^y ++ convs init ++ K12.

Lemma right_item init y l r :
  l <* T8 {{B}}> enc_item init y *> r -->* l <* rconv init y <* T8 {{B}}> r.
Proof.
  unfold enc_item. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply PR|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|].
  rewrite conv_S. unfold rconv. rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Fixpoint Lout (xs:list nat) : list Sym := match xs with [] => [] | x::xs => S6^^x ++ [0;1] ++ Lout xs end.

Lemma Lconvs xs : forall l R, l <* convs xs <{{C}} [0;1] *> R -->* l <{{C}} [0;1] *> Lout xs *> R.
Proof.
  induction xs as [|x xs IH]; intros l R; cbn [convs Lout].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply IH|].
    unfold conv. rewrite Str_app_assoc.
    eapply evstep_trans; [apply L10'|].
    change ([0;1;0;1] *> Lout xs *> R) with ([0;1] *> ([0;1] *> Lout xs *> R)).
    eapply evstep_trans; [apply LB1'|].
    rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Lemma left_item_raw init y l r :
  l <* rconv init y <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> PH *> [1;1;1;1;1;1;1] *> Lout init *> S6^^y *> [0] *> r.
Proof.
  unfold rconv. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply LK'|].
  apply evstep_refl.
Qed.

Lemma Lout_Ms xs : [1] ++ Lout xs = Ms xs ++ [1].
Proof.
  induction xs as [|x xs IH]; [reflexivity|]. cbn [Lout Ms]. unfold Mb. rewrite <- !app_assoc.
  f_equal. f_equal. cbn [app]. f_equal. exact IH.
Qed.

(** * The law of one sweep on an item, and its leftward lemma *)

Definition law (init:list nat) (y:nat) : list nat :=
  match init with [] => [S y] | x0 :: mids => S x0 :: mids ++ [y] end.

Lemma Ms_app xs ys : Ms (xs ++ ys) = Ms xs ++ Ms ys.
Proof. induction xs as [|x xs IH]; cbn [Ms app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma law_list init y : [1;1;1;1;1;1;1] ++ Lout init ++ S6^^y ++ [0] = Ms (law init y).
Proof.
  destruct init as [|x0 mids]; cbn [law Lout Ms].
  - unfold Mb, S6. cbn [lpow]. rewrite !app_nil_r. reflexivity.
  - rewrite Ms_app. cbn [Ms]. unfold Mb. rewrite app_nil_r. cbn [lpow]. rewrite <- !app_assoc.
    assert (H1 : forall X, [1] ++ S6 ++ X = [1;1;1;1;1;1;1] ++ X) by reflexivity. rewrite H1.
    f_equal. f_equal. cbn [app]. f_equal.
    change (1 :: Lout mids ++ S6^^y ++ [0]) with (([1] ++ Lout mids) ++ S6^^y ++ [0]).
    rewrite Lout_Ms, <- app_assoc. reflexivity.
Qed.

Lemma left_item init y l r :
  l <* rconv init y <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> (PH ++ Ms (law init y)) *> r.
Proof.
  eapply evstep_trans; [apply left_item_raw|].
  rewrite <- law_list. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * A list of items *)

Fixpoint Items (its:list (list nat * nat)) : list Sym :=
  match its with [] => [] | (i,y)::its => enc_item i y ++ Items its end.
Fixpoint rconvs (its:list (list nat * nat)) : list Sym :=
  match its with [] => [] | (i,y)::its => rconvs its ++ rconv i y end.
Fixpoint Items' (xss:list (list nat)) : list Sym :=
  match xss with [] => [] | xs::xss => (PH ++ Ms xs) ++ Items' xss end.
Definition laws (its:list (list nat * nat)) : list (list nat) := map (fun '(i,y) => law i y) its.

Lemma right_items its : forall l r, l <* T8 {{B}}> Items its *> r -->* l <* rconvs its <* T8 {{B}}> r.
Proof.
  induction its as [|[i y] its IH]; intros l r; cbn [Items rconvs].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply right_item|].
    eapply evstep_trans; [apply (IH (l <* rconv i y))|].
    rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma left_items its : forall l r, l <* rconvs its <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> Items' (laws its) *> r.
Proof.
  induction its as [|[i y] its IH]; intros l r; cbn [rconvs Items' laws map].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply IH|].
    eapply evstep_trans; [apply left_item|].
    rewrite !Str_app_assoc. fold (laws its). apply evstep_refl.
Qed.

(** * The two ends *)

Definition Zc : list Sym := [1;0;1;0;1;0;1;0] ++ [1;1;1;1;1;1;1;1;1;1;1] ++ [0;1;1].
Definition ENDc : list Sym := PH ++ Mb 2 ++ Zc.

Lemma END0 l r :
  l <* [1;0;0;1;0;0] <* [1;0] {{B}}>
    [1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;0;1;1] *>
    [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0] *> r -->*
  l <{{C}} [0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;0;1;0;1;0;
            1;1;1;1;1;1;1;1;1;1;1;0;1;1;0;0;0;0;0;0;0] *> r.
Proof. es' & l r. Qed.

Lemma zeros_0inf k : [0]^^k *> 0inf = 0inf.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [lpow]. rewrite Str_app_assoc, IH. solve_const0_eq. Qed.

(* the turn at the right end: a new item P M(2) appears before END *)
Lemma END_turn' l r :
  l <* T8 {{B}}> ENDc *> [0]^^20 *> r -->* l <{{C}} [0;1;0] *> PH *> Mb 2 *> ENDc *> [0]^^7 *> r.
Proof. exact (END0 l r). Qed.
Lemma END_turn l : l <* T8 {{B}}> ENDc *> 0inf -->* l <{{C}} [0;1;0] *> PH *> Mb 2 *> ENDc *> 0inf.
Proof.
  pose proof (END_turn' l 0inf) as H. rewrite !zeros_0inf in H. exact H.
Qed.

Lemma DS_even0 m l r : l <* [0;0;0] <{{D}} [1;0;1;0]^^m *> r -->* l <* [0;1;0;1]^^m <* [1;0;1] {{B}}> r.
Proof. es' m & l r. Qed.
Lemma DS_odd0 m l r : l <* [0;0;0] <{{D}} [1;0] *> [1;0;1;0]^^m *> r -->* l <* [0;1;0;1]^^m <* [1;0;1;0;1] {{B}}> r.
Proof. es' m & l r. Qed.
Lemma LBlk m l r : l <* [0;1]^^m {{C}}> [1;0] *> r -->* l <{{D}} [1;0] *> [1;0]^^m *> r.
Proof. es' m & l r. Qed.

Section P_M269c.
Lemma pow2 {A} (a:list A) m : (a ++ a)^^m = a^^(m+m).
Proof.
  induction m as [|m IH]; [reflexivity|]. cbn [lpow]. rewrite IH.
  replace (S m + S m) with (S (S (m + m))) by lia. cbn [lpow]. rewrite app_assoc. reflexivity.
Qed.

Lemma z3 : 0inf = [0;0;0] *> 0inf.
Proof. solve_const0_eq. Qed.

Lemma blk_even m : [1;0]^^(2*m) = [1;0;1;0]^^m.
Proof. replace (2*m) with (m+m) by lia. rewrite <- pow2. reflexivity. Qed.
Lemma blk_odd m : [1;0]^^(2*m+1) = [1;0] ++ [1;0;1;0]^^m.
Proof. replace (2*m+1) with (S (m+m)) by lia. cbn [lpow]. rewrite <- pow2. reflexivity. Qed.
Lemma blk_rot m : [1;0]^^(m+m) ++ [1] = [1] ++ [0;1;0;1]^^m.
Proof.
  rewrite <- pow2. change ([1;0] ++ [1;0]) with (1::[0;1;0]).
  rewrite lpow_rotate_list, app_nil_r. reflexivity.
Qed.

Lemma DS_even m r : 0inf <{{D}} [1;0;1;0]^^m *> r -->* 0inf <* [0;1;0;1]^^m <* [1;0;1] {{B}}> r.
Proof. pose proof (DS_even0 m 0inf r) as H. rewrite <- z3 in H. exact H. Qed.
Lemma DS_odd m r : 0inf <{{D}} [1;0] *> [1;0;1;0]^^m *> r -->* 0inf <* [0;1;0;1]^^m <* [1;0;1;0;1] {{B}}> r.
Proof. pose proof (DS_odd0 m 0inf r) as H. rewrite <- z3 in H. exact H. Qed.

Lemma LE_even0 m l r : l <* [0;1;0;1]^^m <* [1;0;1] <{{C}} [0;1] *> r -->* l <{{D}} [1;0;1;0;1] *> [0;1;0;1]^^m *> r.
Proof. es' m & l r. Qed.
Lemma LE_odd0 m l r :
  l <* [0;1;0;1]^^m <* [1;0;1;0;1] <{{C}} [0;1] *> r -->* l <{{D}} [1;0;1;0;1;0;1] *> [0;1;0;1]^^m *> r.
Proof. es' m & l r. Qed.

Lemma LE_even m x R :
  0inf <* [0;1;0;1]^^m <* [1;0;1] <* B6^^x <{{C}} [0;1;0] *> R -->* 0inf <{{D}} [1;0]^^(S (S (2*m))) *> Mb x *> R.
Proof.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply LE_even0|].
  replace (2*m) with (m+m) by lia.
  assert (E : [1;0]^^(S (S (m+m))) ++ [1] = [1;0;1;0;1] ++ [0;1;0;1]^^m).
  { cbn [lpow]. rewrite <- !app_assoc, blk_rot. reflexivity. }
  unfold Mb. rewrite !Str_app_assoc. rewrite <- (Str_app_assoc ([1;0]^^(S (S (m+m)))) [1]).
  rewrite E, Str_app_assoc. apply evstep_refl.
Qed.
Lemma LE_odd m x R :
  0inf <* [0;1;0;1]^^m <* [1;0;1;0;1] <* B6^^x <{{C}} [0;1;0] *> R -->* 0inf <{{D}} [1;0]^^(S (S (2*m+1))) *> Mb x *> R.
Proof.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply LE_odd0|].
  replace (2*m+1) with (S (m+m)) by lia.
  assert (E : [1;0]^^(S (S (S (m+m)))) ++ [1] = [1;0;1;0;1;0;1] ++ [0;1;0;1]^^m).
  { cbn [lpow]. rewrite <- !app_assoc, blk_rot. reflexivity. }
  unfold Mb. rewrite !Str_app_assoc. rewrite <- (Str_app_assoc ([1;0]^^(S (S (S (m+m))))) [1]).
  rewrite E, Str_app_assoc. apply evstep_refl.
Qed.

(** * One collision-free sweep *)

(* the tape at a D-record: block (10)^n, the rest block M(r), the items, END *)
Definition record (n r:nat) (xss:list (list nat)) : Q * tape :=
  0inf <{{D}} [1;0]^^n *> Mb r *> Items' xss *> ENDc *> 0inf.

Lemma sweep_cf_raw n r1 its :
  0inf <{{D}} [1;0]^^n *> Mb (S r1) *> Items its *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^(S (S n)) *> Mb r1 *> Items' (laws its) *> PH *> Mb 2 *> ENDc *> 0inf.
Proof.
  assert (P : exists m, n = 2*m \/ n = 2*m+1).
  { induction n as [|n [m [H|H]]]; [exists O; lia|exists m; lia|exists (S m); lia]. }
  destruct P as [m [H|H]]; subst n.
  - rewrite blk_even.
    eapply evstep_trans; [apply DS_even|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply right_items|].
    eapply evstep_trans; [apply END_turn|].
    eapply evstep_trans; [apply left_items|].
    apply LE_even.
  - rewrite blk_odd, Str_app_assoc.
    eapply evstep_trans; [apply DS_odd|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply right_items|].
    eapply evstep_trans; [apply END_turn|].
    eapply evstep_trans; [apply left_items|].
    apply LE_odd.
Qed.
End P_M269c.

Section P_M269d.
(* rightward: the pending cells T8 ++ [1;0] of the seam item, the next item P M(2+b), and the header after it *)
Lemma SK_R0 b l r :
  l <* [1;0;0;1;0;0] <* [1;0] <* [1;0] {{B}}>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0] *> [1;1;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^b <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' b & l r. Qed.

(* leftward over the same cells; the seam lands as  M(1)  at the front of the item after next *)
Lemma SK_L0 b l r :
  l <* [1;0;1;1;0;0] <* [1;0;0;1;0;0]^^b <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0]
    <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0;1;1;1;0;1;1;1;1;1;1;1;0;1] *> r.
Proof. es' b & l r. Qed.

Definition W0 (b:nat) : list Sym := [1;0] ++ K12 ++ B6 ++ B6 ++ B6^^b ++ [1;0;1;1;0;0].

Lemma rotX b : [1;0] ++ [0;1;0;0;1;0]^^b = [1;0;0;1;0;0]^^b ++ [1;0].
Proof. symmetry. exact (lpow_rotate_list' [1;0] [0;1;0;0] b). Qed.

Lemma W0_eq b :
  [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ [0;1;0;0;1;0]^^b ++ [1;1;0;0] = W0 b.
Proof.
  unfold W0, K12, B6.
  change [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] with
    ([1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ [1;0]).
  rewrite <- app_assoc, (app_assoc [1;0] ([0;1;0;0;1;0]^^b)), rotX, <- !app_assoc. reflexivity.
Qed.

Lemma Mb2 b : Mb (2+b) = [1;1;1;1;1;1;1;1;1;1;1;1;1] ++ [1;1;1;1;1;1]^^b ++ [0].
Proof. reflexivity. Qed.

Lemma SK_R b l r : l <* T8 <* [1;0] {{B}}> PH *> Mb (2+b) *> PH *> r -->* l <* W0 b {{B}}> r.
Proof.
  rewrite Mb2. unfold T8, PH. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply SK_R0|]. rewrite <- W0_eq, !Str_app_assoc. apply evstep_refl.
Qed.

Lemma SK_L b l r :
  l <* W0 b <{{C}} [0;1] *> r -->* l <{{C}} [0;1;0] *> PH *> Mb (2+b) *> PH *> [1;1;1;1;1;1;1;0;1] *> r.
Proof.
  unfold W0, K12, B6. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply SK_L0|].
  rewrite Mb2. unfold PH. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * The skip as one unit: the seam item, the next item, and the item after next *)

Definition skip_in (init:list nat) (y b:nat) (init3:list nat) (y3:nat) : list Sym :=
  PH ++ Ms init ++ Mb (S y) ++ Mb 0 ++ PH ++ Mb (2+b) ++ PH ++ Ms init3 ++ Mb (S y3).
Definition skip_rc (init:list nat) (y b:nat) (init3:list nat) (y3:nat) : list Sym := B6^^y3 ++ convs init3 ++ W0 b ++ rconv init y.
Definition skip_out (init:list nat) (y b:nat) (init3:list nat) (y3:nat) : list Sym :=
  PH ++ Ms (law init y) ++ PH ++ Mb (2+b) ++ PH ++ Ms (1%nat :: init3 ++ [y3]).

Lemma skip_right init y b init3 y3 l r :
  l <* T8 {{B}}> skip_in init y b init3 y3 *> r -->* l <* skip_rc init y b init3 y3 <* T8 {{B}}> r.
Proof.
  unfold skip_in. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply PR|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply SK_R|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S.
  unfold skip_rc, rconv. rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma seam_list init3 y3 : [1;1;1;1;1;1;1;0;1] ++ Lout init3 ++ S6^^y3 ++ [0] = Ms (1%nat :: init3 ++ [y3]).
Proof.
  cbn [Ms]. rewrite Ms_app. cbn [Ms]. rewrite app_nil_r.
  change ([1;1;1;1;1;1;1;0;1] ++ Lout init3 ++ S6^^y3 ++ [0]) with (Mb 1 ++ ([1] ++ Lout init3) ++ S6^^y3 ++ [0]).
  rewrite Lout_Ms. unfold Mb at 3. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma skip_left init y b init3 y3 l r :
  l <* skip_rc init y b init3 y3 <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> skip_out init y b init3 y3 *> r.
Proof.
  unfold skip_rc. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply SK_L|].
  eapply evstep_trans; [apply left_item|].
  unfold skip_out. rewrite <- seam_list. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * The merge (a trailing marker merges the next two items Y, Y2 into [Y+6, 1] + own(Y2)) *)

Lemma MG_R0 a l r :
  l <* [1;0;0;1;0;0] <* [1;0] <* [1;0] <* [1;0] {{B}}>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *> [1;1;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^a <* [1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a & l r. Qed.

Lemma MG_L0 a l r :
  l <* [1;0;1;1;0;0] <* [1;0;0;1;0;0]^^a <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;0]
    <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0;1;0;1;1;1;1;1;1;1] *> r.
Proof. es' a & l r. Qed.

Definition W1 (a:nat) : list Sym := [1;0;0;1;0;0;1;0;1;0] ++ B6 ++ B6 ++ B6 ++ B6^^a ++ [1;0;1;1;0;0].

Lemma W1_eq a :
  [1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ [0;1;0;0;1;0]^^a ++ [1;1;0;0] = W1 a.
Proof.
  unfold W1, B6.
  change [1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] with
    ([1;0;0;1;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ [1;0]).
  rewrite <- app_assoc, (app_assoc [1;0] ([0;1;0;0;1;0]^^a)), rotX, <- !app_assoc. reflexivity.
Qed.

Lemma Mb3 a : Mb (3+a) = [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] ++ [1;1;1;1;1;1]^^a ++ [0].
Proof. reflexivity. Qed.

Lemma MG_R a l r : l <* T8 <* [1;0] <* [1;0] {{B}}> PH *> Mb (2+a) *> PH *> r -->* l <* W1 a {{B}}> r.
Proof.
  rewrite Mb2. unfold T8, PH. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply MG_R0|]. rewrite <- W1_eq, !Str_app_assoc. apply evstep_refl.
Qed.

Lemma MG_L a l r :
  l <* W1 a <{{C}} [0;1] *> r -->* l <{{C}} [0;1;0] *> PH *> Mb (3+a) *> Mb 0 *> [1;1;1;1;1;1;1] *> r.
Proof.
  unfold W1, B6. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply MG_L0|].
  rewrite Mb3. unfold PH, Mb. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Definition merge_in (init:list nat) (y a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms init ++ Mb (S y) ++ Mb 0 ++ Mb 0 ++ PH ++ Mb (2+a) ++ PH ++ Ms init2 ++ Mb (S y2).
Definition merge_rc (init:list nat) (y a:nat) (init2:list nat) (y2:nat) : list Sym :=
  B6^^y2 ++ convs init2 ++ W1 a ++ rconv init y.
Definition merge_out (init:list nat) (y a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms (law init y) ++ PH ++ Ms ((3+a)%nat :: 0%nat :: law init2 y2).

Lemma merge_right init y a init2 y2 l r :
  l <* T8 {{B}}> merge_in init y a init2 y2 *> r -->* l <* merge_rc init y a init2 y2 <* T8 {{B}}> r.
Proof.
  unfold merge_in. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply PR|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply MG_R|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S.
  unfold merge_rc, rconv. rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma merge_left init y a init2 y2 l r :
  l <* merge_rc init y a init2 y2 <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> merge_out init y a init2 y2 *> r.
Proof.
  unfold merge_rc. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply MG_L|].
  eapply evstep_trans; [apply left_item|].
  unfold merge_out. cbn [Ms]. rewrite <- (law_list init2 y2). rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * A seam that skips onto END lands in the new 13 before END: [7, 7] *)

Lemma SKE0 b l r :
  l <* [1;0;0;1;0;0] <* [1;0] <* [1;0] {{B}}>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0] *>
    [1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;0;1;1] *>
    [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0] *> r -->*
  l <{{C}} [0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *>
    [0;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;0;1;0;1;0;
     1;1;1;1;1;1;1;1;1;1;1;0;1;1;0;0;0;0;0;0;0] *> r.
Proof. es' b & l r. Qed.

Lemma SKE b l r :
  l <* T8 <* [1;0] {{B}}> PH *> Mb (2+b) *> ENDc *> [0]^^20 *> r -->*
  l <{{C}} [0;1;0] *> PH *> Mb (2+b) *> PH *> Mb 1 *> Mb 1 *> ENDc *> [0]^^7 *> r.
Proof.
  rewrite Mb2. unfold T8. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply SKE0|].
  apply evstep_refl.
Qed.

Lemma SKE' b l :
  l <* T8 <* [1;0] {{B}}> PH *> Mb (2+b) *> ENDc *> 0inf -->*
  l <{{C}} [0;1;0] *> PH *> Mb (2+b) *> PH *> Mb 1 *> Mb 1 *> ENDc *> 0inf.
Proof. pose proof (SKE b l 0inf) as H. rewrite !zeros_0inf in H. exact H. Qed.

(** * Collision C1: a seam lands in an item that a marker is merging: no merge, Y -> [0;0;Y], the seam moves on *)

Lemma C1_R0 b a l r :
  l <* [1;0;0;1;0;0] <* [1;0] <* [1;0] {{B}}>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0] *> [1;0] *> [1;0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *> [1;1;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^b <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a
    <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' b a & l r. Qed.

Lemma C1_L0 b a l r :
  l <* [1;0;1;1;0;0] <* [1;0;0;1;0;0]^^b <* [1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] <* [1;0;0;1;0;0]^^a
    <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1;0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *>
    [0;1;1;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0;1;1;1;0;1;1;1;1;1;1;1;0;1] *> r.
Proof. es' b a & l r. Qed.

Definition W2 (b a:nat) : list Sym :=
  [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ B6^^a ++
  [1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ B6^^b ++ [1;0;1;1;0;0].

Lemma W2_eq b a :
  [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ [0;1;0;0;1;0]^^a ++
  [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ [0;1;0;0;1;0]^^b ++ [1;1;0;0] = W2 b a.
Proof.
  unfold W2, B6.
  change [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] with
    ([1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ [1;0]).
  change [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] with ([1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0] ++ [1;0]).
  rewrite <- !app_assoc.
  rewrite (app_assoc [1;0] ([0;1;0;0;1;0]^^a)), rotX.
  rewrite (app_assoc [1;0] ([0;1;0;0;1;0]^^b)), rotX.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma C1_R b a l r :
  l <* T8 <* [1;0] {{B}}> PH *> Mb (2+b) *> Mb 0 *> Mb 0 *> PH *> Mb (2+a) *> PH *> r -->* l <* W2 b a {{B}}> r.
Proof.
  rewrite !Mb2. unfold T8, PH, Mb. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply C1_R0|]. rewrite <- W2_eq, !Str_app_assoc. apply evstep_refl.
Qed.

Lemma C1_L b a l r :
  l <* W2 b a <{{C}} [0;1] *> r -->*
  l <{{C}} [0;1;0] *> PH *> Mb (2+b) *> PH *> Mb 0 *> Mb 0 *> Mb (2+a) *> PH *> [1;1;1;1;1;1;1;0;1] *> r.
Proof.
  unfold W2, B6. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply C1_L0|].
  rewrite !Mb2. unfold PH, Mb. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Definition c1_in (init:list nat) (y b a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms init ++ Mb (S y) ++ Mb 0 ++ PH ++ Mb (2+b) ++ Mb 0 ++ Mb 0 ++ PH ++ Mb (2+a) ++ PH ++ Ms init2 ++ Mb (S y2).
Definition c1_rc (init:list nat) (y b a:nat) (init2:list nat) (y2:nat) : list Sym :=
  B6^^y2 ++ convs init2 ++ W2 b a ++ rconv init y.
Definition c1_out (init:list nat) (y b a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms (law init y) ++ PH ++ Mb (2+b) ++ PH ++ Ms [0%nat; 0%nat; (2+a)%nat] ++ PH ++ Ms (1%nat :: init2 ++ [y2]).

Lemma c1_right init y b a init2 y2 l r :
  l <* T8 {{B}}> c1_in init y b a init2 y2 *> r -->* l <* c1_rc init y b a init2 y2 <* T8 {{B}}> r.
Proof.
  unfold c1_in. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply PR|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply C1_R|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S.
  unfold c1_rc, rconv. rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma c1_left init y b a init2 y2 l r :
  l <* c1_rc init y b a init2 y2 <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> c1_out init y b a init2 y2 *> r.
Proof.
  unfold c1_rc. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply C1_L|].
  eapply evstep_trans; [apply left_item|].
  unfold c1_out. rewrite <- seam_list. cbn [Ms]. rewrite app_nil_r, !Str_app_assoc. apply evstep_refl.
Qed.
End P_M269d.

Section P_M269e.
(** * A seam that lands in a marker item whose marker merges the next two items *)

Definition sm_in (init:list nat) (y b:nat) (init3:list nat) (y3 a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms init ++ Mb (S y) ++ Mb 0 ++ PH ++ Mb (2+b) ++
  PH ++ Ms init3 ++ Mb (S y3) ++ Mb 0 ++ Mb 0 ++ PH ++ Mb (2+a) ++ PH ++ Ms init2 ++ Mb (S y2).
Definition sm_rc (init:list nat) (y b:nat) (init3:list nat) (y3 a:nat) (init2:list nat) (y2:nat) : list Sym :=
  B6^^y2 ++ convs init2 ++ W1 a ++ B6^^y3 ++ convs init3 ++ W0 b ++ rconv init y.
Definition sm_out (init:list nat) (y b:nat) (init3:list nat) (y3 a:nat) (init2:list nat) (y2:nat) : list Sym :=
  PH ++ Ms (law init y) ++ PH ++ Mb (2+b) ++ PH ++ Ms (1%nat :: init3 ++ [y3]) ++
  PH ++ Ms ((3+a)%nat :: 0%nat :: law init2 y2).

Lemma sm_right init y b init3 y3 a init2 y2 l r :
  l <* T8 {{B}}> sm_in init y b init3 y3 a init2 y2 *> r -->* l <* sm_rc init y b init3 y3 a init2 y2 <* T8 {{B}}> r.
Proof.
  unfold sm_in. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply PR|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply SK_R|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply MG_R|].
  eapply evstep_trans; [apply MRs|].
  eapply evstep_trans; [apply MR|]. rewrite conv_S.
  unfold sm_rc, rconv. rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma sm_left init y b init3 y3 a init2 y2 l r :
  l <* sm_rc init y b init3 y3 a init2 y2 <{{C}} [0;1;0] *> r -->*
  l <{{C}} [0;1;0] *> sm_out init y b init3 y3 a init2 y2 *> r.
Proof.
  unfold sm_rc. rewrite !Str_app_assoc.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply MG_L|].
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply SK_L|].
  eapply evstep_trans; [apply left_item|].
  unfold sm_out. rewrite <- seam_list. cbn [Ms]. rewrite <- (law_list init2 y2). rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Inductive unit : Type :=
| Uitem (init:list nat) (y:nat)                                   (* P Ms(init) M(S y) *)
| Uskip (init:list nat) (y b:nat) (init3:list nat) (y3:nat)       (* seam item, P M(2+b), target item *)
| Umerge (init:list nat) (y a:nat) (init2:list nat) (y2:nat)      (* marker item, Y = P M(2+a), Y2 *)
| Usm (init:list nat) (y b:nat) (init3:list nat) (y3 a:nat) (init2:list nat) (y2:nat)  (* skip into a marker item *)
| Uc1 (init:list nat) (y b a:nat) (init2:list nat) (y2:nat).     (* collision C1 *)

Definition u_in (u:unit) : list Sym :=
  match u with
  | Uitem i y => enc_item i y
  | Uskip i y b i3 y3 => skip_in i y b i3 y3
  | Umerge i y a i2 y2 => merge_in i y a i2 y2
  | Usm i y b i3 y3 a i2 y2 => sm_in i y b i3 y3 a i2 y2
  | Uc1 i y b a i2 y2 => c1_in i y b a i2 y2
  end.
Definition u_rc (u:unit) : list Sym :=
  match u with
  | Uitem i y => rconv i y
  | Uskip i y b i3 y3 => skip_rc i y b i3 y3
  | Umerge i y a i2 y2 => merge_rc i y a i2 y2
  | Usm i y b i3 y3 a i2 y2 => sm_rc i y b i3 y3 a i2 y2
  | Uc1 i y b a i2 y2 => c1_rc i y b a i2 y2
  end.
Definition u_out (u:unit) : list Sym :=
  match u with
  | Uitem i y => PH ++ Ms (law i y)
  | Uskip i y b i3 y3 => skip_out i y b i3 y3
  | Umerge i y a i2 y2 => merge_out i y a i2 y2
  | Usm i y b i3 y3 a i2 y2 => sm_out i y b i3 y3 a i2 y2
  | Uc1 i y b a i2 y2 => c1_out i y b a i2 y2
  end.

Lemma u_right u l r : l <* T8 {{B}}> u_in u *> r -->* l <* u_rc u <* T8 {{B}}> r.
Proof. destruct u; [apply right_item|apply skip_right|apply merge_right|apply sm_right|apply c1_right]. Qed.
Lemma u_left u l r : l <* u_rc u <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> u_out u *> r.
Proof. destruct u; [apply left_item|apply skip_left|apply merge_left|apply sm_left|apply c1_left]. Qed.

Fixpoint us_in (us:list unit) : list Sym := match us with [] => [] | u :: us => u_in u ++ us_in us end.
Fixpoint us_rc (us:list unit) : list Sym := match us with [] => [] | u :: us => us_rc us ++ u_rc u end.
Fixpoint us_out (us:list unit) : list Sym := match us with [] => [] | u :: us => u_out u ++ us_out us end.

Lemma us_right us : forall l r, l <* T8 {{B}}> us_in us *> r -->* l <* us_rc us <* T8 {{B}}> r.
Proof.
  induction us as [|u us IH]; intros l r; cbn [us_in us_rc].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply u_right|].
    eapply evstep_trans; [apply (IH (l <* u_rc u))|].
    rewrite <- !Str_app_assoc, <- !app_assoc. apply evstep_refl.
Qed.

Lemma us_left us : forall l r, l <* us_rc us <{{C}} [0;1;0] *> r -->* l <{{C}} [0;1;0] *> us_out us *> r.
Proof.
  induction us as [|u us IH]; intros l r; cbn [us_rc us_out].
  - apply evstep_refl.
  - rewrite Str_app_assoc. eapply evstep_trans; [apply IH|].
    eapply evstep_trans; [apply u_left|].
    rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * The right end *)

Inductive tail : Type := Tstd | Tskip (init:list nat) (y b:nat).   (* Tskip: a seam skips onto END *)

Definition t_in (t:tail) : list Sym :=
  match t with Tstd => [] | Tskip i y b => enc_item i y ++ Mb 0 ++ PH ++ Mb (2+b) end.
Definition t_out (t:tail) : list Sym :=
  match t with
  | Tstd => PH ++ Mb 2
  | Tskip i y b => PH ++ Ms (law i y) ++ PH ++ Mb (2+b) ++ PH ++ Mb 1 ++ Mb 1
  end.

Lemma t_turn t l : l <* T8 {{B}}> t_in t *> ENDc *> 0inf -->* l <{{C}} [0;1;0] *> t_out t *> ENDc *> 0inf.
Proof.
  destruct t as [|i y b]; cbn [t_in t_out].
  - eapply evstep_trans; [apply END_turn|]. rewrite Str_app_assoc. apply evstep_refl.
  - rewrite !Str_app_assoc.
    eapply evstep_trans; [apply right_item|].
    eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
    eapply evstep_trans; [apply SKE'|].
    eapply evstep_trans; [apply left_item|].
    rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * The left end with a rest block R of several blocks *)

Lemma LE_even' m initR x R :
  0inf <* [0;1;0;1]^^m <* [1;0;1] <* convs initR <* B6^^x <{{C}} [0;1;0] *> R -->*
  0inf <{{D}} [1;0]^^(S (S (2*m))) *> Ms (initR ++ [x]) *> R.
Proof.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply LE_even0|].
  replace (2*m) with (m+m) by lia.
  assert (E : [1;0]^^(S (S (m+m))) ++ Ms (initR ++ [x]) =
              [1;0;1;0;1] ++ [0;1;0;1]^^m ++ Lout initR ++ [1;1;1;1;1;1]^^x ++ [0]).
  { rewrite Ms_app. cbn [Ms]. rewrite app_nil_r. unfold Mb.
    rewrite (app_assoc (Ms initR) [1]), <- Lout_Ms.
    cbn [lpow]. rewrite <- !app_assoc. rewrite (app_assoc ([1;0]^^(m+m)) [1]), blk_rot. reflexivity. }
  rewrite <- (Str_app_assoc ([1;0]^^(S (S (m+m)))) (Ms (initR ++ [x]))), E, !Str_app_assoc.
  apply evstep_refl.
Qed.

Lemma LE_odd' m initR x R :
  0inf <* [0;1;0;1]^^m <* [1;0;1;0;1] <* convs initR <* B6^^x <{{C}} [0;1;0] *> R -->*
  0inf <{{D}} [1;0]^^(S (S (2*m+1))) *> Ms (initR ++ [x]) *> R.
Proof.
  eapply evstep_trans; [apply LB0'|].
  eapply evstep_trans; [apply Lconvs|].
  eapply evstep_trans; [apply LE_odd0|].
  replace (2*m+1) with (S (m+m)) by lia.
  assert (E : [1;0]^^(S (S (S (m+m)))) ++ Ms (initR ++ [x]) =
              [1;0;1;0;1;0;1] ++ [0;1;0;1]^^m ++ Lout initR ++ [1;1;1;1;1;1]^^x ++ [0]).
  { rewrite Ms_app. cbn [Ms]. rewrite app_nil_r. unfold Mb.
    rewrite (app_assoc (Ms initR) [1]), <- Lout_Ms.
    cbn [lpow]. rewrite <- !app_assoc. rewrite (app_assoc ([1;0]^^(m+m)) [1]), blk_rot. reflexivity. }
  rewrite <- (Str_app_assoc ([1;0]^^(S (S (S (m+m))))) (Ms (initR ++ [x]))), E, !Str_app_assoc.
  apply evstep_refl.
Qed.

(** * One sweep *)

Theorem sweep n initR r1 us t :
  0inf <{{D}} [1;0]^^n *> Ms (initR ++ [S r1]) *> us_in us *> t_in t *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^(S (S n)) *> Ms (initR ++ [r1]) *> us_out us *> t_out t *> ENDc *> 0inf.
Proof.
  assert (P : exists m, n = 2*m \/ n = 2*m+1).
  { induction n as [|n [m [H|H]]]; [exists O; lia|exists m; lia|exists (S m); lia]. }
  destruct P as [m [H|H]]; subst n.
  - rewrite blk_even.
    eapply evstep_trans; [apply DS_even|].
    rewrite Ms_app. cbn [Ms]. rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply us_right|].
    eapply evstep_trans; [apply t_turn|].
    eapply evstep_trans; [apply us_left|].
    apply LE_even'.
  - rewrite blk_odd, Str_app_assoc.
    eapply evstep_trans; [apply DS_odd|].
    rewrite Ms_app. cbn [Ms]. rewrite app_nil_r, Str_app_assoc.
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply us_right|].
    eapply evstep_trans; [apply t_turn|].
    eapply evstep_trans; [apply us_left|].
    apply LE_odd'.
Qed.

(** * A sweep in which the trailing marker of R merges the first two items *)

Theorem sweep_Rmerge n initR y a init2 y2 us t :
  0inf <{{D}} [1;0]^^n *> Ms (initR ++ [S y; 0%nat; 0%nat]) *> (PH ++ Mb (2+a) ++ PH ++ Ms init2 ++ Mb (S y2)) *>
    us_in us *> t_in t *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^(S (S n)) *> Ms (initR ++ [y]) *> (PH ++ Ms ((3+a)%nat :: 0%nat :: law init2 y2)) *>
    us_out us *> t_out t *> ENDc *> 0inf.
Proof.
  cbn [Ms]. rewrite <- (law_list init2 y2). rewrite Ms_app. cbn [Ms]. rewrite app_nil_r, !Str_app_assoc.
  assert (P : exists m, n = 2*m \/ n = 2*m+1).
  { induction n as [|n [m [H|H]]]; [exists O; lia|exists m; lia|exists (S m); lia]. }
  destruct P as [m [H|H]]; subst n.
  - rewrite blk_even.
    eapply evstep_trans; [apply DS_even|].
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
    eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
    eapply evstep_trans; [apply MG_R|].
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply us_right|].
    eapply evstep_trans; [apply t_turn|].
    eapply evstep_trans; [apply us_left|].
    eapply evstep_trans; [apply LB0'|].
    eapply evstep_trans; [apply Lconvs|].
    eapply evstep_trans; [apply MG_L|].
    apply LE_even'.
  - rewrite blk_odd, Str_app_assoc.
    eapply evstep_trans; [apply DS_odd|].
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
    eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
    eapply evstep_trans; [apply MG_R|].
    eapply evstep_trans; [apply MRs|].
    eapply evstep_trans; [apply MR|]. rewrite conv_S, Str_app_assoc.
    eapply evstep_trans; [apply us_right|].
    eapply evstep_trans; [apply t_turn|].
    eapply evstep_trans; [apply us_left|].
    eapply evstep_trans; [apply LB0'|].
    eapply evstep_trans; [apply Lconvs|].
    eapply evstep_trans; [apply MG_L|].
    apply LE_odd'.
Qed.
End P_M269e.

Section P_M269f.
Lemma RF_R0 k a c l r :
  l <* [0;0;0;0;0;0;0;0] <{{D}} [1;0;1;0;1;0]^^k *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r -->*
  l <* [1;0;0;0] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' k a c & l r. Qed.
Lemma RF_R1 k a c l r :
  l <* [0;0;0;0;0;0;0;0] <{{D}} [1;0;1;0;1;0]^^k *> [1;0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r -->*
  l <* [1;0;0;0] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' k a c & l r. Qed.
Lemma RF_R2 k a c l r :
  l <* [0;0;0;0;0;0;0;0] <{{D}} [1;0;1;0;1;0]^^k *> [1;0;1;0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r -->*
  l <* [1;0;0;0] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' k a c & l r. Qed.

Lemma RF_L0 k a c l r :
  l <* [1] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c
    <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <{{D}} [1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^k *> [1;1;1;1;1;1]^^a *>
    [0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r.
Proof. es' k a c & l r. Qed.
Lemma RF_L1 k a c l r :
  l <* [1] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <{{D}} [1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^k *> [1;1;1;1;1;1]^^a *>
    [0;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r.
Proof. es' k a c & l r. Qed.
Lemma RF_L2 k a c l r :
  l <* [1] <* [0;1;0;0;1;0]^^k <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <{{D}} [1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^k *> [1;1;1;1;1;1]^^a *>
    [0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r.
Proof. es' k a c & l r. Qed.

Definition X6 : list Sym := [0;1;0;0;1;0].
Definition Rc0 k a c : list Sym :=
  [1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ X6^^c ++ [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ X6^^a ++ X6^^k ++ [1].
Definition Rc1 k a c : list Sym :=
  [1;0;0;1;0;0;1;0] ++ X6^^c ++ [1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ X6^^a ++ X6^^k ++ [1].
Definition Rc2 k a c : list Sym :=
  [1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ X6^^c ++ [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] ++ X6^^a ++ X6^^k ++ [1].

Lemma z8 : 0inf = [0;0;0;0;0;0;0;0] *> 0inf.
Proof. solve_const0_eq. Qed.

Lemma blk3 k : [1;0]^^(3*k) = [1;0;1;0;1;0]^^k.
Proof. replace (3*k) with (k*3) by lia. rewrite lpow_mul. reflexivity. Qed.
Lemma blk3_1 k : [1;0]^^(3*k+1) = [1;0;1;0;1;0]^^k ++ [1;0].
Proof. rewrite lpow_add, blk3. reflexivity. Qed.
Lemma blk3_2 k : [1;0]^^(3*k+2) = [1;0;1;0;1;0]^^k ++ [1;0;1;0].
Proof. rewrite lpow_add, blk3. reflexivity. Qed.

Lemma Mb1 c : Mb (1+c) = [1;1;1;1;1;1;1] ++ [1;1;1;1;1;1]^^c ++ [0].
Proof. reflexivity. Qed.
Lemma Mb_ka k a : Mb (2+k+a) = [1;1;1;1;1;1;1;1;1;1;1;1;1] ++ [1;1;1;1;1;1]^^k ++ [1;1;1;1;1;1]^^a ++ [0].
Proof. unfold Mb. replace (2+k+a) with (S (S (k+a))) by lia. cbn [lpow]. rewrite lpow_add, <- !app_assoc. reflexivity. Qed.
Lemma Mb_ka3 k a :
  Mb (3+k+a) = [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] ++ [1;1;1;1;1;1]^^k ++ [1;1;1;1;1;1]^^a ++ [0].
Proof. unfold Mb. replace (3+k+a) with (S (S (S (k+a)))) by lia. cbn [lpow]. rewrite lpow_add, <- !app_assoc. reflexivity. Qed.

Ltac rf_right H :=
  rewrite <- z8 in H; rewrite !Mb2; unfold PH; rewrite !Str_app_assoc;
  eapply evstep_trans; [exact H|]; unfold Rc0, Rc1, Rc2, T8, X6; rewrite !Str_app_assoc; apply evstep_refl.

Lemma RF0 k a c r :
  0inf <{{D}} [1;0;1;0;1;0]^^k *> PH *> Mb (2+a) *> PH *> Mb (2+c) *> r -->* 0inf <* [0;0;0] <* Rc0 k a c <* T8 {{B}}> r.
Proof. pose proof (RF_R0 k a c 0inf r) as H. rf_right H. Qed.
Lemma RF1 k a c r :
  0inf <{{D}} [1;0;1;0;1;0]^^k *> [1;0] *> PH *> Mb (2+a) *> PH *> Mb (2+c) *> r -->*
  0inf <* [0;0;0] <* Rc1 k a c <* T8 {{B}}> r.
Proof. pose proof (RF_R1 k a c 0inf r) as H. rf_right H. Qed.
Lemma RF2 k a c r :
  0inf <{{D}} [1;0;1;0;1;0]^^k *> [1;0;1;0] *> PH *> Mb (2+a) *> PH *> Mb (2+c) *> r -->*
  0inf <* [0;0;0] <* Rc2 k a c <* T8 {{B}}> r.
Proof. pose proof (RF_R2 k a c 0inf r) as H. rf_right H. Qed.

Lemma LF0 k a c l r : l <* Rc0 k a c <{{C}} [0;1;0] *> r -->* l <{{D}} [1;0]^^2 *> Mb (2+k+a) *> PH *> Mb (2+c) *> r.
Proof.
  unfold Rc0, X6. rewrite !Str_app_assoc. eapply evstep_trans; [apply RF_L0|].
  rewrite Mb_ka, Mb2. unfold PH. rewrite !Str_app_assoc. apply evstep_refl.
Qed.
Lemma LF1 k a c l r :
  l <* Rc1 k a c <{{C}} [0;1;0] *> r -->* l <{{D}} [1;0]^^2 *> Mb (2+k+a) *> PH *> Mb 1 *> Mb (1+c) *> r.
Proof.
  unfold Rc1, X6. rewrite !Str_app_assoc. eapply evstep_trans; [apply RF_L1|].
  rewrite Mb_ka, (Mb1 c). unfold PH. rewrite !Str_app_assoc. apply evstep_refl.
Qed.
Lemma LF2 k a c l r :
  l <* Rc2 k a c <{{C}} [0;1;0] *> r -->* l <{{D}} [1;0]^^2 *> Mb (3+k+a) *> Mb 0 *> Mb (2+c) *> r.
Proof.
  unfold Rc2, X6. rewrite !Str_app_assoc. eapply evstep_trans; [apply RF_L2|].
  rewrite Mb_ka3, Mb2. unfold Mb at 1. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * The three refill sweeps *)

Theorem sweep_refill0 k a c us t :
  0inf <{{D}} [1;0]^^(3*k) *> (PH ++ Mb (2+a) ++ PH ++ Mb (2+c)) *> us_in us *> t_in t *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^2 *> Mb (2+k+a) *> (PH ++ Mb (2+c)) *> us_out us *> t_out t *> ENDc *> 0inf.
Proof.
  rewrite blk3, !Str_app_assoc.
  eapply evstep_trans; [apply RF0|].
  eapply evstep_trans; [apply us_right|].
  eapply evstep_trans; [apply t_turn|].
  eapply evstep_trans; [apply us_left|].
  eapply evstep_trans; [apply LF0|].
  rewrite <- z3. apply evstep_refl.
Qed.

Theorem sweep_refill1 k a c us t :
  0inf <{{D}} [1;0]^^(3*k+1) *> (PH ++ Mb (2+a) ++ PH ++ Mb (2+c)) *> us_in us *> t_in t *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^2 *> Mb (2+k+a) *> (PH ++ Mb 1 ++ Mb (1+c)) *> us_out us *> t_out t *> ENDc *> 0inf.
Proof.
  rewrite blk3_1, !Str_app_assoc.
  eapply evstep_trans; [apply RF1|].
  eapply evstep_trans; [apply us_right|].
  eapply evstep_trans; [apply t_turn|].
  eapply evstep_trans; [apply us_left|].
  eapply evstep_trans; [apply LF1|].
  rewrite <- z3. apply evstep_refl.
Qed.

Theorem sweep_refill2 k a c us t :
  0inf <{{D}} [1;0]^^(3*k+2) *> (PH ++ Mb (2+a) ++ PH ++ Mb (2+c)) *> us_in us *> t_in t *> ENDc *> 0inf -->*
  0inf <{{D}} [1;0]^^2 *> Ms [(3+k+a)%nat; 0%nat; (2+c)%nat] *> us_out us *> t_out t *> ENDc *> 0inf.
Proof.
  rewrite blk3_2, !Str_app_assoc.
  eapply evstep_trans; [apply RF2|].
  eapply evstep_trans; [apply us_right|].
  eapply evstep_trans; [apply t_turn|].
  eapply evstep_trans; [apply us_left|].
  eapply evstep_trans; [apply LF2|].
  rewrite <- z3. cbn [Ms]. rewrite app_nil_r, !Str_app_assoc. apply evstep_refl.
Qed.
End P_M269f.

Section P_M269g.
(** * Items with binary block sizes *)

(* SP x c: c plain items P M(x); SD bs: one item P Ms(bs) *)
Inductive seg : Type := SP (x c : N) | SD (bs : list N).

Definition tn (xs : list N) : list nat := map N.to_nat xs.
Definition itm (bs : list N) : list Sym := PH ++ Ms (tn bs).
Fixpoint rep (n : nat) (w : list Sym) : list Sym := match n with O => [] | S n => w ++ rep n w end.
Definition flat1 (s : seg) : list Sym := match s with SP x c => rep (N.to_nat c) (itm [x]) | SD bs => itm bs end.
Fixpoint flat (ss : list seg) : list Sym := match ss with [] => [] | s :: ss => flat1 s ++ flat ss end.

Record st : Type := mk { blk : N; rst : list N; its : list seg }.
Definition cfg (s : st) : Q * tape :=
  0inf <{{D}} [1;0]^^(N.to_nat (blk s)) *> Ms (tn (rst s)) *> flat (its s) *> ENDc *> 0inf.

Local Open Scope N_scope.

Fixpoint unsnoc (xs : list N) : option (list N * N) :=
  match xs with
  | [] => None
  | [x] => Some ([], x)
  | x :: xs' => match unsnoc xs' with Some (i, z) => Some (x :: i, z) | None => None end
  end.

(* the end of an item: no unit (last block >= 1), a seam (.., w, 0), a marker (.., v, 0, 0) *)
Inductive kind : Type := Kn (i : list N) (z : N) | Ks (i : list N) (w : N) | Km (i : list N) (v : N) | Kbad.
Definition kindof (bs : list N) : kind :=
  match unsnoc bs with
  | Some (i, z) =>
      if 0 <? z then Kn i z else
      match unsnoc i with
      | Some (i', w) =>
          if 0 <? w then Ks i' w else
          match unsnoc i' with Some (i'', v) => if 0 <? v then Km i'' v else Kbad | None => Kbad end
      | None => Kbad
      end
  | None => Kbad
  end.

Definition lawN (i : list N) (z : N) : list N := match i with [] => [z] | x0 :: mids => (x0 + 1) :: mids ++ [z - 1] end.
Definition pl (bs : list N) : seg := match bs with [x] => SP x 1 | _ => SD bs end.

Definition take_item (ss : list seg) : option (list N * list seg) :=
  match ss with
  | SP x c :: ss' => if 1 <? c then Some ([x], SP x (c - 1) :: ss') else if c =? 1 then Some ([x], ss') else None
  | SD bs :: ss' => Some (bs, ss')
  | [] => None
  end.
Definition take_plain (ss : list seg) : option (N * list seg) :=
  match take_item ss with Some ([x], ss') => Some (x, ss') | _ => None end.
(* an item whose last block is >= 1 *)
Definition take_n (ss : list seg) : option (list N * N * list seg) :=
  match take_item ss with
  | Some (bs, ss') => match kindof bs with Kn i z => Some (i, z, ss') | _ => None end
  | None => None
  end.

(** * One sweep over the items (END implicit at the right) *)

Fixpoint sw (fuel : nat) (ss : list seg) : option (list seg) :=
  match fuel with O => None | S f =>
  match ss with
  | [] => Some [SP 2 1]
  | SP x c :: ss' => if (1 <=? x) && (1 <=? c) then option_map (cons (SP x c)) (sw f ss') else None
  | SD bs :: ss' =>
    match kindof bs with
    | Kn i z => option_map (cons (pl (lawN i z))) (sw f ss')
    | Ks i w =>
      match take_item ss' with
      | Some ([x2], ss2) =>
        if 2 <=? x2 then
          match ss2 with
          | [] => Some [pl (lawN i w); SP x2 1; SD [1; 1]]
          | _ =>
            match take_item ss2 with
            | Some (b3, ss3) =>
              match kindof b3 with
              | Kn i3 z3 => option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD (1 :: i3 ++ [z3 - 1]) :: r) (sw f ss3)
              | Km i3 v3 =>
                match take_plain ss3 with
                | Some (xa, ss4) =>
                  if 2 <=? xa then
                    match take_n ss4 with
                    | Some (i5, z5, ss5) =>
                      option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD (1 :: i3 ++ [v3 - 1]) ::
                                           SD ((xa + 1) :: 0 :: lawN i5 z5) :: r) (sw f ss5)
                    | None => None
                    end
                  else None
                | None => None
                end
              | _ => None
              end
            | None => None
            end
          end
        else None
      | Some (b2, ss2) =>
        match kindof b2 with
        | Km [] x2 =>
          if 2 <=? x2 then
            match take_plain ss2 with
            | Some (xa, ss3) =>
              if 2 <=? xa then
                match take_n ss3 with
                | Some (i4, z4, ss4) =>
                  option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD [0; 0; xa] :: SD (1 :: i4 ++ [z4 - 1]) :: r) (sw f ss4)
                | None => None
                end
              else None
            | None => None
            end
          else None
        | _ => None
        end
      | None => None
      end
    | Km i v =>
      match take_plain ss' with
      | Some (xa, ss2) =>
        if 2 <=? xa then
          match take_n ss2 with
          | Some (i2, z2, ss3) => option_map (fun r => pl (lawN i v) :: SD ((xa + 1) :: 0 :: lawN i2 z2) :: r) (sw f ss3)
          | None => None
          end
        else None
      | None => None
      end
    | Kbad => None
    end
  end end.

(* merge equal neighbouring plain groups *)
Fixpoint canon (ss : list seg) : list seg :=
  match ss with
  | SP x c :: ss' =>
    match canon ss' with
    | SP x' c' :: r => if x =? x' then SP x (c + c') :: r else SP x c :: SP x' c' :: r
    | r => SP x c :: r
    end
  | s :: ss' => s :: canon ss'
  | [] => []
  end.

Definition fuel_of (ss : list seg) : nat := S (length ss).

(** * One sweep of the whole tape *)

Definition step (s : st) : option st :=
  let n := blk s in
  match rst s with
  | [] =>
    match take_plain (its s) with
    | Some (x1, ss1) =>
      match take_plain ss1 with
      | Some (x2, ss2) =>
        if (2 <=? x1) && (2 <=? x2) then
          match sw (fuel_of ss2) ss2 with
          | Some r =>
            let k := n / 3 in
            match n mod 3 with
            | 0 => Some (mk 2 [x1 + k] (canon (SP x2 1 :: r)))
            | 1 => Some (mk 2 [x1 + k] (canon (SD [1; x2 - 1] :: r)))
            | _ => Some (mk 2 [x1 + k + 1; 0; x2] (canon r))
            end
          | None => None
          end
        else None
      | None => None
      end
    | None => None
    end
  | Rr =>
    match kindof Rr with
    | Kn iR zR =>
      match sw (fuel_of (its s)) (its s) with
      | Some r => Some (if (zR =? 1) && (match iR with [] => true | _ => false end)
                        then mk (n + 3) [] (canon r) else mk (n + 2) (iR ++ [zR - 1]) (canon r))
      | None => None
      end
    | Km iR vR =>
      match take_plain (its s) with
      | Some (xa, ss2) =>
        if 2 <=? xa then
          match take_n ss2 with
          | Some (i2, z2, ss3) =>
            match sw (fuel_of ss3) ss3 with
            | Some r => Some (mk (n + 2) (iR ++ [vR - 1]) (canon (SD ((xa + 1) :: 0 :: lawN i2 z2) :: r)))
            | None => None
            end
          | None => None
          end
        else None
      | None => None
      end
    | _ => None
    end
  end.
End P_M269g.

Section P_M269h.
Lemma flat_app a b : flat (a ++ b) = flat a ++ flat b.
Proof. induction a as [|s a IH]; cbn [flat app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma tn_app a b : tn (a ++ b) = tn a ++ tn b.
Proof. apply map_app. Qed.

Lemma unsnoc_spec xs : forall i z, unsnoc xs = Some (i, z) -> xs = i ++ [z].
Proof.
  induction xs as [|x xs IH]; intros i z H; [discriminate|].
  destruct xs as [|x' xs'].
  - cbn in H. injection H as <- <-. reflexivity.
  - change (unsnoc (x :: x' :: xs')) with
      (match unsnoc (x' :: xs') with Some (i, z) => Some (x :: i, z) | None => None end) in H.
    destruct (unsnoc (x' :: xs')) as [[i0 z0]|] eqn:E; [|discriminate].
    injection H as <- <-. rewrite (IH i0 z0 eq_refl). reflexivity.
Qed.

Lemma kindof_Kn bs i z : kindof bs = Kn i z -> bs = i ++ [z] /\ (0 < z)%N.
Proof.
  unfold kindof. destruct (unsnoc bs) as [[i0 z0]|] eqn:E; [|discriminate].
  apply unsnoc_spec in E. destruct (0 <? z0)%N eqn:Z.
  - intro H. injection H as <- <-. split; [exact E|]. apply N.ltb_lt. exact Z.
  - destruct (unsnoc i0) as [[i1 w]|]; [|discriminate].
    destruct (0 <? w)%N; [discriminate|]. destruct (unsnoc i1) as [[i2 v]|]; [|discriminate].
    destruct (0 <? v)%N; discriminate.
Qed.
Lemma kindof_Ks bs i w : kindof bs = Ks i w -> bs = i ++ [w; 0%N] /\ (0 < w)%N.
Proof.
  unfold kindof. destruct (unsnoc bs) as [[i0 z0]|] eqn:E; [|discriminate].
  apply unsnoc_spec in E. destruct (0 <? z0)%N eqn:Z; [discriminate|].
  apply N.ltb_ge in Z. assert (z0 = 0%N) by lia. subst z0.
  destruct (unsnoc i0) as [[i1 w0]|] eqn:E1; [|discriminate]. apply unsnoc_spec in E1.
  destruct (0 <? w0)%N eqn:W.
  - intro H. injection H as <- <-. subst. rewrite <- app_assoc. split; [reflexivity|]. apply N.ltb_lt. exact W.
  - destruct (unsnoc i1) as [[i2 v]|]; [|discriminate]. destruct (0 <? v)%N; discriminate.
Qed.
Lemma kindof_Km bs i v : kindof bs = Km i v -> bs = i ++ [v; 0%N; 0%N] /\ (0 < v)%N.
Proof.
  unfold kindof. destruct (unsnoc bs) as [[i0 z0]|] eqn:E; [|discriminate].
  apply unsnoc_spec in E. destruct (0 <? z0)%N eqn:Z; [discriminate|].
  apply N.ltb_ge in Z. assert (z0 = 0%N) by lia. subst z0.
  destruct (unsnoc i0) as [[i1 w0]|] eqn:E1; [|discriminate]. apply unsnoc_spec in E1.
  destruct (0 <? w0)%N eqn:W; [discriminate|].
  apply N.ltb_ge in W. assert (w0 = 0%N) by lia. subst w0.
  destruct (unsnoc i1) as [[i2 v0]|] eqn:E2; [|discriminate]. apply unsnoc_spec in E2.
  destruct (0 <? v0)%N eqn:V; [|discriminate].
  intro H. injection H as <- <-. subst. rewrite <- !app_assoc. split; [reflexivity|]. apply N.ltb_lt. exact V.
Qed.

Lemma take_item_spec ss bs ss' : take_item ss = Some (bs, ss') -> flat ss = itm bs ++ flat ss'.
Proof.
  destruct ss as [|[x c|b] ss0]; cbn [take_item]; [discriminate| |].
  - destruct (1 <? c)%N eqn:C.
    + intro H. injection H as <- <-. apply N.ltb_lt in C. cbn [flat flat1].
      replace (N.to_nat c) with (S (N.to_nat (c - 1))) by lia. cbn [rep]. rewrite app_assoc. reflexivity.
    + destruct (c =? 1)%N eqn:C1; [|discriminate]. apply N.eqb_eq in C1. subst c.
      intro H. injection H as <- <-. cbn [flat flat1 rep]. change (N.to_nat 1) with 1%nat. cbn [rep].
      rewrite app_nil_r. reflexivity.
  - intro H. injection H as <- <-. reflexivity.
Qed.
Lemma take_plain_spec ss x ss' : take_plain ss = Some (x, ss') -> flat ss = itm [x] ++ flat ss'.
Proof.
  unfold take_plain. destruct (take_item ss) as [[bs s0]|] eqn:E; [|discriminate].
  destruct bs as [|x0 [|]]; try discriminate. intro H. injection H as <- <-. exact (take_item_spec _ _ _ E).
Qed.
Lemma take_n_spec ss i z ss' : take_n ss = Some (i, z, ss') -> flat ss = itm (i ++ [z]) ++ flat ss' /\ (0 < z)%N.
Proof.
  unfold take_n. destruct (take_item ss) as [[bs s0]|] eqn:E; [|discriminate].
  destruct (kindof bs) eqn:K; try discriminate. intro H. injection H as <- <- <-.
  apply kindof_Kn in K as [-> Hz]. split; [exact (take_item_spec _ _ _ E)|exact Hz].
Qed.

Lemma pl_flat bs : flat1 (pl bs) = itm bs.
Proof.
  destruct bs as [|x [|y bs]]; try reflexivity.
  cbn [pl flat1]. change (N.to_nat 1) with 1%nat. cbn [rep]. apply app_nil_r.
Qed.

Lemma rep_add p q w : rep (p + q) w = rep p w ++ rep q w.
Proof. induction p as [|p IH]; cbn [rep Nat.add]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma canon_flat ss : flat (canon ss) = flat ss.
Proof.
  induction ss as [|[x c|b] ss IH]; [reflexivity| |cbn [canon flat]; rewrite IH; reflexivity].
  cbn [canon]. destruct (canon ss) as [|[x' c'|b'] r] eqn:E; cbn [flat] in IH |- *;
    rewrite <- IH; try reflexivity.
  destruct (x =? x')%N eqn:X; [|reflexivity]. apply N.eqb_eq in X. subst x'.
  cbn [flat flat1]. rewrite N2Nat.inj_add, rep_add, <- app_assoc. reflexivity.
Qed.

(** * Items in unit form *)

Lemma Ms_snoc xs x : Ms (xs ++ [x]) = Ms xs ++ Mb x.
Proof. rewrite Ms_app. cbn [Ms]. rewrite app_nil_r. reflexivity. Qed.

Lemma H_n i z : (0 < z)%N -> itm (i ++ [z]) = enc_item (tn i) (N.to_nat z - 1).
Proof.
  intro Hz. unfold itm, enc_item. rewrite tn_app. change (tn [z]) with [N.to_nat z]. rewrite Ms_snoc.
  replace (S (N.to_nat z - 1)) with (N.to_nat z) by lia. rewrite app_assoc. reflexivity.
Qed.
Lemma H_s i w : (0 < w)%N -> itm (i ++ [w; 0%N]) = enc_item (tn i) (N.to_nat w - 1) ++ Mb 0.
Proof.
  intro Hw. unfold itm, enc_item. rewrite tn_app. change (tn [w; 0%N]) with [N.to_nat w; 0%nat].
  rewrite Ms_app. cbn [Ms]. rewrite app_nil_r. replace (S (N.to_nat w - 1)) with (N.to_nat w) by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.
Lemma H_m i v : (0 < v)%N -> itm (i ++ [v; 0%N; 0%N]) = enc_item (tn i) (N.to_nat v - 1) ++ Mb 0 ++ Mb 0.
Proof.
  intro Hv. unfold itm, enc_item. rewrite tn_app. change (tn [v; 0%N; 0%N]) with [N.to_nat v; 0%nat; 0%nat].
  rewrite Ms_app. cbn [Ms]. rewrite app_nil_r. replace (S (N.to_nat v - 1)) with (N.to_nat v) by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.
Lemma H_p x : (2 <= x)%N -> itm [x] = PH ++ Mb (2 + (N.to_nat x - 2)).
Proof.
  intro Hx. unfold itm. change (tn [x]) with [N.to_nat x]. cbn [Ms]. rewrite app_nil_r.
  replace (2 + (N.to_nat x - 2))%nat with (N.to_nat x) by lia. reflexivity.
Qed.
Lemma lawN_tn i z : (0 < z)%N -> tn (lawN i z) = law (tn i) (N.to_nat z - 1).
Proof.
  intro Hz. destruct i as [|x0 mids]; cbn [lawN law tn map].
  - f_equal. lia.
  - rewrite map_app. cbn [map]. f_equal; [lia|]. f_equal. f_equal. lia.
Qed.
Lemma H_law i z : (0 < z)%N -> itm (lawN i z) = PH ++ Ms (law (tn i) (N.to_nat z - 1)).
Proof. intro Hz. unfold itm. rewrite lawN_tn by exact Hz. reflexivity. Qed.
Lemma H_seam i3 z3 : itm (1%N :: i3 ++ [(z3 - 1)%N]) = PH ++ Ms (1%nat :: tn i3 ++ [(N.to_nat z3 - 1)%nat]).
Proof. unfold itm. cbn [tn map]. rewrite map_app. cbn [map]. rewrite N2Nat.inj_sub. reflexivity. Qed.
Lemma H_merge xa i2 z2 : (2 <= xa)%N -> (0 < z2)%N ->
  itm ((xa + 1)%N :: 0%N :: lawN i2 z2) = PH ++ Ms ((3 + (N.to_nat xa - 2))%nat :: 0%nat :: law (tn i2) (N.to_nat z2 - 1)).
Proof.
  intros Hx Hz. unfold itm. cbn [tn map]. fold (tn (lawN i2 z2)). rewrite lawN_tn by exact Hz.
  replace (N.to_nat (xa + 1)) with (3 + (N.to_nat xa - 2))%nat by lia. reflexivity.
Qed.
Lemma H_c1 xa : (2 <= xa)%N -> itm [0%N; 0%N; xa] = PH ++ Ms [0%nat; 0%nat; (2 + (N.to_nat xa - 2))%nat].
Proof. intro Hx. unfold itm. cbn [tn map]. replace (2 + (N.to_nat xa - 2))%nat with (N.to_nat xa) by lia. reflexivity. Qed.

Lemma us_in_app a b : us_in (a ++ b) = us_in a ++ us_in b.
Proof. induction a as [|u a IH]; cbn [us_in app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma us_out_app a b : us_out (a ++ b) = us_out a ++ us_out b.
Proof. induction a as [|u a IH]; cbn [us_out app]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma us_in_rep u n : us_in (repeat u n) = rep n (u_in u).
Proof. induction n as [|n IH]; cbn [repeat us_in rep]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma us_out_rep u n : us_out (repeat u n) = rep n (u_out u).
Proof. induction n as [|n IH]; cbn [repeat us_out rep]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma H_m2 v : (2 <= v)%N -> itm [v; 0%N; 0%N] = PH ++ Mb (2 + (N.to_nat v - 2)) ++ Mb 0 ++ Mb 0.
Proof.
  intro Hv. unfold itm. change (tn [v; 0%N; 0%N]) with [N.to_nat v; 0%nat; 0%nat]. cbn [Ms]. rewrite app_nil_r.
  replace (2 + (N.to_nat v - 2))%nat with (N.to_nat v) by lia. reflexivity.
Qed.

Lemma rep1 w : rep (N.to_nat 1) w = w.
Proof. change (N.to_nat 1) with 1%nat. cbn [rep]. apply app_nil_r. Qed.

Ltac fin :=
  cbn [t_in t_out]; unfold skip_in, skip_out, merge_in, merge_out, sm_in, sm_out, c1_in, c1_out, enc_item;
  rewrite ?app_nil_l, <- !app_assoc; reflexivity.
Ltac red_H H := cbn - [kindof sw take_item take_plain take_n lawN pl tn itm flat] in H.

Lemma sw_spec f : forall ss ss', sw f ss = Some ss' ->
  exists us t, flat ss = us_in us ++ t_in t /\ flat ss' = us_out us ++ t_out t.
Proof.
  induction f as [|f IH]; intros ss ss' H; [discriminate|].
  destruct ss as [|[x c|bs] ss0].
  - (* END: a new P M(2) *)
    cbn [sw] in H. injection H as <-. exists (@nil unit), Tstd. split; [reflexivity|].
    cbn [flat flat1 us_out t_out]. rewrite rep1. unfold itm. change (tn [2%N]) with [2%nat]. cbn [Ms].
    rewrite !app_nil_r. reflexivity.
  - (* a plain group *)
    cbn [sw] in H. destruct ((1 <=? x)%N && (1 <=? c)%N) eqn:C; [|discriminate].
    apply andb_prop in C as [Cx Cc]. apply N.leb_le in Cx, Cc.
    destruct (sw f ss0) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
    destruct (IH ss0 r E) as [us [t [H1 H2]]].
    exists (repeat (Uitem [] (N.to_nat x - 1)) (N.to_nat c) ++ us), t.
    rewrite us_in_app, us_out_app, us_in_rep, us_out_rep. cbn [flat flat1]. rewrite H1, H2, <- !app_assoc.
    assert (U1 : u_in (Uitem [] (N.to_nat x - 1)) = itm [x]).
    { cbn [u_in]. pose proof (H_n [] x ltac:(lia)) as K. cbn [app tn map] in K. symmetry. exact K. }
    assert (U2 : u_out (Uitem [] (N.to_nat x - 1)) = itm [x]).
    { cbn [u_out law]. unfold itm. change (tn [x]) with [N.to_nat x].
      replace (S (N.to_nat x - 1)) with (N.to_nat x) by lia. reflexivity. }
    rewrite U1, U2. split; reflexivity.
  - cbn [sw] in H. destruct (kindof bs) as [i z|i w|i v|] eqn:K; [ | | | discriminate].
    + (* no unit: a plain item *)
      apply kindof_Kn in K as [-> Hz].
      destruct (sw f ss0) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
      destruct (IH ss0 r E) as [us [t [H1 H2]]].
      exists (Uitem (tn i) (N.to_nat z - 1) :: us), t. cbn [flat flat1 us_in us_out u_in u_out].
      rewrite H1, H2, pl_flat, H_n, H_law by exact Hz. rewrite <- !app_assoc. split; reflexivity.
    + (* a trailing seam *)
      apply kindof_Ks in K as [-> Hw].
      destruct (take_item ss0) as [[b2 ss2]|] eqn:T2; [|discriminate].
      destruct b2 as [|x2 [|y2 b2']].
      * red_H H. discriminate.
      * red_H H. destruct (2 <=? x2)%N eqn:X2; [|discriminate]. apply N.leb_le in X2.
        apply take_item_spec in T2.
        destruct ss2 as [|s3 ss3'].
        -- (* the seam lands on END *)
           injection H as <-. exists (@nil unit), (Tskip (tn i) (N.to_nat w - 1) (N.to_nat x2 - 2)).
           cbn [flat]. rewrite T2. cbn [flat flat1 us_in us_out]. rewrite !rep1, !app_nil_r, pl_flat.
           rewrite H_s, H_p, H_law by (try exact Hw; lia). split; [fin|].
           unfold itm. change (tn [1%N; 1%N]) with [1%nat; 1%nat]. cbn [Ms]. rewrite app_nil_r. fin.
        -- destruct (take_item (s3 :: ss3')) as [[b3 ss3]|] eqn:T3; [|discriminate].
           destruct (kindof b3) as [i3 z3|i3 w3|i3 v3|] eqn:K3; try discriminate.
           ++ (* skip *)
              apply kindof_Kn in K3 as [-> Hz3]. apply take_item_spec in T3.
              destruct (sw f ss3) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
              destruct (IH ss3 r E) as [us [t [H1 H2]]].
              exists (Uskip (tn i) (N.to_nat w - 1) (N.to_nat x2 - 2) (tn i3) (N.to_nat z3 - 1) :: us), t.
              cbn [flat]. rewrite T2, T3, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
              rewrite H_s, H_p, H_n, H_law, H_seam by (try exact Hw; try exact Hz3; lia). split; fin.
           ++ (* skip into a marker item *)
              apply kindof_Km in K3 as [-> Hv3]. apply take_item_spec in T3.
              destruct (take_plain ss3) as [[xa ss4]|] eqn:T4; [|discriminate].
              destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
              destruct (take_n ss4) as [[[i5 z5] ss5]|] eqn:T5; [|discriminate].
              apply take_plain_spec in T4. apply take_n_spec in T5 as [T5 Hz5].
              destruct (sw f ss5) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
              destruct (IH ss5 r E) as [us [t [H1 H2]]].
              exists (Usm (tn i) (N.to_nat w - 1) (N.to_nat x2 - 2) (tn i3) (N.to_nat v3 - 1) (N.to_nat xa - 2)
                          (tn i5) (N.to_nat z5 - 1) :: us), t.
              cbn [flat]. rewrite T2, T3, T4, T5, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
              rewrite H_s, (H_p x2), H_m, (H_p xa), H_n, H_law, H_seam, H_merge
                by (try exact Hw; try exact Hv3; try exact Hz5; lia).
              split; fin.
      * (* the next item is a marker item: collision C1 *)
        red_H H. destruct (kindof (x2 :: y2 :: b2')) as [i' z'|i' w'|i' v'|] eqn:K2; try discriminate.
        destruct i' as [|? ?]; [|discriminate].
        apply kindof_Km in K2 as [K2 Hv']. cbn [app] in K2. rewrite K2 in T2. apply take_item_spec in T2.
        destruct (2 <=? v')%N eqn:X2; [|discriminate]. apply N.leb_le in X2.
        destruct (take_plain ss2) as [[xa ss3]|] eqn:T3; [|discriminate].
        destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
        destruct (take_n ss3) as [[[i4 z4] ss4]|] eqn:T4; [|discriminate].
        apply take_plain_spec in T3. apply take_n_spec in T4 as [T4 Hz4].
        destruct (sw f ss4) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
        destruct (IH ss4 r E) as [us [t [H1 H2]]].
        exists (Uc1 (tn i) (N.to_nat w - 1) (N.to_nat v' - 2) (N.to_nat xa - 2) (tn i4) (N.to_nat z4 - 1) :: us), t.
        cbn [flat]. rewrite T2, T3, T4, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
        rewrite H_s, H_m2, (H_p xa), H_n, H_law, (H_p v'), H_c1, H_seam by (try exact Hw; try exact Hz4; lia).
        split; fin.
    + (* a trailing marker: merge *)
      apply kindof_Km in K as [-> Hv].
      destruct (take_plain ss0) as [[xa ss2]|] eqn:T2; [|discriminate].
      destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
      destruct (take_n ss2) as [[[i2 z2] ss3]|] eqn:T3; [|discriminate].
      apply take_plain_spec in T2. apply take_n_spec in T3 as [T3 Hz2].
      destruct (sw f ss3) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
      destruct (IH ss3 r E) as [us [t [H1 H2]]].
      exists (Umerge (tn i) (N.to_nat v - 1) (N.to_nat xa - 2) (tn i2) (N.to_nat z2 - 1) :: us), t.
      cbn [flat]. rewrite T2, T3, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite pl_flat.
      rewrite H_m, H_p, H_n, H_law, H_merge by (try exact Hv; try exact Hz2; lia). split; fin.
Qed.

(** * One sweep of the whole tape *)

Lemma cfg_mk n R ss : cfg (mk n R ss) = 0inf <{{D}} [1;0]^^(N.to_nat n) *> Ms (tn R) *> flat ss *> ENDc *> 0inf.
Proof. reflexivity. Qed.

Lemma refill_pre n ss x1 x2 ss2 us t k :
  flat ss = itm [x1] ++ itm [x2] ++ flat ss2 -> flat ss2 = us_in us ++ t_in t ->
  (2 <= x1)%N -> (2 <= x2)%N -> N.to_nat n = k ->
  cfg (mk n [] ss) =
  0inf <{{D}} [1;0]^^k *> (PH ++ Mb (2 + (N.to_nat x1 - 2)) ++ PH ++ Mb (2 + (N.to_nat x2 - 2))) *>
    us_in us *> t_in t *> ENDc *> 0inf.
Proof.
  intros F H1 X1 X2 K. unfold cfg. cbn [blk rst its]. rewrite F, H1, !H_p by lia. rewrite K.
  change (Ms (tn [])) with (@nil Sym). rewrite !Str_app_assoc. reflexivity.
Qed.

Theorem step_sound s s' : step s = Some s' -> cfg s -->* cfg s'.
Proof.
  destruct s as [n Rr ss]. unfold step. cbn [blk rst its].
  destruct Rr as [|r0 R0].
  - (* R empty: refill *)
    destruct (take_plain ss) as [[x1 ss1]|] eqn:T1; [|discriminate].
    destruct (take_plain ss1) as [[x2 ss2]|] eqn:T2; [|discriminate].
    destruct ((2 <=? x1)%N && (2 <=? x2)%N) eqn:X; [|discriminate].
    apply andb_prop in X as [X1 X2]. apply N.leb_le in X1, X2.
    destruct (sw (fuel_of ss2) ss2) as [r|] eqn:E; [|discriminate].
    destruct (sw_spec _ _ _ E) as [us [t [H1 H2]]].
    apply take_plain_spec in T1, T2. rewrite T2 in T1.
    pose proof (N.div_mod n 3 ltac:(lia)) as DM. pose proof (N.mod_lt n 3 ltac:(lia)) as ML.
    remember (N.to_nat (n / 3)) as k eqn:Hk.
    destruct (n mod 3)%N as [|[p|p|]] eqn:M.
    + intro H. assert (Hs : s' = mk 2 [(x1 + n / 3)%N] (canon (SP x2 1 :: r))) by (injection H as <-; reflexivity).
      subst s'.
      rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k) T1 H1 X1 X2) by lia.
      eapply evstep_trans; [apply sweep_refill0|].
      rewrite cfg_mk, canon_flat. cbn [flat flat1]. rewrite rep1, H2, H_p by lia.
      change (tn [(x1 + n / 3)%N]) with [N.to_nat (x1 + n / 3)]. cbn [Ms]. rewrite app_nil_r.
      replace (N.to_nat (x1 + n / 3)) with (2 + k + (N.to_nat x1 - 2))%nat by lia.
      change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
    + exfalso. lia.
    + assert (p = 1%positive) by lia. subst p.
      intro H. assert (Hs : s' = mk 2 [(x1 + n / 3 + 1)%N; 0%N; x2] (canon r)) by (injection H as <-; reflexivity).
      subst s'.
      rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k + 2) T1 H1 X1 X2) by lia.
      eapply evstep_trans; [apply sweep_refill2|].
      rewrite cfg_mk, canon_flat, H2.
      assert (L : tn [(x1 + n / 3 + 1)%N; 0%N; x2] = [(3 + k + (N.to_nat x1 - 2))%nat; 0%nat; (2 + (N.to_nat x2 - 2))%nat]).
      { cbn [tn map]. f_equal; [lia|]. f_equal. f_equal. lia. }
      rewrite L. change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
    + intro H. assert (Hs : s' = mk 2 [(x1 + n / 3)%N] (canon (SD [1%N; (x2 - 1)%N] :: r))) by (injection H as <-; reflexivity).
      subst s'.
      rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k + 1) T1 H1 X1 X2) by lia.
      eapply evstep_trans; [apply sweep_refill1|].
      rewrite cfg_mk, canon_flat. cbn [flat flat1]. rewrite H2.
      change (tn [(x1 + n / 3)%N]) with [N.to_nat (x1 + n / 3)]. cbn [Ms]. rewrite app_nil_r.
      replace (N.to_nat (x1 + n / 3)) with (2 + k + (N.to_nat x1 - 2))%nat by lia.
      unfold itm. change (tn [1%N; (x2 - 1)%N]) with [1%nat; N.to_nat (x2 - 1)]. cbn [Ms]. rewrite app_nil_r.
      replace (N.to_nat (x2 - 1)) with (1 + (N.to_nat x2 - 2))%nat by lia.
      change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
  - (* R non-empty *)
    destruct (kindof (r0 :: R0)) as [iR zR|iR wR|iR vR|] eqn:K; try discriminate.
    + (* plain left end *)
      apply kindof_Kn in K as [KR Hz].
      destruct (sw (fuel_of ss) ss) as [r|] eqn:E; [|discriminate].
      destruct (sw_spec _ _ _ E) as [us [t [H1 H2]]].
      assert (L : cfg (mk n (r0 :: R0) ss) =
        0inf <{{D}} [1;0]^^(N.to_nat n) *> Ms (tn iR ++ [S (N.to_nat zR - 1)]) *> us_in us *> t_in t *> ENDc *> 0inf).
      { rewrite cfg_mk, KR, tn_app, H1. change (tn [zR]) with [N.to_nat zR].
        replace (S (N.to_nat zR - 1)) with (N.to_nat zR) by lia. rewrite !Str_app_assoc. reflexivity. }
      rewrite L. intro H.
      destruct ((zR =? 1)%N && match iR with [] => true | _ => false end) eqn:Z.
      * assert (Hs : s' = mk (n + 3) [] (canon r)) by (injection H as <-; reflexivity). subst s'.
        apply andb_prop in Z as [Z1 Z2]. apply N.eqb_eq in Z1. subst zR. destruct iR; [|discriminate].
        eapply evstep_trans; [apply sweep|].
        rewrite cfg_mk, canon_flat, H2. change (tn []) with (@nil nat). change (Ms []) with (@nil Sym).
        replace (N.to_nat (n + 3)) with (S (S (S (N.to_nat n)))) by lia.
        change (N.to_nat 1 - 1)%nat with 0%nat. cbn [app Ms]. rewrite app_nil_r.
        change ([1;0]^^(S (S (S (N.to_nat n))))) with ([1;0] ++ [1;0]^^(S (S (N.to_nat n)))).
        rewrite <- lpow_shift, !Str_app_assoc. apply evstep_refl.
      * assert (Hs : s' = mk (n + 2) (iR ++ [(zR - 1)%N]) (canon r)) by (injection H as <-; reflexivity). subst s'.
        eapply evstep_trans; [apply sweep|].
        rewrite cfg_mk, canon_flat, H2, tn_app. change (tn [(zR - 1)%N]) with [N.to_nat (zR - 1)].
        rewrite N2Nat.inj_sub. change (N.to_nat 1) with 1%nat.
        replace (N.to_nat (n + 2)) with (S (S (N.to_nat n))) by lia. rewrite !Str_app_assoc. apply evstep_refl.
    + (* R-merge *)
      apply kindof_Km in K as [KR Hv].
      destruct (take_plain ss) as [[xa ss2]|] eqn:T2; [|discriminate].
      destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
      destruct (take_n ss2) as [[[i2 z2] ss3]|] eqn:T3; [|discriminate].
      destruct (sw (fuel_of ss3) ss3) as [r|] eqn:E; [|discriminate].
      destruct (sw_spec _ _ _ E) as [us [t [H1 H2]]].
      apply take_plain_spec in T2. apply take_n_spec in T3 as [T3 Hz2].
      intro H.
      assert (Hs : s' = mk (n + 2) (iR ++ [(vR - 1)%N]) (canon (SD ((xa + 1)%N :: 0%N :: lawN i2 z2) :: r)))
        by (injection H as <-; reflexivity). subst s'.
      assert (L : cfg (mk n (r0 :: R0) ss) =
        0inf <{{D}} [1;0]^^(N.to_nat n) *> Ms (tn iR ++ [S (N.to_nat vR - 1); 0%nat; 0%nat]) *>
          (PH ++ Mb (2 + (N.to_nat xa - 2)) ++ PH ++ Ms (tn i2) ++ Mb (S (N.to_nat z2 - 1))) *>
          us_in us *> t_in t *> ENDc *> 0inf).
      { rewrite cfg_mk, KR, tn_app, T2, T3, H1, H_p, H_n by lia. change (tn [vR; 0%N; 0%N]) with [N.to_nat vR; 0%nat; 0%nat].
        replace (S (N.to_nat vR - 1)) with (N.to_nat vR) by lia. unfold enc_item. rewrite !Str_app_assoc. reflexivity. }
      rewrite L. eapply evstep_trans; [apply sweep_Rmerge|].
      rewrite cfg_mk, canon_flat. cbn [flat flat1]. rewrite H2, H_merge by lia. rewrite tn_app.
      change (tn [(vR - 1)%N]) with [N.to_nat (vR - 1)]. rewrite N2Nat.inj_sub. change (N.to_nat 1) with 1%nat.
      replace (N.to_nat (n + 2)) with (S (S (N.to_nat n))) by lia. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

(** * Many sweeps *)

Fixpoint iterP (p : positive) (s : st) : option st :=
  match p with
  | xH => step s
  | xO p' => match iterP p' s with Some s' => iterP p' s' | None => None end
  | xI p' => match step s with
             | Some s1 => match iterP p' s1 with Some s2 => iterP p' s2 | None => None end
             | None => None
             end
  end.

Lemma iterP_sound p : forall s s', iterP p s = Some s' -> cfg s -->* cfg s'.
Proof.
  induction p as [p IH|p IH|]; intros s s' H; cbn [iterP] in H.
  - destruct (step s) as [s1|] eqn:E1; [|discriminate].
    destruct (iterP p s1) as [s2|] eqn:E2; [|discriminate].
    eapply evstep_trans; [apply step_sound; exact E1|].
    eapply evstep_trans; [apply IH; exact E2|]. apply IH. exact H.
  - destruct (iterP p s) as [s1|] eqn:E1; [|discriminate].
    eapply evstep_trans; [apply IH; exact E1|]. apply IH. exact H.
  - apply step_sound. exact H.
Qed.
End P_M269h.

Section P_M269i.
Local Open Scope N_scope.

Definition s100 : st := mk 16 [26; 0; 4] [SP 11 4; SD [4; 7]; SD [9; 0; 2]; SP 5 4; SP 2 1; SP 5 1; SD [5; 0; 0]; SP 2 4; SD [1; 1]; SP 2 18; SD [2; 0]; SP 2 12; SD [1; 1]].

(* a concrete stepper with a binary step count *)
Fixpoint ccsteps (p : positive) (x : cconfig) : option cconfig :=
  match p with
  | xH => cconfig_step tm x
  | xO p' => match ccsteps p' x with Some x' => ccsteps p' x' | None => None end
  | xI p' => match cconfig_step tm x with
             | Some x1 => match ccsteps p' x1 with Some x2 => ccsteps p' x2 | None => None end
             | None => None
             end
  end.

Lemma cstep1 x y : cconfig_step tm x = Some y -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof. intro H. pose proof (cconfig_step_spec tm x) as K. rewrite H in K. eapply evstep_step; [exact K|apply evstep_refl]. Qed.

Lemma ccsteps_sound p : forall x y, ccsteps p x = Some y -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof.
  induction p as [p IH|p IH|]; intros x y H; cbn [ccsteps] in H.
  - destruct (cconfig_step tm x) as [x1|] eqn:E1; [|discriminate].
    destruct (ccsteps p x1) as [x2|] eqn:E2; [|discriminate].
    eapply evstep_trans; [apply cstep1; exact E1|]. eapply evstep_trans; [apply IH; exact E2|]. apply IH. exact H.
  - destruct (ccsteps p x) as [x1|] eqn:E1; [|discriminate].
    eapply evstep_trans; [apply IH; exact E1|]. apply IH. exact H.
  - apply cstep1. exact H.
Qed.

Definition ccreach (p : positive) (x y : cconfig) : bool :=
  match ccsteps p x with Some x' => cconfig_eqb x' y | None => false end.
Lemma ccreach_spec p x y : ccreach p x y = true -> cconfig_to_config x -[ tm ]->* cconfig_to_config y.
Proof.
  unfold ccreach. destruct (ccsteps p x) as [x'|] eqn:E; [|discriminate]. intro H.
  rewrite <- (cconfig_eqb_spec _ _ H). exact (ccsteps_sound p _ _ E).
Qed.

Lemma cfg_cc s : cfg s = cconfig_to_config ([], ([1;0])%sym^^(N.to_nat (blk s)) ++ Ms (tn (rst s)) ++ flat (its s) ++ ENDc, 0%sym, D).
Proof. unfold cfg, cconfig_to_config. rewrite <- !Str_app_assoc, <- !app_assoc. reflexivity. Qed.

(* the record of sweep 100 is reached after 512,298 steps *)
Lemma init100 : c0 -[ tm ]->* cfg s100.
Proof. rewrite cfg_cc, c0_to_cconfig. apply (ccreach_spec 512298). vm_compute. reflexivity. Qed.
End P_M269i.

Section P_M269m.
(** * One sweep of a prefix (no END) and of a suffix (with END), as unit decompositions *)

Definition SWP (A A' : list seg) : Prop := exists us, flat A = us_in us /\ flat A' = us_out us.
Definition SW (X X' : list seg) : Prop := exists us t, flat X = us_in us ++ t_in t /\ flat X' = us_out us ++ t_out t.

Lemma cut A A' X X' : SWP A A' -> SW X X' -> SW (A ++ X) (A' ++ X').
Proof.
  intros [ua [H1 H2]] [ux [t [H3 H4]]]. exists (ua ++ ux), t.
  rewrite !flat_app, us_in_app, us_out_app, H1, H2, H3, H4, <- !app_assoc. split; reflexivity.
Qed.

Local Open Scope N_scope.
Fixpoint swp (fuel : nat) (ss : list seg) : option (list seg) :=
  match fuel with O => None | S f =>
  match ss with
  | [] => Some []
  | SP x c :: ss' => if (1 <=? x) && (1 <=? c) then option_map (cons (SP x c)) (swp f ss') else None
  | SD bs :: ss' =>
    match kindof bs with
    | Kn i z => option_map (cons (pl (lawN i z))) (swp f ss')
    | Ks i w =>
      match take_item ss' with
      | Some ([x2], ss2) =>
        if 2 <=? x2 then
          match ss2 with
          | [] => None
          | _ =>
            match take_item ss2 with
            | Some (b3, ss3) =>
              match kindof b3 with
              | Kn i3 z3 => option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD (1 :: i3 ++ [z3 - 1]) :: r) (swp f ss3)
              | Km i3 v3 =>
                match take_plain ss3 with
                | Some (xa, ss4) =>
                  if 2 <=? xa then
                    match take_n ss4 with
                    | Some (i5, z5, ss5) =>
                      option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD (1 :: i3 ++ [v3 - 1]) ::
                                           SD ((xa + 1) :: 0 :: lawN i5 z5) :: r) (swp f ss5)
                    | None => None
                    end
                  else None
                | None => None
                end
              | _ => None
              end
            | None => None
            end
          end
        else None
      | Some (b2, ss2) =>
        match kindof b2 with
        | Km [] x2 =>
          if 2 <=? x2 then
            match take_plain ss2 with
            | Some (xa, ss3) =>
              if 2 <=? xa then
                match take_n ss3 with
                | Some (i4, z4, ss4) =>
                  option_map (fun r => pl (lawN i w) :: SP x2 1 :: SD [0; 0; xa] :: SD (1 :: i4 ++ [z4 - 1]) :: r) (swp f ss4)
                | None => None
                end
              else None
            | None => None
            end
          else None
        | _ => None
        end
      | None => None
      end
    | Km i v =>
      match take_plain ss' with
      | Some (xa, ss2) =>
        if 2 <=? xa then
          match take_n ss2 with
          | Some (i2, z2, ss3) => option_map (fun r => pl (lawN i v) :: SD ((xa + 1) :: 0 :: lawN i2 z2) :: r) (swp f ss3)
          | None => None
          end
        else None
      | None => None
      end
    | Kbad => None
    end
  end end.

Local Close Scope N_scope.

Ltac finp :=
  cbn [t_in t_out]; unfold skip_in, skip_out, merge_in, merge_out, sm_in, sm_out, c1_in, c1_out, enc_item;
  rewrite ?app_nil_l, <- ?app_assoc; reflexivity.
Ltac red_Hp H := cbn - [kindof swp take_item take_plain take_n lawN pl tn itm flat] in H.

Lemma swp_spec f : forall ss ss', swp f ss = Some ss' -> SWP ss ss'.
Proof.
  induction f as [|f IH]; intros ss ss' H; [discriminate|].
  destruct ss as [|[x c|bs] ss0].
  - (* the end of the prefix *)
    cbn [swp] in H. injection H as <-. exists (@nil unit). split; reflexivity.
  - (* a plain group *)
    cbn [swp] in H. destruct ((1 <=? x)%N && (1 <=? c)%N) eqn:C; [|discriminate].
    apply andb_prop in C as [Cx Cc]. apply N.leb_le in Cx, Cc.
    destruct (swp f ss0) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
    destruct (IH ss0 r E) as [us [H1 H2]].
    exists (repeat (Uitem [] (N.to_nat x - 1)) (N.to_nat c) ++ us).
    rewrite us_in_app, us_out_app, us_in_rep, us_out_rep. cbn [flat flat1]. rewrite H1, H2, <- ?app_assoc.
    assert (U1 : u_in (Uitem [] (N.to_nat x - 1)) = itm [x]).
    { cbn [u_in]. pose proof (H_n [] x ltac:(lia)) as K. cbn [app tn map] in K. symmetry. exact K. }
    assert (U2 : u_out (Uitem [] (N.to_nat x - 1)) = itm [x]).
    { cbn [u_out law]. unfold itm. change (tn [x]) with [N.to_nat x].
      replace (S (N.to_nat x - 1)) with (N.to_nat x) by lia. reflexivity. }
    rewrite U1, U2. split; reflexivity.
  - cbn [swp] in H. destruct (kindof bs) as [i z|i w|i v|] eqn:K; [ | | | discriminate].
    + (* no unit: a plain item *)
      apply kindof_Kn in K as [-> Hz].
      destruct (swp f ss0) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
      destruct (IH ss0 r E) as [us [H1 H2]].
      exists (Uitem (tn i) (N.to_nat z - 1) :: us). cbn [flat flat1 us_in us_out u_in u_out].
      rewrite H1, H2, pl_flat, H_n, H_law by exact Hz. rewrite <- ?app_assoc. split; reflexivity.
    + (* a trailing seam *)
      apply kindof_Ks in K as [-> Hw].
      destruct (take_item ss0) as [[b2 ss2]|] eqn:T2; [|discriminate].
      destruct b2 as [|x2 [|y2 b2']].
      * red_Hp H. discriminate.
      * red_Hp H. destruct (2 <=? x2)%N eqn:X2; [|discriminate]. apply N.leb_le in X2.
        apply take_item_spec in T2.
        destruct ss2 as [|s3 ss3'].
        -- (* a skip that would need END: not a prefix sweep *)
           discriminate.
        -- destruct (take_item (s3 :: ss3')) as [[b3 ss3]|] eqn:T3; [|discriminate].
           destruct (kindof b3) as [i3 z3|i3 w3|i3 v3|] eqn:K3; try discriminate.
           ++ (* skip *)
              apply kindof_Kn in K3 as [-> Hz3]. apply take_item_spec in T3.
              destruct (swp f ss3) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
              destruct (IH ss3 r E) as [us [H1 H2]].
              exists (Uskip (tn i) (N.to_nat w - 1) (N.to_nat x2 - 2) (tn i3) (N.to_nat z3 - 1) :: us).
              cbn [flat]. rewrite T2, T3, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
              rewrite H_s, H_p, H_n, H_law, H_seam by (try exact Hw; try exact Hz3; lia). split; finp.
           ++ (* skip into a marker item *)
              apply kindof_Km in K3 as [-> Hv3]. apply take_item_spec in T3.
              destruct (take_plain ss3) as [[xa ss4]|] eqn:T4; [|discriminate].
              destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
              destruct (take_n ss4) as [[[i5 z5] ss5]|] eqn:T5; [|discriminate].
              apply take_plain_spec in T4. apply take_n_spec in T5 as [T5 Hz5].
              destruct (swp f ss5) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
              destruct (IH ss5 r E) as [us [H1 H2]].
              exists (Usm (tn i) (N.to_nat w - 1) (N.to_nat x2 - 2) (tn i3) (N.to_nat v3 - 1) (N.to_nat xa - 2)
                          (tn i5) (N.to_nat z5 - 1) :: us).
              cbn [flat]. rewrite T2, T3, T4, T5, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
              rewrite H_s, (H_p x2), H_m, (H_p xa), H_n, H_law, H_seam, H_merge
                by (try exact Hw; try exact Hv3; try exact Hz5; lia).
              split; finp.
      * (* the next item is a marker item: collision C1 *)
        red_Hp H. destruct (kindof (x2 :: y2 :: b2')) as [i' z'|i' w'|i' v'|] eqn:K2; try discriminate.
        destruct i' as [|? ?]; [|discriminate].
        apply kindof_Km in K2 as [K2 Hv']. cbn [app] in K2. rewrite K2 in T2. apply take_item_spec in T2.
        destruct (2 <=? v')%N eqn:X2; [|discriminate]. apply N.leb_le in X2.
        destruct (take_plain ss2) as [[xa ss3]|] eqn:T3; [|discriminate].
        destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
        destruct (take_n ss3) as [[[i4 z4] ss4]|] eqn:T4; [|discriminate].
        apply take_plain_spec in T3. apply take_n_spec in T4 as [T4 Hz4].
        destruct (swp f ss4) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
        destruct (IH ss4 r E) as [us [H1 H2]].
        exists (Uc1 (tn i) (N.to_nat w - 1) (N.to_nat v' - 2) (N.to_nat xa - 2) (tn i4) (N.to_nat z4 - 1) :: us).
        cbn [flat]. rewrite T2, T3, T4, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite rep1, pl_flat.
        rewrite H_s, H_m2, (H_p xa), H_n, H_law, (H_p v'), H_c1, H_seam by (try exact Hw; try exact Hz4; lia).
        split; finp.
    + (* a trailing marker: merge *)
      apply kindof_Km in K as [-> Hv].
      destruct (take_plain ss0) as [[xa ss2]|] eqn:T2; [|discriminate].
      destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
      destruct (take_n ss2) as [[[i2 z2] ss3]|] eqn:T3; [|discriminate].
      apply take_plain_spec in T2. apply take_n_spec in T3 as [T3 Hz2].
      destruct (swp f ss3) as [r|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
      destruct (IH ss3 r E) as [us [H1 H2]].
      exists (Umerge (tn i) (N.to_nat v - 1) (N.to_nat xa - 2) (tn i2) (N.to_nat z2 - 1) :: us).
      cbn [flat]. rewrite T2, T3, H1, H2. cbn [flat1 us_in us_out u_in u_out]. rewrite pl_flat.
      rewrite H_m, H_p, H_n, H_law, H_merge by (try exact Hv; try exact Hz2; lia). split; finp.
Qed.




(** * The left end with a prefix H, for any suffix that sweeps *)

Lemma cfg_flat n R a b : flat a = flat b -> cfg (mk n R a) = cfg (mk n R b).
Proof. intro E. rewrite !cfg_mk, E. reflexivity. Qed.
Lemma to_cfg c n R a b : c -->* cfg (mk n R a) -> flat a = flat b -> c -->* cfg (mk n R b).
Proof. intros H E. rewrite <- (cfg_flat n R a b E). exact H. Qed.

Lemma case_refill0 n ss x1 x2 ss2 us t r :
  flat ss = itm [x1] ++ itm [x2] ++ flat ss2 -> flat ss2 = us_in us ++ t_in t -> flat r = us_out us ++ t_out t ->
  (2 <= x1)%N -> (2 <= x2)%N -> (n mod 3 = 0)%N ->
  cfg (mk n [] ss) -->* cfg (mk 2 [(x1 + n / 3)%N] (SP x2 1 :: r)).
Proof.
  intros T1 H1 H2 X1 X2 M.
  pose proof (N.div_mod n 3 ltac:(lia)) as DM. rewrite M in DM.
  remember (N.to_nat (n / 3)) as k eqn:Hk.
  rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k) T1 H1 X1 X2) by lia.
  eapply evstep_trans; [apply sweep_refill0|].
  rewrite cfg_mk. cbn [flat flat1]. rewrite rep1, H2, H_p by lia.
  change (tn [(x1 + n / 3)%N]) with [N.to_nat (x1 + n / 3)]. cbn [Ms]. rewrite app_nil_r.
  replace (N.to_nat (x1 + n / 3)) with (2 + k + (N.to_nat x1 - 2))%nat by lia.
  change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Lemma case_refill1 n ss x1 x2 ss2 us t r :
  flat ss = itm [x1] ++ itm [x2] ++ flat ss2 -> flat ss2 = us_in us ++ t_in t -> flat r = us_out us ++ t_out t ->
  (2 <= x1)%N -> (2 <= x2)%N -> (n mod 3 = 1)%N ->
  cfg (mk n [] ss) -->* cfg (mk 2 [(x1 + n / 3)%N] (SD [1%N; (x2 - 1)%N] :: r)).
Proof.
  intros T1 H1 H2 X1 X2 M.
  pose proof (N.div_mod n 3 ltac:(lia)) as DM. rewrite M in DM.
  remember (N.to_nat (n / 3)) as k eqn:Hk.
  rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k + 1) T1 H1 X1 X2) by lia.
  eapply evstep_trans; [apply sweep_refill1|].
  rewrite cfg_mk. cbn [flat flat1]. rewrite H2.
  change (tn [(x1 + n / 3)%N]) with [N.to_nat (x1 + n / 3)]. cbn [Ms]. rewrite app_nil_r.
  replace (N.to_nat (x1 + n / 3)) with (2 + k + (N.to_nat x1 - 2))%nat by lia.
  unfold itm. change (tn [1%N; (x2 - 1)%N]) with [1%nat; N.to_nat (x2 - 1)]. cbn [Ms]. rewrite app_nil_r.
  replace (N.to_nat (x2 - 1)) with (1 + (N.to_nat x2 - 2))%nat by lia.
  change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Lemma case_refill2 n ss x1 x2 ss2 us t r :
  flat ss = itm [x1] ++ itm [x2] ++ flat ss2 -> flat ss2 = us_in us ++ t_in t -> flat r = us_out us ++ t_out t ->
  (2 <= x1)%N -> (2 <= x2)%N -> (n mod 3 = 2)%N ->
  cfg (mk n [] ss) -->* cfg (mk 2 [(x1 + n / 3 + 1)%N; 0%N; x2] r).
Proof.
  intros T1 H1 H2 X1 X2 M.
  pose proof (N.div_mod n 3 ltac:(lia)) as DM. rewrite M in DM.
  remember (N.to_nat (n / 3)) as k eqn:Hk.
  rewrite (refill_pre n ss x1 x2 ss2 us t (3 * k + 2) T1 H1 X1 X2) by lia.
  eapply evstep_trans; [apply sweep_refill2|].
  rewrite cfg_mk, H2.
  assert (L : tn [(x1 + n / 3 + 1)%N; 0%N; x2] = [(3 + k + (N.to_nat x1 - 2))%nat; 0%nat; (2 + (N.to_nat x2 - 2))%nat]).
  { cbn [tn map]. f_equal; [lia|]. f_equal. f_equal. lia. }
  rewrite L. change (N.to_nat 2) with 2%nat. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Lemma case_plain n iR zR ss us t r :
  flat ss = us_in us ++ t_in t -> flat r = us_out us ++ t_out t -> (0 < zR)%N ->
  cfg (mk n (iR ++ [zR]) ss) -->*
  cfg (if (zR =? 1)%N && match iR with [] => true | _ => false end then mk (n + 3) [] r
       else mk (n + 2) (iR ++ [(zR - 1)%N]) r).
Proof.
  intros H1 H2 Hz.
  assert (L : cfg (mk n (iR ++ [zR]) ss) =
    0inf <{{D}} [1;0]^^(N.to_nat n) *> Ms (tn iR ++ [S (N.to_nat zR - 1)]) *> us_in us *> t_in t *> ENDc *> 0inf).
  { rewrite cfg_mk, tn_app, H1. change (tn [zR]) with [N.to_nat zR].
    replace (S (N.to_nat zR - 1)) with (N.to_nat zR) by lia. rewrite !Str_app_assoc. reflexivity. }
  rewrite L.
  destruct ((zR =? 1)%N && match iR with [] => true | _ => false end) eqn:Z.
  - apply andb_prop in Z as [Z1 Z2]. apply N.eqb_eq in Z1. subst zR. destruct iR; [|discriminate].
    eapply evstep_trans; [apply sweep|].
    rewrite cfg_mk, H2. change (tn []) with (@nil nat). change (Ms []) with (@nil Sym).
    replace (N.to_nat (n + 3)) with (S (S (S (N.to_nat n)))) by lia.
    change (N.to_nat 1 - 1)%nat with 0%nat. cbn [app Ms]. rewrite app_nil_r.
    change ([1;0]^^(S (S (S (N.to_nat n))))) with ([1;0] ++ [1;0]^^(S (S (N.to_nat n)))).
    rewrite <- lpow_shift, !Str_app_assoc. apply evstep_refl.
  - eapply evstep_trans; [apply sweep|].
    rewrite cfg_mk, H2, tn_app. change (tn [(zR - 1)%N]) with [N.to_nat (zR - 1)].
    rewrite N2Nat.inj_sub. change (N.to_nat 1) with 1%nat.
    replace (N.to_nat (n + 2)) with (S (S (N.to_nat n))) by lia. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Lemma case_rmerge n iR vR ss xa i2 z2 ss3 us t r :
  flat ss = itm [xa] ++ itm (i2 ++ [z2]) ++ flat ss3 -> flat ss3 = us_in us ++ t_in t -> flat r = us_out us ++ t_out t ->
  (0 < vR)%N -> (2 <= xa)%N -> (0 < z2)%N ->
  cfg (mk n (iR ++ [vR; 0%N; 0%N]) ss) -->*
  cfg (mk (n + 2) (iR ++ [(vR - 1)%N]) (SD ((xa + 1)%N :: 0%N :: lawN i2 z2) :: r)).
Proof.
  intros T H1 H2 Hv XA Hz2.
  assert (L : cfg (mk n (iR ++ [vR; 0%N; 0%N]) ss) =
    0inf <{{D}} [1;0]^^(N.to_nat n) *> Ms (tn iR ++ [S (N.to_nat vR - 1); 0%nat; 0%nat]) *>
      (PH ++ Mb (2 + (N.to_nat xa - 2)) ++ PH ++ Ms (tn i2) ++ Mb (S (N.to_nat z2 - 1))) *>
      us_in us *> t_in t *> ENDc *> 0inf).
  { rewrite cfg_mk, tn_app, T, H1, H_p, H_n by lia. change (tn [vR; 0%N; 0%N]) with [N.to_nat vR; 0%nat; 0%nat].
    replace (S (N.to_nat vR - 1)) with (N.to_nat vR) by lia. unfold enc_item. rewrite !Str_app_assoc. reflexivity. }
  rewrite L. eapply evstep_trans; [apply sweep_Rmerge|].
  rewrite cfg_mk. cbn [flat flat1]. rewrite H2, H_merge by lia. rewrite tn_app.
  change (tn [(vR - 1)%N]) with [N.to_nat (vR - 1)]. rewrite N2Nat.inj_sub. change (N.to_nat 1) with 1%nat.
  replace (N.to_nat (n + 2)) with (S (S (N.to_nat n))) by lia. rewrite !Str_app_assoc. apply evstep_refl.
Qed.

Local Open Scope N_scope.
Definition stepH (s : st) : option st :=
  let n := blk s in
  match rst s with
  | [] =>
    match take_plain (its s) with
    | Some (x1, ss1) =>
      match take_plain ss1 with
      | Some (x2, ss2) =>
        if (2 <=? x1) && (2 <=? x2) then
          match swp (fuel_of ss2) ss2 with
          | Some r =>
            let k := n / 3 in
            match n mod 3 with
            | 0 => Some (mk 2 [x1 + k] (canon (SP x2 1 :: r)))
            | 1 => Some (mk 2 [x1 + k] (canon (SD [1; x2 - 1] :: r)))
            | _ => Some (mk 2 [x1 + k + 1; 0; x2] (canon r))
            end
          | None => None
          end
        else None
      | None => None
      end
    | None => None
    end
  | Rr =>
    match kindof Rr with
    | Kn iR zR =>
      match swp (fuel_of (its s)) (its s) with
      | Some r => Some (if (zR =? 1) && (match iR with [] => true | _ => false end)
                        then mk (n + 3) [] (canon r) else mk (n + 2) (iR ++ [zR - 1]) (canon r))
      | None => None
      end
    | Km iR vR =>
      match take_plain (its s) with
      | Some (xa, ss2) =>
        if 2 <=? xa then
          match take_n ss2 with
          | Some (i2, z2, ss3) =>
            match swp (fuel_of ss3) ss3 with
            | Some r => Some (mk (n + 2) (iR ++ [vR - 1]) (canon (SD ((xa + 1) :: 0 :: lawN i2 z2) :: r)))
            | None => None
            end
          | None => None
          end
        else None
      | None => None
      end
    | _ => None
    end
  end.
Local Close Scope N_scope.

Definition cfgx (s : st) (X : list seg) : Q * tape := cfg (mk (blk s) (rst s) (its s ++ X)).

Ltac flateq := rewrite ?flat_app, ?canon_flat; cbn [flat]; rewrite ?flat_app, <- ?app_assoc; reflexivity.

Theorem stepH_sound s s' : stepH s = Some s' -> forall X X', SW X X' -> cfgx s X -->* cfgx s' X'.
Proof.
  intros H X X' [usX [t [HX1 HX2]]].
  destruct s as [n Rr ss]. revert H. unfold stepH, cfgx. cbn [blk rst its].
  destruct Rr as [|r0 R0].
  - destruct (take_plain ss) as [[x1 ss1]|] eqn:T1; [|discriminate].
    destruct (take_plain ss1) as [[x2 ss2]|] eqn:T2; [|discriminate].
    destruct ((2 <=? x1)%N && (2 <=? x2)%N) eqn:X0; [|discriminate].
    apply andb_prop in X0 as [X1 X2]. apply N.leb_le in X1, X2.
    destruct (swp (fuel_of ss2) ss2) as [r|] eqn:E; [|discriminate].
    destruct (swp_spec _ _ _ E) as [us [H1 H2]].
    apply take_plain_spec in T1, T2. rewrite T2 in T1.
    assert (T1' : flat (ss ++ X) = itm [x1] ++ itm [x2] ++ flat (ss2 ++ X))
      by (rewrite !flat_app, T1, <- !app_assoc; reflexivity).
    assert (H1' : flat (ss2 ++ X) = us_in (us ++ usX) ++ t_in t)
      by (rewrite flat_app, us_in_app, H1, HX1, <- ?app_assoc; reflexivity).
    assert (H2' : flat (r ++ X') = us_out (us ++ usX) ++ t_out t)
      by (rewrite flat_app, us_out_app, H2, HX2, <- ?app_assoc; reflexivity).
    pose proof (N.mod_lt n 3 ltac:(lia)) as ML.
    destruct (n mod 3)%N as [|[p|p|]] eqn:M.
    + intro H. assert (Hs : s' = mk 2 [(x1 + n / 3)%N] (canon (SP x2 1 :: r))) by (injection H as <-; reflexivity).
      subst s'. cbn [blk rst its].
      eapply to_cfg; [exact (case_refill0 n (ss ++ X) x1 x2 (ss2 ++ X) (us ++ usX) t (r ++ X') T1' H1' H2' X1 X2 M)|].
      flateq.
    + exfalso. lia.
    + assert (p = 1%positive) by lia. subst p.
      intro H. assert (Hs : s' = mk 2 [(x1 + n / 3 + 1)%N; 0%N; x2] (canon r)) by (injection H as <-; reflexivity).
      subst s'. cbn [blk rst its].
      eapply to_cfg; [exact (case_refill2 n (ss ++ X) x1 x2 (ss2 ++ X) (us ++ usX) t (r ++ X') T1' H1' H2' X1 X2 M)|].
      flateq.
    + intro H. assert (Hs : s' = mk 2 [(x1 + n / 3)%N] (canon (SD [1%N; (x2 - 1)%N] :: r)))
        by (injection H as <-; reflexivity).
      subst s'. cbn [blk rst its].
      eapply to_cfg; [exact (case_refill1 n (ss ++ X) x1 x2 (ss2 ++ X) (us ++ usX) t (r ++ X') T1' H1' H2' X1 X2 M)|].
      flateq.
  - destruct (kindof (r0 :: R0)) as [iR zR|iR wR|iR vR|] eqn:K; try discriminate.
    + apply kindof_Kn in K as [KR Hz].
      destruct (swp (fuel_of ss) ss) as [r|] eqn:E; [|discriminate].
      destruct (swp_spec _ _ _ E) as [us [H1 H2]].
      assert (H1' : flat (ss ++ X) = us_in (us ++ usX) ++ t_in t)
        by (rewrite flat_app, us_in_app, H1, HX1, <- ?app_assoc; reflexivity).
      assert (H2' : flat (r ++ X') = us_out (us ++ usX) ++ t_out t)
        by (rewrite flat_app, us_out_app, H2, HX2, <- ?app_assoc; reflexivity).
      intro H. assert (Hs : s' = (if (zR =? 1)%N && match iR with [] => true | _ => false end
                                  then mk (n + 3) [] (canon r) else mk (n + 2) (iR ++ [(zR - 1)%N]) (canon r)))
        by (injection H as <-; reflexivity).
      subst s'. rewrite KR.
      pose proof (case_plain n iR zR (ss ++ X) (us ++ usX) t (r ++ X') H1' H2' Hz) as C.
      destruct ((zR =? 1)%N && match iR with [] => true | _ => false end); cbn [blk rst its];
        (eapply to_cfg; [exact C|]); flateq.
    + apply kindof_Km in K as [KR Hv].
      destruct (take_plain ss) as [[xa ss2]|] eqn:T2; [|discriminate].
      destruct (2 <=? xa)%N eqn:XA; [|discriminate]. apply N.leb_le in XA.
      destruct (take_n ss2) as [[[i2 z2] ss3]|] eqn:T3; [|discriminate].
      destruct (swp (fuel_of ss3) ss3) as [r|] eqn:E; [|discriminate].
      destruct (swp_spec _ _ _ E) as [us [H1 H2]].
      apply take_plain_spec in T2. apply take_n_spec in T3 as [T3 Hz2]. rewrite T3 in T2.
      assert (T' : flat (ss ++ X) = itm [xa] ++ itm (i2 ++ [z2]) ++ flat (ss3 ++ X))
        by (rewrite !flat_app, T2, <- !app_assoc; reflexivity).
      assert (H1' : flat (ss3 ++ X) = us_in (us ++ usX) ++ t_in t)
        by (rewrite flat_app, us_in_app, H1, HX1, <- ?app_assoc; reflexivity).
      assert (H2' : flat (r ++ X') = us_out (us ++ usX) ++ t_out t)
        by (rewrite flat_app, us_out_app, H2, HX2, <- ?app_assoc; reflexivity).
      intro H. assert (Hs : s' = mk (n + 2) (iR ++ [(vR - 1)%N]) (canon (SD ((xa + 1)%N :: 0%N :: lawN i2 z2) :: r)))
        by (injection H as <-; reflexivity).
      subst s'. rewrite KR. cbn [blk rst its].
      eapply to_cfg; [exact (case_rmerge n iR vR (ss ++ X) xa i2 z2 (ss3 ++ X) (us ++ usX) t (r ++ X') T' H1' H2' Hv XA Hz2)|].
      flateq.
Qed.

(** * Several sweeps *)

Fixpoint SWn (k : nat) (X X' : list seg) : Prop :=
  match k with O => flat X = flat X' | S k => exists Y, SW X Y /\ SWn k Y X' end.
Fixpoint SWPn (k : nat) (A A' : list seg) : Prop :=
  match k with O => flat A = flat A' | S k => exists B, SWP A B /\ SWPn k B A' end.
Definition LSn (k : nat) (s s' : st) : Prop := forall X X', SWn k X X' -> cfgx s X -->* cfgx s' X'.

Lemma cfgx_flat s s' X X' : blk s = blk s' -> rst s = rst s' -> flat (its s) = flat (its s') -> flat X = flat X' ->
  cfgx s X = cfgx s' X'.
Proof. intros B R I E. unfold cfgx. rewrite B, R. apply cfg_flat. rewrite !flat_app, I, E. reflexivity. Qed.

Lemma SW_flat X X0 Y Y0 : SW X Y -> flat X0 = flat X -> flat Y0 = flat Y -> SW X0 Y0.
Proof. intros [us [t [H1 H2]]] E1 E2. exists us, t. rewrite E1, E2. split; assumption. Qed.
Lemma SWP_flat A A0 B B0 : SWP A B -> flat A0 = flat A -> flat B0 = flat B -> SWP A0 B0.
Proof. intros [us [H1 H2]] E1 E2. exists us. rewrite E1, E2. split; assumption. Qed.

Lemma SWn_flatl k X Y Z : SWn k Y Z -> flat X = flat Y -> SWn k X Z.
Proof.
  destruct k as [|k]; cbn [SWn]; intros H E.
  - rewrite E. exact H.
  - destruct H as [W [H1 H2]]. exists W. split; [|exact H2]. eapply SW_flat; [exact H1|exact E|reflexivity].
Qed.
Lemma SWn_flatr k : forall X Y Z, SWn k X Y -> flat Y = flat Z -> SWn k X Z.
Proof.
  induction k as [|k IH]; cbn [SWn]; intros X Y Z H E.
  - rewrite H. exact E.
  - destruct H as [W [H1 H2]]. exists W. split; [exact H1|]. eapply IH; [exact H2|exact E].
Qed.
Lemma SWPn_flatl k A B C : SWPn k B C -> flat A = flat B -> SWPn k A C.
Proof.
  destruct k as [|k]; cbn [SWPn]; intros H E.
  - rewrite E. exact H.
  - destruct H as [W [H1 H2]]. exists W. split; [|exact H2]. eapply SWP_flat; [exact H1|exact E|reflexivity].
Qed.

Lemma cutn k : forall A A' X X', SWPn k A A' -> SWn k X X' -> SWn k (A ++ X) (A' ++ X').
Proof.
  induction k as [|k IH]; intros A A' X X' HA HX; cbn [SWPn SWn] in *.
  - rewrite !flat_app, HA, HX. reflexivity.
  - destruct HA as [B [HA1 HA2]]. destruct HX as [Y [HX1 HX2]].
    exists (B ++ Y). split; [apply cut; assumption|]. apply IH; assumption.
Qed.

Lemma SWn_add a : forall b X Y Z, SWn a X Y -> SWn b Y Z -> SWn (a + b) X Z.
Proof.
  induction a as [|a IH]; intros b X Y Z H1 H2; cbn [SWn Nat.add] in *.
  - eapply SWn_flatl; [exact H2|exact H1].
  - destruct H1 as [W [H1 H3]]. exists W. split; [exact H1|]. eapply IH; [exact H3|exact H2].
Qed.
Lemma SWPn_add a : forall b X Y Z, SWPn a X Y -> SWPn b Y Z -> SWPn (a + b) X Z.
Proof.
  induction a as [|a IH]; intros b X Y Z H1 H2; cbn [SWPn Nat.add] in *.
  - eapply SWPn_flatl; [exact H2|exact H1].
  - destruct H1 as [W [H1 H3]]. exists W. split; [exact H1|]. eapply IH; [exact H3|exact H2].
Qed.
Lemma SWn_split a : forall b X Z, SWn (a + b) X Z -> exists Y, SWn a X Y /\ SWn b Y Z.
Proof.
  induction a as [|a IH]; intros b X Z H; cbn [SWn Nat.add] in *.
  - exists X. split; [reflexivity|exact H].
  - destruct H as [W [H1 H2]]. destruct (IH b W Z H2) as [Y [H3 H4]].
    exists Y. split; [exists W; split; assumption|exact H4].
Qed.

Lemma LSn_add a b s s1 s2 : LSn a s s1 -> LSn b s1 s2 -> LSn (a + b) s s2.
Proof.
  intros H1 H2 X Z HX. destruct (SWn_split a b X Z HX) as [Y [HY1 HY2]].
  eapply evstep_trans; [apply H1; exact HY1|]. apply H2. exact HY2.
Qed.
Lemma LSn_zero s : LSn 0 s s.
Proof. intros X X' E. cbn [SWn] in E. rewrite (cfgx_flat s s X X' eq_refl eq_refl eq_refl E). apply evstep_refl. Qed.
Lemma LSn_one s s' : (forall X X', SW X X' -> cfgx s X -->* cfgx s' X') -> LSn 1 s s'.
Proof.
  intros H X Z [Y [HY HZ]]. cbn [SWn] in HZ.
  eapply evstep_trans; [apply H; exact HY|].
  rewrite (cfgx_flat s' s' Y Z eq_refl eq_refl eq_refl HZ). apply evstep_refl.
Qed.
Lemma LSn_same k s s1 s' : LSn k s s1 -> blk s1 = blk s' -> rst s1 = rst s' -> flat (its s1) = flat (its s') ->
  LSn k s s'.
Proof. intros H B R I X X' HX. rewrite <- (cfgx_flat s1 s' X' X' B R I eq_refl). apply H. exact HX. Qed.

(** * A quiet stretch of the high part in closed form *)

Local Open Scope N_scope.
Definition qitem (r : N) (s : seg) : bool :=
  match s with
  | SP x c => (r =? 0) || ((1 <=? x) && (1 <=? c))
  | SD bs => match kindof bs with Kn (_ :: _) z => r <=? z | _ => r =? 0 end
  end.
Definition qshift (r : N) (s : seg) : seg :=
  match s with
  | SP x c => SP x c
  | SD bs => match kindof bs with Kn (x0 :: mids) z => SD ((x0 + r) :: mids ++ [z - r]) | _ => SD bs end
  end.
Definition qstate (r : N) (s : st) : bool :=
  match kindof (rst s) with Kn iR zR => (r + 1 <=? zR) && forallb (qitem r) (its s) | _ => false end.
Definition shiftS (r : N) (s : st) : st :=
  mk (blk s + 2 * r) (match kindof (rst s) with Kn iR zR => iR ++ [zR - r] | _ => rst s end)
     (map (qshift r) (its s)).
Local Close Scope N_scope.

Lemma unsnoc_snoc i : forall z, unsnoc (i ++ [z]) = Some (i, z).
Proof.
  induction i as [|x i IH]; intro z; [reflexivity|].
  destruct i as [|y i']; [reflexivity|].
  change ((x :: y :: i') ++ [z]) with (x :: ((y :: i') ++ [z])).
  change (unsnoc (x :: ((y :: i') ++ [z]))) with
    (match unsnoc ((y :: i') ++ [z]) with Some (i0, z0) => Some (x :: i0, z0) | None => None end).
  rewrite IH. reflexivity.
Qed.
Lemma kindof_snoc i z : (0 < z)%N -> kindof (i ++ [z]) = Kn i z.
Proof. intro Hz. unfold kindof. rewrite unsnoc_snoc. replace (0 <? z)%N with true by (symmetry; apply N.ltb_lt; lia). reflexivity. Qed.
Lemma kindof_cons_snoc x l z : (0 < z)%N -> kindof (x :: l ++ [z]) = Kn (x :: l) z.
Proof. intro Hz. exact (kindof_snoc (x :: l) z Hz). Qed.
Lemma pl_snoc x l y : pl (x :: l ++ [y]) = SD (x :: l ++ [y]).
Proof. destruct l; reflexivity. Qed.

Lemma qshift_0 x : qshift 0 x = x.
Proof.
  destruct x as [x c|bs]; [reflexivity|]. cbn [qshift].
  destruct (kindof bs) as [i z| | |] eqn:K; try reflexivity. destruct i as [|x0 mids]; [reflexivity|].
  apply kindof_Kn in K as [-> _]. rewrite N.add_0_r, N.sub_0_r. reflexivity.
Qed.
Lemma map_qshift_0 H : map (qshift 0) H = H.
Proof. induction H as [|x H IH]; [reflexivity|]. cbn [map]. rewrite qshift_0, IH. reflexivity. Qed.
Lemma qitem_0 x : qitem 0 x = true.
Proof.
  destruct x as [x c|bs]; [reflexivity|]. cbn [qitem].
  destruct (kindof bs) as [[|x0 mids] z| | |]; try reflexivity. apply N.leb_le. lia.
Qed.
Lemma qitem_shift k x : qitem (1 + k) x = true -> qitem k (qshift 1 x) = true /\ qshift k (qshift 1 x) = qshift (1 + k) x.
Proof.
  intro Q. destruct x as [x c|bs]; cbn [qitem qshift] in *.
  - split; [|reflexivity]. apply Bool.orb_prop in Q as [Q|Q]; [apply N.eqb_eq in Q; lia|].
    apply Bool.orb_true_intro. right. exact Q.
  - destruct (kindof bs) as [[|x0 mids] z| | |] eqn:K; try (apply N.eqb_eq in Q; lia).
    apply N.leb_le in Q.
    destruct (N.eq_dec k 0) as [->|Hk].
    + split; [apply qitem_0|]. rewrite qshift_0. reflexivity.
    + cbn [qitem qshift]. rewrite (kindof_cons_snoc (x0 + 1)%N mids (z - 1)%N) by lia.
      split; [apply N.leb_le; lia|]. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
Qed.

Lemma swp_SP f x c H : swp (S f) (SP x c :: H) =
  if (1 <=? x)%N && (1 <=? c)%N then option_map (cons (SP x c)) (swp f H) else None.
Proof. reflexivity. Qed.
Lemma swp_SD_Kn f bs i z H : kindof bs = Kn i z -> swp (S f) (SD bs :: H) = option_map (cons (pl (lawN i z))) (swp f H).
Proof. intro K. cbn [swp]. rewrite K. reflexivity. Qed.

Lemma swp_quiet H : forallb (qitem 1) H = true -> swp (fuel_of H) H = Some (map (qshift 1) H).
Proof.
  unfold fuel_of. induction H as [|s H IH]; intro Q; [reflexivity|].
  cbn [forallb] in Q. apply andb_prop in Q as [Q1 Q2]. cbn [length].
  destruct s as [x c|bs]; cbn [qitem] in Q1.
  - rewrite swp_SP.
    assert (Q1' : ((1 <=? x)%N && (1 <=? c)%N) = true)
      by (destruct ((1 <=? x)%N && (1 <=? c)%N); [reflexivity|discriminate Q1]).
    rewrite Q1', (IH Q2). reflexivity.
  - destruct (kindof bs) as [i z|i w|i v|] eqn:K; try discriminate Q1.
    destruct i as [|x0 mids]; [discriminate Q1|]. rewrite (swp_SD_Kn _ bs (x0 :: mids) z H K), (IH Q2).
    cbn [option_map map qshift]. rewrite K. cbn [lawN]. rewrite pl_snoc. reflexivity.
Qed.

Lemma stepH_quiet s : qstate 1 s = true -> exists s1, stepH s = Some s1 /\
  blk s1 = blk (shiftS 1 s) /\ rst s1 = rst (shiftS 1 s) /\ flat (its s1) = flat (its (shiftS 1 s)).
Proof.
  destruct s as [n R H]. unfold qstate, shiftS. cbn [blk rst its].
  destruct R as [|r0 R0]; [discriminate|].
  destruct (kindof (r0 :: R0)) as [iR zR| | |] eqn:K; try discriminate. intro Q.
  apply andb_prop in Q as [Q1 Q2]. apply N.leb_le in Q1.
  unfold stepH. cbn [blk rst its]. rewrite K, (swp_quiet H Q2).
  replace ((zR =? 1)%N && match iR with [] => true | _ => false end) with false
    by (replace (zR =? 1)%N with false by (symmetry; apply N.eqb_neq; lia); reflexivity).
  eexists. split; [reflexivity|]. cbn [blk rst its]. split; [lia|]. split; [reflexivity|]. apply canon_flat.
Qed.

Lemma qstate_shift k s : qstate (1 + k) s = true ->
  qstate 1 s = true /\ qstate k (shiftS 1 s) = true /\
  blk (shiftS k (shiftS 1 s)) = blk (shiftS (1 + k) s) /\ rst (shiftS k (shiftS 1 s)) = rst (shiftS (1 + k) s) /\
  its (shiftS k (shiftS 1 s)) = its (shiftS (1 + k) s).
Proof.
  destruct s as [n R H]. unfold qstate, shiftS. cbn [blk rst its].
  destruct (kindof R) as [iR zR| | |] eqn:K; try discriminate. intro Q.
  apply andb_prop in Q as [Q1 Q2]. apply N.leb_le in Q1.
  rewrite (kindof_snoc iR (zR - 1)) by lia.
  assert (A : forall x, In x H -> qitem (1 + k) x = true) by (intros x Hx; exact (proj1 (forallb_forall _ _) Q2 x Hx)).
  split; [apply andb_true_intro; split; [apply N.leb_le; lia|]|].
  { apply forallb_forall. intros x Hx. specialize (A x Hx). destruct x as [x c|bs]; cbn [qitem] in *.
    - apply Bool.orb_prop in A as [A|A]; [apply N.eqb_eq in A; lia|]. apply Bool.orb_true_intro. right. exact A.
    - destruct (kindof bs) as [[|x0 mids] z| | |]; try (apply N.eqb_eq in A; lia). apply N.leb_le. apply N.leb_le in A. lia. }
  split; [apply andb_true_intro; split; [apply N.leb_le; lia|]|].
  { apply forallb_forall. intros x Hx. apply in_map_iff in Hx as [y [<- Hy]]. exact (proj1 (qitem_shift k y (A y Hy))). }
  split; [lia|]. split; [f_equal; f_equal; lia|].
  rewrite map_map. apply map_ext_in. intros x Hx. exact (proj2 (qitem_shift k x (A x Hx))).
Qed.

Lemma batch_sound k : forall s, qstate (N.of_nat k) s = true -> LSn k s (shiftS (N.of_nat k) s).
Proof.
  induction k as [|k IH]; intros s Q.
  - eapply LSn_same; [apply LSn_zero| | |]; destruct s as [n R H]; unfold shiftS, qstate in *; cbn [blk rst its] in *.
    + lia.
    + destruct (kindof R) as [iR zR| | |] eqn:K; try discriminate. apply kindof_Kn in K as [-> _].
      rewrite N.sub_0_r. reflexivity.
    + rewrite map_qshift_0. reflexivity.
  - replace (N.of_nat (S k)) with (1 + N.of_nat k)%N in * by lia.
    destruct (qstate_shift (N.of_nat k) s Q) as [Q1 [Qk [B [R I]]]].
    destruct (stepH_quiet s Q1) as [s1 [E [B1 [R1 I1]]]].
    change (S k) with (1 + k). apply LSn_add with (shiftS 1 s).
    + apply LSn_one. intros X X' HX. rewrite <- (cfgx_flat s1 (shiftS 1 s) X' X' B1 R1 I1 eq_refl).
      exact (stepH_sound s s1 E X X' HX).
    + eapply LSn_same; [exact (IH (shiftS 1 s) Qk)|exact B|exact R|rewrite I; reflexivity].
Qed.

(** * The high part over k sweeps: closed-form stretches between its own events *)

Local Open Scope N_scope.
Definition qtime_item (a : N) (x : seg) : N :=
  match x with SP _ _ => a | SD bs => match kindof bs with Kn (_ :: _) z => N.min a z | _ => 0 end end.
Definition qtime (s : st) : N :=
  match kindof (rst s) with Kn _ zR => fold_left qtime_item (its s) (zR - 1) | _ => 0 end.

Fixpoint hrun (fuel : nat) (k : N) (s : st) : option st :=
  match fuel with
  | O => None
  | S f =>
    if k =? 0 then Some s else
    let r := N.min (qtime s) k in
    if (0 <? r) && qstate r s then hrun f (k - r) (shiftS r s)
    else match stepH s with Some s' => hrun f (k - 1) s' | None => None end
  end.
Local Close Scope N_scope.

Lemma hrun_sound f : forall k s s', hrun f k s = Some s' -> LSn (N.to_nat k) s s'.
Proof.
  induction f as [|f IH]; intros k s s' H; [discriminate|]. cbn [hrun] in H.
  destruct (k =? 0)%N eqn:K0.
  - injection H as <-. apply N.eqb_eq in K0. subst k. apply LSn_zero.
  - apply N.eqb_neq in K0.
    destruct ((0 <? N.min (qtime s) k)%N && qstate (N.min (qtime s) k) s) eqn:Q.
    + apply andb_prop in Q as [Q1 Q2]. apply N.ltb_lt in Q1.
      assert (Hk : N.to_nat k = (N.to_nat (N.min (qtime s) k) + N.to_nat (k - N.min (qtime s) k))%nat) by lia.
      rewrite Hk. apply LSn_add with (shiftS (N.min (qtime s) k) s).
      * pose proof (batch_sound (N.to_nat (N.min (qtime s) k)) s) as BS. rewrite N2Nat.id in BS. exact (BS Q2).
      * apply IH. exact H.
    + destruct (stepH s) as [s1|] eqn:E; [|discriminate].
      assert (Hk : N.to_nat k = (1 + N.to_nat (k - 1))%nat) by lia.
      rewrite Hk. apply LSn_add with s1.
      * apply LSn_one. intros X X' HX. exact (stepH_sound s s1 E X X' HX).
      * apply IH. exact H.
Qed.

(** * Equality of item lists *)

Local Open Scope N_scope.
Fixpoint Nl_eqb (l l' : list N) : bool :=
  match l, l' with [], [] => true | x :: l, x' :: l' => (x =? x') && Nl_eqb l l' | _, _ => false end.
Definition seg_eqb (a b : seg) : bool :=
  match a, b with
  | SP x c, SP x' c' => (x =? x') && (c =? c')
  | SD l, SD l' => Nl_eqb l l'
  | _, _ => false
  end.
Fixpoint segs_eqb (a b : list seg) : bool :=
  match a, b with [], [] => true | x :: a, y :: b => seg_eqb x y && segs_eqb a b | _, _ => false end.
Local Close Scope N_scope.

Lemma Nl_eqb_eq l : forall l', Nl_eqb l l' = true -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|x' l'] H; try discriminate; [reflexivity|].
  cbn [Nl_eqb] in H. apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. rewrite H1, (IH l' H2). reflexivity.
Qed.
Lemma seg_eqb_eq a b : seg_eqb a b = true -> a = b.
Proof.
  destruct a as [x c|l], b as [x' c'|l']; cbn [seg_eqb]; intro H; try discriminate.
  - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1, H2. subst. reflexivity.
  - rewrite (Nl_eqb_eq l l' H). reflexivity.
Qed.
Lemma segs_eqb_eq a : forall b, segs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [segs_eqb] in H. apply andb_prop in H as [H1 H2]. rewrite (seg_eqb_eq x y H1), (IH b H2). reflexivity.
Qed.

(** * The long run of plain items of size 2 and everything right of it: period 2 *)

Lemma SWP_plain x c : (1 <= x)%N -> SWP [SP x c] [SP x c].
Proof.
  intro Hx. exists (repeat (Uitem [] (N.to_nat x - 1)) (N.to_nat c)).
  rewrite us_in_rep, us_out_rep. cbn [flat flat1]. rewrite !app_nil_r.
  assert (U1 : u_in (Uitem [] (N.to_nat x - 1)) = itm [x]).
  { cbn [u_in]. pose proof (H_n [] x ltac:(lia)) as K. cbn [app tn map] in K. symmetry. exact K. }
  assert (U2 : u_out (Uitem [] (N.to_nat x - 1)) = itm [x]).
  { cbn [u_out law]. unfold itm. change (tn [x]) with [N.to_nat x].
    replace (S (N.to_nat x - 1)) with (N.to_nat x) by lia. reflexivity. }
  rewrite U1, U2. split; reflexivity.
Qed.

Local Open Scope N_scope.
Definition tail_ok (P : list seg) : bool :=
  match sw (fuel_of P) P with
  | Some P1 =>
    match sw (fuel_of P1) P1 with
    | Some P2 => segs_eqb (canon P2) (canon (SP 2 2 :: P))
    | None => false
    end
  | None => false
  end.
Local Close Scope N_scope.

Lemma tail_two P b : tail_ok P = true -> SWn 2 (SP 2 b :: P) (SP 2 (b + 2) :: P).
Proof.
  unfold tail_ok. destruct (sw (fuel_of P) P) as [P1|] eqn:E1; [|discriminate].
  destruct (sw (fuel_of P1) P1) as [P2|] eqn:E2; [|discriminate]. intro Q.
  apply segs_eqb_eq in Q.
  assert (F : flat P2 = flat (SP 2 2 :: P))
    by (rewrite <- (canon_flat P2), <- (canon_flat (SP 2 2 :: P)), Q; reflexivity).
  cbn [SWn]. exists (SP 2 b :: P1). split.
  { change (SP 2 b :: P) with ([SP 2 b] ++ P). change (SP 2 b :: P1) with ([SP 2 b] ++ P1).
    apply cut; [apply SWP_plain; lia|exact (sw_spec _ _ _ E1)]. }
  exists (SP 2 b :: P2). split.
  { change (SP 2 b :: P1) with ([SP 2 b] ++ P1). change (SP 2 b :: P2) with ([SP 2 b] ++ P2).
    apply cut; [apply SWP_plain; lia|exact (sw_spec _ _ _ E2)]. }
  cbn [flat flat1]. rewrite F. cbn [flat flat1]. rewrite N2Nat.inj_add, rep_add, <- app_assoc. reflexivity.
Qed.

Lemma tail_k P k : tail_ok P = true -> forall b, SWn (2 * k) (SP 2 b :: P) (SP 2 (b + N.of_nat (2 * k)) :: P).
Proof.
  intro Q. induction k as [|k IH]; intro b.
  - change (2 * 0)%nat with 0%nat. change (N.of_nat 0) with 0%N. rewrite N.add_0_r. exact eq_refl.
  - replace (2 * S k)%nat with (2 + 2 * k)%nat by lia.
    eapply SWn_add; [apply (tail_two P b Q)|].
    replace (b + N.of_nat (2 + 2 * k))%N with (b + 2 + N.of_nat (2 * k))%N by lia. apply IH.
Qed.

(** * The low window: 192 sweeps, checked once per window *)

Fixpoint swpn (k : nat) (A : list seg) : option (list seg) :=
  match k with O => Some A | S k => match swp (fuel_of A) A with Some A1 => swpn k (canon A1) | None => None end end.

Lemma swpn_sound k : forall A A', swpn k A = Some A' -> SWPn k A A'.
Proof.
  induction k as [|k IH]; intros A A' H; cbn [swpn SWPn] in *.
  - injection H as <-. reflexivity.
  - destruct (swp (fuel_of A) A) as [B|] eqn:E; [|discriminate].
    exists (canon B). split; [eapply SWP_flat; [exact (swp_spec _ _ _ E)|reflexivity|apply canon_flat]|].
    apply IH. exact H.
Qed.
Local Open Scope N_scope.
Fixpoint split13 (ss : list seg) : option (list seg * N * list seg) :=
  match ss with
  | [] => None
  | SP x c :: r =>
    if (x =? 2) && (1000 <=? c) then Some ([], c, r)
    else match split13 r with Some (f, c', P) => Some (SP x c :: f, c', P) | None => None end
  | s :: r => match split13 r with Some (f, c', P) => Some (s :: f, c', P) | None => None end
  end.
Local Close Scope N_scope.

Lemma split13_spec ss : forall f c P, split13 ss = Some (f, c, P) -> ss = f ++ SP 2 c :: P.
Proof.
  induction ss as [|s ss IH]; intros f c P H; [discriminate|].
  destruct s as [x c0|bs]; cbn [split13] in H.
  - destruct ((x =? 2)%N && (1000 <=? c0)%N) eqn:E.
    + injection H as <- <- <-. apply andb_prop in E as [E _]. apply N.eqb_eq in E. subst x. reflexivity.
    + destruct (split13 ss) as [[[f' c'] P']|] eqn:S; [|discriminate]. injection H as <- <- <-.
      rewrite (IH f' c' P' eq_refl). reflexivity.
  - destruct (split13 ss) as [[[f' c'] P']|] eqn:S; [|discriminate]. injection H as <- <- <-.
    rewrite (IH f' c' P' eq_refl). reflexivity.
Qed.

(** * Windows: the low levels, from the k-th marker item up to the long run of plain items of size 2, plus 200 of them *)

Definition AW : N := 200.
Definition cache := list (list seg * list seg).
Definition wok (c : cache) : Prop := forall w w', In (w, w') c -> SWPn 192 (w ++ [SP 2 AW]) w'.
Lemma wok_nil : wok [].
Proof. intros w w' []. Qed.

Fixpoint lookup (c : cache) (w : list seg) : option (list seg) :=
  match c with [] => None | (v, v') :: c' => if segs_eqb v w then Some v' else lookup c' w end.
Lemma lookup_in c w w' : lookup c w = Some w' -> In (w, w') c.
Proof.
  induction c as [|[v v'] c IH]; cbn [lookup]; [discriminate|].
  destruct (segs_eqb v w) eqn:E.
  - intro H. injection H as <-. apply segs_eqb_eq in E. subst v. left. reflexivity.
  - intro H. right. exact (IH H).
Qed.
Lemma in_firstn {A} n (l : list A) x : In x (firstn n l) -> In x l.
Proof. intro I. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact I. Qed.

Definition getw (c : cache) (w : list seg) : option (list seg * cache) :=
  match lookup c w with
  | Some w' => Some (w', c)
  | None => match swpn 192 (w ++ [SP 2 AW]) with Some w' => Some (w', firstn 256 ((w, w') :: c)) | None => None end
  end.
Lemma getw_ok c w w' c' : wok c -> getw c w = Some (w', c') -> SWPn 192 (w ++ [SP 2 AW]) w' /\ wok c'.
Proof.
  intro Hc. unfold getw. destruct (lookup c w) as [v|] eqn:L.
  - intro H. injection H as <- <-. split; [exact (Hc w v (lookup_in c w v L))|exact Hc].
  - destruct (swpn 192 (w ++ [SP 2 AW])) as [v|] eqn:E; [|discriminate].
    intro H. assert (V : v = w' /\ firstn 256 ((w, v) :: c) = c').
    { change (Some (v, firstn 256 ((w, v) :: c)) = Some (w', c')) in H.
      split; [exact (f_equal (fun o => match o with Some (a, _) => a | None => v end) H)
             |exact (f_equal (fun o => match o with Some (_, b) => b | None => c end) H)]. }
    destruct V as [<- <-]. split; [exact (swpn_sound _ _ _ E)|].
    intros u u' I. apply in_firstn in I. destruct I as [I|I].
    + injection I as <- <-. exact (swpn_sound _ _ _ E).
    + exact (Hc u u' I).
Qed.

(** [split_k k (rev front) []] cuts [front] just before its k-th SD item from the right. *)
Fixpoint split_k (k : nat) (rv acc : list seg) : option (list seg * list seg) :=
  match rv with
  | [] => None
  | SD bs :: rv' => match k with O => None | S O => Some (rev rv', SD bs :: acc) | S k' => split_k k' rv' (SD bs :: acc) end
  | x :: rv' => split_k k rv' (x :: acc)
  end.
Lemma split_k_spec rv : forall k acc H w, split_k k rv acc = Some (H, w) -> rev rv ++ acc = H ++ w.
Proof.
  induction rv as [|x rv IH]; intros k acc H w E; [discriminate|].
  destruct x as [x c|bs]; cbn [split_k] in E.
  - cbn [rev]. rewrite <- app_assoc. exact (IH _ _ _ _ E).
  - destruct k as [|[|k]]; [discriminate| |].
    + injection E as <- <-. cbn [rev]. rewrite <- app_assoc. reflexivity.
    + cbn [rev]. rewrite <- app_assoc. exact (IH _ _ _ _ E).
Qed.

(** * One macro tick: 192 sweeps of  H ++ W ++ SP 2 n :: P *)

Lemma macro_core s H w w2 n P s' : its s = H ++ w ++ SP 2 n :: P -> (AW + 1 <= n)%N -> tail_ok P = true ->
  SWPn 192 (w ++ [SP 2 AW]) w2 -> hrun 2000 192 (mk (blk s) (rst s) H) = Some s' ->
  cfg s -->* cfg (mk (blk s') (rst s') (canon (its s' ++ w2 ++ SP 2 (n - AW + 192) :: P))).
Proof.
  intros Hs C1 TP SWW HR.
  pose proof (hrun_sound _ _ _ _ HR) as LS. change (N.to_nat 192) with 192%nat in LS.
  pose proof (cutn 192 _ _ _ _ SWW (tail_k P 96 TP (n - AW)%N)) as SWX.
  change (N.of_nat (2 * 96)) with 192%N in SWX.
  specialize (LS _ _ SWX). unfold cfgx in LS. cbn [blk rst its] in LS.
  destruct s as [b R ss]. cbn [blk rst its] in *.
  eapply to_cfg; [rewrite (cfg_flat b R ss (H ++ (w ++ [SP 2 AW]) ++ SP 2 (n - AW)%N :: P)); [exact LS|]|].
  - rewrite Hs. rewrite !flat_app. cbn [flat flat1]. rewrite app_nil_r.
    replace (N.to_nat n) with (N.to_nat AW + N.to_nat (n - AW))%nat by lia. rewrite rep_add.
    rewrite <- !app_assoc. reflexivity.
  - rewrite canon_flat. reflexivity.
Qed.

Local Open Scope N_scope.
Fixpoint tryk (ks : list nat) (c : cache) (s : st) (front : list seg) (n : N) (P : list seg) : option st * cache :=
  match ks with
  | [] => (None, c)
  | k :: ks' =>
    match split_k k (rev front) [] with
    | Some (H, w) =>
      match getw c w with
      | Some (w2, c') =>
        match hrun 2000 192 (mk (blk s) (rst s) H) with
        | Some s' => (Some (mk (blk s') (rst s') (canon (its s' ++ w2 ++ SP 2 (n - AW + 192) :: P))), c')
        | None => tryk ks' c' s front n P
        end
      | None => tryk ks' c s front n P
      end
    | None => tryk ks' c s front n P
    end
  end.

Definition macro (c : cache) (s : st) : option st * cache :=
  match split13 (its s) with
  | Some (front, n, P) => if (AW + 1 <=? n) && tail_ok P then tryk [6; 7; 8; 9]%nat c s front n P else (None, c)
  | None => (None, c)
  end.
Local Close Scope N_scope.

Lemma tryk_sound ks : forall c s front n P o c2, wok c -> its s = front ++ SP 2 n :: P -> (AW + 1 <= n)%N ->
  tail_ok P = true -> tryk ks c s front n P = (o, c2) -> wok c2 /\ (forall s2, o = Some s2 -> cfg s -->* cfg s2).
Proof.
  induction ks as [|k ks IH]; intros c s front n P o c2 Hc Hs C1 TP E; cbn [tryk] in E.
  - injection E as <- <-. split; [exact Hc|intros ? E'; discriminate E'].
  - destruct (split_k k (rev front) []) as [[H w]|] eqn:SK; [|exact (IH _ _ _ _ _ _ _ Hc Hs C1 TP E)].
    destruct (getw c w) as [[w2 c']|] eqn:G; [|exact (IH _ _ _ _ _ _ _ Hc Hs C1 TP E)].
    destruct (getw_ok c w w2 c' Hc G) as [SWW Hc'].
    destruct (hrun 2000 192 (mk (blk s) (rst s) H)) as [s'|] eqn:HR; [|exact (IH _ _ _ _ _ _ _ Hc' Hs C1 TP E)].
    injection E as <- <-. split; [exact Hc'|]. intros s2 E2. injection E2 as <-.
    apply split_k_spec in SK. rewrite rev_involutive, app_nil_r in SK.
    apply (macro_core s H w w2 n P s'); [rewrite Hs, SK, <- app_assoc; reflexivity|exact C1|exact TP|exact SWW|exact HR].
Qed.

Lemma macro_sound c s o c2 : wok c -> macro c s = (o, c2) -> wok c2 /\ (forall s2, o = Some s2 -> cfg s -->* cfg s2).
Proof.
  intro Hc. unfold macro. destruct (split13 (its s)) as [[[front n] P]|] eqn:Sp.
  - destruct ((AW + 1 <=? n)%N && tail_ok P) eqn:C.
    + apply andb_prop in C as [C1 TP]. apply N.leb_le in C1.
      intro E. exact (tryk_sound _ _ _ _ _ _ _ _ Hc (split13_spec _ _ _ _ Sp) C1 TP E).
    + intro E. injection E as <- <-. split; [exact Hc|intros ? E'; discriminate E'].
  - intro E. injection E as <- <-. split; [exact Hc|intros ? E'; discriminate E'].
Qed.

(** * The run: a macro tick where one applies, one sweep otherwise *)

Local Open Scope N_scope.
Definition tickR (x : st * N * cache) : st * N * cache :=
  let '(s, rem, c) := x in
  if rem =? 0 then x else
  let (o, c') := (if 192 <=? rem then macro c s else (None, c)) in
  match o with
  | Some s' => (s', rem - 192, c')
  | None => match step s with Some s' => (s', rem - 1, c') | None => (s, rem, c') end
  end.
Local Close Scope N_scope.

Lemma tickR_sound s rem c s' rem' c' : wok c -> tickR (s, rem, c) = (s', rem', c') -> wok c' /\ cfg s -->* cfg s'.
Proof.
  intro Hc. unfold tickR. cbv beta iota.
  destruct (rem =? 0)%N; cbv beta iota.
  - intro E. injection E as <- <- <-. split; [exact Hc|apply evstep_refl].
  - destruct (if (192 <=? rem)%N then macro c s else (None, c)) as [o c1] eqn:M. cbv beta iota.
    assert (K : wok c1 /\ (forall s2, o = Some s2 -> cfg s -->* cfg s2)).
    { destruct (192 <=? rem)%N; [exact (macro_sound c s o c1 Hc M)|].
      injection M as <- <-. split; [exact Hc|intros ? E'; discriminate E']. }
    destruct K as [Hc1 Ko]. destruct o as [s1|]; cbv beta iota.
    + intro E. injection E as <- <- <-. split; [exact Hc1|exact (Ko s1 eq_refl)].
    + destruct (step s) as [s1|] eqn:St; cbv beta iota; intro E; injection E as <- <- <-; split; try exact Hc1.
      * exact (step_sound s s1 St).
      * apply evstep_refl.
Qed.

Fixpoint runP (p : positive) (x : st * N * cache) : st * N * cache :=
  match p with
  | xH => tickR x
  | xO p' => runP p' (runP p' x)
  | xI p' => runP p' (runP p' (tickR x))
  end.

Lemma runP_sound p : forall s rem c s' rem' c', wok c -> runP p (s, rem, c) = (s', rem', c') -> wok c' /\ cfg s -->* cfg s'.
Proof.
  induction p as [p IH|p IH|]; intros s rem c s' rem' c' Hc E; cbn [runP] in E.
  - destruct (tickR (s, rem, c)) as [[s1 r1] c1] eqn:E1.
    destruct (tickR_sound _ _ _ _ _ _ Hc E1) as [Hc1 R1].
    destruct (runP p (s1, r1, c1)) as [[s2 r2] c2] eqn:E2.
    destruct (IH _ _ _ _ _ _ Hc1 E2) as [Hc2 R2].
    destruct (IH _ _ _ _ _ _ Hc2 E) as [Hc3 R3].
    split; [exact Hc3|]. eapply evstep_trans; [exact R1|]. eapply evstep_trans; [exact R2|exact R3].
  - destruct (runP p (s, rem, c)) as [[s1 r1] c1] eqn:E1.
    destruct (IH _ _ _ _ _ _ Hc E1) as [Hc1 R1].
    destruct (IH _ _ _ _ _ _ Hc1 E) as [Hc2 R2].
    split; [exact Hc2|]. eapply evstep_trans; [exact R1|exact R2].
  - exact (tickR_sound _ _ _ _ _ _ Hc E).
Qed.

Definition st_eqb (a b : st) : bool := (blk a =? blk b)%N && Nl_eqb (rst a) (rst b) && segs_eqb (its a) (its b).
Lemma st_eqb_eq a b : st_eqb a b = true -> a = b.
Proof.
  destruct a as [n R l], b as [n' R' l']. unfold st_eqb. cbn [blk rst its]. intro E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply N.eqb_eq in E1. apply Nl_eqb_eq in E2. apply segs_eqb_eq in E3. subst. reflexivity.
Qed.

Lemma run_main p s0 k s1 :
  (let '(s, r, _) := runP p (s0, k, []) in (r =? 0)%N && st_eqb s s1) = true -> cfg s0 -->* cfg s1.
Proof.
  destruct (runP p (s0, k, [])) as [[s r] c] eqn:E. cbv beta iota. intro Q. apply andb_prop in Q as [_ Q].
  apply st_eqb_eq in Q. subst s1. exact (proj2 (runP_sound p s0 k [] s r c wok_nil E)).
Qed.
End P_M269m.

Section P_STATES.
Local Open Scope N_scope.
Definition s_110596984 : st := mk 18210720 [30926190; 0; 3477552] [SP 12582911 5; SD [8703710; 0; 3879201]; SP 6291455 5; SD [4658317; 1633138]; SP 6291455 1; SD [4791926; 0; 1499529]; SP 3145727 1; SD [1852006; 0; 1293721]; SD [1368951; 0; 203912]; SP 786431 4; SD [749889; 0; 36542]; SP 393215 2; SD [313790; 0; 79425]; SP 196607 7; SD [141268; 55339]; SP 196607 1; SP 193535 1; SD [177789; 18818]; SP 196607 2; SD [145379; 0; 51228]; SP 98303 7; SD [7591; 90712]; SD [74900; 0; 23403]; SP 49151 4; SD [47843; 0; 1308]; SP 24575 4; SD [15950; 8625]; SP 24575 1; SD [19873; 0; 4702]; SP 12287 16; SD [7007; 5280]; SP 12287 4; SD [3713; 8574]; SP 12287 4; SD [6443; 5844]; SP 12287 9; SD [5166; 7121]; SP 12287 12; SD [8905; 3382]; SP 12287 4; SD [8077; 4210]; SP 12287 2; SD [11448; 839]; SP 12287 5; SD [7881; 0; 4406]; SP 6143 8; SD [3629; 2514]; SP 6143 4; SD [4157; 1986]; SP 6143 2; SD [4607; 0; 0]; SD [2036; 1035]; SP 3071 18; SD [2194; 0; 877]; SD [679; 856]; SP 1535 13; SD [1394; 0; 141]; SP 767 21; SD [450; 0; 317]; SP 383 8; SD [369; 0; 14]; SP 191 4; SD [104; 0; 87]; SP 95 10; SD [70; 0; 25]; SP 47 10; SD [35; 0; 12]; SP 23 5; SD [19; 0; 4]; SP 11 9; SD [9; 0; 2]; SP 5 13; SD [5; 0; 0]; SP 2 26133524; SD [2; 0]; SP 2 6265984; SD [1; 1]; SP 2 3239650; SD [2; 0]; SP 2 248432; SD [1; 1]; SP 2 407346; SD [2; 0]; SP 2 565312; SD [1; 1]; SP 2 5338; SD [2; 0]; SP 2 46; SD [1; 1]; SP 2 18; SD [2; 0]; SP 2 12; SD [1; 1]].
End P_STATES.

Lemma main_run : cfg s100 -->* cfg s_110596984.
Proof. apply (run_main 2097152 s100 110596884). vm_compute. reflexivity. Qed.

(* The end game below compacts the heap between its larger lemmas: this keeps the peak under 1 GB with the
   default GC settings. *)
Optimize Heap.

Section P_M269t.
Local Open Scope string_scope.
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) "&" constr(e) constr(f) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else O)
    (fun s => if String.eqb s "e" then e else if String.eqb s "f" then f else 0inf)).
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) "&" constr(f) constr(g) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else
              if String.eqb s "e" then e else O)
    (fun s => if String.eqb s "f" then f else if String.eqb s "g" then g else 0inf)).
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) "&" constr(g) constr(h) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else
              if String.eqb s "e" then e else if String.eqb s "f" then f else O)
    (fun s => if String.eqb s "g" then g else if String.eqb s "h" then h else 0inf)).
Local Close Scope string_scope.
Local Open Scope string_scope.
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) "&" constr(h) constr(i) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else
              if String.eqb s "e" then e else if String.eqb s "f" then f else
              if String.eqb s "g" then g else O)
    (fun s => if String.eqb s "h" then h else if String.eqb s "i" then i else 0inf)).
Tactic Notation "es'" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) "&" constr(i) constr(j) :=
  (es_v3_pre; es_v3_nmp_smp
    (fun s => if String.eqb s "a" then a else if String.eqb s "b" then b else
              if String.eqb s "c" then c else if String.eqb s "d" then d else
              if String.eqb s "e" then e else if String.eqb s "f" then f else
              if String.eqb s "g" then g else if String.eqb s "h" then h else O)
    (fun s => if String.eqb s "i" then i else if String.eqb s "j" then j else 0inf)).
Local Close Scope string_scope.


(* the right pass of the record sweep over the marker item's tail, Y (two blocks) and Y2 *)
Optimize Heap.
Lemma EXR a b c l r :
  l <* [1;0;0;1;0;0] <* [1;0] <* [1;0] <* [1;0] {{B}}> [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0] *>
    [1;1;1;0] *> [1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^a <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c & l r. Qed.

Optimize Heap.
Lemma turn1 a b c d e f g h l r :
  l <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^h <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0] <* [1;0;0;1;0;0]^^g <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^f <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^e <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^d <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;1;0;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn2 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn3 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn4 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn5 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn6 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn7 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn8 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn9 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn10 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

Optimize Heap.
Lemma turn11 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof. es' a b c d e f g h & l r. Qed.

(* the last leftward leg ends in state F reading 1 *)
Optimize Heap.
Lemma H12 a b c d e f g h l r :
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r -->*
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{F}}> [1] *> [1;1;0;1;1;1;1;1;1;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^g *> [0;1;1;1;1;1;1;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^f *> [0;1;1;1;1;1;1;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^e *> [0;1;1;1;1;1;1;1;0;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^d *> [0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^a *> [0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^b *> [0;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] *> [1;1;1;1;1;1]^^c *> [0] *> r.
Proof. es' a b c d e f g h & l r. Qed.

(* the left side after turn k, without the pending T8 of Y2 *)
Definition Wd1 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd1_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd1 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd2 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd2_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd2 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd3 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd3_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd3 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd4 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd4_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd4 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd5 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd5_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd5 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd6 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd6_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd6 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd7 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd7_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd7 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd8 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd8_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd8 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd9 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd9_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd9 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd10 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd10_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd10 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.
Definition Wd11 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma Wd11_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r = Wd11 a b c d e f g h l <* T8 {{B}}> r.
Proof. reflexivity. Qed.

(* the left side of turn k's input, and the bridge from turn k's output (two blocks of every power shown) *)
Definition INL2 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL2_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL2 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL3 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL3_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL3 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL4 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL4_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL4 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL5 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL5_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL5 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL6 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL6_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL6 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL7 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL7_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL7 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL8 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL8_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL8 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL9 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL9_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL9 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL10 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL10_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL10 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL11 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL11_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL11 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Definition INL12 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0].
Optimize Heap.
Lemma INL12_eq a b c d e f g h (l r : side) : l <* [1;1;0;0] <* [0;1;0;0;1;0]^^h <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;1;0;1;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^g <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^f <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^e <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;1;0;0;1;0;0;1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^d <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <{{C}} [0;1;0] *> r = INL12 a b c d e f g h l <{{C}} [0;1;0] *> r.
Proof. reflexivity. Qed.
Optimize Heap.
Lemma Bridge1 a b c d e f g h (l : side) :
  Wd1 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL2 a b c d e f g h l.
Proof. unfold Wd1, INL2. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge2 a b c d e f g h (l : side) :
  Wd2 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL3 a b c d e f g h l.
Proof. unfold Wd2, INL3. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge3 a b c d e f g h (l : side) :
  Wd3 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL4 a b c d e f g h l.
Proof. unfold Wd3, INL4. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge4 a b c d e f g h (l : side) :
  Wd4 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL5 a b c d e f g h l.
Proof. unfold Wd4, INL5. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge5 a b c d e f g h (l : side) :
  Wd5 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL6 a b c d e f g h l.
Proof. unfold Wd5, INL6. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge6 a b c d e f g h (l : side) :
  Wd6 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL7 a b c d e f g h l.
Proof. unfold Wd6, INL7. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge7 a b c d e f g h (l : side) :
  Wd7 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL8 a b c d e f g h l.
Proof. unfold Wd7, INL8. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge8 a b c d e f g h (l : side) :
  Wd8 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL9 a b c d e f g h l.
Proof. unfold Wd8, INL9. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge9 a b c d e f g h (l : side) :
  Wd9 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL10 a b c d e f g h l.
Proof. unfold Wd9, INL10. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge10 a b c d e f g h (l : side) :
  Wd10 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL11 a b c d e f g h l.
Proof. unfold Wd10, INL11. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
Optimize Heap.
Lemma Bridge11 a b c d e f g h (l : side) :
  Wd11 (2+a) (2+b) (2+c) (2+d) (2+e) (2+f) (2+g) (2+h) l = INL12 a b c d e f g h l.
Proof. unfold Wd11, INL12. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.

Definition INL1 (a b c d e f g h : nat) (l : side) : side :=
  l <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^h <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0] <* [1;0;0;1;0;0]^^g <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^f <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^e <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;0;0;1;0;0;1;0;1;1;0;0] <* [1;0;0;1;0;0]^^d <* [1;0;0;1;0;0] <* [1;0;0;1;0;0] <* [1;1;0;0] <* [0;1;0;0;1;0]^^a <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^b <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^c <* [0;1;0;0;1;0] <* [0;1;0;0;1;0] <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0].
End P_M269t.

Section P_M269j.
(** * A partial sweep: right to END and back, over the items right of the region *)

Definition nxt (ss : list seg) : option (list seg) := option_map canon (sw (fuel_of ss) ss).

Lemma partial_nxt ss ss' l : nxt ss = Some ss' ->
  l <* T8 {{B}}> flat ss *> ENDc *> 0inf -->* l <{{C}} [0;1;0] *> flat ss' *> ENDc *> 0inf.
Proof.
  unfold nxt. destruct (sw (fuel_of ss) ss) as [r|] eqn:E; [|discriminate]. cbn [option_map]. intro H.
  injection H as <-. destruct (sw_spec _ _ _ E) as [us [t [H1 H2]]].
  rewrite canon_flat, H1, H2, !Str_app_assoc.
  eapply evstep_trans; [apply us_right|]. eapply evstep_trans; [apply t_turn|]. apply us_left.
Qed.

(** * The items right of the region, leg by leg *)

Definition getl (o : option (list seg)) : list seg := match o with Some s => s | None => [] end.
Definition R0 : list seg := SP 3071 17 :: skipn 53 (its s_110596984).

Definition R1 : list seg := Eval vm_compute in getl (nxt R0).
Definition R2 : list seg := Eval vm_compute in getl (nxt R1).
Definition R3 : list seg := Eval vm_compute in getl (nxt R2).
Definition R4 : list seg := Eval vm_compute in getl (nxt R3).
Definition R5 : list seg := Eval vm_compute in getl (nxt R4).
Definition R6 : list seg := Eval vm_compute in getl (nxt R5).
Definition R7 : list seg := Eval vm_compute in getl (nxt R6).
Definition R8 : list seg := Eval vm_compute in getl (nxt R7).
Definition R9 : list seg := Eval vm_compute in getl (nxt R8).
Definition R10 : list seg := Eval vm_compute in getl (nxt R9).
Definition R11 : list seg := Eval vm_compute in getl (nxt R10).
Definition R12 : list seg := Eval vm_compute in getl (nxt R11).
Lemma nxt0 : nxt R0 = Some R1. Proof. vm_compute. reflexivity. Qed.
Lemma nxt1 : nxt R1 = Some R2. Proof. vm_compute. reflexivity. Qed.
Lemma nxt2 : nxt R2 = Some R3. Proof. vm_compute. reflexivity. Qed.
Lemma nxt3 : nxt R3 = Some R4. Proof. vm_compute. reflexivity. Qed.
Lemma nxt4 : nxt R4 = Some R5. Proof. vm_compute. reflexivity. Qed.
Lemma nxt5 : nxt R5 = Some R6. Proof. vm_compute. reflexivity. Qed.
Lemma nxt6 : nxt R6 = Some R7. Proof. vm_compute. reflexivity. Qed.
Lemma nxt7 : nxt R7 = Some R8. Proof. vm_compute. reflexivity. Qed.
Lemma nxt8 : nxt R8 = Some R9. Proof. vm_compute. reflexivity. Qed.
Lemma nxt9 : nxt R9 = Some R10. Proof. vm_compute. reflexivity. Qed.
Lemma nxt10 : nxt R10 = Some R11. Proof. vm_compute. reflexivity. Qed.
Lemma nxt11 : nxt R11 = Some R12. Proof. vm_compute. reflexivity. Qed.

(** * The turns: each left pass turns in the region, the last one halts there *)

Optimize Heap.
Lemma step1 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL2 2030 1029 3065 4602 6138 6138 1981 4153 L <{{C}} [0;1;0] *> r') -> halts tm (INL1 2032 1031 3067 4604 6140 6140 1983 4155 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn1 2032 1031 3067 4604 6140 6140 1983 4155 L r)].
  rewrite Wd1_eq. eapply halts_evstep; [|apply P].
  replace (Wd1 2032 1031 3067 4604 6140 6140 1983 4155 L) with (INL2 2030 1029 3065 4602 6138 6138 1981 4153 L) by (symmetry; apply (Bridge1 2030 1029 3065 4602 6138 6138 1981 4153 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step2 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL3 2028 1027 3063 4600 6136 6136 1979 4151 L <{{C}} [0;1;0] *> r') -> halts tm (INL2 2030 1029 3065 4602 6138 6138 1981 4153 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn2 2030 1029 3065 4602 6138 6138 1981 4153 L r)].
  rewrite Wd2_eq. eapply halts_evstep; [|apply P].
  replace (Wd2 2030 1029 3065 4602 6138 6138 1981 4153 L) with (INL3 2028 1027 3063 4600 6136 6136 1979 4151 L) by (symmetry; apply (Bridge2 2028 1027 3063 4600 6136 6136 1979 4151 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step3 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL4 2026 1025 3061 4598 6134 6134 1977 4149 L <{{C}} [0;1;0] *> r') -> halts tm (INL3 2028 1027 3063 4600 6136 6136 1979 4151 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn3 2028 1027 3063 4600 6136 6136 1979 4151 L r)].
  rewrite Wd3_eq. eapply halts_evstep; [|apply P].
  replace (Wd3 2028 1027 3063 4600 6136 6136 1979 4151 L) with (INL4 2026 1025 3061 4598 6134 6134 1977 4149 L) by (symmetry; apply (Bridge3 2026 1025 3061 4598 6134 6134 1977 4149 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step4 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL5 2024 1023 3059 4596 6132 6132 1975 4147 L <{{C}} [0;1;0] *> r') -> halts tm (INL4 2026 1025 3061 4598 6134 6134 1977 4149 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn4 2026 1025 3061 4598 6134 6134 1977 4149 L r)].
  rewrite Wd4_eq. eapply halts_evstep; [|apply P].
  replace (Wd4 2026 1025 3061 4598 6134 6134 1977 4149 L) with (INL5 2024 1023 3059 4596 6132 6132 1975 4147 L) by (symmetry; apply (Bridge4 2024 1023 3059 4596 6132 6132 1975 4147 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step5 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL6 2022 1021 3057 4594 6130 6130 1973 4145 L <{{C}} [0;1;0] *> r') -> halts tm (INL5 2024 1023 3059 4596 6132 6132 1975 4147 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn5 2024 1023 3059 4596 6132 6132 1975 4147 L r)].
  rewrite Wd5_eq. eapply halts_evstep; [|apply P].
  replace (Wd5 2024 1023 3059 4596 6132 6132 1975 4147 L) with (INL6 2022 1021 3057 4594 6130 6130 1973 4145 L) by (symmetry; apply (Bridge5 2022 1021 3057 4594 6130 6130 1973 4145 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step6 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL7 2020 1019 3055 4592 6128 6128 1971 4143 L <{{C}} [0;1;0] *> r') -> halts tm (INL6 2022 1021 3057 4594 6130 6130 1973 4145 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn6 2022 1021 3057 4594 6130 6130 1973 4145 L r)].
  rewrite Wd6_eq. eapply halts_evstep; [|apply P].
  replace (Wd6 2022 1021 3057 4594 6130 6130 1973 4145 L) with (INL7 2020 1019 3055 4592 6128 6128 1971 4143 L) by (symmetry; apply (Bridge6 2020 1019 3055 4592 6128 6128 1971 4143 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step7 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL8 2018 1017 3053 4590 6126 6126 1969 4141 L <{{C}} [0;1;0] *> r') -> halts tm (INL7 2020 1019 3055 4592 6128 6128 1971 4143 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn7 2020 1019 3055 4592 6128 6128 1971 4143 L r)].
  rewrite Wd7_eq. eapply halts_evstep; [|apply P].
  replace (Wd7 2020 1019 3055 4592 6128 6128 1971 4143 L) with (INL8 2018 1017 3053 4590 6126 6126 1969 4141 L) by (symmetry; apply (Bridge7 2018 1017 3053 4590 6126 6126 1969 4141 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step8 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL9 2016 1015 3051 4588 6124 6124 1967 4139 L <{{C}} [0;1;0] *> r') -> halts tm (INL8 2018 1017 3053 4590 6126 6126 1969 4141 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn8 2018 1017 3053 4590 6126 6126 1969 4141 L r)].
  rewrite Wd8_eq. eapply halts_evstep; [|apply P].
  replace (Wd8 2018 1017 3053 4590 6126 6126 1969 4141 L) with (INL9 2016 1015 3051 4588 6124 6124 1967 4139 L) by (symmetry; apply (Bridge8 2016 1015 3051 4588 6124 6124 1967 4139 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step9 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL10 2014 1013 3049 4586 6122 6122 1965 4137 L <{{C}} [0;1;0] *> r') -> halts tm (INL9 2016 1015 3051 4588 6124 6124 1967 4139 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn9 2016 1015 3051 4588 6124 6124 1967 4139 L r)].
  rewrite Wd9_eq. eapply halts_evstep; [|apply P].
  replace (Wd9 2016 1015 3051 4588 6124 6124 1967 4139 L) with (INL10 2014 1013 3049 4586 6122 6122 1965 4137 L) by (symmetry; apply (Bridge9 2014 1013 3049 4586 6122 6122 1965 4137 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step10 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL11 2012 1011 3047 4584 6120 6120 1963 4135 L <{{C}} [0;1;0] *> r') -> halts tm (INL10 2014 1013 3049 4586 6122 6122 1965 4137 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn10 2014 1013 3049 4586 6122 6122 1965 4137 L r)].
  rewrite Wd10_eq. eapply halts_evstep; [|apply P].
  replace (Wd10 2014 1013 3049 4586 6122 6122 1965 4137 L) with (INL11 2012 1011 3047 4584 6120 6120 1963 4135 L) by (symmetry; apply (Bridge10 2012 1011 3047 4584 6120 6120 1963 4135 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step11 L (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  halts tm (INL12 2010 1009 3045 4582 6118 6118 1961 4133 L <{{C}} [0;1;0] *> r') -> halts tm (INL11 2012 1011 3047 4584 6120 6120 1963 4135 L <{{C}} [0;1;0] *> r).
Proof.
  intro H. eapply halts_evstep; [|exact (turn11 2012 1011 3047 4584 6120 6120 1963 4135 L r)].
  rewrite Wd11_eq. eapply halts_evstep; [|apply P].
  replace (Wd11 2012 1011 3047 4584 6120 6120 1963 4135 L) with (INL12 2010 1009 3045 4582 6118 6118 1961 4133 L) by (symmetry; apply (Bridge11 2010 1009 3045 4582 6118 6118 1961 4133 L)).
  exact H.
Qed.
Optimize Heap.
Lemma step12 L (r : side) : halts tm (INL12 2010 1009 3045 4582 6118 6118 1961 4133 L <{{C}} [0;1;0] *> r).
Proof. eapply halts_evstep; [|exact (H12 2010 1009 3045 4582 6118 6118 1961 4133 L r)]. apply halted_halts. reflexivity. Qed.

Definition Rt1 : side := flat R1 *> ENDc *> 0inf.
Definition Rt2 : side := flat R2 *> ENDc *> 0inf.
Definition Rt3 : side := flat R3 *> ENDc *> 0inf.
Definition Rt4 : side := flat R4 *> ENDc *> 0inf.
Definition Rt5 : side := flat R5 *> ENDc *> 0inf.
Definition Rt6 : side := flat R6 *> ENDc *> 0inf.
Definition Rt7 : side := flat R7 *> ENDc *> 0inf.
Definition Rt8 : side := flat R8 *> ENDc *> 0inf.
Definition Rt9 : side := flat R9 *> ENDc *> 0inf.
Definition Rt10 : side := flat R10 *> ENDc *> 0inf.
Definition Rt11 : side := flat R11 *> ENDc *> 0inf.
Definition Rt12 : side := flat R12 *> ENDc *> 0inf.
Optimize Heap.
Lemma PS1 l : l <* T8 {{B}}> Rt1 -->* l <{{C}} [0;1;0] *> Rt2.
Proof. unfold Rt1, Rt2. apply partial_nxt. exact nxt1. Qed.
Optimize Heap.
Lemma PS2 l : l <* T8 {{B}}> Rt2 -->* l <{{C}} [0;1;0] *> Rt3.
Proof. unfold Rt2, Rt3. apply partial_nxt. exact nxt2. Qed.
Optimize Heap.
Lemma PS3 l : l <* T8 {{B}}> Rt3 -->* l <{{C}} [0;1;0] *> Rt4.
Proof. unfold Rt3, Rt4. apply partial_nxt. exact nxt3. Qed.
Optimize Heap.
Lemma PS4 l : l <* T8 {{B}}> Rt4 -->* l <{{C}} [0;1;0] *> Rt5.
Proof. unfold Rt4, Rt5. apply partial_nxt. exact nxt4. Qed.
Optimize Heap.
Lemma PS5 l : l <* T8 {{B}}> Rt5 -->* l <{{C}} [0;1;0] *> Rt6.
Proof. unfold Rt5, Rt6. apply partial_nxt. exact nxt5. Qed.
Optimize Heap.
Lemma PS6 l : l <* T8 {{B}}> Rt6 -->* l <{{C}} [0;1;0] *> Rt7.
Proof. unfold Rt6, Rt7. apply partial_nxt. exact nxt6. Qed.
Optimize Heap.
Lemma PS7 l : l <* T8 {{B}}> Rt7 -->* l <{{C}} [0;1;0] *> Rt8.
Proof. unfold Rt7, Rt8. apply partial_nxt. exact nxt7. Qed.
Optimize Heap.
Lemma PS8 l : l <* T8 {{B}}> Rt8 -->* l <{{C}} [0;1;0] *> Rt9.
Proof. unfold Rt8, Rt9. apply partial_nxt. exact nxt8. Qed.
Optimize Heap.
Lemma PS9 l : l <* T8 {{B}}> Rt9 -->* l <{{C}} [0;1;0] *> Rt10.
Proof. unfold Rt9, Rt10. apply partial_nxt. exact nxt9. Qed.
Optimize Heap.
Lemma PS10 l : l <* T8 {{B}}> Rt10 -->* l <{{C}} [0;1;0] *> Rt11.
Proof. unfold Rt10, Rt11. apply partial_nxt. exact nxt10. Qed.
Optimize Heap.
Lemma PS11 l : l <* T8 {{B}}> Rt11 -->* l <{{C}} [0;1;0] *> Rt12.
Proof. unfold Rt11, Rt12. apply partial_nxt. exact nxt11. Qed.
Optimize Heap.
Lemma endgame_from L : halts tm (INL1 2032 1031 3067 4604 6140 6140 1983 4155 L <{{C}} [0;1;0] *> Rt1).
Proof.
  apply (step1 L _ _ (PS1)).
  apply (step2 L _ _ (PS2)).
  apply (step3 L _ _ (PS3)).
  apply (step4 L _ _ (PS4)).
  apply (step5 L _ _ (PS5)).
  apply (step6 L _ _ (PS6)).
  apply (step7 L _ _ (PS7)).
  apply (step8 L _ _ (PS8)).
  apply (step9 L _ _ (PS9)).
  apply (step10 L _ _ (PS10)).
  apply (step11 L _ _ (PS11)).
  apply step12.
Qed.
End P_M269j.

Section P_M269k1.
Optimize Heap.
(** * The items at the last record: pre48, the region, the items right of the region *)

Definition pre48 : list seg := firstn 48 (its s_110596984).
Lemma its_split : its s_110596984 =
  pre48 ++ SD [4157; 1986]%N :: SP 6143 2 :: SD [4607; 0; 0]%N :: SD [2036; 1035]%N :: SP 3071 18 :: skipn 53 (its s_110596984).
Proof. vm_compute. reflexivity. Qed.

Lemma flat_last : flat (its s_110596984) =
  flat pre48 ++ itm [4157; 1986]%N ++ itm [6143%N] ++ itm [6143%N] ++ itm [4607; 0; 0]%N ++ itm [2036; 1035]%N ++
  itm [3071%N] ++ flat R0.
Proof.
  rewrite its_split, flat_app. apply (f_equal (app (flat pre48))). unfold R0. cbn [flat flat1].
  change (N.to_nat 2) with 2%nat. change (N.to_nat 18) with 18%nat. change (N.to_nat 17) with 17%nat.
  cbn [rep]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

(** * The right pass over plain items *)

Fixpoint plain_ok (ss : list seg) : bool :=
  match ss with
  | [] => true
  | SP x c :: r => (1 <=? x)%N && plain_ok r
  | SD bs :: r => match kindof bs with Kn _ _ => plain_ok r | _ => false end
  end.

Lemma right_rep n w : (forall l r, exists W, l <* T8 {{B}}> w *> r -->* l <* W <* T8 {{B}}> r) ->
  forall l r, exists W, l <* T8 {{B}}> rep n w *> r -->* l <* W <* T8 {{B}}> r.
Proof.
  intros Hw. induction n as [|n IH]; intros l r; cbn [rep].
  - exists (@nil Sym). apply evstep_refl.
  - rewrite Str_app_assoc. destruct (Hw l (rep n w *> r)) as [W1 H1]. destruct (IH (l <* W1) r) as [W2 H2].
    exists (W2 ++ W1). eapply evstep_trans; [exact H1|]. rewrite Str_app_assoc. exact H2.
Qed.

Lemma right_itm bs : match kindof bs with Kn _ _ => True | _ => False end ->
  forall l r, exists W, l <* T8 {{B}}> itm bs *> r -->* l <* W <* T8 {{B}}> r.
Proof.
  destruct (kindof bs) as [i z| | |] eqn:K; try contradiction. intros _ l r.
  apply kindof_Kn in K as [-> Hz]. rewrite H_n by exact Hz. eexists. apply right_item.
Qed.

Lemma right_ok ss : plain_ok ss = true -> forall l r, exists W, l <* T8 {{B}}> flat ss *> r -->* l <* W <* T8 {{B}}> r.
Proof.
  induction ss as [|[x c|bs] ss IH]; intros H l r; cbn [flat plain_ok] in *.
  - exists (@nil Sym). apply evstep_refl.
  - apply andb_prop in H as [Hx H]. apply N.leb_le in Hx. rewrite Str_app_assoc. cbn [flat1].
    assert (Hw : forall l r, exists W, l <* T8 {{B}}> itm [x] *> r -->* l <* W <* T8 {{B}}> r).
    { apply right_itm. unfold kindof. cbn [unsnoc]. destruct (0 <? x)%N eqn:E; [exact I|]. apply N.ltb_ge in E. lia. }
    destruct (right_rep (N.to_nat c) (itm [x]) Hw l (flat ss *> r)) as [W1 H1].
    destruct (IH H (l <* W1) r) as [W2 H2].
    exists (W2 ++ W1). eapply evstep_trans; [exact H1|]. rewrite Str_app_assoc. exact H2.
  - destruct (kindof bs) eqn:K; try discriminate. rewrite Str_app_assoc. cbn [flat1].
    assert (Hw : match kindof bs with Kn _ _ => True | _ => False end) by (rewrite K; exact I).
    destruct (right_itm bs Hw l (flat ss *> r)) as [W1 H1].
    destruct (IH H (l <* W1) r) as [W2 H2].
    exists (W2 ++ W1). eapply evstep_trans; [exact H1|]. rewrite Str_app_assoc. exact H2.
Qed.

Lemma prefix_ok : plain_ok pre48 = true.
Proof. vm_compute. reflexivity. Qed.

(** * The right pass of the record sweep *)

Lemma left_right n m initR r1 r : n = (2 * m)%nat ->
  0inf <{{D}} [1;0]^^n *> Ms (initR ++ [S r1]) *> r -->*
  0inf <* [0;1;0;1]^^m <* [1;0;1] <* convs initR <* B6^^r1 <* T8 {{B}}> r.
Proof.
  intros ->. rewrite blk_even. eapply evstep_trans; [apply DS_even|].
  rewrite Ms_app. cbn [Ms]. rewrite app_nil_r, Str_app_assoc.
  eapply evstep_trans; [apply MRs|]. eapply evstep_trans; [apply MR|]. rewrite conv_S, !Str_app_assoc. apply evstep_refl.
Qed.

Lemma region_right l r :
  l <* T8 {{B}}> itm [4157; 1986]%N *> itm [6143%N] *> itm [6143%N] *> itm [4607; 0; 0]%N *> itm [2036; 1035]%N *>
    itm [3071%N] *> r -->*
  l <* rconv [4157] 1985 <* rconv [] 6142 <* rconv [] 6142 <* rconv [] 4606 <* [1;1;0;0] <* [0;1;0;0;1;0]^^2034
    <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^1033 <* [1;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^3069 <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] {{B}}> r.
Proof.
  assert (E1 : itm [4157; 1986]%N = enc_item [4157] 1985).
  { pose proof (H_n [4157%N] 1986%N ltac:(lia)) as K. cbn [app] in K. rewrite K. reflexivity. }
  assert (E2 : itm [6143%N] = enc_item [] 6142).
  { pose proof (H_n [] 6143%N ltac:(lia)) as K. cbn [app] in K. rewrite K. reflexivity. }
  assert (E3 : itm [4607; 0; 0]%N = enc_item [] 4606 ++ Mb 0 ++ Mb 0).
  { pose proof (H_m [] 4607%N ltac:(lia)) as K. cbn [app] in K. rewrite K. reflexivity. }
  assert (E4 : itm [2036; 1035]%N = PH ++ Mb (2+2034) ++ Mb (2+1033)).
  { unfold itm. cbn [tn map Ms]. rewrite app_nil_r. reflexivity. }
  assert (E5 : itm [3071%N] = PH ++ Mb (2+3069)).
  { unfold itm. cbn [tn map Ms]. rewrite app_nil_r. reflexivity. }
  rewrite E1, E2, E3, E4, E5, !Str_app_assoc.
  eapply evstep_trans; [apply right_item|].
  eapply evstep_trans; [apply right_item|].
  eapply evstep_trans; [apply right_item|].
  eapply evstep_trans; [apply right_item|].
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  eapply evstep_trans; [apply MR|]. change (conv 0) with [1;0].
  rewrite !Mb2. unfold T8. rewrite !Str_app_assoc.
  apply EXR.
Qed.

Lemma rec_bridge a b c d e f g h l :
  l <* rconv [2+h] (2+g) <* rconv [] (2+f) <* rconv [] (2+e) <* rconv [] (2+d) <* [1;1;0;0] <* [0;1;0;0;1;0]^^(2+a)
    <* [1;0;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* [0;1;0;0;1;0]^^(2+b) <* [1;1;0;0;1;0;0;1;0;0;1;0]
    <* [0;1;0;0;1;0]^^(2+c) <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0] = INL1 a b c d e f g h l.
Proof. unfold rconv, convs, conv, INL1, K12, B6. cbn [lpow Nat.add]. rewrite !Str_app_assoc. reflexivity. Qed.
End P_M269k1.

Section P_M269l.
Optimize Heap.
Definition Rt0 : side := flat R0 *> ENDc *> 0inf.
Lemma PS0 l : l <* T8 {{B}}> Rt0 -->* l <{{C}} [0;1;0] *> Rt1.
Proof. unfold Rt0, Rt1. apply partial_nxt. exact nxt0. Qed.

Lemma split22 (Z : side) :
  Z <* [1;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0] = Z <* [1;0;0;1;0;0;1;0;0;1;0;0;1;0] <* T8.
Proof. reflexivity. Qed.

Lemma rec_core l (r r' : side) (P : forall l, l <* T8 {{B}}> r -->* l <{{C}} [0;1;0] *> r') :
  l <* T8 {{B}}> itm [4157; 1986]%N *> itm [6143%N] *> itm [6143%N] *> itm [4607; 0; 0]%N *> itm [2036; 1035]%N *>
    itm [3071%N] *> r -->*
  INL1 2032 1031 3067 4604 6140 6140 1983 4155 l <{{C}} [0;1;0] *> r'.
Proof.
  eapply evstep_trans; [apply region_right|].
  rewrite split22.
  eapply evstep_trans; [apply P|].
  rewrite <- (rec_bridge 2032 1031 3067 4604 6140 6140 1983 4155 l). apply evstep_refl.
Qed.

Lemma record_part : exists L0, cfg s_110596984 -->* INL1 2032 1031 3067 4604 6140 6140 1983 4155 L0 <{{C}} [0;1;0] *> Rt1.
Proof.
  set (Lb := 0inf <* [0;1;0;1]^^(N.to_nat 9105360) <* [1;0;1] <* convs [N.to_nat 30926190; 0%nat] <* B6^^(N.to_nat 3477551)).
  destruct (right_ok pre48 prefix_ok Lb (itm [4157; 1986]%N *> itm [6143%N] *> itm [6143%N] *> itm [4607; 0; 0]%N *>
              itm [2036; 1035]%N *> itm [3071%N] *> Rt0)) as [Wp Hp].
  exists (Lb <* Wp).
  unfold cfg. rewrite flat_last, !Str_app_assoc. change (flat R0 *> ENDc *> 0inf) with Rt0.
  change (blk s_110596984) with 18210720%N. change (rst s_110596984) with [30926190; 0; 3477552]%N.
  replace (N.to_nat 18210720) with (2 * N.to_nat 9105360)%nat by lia.
  change (tn [30926190; 0; 3477552]%N) with ([N.to_nat 30926190; 0%nat] ++ [N.to_nat 3477552]).
  replace (N.to_nat 3477552) with (S (N.to_nat 3477551)) by lia.
  eapply evstep_trans; [apply left_right; reflexivity|].
  eapply evstep_trans; [exact Hp|].
  exact (rec_core (Lb <* Wp) Rt0 Rt1 PS0).
Qed.

(** * The end game *)

Theorem endgame : halts tm (cfg s_110596984).
Proof. destruct record_part as [L0 H]. eapply halts_evstep; [apply endgame_from|exact H]. Qed.
End P_M269l.

Theorem reach_last : c0 -->* cfg s_110596984.
Proof. eapply evstep_trans; [exact init100|exact main_run]. Qed.

Theorem halt : halts tm c0.
Proof. eapply halts_evstep; [exact endgame|exact reach_last]. Qed.

Print Assumptions halt.

End TM1.
