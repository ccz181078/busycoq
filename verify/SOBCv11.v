Require Import List NArith PeanoNat ZArith ZifyNat Lia Bool.
Import ListNotations.


Module Capacity.
Inductive letter := Odd | Even | Gap.

(* E denotes the working P atom, O the working Q atom. *)
Definition atom (even : bool) (g : nat) (s : N) : option N :=
  let u := (s / 2 * 2)%N in
  let r := N.of_nat (g / 3) in
  let j := g mod 3 in
  if even then
    match g with
    | 0 => Some (2*u+2)%N
    | 1 => Some (2*u+1)%N
    | _ => if Nat.eqb j 2 then
             if (2 <=? s)%N then Some (2^(r+1)*u-1)%N else None
           else Some (2^(r+1)*(u+1)-1)%N
    end
  else
    match g with
    | 0 => if (3 <=? s)%N then Some (s-3)%N else None
    | 1 => Some (2*u)%N
    | 2 => if (2 <=? s)%N then Some (2*u-1)%N else None
    | _ => if Nat.eqb j 0 then
             if (2 <=? s)%N then Some (2^r*u-3)%N else None
           else Some (2^(r+1)*(u+1)-3)%N
    end.

Local Open Scope N_scope.

Lemma atom_monotone b g s s' t :
  atom b g s = Some s' -> s <= t ->
  exists t', atom b g t = Some t' /\ s' <= t'.
Proof.
  intros H Hst.
  assert (Hu: s/2*2 <= t/2*2) by (apply N.mul_le_mono_r; apply N.Div0.div_le_mono; assumption).
  unfold atom in *.
  destruct b; destruct g as [|[|[|g]]]; cbv beta iota zeta in *.
  all: repeat match goal with
       | H: context [if ?test then _ else _] |- _ => destruct test eqn:?
       | |- context [if ?test then _ else _] => destruct test eqn:?
       end.
  all: repeat match goal with
       | H: (_ <=? _)%N = true |- _ => apply N.leb_le in H
       | H: (_ <=? _)%N = false |- _ => apply N.leb_gt in H
       end.
  all: try discriminate; try lia.
  all: match goal with
  | H: Some ?x = Some ?y |- exists t', Some ?z = Some t' /\ ?y <= t' =>
      exists z; split; [reflexivity|];
      assert (Hm: x <= z) by nia; congruence
  end.
Qed.

Local Close Scope N_scope.

(* All gaps of length at least four share a sufficient lower transition. *)
Lemma atom_large b g s : (4 <= g)%nat -> (2 <= s)%N ->
  exists v, atom b g s = Some v /\
    (8*(s/2)-(if b then 1 else 3) <= v)%N.
Proof.
  intros Hg Hs.
  assert (Hr: (1 <= g/3)%nat) by (apply Nat.div_le_lower_bound; lia).
  assert (Hp: (2 <= 2^(N.of_nat (g/3)))%N).
  { change 2%N with (2^1)%N; apply N.pow_le_mono_r; lia. }
  assert (Hp': (4 <= 2^(N.of_nat (g/3)+1))%N).
  { rewrite N.pow_add_r; cbn [N.pow]; nia. }
  pose proof (Nat.div_mod g 3 ltac:(lia)) as Hdiv.
  assert (Hq: (1 <= s/2)%N) by (apply N.div_le_lower_bound; lia).
  unfold atom.
  destruct g as [|[|[|[|g]]]]; try lia; cbv beta iota zeta.
  destruct b.
  - destruct (Nat.eqb (S (S (S (S g))) mod 3) 2) eqn:Hj.
    + rewrite (proj2 (N.leb_le _ _) Hs); eexists; split; [reflexivity|]; nia.
    + eexists; split; [reflexivity|]; nia.
  - destruct (Nat.eqb (S (S (S (S g))) mod 3) 0) eqn:Hj.
    + apply Nat.eqb_eq in Hj.
      assert (Hr2: (2 <= S (S (S (S g)))/3)%nat) by lia.
      assert (Hp2: (4 <= 2^(N.of_nat (S (S (S (S g)))/3)))%N).
      { change 4%N with (2^2)%N; apply N.pow_le_mono_r; lia. }
      rewrite (proj2 (N.leb_le _ _) Hs); eexists; split; [reflexivity|]; nia.
    + eexists; split; [reflexivity|]; nia.
Qed.

(* Gap columns are 0, 1, 2, 3, and all larger counts. *)
Definition abstract_atom b g s :=
  if g <? 4 then atom b g s
  else if (2 <=? s)%N then Some (8*(s/2)-(if b then 1 else 3))%N else None.

Lemma abstract_sound b g s v t :
  abstract_atom b (Nat.min 4 g) s = Some v -> (s <= t)%N ->
  exists v', atom b g t = Some v' /\ (v <= v')%N.
Proof.
  intros H Hst; destruct (Nat.lt_ge_cases g 4) as [Hg|Hg].
  - rewrite Nat.min_r in H by lia.
    unfold abstract_atom in H; rewrite (proj2 (Nat.ltb_lt _ _) Hg) in H.
    eapply atom_monotone; eauto.
  - rewrite Nat.min_l in H by lia.
    change ((if (2 <=? s)%N then Some (8*(s/2)-(if b then 1 else 3))%N
      else None) = Some v) in H.
    destruct (2 <=? s)%N eqn:Hs; try discriminate.
    apply N.leb_le in Hs; inversion H; subst v.
    destruct (atom_large b g s Hg Hs) as [v [Hv Hle]].
    destruct (atom_monotone b g s v t Hv Hst) as [v' [Hv' Hle']].
    exists v'; split; [exact Hv'|].
    change (8*(s/2)-(if b then 1 else 3) <= v')%N.
    eapply N.le_trans; eauto.
Qed.

Record row := Row {
  edges : list (letter * nat);
  final : bool;
  bounds : list N
}.
Definition node (graph:list row) q := nth q graph (Row [] false []).
(* Zero denotes no backward obligation; n+1 requires capacity n. *)
Definition bound graph q g := nth g (bounds (node graph q)) 0%N.
Inductive path (graph:list row) : nat -> list letter -> nat -> Prop :=
| path_nil q : path graph q [] q
| path_cons q c q' w q'' :
    In (c,q') (edges (node graph q)) -> path graph q' w q'' ->
    path graph q (c::w) q''.

Section Check.
Variable graph : list row.
Definition check_step q c q' g :=
  let b := bound graph q' g in
  if (b =? 0)%N then true else
  match c with
  | Gap => (0 <? bound graph q (Nat.min 4 (S g)))%N &&
           (b <=? bound graph q (Nat.min 4 (S g)))%N
  | _ => (0 <? bound graph q 0)%N &&
      match abstract_atom (match c with Even => true | _ => false end) g
        (bound graph q 0-1)%N with
      | Some t => (b <=? t+1)%N | None => false
      end
  end.
Definition check_edge q '(c,q') :=
  (q' <? length graph) && forallb (check_step q c q') (seq 0 5).
Definition check_node q :=
  (if final (node graph q) then (29 <=? bound graph q 0)%N else true) &&
  forallb (check_edge q) (edges (node graph q)).
Definition check := forallb check_node (seq 0 (length graph)).

Lemma checked_node q : check = true -> q < length graph -> check_node q = true.
Proof.
  unfold check; intros H Hq; apply forallb_forall with (x:=q) in H;
    [exact H|apply in_seq; lia].
Qed.
Lemma checked_edge q c q' : check = true -> q < length graph ->
  In (c,q') (edges (node graph q)) ->
  q' < length graph /\ forall g, g < 5 -> check_step q c q' g = true.
Proof.
  intros HC Hq HE; pose proof (checked_node q HC Hq) as H.
  apply andb_true_iff in H; destruct H as [_ H].
  apply forallb_forall with (x:=(c,q')) in H; auto.
  apply andb_true_iff in H; destruct H as [Hq' H].
  split; [apply Nat.ltb_lt,Hq'|].
  intros g Hg; apply forallb_forall with (x:=g) in H;
    [exact H|apply in_seq; lia].
Qed.
Lemma checked_final q : check = true -> q < length graph ->
  final (node graph q) = true -> (29 <= bound graph q 0)%N.
Proof.
  intros HC Hq HF; pose proof (checked_node q HC Hq) as H.
  unfold check_node in H; rewrite HF in H; apply andb_true_iff in H.
  apply N.leb_le; exact (proj1 H).
Qed.

Lemma checked_gap q q' g : check = true -> q < length graph ->
  In (Gap,q') (edges (node graph q)) -> g < 5 -> (0 < bound graph q' g)%N ->
  (bound graph q' g <= bound graph q (Nat.min 4 (S g)))%N.
Proof.
  intros HC Hq HE Hg Hb.
  pose proof (proj2 (checked_edge q Gap q' HC Hq HE) g Hg) as H.
  unfold check_step in H.
  destruct (bound graph q' g =? 0)%N eqn:E.
  { apply N.eqb_eq in E; lia. }
  apply andb_true_iff in H; apply N.leb_le; exact (proj2 H).
Qed.

Lemma checked_gaps q n w f : check = true -> q < length graph ->
  path graph q (repeat Gap n ++ w) f ->
  exists q', q' < length graph /\ path graph q' w f /\
    ((0 < bound graph q' 0)%N ->
      (bound graph q' 0 <= bound graph q (Nat.min 4 n))%N).
Proof.
  revert q; induction n as [|n IH]; intros q HC Hq HP.
  - exists q; split; [exact Hq|].
    split; [exact HP|]; cbn [Nat.min]; intros; apply N.le_refl.
  - cbn [repeat app] in HP.
    inversion HP as [|q0 c q1 w0 f0 HE HR]; subst.
    destruct (checked_edge q Gap q1 HC Hq HE) as [Hq1 _].
    destruct (IH q1 HC Hq1 HR) as [q' [Hq' [HR' HB]]].
    exists q'; repeat split; auto.
    intro Hb; specialize (HB Hb).
    pose proof (checked_gap q q1 (Nat.min 4 n) HC Hq HE ltac:(lia) ltac:(lia)) as H.
    replace (Nat.min 4 (S (Nat.min 4 n))) with (Nat.min 4 (S n)) in H by lia.
    lia.
Qed.

Lemma checked_digit q q' (b:bool) g : check = true -> q < length graph ->
  In ((if b then Even else Odd),q') (edges (node graph q)) ->
  (0 < bound graph q' (Nat.min 4 g))%N ->
  (0 < bound graph q 0)%N /\ forall s, (bound graph q 0-1 <= s)%N ->
    exists t, atom b g s = Some t /\ (bound graph q' (Nat.min 4 g)-1 <= t)%N.
Proof.
  intros HC Hq HE Hb.
  pose proof (proj2 (checked_edge q _ q' HC Hq HE) (Nat.min 4 g) ltac:(lia)) as H.
  unfold check_step in H.
  destruct (bound graph q' (Nat.min 4 g) =? 0)%N eqn:E.
  { apply N.eqb_eq in E; lia. }
  destruct b; cbv beta iota zeta in H.
  all: apply andb_true_iff in H; destruct H as [Hpos H]; apply N.ltb_lt in Hpos;
    destruct (abstract_atom _ _ _) as [t|] eqn:HA; try discriminate.
  all: apply N.leb_le in H; split; [exact Hpos|]; intros s Hs;
    destruct (abstract_sound _ _ _ _ _ HA Hs) as [t' [HT Hle]];
    exists t'; split; [exact HT|lia].
Qed.
End Check.

End Capacity.
Import Capacity.


Module Automata.
Definition letter_eqb a b :=
  match a,b with Odd,Odd | Even,Even | Gap,Gap => true | _,_ => false end.
Lemma letter_eqb_spec a b : letter_eqb a b = true <-> a=b.
Proof. destruct a,b; cbn; split; congruence. Qed.

Fixpoint encode (xs : list nat) : N :=
  match xs with [] => 0%N | x::xs => N.setbit (encode xs) (N.of_nat x) end.
Definition member (m : N) (q : nat) := N.testbit m (N.of_nat q) = true.
Definition subset a b := N.eqb (N.land a b) a.

Lemma encode_spec xs q : member (encode xs) q <-> In q xs.
Proof.
  unfold member; induction xs as [|x xs IH].
  - cbn [encode In]; rewrite N.bits_0; split; intro H; inversion H.
  - cbn [encode In]; rewrite N.setbit_iff, IH.
    split; intros [H|H]; auto.
    + left; apply Nat2N.inj in H; auto.
Qed.

Lemma subset_spec a b q : subset a b = true -> member a q -> member b q.
Proof.
  unfold subset, member; intros H Ha.
  apply N.eqb_eq in H.
  pose proof (f_equal (fun m => N.testbit m (N.of_nat q)) H) as E.
  cbv beta in E.
  rewrite N.land_spec, Ha in E; cbn in E; exact E.
Qed.

Record mask := Mask {
  bits : N;
  vertices : list nat;
  move_odd : N;
  move_even : N;
  move_gap : N;
  accepting : bool
}.
Definition mask_move m c :=
  match c with Odd => move_odd m | Even => move_even m | Gap => move_gap m end.
Definition mask_output m c := match c with None => bits m | Some c => mask_move m c end.

Record trans_row := TransRow {
  trans_edges : list (option letter * option letter * nat);
  trans_final : bool
}.

Section Closure.
Variable graph : list row.
Variable trans : list trans_row.
Variable masks : list mask.
Variable certificate : list (list (list nat)).

Definition tnode q := nth q trans (TransRow [] false).
Definition get_mask k := nth k masks (Mask 0 [] 0 0 0 false).
Definition cell u v := nth v (nth u certificate []) [].
Definition next u c := map snd (filter (fun e => letter_eqb (fst e) c) (edges (node graph u))).
Definition input_next u c := match c with None => [u] | Some c => next u c end.

Lemma next_spec u c v : In v (next u c) <-> In (c,v) (edges (node graph u)).
Proof.
  unfold next; rewrite in_map_iff.
  split.
  - intros [[c' v'] [E H]]; cbn in E; subst v'.
    apply filter_In in H; destruct H as [H E].
    cbn in E; apply letter_eqb_spec in E; subst; auto.
  - intro H; exists (c,v); split; auto.
    apply filter_In; split; auto; apply letter_eqb_spec; reflexivity.
Qed.

Definition mask_check m :=
  N.eqb (bits m) (encode (vertices m)) &&
  forallb (fun c => N.eqb (mask_move m c) (encode (flat_map (fun u => next u c) (vertices m))))
    [Odd;Even;Gap] &&
  Bool.eqb (accepting m) (existsb (fun u => final (node graph u)) (vertices m)).

Definition masks_check := forallb mask_check masks.

Lemma mask_checked k : masks_check = true -> mask_check (get_mask k) = true.
Proof.
  unfold masks_check, get_mask; intro H.
  destruct (Nat.lt_ge_cases k (length masks)).
  - apply forallb_forall with (x:=nth k masks (Mask 0 [] 0 0 0 false)) in H; auto.
    apply nth_In; assumption.
  - rewrite nth_overflow; [reflexivity|lia].
Qed.

Lemma mask_vertices k q : masks_check = true ->
  member (bits (get_mask k)) q <-> In q (vertices (get_mask k)).
Proof.
  intro H; apply (mask_checked k) in H.
  unfold mask_check in H; repeat rewrite andb_true_iff in H.
  destruct H as [[H _] _]; apply N.eqb_eq in H.
  rewrite H; apply encode_spec.
Qed.

Lemma mask_next k c q : masks_check = true ->
  member (mask_move (get_mask k) c) q ->
  exists p, member (bits (get_mask k)) p /\ In (c,q) (edges (node graph p)).
Proof.
  intros HC H.
  pose proof (mask_checked k HC) as HM.
  unfold mask_check in HM; repeat rewrite andb_true_iff in HM.
  destruct HM as [[_ HM] _].
  apply forallb_forall with (x:=c) in HM; [|destruct c; cbn; auto].
  apply N.eqb_eq in HM; rewrite HM, encode_spec in H.
  apply in_flat_map in H; destruct H as [p [Hp Hq]].
  exists p; split.
  - apply (mask_vertices k p HC); exact Hp.
  - apply next_spec; exact Hq.
Qed.

Lemma mask_final k : masks_check = true -> accepting (get_mask k) = true ->
  exists p, member (bits (get_mask k)) p /\ final (node graph p) = true.
Proof.
  intros HC HF.
  pose proof (mask_checked k HC) as HM.
  unfold mask_check in HM; repeat rewrite andb_true_iff in HM.
  destruct HM as [_ HM].
  apply Bool.eqb_prop in HM; rewrite HF in HM.
  symmetry in HM; apply existsb_exists in HM; destruct HM as [p [Hp Hp']].
  exists p; split; auto; apply (mask_vertices k p HC); exact Hp.
Qed.

Definition covers u v m := existsb (fun k => subset (bits (get_mask k)) m) (cell u v).
Definition edge_check u k '(i,o,v) :=
  (v <? length trans) &&
  forallb (fun u' => (u' <? length graph) && covers u' v (mask_output (get_mask k) o))
    (input_next u i).
Definition cell_check u v :=
  forallb (fun k =>
    forallb (edge_check u k) (trans_edges (tnode v)) &&
    if final (node graph u) && trans_final (tnode v) then accepting (get_mask k) else true)
    (cell u v).
Definition closure_check :=
  forallb (fun u => forallb (cell_check u) (seq 0 (length trans)))
    (seq 0 (length graph)).

Lemma cell_checked u v : closure_check = true ->
  u < length graph -> v < length trans -> cell_check u v = true.
Proof.
  unfold closure_check; intros H Hu Hv.
  apply forallb_forall with (x:=u) in H; [|apply in_seq; lia].
  apply forallb_forall with (x:=v) in H; auto; apply in_seq; lia.
Qed.

Definition emit (c : option letter) := match c with None => [] | Some c => [c] end.
Inductive trans_path : nat -> list letter -> list letter -> nat -> Prop :=
| trans_nil v : trans_path v [] [] v
| trans_cons v i o v' xs ys v'' :
    In (i,o,v') (trans_edges (tnode v)) -> trans_path v' xs ys v'' ->
    trans_path v (emit i ++ xs) (emit o ++ ys) v''.

Lemma trans_path_app u xs ys v xs' ys' w :
  trans_path u xs ys v -> trans_path v xs' ys' w ->
  trans_path u (xs++xs') (ys++ys') w.
Proof.
  intros H; induction H; intro Hrest; cbn [app]; auto.
  repeat rewrite <-app_assoc; econstructor; eauto.
Qed.

Definition trans_edge_eq_dec (a b : option letter * option letter * nat) :
  {a=b}+{a<>b}.
Proof. repeat decide equality. Defined.

Fixpoint trace_check q es :=
  match es with
  | [] => true
  | (i,o,q')::es =>
      if in_dec trans_edge_eq_dec (i,o,q') (trans_edges (tnode q)) then trace_check q' es else false
  end.
Fixpoint trace_input (es : list (option letter * option letter * nat)) :=
  match es with [] => [] | (i,o,q)::es => emit i ++ trace_input es end.
Fixpoint trace_output (es : list (option letter * option letter * nat)) :=
  match es with [] => [] | (i,o,q)::es => emit o ++ trace_output es end.
Fixpoint trace_end q (es : list (option letter * option letter * nat)) :=
  match es with [] => q | (i,o,q')::es => trace_end q' es end.

Lemma trace_spec q es : trace_check q es = true ->
  trans_path q (trace_input es) (trace_output es) (trace_end q es).
Proof.
  revert q; induction es as [|[[i o] q'] es IH]; intros q; cbn.
  - intro; constructor.
  - destruct (in_dec trans_edge_eq_dec (i,o,q') (trans_edges (tnode q))); try discriminate.
    intro H; econstructor; [exact i0|apply IH,H].
Qed.

Lemma input_path u i xs q : path graph u (emit i ++ xs) q ->
  exists u', In u' (input_next u i) /\ path graph u' xs q.
Proof.
  destruct i as [c|]; cbn [emit app input_next]; intro H.
  - inversion H; subst; eexists; split; [apply next_spec; eauto|eauto].
  - exists u; split; [cbn; auto|exact H].
Qed.

Theorem closure_sound v xs ys v' :
  masks_check = true -> closure_check = true ->
  trans_path v xs ys v' -> trans_final (tnode v') = true ->
  forall u q k, u < length graph -> v < length trans -> In k (cell u v) ->
  path graph u xs q -> final (node graph q) = true ->
  exists p q', member (bits (get_mask k)) p /\ path graph p ys q' /\ final (node graph q') = true.
Proof.
  intros HM HC HT; induction HT; intros HF u q k Hu Hv Hk HP HQ.
  - assert (q=u) by (inversion HP; reflexivity); subst q.
    pose proof (cell_checked u v HC Hu Hv) as Hcell.
    unfold cell_check in Hcell; apply forallb_forall with (x:=k) in Hcell; auto.
    apply andb_true_iff in Hcell; destruct Hcell as [_ Hcell].
    rewrite HQ, HF in Hcell; cbn in Hcell.
    destruct (mask_final k HM Hcell) as [p [Hp Hp']].
    exists p,p; repeat split; auto; constructor.
  - pose proof (cell_checked u v HC Hu Hv) as Hcell.
    unfold cell_check in Hcell; apply forallb_forall with (x:=k) in Hcell; auto.
    apply andb_true_iff in Hcell; destruct Hcell as [HE _].
    apply forallb_forall with (x:=(i,o,v')) in HE; auto.
    unfold edge_check in HE; apply andb_true_iff in HE; destruct HE as [Hv' HE].
    apply Nat.ltb_lt in Hv'.
    destruct (input_path _ _ _ _ HP) as [u' [Hin HP']].
    apply forallb_forall with (x:=u') in HE; auto.
    apply andb_true_iff in HE; destruct HE as [Hu' HE].
    apply Nat.ltb_lt in Hu'.
    unfold covers in HE; apply existsb_exists in HE.
    destruct HE as [k' [Hk' Hsub]].
    destruct (IHHT HF u' q k' Hu' Hv' Hk' HP' HQ) as [p' [q' [Hp' [HR HQ']]]].
    pose proof (subset_spec _ _ _ Hsub Hp') as Hp.
    destruct o as [c|]; cbn [mask_output emit app] in *.
    + destruct (mask_next k c p' HM Hp) as [p [Hp0 Hedge]].
      exists p,q'; repeat split; auto; econstructor; eauto.
    + exists p',q'; repeat split; auto.
Qed.

Definition language starts w :=
  exists u q, In u starts /\ path graph u w q /\ final (node graph q) = true.

Definition initial_check starts v :=
  forallb (fun u => (u <? length graph) && (v <? length trans) &&
    covers u v (encode starts)) starts.

Theorem language_closed starts v xs ys v' :
  masks_check = true -> closure_check = true -> initial_check starts v = true ->
  trans_path v xs ys v' -> trans_final (tnode v') = true ->
  language starts xs -> language starts ys.
Proof.
  intros HM HC HI HT HF [u [q [Hu [HP HQ]]]].
  unfold initial_check in HI; apply forallb_forall with (x:=u) in HI; auto.
  repeat rewrite andb_true_iff in HI; destruct HI as [[Hu0 Hv] HK].
  apply Nat.ltb_lt in Hu0, Hv.
  unfold covers in HK; apply existsb_exists in HK; destruct HK as [k [Hk HS]].
  destruct (closure_sound _ _ _ _ HM HC HT HF u q k Hu0 Hv Hk HP HQ)
    as [p [q' [HB [HP' HQ']]]].
  exists p,q'; repeat split; auto.
  apply encode_spec; eapply subset_spec; eauto.
Qed.

End Closure.

Lemma same_edges g h : map edges g = map edges h ->
  forall q, edges (node g q) = edges (node h q).
Proof.
  intros H q; unfold node.
  pose proof (f_equal (fun xs => nth q xs []) H) as E.
  cbv beta in E.
  rewrite (map_nth edges g (Row [] false [])), (map_nth edges h (Row [] false [])) in E.
  exact E.
Qed.

Definition pre_even g r :=
  existsb (fun e => letter_eqb (fst e) Even && final (node g (snd e))) (edges r).
Lemma same_pre_even g h : map final h = map (pre_even g) g ->
  forall q, final (node h q) = pre_even g (node g q).
Proof.
  intros H q; unfold node.
  pose proof (f_equal (fun xs => nth q xs false) H) as E.
  cbv beta in E.
  rewrite (map_nth final h (Row [] false [])), (map_nth (pre_even g) g (Row [] false [])) in E.
  exact E.
Qed.

Lemma path_core g h w :
  (forall q, edges (node g q) = edges (node h q)) ->
  (forall q, final (node h q) = pre_even g (node g q)) ->
  forall u f, path g u (w++[Even]) f -> final (node g f)=true ->
  exists v, path h u w v /\ final (node h v)=true.
Proof.
  intros HE HF; induction w as [|c w IH]; intros u f HP Hfinal; cbn [app] in HP.
  - inversion HP as [|q c q' xs q'' Hedge HR]; subst.
    assert (f=q') by (inversion HR; reflexivity); subst f.
    exists u; split; [constructor|].
    rewrite HF; unfold pre_even.
    apply existsb_exists; exists (Even,q'); split; auto.
  - inversion HP as [|q c0 q' xs q'' Hedge HR]; subst.
    destruct (IH _ _ HR Hfinal) as [v [Hpath Hv]].
    exists v; split; auto; econstructor; [rewrite <-HE; exact Hedge|exact Hpath].
Qed.
End Automata.
Import Automata.


From BusyCoq Require HashTable.
Require PArray Uint63.
Module Certificate.
(* A finite invariant. Its certificates are computed below and then checked. *)
Local Open Scope N_scope.
Definition body_graph : list row := [
  Row [(Even,1%nat);(Odd,80%nat)] false [];
  Row [(Gap,234%nat)] false [];
  Row [(Gap,371%nat)] false [];
  Row [(Gap,438%nat)] false [];
  Row [(Even,314%nat)] false [];
  Row [(Odd,428%nat)] false [];
  Row [(Odd,8%nat)] false [];
  Row [(Gap,6%nat)] false [];
  Row [(Even,301%nat)] false [];
  Row [(Gap,8%nat)] false [];
  Row [(Odd,9%nat)] false [];
  Row [(Even,164%nat)] false [];
  Row [(Gap,10%nat)] false [];
  Row [(Gap,73%nat)] false [];
  Row [(Even,409%nat)] false [];
  Row [(Even,436%nat)] false [];
  Row [(Odd,292%nat)] false [];
  Row [(Even,23%nat);(Even,42%nat);(Even,62%nat);(Even,197%nat);(Even,293%nat);(Even,435%nat)] false [];
  Row [(Gap,337%nat)] false [];
  Row [(Even,5%nat)] false [];
  Row [(Gap,435%nat)] false [];
  Row [(Even,10%nat)] false [];
  Row [(Even,6%nat)] false [];
  Row [(Odd,26%nat)] false [];
  Row [(Gap,372%nat)] false [];
  Row [(Gap,23%nat)] false [];
  Row [(Even,438%nat)] false [];
  Row [(Gap,26%nat)] false [];
  Row [(Gap,400%nat)] false [];
  Row [(Even,29%nat);(Gap,135%nat);(Gap,190%nat);(Gap,224%nat)] false [];
  Row [(Odd,27%nat)] false [];
  Row [(Even,30%nat)] false [];
  Row [(Odd,350%nat)] false [];
  Row [(Odd,439%nat)] false [];
  Row [(Gap,27%nat)] false [];
  Row [(Gap,41%nat)] false [];
  Row [(Even,37%nat)] false [];
  Row [(Even,37%nat);(Gap,137%nat);(Gap,141%nat);(Odd,132%nat)] false [];
  Row [(Gap,434%nat)] false [];
  Row [(Gap,28%nat)] false [];
  Row [(Odd,60%nat)] false [];
  Row [(Even,68%nat)] false [];
  Row [(Odd,118%nat)] false [];
  Row [(Gap,11%nat);(Gap,21%nat);(Gap,31%nat);(Gap,65%nat);(Gap,72%nat);(Gap,77%nat);(Gap,82%nat);(Gap,97%nat);(Gap,103%nat);(Gap,120%nat);(Gap,150%nat);(Gap,160%nat);(Gap,172%nat);(Gap,183%nat);(Gap,196%nat);(Gap,204%nat);(Gap,215%nat);(Gap,216%nat);(Gap,217%nat);(Gap,246%nat);(Gap,254%nat);(Gap,276%nat);(Gap,280%nat);(Gap,284%nat);(Gap,304%nat);(Gap,311%nat);(Gap,316%nat);(Gap,344%nat);(Gap,352%nat);(Gap,379%nat);(Gap,380%nat);(Gap,387%nat);(Gap,389%nat);(Gap,410%nat);(Gap,421%nat);(Odd,78%nat);(Odd,167%nat);(Odd,226%nat);(Odd,244%nat);(Odd,286%nat);(Odd,296%nat);(Odd,328%nat);(Odd,331%nat);(Odd,351%nat);(Odd,383%nat);(Odd,396%nat);(Odd,414%nat);(Odd,429%nat)] false [];
  Row [(Gap,58%nat)] false [];
  Row [(Even,214%nat)] false [];
  Row [(Gap,124%nat)] false [];
  Row [(Even,346%nat)] false [];
  Row [(Even,397%nat)] false [];
  Row [(Gap,33%nat)] false [];
  Row [(Even,396%nat)] false [];
  Row [(Gap,48%nat)] false [];
  Row [(Odd,51%nat)] false [];
  Row [(Even,200%nat)] false [];
  Row [(Gap,52%nat)] false [];
  Row [(Gap,194%nat)] false [];
  Row [(Even,52%nat)] false [];
  Row [(Even,10%nat);(Even,16%nat);(Even,32%nat);(Even,159%nat);(Even,169%nat);(Even,255%nat);(Even,272%nat);(Even,341%nat);(Even,408%nat)] false [];
  Row [(Odd,48%nat)] false [];
  Row [(Gap,51%nat)] false [];
  Row [(Even,8%nat)] false [];
  Row [(Gap,42%nat)] false [];
  Row [(Odd,69%nat)] false [];
  Row [(Even,33%nat)] false [];
  Row [(Gap,62%nat)] false [];
  Row [(Even,16%nat)] false [];
  Row [(Odd,98%nat)] false [];
  Row [(Gap,43%nat)] false [];
  Row [(Even,41%nat);(Even,195%nat);(Odd,180%nat)] false [];
  Row [(Even,123%nat);(Odd,119%nat)] false [];
  Row [(Gap,69%nat)] false [];
  Row [(Odd,70%nat)] false [];
  Row [(Even,71%nat)] false [];
  Row [(Even,27%nat);(Even,70%nat);(Even,93%nat);(Even,171%nat);(Even,194%nat);(Even,202%nat);(Gap,10%nat);(Gap,131%nat);(Gap,272%nat);(Gap,334%nat);(Gap,341%nat)] false [];
  Row [(Gap,430%nat)] false [];
  Row [(Gap,70%nat)] false [];
  Row [(Even,62%nat)] false [];
  Row [(Even,53%nat)] false [];
  Row [(Odd,397%nat)] false [];
  Row [(Even,187%nat);(Gap,6%nat);(Gap,14%nat);(Gap,44%nat);(Gap,63%nat);(Gap,81%nat);(Gap,99%nat);(Gap,144%nat);(Gap,145%nat);(Gap,181%nat);(Gap,205%nat);(Gap,210%nat);(Gap,231%nat);(Gap,251%nat);(Gap,261%nat);(Gap,266%nat);(Gap,307%nat);(Gap,318%nat);(Gap,325%nat);(Gap,329%nat);(Gap,339%nat);(Gap,368%nat);(Gap,369%nat);(Gap,401%nat);(Gap,418%nat);(Gap,426%nat);(Odd,5%nat);(Odd,89%nat);(Odd,106%nat);(Odd,126%nat);(Odd,147%nat);(Odd,175%nat);(Odd,220%nat);(Odd,259%nat);(Odd,289%nat);(Odd,314%nat);(Odd,330%nat);(Odd,355%nat);(Odd,358%nat);(Odd,392%nat);(Odd,399%nat);(Odd,405%nat);(Odd,409%nat);(Odd,423%nat)] false [];
  Row [(Even,292%nat);(Gap,384%nat)] false [];
  Row [(Gap,92%nat)] false [];
  Row [(Gap,66%nat)] false [];
  Row [(Even,73%nat);(Even,370%nat);(Even,430%nat);(Odd,298%nat);(Odd,365%nat)] false [];
  Row [(Gap,83%nat)] false [];
  Row [(Odd,84%nat)] false [];
  Row [(Odd,188%nat)] false [];
  Row [(Gap,343%nat)] false [];
  Row [(Gap,85%nat)] false [];
  Row [(Gap,143%nat);(Gap,258%nat)] false [];
  Row [(Even,296%nat)] false [];
  Row [(Even,85%nat)] false [];
  Row [(Odd,83%nat)] false [];
  Row [(Gap,118%nat)] false [];
  Row [(Gap,439%nat)] false [];
  Row [(Even,435%nat)] false [];
  Row [(Gap,84%nat)] false [];
  Row [(Gap,396%nat)] false [];
  Row [(Even,26%nat)] false [];
  Row [(Odd,142%nat)] false [];
  Row [(Odd,104%nat)] false [];
  Row [(Even,264%nat);(Even,319%nat)] false [];
  Row [(Gap,364%nat)] false [];
  Row [(Gap,100%nat)] false [];
  Row [(Even,69%nat)] false [];
  Row [(Gap,104%nat)] false [];
  Row [(Odd,105%nat)] false [];
  Row [(Even,106%nat)] false [];
  Row [(Gap,93%nat)] false [];
  Row [(Gap,67%nat)] false [];
  Row [(Even,100%nat)] false [];
  Row [(Even,119%nat);(Odd,121%nat)] false [];
  Row [(Gap,302%nat)] false [];
  Row [(Even,57%nat)] false [];
  Row [(Even,405%nat)] false [];
  Row [(Even,115%nat);(Gap,4%nat);(Gap,6%nat);(Gap,7%nat);(Gap,14%nat);(Gap,19%nat);(Gap,20%nat);(Gap,25%nat);(Gap,44%nat);(Gap,61%nat);(Gap,63%nat);(Gap,64%nat);(Gap,81%nat);(Gap,99%nat);(Gap,107%nat);(Gap,114%nat);(Gap,128%nat);(Gap,129%nat);(Gap,144%nat);(Gap,145%nat);(Gap,148%nat);(Gap,158%nat);(Gap,161%nat);(Gap,166%nat);(Gap,173%nat);(Gap,181%nat);(Gap,182%nat);(Gap,185%nat);(Gap,198%nat);(Gap,205%nat);(Gap,210%nat);(Gap,221%nat);(Gap,225%nat);(Gap,231%nat);(Gap,251%nat);(Gap,261%nat);(Gap,265%nat);(Gap,266%nat);(Gap,267%nat);(Gap,282%nat);(Gap,294%nat);(Gap,307%nat);(Gap,318%nat);(Gap,325%nat);(Gap,329%nat);(Gap,333%nat);(Gap,339%nat);(Gap,360%nat);(Gap,368%nat);(Gap,369%nat);(Gap,395%nat);(Gap,401%nat);(Gap,403%nat);(Gap,417%nat);(Gap,418%nat);(Gap,419%nat);(Gap,425%nat);(Gap,426%nat);(Gap,432%nat);(Odd,5%nat);(Odd,6%nat);(Odd,58%nat);(Odd,68%nat);(Odd,89%nat);(Odd,92%nat);(Odd,101%nat);(Odd,106%nat);(Odd,126%nat);(Odd,147%nat);(Odd,175%nat);(Odd,220%nat);(Odd,259%nat);(Odd,266%nat);(Odd,270%nat);(Odd,289%nat);(Odd,314%nat);(Odd,329%nat);(Odd,330%nat);(Odd,355%nat);(Odd,358%nat);(Odd,392%nat);(Odd,399%nat);(Odd,405%nat);(Odd,409%nat);(Odd,423%nat)] false [];
  Row [(Odd,262%nat)] false [];
  Row [(Gap,98%nat)] false [];
  Row [(Even,337%nat)] false [];
  Row [(Gap,402%nat)] false [];
  Row [(Gap,111%nat)] false [];
  Row [(Even,13%nat);(Even,105%nat);(Even,117%nat);(Even,122%nat);(Even,219%nat);(Even,239%nat);(Even,288%nat);(Even,313%nat);(Even,356%nat);(Even,371%nat);(Even,391%nat);(Even,411%nat);(Even,428%nat);(Gap,22%nat);(Gap,33%nat);(Gap,35%nat);(Gap,76%nat);(Gap,95%nat);(Gap,139%nat);(Gap,156%nat);(Gap,163%nat);(Gap,175%nat);(Gap,207%nat);(Gap,209%nat);(Gap,212%nat);(Gap,232%nat);(Gap,242%nat);(Gap,253%nat);(Gap,281%nat);(Gap,297%nat);(Gap,299%nat);(Gap,308%nat);(Gap,309%nat);(Gap,324%nat);(Gap,330%nat);(Gap,335%nat);(Gap,345%nat);(Gap,355%nat);(Gap,364%nat);(Gap,373%nat);(Gap,409%nat);(Gap,412%nat);(Gap,423%nat);(Odd,125%nat);(Odd,153%nat);(Odd,174%nat);(Odd,238%nat);(Odd,245%nat);(Odd,336%nat);(Odd,388%nat);(Odd,422%nat)] false [];
  Row [(Gap,121%nat)] false [];
  Row [(Even,13%nat);(Even,69%nat);(Even,105%nat);(Even,117%nat);(Even,122%nat);(Even,219%nat);(Even,239%nat);(Even,288%nat);(Even,313%nat);(Even,356%nat);(Even,371%nat);(Even,391%nat);(Even,411%nat);(Even,428%nat);(Gap,22%nat);(Gap,33%nat);(Gap,35%nat);(Gap,76%nat);(Gap,95%nat);(Gap,139%nat);(Gap,156%nat);(Gap,163%nat);(Gap,175%nat);(Gap,207%nat);(Gap,209%nat);(Gap,212%nat);(Gap,232%nat);(Gap,242%nat);(Gap,253%nat);(Gap,281%nat);(Gap,297%nat);(Gap,299%nat);(Gap,308%nat);(Gap,309%nat);(Gap,324%nat);(Gap,330%nat);(Gap,335%nat);(Gap,345%nat);(Gap,355%nat);(Gap,364%nat);(Gap,373%nat);(Gap,409%nat);(Gap,412%nat);(Gap,423%nat);(Odd,125%nat);(Odd,153%nat);(Odd,174%nat);(Odd,238%nat);(Odd,245%nat);(Odd,336%nat);(Odd,388%nat);(Odd,422%nat)] false [];
  Row [(Even,6%nat);(Even,99%nat);(Even,145%nat);(Even,162%nat);(Even,205%nat);(Even,251%nat);(Even,266%nat);(Even,329%nat);(Even,401%nat)] false [];
  Row [(Gap,119%nat)] false [];
  Row [(Even,125%nat);(Odd,122%nat)] false [];
  Row [(Even,33%nat);(Even,139%nat);(Even,175%nat);(Even,324%nat);(Even,330%nat);(Even,335%nat);(Even,355%nat);(Even,364%nat);(Even,373%nat);(Even,409%nat);(Even,423%nat)] false [];
  Row [(Gap,99%nat)] false [];
  Row [(Even,126%nat)] false [];
  Row [(Even,111%nat)] false [];
  Row [(Gap,87%nat)] false [];
  Row [(Gap,133%nat)] false [];
  Row [(Gap,134%nat)] false [];
  Row [(Gap,136%nat)] false [];
  Row [(Gap,146%nat)] false [];
  Row [(Even,227%nat)] false [];
  Row [(Gap,141%nat)] false [];
  Row [(Gap,123%nat)] false [];
  Row [(Even,302%nat);(Odd,13%nat)] false [];
  Row [(Gap,115%nat)] false [];
  Row [(Odd,136%nat)] false [];
  Row [(Even,73%nat);(Odd,367%nat)] false [];
  Row [(Gap,138%nat)] false [];
  Row [(Even,17%nat)] false [];
  Row [(Odd,211%nat)] false [];
  Row [(Odd,168%nat)] false [];
  Row [(Odd,411%nat)] false [];
  Row [(Gap,125%nat)] false [];
  Row [(Even,67%nat);(Gap,12%nat);(Gap,30%nat);(Gap,71%nat);(Gap,164%nat);(Gap,193%nat);(Gap,203%nat);(Gap,233%nat);(Gap,273%nat);(Gap,277%nat);(Gap,342%nat);(Odd,87%nat)] false [];
  Row [(Gap,116%nat)] false [];
  Row [(Gap,154%nat)] false [];
  Row [(Gap,89%nat)] false [];
  Row [(Even,5%nat);(Even,106%nat);(Even,126%nat);(Even,147%nat);(Even,175%nat);(Even,220%nat);(Even,259%nat);(Even,289%nat);(Even,330%nat);(Even,355%nat);(Even,358%nat);(Even,392%nat);(Even,399%nat);(Even,405%nat);(Even,409%nat);(Even,423%nat)] false [];
  Row [(Even,40%nat);(Even,66%nat);(Even,100%nat);(Even,111%nat);(Even,116%nat);(Even,167%nat);(Even,214%nat);(Even,283%nat);(Even,286%nat);(Even,296%nat);(Even,346%nat);(Even,347%nat);(Even,386%nat);(Even,396%nat);(Even,414%nat);(Even,436%nat)] false [];
  Row [(Gap,142%nat)] false [];
  Row [(Even,42%nat)] false [];
  Row [(Gap,17%nat)] false [];
  Row [(Gap,162%nat)] false [];
  Row [(Even,57%nat);(Even,381%nat)] false [];
  Row [(Even,159%nat)] false [];
  Row [(Gap,145%nat)] false [];
  Row [(Even,17%nat);(Even,124%nat)] false [];
  Row [(Even,162%nat)] false [];
  Row [(Odd,194%nat)] false [];
  Row [(Even,29%nat);(Even,327%nat);(Gap,21%nat);(Gap,24%nat);(Gap,40%nat);(Gap,56%nat);(Gap,66%nat);(Gap,91%nat);(Gap,97%nat);(Gap,100%nat);(Gap,111%nat);(Gap,112%nat);(Gap,116%nat);(Gap,167%nat);(Gap,172%nat);(Gap,177%nat);(Gap,213%nat);(Gap,214%nat);(Gap,243%nat);(Gap,252%nat);(Gap,280%nat);(Gap,283%nat);(Gap,286%nat);(Gap,290%nat);(Gap,296%nat);(Gap,300%nat);(Gap,304%nat);(Gap,316%nat);(Gap,320%nat);(Gap,344%nat);(Gap,346%nat);(Gap,347%nat);(Gap,366%nat);(Gap,382%nat);(Gap,385%nat);(Gap,386%nat);(Gap,396%nat);(Gap,414%nat);(Gap,421%nat);(Gap,436%nat);(Odd,10%nat);(Odd,16%nat);(Odd,30%nat);(Odd,32%nat);(Odd,53%nat);(Odd,71%nat);(Odd,159%nat);(Odd,164%nat);(Odd,169%nat);(Odd,193%nat);(Odd,203%nat);(Odd,255%nat);(Odd,272%nat);(Odd,277%nat);(Odd,310%nat);(Odd,341%nat);(Odd,408%nat)] false [];
  Row [(Even,147%nat)] false [];
  Row [(Even,170%nat);(Odd,370%nat)] false [];
  Row [(Gap,179%nat)] false [];
  Row [(Odd,155%nat)] false [];
  Row [(Gap,191%nat)] false [];
  Row [(Gap,149%nat)] false [];
  Row [(Gap,167%nat)] false [];
  Row [(Odd,323%nat)] false [];
  Row [(Gap,170%nat)] false [];
  Row [(Even,174%nat);(Odd,371%nat)] false [];
  Row [(Even,208%nat)] false [];
  Row [(Gap,331%nat)] false [];
  Row [(Gap,175%nat)] false [];
  Row [(Even,36%nat)] false [];
  Row [(Gap,165%nat)] false [];
  Row [(Even,175%nat)] false [];
  Row [(Even,343%nat);(Odd,43%nat)] false [];
  Row [(Even,169%nat)] false [];
  Row [(Even,167%nat)] false [];
  Row [(Even,89%nat);(Odd,187%nat)] false [];
  Row [(Even,116%nat)] false [];
  Row [(Gap,4%nat);(Gap,7%nat);(Gap,14%nat);(Gap,19%nat);(Gap,20%nat);(Gap,25%nat);(Gap,61%nat);(Gap,64%nat);(Gap,107%nat);(Gap,114%nat);(Gap,128%nat);(Gap,129%nat);(Gap,148%nat);(Gap,158%nat);(Gap,161%nat);(Gap,166%nat);(Gap,173%nat);(Gap,181%nat);(Gap,182%nat);(Gap,185%nat);(Gap,198%nat);(Gap,221%nat);(Gap,225%nat);(Gap,261%nat);(Gap,265%nat);(Gap,267%nat);(Gap,282%nat);(Gap,294%nat);(Gap,333%nat);(Gap,360%nat);(Gap,369%nat);(Gap,395%nat);(Gap,403%nat);(Gap,417%nat);(Gap,419%nat);(Gap,425%nat);(Gap,426%nat);(Gap,432%nat);(Odd,6%nat);(Odd,58%nat);(Odd,68%nat);(Odd,92%nat);(Odd,101%nat);(Odd,266%nat);(Odd,270%nat);(Odd,329%nat)] false [];
  Row [(Gap,413%nat)] false [];
  Row [(Gap,187%nat)] false [];
  Row [(Gap,224%nat)] false [];
  Row [(Gap,189%nat)] false [];
  Row [(Gap,270%nat)] false [];
  Row [(Odd,171%nat)] false [];
  Row [(Gap,433%nat)] false [];
  Row [(Gap,310%nat)] false [];
  Row [(Even,32%nat)] false [];
  Row [(Odd,199%nat)] false [];
  Row [(Gap,197%nat)] false [];
  Row [(Even,189%nat);(Gap,10%nat);(Gap,16%nat);(Gap,32%nat);(Gap,53%nat);(Gap,54%nat);(Gap,88%nat);(Gap,113%nat);(Gap,151%nat);(Gap,169%nat);(Gap,255%nat);(Gap,272%nat);(Gap,341%nat);(Gap,348%nat);(Gap,393%nat);(Gap,408%nat);(Odd,152%nat);(Odd,275%nat);(Odd,291%nat)] false [];
  Row [(Even,53%nat);(Even,310%nat);(Odd,165%nat)] false [];
  Row [(Even,286%nat)] false [];
  Row [(Gap,199%nat)] false [];
  Row [(Odd,202%nat)] false [];
  Row [(Even,203%nat)] false [];
  Row [(Odd,86%nat)] false [];
  Row [(Gap,202%nat)] false [];
  Row [(Even,197%nat)] false [];
  Row [(Even,73%nat);(Even,176%nat);(Even,370%nat);(Odd,170%nat);(Odd,188%nat);(Odd,367%nat);(Odd,420%nat)] false [];
  Row [(Even,99%nat)] false [];
  Row [(Gap,68%nat)] false [];
  Row [(Odd,420%nat)] false [];
  Row [(Even,293%nat)] false [];
  Row [(Gap,226%nat)] false [];
  Row [(Odd,218%nat)] false [];
  Row [(Gap,214%nat)] false [];
  Row [(Gap,40%nat)] false [];
  Row [(Even,193%nat)] false [];
  Row [(Even,199%nat)] false [];
  Row [(Gap,218%nat)] false [];
  Row [(Odd,219%nat)] false [];
  Row [(Even,220%nat)] false [];
  Row [(Gap,322%nat)] false [];
  Row [(Gap,355%nat)] false [];
  Row [(Even,235%nat)] false [];
  Row [(Gap,205%nat)] false [];
  Row [(Even,152%nat);(Even,291%nat);(Odd,140%nat)] false [];
  Row [(Even,228%nat)] false [];
  Row [(Even,229%nat)] false [];
  Row [(Even,229%nat);(Gap,305%nat);(Gap,306%nat);(Odd,305%nat)] false [];
  Row [(Gap,222%nat)] false [];
  Row [(Even,124%nat)] false [];
  Row [(Gap,195%nat)] false [];
  Row [(Gap,334%nat)] false [];
  Row [(Gap,230%nat)] false [];
  Row [(Gap,268%nat)] false [];
  Row [(Gap,86%nat)] false [];
  Row [(Gap,208%nat)] false [];
  Row [(Even,89%nat);(Even,314%nat);(Odd,115%nat)] false [];
  Row [(Gap,60%nat)] false [];
  Row [(Even,240%nat);(Gap,7%nat);(Gap,11%nat);(Gap,21%nat);(Gap,23%nat);(Gap,31%nat);(Gap,42%nat);(Gap,62%nat);(Gap,65%nat);(Gap,72%nat);(Gap,77%nat);(Gap,82%nat);(Gap,97%nat);(Gap,103%nat);(Gap,120%nat);(Gap,150%nat);(Gap,160%nat);(Gap,172%nat);(Gap,183%nat);(Gap,192%nat);(Gap,196%nat);(Gap,197%nat);(Gap,204%nat);(Gap,215%nat);(Gap,216%nat);(Gap,217%nat);(Gap,246%nat);(Gap,254%nat);(Gap,267%nat);(Gap,276%nat);(Gap,280%nat);(Gap,284%nat);(Gap,293%nat);(Gap,304%nat);(Gap,311%nat);(Gap,316%nat);(Gap,333%nat);(Gap,344%nat);(Gap,352%nat);(Gap,379%nat);(Gap,380%nat);(Gap,387%nat);(Gap,389%nat);(Gap,410%nat);(Gap,421%nat);(Gap,435%nat);(Odd,78%nat);(Odd,167%nat);(Odd,226%nat);(Odd,244%nat);(Odd,286%nat);(Odd,296%nat);(Odd,328%nat);(Odd,331%nat);(Odd,343%nat);(Odd,351%nat);(Odd,383%nat);(Odd,396%nat);(Odd,414%nat);(Odd,429%nat)] false [];
  Row [(Gap,240%nat)] false [];
  Row [(Even,145%nat)] false [];
  Row [(Gap,244%nat)] false [];
  Row [(Even,87%nat);(Odd,241%nat)] false [];
  Row [(Even,343%nat);(Odd,240%nat)] false [];
  Row [(Even,277%nat)] false [];
  Row [(Gap,275%nat)] false [];
  Row [(Gap,241%nat)] false [];
  Row [(Even,245%nat)] false [];
  Row [(Gap,140%nat)] false [];
  Row [(Odd,278%nat)] false [];
  Row [(Even,334%nat)] false [];
  Row [(Gap,264%nat)] false [];
  Row [(Gap,256%nat)] false [];
  Row [(Odd,236%nat)] false [];
  Row [(Even,10%nat);(Even,272%nat);(Even,334%nat);(Even,341%nat)] false [];
  Row [(Even,359%nat);(Odd,374%nat)] false [];
  Row [(Gap,18%nat)] false [];
  Row [(Odd,239%nat)] false [];
  Row [(Even,256%nat)] false [];
  Row [(Even,355%nat)] false [];
  Row [(Even,433%nat)] false [];
  Row [(Gap,152%nat)] false [];
  Row [(Even,6%nat);(Even,266%nat);(Even,270%nat);(Even,329%nat)] false [];
  Row [(Gap,251%nat)] false [];
  Row [(Odd,269%nat)] false [];
  Row [(Gap,266%nat)] false [];
  Row [(Gap,168%nat)] false [];
  Row [(Even,241%nat);(Gap,12%nat);(Gap,30%nat);(Gap,71%nat);(Gap,164%nat);(Gap,193%nat);(Gap,203%nat);(Gap,233%nat);(Gap,273%nat);(Gap,277%nat);(Gap,342%nat);(Odd,87%nat)] false [];
  Row [(Odd,208%nat)] false [];
  Row [(Gap,269%nat)] false [];
  Row [(Odd,271%nat)] false [];
  Row [(Gap,272%nat)] false [];
  Row [(Gap,291%nat)] false [];
  Row [(Even,78%nat);(Even,167%nat);(Even,286%nat);(Even,296%nat);(Even,328%nat);(Even,331%nat);(Even,351%nat);(Even,383%nat);(Even,396%nat);(Even,414%nat);(Even,429%nat)] false [];
  Row [(Even,255%nat)] false [];
  Row [(Odd,93%nat)] false [];
  Row [(Even,370%nat);(Odd,170%nat)] false [];
  Row [(Gap,171%nat)] false [];
  Row [(Even,272%nat)] false [];
  Row [(Even,266%nat)] false [];
  Row [(Even,259%nat)] false [];
  Row [(Odd,285%nat)] false [];
  Row [(Gap,283%nat)] false [];
  Row [(Even,269%nat)] false [];
  Row [(Odd,176%nat)] false [];
  Row [(Even,238%nat)] false [];
  Row [(Gap,285%nat)] false [];
  Row [(Odd,288%nat)] false [];
  Row [(Gap,383%nat)] false [];
  Row [(Even,226%nat);(Even,244%nat)] false [];
  Row [(Gap,278%nat)] false [];
  Row [(Odd,149%nat)] false [];
  Row [(Even,289%nat)] false [];
  Row [(Even,283%nat)] false [];
  Row [(Even,188%nat)] false [];
  Row [(Even,205%nat)] false [];
  Row [(Gap,248%nat)] false [];
  Row [(Gap,319%nat)] false [];
  Row [(Gap,351%nat)] false [];
  Row [(Even,8%nat);(Even,269%nat);(Even,338%nat)] false [];
  Row [(Gap,298%nat)] false [];
  Row [(Even,40%nat)] false [];
  Row [(Gap,286%nat)] false [];
  Row [(Even,375%nat)] false [];
  Row [(Gap,305%nat)] false [];
  Row [(Even,364%nat)] false [];
  Row [(Even,23%nat)] false [];
  Row [(Even,251%nat)] false [];
  Row [(Gap,2%nat);(Gap,34%nat);(Gap,55%nat);(Gap,75%nat);(Gap,94%nat);(Gap,108%nat);(Gap,206%nat);(Gap,279%nat);(Gap,354%nat);(Gap,363%nat)] false [];
  Row [(Gap,315%nat)] false [];
  Row [(Gap,301%nat)] false [];
  Row [(Gap,176%nat)] false [];
  Row [(Even,238%nat);(Even,245%nat)] false [];
  Row [(Even,52%nat);(Even,85%nat);(Even,362%nat)] false [];
  Row [(Gap,296%nat)] false [];
  Row [(Even,315%nat)] false [];
  Row [(Gap,101%nat)] false [];
  Row [(Even,58%nat);(Even,92%nat);(Even,101%nat)] false [];
  Row [(Gap,328%nat)] false [];
  Row [(Gap,324%nat)] false [];
  Row [(Odd,79%nat)] false [];
  Row [(Even,240%nat);(Gap,7%nat);(Gap,23%nat);(Gap,42%nat);(Gap,62%nat);(Gap,192%nat);(Gap,197%nat);(Gap,267%nat);(Gap,293%nat);(Gap,333%nat);(Gap,435%nat);(Odd,343%nat)] false [];
  Row [(Even,127%nat)] false [];
  Row [(Even,324%nat)] false [];
  Row [(Gap,139%nat)] false [];
  Row [(Even,327%nat);(Gap,21%nat);(Gap,24%nat);(Gap,40%nat);(Gap,56%nat);(Gap,66%nat);(Gap,91%nat);(Gap,97%nat);(Gap,100%nat);(Gap,111%nat);(Gap,112%nat);(Gap,116%nat);(Gap,167%nat);(Gap,172%nat);(Gap,177%nat);(Gap,213%nat);(Gap,214%nat);(Gap,243%nat);(Gap,252%nat);(Gap,280%nat);(Gap,283%nat);(Gap,286%nat);(Gap,290%nat);(Gap,296%nat);(Gap,300%nat);(Gap,304%nat);(Gap,316%nat);(Gap,320%nat);(Gap,344%nat);(Gap,346%nat);(Gap,347%nat);(Gap,366%nat);(Gap,382%nat);(Gap,385%nat);(Gap,386%nat);(Gap,396%nat);(Gap,414%nat);(Gap,421%nat);(Gap,436%nat);(Odd,10%nat);(Odd,16%nat);(Odd,30%nat);(Odd,32%nat);(Odd,53%nat);(Odd,71%nat);(Odd,159%nat);(Odd,164%nat);(Odd,169%nat);(Odd,193%nat);(Odd,203%nat);(Odd,255%nat);(Odd,272%nat);(Odd,277%nat);(Odd,310%nat);(Odd,341%nat);(Odd,408%nat)] false [];
  Row [(Even,275%nat)] false [];
  Row [(Odd,338%nat)] false [];
  Row [(Odd,313%nat)] false [];
  Row [(Odd,430%nat)] false [];
  Row [(Even,66%nat)] false [];
  Row [(Gap,329%nat)] false [];
  Row [(Odd,237%nat)] false [];
  Row [(Odd,312%nat)] false [];
  Row [(Gap,188%nat)] false [];
  Row [(Even,26%nat);(Even,118%nat);(Even,149%nat);(Even,199%nat);(Even,433%nat)] false [];
  Row [(Even,140%nat);(Gap,10%nat);(Gap,16%nat);(Gap,32%nat);(Gap,53%nat);(Gap,54%nat);(Gap,88%nat);(Gap,113%nat);(Gap,151%nat);(Gap,169%nat);(Gap,255%nat);(Gap,272%nat);(Gap,341%nat);(Gap,348%nat);(Gap,393%nat);(Gap,408%nat);(Odd,152%nat);(Odd,275%nat);(Odd,291%nat)] false [];
  Row [(Even,139%nat)] false [];
  Row [(Gap,338%nat)] false [];
  Row [(Odd,340%nat)] false [];
  Row [(Gap,341%nat)] false [];
  Row [(Gap,59%nat);(Gap,96%nat)] false [];
  Row [(Even,341%nat)] false [];
  Row [(Even,329%nat)] false [];
  Row [(Odd,415%nat)] false [];
  Row [(Odd,353%nat)] false [];
  Row [(Gap,362%nat)] false [];
  Row [(Gap,330%nat)] false [];
  Row [(Gap,211%nat)] false [];
  Row [(Even,298%nat);(Odd,73%nat)] false [];
  Row [(Gap,347%nat)] false [];
  Row [(Even,338%nat)] false [];
  Row [(Gap,74%nat)] false [];
  Row [(Even,336%nat)] false [];
  Row [(Gap,353%nat)] false [];
  Row [(Gap,335%nat)] false [];
  Row [(Odd,356%nat)] false [];
  Row [(Gap,38%nat)] false [];
  Row [(Even,358%nat)] false [];
  Row [(Even,347%nat)] false [];
  Row [(Even,256%nat);(Even,315%nat)] false [];
  Row [(Gap,13%nat)] false [];
  Row [(Odd,74%nat)] false [];
  Row [(Gap,250%nat)] false [];
  Row [(Gap,429%nat)] false [];
  Row [(Gap,109%nat)] false [];
  Row [(Even,335%nat)] false [];
  Row [(Even,330%nat)] false [];
  Row [(Even,9%nat);(Even,155%nat);(Even,236%nat);(Even,271%nat);(Even,292%nat);(Even,340%nat);(Even,350%nat);(Even,406%nat);(Gap,15%nat);(Gap,45%nat);(Gap,47%nat);(Gap,50%nat);(Gap,52%nat);(Gap,85%nat);(Gap,90%nat);(Gap,110%nat);(Gap,130%nat);(Gap,184%nat);(Gap,186%nat);(Gap,201%nat);(Gap,247%nat);(Gap,260%nat);(Gap,263%nat);(Gap,274%nat);(Gap,295%nat);(Gap,303%nat);(Gap,317%nat);(Gap,332%nat);(Gap,361%nat);(Gap,398%nat);(Gap,427%nat);(Odd,57%nat);(Odd,200%nat);(Odd,381%nat)] false [];
  Row [(Gap,370%nat)] false [];
  Row [(Gap,365%nat)] false [];
  Row [(Even,372%nat);(Odd,371%nat)] false [];
  Row [(Even,13%nat);(Even,239%nat);(Even,288%nat);(Even,313%nat);(Even,356%nat);(Even,371%nat);(Gap,33%nat);(Gap,39%nat);(Gap,139%nat);(Gap,364%nat);(Gap,373%nat);(Odd,174%nat);(Odd,336%nat);(Odd,388%nat);(Odd,422%nat)] false [];
  Row [(Even,376%nat)] false [];
  Row [(Even,377%nat)] false [];
  Row [(Even,378%nat)] false [];
  Row [(Even,378%nat)] true [];
  Row [(Gap,436%nat)] false [];
  Row [(Even,310%nat);(Odd,165%nat)] false [];
  Row [(Even,30%nat);(Even,71%nat);(Even,164%nat);(Even,193%nat);(Even,203%nat);(Even,277%nat)] false [];
  Row [(Gap,78%nat)] false [];
  Row [(Odd,301%nat)] false [];
  Row [(Even,257%nat)] false [];
  Row [(Even,362%nat)] false [];
  Row [(Odd,390%nat)] false [];
  Row [(Gap,386%nat)] false [];
  Row [(Gap,367%nat)] false [];
  Row [(Gap,346%nat)] false [];
  Row [(Even,118%nat)] false [];
  Row [(Gap,390%nat)] false [];
  Row [(Odd,391%nat)] false [];
  Row [(Even,381%nat)] false [];
  Row [(Gap,323%nat)] false [];
  Row [(Even,392%nat)] false [];
  Row [(Even,367%nat);(Odd,73%nat)] false [];
  Row [(Even,48%nat);(Even,180%nat);(Gap,5%nat);(Gap,46%nat);(Gap,49%nat);(Gap,102%nat);(Gap,106%nat);(Gap,126%nat);(Gap,147%nat);(Gap,157%nat);(Gap,175%nat);(Gap,178%nat);(Gap,220%nat);(Gap,223%nat);(Gap,249%nat);(Gap,259%nat);(Gap,287%nat);(Gap,289%nat);(Gap,321%nat);(Gap,326%nat);(Gap,330%nat);(Gap,349%nat);(Gap,355%nat);(Gap,357%nat);(Gap,358%nat);(Gap,392%nat);(Gap,399%nat);(Gap,405%nat);(Gap,407%nat);(Gap,409%nat);(Gap,423%nat);(Gap,424%nat);(Gap,431%nat);(Odd,41%nat);(Odd,195%nat);(Odd,264%nat);(Odd,319%nat)] false [];
  Row [(Even,386%nat)] false [];
  Row [(Even,153%nat)] false [];
  Row [(Gap,34%nat);(Gap,55%nat);(Gap,75%nat);(Gap,108%nat);(Gap,206%nat);(Gap,279%nat)] false [];
  Row [(Odd,404%nat)] false [];
  Row [(Gap,180%nat)] false [];
  Row [(Gap,401%nat)] false [];
  Row [(Even,176%nat)] false [];
  Row [(Odd,117%nat)] false [];
  Row [(Gap,404%nat)] false [];
  Row [(Gap,373%nat)] false [];
  Row [(Odd,406%nat)] false [];
  Row [(Even,388%nat);(Odd,13%nat)] false [];
  Row [(Even,408%nat)] false [];
  Row [(Gap,262%nat)] false [];
  Row [(Even,401%nat)] false [];
  Row [(Gap,394%nat)] false [];
  Row [(Even,420%nat)] false [];
  Row [(Even,149%nat)] false [];
  Row [(Even,327%nat);(Gap,21%nat);(Gap,40%nat);(Gap,56%nat);(Gap,66%nat);(Gap,91%nat);(Gap,97%nat);(Gap,100%nat);(Gap,111%nat);(Gap,116%nat);(Gap,167%nat);(Gap,172%nat);(Gap,177%nat);(Gap,213%nat);(Gap,214%nat);(Gap,243%nat);(Gap,252%nat);(Gap,280%nat);(Gap,283%nat);(Gap,286%nat);(Gap,290%nat);(Gap,296%nat);(Gap,300%nat);(Gap,304%nat);(Gap,316%nat);(Gap,320%nat);(Gap,344%nat);(Gap,346%nat);(Gap,347%nat);(Gap,366%nat);(Gap,382%nat);(Gap,385%nat);(Gap,386%nat);(Gap,396%nat);(Gap,414%nat);(Gap,421%nat);(Gap,436%nat);(Odd,10%nat);(Odd,16%nat);(Odd,30%nat);(Odd,32%nat);(Odd,53%nat);(Odd,71%nat);(Odd,159%nat);(Odd,164%nat);(Odd,169%nat);(Odd,193%nat);(Odd,203%nat);(Odd,255%nat);(Odd,272%nat);(Odd,277%nat);(Odd,310%nat);(Odd,341%nat);(Odd,408%nat)] false [];
  Row [(Gap,127%nat)] false [];
  Row [(Even,373%nat)] false [];
  Row [(Even,399%nat)] false [];
  Row [(Gap,3%nat)] false [];
  Row [(Gap,414%nat)] false [];
  Row [(Gap,420%nat)] false [];
  Row [(Even,422%nat)] false [];
  Row [(Gap,423%nat)] false [];
  Row [(Gap,293%nat)] false [];
  Row [(Even,423%nat)] false [];
  Row [(Even,414%nat)] false [];
  Row [(Gap,415%nat)] false [];
  Row [(Even,365%nat);(Odd,370%nat)] false [];
  Row [(Even,83%nat)] false [];
  Row [(Gap,409%nat)] false [];
  Row [(Odd,437%nat)] false [];
  Row [(Even,394%nat)] false [];
  Row [(Gap,416%nat)] false [];
  Row [(Odd,433%nat)] false [];
  Row [(Even,154%nat)] false [];
  Row [(Even,115%nat);(Gap,6%nat);(Gap,14%nat);(Gap,44%nat);(Gap,63%nat);(Gap,81%nat);(Gap,99%nat);(Gap,144%nat);(Gap,145%nat);(Gap,181%nat);(Gap,205%nat);(Gap,210%nat);(Gap,231%nat);(Gap,251%nat);(Gap,261%nat);(Gap,266%nat);(Gap,307%nat);(Gap,318%nat);(Gap,325%nat);(Gap,329%nat);(Gap,339%nat);(Gap,368%nat);(Gap,369%nat);(Gap,401%nat);(Gap,418%nat);(Gap,426%nat);(Odd,5%nat);(Odd,89%nat);(Odd,106%nat);(Odd,126%nat);(Odd,147%nat);(Odd,175%nat);(Odd,220%nat);(Odd,259%nat);(Odd,289%nat);(Odd,314%nat);(Odd,330%nat);(Odd,355%nat);(Odd,358%nat);(Odd,392%nat);(Odd,399%nat);(Odd,405%nat);(Odd,409%nat);(Odd,423%nat)] false [];
  Row [(Gap,437%nat)] false [];
  Row [(Gap,397%nat)] false [];
  Row [(Even,441%nat)] false [];
  Row [(Gap,452%nat)] false [];
  Row [(Even,454%nat)] false [];
  Row [(Even,444%nat)] false [];
  Row [(Even,445%nat)] false [];
  Row [(Even,446%nat)] false [];
  Row [(Even,447%nat)] false [];
  Row [(Even,448%nat)] false [];
  Row [(Even,449%nat)] false [];
  Row [(Even,450%nat)] false [];
  Row [(Even,451%nat)] false [];
  Row [(Even,453%nat)] false [];
  Row [(Gap,463%nat)] false [];
  Row [(Even,455%nat)] false [];
  Row [(Even,464%nat)] false [];
  Row [(Even,456%nat)] false [];
  Row [(Even,457%nat)] false [];
  Row [(Even,458%nat)] false [];
  Row [(Even,459%nat)] false [];
  Row [(Even,460%nat)] false [];
  Row [(Even,461%nat)] false [];
  Row [(Even,462%nat)] false [];
  Row [(Even,305%nat)] false [];
  Row [(Gap,469%nat)] false [];
  Row [(Even,465%nat)] false [];
  Row [(Even,466%nat)] false [];
  Row [(Even,467%nat)] false [];
  Row [(Even,468%nat)] false [];
  Row [(Even,470%nat)] false [];
  Row [(Gap,472%nat)] false [];
  Row [(Even,471%nat)] false [];
  Row [(Even,443%nat)] false [];
  Row [(Even,473%nat)] false [];
  Row [(Even,474%nat)] false [];
  Row [(Even,475%nat)] false [];
  Row [(Odd,476%nat)] false [];
  Row [(Even,442%nat)] false [];
  Row [(Odd,478%nat)] false [];
  Row [(Gap,485%nat)] false [];
  Row [(Even,480%nat)] false [];
  Row [(Even,482%nat)] false [];
  Row [(Gap,505%nat)] false [];
  Row [(Even,483%nat)] false [];
  Row [(Even,484%nat)] false [];
  Row [(Even,486%nat)] false [];
  Row [(Even,494%nat)] false [];
  Row [(Even,136%nat)] false [];
  Row [(Even,496%nat)] false [];
  Row [(Even,490%nat)] false [];
  Row [(Even,512%nat)] false [];
  Row [(Even,491%nat)] false [];
  Row [(Even,492%nat)] false [];
  Row [(Even,493%nat)] false [];
  Row [(Even,495%nat)] false [];
  Row [(Odd,498%nat)] false [];
  Row [(Even,497%nat)] false [];
  Row [(Even,510%nat)] false [];
  Row [(Even,501%nat)] false [];
  Row [(Even,499%nat)] false [];
  Row [(Even,500%nat)] false [];
  Row [(Odd,502%nat)] false [];
  Row [(Even,504%nat)] false [];
  Row [(Gap,503%nat)] false [];
  Row [(Gap,481%nat)] false [];
  Row [(Even,506%nat)] false [];
  Row [(Even,489%nat)] false [];
  Row [(Even,507%nat)] false [];
  Row [(Even,508%nat)] false [];
  Row [(Even,509%nat)] false [];
  Row [(Even,487%nat)] false [];
  Row [(Even,511%nat)] false [];
  Row [(Even,513%nat)] false [];
  Row [(Even,488%nat)] false [];
  Row [(Even,514%nat)] false [];
  Row [(Even,479%nat)] false [];
  Row [(Odd,516%nat)] false [];
  Row [(Even,529%nat)] false [];
  Row [(Even,519%nat)] false [];
  Row [(Even,555%nat)] false [];
  Row [(Even,521%nat)] false [];
  Row [(Gap,527%nat)] false [];
  Row [(Even,523%nat)] false [];
  Row [(Even,543%nat)] false [];
  Row [(Even,524%nat)] false [];
  Row [(Even,525%nat)] false [];
  Row [(Even,539%nat)] false [];
  Row [(Even,535%nat)] false [];
  Row [(Even,538%nat)] false [];
  Row [(Even,537%nat)] false [];
  Row [(Gap,531%nat)] false [];
  Row [(Even,545%nat)] false [];
  Row [(Odd,532%nat)] false [];
  Row [(Gap,533%nat)] false [];
  Row [(Gap,536%nat)] false [];
  Row [(Gap,552%nat)] false [];
  Row [(Even,549%nat)] false [];
  Row [(Gap,554%nat)] false [];
  Row [(Gap,534%nat)] false [];
  Row [(Even,518%nat)] false [];
  Row [(Even,540%nat)] false [];
  Row [(Even,541%nat)] false [];
  Row [(Even,542%nat)] false [];
  Row [(Even,522%nat)] false [];
  Row [(Even,544%nat)] false [];
  Row [(Even,546%nat)] false [];
  Row [(Even,550%nat)] false [];
  Row [(Even,547%nat)] false [];
  Row [(Even,548%nat)] false [];
  Row [(Even,530%nat)] false [];
  Row [(Even,179%nat)] false [];
  Row [(Even,551%nat)] false [];
  Row [(Even,553%nat)] false [];
  Row [(Odd,520%nat)] false [];
  Row [(Even,526%nat)] false [];
  Row [(Even,528%nat)] false [];
  Row [(Even,517%nat)] false []
].
Definition boundary : list trans_row := [
  TransRow [(None,Some Even,1%nat);(None,Some Odd,12%nat)] false;
  TransRow [(Some Odd,None,47%nat)] false;
  TransRow [(Some Gap,None,3%nat)] false;
  TransRow [(Some Gap,None,4%nat)] false;
  TransRow [(Some Gap,None,5%nat)] false;
  TransRow [(None,Some Gap,60%nat)] false;
  TransRow [(Some Gap,None,7%nat)] false;
  TransRow [(Some Gap,None,8%nat)] false;
  TransRow [(None,Some Gap,10%nat)] false;
  TransRow [(Some Gap,None,16%nat)] false;
  TransRow [(None,Some Gap,45%nat)] false;
  TransRow [(Some Gap,None,13%nat)] false;
  TransRow [(Some Even,None,23%nat);(Some Even,None,39%nat);(Some Even,None,51%nat);(Some Even,None,6%nat);(Some Even,None,61%nat);(Some Even,None,9%nat);(Some Odd,None,11%nat);(Some Odd,None,17%nat);(Some Odd,None,21%nat);(Some Odd,None,31%nat);(Some Odd,None,37%nat);(Some Odd,None,46%nat)] false;
  TransRow [(None,Some Even,14%nat);(None,Some Odd,15%nat)] false;
  TransRow [(None,Some Gap,12%nat)] false;
  TransRow [(None,Some Gap,1%nat)] false;
  TransRow [(None,Some Gap,0%nat)] false;
  TransRow [(Some Gap,None,18%nat)] false;
  TransRow [(Some Gap,None,19%nat)] false;
  TransRow [(None,Some Gap,20%nat)] false;
  TransRow [(None,Some Even,15%nat);(None,Some Odd,14%nat)] false;
  TransRow [(Some Gap,None,22%nat)] false;
  TransRow [(Some Gap,None,24%nat)] false;
  TransRow [(None,Some Even,12%nat);(None,Some Odd,1%nat)] false;
  TransRow [(Some Gap,None,25%nat)] false;
  TransRow [(None,Some Gap,26%nat)] false;
  TransRow [(None,Some Gap,27%nat)] false;
  TransRow [(Some Gap,None,28%nat);(None,Some Even,15%nat);(None,Some Odd,14%nat)] false;
  TransRow [(Some Gap,None,29%nat)] false;
  TransRow [(Some Gap,None,30%nat)] false;
  TransRow [(None,Some Even,27%nat)] false;
  TransRow [(Some Gap,None,32%nat)] false;
  TransRow [(Some Gap,None,33%nat)] false;
  TransRow [(Some Gap,None,35%nat)] false;
  TransRow [(None,Some Odd,45%nat)] false;
  TransRow [(Some Gap,None,36%nat)] false;
  TransRow [(None,Some Odd,27%nat)] false;
  TransRow [(Some Gap,None,38%nat)] false;
  TransRow [(Some Gap,None,40%nat)] false;
  TransRow [(Some Gap,None,44%nat)] false;
  TransRow [(Some Gap,None,41%nat)] false;
  TransRow [(Some Gap,None,42%nat)] false;
  TransRow [(Some Gap,None,43%nat)] false;
  TransRow [(None,Some Gap,30%nat)] false;
  TransRow [(Some Gap,None,50%nat)] false;
  TransRow [(Some Gap,None,56%nat);(None,Some Even,1%nat);(None,Some Odd,12%nat)] false;
  TransRow [(None,Some Gap,49%nat)] false;
  TransRow [(None,Some Gap,48%nat)] false;
  TransRow [(None,Some Gap,14%nat)] false;
  TransRow [(None,Some Gap,15%nat)] false;
  TransRow [(Some Gap,None,34%nat)] false;
  TransRow [(None,Some Gap,52%nat);(None,Some Gap,58%nat);(None,Some Odd,52%nat)] false;
  TransRow [(None,Some Even,53%nat)] false;
  TransRow [(None,Some Even,54%nat)] false;
  TransRow [(None,Some Even,55%nat)] false;
  TransRow [(None,Some Even,57%nat)] false;
  TransRow [(Some Gap,None,59%nat)] false;
  TransRow [(None,Some Even,57%nat)] true;
  TransRow [(None,Some Gap,52%nat)] false;
  TransRow [(Some Gap,None,60%nat)] false;
  TransRow [(None,Some Even,45%nat)] false;
  TransRow [(Some Gap,None,2%nat)] false
].
Definition starts : list nat := [0%nat;440%nat;477%nat;515%nat].
Definition boundary_start : nat := 0%nat.
Local Close Scope N_scope.
Module Generate.
Import Uint63.

(* Worklists only discover candidates. The checks below verify the resulting
   ordinary lists, so generation adds no assumptions to the nonhalting proof.
   Exhausting the fixed search budget produces an empty candidate, which fails
   the initial-state checks. *)
Definition ix n := Uint63.of_Z (Z.of_nat n).
Definition array_of_list {A} (d:A) (xs:list A) :=
  fst (fold_left (fun '(a,i) x => (PArray.set a i x, Uint63.add i 1)) xs
    (PArray.make (ix (List.length xs)) d, 0%uint63)).
Definition graph := Eval vm_compute in array_of_list (Row [] false []) body_graph.
Definition trans := Eval vm_compute in array_of_list (TransRow [] false) boundary.

(* These inverse formulas only construct a candidate. The checker uses
   forward atoms and their lower-simulation proof. *)
Definition cap_need (b:bool) (g:nat) (t:N) : N :=
  (if b then match g with
   | 0%nat => 2*((t-2+3)/4)
   | 1%nat => 2*((t-1+3)/4)
   | 2%nat => 2*N.max 1 ((t+4)/4)
   | 3%nat => 2*((t-3+7)/8)
   | _ => 2*N.max 1 ((t+8)/8)
   end else match g with
   | 0%nat => t+3
   | 1%nat => 2*((t+3)/4)
   | 2%nat => 2*N.max 1 ((t+4)/4)
   | 3%nat => 2*N.max 1 ((t+6)/4)
   | _ => 2*N.max 1 ((t+10)/8)
   end)%N.
Definition predecessors := Eval vm_compute in
  fold_left (fun a u =>
    fold_left (fun a '(c,v) =>
      PArray.set a (ix v) ((c,u)::PArray.get a (ix v)))
      (edges (PArray.get graph (ix u))) a)
    (seq 0 (List.length body_graph)) (PArray.make (ix (List.length body_graph)) []).
Definition cap_index u g := Uint63.add (Uint63.mul (ix u) 5) (ix g).
Definition cap_update u g s '(a,work) :=
  let old := PArray.get a (cap_index u g) in
  if N.eqb old 0 || N.ltb old (N.succ s) then
    (PArray.set a (cap_index u g) (N.succ s), (u,g)::work)
  else (a,work).
Definition cap_step u g '(a,work) :=
  let s := N.pred (PArray.get a (cap_index u g)) in
  fold_left (fun acc '(c,v) =>
    match c with
    | Gap => cap_update v (Nat.min 4 (S g)) s acc
    | _ => cap_update v 0 (cap_need (letter_eqb c Even) g s) acc
    end) (PArray.get predecessors (ix u)) (a,work).
Fixpoint cap_run fuel front back a :=
  match fuel with
  | O => None
  | S fuel =>
    match front with
    | (u,g)::front => let '(a,back) := cap_step u g (a,back) in
        cap_run fuel front back a
    | [] => match back with
      | [] => Some a
      | _ => cap_run fuel (rev back) [] a
      end
    end
  end.
Definition generate_capacity :=
  let '(a,work) := fold_left (fun acc u =>
    if pre_even body_graph (PArray.get graph (ix u)) then cap_update u 0 28 acc else acc)
    (seq 0 (List.length body_graph))
    (PArray.make (ix (List.length body_graph * 5)) 0%N, []) in
  match cap_run (N.to_nat 100000) work [] a with
  | None => []
  | Some a => map (fun u =>
      let r := PArray.get graph (ix u) in
      Row (edges r) (pre_even body_graph r)
        (map (fun g => PArray.get a (cap_index u g)) (seq 0 5)))
      (seq 0 (List.length body_graph))
  end.

Definition closure_index u v :=
  Uint63.add (Uint63.mul (ix u) (ix (List.length boundary))) (ix v).
Fixpoint pos_vertices p n :=
  match p with
  | xH => [n]
  | xO p => pos_vertices p (S n)
  | xI p => n::pos_vertices p (S n)
  end.
Definition mask_vertices m := match m with N0 => [] | Npos p => pos_vertices p 0 end.
Definition make_mask m :=
  let vs := mask_vertices m in
  let move c := encode (flat_map (fun u =>
    map snd (filter (fun e => letter_eqb (fst e) c) (edges (PArray.get graph (ix u))))) vs) in
  Mask m vs (move Odd) (move Even) (move Gap)
    (existsb (fun u => final (PArray.get graph (ix u))) vs).
Module NKey <: HashTable.HashableType.
  Definition K := N.
  Definition K_hash := HashTable.HashConcat.N_hash.
  Definition K_eq := N.eqb.
  Definition K_eq_spec := N.eqb_spec.
End NKey.
Module MaskValue <: HashTable.ValueType.
  Definition V := (nat * mask)%type.
End MaskValue.
Module Cache := HashTable.HashMap NKey MaskValue.
Definition get_cached m cache :=
  match Cache.hmap_get m cache with
  | Some (_,v) => (v,cache)
  | None =>
      let v := make_mask m in (v,Cache.hmap_set m (0,v) cache)
  end.
(* Keep only minimal output sets: a smaller set covers every obligation
   covered by one of its supersets. *)
Definition closure_push u v m '(a,work) :=
  let prev := PArray.get a (closure_index u v) in
  if existsb (fun n => subset n m) prev then (a,work)
  else (PArray.set a (closure_index u v)
    (m::filter (fun n => negb (subset m n)) prev), (u,v,m)::work).
Definition closure_step u v m '(a,work) :=
  fold_left (fun acc '(i,o,v') =>
    let us := match i with
      | None => [u]
      | Some c => map snd (filter (fun e => letter_eqb (fst e) c)
          (edges (PArray.get graph (ix u))))
      end in
    fold_left (fun acc u' => closure_push u' v' (mask_output m o) acc) us acc)
    (trans_edges (PArray.get trans (ix v))) (a,work).
Fixpoint closure_run fuel front back a cache :=
  match fuel with
  | O => None
  | S fuel =>
    match front with
    | (u,v,b)::front =>
      if existsb (N.eqb b) (PArray.get a (closure_index u v)) then
        let '(m,cache) := get_cached b cache in
        let '(a,back) := closure_step u v m (a,back) in
        closure_run fuel front back a cache
      else closure_run fuel front back a cache
    | [] => match back with
      | [] => Some (a,cache)
      | _ => closure_run fuel (rev back) [] a cache
      end
    end
  end.
Definition generate_closure :=
  let initial := encode starts in
  let '(a,work) := fold_left (fun acc u => closure_push u boundary_start initial acc) starts
    (PArray.make (ix (List.length body_graph * List.length boundary)) [], []) in
  match closure_run (N.to_nat 100000) work [] a (Cache.hmap_make 1024) with
  | None => ([],[])
  | Some (a,cache) =>
      (* Discard transient masks and number the surviving ones densely. *)
      let cells := flat_map (fun u => map (fun v => PArray.get a (closure_index u v))
        (seq 0 (List.length boundary))) (seq 0 (List.length body_graph)) in
      let '(cache',ms') := fold_left (fun '(cache',ms') ns =>
        fold_left (fun '(cache',ms') m =>
          match Cache.hmap_get m cache' with
          | Some _ => (cache',ms')
          | None => let v := match Cache.hmap_get m cache with
                        | Some (_,v) => v | None => make_mask m end in
              (Cache.hmap_set m (List.length ms',v) cache',v::ms')
          end) ns (cache',ms')) cells (Cache.hmap_make 1024,[]) in
      (rev ms',
      map (fun u => map (fun v =>
        map (fun m => match Cache.hmap_get m cache' with
          | Some (k,_) => k | None => List.length ms' end)
          (PArray.get a (closure_index u v))) (seq 0 (List.length boundary)))
        (seq 0 (List.length body_graph)))
  end.
End Generate.
Definition core_graph := Eval vm_compute in Generate.generate_capacity.
Definition closure_certificate := Eval vm_compute in Generate.generate_closure.
Definition masks := fst closure_certificate.
Definition closure_table := snd closure_certificate.
Local Open Scope N_scope.
Lemma capacity_checked : check core_graph = true.
Proof. vm_compute; reflexivity. Qed.
Lemma masks_checked : masks_check body_graph masks = true.
Proof. vm_compute; reflexivity. Qed.
Lemma closure_checked : closure_check body_graph boundary masks closure_table = true.
Proof. vm_compute; reflexivity. Qed.
Lemma initial_checked : initial_check body_graph boundary masks closure_table starts boundary_start = true.
Proof. vm_compute; reflexivity. Qed.
Lemma initial_capacities : forallb (fun q : nat =>
  Nat.ltb q (length core_graph) && (0 <? bound core_graph q 0)%N &&
  (bound core_graph q 0 <=? 12)%N) starts = true.
Proof. vm_compute; reflexivity. Qed.
Theorem closed xs ys v :
  trans_path boundary boundary_start xs ys v -> trans_final (tnode boundary v) = true ->
  language body_graph starts xs -> language body_graph starts ys.
Proof.
  intros HT HF HL.
  exact (language_closed body_graph boundary masks closure_table starts boundary_start xs ys v
    masks_checked closure_checked initial_checked HT HF HL).
Qed.
End Certificate.
Import Certificate.


Module Words.
Definition tr := trans_path boundary.
Definition ready (flip:bool) : nat := if flip then 1 else 12.
Definition guess (flip:bool) (d:letter) := if flip then match d with Odd => Even | Even => Odd | Gap => Gap end else d.

Lemma start_path f : tr 0 [] [guess f Odd] (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 0%nat [(None,Some Even,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 0%nat [(None,Some Odd,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma bare_path f : tr (ready (negb f)) [Odd] [Gap;Gap;Gap] (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 12%nat [(Some Odd,None,46%nat);(None,Some Gap,49%nat);(None,Some Gap,15%nat);(None,Some Gap,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 1%nat [(Some Odd,None,47%nat);(None,Some Gap,48%nat);(None,Some Gap,14%nat);(None,Some Gap,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma p0_path f : tr 12 [Even] ([] ++ [guess f Even] ++ []) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 12%nat [(Some Even,None,23%nat);(None,Some Odd,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 12%nat [(Some Even,None,23%nat);(None,Some Even,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma p1_path f : tr 12 [Even;Gap] ([Gap] ++ [guess f Odd] ++ []) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 12%nat [(Some Even,None,9%nat);(Some Gap,None,16%nat);(None,Some Gap,0%nat);(None,Some Even,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 12%nat [(Some Even,None,9%nat);(Some Gap,None,16%nat);(None,Some Gap,0%nat);(None,Some Odd,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma q1_path f : tr 12 [Odd;Gap] ([] ++ [guess f Even] ++ [Gap]) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 12%nat [(Some Odd,None,11%nat);(Some Gap,None,13%nat);(None,Some Odd,15%nat);(None,Some Gap,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 12%nat [(Some Odd,None,11%nat);(Some Gap,None,13%nat);(None,Some Even,14%nat);(None,Some Gap,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma q2_path f : tr 12 [Odd;Gap;Gap] ([Gap] ++ [guess f Odd] ++ [Gap]) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 12%nat [(Some Odd,None,17%nat);(Some Gap,None,18%nat);(Some Gap,None,19%nat);(None,Some Gap,20%nat);(None,Some Even,15%nat);(None,Some Gap,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 12%nat [(Some Odd,None,17%nat);(Some Gap,None,18%nat);(Some Gap,None,19%nat);(None,Some Gap,20%nat);(None,Some Odd,14%nat);(None,Some Gap,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma p2_prefix : tr 12 [Even;Gap;Gap] [Gap;Gap] 45.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,6%nat);(Some Gap,None,7%nat);(Some Gap,None,8%nat);(None,Some Gap,10%nat);(None,Some Gap,45%nat)]); vm_compute; reflexivity. Qed.

Lemma p3_prefix : tr 12 [Even;Gap;Gap;Gap] [Odd] 45.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,39%nat);(Some Gap,None,44%nat);(Some Gap,None,50%nat);(Some Gap,None,34%nat);(None,Some Odd,45%nat)]); vm_compute; reflexivity. Qed.

Lemma p4_prefix : tr 12 [Even;Gap;Gap;Gap;Gap] [Gap;Even] 45.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,61%nat);(Some Gap,None,2%nat);(Some Gap,None,3%nat);(Some Gap,None,4%nat);(Some Gap,None,5%nat);(None,Some Gap,60%nat);(None,Some Even,45%nat)]); vm_compute; reflexivity. Qed.

Lemma q3_prefix : tr 12 [Odd;Gap;Gap;Gap] [Gap;Gap] 27.
Proof. apply (trace_spec boundary 12%nat [(Some Odd,None,21%nat);(Some Gap,None,22%nat);(Some Gap,None,24%nat);(Some Gap,None,25%nat);(None,Some Gap,26%nat);(None,Some Gap,27%nat)]); vm_compute; reflexivity. Qed.

Lemma q4_prefix : tr 12 [Odd;Gap;Gap;Gap;Gap] [Odd] 27.
Proof. apply (trace_spec boundary 12%nat [(Some Odd,None,31%nat);(Some Gap,None,32%nat);(Some Gap,None,33%nat);(Some Gap,None,35%nat);(Some Gap,None,36%nat);(None,Some Odd,27%nat)]); vm_compute; reflexivity. Qed.

Lemma q5_prefix : tr 12 [Odd;Gap;Gap;Gap;Gap;Gap] [Gap;Even] 27.
Proof. apply (trace_spec boundary 12%nat [(Some Odd,None,37%nat);(Some Gap,None,38%nat);(Some Gap,None,40%nat);(Some Gap,None,41%nat);(Some Gap,None,42%nat);(Some Gap,None,43%nat);(None,Some Gap,30%nat);(None,Some Even,27%nat)]); vm_compute; reflexivity. Qed.

Lemma p_loop : tr 45 [Gap;Gap;Gap] [Even] 45.
Proof. apply (trace_spec boundary 45%nat [(Some Gap,None,56%nat);(Some Gap,None,59%nat);(Some Gap,None,60%nat);(None,Some Even,45%nat)]); vm_compute; reflexivity. Qed.

Lemma p_suffix f : tr 45 [] ([guess f Odd] ++ []) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 45%nat [(None,Some Even,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 45%nat [(None,Some Odd,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma q_loop : tr 27 [Gap;Gap;Gap] [Even] 27.
Proof. apply (trace_spec boundary 27%nat [(Some Gap,None,28%nat);(Some Gap,None,29%nat);(Some Gap,None,30%nat);(None,Some Even,27%nat)]); vm_compute; reflexivity. Qed.

Lemma q_suffix f : tr 27 [] ([guess f Odd] ++ [Gap]) (ready f).
Proof. destruct f.

  - apply (trace_spec boundary 27%nat [(None,Some Even,15%nat);(None,Some Gap,1%nat)]); vm_compute; reflexivity.

  - apply (trace_spec boundary 27%nat [(None,Some Odd,14%nat);(None,Some Gap,12%nat)]); vm_compute; reflexivity.

Qed.

Lemma tail0_prefix : tr 12 [Even] [Odd;Even;Even;Even;Even] 57.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,51%nat);(None,Some Odd,52%nat);(None,Some Even,53%nat);(None,Some Even,54%nat);(None,Some Even,55%nat);(None,Some Even,57%nat)]); vm_compute; reflexivity. Qed.

Lemma tail1_prefix : tr 12 [Even] [Gap;Even;Even;Even;Even] 57.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,51%nat);(None,Some Gap,52%nat);(None,Some Even,53%nat);(None,Some Even,54%nat);(None,Some Even,55%nat);(None,Some Even,57%nat)]); vm_compute; reflexivity. Qed.

Lemma tail2_prefix : tr 12 [Even] [Gap;Gap;Even;Even;Even;Even] 57.
Proof. apply (trace_spec boundary 12%nat [(Some Even,None,51%nat);(None,Some Gap,58%nat);(None,Some Gap,52%nat);(None,Some Even,53%nat);(None,Some Even,54%nat);(None,Some Even,55%nat);(None,Some Even,57%nat)]); vm_compute; reflexivity. Qed.

Lemma tail_loop : tr 57 [] [Even] 57.
Proof. apply (trace_spec boundary 57%nat [(None,Some Even,57%nat)]); vm_compute; reflexivity. Qed.

Lemma pump k n : tr k [Gap;Gap;Gap] [Even] k ->
  tr k (repeat Gap (n*3)) (repeat Even n) k.
Proof.
  intro H; induction n.
  - constructor.
  - change (tr k ([Gap;Gap;Gap] ++ repeat Gap (n*3)) ([Even] ++ repeat Even n) k).
    eapply trans_path_app; [exact H|exact IHn].
Qed.

Lemma branch c g pre k suf n q :
  tr 12 (c::repeat Gap g) pre k ->
  tr k [Gap;Gap;Gap] [Even] k -> tr k [] suf q ->
  tr 12 (c::repeat Gap (g+n*3)) (pre ++ repeat Even n ++ suf) q.
Proof.
  intros Hpre Hloop Hsuf.
  rewrite repeat_app.
  change (tr 12 ((c::repeat Gap g) ++ repeat Gap (n*3)) (pre ++ repeat Even n ++ suf) q).
  eapply trans_path_app; [exact Hpre|].
  rewrite <- (app_nil_r (repeat Gap (n*3))).
  eapply trans_path_app; [apply pump,Hloop|exact Hsuf].
Qed.

Inductive block :=
| BP0 | BP1 | BP2 (n:nat) | BP3 (n:nat) | BP4 (n:nat)
| BQ0 | BQ1 | BQ2 | BQ3 (n:nat) | BQ4 (n:nat) | BQ5 (n:nat).

Definition even_block b :=
  match b with BP0 | BP1 | BP2 _ | BP3 _ | BP4 _ => true | _ => false end.
Definition symbol b := if even_block b then Even else Odd.
Definition gaps b :=
  match b with
  | BP0 | BQ0 => 0 | BP1 | BQ1 => 1 | BQ2 => 2
  | BP2 n => 2+n*3 | BP3 n | BQ3 n => 3+n*3
  | BP4 n | BQ4 n => 4+n*3 | BQ5 n => 5+n*3
  end.
Definition input b := symbol b :: repeat Gap (gaps b).
Definition last_digit b := match b with BP0 | BQ1 => Even | _ => Odd end.
Definition front b :=
  match b with
  | BP1 | BQ2 => [Gap]
  | BP2 n | BQ3 n => [Gap;Gap] ++ repeat Even n
  | BP3 n | BQ4 n => Odd :: repeat Even n
  | BP4 n | BQ5 n => [Gap;Even] ++ repeat Even n
  | _ => []
  end.
Definition back b := if even_block b then [] else [Gap].
Definition output b f := front b ++ [guess f (last_digit b)] ++ back b.

Lemma block_path b f : b <> BQ0 -> tr 12 (input b) (output b f) (ready f).
Proof.
  destruct b; intro H; try contradiction;
    cbn [tr input symbol even_block gaps output front last_digit back].
  - apply p0_path.
  - apply p1_path.
  - eapply (branch Even 2 [Gap;Gap] 45 ([guess f Odd] ++ []) n (ready f));
      [exact p2_prefix|exact p_loop|apply p_suffix].
  - eapply (branch Even 3 [Odd] 45 ([guess f Odd] ++ []) n (ready f));
      [exact p3_prefix|exact p_loop|apply p_suffix].
  - eapply (branch Even 4 [Gap;Even] 45 ([guess f Odd] ++ []) n (ready f));
      [exact p4_prefix|exact p_loop|apply p_suffix].
  - apply q1_path.
  - apply q2_path.
  - eapply (branch Odd 3 [Gap;Gap] 27 ([guess f Odd] ++ [Gap]) n (ready f));
      [exact q3_prefix|exact q_loop|apply q_suffix].
  - eapply (branch Odd 4 [Odd] 27 ([guess f Odd] ++ [Gap]) n (ready f));
      [exact q4_prefix|exact q_loop|apply q_suffix].
  - eapply (branch Odd 5 [Gap;Even] 27 ([guess f Odd] ++ [Gap]) n (ready f));
      [exact q5_prefix|exact q_loop|apply q_suffix].
Qed.

Definition inputs xs := flat_map input xs.
Fixpoint needs_flip xs :=
  match xs with BQ0::xs => negb (needs_flip xs) | _ => false end.
Fixpoint outputs xs :=
  match xs with
  | [] => []
  | BQ0::xs => [Gap;Gap;Gap] ++ outputs xs
  | b::xs => output b (needs_flip xs) ++ outputs xs
  end.

Lemma blocks_path xs : tr (ready (needs_flip xs)) (inputs xs) (outputs xs) 12.
Proof.
  induction xs as [|b xs IH].
  - constructor.
  - destruct b; cbn [needs_flip inputs flat_map outputs];
      eapply trans_path_app; try exact IH;
      try (apply block_path; discriminate).
    apply bare_path.
Qed.

Definition tail_word j := match j with 0 => [Odd] | 1 => [Gap] | _ => [Gap;Gap] end.
Definition tail_count j q := q + match j with 0 => 0 | _ => 1 end.

Lemma tail_repeats n : tr 57 [] (repeat Even n) 57.
Proof.
  induction n; [constructor|].
  change (tr 57 ([]++[]) ([Even]++repeat Even n) 57).
  eapply trans_path_app; [exact tail_loop|exact IHn].
Qed.

Lemma tail_path j n : j<3 -> tr 12 [Even] (tail_word j ++ repeat Even (4+n)) 57.
Proof.
  intro Hj; rewrite repeat_app, app_assoc.
  change (tr 12 ([Even]++[]) ((tail_word j ++ repeat Even 4) ++ repeat Even n) 57).
  eapply trans_path_app; [|apply tail_repeats].
  destruct j as [|[|[|j]]]; try lia;
    [exact tail0_prefix|exact tail1_prefix|exact tail2_prefix].
Qed.

Definition rewritten xs := guess (needs_flip xs) Odd :: outputs xs.

Theorem boundary_path xs j n : j<3 ->
  tr boundary_start (inputs xs ++ [Even])
    (rewritten xs ++ tail_word j ++ repeat Even (4+n)) 57.
Proof.
  intro Hj.
  unfold rewritten.
  change (tr 0 ([] ++ (inputs xs ++ [Even]))
    ([guess (needs_flip xs) Odd] ++ (outputs xs ++ tail_word j ++ repeat Even (4+n))) 57).
  eapply trans_path_app; [apply start_path|].
  eapply trans_path_app; [apply blocks_path|apply tail_path,Hj].
Qed.

Theorem macro_closed xs j n : j<3 ->
  language body_graph starts (inputs xs ++ [Even]) ->
  language body_graph starts (rewritten xs ++ tail_word j ++ repeat Even (4+n)).
Proof.
  intros Hj HL.
  apply (Certificate.closed _ _ 57 (boundary_path xs j n Hj)); [reflexivity|exact HL].
Qed.

Inductive blocks_run : N -> list block -> N -> Prop :=
| blocks_nil s : blocks_run s [] s
| blocks_cons s b s' xs s'' :
    atom (even_block b) (gaps b) s = Some s' -> blocks_run s' xs s'' ->
    blocks_run s (b::xs) s''.

(* Backward budgets propagate through leading gaps and then discharge one
   existing physical block at a time. No alternative block semantics is used. *)
Lemma checked_blocks graph xs : forall u q,
  check graph = true -> u < length graph -> path graph u (inputs xs) q ->
  final (node graph q) = true ->
  (0 < bound graph u 0)%N /\ forall s, (bound graph u 0-1 <= s)%N ->
    exists t, blocks_run s xs t /\ (28 <= t)%N.
Proof.
  induction xs as [|b xs IH]; intros u q HC Hu HP HF.
  - inversion HP; subst q.
    pose proof (checked_final graph u HC Hu HF) as Hbudget.
    split; [lia|]; intros s Hs; exists s; split; [constructor|lia].
  - change (path graph u (symbol b :: repeat Gap (gaps b) ++ inputs xs) q) in HP.
    inversion HP as [|u0 c v w q0 HE HR]; subst.
    destruct (checked_edge graph u (symbol b) v HC Hu HE) as [Hv _].
    destruct (checked_gaps graph v (gaps b) (inputs xs) q HC Hv HR)
      as [z [Hz [HZ HB]]].
    destruct (IH z q HC Hz HZ HF) as [Hb HS].
    specialize (HB Hb).
    unfold symbol in HE.
    destruct (checked_digit graph u v (even_block b) (gaps b) HC Hu HE ltac:(lia))
      as [Hu0 Hstep].
    split; [exact Hu0|]; intros s Hs.
    destruct (Hstep s Hs) as [s' [HA Hs']].
    destruct (HS s' ltac:(lia)) as [t [HT Ht]].
    exists t; split; [econstructor; eauto|exact Ht].
Qed.

Lemma graph_edges : map edges body_graph = map edges core_graph.
Proof. vm_compute; reflexivity. Qed.
Lemma graph_core : map final core_graph = map (pre_even body_graph) body_graph.
Proof. vm_compute; reflexivity. Qed.

Theorem blocks_admissible xs :
  language body_graph starts (inputs xs ++ [Even]) ->
  exists t, blocks_run 11 xs t /\ (28<=t)%N.
Proof.
  intros [u [f [HI [HP HF]]]].
  destruct (path_core body_graph core_graph (inputs xs)
    (same_edges _ _ graph_edges) (same_pre_even _ _ graph_core) u f HP HF)
    as [q [Hpath Hfinal]].
  pose proof initial_capacities as HC.
  apply forallb_forall with (x:=u) in HC; auto.
  repeat rewrite andb_true_iff in HC; destruct HC as [[Hu _] HB].
  apply Nat.ltb_lt in Hu; apply N.leb_le in HB.
  destruct (checked_blocks core_graph xs u q capacity_checked Hu Hpath Hfinal) as [_ HS].
  apply HS; lia.
Qed.

Definition decode (p:bool) g :=
  if p then
    match g with
    | 0 => BP0 | 1 => BP1 | 2 => BP2 0
    | _ => match g mod 3 with 0 => BP3 (g/3-1) | 1 => BP4 (g/3-1) | _ => BP2 (g/3) end
    end
  else
    match g with
    | 0 => BQ0 | 1 => BQ1 | 2 => BQ2
    | _ => match g mod 3 with 0 => BQ3 (g/3-1) | 1 => BQ4 (g/3-1) | _ => BQ5 (g/3-1) end
    end.

Lemma input_decode p g : input (decode p g) = (if p then Even else Odd) :: repeat Gap g.
Proof.
  pose proof (Nat.div_mod g 3 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound g 3 ltac:(lia)) as Hmod.
  destruct p; destruct g as [|[|[|g]]]; try reflexivity;
    unfold decode; cbv beta iota zeta;
    destruct (S (S (S g)) mod 3) as [|[|[|j]]] eqn:E; try lia;
    unfold input, symbol, even_block, gaps; cbv beta iota zeta;
    repeat f_equal; lia.
Qed.

Lemma words_blocks w : exists g xs, w = repeat Gap g ++ inputs xs.
Proof.
  induction w as [|c w IH].
  - exists 0,[]; reflexivity.
  - destruct IH as [g [xs Hw]]; unfold inputs in Hw.
    destruct c.
    + exists 0,(decode false g::xs); cbn [repeat app inputs flat_map].
      rewrite input_decode; cbn [app]; rewrite <-Hw; reflexivity.
    + exists 0,(decode true g::xs); cbn [repeat app inputs flat_map].
      rewrite input_decode; cbn [app]; rewrite <-Hw; reflexivity.
    + exists (S g),xs; cbn [repeat app]; f_equal; exact Hw.
Qed.

Lemma digit_blocks d w : d<>Gap -> exists xs, inputs xs = d::w.
Proof.
  intro Hd; destruct (words_blocks w) as [g [xs Hw]]; unfold inputs in Hw.
  destruct d; try contradiction.
  - exists (decode false g::xs); cbn [inputs flat_map]; rewrite input_decode; cbn [app]; f_equal; symmetry; exact Hw.
  - exists (decode true g::xs); cbn [inputs flat_map]; rewrite input_decode; cbn [app]; f_equal; symmetry; exact Hw.
Qed.

Definition initial_blocks := [BP4 0;BP0;BP0;BP0;BQ0] ++ repeat BP0 31.
Definition initial_word := inputs initial_blocks ++ [Even].

Ltac word_trace qs :=
  lazymatch qs with
  | [] => constructor
  | ?q::?qs => eapply path_cons with (q':=q);
      [vm_compute; intuition|word_trace qs]
  end.

Lemma initial_member : language body_graph starts initial_word.
Proof.
  exists 440,378; split; [vm_compute; auto|split].
  - word_trace [441;452;463;469;472;473;474;475;476;442;454;464;465;466;
      467;468;470;471;443;444;445;446;447;448;449;450;451;453;455;456;
      457;458;459;460;461;462;305;375;376;377;378].
  - reflexivity.
Qed.

Lemma repeat_snoc (a:letter) n : repeat a n ++ [a] = repeat a (S n).
Proof.
  change (repeat a n ++ repeat a 1 = repeat a (S n)).
  rewrite <-repeat_app; f_equal; lia.
Qed.
End Words.
Import Words.


From BusyCoq Require Import Individual62.
Require Import List PeanoNat Lia String NArith ZArith ZifyNat.
Import ListNotations.
Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC0RA_1RA0LD_0RE0LF_0LB---_0RF0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(* Left-hand words are stored nearest cell first, as elsewhere in BusyCoq. *)
Definition e1 := <[0;1;0;1;1;1].
Definition e2 := <[0;1;1;1;1;1].
Definition e3 := <[0;0;1;1;1;1].
Definition e4 := <[1;1;1;1;1;1].
Definition gap n := [1;0]^^n.
Definition workP := [0;0;1;0;0;1].
Definition workQ := [0;1;1;0;0;1].

(* J returns to the same cell, now containing 1. A normal return then
   crosses the right-hand (01) tail and extends it by one pair. *)
Definition J (l l' : side) :=
  forall r, l {{B}}> 0 >> r -->* l' {{B}}> 1 >> r.

Lemma J_enter l l' :
  J l l' -> forall r, l <{{C}} 1 >> r -->* l' {{B}}> 1 >> r.
Proof.
  intros H r.
  specialize (H r).
  destruct l as [x l].
  inversion H as [|c c' c'' Hstep Hrest]; subst.
  assert (HS: x >> l {{B}}> 0 >> r -[tm]-> x >> l <{{C}} 1 >> r).
  { prove_step. }
  pose proof (step_deterministic _ _ _ _ Hstep HS) as E.
  subst c'.
  exact Hrest.
Qed.

Lemma J1 l : J (l <* e1) (l <* e2).
Proof. unfold J, e1, e2; es. Qed.

Lemma J2 l : J (l <* e2) (l <* e3).
Proof. unfold J, e2, e3; es. Qed.

Lemma J3 l : J (l <* e3) (l <* e4).
Proof. unfold J, e3, e4; es. Qed.

Lemma left_four l r :
  l <* e4 {{B}}> 0 >> r -->*
  l {{B}}> 0 >> workP *> r.
Proof. unfold e4, workP; es. Qed.

Lemma carry_middle l r :
  l {{B}}> 1 >> workP *> r -->*
  l {{B}}> 0 >> workQ *> r.
Proof. unfold workP, workQ; es. Qed.

Lemma carry_return l r :
  l {{B}}> 1 >> workQ *> r -->*
  l <* e1 {{B}}> 1 >> r.
Proof. unfold workQ, e1; es. Qed.

Lemma J4 l l' l'' :
  J l l' -> J l' l'' -> J (l <* e4) (l'' <* e1).
Proof.
  unfold J; intros H1 H2 r.
  follow left_four.
  follow H1.
  follow carry_middle.
  follow H2.
  apply carry_return.
Qed.

Lemma left_gaps l r n :
  l <* gap n {{B}}> 0 >> r -->*
  l {{B}}> 0 >> [0;1]^^n *> r.
Proof.
  unfold gap.
  gen l r.
  induction n; intros.
  - finish.
  - mid (l <* [1;0]^^n {{B}}> 0 >> [0;1] *> r).
    + es.
    + follow IHn.
      rewrite lpow_shift'.
      finish.
Qed.

Lemma right_gaps l r n :
  l {{B}}> 1 >> [0;1]^^n *> r -->*
  l <* gap n {{B}}> 1 >> r.
Proof.
  unfold gap.
  gen l r.
  induction n; intros.
  - finish.
  - mid (l <* [1;0] {{B}}> 1 >> [0;1]^^n *> r).
    + es.
    + follow IHn.
      rewrite lpow_shift'.
      finish.
Qed.

Lemma J_gaps l l' n :
  J l l' -> J (l <* gap n) (l' <* gap n).
Proof.
  unfold J; intros H r.
  follow left_gaps.
  follow H.
  apply right_gaps.
Qed.

Lemma left_three l r n :
  l <* e3 {{B}}> 0 >> [0;1]^^n *> workP *> r -->*
  l {{B}}> 0 >> workP *> [0;1]^^n *> workQ *> r.
Proof. unfold e3, workP, workQ; es. Qed.

Lemma scan_right l r n :
  l {{C}}> [0;1]^^n *> r -->*
  l <* [1]^^(n*2) {{C}}> r.
Proof. es. Qed.

Lemma header r :
  const 0 {{B}}> 0 >> workP *> workP *> workP *>
    [0;1]^^2 *> workP *> r -->*
  const 0 <* e4 <* e2 <* e4 <* gap 2 <* e1 <* gap 2 {{C}}> r.
Proof. unfold workP, e1, e2, e4, gap; es. Qed.

Definition work (l r : side) := l <* gap 2 {{C}}> r.

Lemma atom_P0 l r :
  work l (workP *> r) -->* work (l <* e2) r.
Proof. unfold work, workP, e2, gap; es. Qed.

Lemma atom_P1 l r :
  work l ([0;1] *> workP *> r) -->* work (l <* gap 1 <* e3) r.
Proof. unfold work, workP, e3, gap; es. Qed.

Lemma atom_P3 l r n :
  work l ([0;1]^^(3+n*3) *> workP *> r) -->*
  work (l <* e3 <* e2^^n <* e1) r.
Proof. unfold work, workP, e1, e2, e3, gap; es; execute_with_shift_rule'; finish. Qed.

Lemma atom_P4 l r n :
  work l ([0;1]^^(4+n*3) *> workP *> r) -->*
  work (l <* gap 1 <* e4 <* e2^^n <* e1) r.
Proof. unfold work, workP, e1, e2, e4, gap; es; execute_with_shift_rule'; finish. Qed.

Lemma atom_Q1 l r :
  work l ([0;1] *> workQ *> r) -->* work (l <* e4 <* gap 1) r.
Proof. unfold work, workQ, e4, gap; es; execute_with_shift_rule'; finish. Qed.

Lemma atom_Q4 l r n :
  work l ([0;1]^^(4+n*3) *> workQ *> r) -->*
  work (l <* e3 <* e2^^n <* e3 <* gap 1) r.
Proof. unfold work, workQ, e2, e3, gap; es; execute_with_shift_rule'; finish. Qed.

Lemma atom_Q5 l r n :
  work l ([0;1]^^(5+n*3) *> workQ *> r) -->*
  work (l <* gap 1 <* e4 <* e2^^n <* e3 <* gap 1) r.
Proof. unfold work, workQ, e2, e3, e4, gap; es; execute_with_shift_rule'; finish. Qed.

Lemma atom_P2 l l' l'' r n :
  J l l' -> J l' l'' ->
  work l ([0;1]^^(2+n*3) *> workP *> r) -->*
  work (l'' <* gap 2 <* e2^^n <* e1) r.
Proof.
  intros Jl Jl'.
  pose proof (J_enter _ _ Jl) as H1.
  pose proof (J_enter _ _ Jl') as H2.
  unfold work, workP, e1, e2, gap.
  es; er; follow H1.
  es; er; follow H2.
  es; execute_with_shift_rule'; finish.
Qed.

Lemma atom_Q0 l l' l'' l''' r :
  J l l' -> J l' l'' -> J l'' l''' ->
  work l (workQ *> r) -->* work (l''' <* gap 3) r.
Proof.
  intros Jl Jl' Jl''.
  pose proof (J_enter _ _ Jl) as H1.
  pose proof (J_enter _ _ Jl') as H2.
  pose proof (J_enter _ _ Jl'') as H3.
  unfold work, workQ, gap.
  es; er; follow H1.
  es; er; follow H2.
  es; er; follow H3.
  es; er; finish.
Qed.

Lemma atom_Q2 l l' l'' r :
  J l l' -> J l' l'' ->
  work l ([0;1]^^2 *> workQ *> r) -->*
  work (l'' <* gap 1 <* e1 <* gap 1) r.
Proof.
  intros Jl Jl'.
  pose proof (J_enter _ _ Jl) as H1.
  pose proof (J_enter _ _ Jl') as H2.
  unfold work, workQ, e1, gap.
  es; er; follow H1.
  es; er; follow H2.
  es; er; finish.
Qed.

Lemma atom_Q3 l l' l'' r n :
  J l l' -> J l' l'' ->
  work l ([0;1]^^(3+n*3) *> workQ *> r) -->*
  work (l'' <* gap 2 <* e2^^n <* e3 <* gap 1) r.
Proof.
  intros Jl Jl'.
  pose proof (J_enter _ _ Jl) as H1.
  pose proof (J_enter _ _ Jl') as H2.
  unfold work, workQ, e2, e3, gap.
  es; er; follow H1.
  es; er; follow H2.
  es; execute_with_shift_rule'; finish.
Qed.

Lemma tail0 l n :
  work l ([0;1]^^(n*3) *> const 0) -->*
  l <* e1 <* e4^^n {{B}}> const 0.
Proof. unfold work, gap, e1, e4; es; finish. Qed.

Lemma tail1 l n :
  work l ([0;1]^^(1+n*3) *> const 0) -->*
  l <* gap 1 <* e2 <* e4^^n {{B}}> const 0.
Proof. unfold work, gap, e2, e4; es; finish. Qed.

Lemma tail2 l n :
  work l ([0;1]^^(2+n*3) *> const 0) -->*
  l <* gap 2 <* e4^^(1+n) {{B}}> const 0.
Proof. unfold work, gap, e4; es; finish. Qed.

Section Capacity.
Local Open Scope N_scope.

Fixpoint toggle w :=
  match w with
  | [] => []
  | Odd::w => Even::w
  | Even::w => Odd::w
  | Gap::w => Gap::toggle w
  end.

Lemma toggle_twice w : toggle (toggle w) = w.
Proof. induction w as [|[] w IH]; cbn; congruence. Qed.

Lemma toggle_gaps n w : toggle (repeat Gap n ++ w) = repeat Gap n ++ toggle w.
Proof. induction n; cbn; congruence. Qed.

Lemma gaps_cons n w : repeat Gap n ++ Gap::w = Gap::(repeat Gap n ++ w).
Proof. induction n; cbn; congruence. Qed.

(* The parity word, like the physical left side, is stored low digit first. *)
Inductive counter : list letter -> N -> side -> Prop :=
| counter0 : counter [] 0 (const S0)
| counter1 w s l : counter w s l -> counter (Odd::w) (4*(s/2)+3) (l <* e1)
| counter2 w s l : counter w s l -> counter (Even::w) (4*(s/2)+2) (l <* e2)
| counter3 w s l : counter w s l -> counter (Odd::w) (4*(s/2)+1) (l <* e3)
| counter4 w s l : counter w s l -> counter (Even::w) (4*(s/2)) (l <* e4)
| counter_gap w s l n : counter w s l -> counter (repeat Gap n ++ w) s (l <* gap n).

Lemma counter_J_bound m :
  forall w s l, counter w s l -> s < m -> 0 < s ->
  exists l', counter (toggle w) (s-1) l' /\ J l l'.
Proof.
  induction m using N.peano_ind.
  - intros; lia.
  - intros w s l HC.
    induction HC as [|w s l HC IH|w s l HC IH|w s l HC IH|
                     w s l HC IH|w s l n HC IH]; intros Hb Hp; cbn [toggle].
    + lia.
    + exists (l <* e2); split.
      * replace (4*(s/2)+3-1) with (4*(s/2)+2) by lia.
        apply counter2, HC.
      * apply J1.
    + exists (l <* e3); split.
      * replace (4*(s/2)+2-1) with (4*(s/2)+1) by lia.
        apply counter3, HC.
      * apply J2.
    + exists (l <* e4); split.
      * replace (4*(s/2)+1-1) with (4*(s/2)) by lia.
        apply counter4, HC.
      * apply J3.
    + assert (Hs: 2 <= s) by lia.
      assert (Hsm: s < m) by lia.
      destruct (IHm w s l HC Hsm ltac:(lia)) as [l' [HC' HJ]].
      destruct (IHm (toggle w) (s-1) l' HC' ltac:(lia) ltac:(lia)) as [l'' [HC'' HJ']].
      rewrite toggle_twice in HC''.
      exists (l'' <* e1); split.
      * replace (4*(s/2)-1) with (4*((s-1-1)/2)+3) by lia.
        apply counter1, HC''.
      * eapply J4; eauto.
    + destruct (IH Hb Hp) as [l' [HC' HJ]].
      exists (l' <* gap n); split.
      * rewrite toggle_gaps; apply counter_gap, HC'.
      * apply J_gaps, HJ.
Qed.

Lemma counter_J w s l :
  counter w s l -> 0 < s -> exists l', counter (toggle w) (s-1) l' /\ J l l'.
Proof.
  intros HC Hs.
  eapply (counter_J_bound (N.succ s)); eauto; lia.
Qed.

Definition config (l : side) := l {{B}}> const S0.

Lemma normal_step w s l :
  counter w (N.succ s) l ->
  exists l', counter (Gap::toggle w) s l' /\ config l -->+ config l'.
Proof.
  intro HC.
  destruct (counter_J w (N.succ s) l HC ltac:(lia)) as [l' [HC' HJ]].
  exists (l' <* gap 1); split.
  - replace s with (N.succ s-1) at 1 by lia.
    apply (counter_gap _ _ _ 1), HC'.
  - unfold config.
    eapply progress_evstep_trans.
    + apply evstep_progress.
      * apply HJ.
      * discriminate.
    + unfold gap; es.
Qed.

Lemma batch_word_succ s w :
  repeat Gap (N.to_nat s) ++ (if N.odd s then toggle (Gap::toggle w) else Gap::toggle w) =
  repeat Gap (N.to_nat (N.succ s)) ++ (if N.odd (N.succ s) then toggle w else w).
Proof.
  rewrite N2Nat.inj_succ, N.odd_succ, <-N.negb_odd.
  destruct (N.odd s); cbn [repeat negb toggle];
    try rewrite toggle_twice; rewrite gaps_cons; reflexivity.
Qed.

Lemma counter_batch s :
  forall w l, counter w s l ->
  exists l',
    counter (repeat Gap (N.to_nat s) ++ if N.odd s then toggle w else w) 0 l' /\
    config l -->* config l'.
Proof.
  induction s using N.peano_ind; intros w l HC.
  - exists l; split; [exact HC|finish].
  - destruct (normal_step w s l HC) as [l1 [HC1 Hstep]].
    destruct (IHs _ _ HC1) as [l2 [HC2 Hsteps]].
    exists l2; split.
    + rewrite batch_word_succ in HC2; exact HC2.
    + eapply evstep_trans.
      * apply progress_evstep, Hstep.
      * exact Hsteps.
Qed.

Lemma counter_batch_positive s :
  forall w l, counter w s l -> 0<s ->
  exists l',
    counter (repeat Gap (N.to_nat s) ++ if N.odd s then toggle w else w) 0 l' /\
    config l -->+ config l'.
Proof.
  induction s using N.peano_ind; intros w l HC Hs; [lia|].
  destruct (normal_step w s l HC) as [l1 [HC1 Hstep]].
  destruct (counter_batch s _ _ HC1) as [l2 [HC2 Hsteps]].
  exists l2; split.
  - rewrite batch_word_succ in HC2; exact HC2.
  - eapply progress_evstep_trans; eauto.
Qed.

Fixpoint low_odd w :=
  match w with [] => false | Odd::_ => true | Even::_ => false | Gap::w => low_odd w end.

Lemma low_odd_gaps n w : low_odd (repeat Gap n ++ w) = low_odd w.
Proof. induction n; cbn; congruence. Qed.

Lemma counter_odd w s l : counter w s l -> N.odd s = low_odd w.
Proof.
  intro HC; induction HC; cbn [low_odd].
  - reflexivity.
  - rewrite N.odd_add, N.odd_mul; reflexivity.
  - rewrite N.odd_add, N.odd_mul; reflexivity.
  - rewrite N.odd_add, N.odd_mul; reflexivity.
  - rewrite N.odd_mul; reflexivity.
  - rewrite low_odd_gaps; exact IHHC.
Qed.

Lemma counter_e2s w s l n : counter w s l ->
  exists t, counter (repeat Even n ++ w) t (l <* e2^^n) /\
    t/2+1 = 2^(N.of_nat n)*(s/2+1).
Proof.
  intro HC; induction n.
  - exists s; split; [exact HC|].
    change (s/2+1 = 1*(s/2+1)); rewrite N.mul_1_l; reflexivity.
  - destruct IHn as [t [Ht He]].
    exists (4*(t/2)+2); split.
    + cbn [repeat lpow]; rewrite Str_app_assoc.
      apply counter2, Ht.
    + rewrite Nat2N.inj_succ, N.pow_succ_r'.
      nia.
Qed.

Lemma counter_J2 w s l : counter w s l -> 2 <= s ->
  exists l1 l2, counter w (s-2) l2 /\ J l l1 /\ J l1 l2.
Proof.
  intros HC Hs.
  destruct (counter_J _ _ _ HC ltac:(lia)) as [l1 [H1 J1]].
  destruct (counter_J _ _ _ H1 ltac:(lia)) as [l2 [H2 J2]].
  rewrite toggle_twice in H2.
  replace (s-1-1) with (s-2) in H2 by lia.
  exists l1,l2; auto.
Qed.

Lemma counter_J3 w s l : counter w s l -> 3 <= s ->
  exists l1 l2 l3, counter (toggle w) (s-3) l3 /\ J l l1 /\ J l1 l2 /\ J l2 l3.
Proof.
  intros HC Hs.
  destruct (counter_J2 _ _ _ HC ltac:(lia)) as [l1 [l2 [H2 [J1 J2]]]].
  destruct (counter_J _ _ _ H2 ltac:(lia)) as [l3 [H3 J3]].
  replace (s-2-1) with (s-3) in H3 by lia.
  exists l1,l2,l3; auto.
Qed.

Lemma counter_e4s w s l n : counter w s l -> 4<=s ->
  exists t, counter (repeat Even n ++ w) t (l <* e4^^n) /\ s<=t.
Proof.
  intros HC Hs; induction n.
  - exists s; split; [exact HC|lia].
  - destruct IHn as [t [Ht Hle]].
    exists (4*(t/2)); split.
    + cbn [repeat lpow]; rewrite Str_app_assoc; apply counter4,Ht.
    + lia.
Qed.

End Capacity.

Definition update b w :=
  match b with BQ0 => [Gap;Gap;Gap] ++ toggle w | _ => rev (output b false) ++ w end.
Fixpoint updates xs w :=
  match xs with [] => w | b::xs => updates xs (update b w) end.

Lemma toggle_output b f w : b <> BQ0 ->
  toggle (rev (output b f) ++ w) = rev (output b (negb f)) ++ w.
Proof.
  destruct b; destruct f; intro H; try contradiction;
    unfold output, front, last_digit, back, even_block;
    repeat rewrite rev_app_distr; cbn [guess negb rev app toggle]; reflexivity.
Qed.

Lemma updates_outputs xs w :
  updates xs w = rev (outputs xs) ++ if needs_flip xs then toggle w else w.
Proof.
  gen w; induction xs as [|b xs IH]; intro w; [reflexivity|].
  destruct b; cbn [updates update outputs needs_flip]; rewrite IH;
    destruct (needs_flip xs); cbn [negb];
    try (rewrite toggle_output by discriminate);
    repeat rewrite rev_app_distr;
    cbn [toggle rev app negb]; try rewrite toggle_twice;
    repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma updated_seed xs prefix :
  updates xs (Odd::prefix) = rev (rewritten xs) ++ prefix.
Proof.
  rewrite updates_outputs; unfold rewritten; cbn [rev].
  destruct (needs_flip xs); cbn [toggle guess];
    repeat rewrite <-app_assoc; reflexivity.
Qed.

Definition work_operator b := if even_block b then workP else workQ.
Fixpoint work_blocks xs r :=
  match xs with [] => r | b::xs => [0;1]^^(gaps b) *> work_operator b *> work_blocks xs r end.

Ltac word_shape :=
  unfold update, output, front, last_digit, back, even_block;
  repeat rewrite rev_app_distr;
  repeat rewrite rev_repeat;
  cbn [guess rev app repeat]; repeat rewrite rev_repeat; repeat rewrite <-app_assoc.

Lemma block_step b w s l s' :
  counter w s l -> atom (even_block b) (gaps b) s = Some s' ->
  exists l', counter (update b w) s' l' /\
    forall r, work l ([0;1]^^(gaps b) *> work_operator b *> r) -->* work l' r.
Proof.
  intros HC HS; destruct b; unfold even_block, gaps in HS;
    unfold atom in HS;
    repeat rewrite Nat.div_add in HS by lia;
    repeat rewrite Nat.Div0.mod_add in HS;
    cbn [Nat.add Nat.sub Nat.eqb Nat.div Nat.modulo Nat.divmod fst snd] in HS;
    repeat rewrite Nat2N.inj_succ in HS;
    repeat rewrite N.add_1_r in HS;
    repeat rewrite N.pow_succ_r' in HS.
  all: repeat match goal with
       | H: context[if (?a <=? ?b)%N then _ else _] |- _ =>
           destruct (a <=? b)%N eqn:HG;
             [apply N.leb_le in HG | apply N.leb_gt in HG; discriminate]
       end.
  all: apply (f_equal (fun o : option N => match o with Some x => x | None => 0%N end)) in HS;
    cbv beta iota zeta in HS.
  - exists (l <* e2); split.
    + word_shape; replace s' with (4*(s/2)+2)%N by nia; apply counter2,HC.
    + intros; apply atom_P0.
  - exists (l <* gap 1 <* e3); split.
    + word_shape; replace s' with (4*(s/2)+1)%N by nia.
      apply counter3, (counter_gap _ _ _ 1), HC.
    + intros; apply atom_P1.
  - destruct (counter_J2 _ _ _ HC HG) as [l1 [l2 [H2 [J1 J2]]]].
    pose proof (counter_gap _ _ _ 2 H2) as Hgap.
    destruct (counter_e2s _ _ _ n Hgap) as [t [Ht He]].
    replace ((s-2)/2+1)%N with (s/2)%N in He by lia.
    exists (l2 <* gap 2 <* e2^^n <* e1); split.
    + word_shape; replace s' with (4*(t/2)+3)%N by nia; apply counter1,Ht.
    + intros; apply atom_P2 with (l':=l1); assumption.
  - pose proof (counter3 _ _ _ HC) as H3.
    destruct (counter_e2s _ _ _ n H3) as [t [Ht He]].
    replace ((4*(s/2)+1)/2+1)%N with (2*(s/2)+1)%N in He by lia.
    exists (l <* e3 <* e2^^n <* e1); split.
    + word_shape; replace s' with (4*(t/2)+3)%N by nia; apply counter1,Ht.
    + intros; apply atom_P3.
  - pose proof (counter4 _ _ _ (counter_gap _ _ _ 1 HC)) as H4.
    destruct (counter_e2s _ _ _ n H4) as [t [Ht He]].
    replace ((4*(s/2))/2+1)%N with (2*(s/2)+1)%N in He by lia.
    exists (l <* gap 1 <* e4 <* e2^^n <* e1); split.
    + word_shape; replace s' with (4*(t/2)+3)%N by nia; apply counter1,Ht.
    + intros; apply atom_P4.
  - destruct (counter_J3 _ _ _ HC HG) as [l1 [l2 [l3 [H3 [J1 [J2 J3]]]]]].
    exists (l3 <* gap 3); split.
    + change (counter (repeat Gap 3 ++ toggle w) s' (l3 <* gap 3)).
      replace s' with (s-3)%N by congruence; apply counter_gap,H3.
    + intros; eapply atom_Q0; eauto.
  - exists (l <* e4 <* gap 1); split.
    + word_shape; replace s' with (4*(s/2))%N by nia.
      apply (counter_gap _ _ _ 1),counter4,HC.
    + intros; apply atom_Q1.
  - destruct (counter_J2 _ _ _ HC HG) as [l1 [l2 [H2 [J1 J2]]]].
    exists (l2 <* gap 1 <* e1 <* gap 1); split.
    + word_shape; replace s' with (4*((s-2)/2)+3)%N by nia.
      apply (counter_gap _ _ _ 1),counter1,(counter_gap _ _ _ 1),H2.
    + intros; apply atom_Q2 with (l':=l1); assumption.
  - destruct (counter_J2 _ _ _ HC HG) as [l1 [l2 [H2 [J1 J2]]]].
    pose proof (counter_gap _ _ _ 2 H2) as Hgap.
    destruct (counter_e2s _ _ _ n Hgap) as [t [Ht He]].
    replace ((s-2)/2+1)%N with (s/2)%N in He by lia.
    exists (l2 <* gap 2 <* e2^^n <* e3 <* gap 1); split.
    + word_shape; replace s' with (4*(t/2)+1)%N by nia.
      apply (counter_gap _ _ _ 1),counter3,Ht.
    + intros; apply atom_Q3 with (l':=l1); assumption.
  - pose proof (counter3 _ _ _ HC) as H3.
    destruct (counter_e2s _ _ _ n H3) as [t [Ht He]].
    replace ((4*(s/2)+1)/2+1)%N with (2*(s/2)+1)%N in He by lia.
    exists (l <* e3 <* e2^^n <* e3 <* gap 1); split.
    + word_shape; replace s' with (4*(t/2)+1)%N by nia.
      apply (counter_gap _ _ _ 1),counter3,Ht.
    + intros; apply atom_Q4.
  - pose proof (counter4 _ _ _ (counter_gap _ _ _ 1 HC)) as H4.
    destruct (counter_e2s _ _ _ n H4) as [t [Ht He]].
    replace ((4*(s/2))/2+1)%N with (2*(s/2)+1)%N in He by lia.
    exists (l <* gap 1 <* e4 <* e2^^n <* e3 <* gap 1); split.
    + word_shape; replace s' with (4*(t/2)+1)%N by nia.
      apply (counter_gap _ _ _ 1),counter3,Ht.
    + intros; apply atom_Q5.
Qed.

Lemma blocks_steps s xs s' : blocks_run s xs s' ->
  forall w l, counter w s l -> exists l', counter (updates xs w) s' l' /\
    forall r, work l (work_blocks xs r) -->* work l' r.
Proof.
  intro HR; induction HR; intros w l HC.
  - exists l; split; [exact HC|intro; finish].
  - destruct (block_step _ _ _ _ _ HC H) as [l1 [HC1 Hstep]].
    destruct (IHHR _ _ HC1) as [l2 [HC2 Hsteps]].
    exists l2; split; [exact HC2|intro r].
    unfold work_blocks; fold work_blocks.
    follow Hstep; apply Hsteps.
Qed.

Lemma finish_tail w s l q j :
  counter w s l -> (28<=s)%N -> (j<3)%nat ->
  exists l' t,
    counter (rev (tail_word j ++ repeat Even (tail_count j q)) ++ w) t l' /\
    (28<=t)%N /\
    work l ([0;1]^^(j+q*3) *> const 0) -->* config l'.
Proof.
  intros HC Hs Hj.
  destruct j as [|[|[|j]]]; try lia.
  - pose proof (counter1 _ _ _ HC) as H1.
    destruct (counter_e4s _ _ _ q H1 ltac:(lia)) as [t [Ht Hle]].
    exists (l <* e1 <* e4^^q),t; split.
    + unfold tail_word,tail_count.
      rewrite Nat.add_0_r,rev_app_distr,rev_repeat; cbn [rev app].
      repeat rewrite <-app_assoc; exact Ht.
    + split; [lia|apply tail0].
  - pose proof (counter2 _ _ _ (counter_gap _ _ _ 1%nat HC)) as H2.
    destruct (counter_e4s _ _ _ q H2 ltac:(lia)) as [t [Ht Hle]].
    exists (l <* gap 1 <* e2 <* e4^^q),t; split.
    + unfold tail_word,tail_count.
      rewrite rev_app_distr,rev_repeat,repeat_app; cbn [rev app repeat].
      repeat rewrite <-app_assoc; exact Ht.
    + split; [lia|apply tail1].
  - pose proof (counter_gap _ _ _ 2%nat HC) as Hgap.
    destruct (counter_e4s _ _ _ (1+q)%nat Hgap ltac:(lia)) as [t [Ht Hle]].
    exists (l <* gap 2 <* e4^^(1+q)),t; split.
    + unfold tail_word,tail_count.
      rewrite rev_app_distr,rev_repeat; cbn [rev app].
      replace (q+1)%nat with (1+q)%nat by lia.
      repeat rewrite <-app_assoc; exact Ht.
    + split; [lia|apply tail2].
Qed.

Fixpoint scan_word (w : list letter) (g : nat) (r : side) : side :=
  match w with
  | [] => [0;1]^^g *> workP *> r
  | Gap::w => scan_word w (S g) r
  | Odd::w => scan_word w 0 ([0;1]^^g *> workQ *> r)
  | Even::w => scan_word w 0 ([0;1]^^g *> workP *> r)
  end.

Lemma scan_word_gaps n w g r :
  scan_word (repeat Gap n ++ w) g r = scan_word w (n+g) r.
Proof.
  gen g r; induction n; intros; cbn; auto.
  rewrite IHn; f_equal; lia.
Qed.

Lemma scan_saturated w s l :
  counter w s l -> (s <= 1)%N -> forall g r,
  l {{B}}> 0 >> [0;1]^^g *> workP *> r -->*
  const 0 {{B}}> 0 >> scan_word w g r.
Proof.
  intro HC; induction HC; intros Hs g r; cbn [scan_word].
  - finish.
  - lia.
  - lia.
  - follow left_three.
    apply (IHHC ltac:(lia) 0%nat).
  - follow left_four.
    apply (IHHC ltac:(lia) 0%nat).
  - follow left_gaps.
    rewrite scan_word_gaps.
    rewrite <-Str_app_assoc, <-lpow_add.
    apply IHHC, Hs.
Qed.

Fixpoint overflow_word (w : list letter) (r : side) : side :=
  match w with
  | [] => r
  | Gap::w => overflow_word w ([0;1] *> r)
  | Even::w => scan_word w 0 r
  | Odd::_ => r (* excluded by the zero-capacity premise of scan_zero *)
  end.

Lemma overflow_word_gaps n w r :
  overflow_word (repeat Gap n ++ w) r = overflow_word w ([0;1]^^n *> r).
Proof.
  gen r; induction n; intros; cbn; auto.
  rewrite IHn; f_equal.
  apply lpow_shift2.
Qed.

Lemma scan_zero w s l :
  counter w s l -> s=0%N -> forall r,
  l {{B}}> 0 >> r -->* const 0 {{B}}> 0 >> overflow_word w r.
Proof.
  intro HC; induction HC; intros Hs r; cbn [overflow_word].
  - finish.
  - lia.
  - lia.
  - lia.
  - follow left_four.
    apply (scan_saturated _ _ _ HC ltac:(lia) 0%nat).
  - follow left_gaps.
    rewrite overflow_word_gaps.
    apply IHHC, Hs.
Qed.

Definition high_prefix := [Gap;Gap;Even;Even;Even].
Definition header_register := const 0 <* e4 <* e2 <* e4 <* gap 2 <* e1.

Lemma header_counter : counter (Odd::high_prefix) 11 header_register.
Proof.
  exact (counter1 _ _ _ (counter_gap _ _ _ 2%nat
    (counter4 _ _ _ (counter2 _ _ _ (counter4 _ _ _ counter0))))).
Qed.

Lemma scan_block b w r :
  scan_word (rev (input b) ++ w) 0 r =
  scan_word w 0 ([0;1]^^(gaps b) *> work_operator b *> r).
Proof.
  unfold input; cbn [rev].
  rewrite rev_repeat, <-app_assoc, scan_word_gaps, Nat.add_0_r.
  unfold symbol, work_operator; destruct (even_block b); reflexivity.
Qed.

Lemma scan_blocks xs w r :
  scan_word (rev (inputs xs) ++ w) 0 r = scan_word w 0 (work_blocks xs r).
Proof.
  gen w r; induction xs as [|b xs IH]; intros w r; [reflexivity|].
  change (scan_word (rev (input b ++ inputs xs) ++ w) 0 r =
    scan_word w 0 ([0;1]^^(gaps b) *> work_operator b *> work_blocks xs r)).
  rewrite rev_app_distr, <-app_assoc, IH, scan_block; reflexivity.
Qed.

Lemma overflow_start xs n l :
  counter (repeat Gap n ++ Even::(rev (inputs xs) ++ high_prefix)) 0 l ->
  config l -->* work header_register (work_blocks xs ([0;1]^^n *> const 0)).
Proof.
  intro HC; unfold config.
  follow (scan_zero _ _ _ HC eq_refl).
  rewrite overflow_word_gaps; cbn [overflow_word].
  rewrite scan_blocks.
  unfold high_prefix; cbn [scan_word].
  unfold work, header_register.
  apply header.
Qed.

Lemma cycle xs s l :
  counter (Even::(rev (inputs xs) ++ high_prefix)) s l -> (12<=s)%N ->
  language body_graph starts (inputs xs ++ [Even]) ->
  exists xs' s' l',
    counter (Even::(rev (inputs xs') ++ high_prefix)) s' l' /\ (12<=s')%N /\
    language body_graph starts (inputs xs' ++ [Even]) /\ config l -->+ config l'.
Proof.
  intros HC Hs HL.
  pose proof (counter_odd _ _ _ HC) as Hodd; cbn [low_odd] in Hodd.
  destruct (counter_batch_positive _ _ _ HC ltac:(lia)) as [l0 [HC0 Hbatch]].
  rewrite Hodd in HC0.
  pose proof (overflow_start xs (N.to_nat s) l0 HC0) as Hstart.
  destruct (blocks_admissible xs HL) as [t [Hblocks Ht]].
  destruct (blocks_steps _ _ _ Hblocks _ _ header_counter) as [l1 [HC1 Hsteps]].
  rewrite updated_seed in HC1.
  set (q := N.to_nat (s/3)%N).
  set (j := N.to_nat (s mod 3)%N).
  pose proof (N.div_mod s 3 ltac:(lia)) as Hdiv.
  pose proof (N.mod_lt s 3 ltac:(lia)) as Hmod.
  assert (Hj: (j<3)%nat) by (unfold j; lia).
  assert (Hq: (4<=q)%nat) by (unfold q; lia).
  assert (HS: N.to_nat s = (j+q*3)%nat) by (unfold j,q; lia).
  destruct (finish_tail _ _ _ q j HC1 Ht Hj) as [l2 [s2 [HC2 [Hs2 Htail]]]].
  assert (Hcount: (4<=tail_count j q)%nat) by (unfold tail_count; destruct j; lia).
  destruct (digit_blocks (guess (needs_flip xs) Odd)
    (outputs xs ++ tail_word j ++ repeat Even (tail_count j q-1))
    ltac:(destruct (needs_flip xs); discriminate)) as [xs' Hxs'].
  assert (Hword: inputs xs' ++ [Even] = rewritten xs ++ tail_word j ++ repeat Even (tail_count j q)).
  {
    rewrite Hxs'; unfold rewritten; cbn [app].
    repeat rewrite <-app_assoc; rewrite repeat_snoc.
    replace (S (tail_count j q-1)) with (tail_count j q) by lia; reflexivity.
  }
  pose proof (macro_closed xs j (tail_count j q-4) Hj HL) as HL'.
  replace (4+(tail_count j q-4))%nat with (tail_count j q) in HL' by lia.
  rewrite <-Hword in HL'.
  assert (HC': counter (Even::(rev (inputs xs') ++ high_prefix)) s2 l2).
  {
    replace (Even::(rev (inputs xs') ++ high_prefix)) with
      (rev (inputs xs' ++ [Even]) ++ high_prefix) by (rewrite rev_app_distr; reflexivity).
    rewrite Hword.
    repeat rewrite rev_app_distr in *.
    repeat rewrite <-app_assoc in *.
    exact HC2.
  }
  exists xs',s2,l2; split; [exact HC'|].
  split; [lia|split; [exact HL'|]].
  eapply progress_evstep_trans; [exact Hbatch|].
  follow Hstart.
  follow Hsteps.
  rewrite HS; exact Htail.
Qed.

Definition seed_left :=
  const 0 <* e4^^2 <* e2 <* gap 2 <* e2 <* gap 4 <*
    e2^^3 <* e1 <* e4^^32.
Definition seed := config seed_left.

Lemma seed_counter :
  counter (rev initial_word ++ high_prefix) 541165879296%N seed_left.
Proof.
  pose proof counter0 as HC.
  do 2 (apply counter4 in HC).
  apply counter2 in HC.
  apply (counter_gap _ _ _ 2%nat) in HC.
  apply counter2 in HC.
  apply (counter_gap _ _ _ 4%nat) in HC.
  do 3 (apply counter2 in HC).
  apply counter1 in HC.
  do 32 (apply counter4 in HC).
  exact HC.
Qed.

Lemma init : c0 -->* seed.
Proof.
  unfold seed, config, seed_left, e1, e2, e4, gap.
  solve_init.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact init|].
  change (~halts tm (config seed_left)).
  eapply (progress_nonhalt_cond tm (list block*N*side)%type
    (initial_blocks,541165879296%N,seed_left)
    (fun i => config (snd i))
    (fun '(xs,s,l) =>
      counter (Even::(rev (inputs xs) ++ high_prefix)) s l /\ (12<=s)%N /\
      language body_graph starts (inputs xs ++ [Even]))).
  - intros [[xs s] l] [HC [Hs HL]].
    destruct (cycle xs s l HC Hs HL) as [xs' [s' [l' [HC' [Hs' [HL' HR]]]]]].
    exists (xs',s',l'); split; [exact HR|split; [exact HC'|split; assumption]].
  - split.
    + pose proof seed_counter as HC; unfold initial_word in HC.
      rewrite rev_app_distr in HC; cbn [rev app] in HC; exact HC.
    + split; [lia|exact initial_member].
Qed.

End TM1.

