From BusyCoq Require Import Individual62.

Require Import ZArith NArith ZifyNat Lia.
Require Import String List.
From BusyCoq Require Import Longitudinal LongitudinalHalt.

Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC1RC_1LD1RE_1RA0LC_0RB0RF_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Notation hR := (B,<[0]).
Notation hL := (D,[1;0;1;0]).
Notation hR' := (A,<[0;1;1]).
Notation hR'' := (B,<[0;1;1;1;1;1]).
Notation h := [(hR,hL)].
Notation h' := [(hR',hL);(hR,hL)].
Notation h'' := [(hR'',hL)].
Notation w := [1;1;0].
Notation d := [1;1;1;1;1;0].
Notation w10 := [1;1;1;1;1;1;1;1;1;1;0].

Notation RC0 := (flat_map (fun a => d++w^^a)).

Fixpoint RIncs0 k ls :=
  match ls with
  | [] => []
  | a::ls => k+a::RIncs0 (k*2) ls
  end.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6);
   [vm_compute; reflexivity | st; reflexivity]).

Lemma RIncs0_spec k ls:
  segRLs tm (h^^k) (h^^(k*2^(length ls)))
    (RC0 ls) (RC0 (RIncs0 k ls)).
Proof.
  gen k.
  induction ls; cbn[flat_map RIncs0 length]; intros.
  - rewrite Nat.mul_1_r. eapply segRLs_wall''; esc.
  - eapply segRLs_concat.
    2: applys_eq (IHls (k*2)); cbn; flia.
    clear.
    induction k.
    1: esx.
    replace (S k) with (k+1) by lia.
    replace ((k+1)*2) with (k*2+2) by lia.
    eapply segRLs_trans_add.
    1: apply IHk.
    esx.
Qed.

Notation lh := (0inf<*<[1;1;1;0;1;1]).

Lemma LRst:
  sideRLs (flip tm) [(hL,hR'')] lh lh.
Proof. esc. Qed.

Lemma dollar_w10:
  segRLs tm h'' (h'++h^^2) w10 (w10 ++ RC0 [2]).
Proof. esc. Qed.

Lemma hash_wall:
  sideRLs tm h 0inf 0inf.
Proof. esc. Qed.

Lemma hash_w_wall:
  sideRLs tm h (w*>0inf) (w*>0inf).
Proof. esc. Qed.

Lemma hash_ww_wall:
  sideRLs tm h (w*>w*>0inf) (w*>w*>0inf).
Proof. esc. Qed.

Lemma at_hash_edge:
  sideRLs tm h' (w*>0inf) (RC0 [O] *> w*>0inf).
Proof. esc. Qed.

Lemma hash_blank:
  sideRLs tm h 0inf 0inf.
Proof. exact hash_wall. Qed.

Lemma at_blank:
  sideRL tm hR' hL 0inf ([1;1;1;0] *> 0inf).
Proof. unfold sideRL. eapply sideRLs_1. esc. Qed.

Lemma hash_1110_halts:
  forall l, halts tm (l {{{ (hR,R) }}} ([1;1;1;0] *> 0inf)).
Proof. intros; esx. Qed.

Lemma ws_Ov n:
  segRLs tm h' (h^^n++h') (w^^(n*2)) (RC0 ([1%nat]^^n)).
Proof.
  induction n.
  - esx.
  - replace (S n*2) with (n*2+2) by lia.
    replace (S n) with (n+1) by lia.
    repeat rewrite lpow_add.
    rewrite flat_map_app.
    eapply segRLs_concat.
    1: apply IHn.
    rewrite <-app_assoc.
    eapply segRLs_trans.
    1: eapply segRLs_wall''; esx.
    esc.
Qed.

Definition H a b := h^^a++h'++h^^b.

Lemma ws_OvIncs a b n:
  segRLs tm (H a b) (H (a+n) (b*2^n))
    (w^^(n*2)) (RC0 (RIncs0 b ([1%nat]^^n))).
Proof.
  unfold H.
  rewrite lpow_add,<-app_assoc.
  eapply segRLs_trans.
  1: eapply segRLs_wall''; esx.
  rewrite app_assoc.
  eapply segRLs_trans.
  1: apply ws_Ov.
  applys_eq RIncs0_spec.
  rewrite lpow_length; cbn; flia.
Qed.

Lemma dw_Ov n:
  segRLs tm h' (H (1+n) (2*2^n))
    (RC0 [n*2+1])
    (RC0 ([O;2]++RIncs0 2 ([1%nat]^^n))).
Proof.
  unfold H.
  replace (RC0 [n*2+1]) with ((d++w)++w^^(n*2)).
  2:{ unfold RC0. rewrite Nat.add_comm,app_nil_r. trivial. }
  rewrite flat_map_app.
  eapply @segRLs_concat with (ls2:=h++h'++h^^2).
  1: esc.
  apply (ws_OvIncs 1 2).
Qed.

Lemma wdw_Ov n:
  segRLs tm h' (H (3+n) (4*2^n))
    (w++RC0 [n*2+1])
    (RC0 ([O;2;3]++RIncs0 4 ([1%nat]^^n))).
Proof.
  unfold H.
  replace (w++RC0 [n*2+1]) with ((w++d++w)++w^^(n*2)).
  2:{ unfold RC0. rewrite Nat.add_comm,app_nil_r. trivial. }
  rewrite flat_map_app.
  eapply @segRLs_concat with (ls2:=h^^3++h'++h^^4).
  1: esc.
  apply (ws_OvIncs 3 4).
Qed.

Lemma init:
  c0 -->* lh {{{ (hL,L) }}} w10 *> RC0 [2;2] *> w*>0inf.
Proof. esx. Qed.

Lemma hash_blank_1:
  sideRL tm hR hL 0inf 0inf.
Proof. unfold sideRL. eapply sideRLs_1. exact hash_blank. Qed.

Lemma at_hash_blank_halt:
  sideRLs_halt tm (h++h') 0inf.
Proof.
  cbn.
  econstructor 2.
  1: exact hash_blank_1.
  econstructor 2.
  1: exact at_blank.
  constructor 1.
  exact hash_1110_halts.
Qed.

Lemma at_hash_ww_halt:
  sideRLs_halt tm h' (w*>w*>0inf).
Proof.
  change (sideRLs_halt tm h' ((w^^2) *> 0inf)).
  eapply segRLs_sideRLs_halt_concat.
  1: apply (ws_Ov 1).
  cbn[lpow]. exact at_hash_blank_halt.
Qed.

Lemma H_ww_halt a b:
  sideRLs_halt tm (H a b) (w*>w*>0inf).
Proof.
  unfold H.
  change (sideRLs_halt tm (h^^a ++ (h'++h^^b)) (w*>w*>0inf)).
  eapply sideRLs_halt_app_right with
    (hs1:=h^^a) (hs2:=h'++h^^b) (r':=w*>w*>0inf).
  1: eapply sideRLs_wall; exact hash_ww_wall.
  eapply sideRLs_halt_app_left.
  exact at_hash_ww_halt.
Qed.

Lemma H_w_return a b:
  sideRLs tm (H a b) (w*>0inf) (RC0 [b] *> w*>0inf).
Proof.
  unfold H.
  change (sideRLs tm (h^^a ++ (h'++h^^b))
    (w*>0inf) (RC0 [b] *> w*>0inf)).
  eapply (@sideRLs_trans tm (h^^a) (h'++h^^b)
    (w*>0inf) (w*>0inf) (RC0 [b] *> w*>0inf)).
  1: eapply sideRLs_wall; exact hash_w_wall.
  eapply (@sideRLs_trans tm h' (h^^b)
    (w*>0inf) (RC0 [O] *> w*>0inf) (RC0 [b] *> w*>0inf)).
  1: exact at_hash_edge.
  assert (RIncs0 b [O] = [b]) as E by
    (cbn[RIncs0]; rewrite Nat.add_0_r; reflexivity).
  rewrite <-E.
  eapply segRLs_sideRLs_concat.
  1: apply RIncs0_spec.
  eapply sideRLs_wall. exact hash_w_wall.
Qed.

Definition base0 n := [O;2] ++ RIncs0 2 ([1%nat]^^n).
Definition base1 n := [O;2;3] ++ RIncs0 4 ([1%nat]^^n).
Definition out0 b n := RIncs0 b (base0 n).
Definition out1 b n := RIncs0 b (base1 n).

Lemma RIncs0_length k ls:
  length (RIncs0 k ls) = length ls.
Proof.
  gen k. induction ls; intros; cbn[RIncs0].
  - reflexivity.
  - change (S (List.length (RIncs0 (k*2) ls)) = S (List.length ls)).
    f_equal. apply IHls.
Qed.

Lemma base0_length n: length (base0 n) = n+2.
Proof.
  unfold base0.
  rewrite length_app,RIncs0_length,lpow_length.
  cbn. lia.
Qed.

Lemma base1_length n: length (base1 n) = n+3.
Proof.
  unfold base1.
  rewrite length_app,RIncs0_length,lpow_length.
  cbn. lia.
Qed.

Lemma H_prefix_suffix p a b c:
  (h^^p ++ H a b) ++ h^^c = H (p+a) (b+c).
Proof.
  unfold H.
  rewrite !lpow_add.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma col0_raw a b x n:
  x+a=n*2+1 ->
  segRLs tm ((h^^a++h')++h^^b)
    ((h^^(a*2) ++ H (1+n) (2*2^n)) ++
      h^^(b*2^(length (base0 n))))
    (RC0 [x]) (RC0 (out0 b n)).
Proof.
  intros E.
  unfold out0.
  eapply (@segRLs_trans tm
    (h^^a++h') (h^^(a*2)++H (1+n) (2*2^n))
    (h^^b) (h^^(b*2^(length (base0 n))))
    (RC0 [x]) (RC0 (base0 n)) (RC0 (RIncs0 b (base0 n)))).
  - eapply (@segRLs_trans tm
      (h^^a) (h^^(a*2)) h' (H (1+n) (2*2^n))
      (RC0 [x]) (RC0 [x+a]) (RC0 (base0 n))).
    + applys_eq (RIncs0_spec a [x]).
      * f_equal. cbn[RIncs0]. f_equal. lia.
    + unfold base0. applys_eq (dw_Ov n).
      cbn[RIncs0]. f_equal. f_equal. lia.
  - apply RIncs0_spec.
Qed.

Lemma col0 a b x n:
  x+a=n*2+1 ->
  segRLs tm (H a b)
    (H (a*2+(1+n)) (2*2^n+b*2^(n+2)))
    (RC0 [x]) (RC0 (out0 b n)).
Proof.
  intros E.
  epose proof (col0_raw a b x n E) as X.
  rewrite H_prefix_suffix in X.
  applys_eq X.
  - unfold H. rewrite <-app_assoc. reflexivity.
  - f_equal. rewrite base0_length. lia.
Qed.

Lemma hashes_w k:
  segRLs tm (h^^k) (h^^k) w w.
Proof. eapply segRLs_wall''; esx. Qed.

Lemma hashes_w_RC0 k x:
  segRLs tm (h^^k) (h^^(k*2))
    (w++RC0 [x]) (w++RC0 [x+k]).
Proof.
  eapply segRLs_concat.
  1: apply hashes_w.
  applys_eq (RIncs0_spec k [x]).
  f_equal. cbn[RIncs0]. f_equal. lia.
Qed.

Lemma col1_raw a b x n:
  x+a=n*2+1 ->
  segRLs tm ((h^^a++h')++h^^b)
    ((h^^(a*2) ++ H (3+n) (4*2^n)) ++
      h^^(b*2^(length (base1 n))))
    (w++RC0 [x]) (RC0 (out1 b n)).
Proof.
  intros E.
  unfold out1.
  eapply (@segRLs_trans tm
    (h^^a++h') (h^^(a*2)++H (3+n) (4*2^n))
    (h^^b) (h^^(b*2^(length (base1 n))))
    (w++RC0 [x]) (RC0 (base1 n)) (RC0 (RIncs0 b (base1 n)))).
  - eapply (@segRLs_trans tm
      (h^^a) (h^^(a*2)) h' (H (3+n) (4*2^n))
      (w++RC0 [x]) (w++RC0 [x+a]) (RC0 (base1 n))).
    + apply hashes_w_RC0.
    + unfold base1. applys_eq (wdw_Ov n).
      cbn[RIncs0]. f_equal. f_equal. f_equal. lia.
  - apply RIncs0_spec.
Qed.

Lemma col1 a b x n:
  x+a=n*2+1 ->
  segRLs tm (H a b)
    (H (a*2+(3+n)) (4*2^n+b*2^(n+3)))
    (w++RC0 [x]) (RC0 (out1 b n)).
Proof.
  intros E.
  epose proof (col1_raw a b x n E) as X.
  rewrite H_prefix_suffix in X.
  applys_eq X.
  - unfold H. rewrite <-app_assoc. reflexivity.
  - f_equal. rewrite base1_length. lia.
Qed.

Definition lead_word (e:bool) := if e then w else [].

Lemma RC0_app xs ys:
  RC0 xs ++ RC0 ys = RC0 (xs++ys).
Proof. symmetry. apply flat_map_app. Qed.

Lemma w_pow_S n: w^^(S n) = w^^n ++ w.
Proof.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add. cbn[lpow]. rewrite app_nil_r. reflexivity.
Qed.

Lemma RC0_cons x xs:
  RC0 [x] ++ RC0 xs = RC0 (x::xs).
Proof. applys_eq (RC0_app [x] xs). Qed.

Lemma RC0_succ x:
  RC0 [x] ++ w = RC0 [S x].
Proof.
  cbn[flat_map]. rewrite w_pow_S.
  repeat rewrite app_nil_r.
  rewrite app_assoc. reflexivity.
Qed.

Lemma RC0_cons_succ x xs:
  (RC0 [x] ++ w) ++ RC0 xs = RC0 (S x::xs).
Proof. rewrite RC0_succ. apply RC0_cons. Qed.

Lemma RC0_cons_succ_r x xs:
  RC0 [x] ++ (w ++ RC0 xs) = RC0 (S x::xs).
Proof.
  transitivity ((RC0 [x] ++ w) ++ RC0 xs).
  - apply app_assoc.
  - apply RC0_cons_succ.
Qed.

Lemma column_split (e e':bool) (x0 x:nat) (xs:list nat):
  x=x0+(if e' then 1%nat else 0%nat) ->
  (lead_word e ++ RC0 [x0]) ++ (lead_word e' ++ RC0 xs) =
  lead_word e ++ RC0 (x::xs).
Proof.
  intros E. destruct e,e'; unfold lead_word in *; cbn in E; subst x.
  all: repeat rewrite app_nil_l.
  all: repeat rewrite app_nil_r.
  - replace (x0+1) with (S x0) by lia.
    rewrite <-app_assoc,RC0_cons_succ_r. reflexivity.
  - rewrite Nat.add_0_r,<-app_assoc,RC0_cons. reflexivity.
  - replace (x0+1) with (S x0) by lia.
    apply RC0_cons_succ_r.
  - rewrite Nat.add_0_r. apply RC0_cons.
Qed.

Definition bit_nat (e:bool) := if e then 1%nat else 0%nat.
Definition cut_column (x:nat) (next_lead:bool) := x - bit_nat next_lead.
Definition step_out (lead:bool) (b n:nat) :=
  if lead then out1 b n else out0 b n.
Definition step_a (lead:bool) (a n:nat) :=
  a*2 + (if lead then 3+n else 1+n).
Definition step_b (lead:bool) (b n:nat) :=
  if lead then 4*2^n+b*2^(n+3) else 2*2^n+b*2^(n+2).

Lemma step_seg lead next_lead a b x n:
  0<x ->
  x+a=n*2+1+bit_nat next_lead ->
  segRLs tm (H a b) (H (step_a lead a n) (step_b lead b n))
    (lead_word lead ++ RC0 [cut_column x next_lead])
    (RC0 (step_out lead b n)).
Proof.
  intros Hx E.
  destruct lead,next_lead;
    cbn[lead_word cut_column bit_nat step_a step_b step_out] in *.
  - applys_eq (col1 a b (x-1) n); lia.
  - applys_eq (col1 a b x n); try lia.
    unfold cut_column,bit_nat. rewrite Nat.sub_0_r. reflexivity.
  - applys_eq (col0 a b (x-1) n); try lia; reflexivity.
  - applys_eq (col0 a b x n); try lia.
    unfold cut_column,bit_nat. rewrite Nat.sub_0_r. reflexivity.
Qed.

Definition splitN z := (N.div2 (N.pred z), N.even z).
Definition step_aN (lead:bool) (a n:N) :=
  (2*a+n+1+2*N.b2n lead)%N.

Lemma splitN_spec z:
  z<>0%N ->
  let '(n,e) := splitN z in
  z = (n*2+1+N.b2n e)%N.
Proof.
  intros Hz.
  unfold splitN.
  pose proof (N.div2_odd (N.pred z)) as E.
  rewrite N.odd_pred in E by exact Hz.
  pose proof (N.succ_pred z Hz) as Es.
  destruct (N.even z); cbn[N.b2n] in *; nia.
Qed.

Lemma step_aN_to_nat lead a n:
  N.to_nat (step_aN lead a n) =
  step_a lead (N.to_nat a) (N.to_nat n).
Proof.
  destruct lead; unfold step_aN,step_a; cbn[N.b2n].
  all: repeat rewrite N2Nat.inj_add.
  all: repeat rewrite N2Nat.inj_mul.
  all: cbn; lia.
Qed.

Definition right_state lead xs :=
  (lead_word lead ++ RC0 xs) *> w *> 0inf.

Lemma right_column_split lead next_lead x xs:
  0<x ->
  (lead_word lead ++ RC0 [cut_column x next_lead]) *>
    right_state next_lead xs =
  right_state lead (x::xs).
Proof.
  intros Hx.
  assert (E: x=cut_column x next_lead+bit_nat next_lead).
  { unfold cut_column,bit_nat. destruct next_lead; cbn; lia. }
  pose proof (column_split lead next_lead (cut_column x next_lead)
    x xs E) as C.
  unfold right_state.
  rewrite Str_app_assoc.
  repeat rewrite <-Str_app_assoc.
  f_equal. rewrite C. reflexivity.
Qed.

Lemma RC0_app_side xs ys r:
  RC0 (xs++ys) *> r = RC0 xs *> RC0 ys *> r.
Proof.
  rewrite <-RC0_app,Str_app_assoc. reflexivity.
Qed.

(** The executable certificate uses binary naturals.  Converting the
    parameters of the second sweep to unary before evaluation would build
    enormous Peano terms, even though the list of columns itself is short. *)
Fixpoint RIncsN (k:N) (ls:list N) : list N :=
  match ls with
  | [] => []
  | x::ls' => (k+x)%N :: RIncsN (k*2)%N ls'
  end.

Definition base0N n :=
  [0%N;2%N] ++ RIncsN 2%N ([1%N]^^N.to_nat n).

Definition base1N n :=
  [0%N;2%N;3%N] ++ RIncsN 4%N ([1%N]^^N.to_nat n).

Definition outN (lead:bool) (b n:N) :=
  RIncsN b (if lead then base1N n else base0N n).

Definition step_bN (lead:bool) (b n:N) :=
  if lead
  then (4*2^n+b*2^(n+3))%N
  else (2*2^n+b*2^(n+2))%N.

Record SweepResultN := mkSweepN {
  sweep_outN : list N;
  sweep_aN : N;
  sweep_bN : N;
  sweep_leadN : bool
}.

Fixpoint sweepN (a b:N) (lead:bool) (xs:list N) : SweepResultN :=
  match xs with
  | [] => mkSweepN [] a b lead
  | x::xs' =>
      let '(n,next_lead) := splitN (x+a)%N in
      let rr := sweepN (step_aN lead a n) (step_bN lead b n)
        next_lead xs' in
      mkSweepN (outN lead b n++sweep_outN rr)
        (sweep_aN rr) (sweep_bN rr) (sweep_leadN rr)
  end.

Lemma RIncsN_to_nat k ls:
  map N.to_nat (RIncsN k ls) =
  RIncs0 (N.to_nat k) (map N.to_nat ls).
Proof.
  gen k. induction ls as [|x ls IH]; intros k;
    cbn[RIncsN RIncs0 map].
  - reflexivity.
  - rewrite N2Nat.inj_add. cbn. f_equal.
    replace (N.to_nat k*2) with (N.to_nat (k*2)%N).
    apply IH.
    rewrite N2Nat.inj_mul. reflexivity.
Qed.

Lemma map_one_lpowN n:
  map N.to_nat ([1%N]^^n) = [1%nat]^^n.
Proof.
  induction n; cbn[lpow].
  - reflexivity.
  - rewrite map_app,IHn. reflexivity.
Qed.

Lemma base0N_to_nat n:
  map N.to_nat (base0N n) = base0 (N.to_nat n).
Proof.
  unfold base0N,base0.
  rewrite map_app,RIncsN_to_nat,map_one_lpowN.
  reflexivity.
Qed.

Lemma base1N_to_nat n:
  map N.to_nat (base1N n) = base1 (N.to_nat n).
Proof.
  unfold base1N,base1.
  rewrite map_app,RIncsN_to_nat,map_one_lpowN.
  reflexivity.
Qed.

Lemma outN_to_nat lead b n:
  map N.to_nat (outN lead b n) =
  step_out lead (N.to_nat b) (N.to_nat n).
Proof.
  unfold outN,step_out.
  rewrite RIncsN_to_nat.
  destruct lead; [rewrite base1N_to_nat|rewrite base0N_to_nat]; reflexivity.
Qed.

Lemma step_bN_to_nat lead b n:
  N.to_nat (step_bN lead b n) =
  step_b lead (N.to_nat b) (N.to_nat n).
Proof.
  destruct lead; unfold step_bN,step_b.
  all: repeat rewrite N2Nat.inj_add.
  all: repeat rewrite N2Nat.inj_mul.
  all: repeat rewrite N2Nat.inj_pow.
  all: cbn; lia.
Qed.

Lemma sweepN_closed_spec xs:
  forall a b lead,
  Forall (fun x => (0<x)%N) xs ->
  sweep_leadN (sweepN a b lead xs) = false ->
  segRLs tm (H (N.to_nat a) (N.to_nat b))
    (H (N.to_nat (sweep_aN (sweepN a b lead xs)))
       (N.to_nat (sweep_bN (sweepN a b lead xs))))
    (lead_word lead ++ RC0 (map N.to_nat xs))
    (RC0 (map N.to_nat (sweep_outN (sweepN a b lead xs)))).
Proof.
  induction xs as [|x xs IH]; intros a b lead Hpos Hclosed.
  - cbn[sweepN] in *. destruct lead; try discriminate.
    change (segRLs tm (H (N.to_nat a) (N.to_nat b))
      (H (N.to_nat a) (N.to_nat b)) [] []).
    apply segRLs_nil.
  - inverts Hpos.
    destruct (splitN (x+a)%N) as [n next_lead] eqn:Esp.
    cbn[sweepN]. rewrite Esp. cbn.
    cbn[sweepN] in Hclosed. rewrite Esp in Hclosed. cbn in Hclosed.
    assert (Hz: (x+a)%N<>0%N) by nia.
    pose proof (splitN_spec (x+a)%N Hz) as Esum.
    rewrite Esp in Esum. cbn in Esum.
    assert (Hx0: x<>0%N) by nia.
    assert (Hxnat: 0%nat<N.to_nat x).
    { assert (N.to_nat x<>0%nat).
      { intros E. apply Hx0. apply N2Nat.inj.
        change (N.to_nat x = N.to_nat 0%N). exact E. }
      lia. }
    assert (Esum_nat:
      N.to_nat x+N.to_nat a=
      N.to_nat n*2+1+bit_nat next_lead).
    { apply (f_equal N.to_nat) in Esum.
      repeat rewrite N2Nat.inj_add in Esum.
      repeat rewrite N2Nat.inj_mul in Esum.
      unfold bit_nat.
      destruct next_lead; cbn[N.b2n] in *; lia. }
    epose proof (step_seg lead next_lead
      (N.to_nat a) (N.to_nat b) (N.to_nat x) (N.to_nat n)
      Hxnat Esum_nat) as Hstep.
    rewrite <-outN_to_nat in Hstep.
    epose proof (IH (step_aN lead a n) (step_bN lead b n)
      next_lead H3 Hclosed) as Htail.
    rewrite step_aN_to_nat,step_bN_to_nat in Htail.
    epose proof (segRLs_concat Hstep Htail) as X.
    applys_eq X.
    + symmetry. eapply column_split.
      unfold cut_column,bit_nat.
      destruct next_lead; cbn in *; lia.
    + symmetry. rewrite map_app. apply RC0_app.
Qed.

Definition sweep_returnN a b lead xs :=
  sweep_outN (sweepN a b lead xs) ++
  [sweep_bN (sweepN a b lead xs)].

Definition round_listN xs :=
  2%N :: sweep_returnN 0%N 2%N false xs.

Lemma sweep_returnN_spec a b lead xs:
  Forall (fun x => (0<x)%N) xs ->
  sweep_leadN (sweepN a b lead xs) = false ->
  sideRLs tm (H (N.to_nat a) (N.to_nat b))
    (right_state lead (map N.to_nat xs))
    (RC0 (map N.to_nat (sweep_returnN a b lead xs)) *> w*>0inf).
Proof.
  intros Hpos Hclosed.
  epose proof (sweepN_closed_spec xs a b lead Hpos Hclosed) as Hseg.
  epose proof (H_w_return
    (N.to_nat (sweep_aN (sweepN a b lead xs)))
    (N.to_nat (sweep_bN (sweepN a b lead xs)))) as Hedge.
  epose proof (segRLs_sideRLs_concat Hseg Hedge) as X.
  unfold right_state,sweep_returnN.
  rewrite map_app. cbn[map]. rewrite RC0_app_side.
  exact X.
Qed.

Lemma round_sideN xs:
  Forall (fun x => (0<x)%N) xs ->
  sweep_leadN (sweepN 0%N 2%N false xs) = false ->
  sideRLs tm h'' (w10 *> right_state false (map N.to_nat xs))
    (w10 *> right_state false (map N.to_nat (round_listN xs))).
Proof.
  intros Hpos Hclosed.
  epose proof (sweep_returnN_spec 0%N 2%N false xs Hpos Hclosed)
    as Hsweep.
  epose proof (segRLs_sideRLs_concat dollar_w10 Hsweep) as X.
  unfold right_state,round_listN in *.
  cbn[lead_word map] in *.
  exact X.
Qed.

Definition MacroN xs :=
  lh {{{ (hL,L) }}} w10 *> right_state false (map N.to_nat xs).

Lemma round_evstepN xs:
  Forall (fun x => (0<x)%N) xs ->
  sweep_leadN (sweepN 0%N 2%N false xs) = false ->
  MacroN xs -->* MacroN (round_listN xs).
Proof.
  intros Hpos Hclosed.
  unfold MacroN.
  eapply sideRLs_concat_1L with (n:=1%nat) (hR:=hR'').
  - cbn[lpow]. apply round_sideN; assumption.
  - change (sideRLs (flip tm) [(hL,hR'')] lh lh).
    exact LRst.
Qed.

Fixpoint controlNN (a:N) (lead:bool) (xs:list N) : bool :=
  match xs with
  | [] => lead
  | x::xs' =>
      let '(n,next_lead) := splitN (x+a)%N in
      controlNN (step_aN lead a n) next_lead xs'
  end.

Lemma controlNN_halt xs:
  forall a lead,
  Forall (fun x => (0<x)%N) xs ->
  controlNN a lead xs = true ->
  forall b,
  sideRLs_halt tm (H (N.to_nat a) (N.to_nat b))
    (right_state lead (map N.to_nat xs)).
Proof.
  induction xs as [|x xs IH]; intros a lead Hpos Hcontrol b.
  - cbn[controlNN] in Hcontrol.
    destruct lead; try discriminate.
    change (sideRLs_halt tm (H (N.to_nat a) (N.to_nat b))
      (w*>w*>0inf)).
    apply H_ww_halt.
  - inverts Hpos.
    destruct (splitN (x+a)%N) as [n next_lead] eqn:Esp.
    cbn[controlNN] in Hcontrol. rewrite Esp in Hcontrol. cbn in Hcontrol.
    assert (Hz: (x+a)%N<>0%N) by nia.
    pose proof (splitN_spec (x+a)%N Hz) as Esum.
    rewrite Esp in Esum. cbn in Esum.
    assert (Hx0: x<>0%N) by nia.
    assert (Hxnat: 0%nat<N.to_nat x).
    { assert (N.to_nat x<>0%nat).
      { intros E. apply Hx0. apply N2Nat.inj.
        change (N.to_nat x = N.to_nat 0%N). exact E. }
      lia. }
    assert (Esum_nat:
      N.to_nat x+N.to_nat a=
      N.to_nat n*2+1+bit_nat next_lead).
    { apply (f_equal N.to_nat) in Esum.
      repeat rewrite N2Nat.inj_add in Esum.
      repeat rewrite N2Nat.inj_mul in Esum.
      unfold bit_nat.
      destruct next_lead; cbn[N.b2n] in *; lia. }
    epose proof (step_seg lead next_lead
      (N.to_nat a) (N.to_nat b) (N.to_nat x) (N.to_nat n)
      Hxnat Esum_nat) as Hstep.
    epose proof (IH (step_aN lead a n) next_lead H3 Hcontrol
      (step_bN lead b n)) as Htail.
    rewrite step_aN_to_nat,step_bN_to_nat in Htail.
    epose proof (segRLs_sideRLs_halt_concat tm _ _ _ _ _
      Hstep Htail) as X.
    applys_eq X.
    symmetry. apply right_column_split. exact Hxnat.
Qed.

Lemma round_haltN xs:
  Forall (fun x => (0<x)%N) xs ->
  controlNN 0%N false xs = true ->
  halts tm (MacroN xs).
Proof.
  intros Hpos Hcontrol.
  epose proof (controlNN_halt xs 0%N false Hpos Hcontrol 2%N)
    as Hsweep.
  change (sideRLs_halt tm (h'++h^^2)
    (right_state false (map N.to_nat xs))) in Hsweep.
  epose proof (segRLs_sideRLs_halt_concat tm _ _ _ _ _
    dollar_w10 Hsweep) as Hdollar.
  change (sideRLs_halt tm h''
    (w10 *> right_state false (map N.to_nat xs))) in Hdollar.
  epose proof (sideRLs_halt_single tm hR'' hL
    (w10 *> right_state false (map N.to_nat xs)) Hdollar lh) as Hright.
  unfold MacroN.
  eapply halts_evstep.
  1: exact Hright.
  apply progress_evstep.
  eapply sideRLs_1L. exact LRst.
Qed.

Fixpoint all_posN (xs:list N) : bool :=
  match xs with
  | [] => true
  | x::xs' => ((0 <? x)%N && all_posN xs')%bool
  end.

Lemma all_posN_spec xs:
  all_posN xs = true -> Forall (fun x => (0<x)%N) xs.
Proof.
  induction xs as [|x xs IH]; cbn[all_posN]; intros H.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hx Hxs].
    constructor.
    + apply N.ltb_lt. exact Hx.
    + apply IH. exact Hxs.
Qed.

Definition L0N : list N := [2%N;2%N].
Definition L1N := round_listN L0N.
Definition L2N := round_listN L1N.

Lemma L0N_positive: all_posN L0N = true.
Proof. native_check_eq. Qed.

Lemma L1N_positive: all_posN L1N = true.
Proof. native_check_eq. Qed.

Lemma L2N_positive: all_posN L2N = true.
Proof. native_check_eq. Qed.

Lemma L0N_closed:
  sweep_leadN (sweepN 0%N 2%N false L0N) = false.
Proof. native_check_eq. Qed.

Lemma L1N_closed:
  sweep_leadN (sweepN 0%N 2%N false L1N) = false.
Proof. native_check_eq. Qed.

Lemma L2N_halt_control:
  controlNN 0%N false L2N = true.
Proof. native_check_eq. Qed.

Lemma initN:
  c0 -->* MacroN L0N.
Proof.
  unfold MacroN,L0N,right_state.
  cbn[map lead_word]. exact init.
Qed.

Theorem halt:
  halts tm c0.
Proof.
  eapply halts_evstep.
  - apply round_haltN.
    + apply all_posN_spec. exact L2N_positive.
    + exact L2N_halt_control.
  - eapply evstep_trans.
    + exact initN.
    + eapply evstep_trans.
      * apply round_evstepN.
        -- apply all_posN_spec. exact L0N_positive.
        -- exact L0N_closed.
      * apply round_evstepN.
        -- apply all_posN_spec. exact L1N_positive.
        -- exact L1N_closed.
Qed.

End TM3.
