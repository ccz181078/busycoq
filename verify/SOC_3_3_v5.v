(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String Wf_nat Compare_dec.

(* SOC33_TM1.TM1 *)
Module TM1.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String Wf_nat Compare_dec.


Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LF_1LD0LC_1RA0RB_1RD---_0RA1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{D}} [1;0;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1] {{B}}> r) (at level 30).

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |1> rd0^^m *> [1;0] *> r.
Proof. es. Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof. es. Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma ROv1 l r n m:
  l |1> rd1^^n *> [1;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <1| rd0^^(2+n+m) *> [1;0] *> r.
Proof. es. Qed.

Lemma RSkip l r: l |> [1;1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.
Lemma LOv1 r n:
  ldh <* ld1^^(1+n) <1| r -->+ ldh <* ld0^^(1+n) |> rd0 *> r.
Proof. es' n & r. Qed.
Lemma ROv1_blank l n:
  l |1> rd1^^n *> [1;0;1;0;0;0;1] *> 0inf -->+
  l <1| rd0^^(n+3) *> [1] *> 0inf.
Proof. es' n & l. Qed.
Lemma Bad_tail l n r: halts tm (l |1> rd1^^n *> [1;0;1;1] *> r).
Proof. esx. Qed.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition RC1 h n m := BinDec2 [0] [1] [0;0] h n (rd1 *> RC m).
Definition RC2 h n m := BinDec2 [0] [1] [0;0] h n ([0] *> rd1 *> RC m).
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC1,RC2,RC;
  rw_Bin; try solve[solve_pow2_lt];
  try solve[repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia]; follow_rule H.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_Inc len n r: 1+n<2^len -> LC len (1+n) <| r -->+ LC len n |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma LC1_Inc len n r: 1+n<2^len -> LC len (1+n) <1| r -->+ LC len n |1> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc1. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC_Inc1 n l: l |1> RC n -->+ l <1| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc1. Qed.
Lemma RC1_Inc h n m l: 1+n<2^(h+1) -> l |> RC1 h (1+n) m -->+ l <| RC1 h n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RC2_Inc h n m l: 1+n<2^(h+1) -> l |1> RC2 h (1+n) m -->+ l <1| RC2 h n m.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc1. Qed.

Lemma L_Pairs len k m: k<2^len -> LC len k <| RC m -->* LC len 0 <| RC (k+m).
Proof.
  gen m; induction k; intros; [finish|].
  follow_inc LC_Inc; follow_inc RC_Inc.
  replace (S k+m) with (k+(1+m)) by lia; apply IHk; lia.
Qed.
Lemma U_Pairs len k m: k<2^len -> LC len k <1| RC m -->* LC len 0 <1| RC (k+m).
Proof.
  gen m; induction k; intros; [finish|].
  follow_inc LC1_Inc; follow_inc RC_Inc1.
  replace (S k+m) with (k+(1+m)) by lia; apply IHk; lia.
Qed.
Lemma R_Sum len k m: k<2^len -> LC len k |> RC m -->+ LC len 0 <| RC (k+m+1).
Proof.
  intros; eapply progress_evstep_trans; [apply RC_Inc|].
  replace (k+m+1) with (k+(1+m)) by lia; apply L_Pairs; lia.
Qed.
Lemma V_Sum len k m: k<2^len -> LC len k |1> RC m -->+ LC len 0 <1| RC (k+m+1).
Proof.
  intros; eapply progress_evstep_trans; [apply RC_Inc1|].
  replace (k+m+1) with (k+(1+m)) by lia; apply U_Pairs; lia.
Qed.
Lemma RC1_Pairs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RC1 h n m -->* LC len k |> RC1 h 0 m.
Proof.
  gen k; induction n; intros; [rewrite Nat.add_0_r; finish|].
  follow_inc RC1_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  apply IHn; lia.
Qed.
Lemma RC2_Pairs len k h n m: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |1> RC2 h n m -->* LC len k |1> RC2 h 0 m.
Proof.
  gen k; induction n; intros; [rewrite Nat.add_0_r; finish|].
  follow_inc RC2_Inc; rewrite Nat.add_succ_r; follow_inc LC1_Inc.
  apply IHn; lia.
Qed.

Lemma LC_Ov len m h:
  LC len 0 <| RC ((m*2+1)*2^h) -->+ LC len (2^len-1) |> RC1 h ((2^h-1)*2) m.
Proof. solve_rule LOv. Qed.
Lemma LC1_Ov len m:
  LC (len+1) 0 <1| RC m -->+ LC (len+1) (2^(len+1)-1) |> RC (m*2).
Proof. replace (len+1) with (1+len) by lia; solve_rule LOv1. Qed.
Lemma RC1_Ov len k h b i m: k<2^len ->
  LC len k |> RC1 h 0 ((((m*2+1)*2^i)*2+1)*2^b-1) -->+
  LC (len+1+h) ((k*2+1)*2^h-1) |1> RC2 (i+b) (((2^i-1)*2+1)*2^b-1) m.
Proof. solve_rule ROv. Qed.
Lemma RC1_Ov_blank len k h b: k<2^len ->
  LC len k |> RC1 h 0 ((0*2+1)*2^b-1) -->+
  LC (len+1+h) ((k*2+1)*2^h-1) |1> RC (2^b).
Proof. solve_rule ROv. Qed.
Lemma RC2_Merge len k h b i m:
  LC len k |1> RC2 h 0 ((((m*2+1)*2^i)*2+1)*2^b-1) -->+
  LC len k <1| RC2 (i+(h+b+2)) (((2^i-1)*2+1)*2^(h+b+2)-1) m.
Proof. solve_rule ROv1. Qed.
Lemma RC2_Merge_blank len k h b:
  LC len k |1> RC2 h 0 ((0*2+1)*2^b-1) -->+ LC len k <1| RC (2^(h+b+2)).
Proof. solve_rule ROv1. Qed.
Close Scope sym.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Lemma entry_arith b i v:
  let m := (((v*2+1)*2^i)*2+1)*2^b-1 in
  let n := ((2^i-1)*2+1)*2^b-1 in
  n<2^(i+b+1) /\ n+v*2^(i+b+2)<=m /\
  (v+1)*2^(i+b+2)=n+m+2.
Proof. cbn zeta; arith. Qed.
Lemma aux_merge_arith h b i v:
  let m := (((v*2+1)*2^i)*2+1)*2^b-1 in
  let H := i+(h+b+2) in
  let n := ((2^i-1)*2+1)*2^(h+b+2)-1 in
  v<m /\ n<2^(H+1) /\ n+v*2^(H+2)+1<=m*2^(h+2) /\
  (v+1)*2^(H+2)=n+(m+1)*2^(h+2)+1.
Proof. cbn zeta; arith. Qed.
Lemma RC2_Sum m: forall len h n k,
  k+n<2^len -> n<2^(h+1) -> m*2^(h+2)<=k ->
  LC len (k+n) |1> RC2 h n m -->+ LC len 0 <1| RC (k+(m+1)*2^(h+2)).
Proof.
  induction m using lt_wf_ind; intros len h n k Hk Hn Hm.
  eapply evstep_progress_trans; [apply RC2_Pairs; lia|].
  destruct (lowbitS_cases' m) as [u b].
  destruct (lowbit_cases' u) as [|v i].
  - eapply progress_evstep_trans; [apply RC2_Merge_blank|].
    replace (k+((0*2+1)*2^b-1+1)*2^(h+2)) with (k+2^(h+b+2)) by arith.
    apply U_Pairs; lia.
  - pose proof (aux_merge_arith h b i v) as Ha; cbn zeta in Ha.
    destruct k as [|k]; [lia|].
    eapply progress_evstep_trans; [apply RC2_Merge|].
    follow_inc LC1_Inc; apply progress_evstep.
    set (N:=((2^i-1)*2+1)*2^(h+b+2)-1) in *.
    assert (HN:N<=k) by lia.
    replace k with (k-N+N) by lia.
    match goal with |- _ -->+ (LC _ 0 <1| RC ?total) =>
      replace total with ((k-N)+(v+1)*2^(i+(h+b+2)+2)) by lia
    end.
    apply H; lia.
Qed.
Lemma RC1_Sum len k h m: k<2^len -> m<=(k*2+1)*2^h-1 ->
  LC len k |> RC1 h 0 m -->+
  LC (len+1+h) 0 <1| RC ((k*2+1)*2^h-1+m+2).
Proof.
  intros Hk Hm; set (K:=(k*2+1)*2^h-1) in *.
  assert (HK:K<2^(len+1+h)) by (unfold K; arith).
  destruct (lowbitS_cases' m) as [u b].
  destruct (lowbit_cases' u) as [|v i].
  - eapply progress_evstep_trans; [apply RC1_Ov_blank; lia|].
    apply progress_evstep.
    replace (K+((0*2+1)*2^b-1)+2) with (K+2^b+1) by arith.
    apply V_Sum; exact HK.
  - pose proof (entry_arith b i v) as Ha; cbn zeta in Ha.
    eapply progress_evstep_trans; [apply RC1_Ov; lia|].
    apply progress_evstep.
    fold K; set (N:=((2^i-1)*2+1)*2^b-1) in *.
    assert (HN:N<=K) by lia.
    replace K with (K-N+N) by lia.
    match goal with |- _ -->+ (LC _ 0 <1| RC ?total) =>
      replace total with ((K-N)+(v+1)*2^(i+b+2)) by lia
    end.
    apply RC2_Sum; lia.
Qed.
Lemma round_spec len h m k:
  k+(2^h-1)*2=2^len-1 -> m<=(k*2+1)*2^h-1 ->
  LC len 0 <| RC ((m*2+1)*2^h) -->+
  LC (len+1+h) 0 <| RC (2^(len+1+h)+((k*2+1)*2^h-1+m+2)*2).
Proof.
  intros Hb Hm; follow10 LC_Ov.
  replace (2^len-1) with (k+(2^h-1)*2) by lia.
  eapply evstep_trans; [apply RC1_Pairs; arith|].
  eapply evstep_trans; [apply progress_evstep; apply RC1_Sum; [arith|exact Hm]|].
  replace (len+1+h) with ((len+h)+1) by lia.
  eapply evstep_trans; [apply progress_evstep; apply LC1_Ov|].
  apply progress_evstep.
  match goal with |- _ -->+ (LC _ 0 <| RC ?total) =>
    replace total with ((2^((len+h)+1)-1)+((k*2+1)*2^h-1+m+2)*2+1) by arith
  end.
  apply R_Sum; arith.
Qed.
Lemma round_bounds x y m: 2<=x -> y+2<m*2+1<(y+2)*4 ->
  let k := (x*y*2+3)*x-1 in
  m<=k<x*x*(y+2)*2 /\
  x*x*(y+2)*2<x*x*(y+2)*2+(k+m+2)*2<x*x*(y+2)*8.
Proof.
  cbn zeta; intros.
  pose proof (Nat.mul_le_mono_r 4 (x*x) y ltac:(nia)); nia.
Qed.
Lemma round_upper x y m: 2<=x -> (m*2+1)*7<(y+2)*24 ->
  (x*x*(y+2)*2+((x*y*2+3)*x-1+m+2)*2)*7 < x*x*(y+2)*48.
Proof.
  intros; pose proof (Nat.mul_le_mono_r 4 (x*x) (y+2) ltac:(nia)); nia.
Qed.
Lemma round_lower x y m: 1<=x -> 2<=y ->
  x*x*(y+2)*4 < x*x*(y+2)*2+((x*y*2+3)*x-1+m+2)*2.
Proof.
  intros; pose proof (Nat.mul_le_mono_l 2 y (x*x) ltac:(lia)); nia.
Qed.
Lemma no_root len h m: 8<=len -> 1<=h ->
  2^len*2<(m*2+1)*2^h -> ((m*2+1)*2^h)*7<2^len*24 ->
  m+1<>2^h*(2^h*4-3).
Proof.
  intros HL Hh Hlo Hhi E.
  destruct (le_dec (h+h+h+2) len).
  - assert (2^(h+h+h+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
    arith.
  - assert (3<=h) by lia.
    assert (2^3<=2^h) by (apply Nat.pow_le_mono_r; lia).
    assert (2^len<=2^(h+h+h+1)) by (apply Nat.pow_le_mono_r; lia).
    arith.
Qed.
Definition P len s := 8<=len /\ (exists u, s=u*2) /\
  ((2^len<s<2^len*2 /\ exists u, s=u*4+2) \/
   (2^len*2<s /\ s*7<2^len*24 /\ s<>2^len*3)).

Lemma closed len s: P len s -> exists len' s',
  LC len 0 <| RC s -->+ LC len' 0 <| RC s' /\ P len' s'.
Proof.
  intros [HL [[u Eu] HP]].
  assert (HB:2^len<s /\ s*7<2^len*24 /\ s<>2^len*3 /\ s<>2^len*2)
    by (destruct HP as [[[? ?] ?]|[? [? ?]]]; nia).
  destruct (lowbit_cases' s) as [|m h]; [nia|].
  assert (Hh:1<=h) by (destruct h; cbn [Nat.pow] in *; nia).
  assert (Hht:h<len+2) by
    (apply Nat.pow_lt_mono_r_iff with (a:=2); arith).
  assert (Hlt:h<len).
  { destruct (le_dec len h); [|lia].
    assert (h=len \/ h=len+1) as [-> | ->] by lia;
      destruct m as [|[|m]]; arith. }
  assert (exists a,len=h+1+a) as [a ->] by (exists (len-h-1); lia).
  set (y:=2^(a+1)-2).
  set (k:=2^h*y+1).
  assert (HX:2<=2^h) by
    (change (2^1<=2^h); apply Nat.pow_le_mono_r; lia).
  assert (Hq:y+2<m*2+1<(y+2)*4) by (unfold y; arith).
  assert (Hq7:(m*2+1)*7<(y+2)*24) by (unfold y; arith).
  pose proof (round_bounds (2^h) y m HX Hq) as HR; cbn zeta in HR.
  pose proof (round_upper (2^h) y m HX Hq7) as HU.
  set (s':=2^(h+1+a+1+h)+((k*2+1)*2^h-1+m+2)*2).
  exists (h+1+a+1+h),s'; split.
  - apply round_spec.
    + unfold k,y; clear -a h; arith.
    + unfold k; clear -HR; nia.
  - unfold P; split; [lia|]; split.
    + exists (2^(h+1+a)*2^h+((k*2+1)*2^h-1+m+2)); unfold s'; clear -a h k m; arith.
    + assert (HU':s'*7<2^(h+1+a+1+h)*24) by (unfold s',k; clear -HU; unfold y in *; arith).
      destruct h as [|h]; [lia|]; destruct h as [|h].
      * right.
        assert (2^8<=2^(1+1+a)) by (apply Nat.pow_le_mono_r; lia).
        assert (2^(1+1+a+1+1)*3<s') by (unfold s',k,y; arith).
        repeat split; try assumption; lia.
      * assert (Hlo:2^(S (S h)+1+a)*2<(m*2+1)*2^(S (S h))).
        { destruct HP as [[? [v E]]|[? ?]]; [cbn [Nat.pow] in E; nia|assumption]. }
        destruct a as [|a].
        -- assert (m=2) by (unfold y in *; arith); subst m.
           left; split; [unfold s',k,y; arith|].
           exists (2^h*2^h*16+2^h*6+1); unfold s',k,y; arith.
        -- right; split.
           ++ pose proof (round_lower (2^(S (S h))) y m ltac:(lia)
                ltac:(unfold y; clear -a; arith)) as HD.
              unfold s',k; clear -HD; unfold y in *; arith.
           ++ split; [exact HU'|].
              intro E; apply (no_root (S (S h)+1+S a) (S (S h)) m); try lia.
              unfold s',k,y in E; clear -E; arith.
Qed.
Lemma init: c0 -->* (LC 4 0 <| RC 40).
Proof. unfold LC,RC; esx. Qed.
Lemma bad_predecessor: halts tm (LC 5 0 <| RC 38).
Proof. unfold LC,RC; cbn; es'. Qed.
Lemma init8: c0 -->* (LC 8 0 <| RC 310).
Proof.
  eapply evstep_trans; [apply init|].
  apply progress_evstep; apply (round_spec 4 3 2 1); cbn; lia.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init8|].
  apply (progress_nonhalt_cond tm (nat*nat) (8,310)
    (fun p => LC (fst p) 0 <| RC (snd p))
    (fun p => P (fst p) (snd p))).
  - intros [len s] HP; destruct (closed len s HP) as [len' [s' H]].
    exists (len',s'); exact H.
  - unfold P; cbn; split; [lia|]; split; [exists 155; lia|].
    left; split; [lia|exists 77; lia].
Qed.
End TM1.

From BusyCoq Require Import Individual62 Longitudinal BinaryCounter_v2 ES_v2 ES_v3.
Require Import NArith List Bool Lia PeanoNat ZifyNat String.

(* Shared definitions from SOC33_TM4.v. *)
Module SOC33_TM4.
(* SOC(3,3).TM4 / holdout 41: finite RLE simulation to a proved halting pattern.
   Standalone proof: only BusyCoq and standard-library dependencies. *)
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.BinaryCounter_v2 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import NArith List Bool Lia PeanoNat ZifyNat String.

Import ListNotations.

Module SOC33RLE.
Local Open Scope nat_scope.
Definition t := list (bool*N).
Definition run_value (b:bool) (n:N) (v:nat) :=
  if b then (v+1)*2^(N.to_nat n)-1 else v*2^(N.to_nat n).
Fixpoint value (x:t) : nat := match x with
  | []=>0 | (b,n)::x=>run_value b n (value x) end.
Fixpoint width (x:t) : N := match x with
  | []=>0%N | (_,n)::x=>(n+width x)%N end.

Lemma run_zero b v: run_value b 0 v=v.
Proof. destruct b; cbn [run_value]; lia. Qed.
Lemma run_add b n m v:
  run_value b (n+m) v=run_value b n (run_value b m v).
Proof.
  unfold run_value; rewrite N2Nat.inj_add,Nat.pow_add_r; destruct b; nia.
Qed.
Lemma run_add_value b n x y:
  run_value b n (x+y)=run_value b n x+2^(N.to_nat n)*y.
Proof. unfold run_value; destruct b; nia. Qed.
Lemma run_bound b n m v:
  v<2^(N.to_nat m) -> run_value b n v<2^(N.to_nat (n+m)).
Proof.
  unfold run_value; rewrite N2Nat.inj_add,Nat.pow_add_r; destruct b; nia.
Qed.
Lemma run_bits_bound b n: run_value b n 0<2^(N.to_nat n).
Proof. unfold run_value; destruct b; nia. Qed.
Lemma value_bound x: value x<2^(N.to_nat (width x)).
Proof.
  induction x as [|[b n] x IH]; cbn [value width]; [cbn; lia|].
  apply run_bound,IH.
Qed.
Lemma run_carry n v:
  1+run_value true n v=run_value false n (1+v).
Proof. unfold run_value; nia. Qed.
Lemma run_succ b n v:
  run_value b (N.succ n) v=(if b then 1 else 0)+2*run_value b n v.
Proof.
  unfold run_value; rewrite N2Nat.inj_succ; cbn [Nat.pow]; destruct b; nia.
Qed.
Lemma run_peel b n v:
  n<>0%N -> run_value b n v=(if b then 1 else 0)+2*run_value b (N.pred n) v.
Proof.
  intros H; replace n with (N.succ (N.pred n)) at 1 by lia; apply run_succ.
Qed.

(* Zero-size runs and high leading zeros are harmless; correctness below
   does not require a canonical-form invariant. Only new heads are merged. *)
Definition push (b:bool) (n:N) (x:t) : t :=
  if N.eqb n 0 then x else match x with
  | []=>if b then [(true,n)] else []
  | (a,m)::xs=>if Bool.eqb b a then (b,(n+m)%N)::xs else (b,n)::x end.
Lemma push_spec b n x: value (push b n x)=run_value b n (value x).
Proof.
  unfold push; destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; symmetry; apply run_zero.
  - destruct x as [|[a m] x]; destruct b; cbn [value run_value]; try lia;
      destruct a; cbn [value]; try reflexivity; apply run_add.
Qed.

Fixpoint succ (x:t) : t := match x with
  | []=>[(true,1%N)]
  | (b,n)::xs=>if N.eqb n 0 then succ xs else
      if b then push false n (succ xs)
      else push true 1 (push false (N.pred n) xs) end.
Fixpoint pred (x:t) : option t := match x with
  | []=>None
  | (b,n)::xs=>if N.eqb n 0 then pred xs else
      if b then Some (push false 1 (push true (N.pred n) xs))
      else match pred xs with None=>None | Some y=>Some (push true n y) end end.

Lemma succ_spec x: value (succ x)=1+value x.
Proof.
  induction x as [|[b n] x IH]; cbn [succ value]; [reflexivity|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; rewrite run_zero; assumption.
  - apply N.eqb_neq in E; destruct b.
    + rewrite push_spec,IH,run_carry; reflexivity.
    + rewrite !push_spec,(run_peel false n _ E); cbn [run_value]; nia.
Qed.
Lemma pred_spec x:
  match pred x with None=>value x=0 | Some y=>value x=1+value y end.
Proof.
  induction x as [|[b n] x IH]; cbn [pred value]; [reflexivity|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; rewrite run_zero; assumption.
  - apply N.eqb_neq in E; destruct b.
    + rewrite !push_spec,(run_peel true n _ E); cbn [run_value]; nia.
    + destruct (pred x) as [y|]; rewrite IH.
      * rewrite push_spec,run_carry; reflexivity.
      * reflexivity.
Qed.

Fixpoint cut (n:N) (x:t) {struct x} : t*t :=
  if N.eqb n 0 then ([],x) else match x with
  | []=>([(false,n)],[])
  | (b,k)::xs=>if N.leb n k then ([(b,n)],push b (k-n) xs)
      else let '(lo,hi):=cut (n-k) xs in ((b,k)::lo,hi) end.

Lemma run_split b n k v:
  (n<=k)%N -> run_value b k v=
    run_value b n 0+2^(N.to_nat n)*run_value b (k-n) v.
Proof.
  intros H; replace k with (n+(k-n))%N at 1 by lia.
  rewrite run_add; apply (run_add_value b n 0).
Qed.
Lemma pow_split n k:
  (k<=n)%N -> 2^(N.to_nat n)=2^(N.to_nat k)*2^(N.to_nat (n-k)).
Proof.
  intros H; replace n with (k+(n-k))%N at 1 by lia.
  rewrite N2Nat.inj_add,Nat.pow_add_r; reflexivity.
Qed.
Lemma cut_spec n x:
  let '(lo,hi):=cut n x in
  width lo=n /\ value x=value lo+2^(N.to_nat n)*value hi /\
  value lo<2^(N.to_nat n).
Proof.
  revert n; induction x as [|[b k] x IH]; intros n; cbn [cut];
    destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; cbn; repeat split; lia.
  - cbn [value width run_value]; repeat split; try lia.
  - apply N.eqb_eq in E; subst; cbn [value width]; cbn; repeat split; lia.
  - destruct (N.leb n k) eqn:C.
    + apply N.leb_le in C; cbn [value width]; rewrite push_spec.
      repeat split; [lia|apply run_split,C|apply run_bits_bound].
    + apply N.leb_gt in C.
      destruct (cut (n-k) x) as [lo hi] eqn:D.
      specialize (IH (n-k)%N); rewrite D in IH; cbn in IH.
      destruct IH as [Hw [Hv Hb]]; cbn [width value].
      split; [lia|]; split.
      * rewrite Hv,run_add_value,(pow_split n k) by lia; nia.
      * replace n with (k+(n-k))%N by lia; apply run_bound,Hb.
Qed.

Fixpoint prepend (x y:t) : t := match x with
  | []=>y | (b,n)::x=>push b n (prepend x y) end.
Lemma prepend_spec x y:
  value (prepend x y)=value x+2^(N.to_nat (width x))*value y.
Proof.
  induction x as [|[b n] x IH]; cbn [prepend value width]; [cbn; lia|].
  rewrite push_spec,IH,run_add_value,N2Nat.inj_add,Nat.pow_add_r; nia.
Qed.

(* q incoming increments through an all-zero/all-one block. The zero-input
   case of an all-one block is distinct: its original words stay unchanged. *)
Definition flow (b:bool) (n:N) (c:t) : t*t :=
  if b then match pred c with
    | None=>([(true,n)],[])
    | Some p=>let '(lo,hi):=cut n p in (lo,succ hi) end
  else cut n c.
Lemma flow_spec b n c:
  let '(lo,hi):=flow b n c in
  width lo=n /\ run_value b n 0+value c=value lo+2^(N.to_nat n)*value hi /\
  value lo<2^(N.to_nat n).
Proof.
  unfold flow; destruct b.
  - pose proof (pred_spec c) as Hp; destruct (pred c) as [p|].
    + pose proof (cut_spec n p) as Hc; destruct (cut n p) as [lo hi].
      cbn zeta in Hc; destruct Hc as [Hw [Hv Hb]].
      rewrite succ_spec; repeat split; try assumption.
      unfold run_value; nia.
    + cbn [width value]; rewrite Hp; repeat split; [lia|unfold run_value; lia|apply run_bits_bound].
  - pose proof (cut_spec n c) as H; destruct (cut n c) as [lo hi].
    cbn zeta in H; cbn [run_value]; exact H.
Qed.

Fixpoint add (x c:t) {struct x} : t := match x with
  | []=>c
  | (b,n)::x=>let '(lo,hi):=flow b n c in prepend lo (add x hi) end.
Lemma add_spec x c: value (add x c)=value x+value c.
Proof.
  revert c; induction x as [|[b n] x IH]; intros c; cbn [add value]; [reflexivity|].
  pose proof (flow_spec b n c) as H; destruct (flow b n c) as [lo hi].
  cbn zeta in H; destruct H as [Hw [Hv Hb]].
  rewrite prepend_spec,IH,Hw; unfold run_value in *; destruct b; nia.
Qed.

Definition norm x := prepend x [].
Lemma norm_spec x: value (norm x)=value x.
Proof. unfold norm; rewrite prepend_spec; cbn; lia. Qed.
Fixpoint eqb (x y:t) : bool := match x,y with
  | [],[]=>true
  | (b,n)::x,(a,m)::y=>if Bool.eqb b a then if N.eqb n m then eqb x y else false else false
  | _,_=>false end.
Lemma eqb_spec x y: eqb x y=true -> x=y.
Proof.
  revert y; induction x as [|[b n] x IH]; intros [|[a m] y] H; try discriminate; [reflexivity|].
  destruct b,a; cbn [eqb] in H; try discriminate;
    destruct (N.eqb n m) eqn:E; try discriminate;
    apply N.eqb_eq in E; subst; f_equal; apply IH,H.
Qed.
Definition sum_ok x y z := eqb (norm x) (norm (add y z)).
Lemma sum_ok_spec x y z: sum_ok x y z=true -> value x=value y+value z.
Proof.
  unfold sum_ok; intros H; apply eqb_spec in H.
  apply (f_equal value) in H; rewrite !norm_spec,add_spec in H; exact H.
Qed.

Fixpoint is_zero (x:t) : bool := match x with
  | []=>true
  | (b,n)::x=>if N.eqb n 0 then is_zero x else if b then false else is_zero x end.
Lemma is_zero_spec x: is_zero x=true <-> value x=0.
Proof.
  induction x as [|[b n] x IH]; cbn [is_zero value]; [tauto|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; rewrite run_zero; assumption.
  - apply N.eqb_neq in E; destruct b.
    + rewrite (run_peel true n _ E); split; [discriminate|lia].
    + rewrite IH; unfold run_value; nia.
Qed.

Fixpoint uncons (x:t) : bool*t := match x with
  | []=>(false,[])
  | (b,n)::x=>if N.eqb n 0 then uncons x else (b,push b (N.pred n) x) end.
Lemma uncons_spec x:
  let '(b,y):=uncons x in value x=(if b then 1 else 0)+2*value y.
Proof.
  induction x as [|[b n] x IH]; cbn [uncons value]; [reflexivity|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; rewrite run_zero; assumption.
  - rewrite push_spec; apply run_peel; apply N.eqb_neq,E.
Qed.
Definition fits (n:N) x := N.leb (width x) n.
Lemma fits_spec n x: fits n x=true -> value x<2^(N.to_nat n).
Proof.
  unfold fits; intros H; apply N.leb_le in H.
  eapply Nat.lt_le_trans; [apply value_bound|apply Nat.pow_le_mono_r; lia].
Qed.
End SOC33RLE.

Module SOC33Tape.
Definition word := (Sym*Sym*Sym)%type.
Definition t := list (word*N).
Definition bits (w:word) : list Sym := let '(a,b,c):=w in [a;b;c].
Definition z : word := (0,0,0).
Definition same (x y:word) := let '(a,b,c):=x in let '(d,e,f):=y in
  if BB62.sym_eqb a d then if BB62.sym_eqb b e then BB62.sym_eqb c f else false else false.
Lemma same_spec x y: same x y=true -> x=y.
Proof. destruct x as [[a b] c],y as [[d e] f]; destruct a,b,c,d,e,f; cbn; congruence. Qed.

Fixpoint denote (xs:t) : side := match xs with
  | []=>0inf | (w,n)::xs=>(bits w)^^(N.to_nat n) *> denote xs end.
Definition push w n (xs:t) := if N.eqb n 0 then xs else match xs with
  | []=>if same w z then [] else [(w,n)]
  | (v,m)::xs'=>if same w v then (w,(n+m)%N)::xs' else (w,n)::xs end.
Lemma zero_power n: (bits z)^^n *> 0inf=0inf.
Proof.
  induction n; [reflexivity|].
  change (0 >> 0 >> 0 >> (bits z)^^n *> 0inf=0inf).
  rewrite IHn; solve_const0_eq.
Qed.
Lemma push_spec w n xs: denote (push w n xs)=(bits w)^^(N.to_nat n) *> denote xs.
Proof.
  unfold push; destruct (N.eqb n 0) eqn:H.
  - apply N.eqb_eq in H; subst; reflexivity.
  - destruct xs as [|[v m] xs].
    + destruct (same w z) eqn:E; [apply same_spec in E; subst; symmetry; apply zero_power|reflexivity].
    + destruct (same w v) eqn:E; [apply same_spec in E; subst|reflexivity].
      cbn [denote]; rewrite N2Nat.inj_add,lpow_add,Str_app_assoc; reflexivity.
Qed.

(* Insert a bit while keeping every stored word three bits wide. *)
Fixpoint cons (a:Sym) (xs:t) : t := match xs with
  | []=>push (a,0,0) 1 []
  | ((b,c,d),n)::xs=>if N.eqb n 0 then cons a xs else
      push (a,b,c) 1 (push (d,b,c) (N.pred n) (cons d xs)) end.
Lemma rotate (a b c:Sym) n r:
  [a;b;c]^^n *> a >> r = a >> [b;c;a]^^n *> r.
Proof. induction n; [reflexivity|cbn [lpow Str_app app]; rewrite IHn; reflexivity]. Qed.
Lemma cons_spec a xs: denote (cons a xs)=a >> denote xs.
Proof.
  revert a; induction xs as [|[[[b c] d] n] xs IH]; intros a; cbn [cons denote].
  - rewrite push_spec; change (a >> 0 >> 0 >> 0inf=a >> 0inf).
    repeat rewrite <-const_unfold; reflexivity.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; apply IH.
    + rewrite !push_spec,IH; cbn [bits].
      replace n with (N.succ (N.pred n)) at 2 by (apply N.eqb_neq in E; lia).
      rewrite N2Nat.inj_succ; change (N.to_nat 1) with 1%nat.
      cbn [lpow Str_app app]; rewrite rotate; reflexivity.
Qed.

Fixpoint uncons (xs:t) : Sym*t := match xs with
  | []=>(0,[])
  | ((a,b,c),n)::xs=>if N.eqb n 0 then uncons xs
    else (a,cons b (cons c (push (a,b,c) (N.pred n) xs))) end.
Lemma uncons_spec xs:
  let '(a,ys):=uncons xs in denote xs=a >> denote ys.
Proof.
  induction xs as [|[[[a b] c] n] xs IH]; cbn [uncons denote].
  - apply const_unfold.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IH.
    + rewrite !cons_spec,push_spec; cbn [bits].
      replace n with (N.succ (N.pred n)) at 1 by (apply N.eqb_neq in E; lia).
      rewrite N2Nat.inj_succ; reflexivity.
Qed.

Fixpoint prepend (w:list Sym) xs := match w with
  | []=>xs | a::w=>cons a (prepend w xs) end.
Lemma prepend_spec w xs: denote (prepend w xs)=w *> denote xs.
Proof. induction w; cbn [prepend Str_app]; [reflexivity|rewrite cons_spec,IHw; reflexivity]. Qed.

Fixpoint take_word w (xs:t) : N*t := match xs with
  | []=>(0%N,[])
  | (v,n)::rs=>if N.eqb n 0 then take_word w rs else
    if same w v then let '(m,tail):=take_word w rs in ((n+m)%N,tail) else (0%N,xs) end.
Lemma take_word_spec w xs:
  let '(n,tail):=take_word w xs in denote xs=(bits w)^^(N.to_nat n) *> denote tail.
Proof.
  induction xs as [|[v n] xs IH]; cbn [take_word]; [reflexivity|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; exact IH.
  - destruct (same w v) eqn:H; [apply same_spec in H; subst v|reflexivity].
    destruct (take_word w xs) as [m tail]; cbn zeta in IH; cbn [denote].
    rewrite N2Nat.inj_add,lpow_add,Str_app_assoc,IH; reflexivity.
Qed.
Fixpoint drop_prefix (w:list Sym) (xs:t) : option t := match w with
  | []=>Some xs
  | a::w=>let '(b,ys):=uncons xs in if BB62.sym_eqb a b then drop_prefix w ys else None end.
Lemma drop_prefix_spec w xs ys:
  drop_prefix w xs=Some ys -> denote xs=w *> denote ys.
Proof.
  revert xs ys; induction w as [|a w IH]; intros xs ys H; cbn [drop_prefix] in H.
  - inverts H; reflexivity.
  - pose proof (uncons_spec xs) as Hu; destruct (uncons xs) as [b tail].
    destruct a,b; cbn [BB62.sym_eqb] in H; try discriminate;
      rewrite Hu,(IH _ _ H); reflexivity.
Qed.
Definition repeat_symbol a n xs :=
  push (a,a,a) (n/3)%N (prepend ([a]^^(N.to_nat (n mod 3))) xs).
Lemma repeat_symbol_spec a n xs:
  denote (repeat_symbol a n xs)=[a]^^(N.to_nat n) *> denote xs.
Proof.
  unfold repeat_symbol; rewrite push_spec,prepend_spec; cbn [bits].
  change (([a]^^3)^^(N.to_nat (n/3)) *> [a]^^(N.to_nat (n mod 3)) *> denote xs=
    [a]^^(N.to_nat n) *> denote xs).
  rewrite <-lpow_mul,<-Str_app_assoc,<-lpow_add.
  f_equal; f_equal; pose proof (N.div_mod n 3 ltac:(discriminate)); lia.
Qed.
End SOC33Tape.
End SOC33_TM4.

(* SOC33_TM4.TM4 *)
Module TM4.
Import BusyCoq.Individual62 BusyCoq.Longitudinal BusyCoq.BinaryCounter_v2 BusyCoq.ES_v2 BusyCoq.ES_v3.
Import NArith List Bool Lia PeanoNat ZifyNat String.

Import SOC33_TM4.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RF_0LD0LC_1RE0RB_1RF---_1RA1RD").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation "l <| r" := (l <{{D}} [0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma LOv_finite l r n:
  l <* <[0;1] <* ld1^^n <| r -->+ l <* <[1] <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv11 l r n m:
  l |> rd1^^n *> [1] *> rd1^^m *> [1;1] *> r -->+
  l <* ld0 <* ld1^^(n+m) |> r.
Proof. rewrite Nat.add_comm; es. Qed.
Lemma RSkip l r n:
  l |> [1;1;1]^^n *> r -[tm]->* l <* ld0^^n |> r.
Proof. es. Qed.
Lemma ROv01 l r n m:
  l |> rd1^^n *> [1] *> rd1^^m *> [0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(m+n) <| [0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv01111 l r n m:
  l |> rd1^^n *> [1] *> rd1^^m *> [0;1;1;1;1;0;0;0;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(m+n) <* ld0 <* ld1 <* ld1 <| r.
Proof. es' n m & l r. Qed.
Lemma Bad_tail l r n m:
  halts tm (l |> rd1^^n *> [1] *> rd1^^m *> [1;0;1] *> r).
Proof. esx. Qed.
Lemma Prepare_restart l n m q:
  l |> rd1^^n *> [1] *> rd1^^m *> [0] *> [1]^^(4+q) *> 0inf -->+
  l <* ld0 <* ld1^^(m+n) <* <[1;1] <* <[0]^^q <* <[1] <* ld0^^2 <| rd1 *> 0inf.
Proof. es' n m q & l. Qed.
Lemma Bad_restart l r n m:
  halts tm (l |> rd1^^n *> [1] *> rd1^^m *> [0] *> [1]^^7 *>
    [0;0;0;1;0;0;0] *> r).
Proof. esx. Qed.
Lemma init: c0 -[ tm ]->* (ldh <* ld0^^2 <| rd1 *> 0inf).
Proof. esx. Qed.

Notation hb := ((B,[]),(C,[])).
Notation hf := ((F,[]),(C,[])).
Notation b := [hb].
Notation f := [hf].

Lemma BZero: segRL tm (B,[]) (C,[]) [0;0;0] [1;0;0].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.
Lemma BCarry: segRR tm (B,[]) (B,[]) [1;0;0] [1;1;1].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.
Lemma Return: segLL tm (C,[]) (C,[]) [1;1;1] [0;0;0].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.
Lemma FZero: segRL tm (F,[]) (C,[]) [0;0;0] [0;0;1].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.
Lemma FCarry: segRR tm (F,[]) (F,[]) [0;0;1] [1;1;1].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.
Lemma FOldCarry: segRR tm (F,[]) (F,[]) [1;0;0] [1;1;1].
Proof. intros l r; cbn [to_DH_config]; es' & l r. Qed.

Lemma repeat2 n a a' hs hs' w1 w2:
  segRLs tm (hs^^a) (hs'^^a') w1 w2 ->
  segRLs tm (hs^^2) (hs'^^1) w2 w2 ->
  segRLs tm (hs^^(n*2+a)) (hs'^^(n+a')) w1 w2.
Proof.
  intros H0 H1; induction n; [cbn; assumption|].
  replace (S n*2+a) with ((n*2+a)+2) by lia.
  replace (S n+a') with ((n+a')+1) by lia.
  eapply segRLs_trans_add; eassumption.
Qed.

Ltac finite := apply BoundedConfig.segRLs_c_spec with (T:=100); vm_compute; reflexivity.
Ltac finish_repeat := try solve [rewrite ?Nat.add_0_r; reflexivity]; finite.

Lemma GapCycle n: segRLs tm (b^^(n*2)) (f^^n) [0] [0].
Proof. applys_eq (repeat2 n 0 0 b f [0] [0]); finish_repeat. Qed.
Lemma GapOdd n: segRLs tm (b^^(n*2+1)) (f^^n) [0] [1].
Proof. applys_eq (repeat2 n 1 0 b f [0] [1]); finish_repeat. Qed.
Lemma GapOneEven n: segRLs tm (b^^(n*2)) (f^^n) [1] [1].
Proof. applys_eq (repeat2 n 0 0 b f [1] [1]); finish_repeat. Qed.
Lemma GapOneOdd n: segRLs tm (b^^(n*2+1)) (f^^(n+1)) [1] [0].
Proof. applys_eq (repeat2 n 1 1 b f [1] [0]); finish_repeat. Qed.


Lemma BZeroEven n: segRLs tm (b^^(n*2)) (b^^n) [0;0;0] [0;0;0].
Proof. applys_eq (repeat2 n 0 0 b b [0;0;0] [0;0;0]); finish_repeat. Qed.
Lemma FZeroEven n: segRLs tm (f^^(n*2)) (f^^n) [0;0;0] [0;0;0].
Proof. applys_eq (repeat2 n 0 0 f f [0;0;0] [0;0;0]); finish_repeat. Qed.

Lemma zero_cycles hs d n k:
  (forall c, segRLs tm (hs^^(c*2)) (hs^^c) d d) ->
  segRLs tm (hs^^(k*2^n)) (hs^^k) (d^^n) (d^^n).
Proof.
  intros H; gen k; induction n; intros.
  - cbn; rewrite Nat.mul_1_r; apply segRLs_nil.
  - replace (k*2^(S n)) with ((k*2^n)*2) by (cbn; nia).
    cbn [lpow]; eapply segRLs_concat; [apply H|apply IHn].
Qed.
Lemma BZeros n k:
  segRLs tm (b^^(k*2^n)) (b^^k) (rd0^^n) (rd0^^n).
Proof. apply zero_cycles,BZeroEven. Qed.
Lemma FZeros n k:
  segRLs tm (f^^(k*2^n)) (f^^k) (rd0^^n) (rd0^^n).
Proof. apply zero_cycles,FZeroEven. Qed.
Lemma BFill n k:
  segRLs tm (b^^((k+1)*2^n-1)) (b^^k) (rd0^^n) (rd1^^n).
Proof. eapply BC.IncsOvs; [apply BZero|apply BCarry|apply Return]. Qed.
Lemma FFill n k:
  segRLs tm (f^^((k+1)*2^n-1)) (f^^k) (rd0^^n) ([0;0;1]^^n).
Proof. eapply BC.IncsOvs; [apply FZero|apply FCarry|apply Return]. Qed.

Lemma pass_blocks n hs u v:
  segRLs tm hs hs u v -> segRLs tm hs hs (u^^n) (v^^n).
Proof.
  intros H; induction n; cbn [lpow]; [apply segRLs_nil|].
  eapply segRLs_concat; eassumption.
Qed.
Lemma BOnes n: segRLs tm b b (rd1^^n) (rd0^^n).
Proof. apply pass_blocks; finite. Qed.
Lemma FOnes n: segRLs tm f f ([0;0;1]^^n) (rd0^^n).
Proof. apply pass_blocks; finite. Qed.
Lemma FOldOnes n: segRLs tm f f (rd1^^n) (rd0^^n).
Proof. apply pass_blocks; finite. Qed.

Definition LC len k l := BinDec ld0 ld1 len k l.
Lemma ReturnHead l r:
  (l <* ld0 <{{C}} r) -[tm]->+ (l <| r).
Proof. es' & l r. Qed.
Lemma LC_Inc len k l r:
  1+k<2^len -> LC len (1+k) l <| r -[tm]->+ LC len k l |> r.
Proof. intros; apply LBinDec_spec; [apply LInc|assumption]. Qed.

Lemma RightPrefix n len k l r r':
  k+n<2^len -> sideRLs tm (b^^n) r r' ->
  LC len (k+n) l |> r -[tm]->* LC len k l |> r'.
Proof.
  gen k r; induction n; intros k r Hk Hs.
  - cbn [lpow] in Hs; inverts Hs; rewrite Nat.add_0_r; apply evstep_refl.
  - cbn [lpow app] in Hs.
    inversion Hs as [|hr hl rin mid rout hs Hfirst Hrest]; subst.
    eapply evstep_trans; [apply progress_evstep,Hfirst|].
    eapply evstep_trans; [apply progress_evstep,ReturnHead|].
    replace (k+S n) with (1+(k+n)) by lia.
    eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
    apply IHn; [lia|exact Hrest].
Qed.
Lemma RightAll len k l r r':
  k<2^len -> sideRLs tm (b^^(k+1)) r r' ->
  LC len k l |> r -[tm]->+ LC len 0 l <| r'.
Proof.
  intros Hk Hs; rewrite lpow_add in Hs.
  destruct (sideRLs_split Hs) as [mid [Hp Hlast]].
  eapply evstep_progress_trans.
  - apply (RightPrefix k len 0); [lia|exact Hp].
  - eapply progress_evstep_trans; [apply (sideRLs_1 tm (B,[]) (C,[]) _ _ Hlast)|].
    apply progress_evstep,ReturnHead.
Qed.

Module RN := SOC33RLE.

(* These words are semantic objects only: the evaluator keeps the run list. *)
Fixpoint words (d0 d1:list Sym) (x:RN.t) : list Sym := match x with
  | []=>[]
  | (a,n)::x=>(if a then d1 else d0)^^(N.to_nat n) ++ words d0 d1 x end.

Lemma zero_words hs d0 d1 x k:
  (forall n q, segRLs tm (hs^^(q*2^n)) (hs^^q) (d0^^n) (d0^^n)) ->
  (forall n q, segRLs tm (hs^^((q+1)*2^n-1)) (hs^^q) (d0^^n) (d1^^n)) ->
  segRLs tm (hs^^(RN.value x+2^(N.to_nat (RN.width x))*k)) (hs^^k)
    (d0^^(N.to_nat (RN.width x))) (words d0 d1 x).
Proof.
  intros H0 H1; revert k; induction x as [|[a n] x IH]; intros k.
  - cbn; rewrite Nat.add_0_r; apply segRLs_nil.
  - cbn [RN.value RN.width words].
    replace (RN.run_value a n (RN.value x)+2^(N.to_nat (n+RN.width x))*k)
      with (RN.run_value a n (RN.value x+2^(N.to_nat (RN.width x))*k))
      by (rewrite RN.run_add_value,N2Nat.inj_add,Nat.pow_add_r; nia).
    rewrite N2Nat.inj_add,(lpow_add Sym _ _ d0).
    eapply segRLs_concat; [destruct a; cbn [RN.run_value]; [apply H1|apply H0]|apply IH].
Qed.

Lemma zero_cut hs d0 d1 n c lo hi:
  (forall x k, segRLs tm (hs^^(RN.value x+2^(N.to_nat (RN.width x))*k)) (hs^^k)
    (d0^^(N.to_nat (RN.width x))) (words d0 d1 x)) ->
  RN.cut n c=(lo,hi) ->
  segRLs tm (hs^^(RN.value c)) (hs^^(RN.value hi))
    (d0^^(N.to_nat n)) (words d0 d1 lo).
Proof.
  intros H E; pose proof (RN.cut_spec n c) as Hc; rewrite E in Hc.
  destruct Hc as [Hw [Hv Hb]]; rewrite Hv,<-Hw; apply H.
Qed.
Lemma BZeroCut n c lo hi:
  RN.cut n c=(lo,hi) ->
  segRLs tm (b^^(RN.value c)) (b^^(RN.value hi))
    (rd0^^(N.to_nat n)) (words rd0 rd1 lo).
Proof. apply zero_cut; intros; apply zero_words; [apply BZeros|apply BFill]. Qed.
Lemma FZeroCut n c lo hi:
  RN.cut n c=(lo,hi) ->
  segRLs tm (f^^(RN.value c)) (f^^(RN.value hi))
    (rd0^^(N.to_nat n)) (words rd0 [0;0;1] lo).
Proof. apply zero_cut; intros; apply zero_words; [apply FZeros|apply FFill]. Qed.

Lemma one_cut hs d0 old d1 n c p lo hi:
  (forall m, segRLs tm (hs^^1) (hs^^1) (old^^m) (d0^^m)) ->
  (forall n c lo hi, RN.cut n c=(lo,hi) ->
    segRLs tm (hs^^(RN.value c)) (hs^^(RN.value hi))
      (d0^^(N.to_nat n)) (words d0 d1 lo)) ->
  RN.pred c=Some p -> RN.cut n p=(lo,hi) ->
  segRLs tm (hs^^(RN.value c)) (hs^^(RN.value (RN.succ hi)))
    (old^^(N.to_nat n)) (words d0 d1 lo).
Proof.
  intros H1 H0 Ep Ec; pose proof (RN.pred_spec c) as Hp; rewrite Ep in Hp.
  rewrite Hp,RN.succ_spec; eapply segRLs_trans_add; [apply H1|apply H0,Ec].
Qed.
Lemma BOneCut n c p lo hi:
  RN.pred c=Some p -> RN.cut n p=(lo,hi) ->
  segRLs tm (b^^(RN.value c)) (b^^(RN.value (RN.succ hi)))
    (rd1^^(N.to_nat n)) (words rd0 rd1 lo).
Proof. apply one_cut; [intros; apply BOnes|apply BZeroCut]. Qed.
Lemma FOneCut n c p lo hi:
  RN.pred c=Some p -> RN.cut n p=(lo,hi) ->
  segRLs tm (f^^(RN.value c)) (f^^(RN.value (RN.succ hi)))
    ([0;0;1]^^(N.to_nat n)) (words rd0 [0;0;1] lo).
Proof. apply one_cut; [intros; apply FOnes|apply FZeroCut]. Qed.
Lemma FOldOneCut n c p lo hi:
  RN.pred c=Some p -> RN.cut n p=(lo,hi) ->
  segRLs tm (f^^(RN.value c)) (f^^(RN.value (RN.succ hi)))
    (rd1^^(N.to_nat n)) (words rd0 [0;0;1] lo).
Proof. apply one_cut; [intros; apply FOldOnes|apply FZeroCut]. Qed.

Definition bit_word (a:bool) : list Sym := if a then [1] else [0].
Definition gap (a:bool) c := RN.uncons (if a then RN.succ c else c).
Lemma Gap a c a' out:
  gap a c=(a',out) ->
  segRLs tm (b^^(RN.value c)) (f^^(RN.value out)) (bit_word a) (bit_word a').
Proof.
  unfold gap; intros E; pose proof (RN.uncons_spec (if a then RN.succ c else c)) as H.
  rewrite E in H; destruct a,a'; cbn [bit_word] in *; rewrite ?RN.succ_spec in H.
  - applys_eq (GapOneEven (RN.value out)); f_equal; lia.
  - applys_eq (GapOneOdd (RN.value out-1)); f_equal; lia.
  - applys_eq (GapOdd (RN.value out)); f_equal; lia.
  - applys_eq (GapCycle (RN.value out)); f_equal; lia.
Qed.

Lemma CheckedPrefix len k k' c l r r':
  RN.fits len k=true -> RN.sum_ok k k' c=true ->
  sideRLs tm (b^^(RN.value c)) r r' ->
  LC (N.to_nat len) (RN.value k) l |> r -[tm]->*
  LC (N.to_nat len) (RN.value k') l |> r'.
Proof.
  intros Hk Hc Hs; apply RN.fits_spec in Hk; apply RN.sum_ok_spec in Hc.
  rewrite Hc in *; apply RightPrefix; assumption.
Qed.
Lemma CheckedAll len k l r r':
  RN.fits len k=true -> sideRLs tm (b^^(RN.value (RN.succ k))) r r' ->
  LC (N.to_nat len) (RN.value k) l |> r -[tm]->+
  LC (N.to_nat len) 0 l <| r'.
Proof.
  intros Hk Hs; apply RightAll; [apply RN.fits_spec,Hk|].
  rewrite RN.succ_spec in Hs; replace (RN.value k+1) with (1+RN.value k) by lia; exact Hs.
Qed.

(* A finite prefix is supplied as words, not as unexpanded natural-valued
   counters. Zero output is checked before the untouched suffix is reused. *)
Inductive chunk := ZerosBlock (n:N) | OnesBlock (old:bool) (n:N) | GapBlock (a:bool).
Definition chunk_word x : list Sym := match x with
  | ZerosBlock n=>rd0^^(N.to_nat n)
  | OnesBlock old n=>(if old then rd1 else [0;0;1])^^(N.to_nat n)
  | GapBlock a=>bit_word a end.
Fixpoint chunk_words xs : list Sym := match xs with
  | []=>[] | x::xs=>chunk_word x++chunk_words xs end.
Definition encode_runs (mode:bool) (x:RN.t) :=
  map (fun bn:bool*N=>let '(a,n):=bn in if a then OnesBlock (negb mode) n else ZerosBlock n) x.
Definition signals (mode:bool) : list (DH0*DH0) := if mode then f else b.
Lemma encode_runs_spec mode x:
  chunk_words (encode_runs mode x)=words rd0 (if mode then [0;0;1] else rd1) x.
Proof.
  unfold encode_runs; induction x as [|[a n] x IH]; [reflexivity|].
  destruct a,mode; cbn [map chunk_words chunk_word words negb] in *; rewrite IH; reflexivity.
Qed.
Lemma chunk_words_app xs ys: chunk_words (xs++ys)=chunk_words xs++chunk_words ys.
Proof. induction xs; cbn; [reflexivity|rewrite IHxs,app_assoc; reflexivity]. Qed.

Definition transfer mode x c : option (bool*list chunk*RN.t) := match x with
  | ZerosBlock n=>let '(lo,hi):=RN.cut n c in Some (mode,encode_runs mode lo,hi)
  | OnesBlock old n=>if (if mode then true else old) then match RN.pred c with
      | None=>None
      | Some p=>let '(lo,hi):=RN.cut n p in Some (mode,encode_runs mode lo,RN.succ hi) end
    else None
  | GapBlock a=>if mode then None else let '(a',out):=gap a c in Some (true,[GapBlock a'],out)
  end.
Lemma transfer_spec mode x c mode' xs c':
  transfer mode x c=Some (mode',xs,c') ->
  segRLs tm ((signals mode)^^(RN.value c)) ((signals mode')^^(RN.value c'))
    (chunk_word x) (chunk_words xs).
Proof.
  destruct x as [n|old n|a]; cbn [transfer]; intros E.
  - destruct (RN.cut n c) as [lo hi] eqn:H; inverts E; rewrite encode_runs_spec.
    destruct mode'; cbn [signals chunk_word]; [apply FZeroCut|apply BZeroCut]; assumption.
  - destruct mode,old; cbn in E; try discriminate;
      destruct (RN.pred c) as [p|] eqn:Hp; try discriminate;
      destruct (RN.cut n p) as [lo hi] eqn:H; inverts E;
      rewrite encode_runs_spec; cbn [signals chunk_word];
      first [eapply FOldOneCut|eapply FOneCut|eapply BOneCut]; eassumption.
  - destruct mode; [discriminate|]; destruct (gap a c) as [a' out] eqn:H; inverts E.
    cbn [signals chunk_words chunk_word]; rewrite app_nil_r; apply Gap,H.
Qed.

Fixpoint run mode c xs : option (list chunk) :=
  if RN.is_zero c then Some xs else match xs with
  | []=>None
  | x::xs=>match transfer mode x c with
    | None=>None
    | Some (mode',ys,out)=>match run mode' out xs with
      | None=>None | Some zs=>Some (ys++zs) end end end.
Lemma run_spec mode c xs ys:
  run mode c xs=Some ys -> forall r,
  sideRLs tm ((signals mode)^^(RN.value c)) (chunk_words xs *> r) (chunk_words ys *> r).
Proof.
  revert mode c ys; induction xs as [|x xs IH]; intros mode c ys E r;
    cbn [run] in E; destruct (RN.is_zero c) eqn:H0.
  - inverts E; apply RN.is_zero_spec in H0; rewrite H0; constructor.
  - discriminate.
  - inverts E; apply RN.is_zero_spec in H0; rewrite H0; constructor.
  - destruct (transfer mode x c) as [[[mode' zs] out]|] eqn:H; try discriminate.
    destruct (run mode' out xs) as [ys'|] eqn:Hr; inverts E.
    rewrite chunk_words_app; cbn [chunk_words].
    rewrite !Str_app_assoc.
    eapply segRLs_sideRLs_concat; [eapply transfer_spec,H|apply IH,Hr].
Qed.

Module PT := SOC33Tape.

Definition adjoin x (p:list chunk*PT.t) := let '(xs,r):=p in (x::xs,r).
Fixpoint scanF extra (r:PT.t) : list chunk*PT.t := match r with
  | []=>([ZerosBlock extra],[])
  | (w,n)::rs=>if N.eqb n 0 then scanF extra rs else match w with
    | (S0,S0,S0)=>adjoin (ZerosBlock n) (scanF extra rs)
    | (S1,S0,S0)=>adjoin (OnesBlock true n) (scanF extra rs)
    | (S0,S0,S1)=>adjoin (OnesBlock false n) (scanF extra rs)
    | _=>([],r) end end.
Definition as_bit (a:Sym) := match a with S0=>false | S1=>true end.
Definition of_bit (a:bool) : Sym := if a then S1 else S0.
Definition scanGap extra r :=
  let '(a,rs):=PT.uncons r in adjoin (GapBlock (as_bit a)) (scanF extra rs).
Fixpoint scanB extra (r:PT.t) : list chunk*PT.t := match r with
  | []=>([ZerosBlock extra],[])
  | (w,n)::rs=>if N.eqb n 0 then scanB extra rs else match w with
    | (S0,S0,S0)=>adjoin (ZerosBlock n) (scanB extra rs)
    | (S1,S0,S0)=>adjoin (OnesBlock true n) (scanB extra rs)
    | _=>scanGap extra r end end.

Lemma scanF_spec extra r:
  let '(xs,tail):=scanF extra r in PT.denote r=chunk_words xs *> PT.denote tail.
Proof.
  induction r as [|[[[a b] c] n] r IH]; cbn [scanF].
  - cbn [chunk_words chunk_word PT.denote]; rewrite app_nil_r; symmetry; apply PT.zero_power.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IH.
    + destruct (scanF extra r) as [xs tail] eqn:H; cbn zeta in IH.
      destruct a,b,c; cbn [adjoin PT.denote PT.bits chunk_words chunk_word];
        try reflexivity; rewrite Str_app_assoc,IH; reflexivity.
Qed.
Lemma scanGap_spec extra r:
  let '(xs,tail):=scanGap extra r in PT.denote r=chunk_words xs *> PT.denote tail.
Proof.
  unfold scanGap; pose proof (PT.uncons_spec r) as Hg; destruct (PT.uncons r) as [a rs].
  pose proof (scanF_spec extra rs) as Hf; destruct (scanF extra rs) as [xs tail].
  cbn [adjoin]; cbn zeta in Hg,Hf; rewrite Hg,Hf; destruct a; reflexivity.
Qed.
Lemma scanB_spec extra r:
  let '(xs,tail):=scanB extra r in PT.denote r=chunk_words xs *> PT.denote tail.
Proof.
  induction r as [|[[[a b] c] n] r IH]; cbn [scanB].
  - cbn [chunk_words chunk_word PT.denote]; rewrite app_nil_r; symmetry; apply PT.zero_power.
  - destruct (N.eqb n 0) eqn:E.
    + apply N.eqb_eq in E; subst; exact IH.
    + destruct a,b,c; try apply scanGap_spec;
        destruct (scanB extra r) as [xs tail]; cbn zeta in IH;
        cbn [adjoin PT.denote PT.bits chunk_words chunk_word]; rewrite Str_app_assoc,IH; reflexivity.
Qed.

Fixpoint write_chunks xs r := match xs with
  | []=>r
  | x::xs=>let r':=write_chunks xs r in match x with
    | ZerosBlock n=>PT.push PT.z n r'
    | OnesBlock old n=>PT.push (if old then (1,0,0) else (0,0,1)) n r'
    | GapBlock a=>PT.cons (of_bit a) r' end end.
Lemma write_chunks_spec xs r:
  PT.denote (write_chunks xs r)=chunk_words xs *> PT.denote r.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  destruct x as [n|old n|a]; cbn [write_chunks chunk_words chunk_word];
    rewrite ?PT.push_spec,?PT.cons_spec,IH,?Str_app_assoc; try reflexivity.
  all: try destruct old; try destruct a; reflexivity.
Qed.

Definition calls c r := let '(xs,tail):=scanB (N.succ (RN.width c)) r in
  match run false c xs with None=>None | Some ys=>Some (write_chunks ys tail) end.
Lemma calls_spec c r r':
  calls c r=Some r' -> sideRLs tm (b^^(RN.value c)) (PT.denote r) (PT.denote r').
Proof.
  unfold calls; intros E; pose proof (scanB_spec (N.succ (RN.width c)) r) as Hp.
  destruct (scanB (N.succ (RN.width c)) r) as [xs tail] eqn:H.
  destruct (run false c xs) as [ys|] eqn:Hr; inverts E.
  rewrite write_chunks_spec,Hp; apply (run_spec false c xs ys),Hr.
Qed.

(* These two numerical proposals are not trusted: sum_ok and calls check the
   proposed budget split and the complete right-side execution. *)
Definition complement (x:RN.t) :=
  RN.norm (map (fun an:bool*N=>let '(a,n):=an in (negb a,n)) x).
Definition subtract_hint k c :=
  let n:=RN.width k in let '(lo,_):=RN.cut n c in
  RN.norm (fst (RN.cut n (RN.succ (RN.add k (complement lo))))).
Fixpoint counter_bits xs : RN.t := match xs with
  | []=>[]
  | x::xs=>(match x with
    | ZerosBlock n=>(false,n) | OnesBlock _ n=>(true,n) | GapBlock a=>(a,1%N) end)::counter_bits xs end.
Definition capacity k r := complement (counter_bits (fst (scanB (N.succ (RN.width k)) r))).
Definition right_step len k r : option (bool*RN.t*PT.t) :=
  if RN.fits len k then match calls (RN.succ k) r with
  | Some r'=>Some (true,[],r')
  | None=>let c:=capacity k r in if RN.is_zero c then None else
    let k':=subtract_hint k c in if RN.sum_ok k k' c then
      match calls c r with Some r'=>Some (false,k',r') | None=>None end
    else None end else None.
Definition config (left:bool) len k l r :=
  if left then LC (N.to_nat len) (RN.value k) l <| PT.denote r
  else LC (N.to_nat len) (RN.value k) l |> PT.denote r.
Lemma right_step_spec len k r left k' r' l:
  right_step len k r=Some (left,k',r') ->
  RN.value k'<2^(N.to_nat len) /\
  (config false len k l r -[tm]->* config left len k' l r').
Proof.
  unfold right_step; intros E; destruct (RN.fits len k) eqn:Hk; try discriminate.
  destruct (calls (RN.succ k) r) as [rs|] eqn:Hfull.
  - inverts E; split; [cbn [RN.value]; lia|].
    unfold config; apply progress_evstep,CheckedAll; [exact Hk|apply calls_spec,Hfull].
  - destruct (RN.is_zero (capacity k r)) eqn:Hz; try discriminate.
    destruct (RN.sum_ok k (subtract_hint k (capacity k r)) (capacity k r)) eqn:Hs; try discriminate.
    destruct (calls (capacity k r) r) as [rs|] eqn:Hc; inverts E.
    split.
    + apply RN.fits_spec in Hk; apply RN.sum_ok_spec in Hs; lia.
    + unfold config; eapply CheckedPrefix; [exact Hk|exact Hs|apply calls_spec,Hc].
Qed.

Lemma left_words_spec x l:
  words ld1 ld0 x *> l=LC (N.to_nat (RN.width x)) (RN.value x) l.
Proof.
  induction x as [|[a n] x IH]; [reflexivity|].
  pose proof (RN.value_bound ((a,n)::x)) as Hb.
  cbn [RN.value RN.width] in Hb; rewrite N2Nat.inj_add,Nat.add_comm in Hb.
  cbn [words RN.value RN.width]; rewrite Str_app_assoc,IH,N2Nat.inj_add,Nat.add_comm.
  unfold LC; destruct a; cbn [RN.run_value] in *.
  - rewrite BinDec_mulpow2sub1' by exact Hb; reflexivity.
  - rewrite BinDec_mulpow2 by exact Hb; reflexivity.
Qed.

Definition low n x := fst (RN.cut n x).
Lemma low_spec n x:
  RN.value x<2^(N.to_nat n) -> RN.width (low n x)=n /\ RN.value (low n x)=RN.value x.
Proof.
  unfold low; pose proof (RN.cut_spec n x) as H; destruct (RN.cut n x) as [lo hi].
  cbn [fst] in H |- *; intros Hb; destruct H as [Hw [Hv Hl]]; split; [exact Hw|].
  destruct (RN.value hi); nia.
Qed.
Fixpoint scanLeft (l:PT.t) : RN.t*PT.t := match l with
  | []=>([],[])
  | (w,n)::ls=>if N.eqb n 0 then scanLeft ls else match w with
    | (S0,S1,S1)=>let '(ds,tail):=scanLeft ls in ((true,n)::ds,tail)
    | (S1,S1,S1)=>let '(ds,tail):=scanLeft ls in ((false,n)::ds,tail)
    | _=>([],l) end end.
Lemma scanLeft_spec l:
  let '(ds,tail):=scanLeft l in PT.denote l=words ld1 ld0 ds *> PT.denote tail.
Proof.
  induction l as [|[[[a b] c] n] l IH]; cbn [scanLeft]; [reflexivity|].
  destruct (N.eqb n 0) eqn:E.
  - apply N.eqb_eq in E; subst; exact IH.
  - destruct (scanLeft l) as [ds tail]; cbn zeta in IH.
    destruct a,b,c; cbn [PT.denote PT.bits words]; try reflexivity;
      rewrite Str_app_assoc,IH; reflexivity.
Qed.
Fixpoint put_left (ds:RN.t) tail := match ds with
  | []=>tail | (a,n)::ds=>PT.push (if a then (0,1,1) else (1,1,1)) n (put_left ds tail) end.
Lemma put_left_spec ds tail:
  PT.denote (put_left ds tail)=words ld1 ld0 ds *> PT.denote tail.
Proof.
  induction ds as [|[a n] ds IH]; [reflexivity|].
  destruct a; cbn [put_left words]; rewrite PT.push_spec,IH,Str_app_assoc; reflexivity.
Qed.
Definition padded_left len k tail := put_left (low len k) tail.
Lemma padded_left_spec len k tail:
  RN.value k<2^(N.to_nat len) ->
  PT.denote (padded_left len k tail)=LC (N.to_nat len) (RN.value k) (PT.denote tail).
Proof.
  intros H; apply low_spec in H; destruct H as [Hw Hv].
  unfold padded_left; rewrite put_left_spec,left_words_spec,Hw,Hv; reflexivity.
Qed.

Definition state := (bool*PT.t*PT.t)%type.
Definition physical_config (s:state) := let '(left,l,r):=s in
  if left then PT.denote l <| PT.denote r else PT.denote l |> PT.denote r.
Definition right_on_tapes l r : option state := let '(ds,tail):=scanLeft l in
  let len:=RN.width ds in match right_step len ds r with
  | None=>None
  | Some (left,k',r')=>Some (left,padded_left len k' tail,r') end.
Lemma right_on_tapes_spec l r s:
  right_on_tapes l r=Some s ->
  physical_config (false,l,r) -[tm]->* physical_config s.
Proof.
  unfold right_on_tapes; intros E; pose proof (scanLeft_spec l) as Hl.
  destruct (scanLeft l) as [ds tail]; cbn zeta in Hl.
  destruct (right_step (RN.width ds) ds r) as [[[left k'] r']|] eqn:Hstep; inverts E.
  destruct (right_step_spec _ _ _ _ _ _ (PT.denote tail) Hstep) as [Hb H].
  unfold physical_config; rewrite Hl,left_words_spec.
  destruct left; unfold config in H; rewrite padded_left_spec by exact Hb; exact H.
Qed.

Definition left_on_tapes l r : option state := let '(ds,tail):=scanLeft l in
  let len:=RN.width ds in match RN.pred ds with
  | Some k=>Some (false,padded_left len k tail,r)
  | None=>match PT.drop_prefix [1;0] tail with
    | None=>None
    | Some base=>Some (false,PT.push (0,1,1) len (PT.cons 1 base),PT.cons 1 r) end end.
Lemma left_on_tapes_spec l r s:
  left_on_tapes l r=Some s ->
  physical_config (true,l,r) -[tm]->* physical_config s.
Proof.
  unfold left_on_tapes; intros E; pose proof (scanLeft_spec l) as Hl.
  destruct (scanLeft l) as [ds tail]; cbn zeta in Hl.
  pose proof (RN.pred_spec ds) as Hp; pose proof (RN.value_bound ds) as Hb.
  destruct (RN.pred ds) as [k|].
  - inverts E; unfold physical_config; rewrite Hl,left_words_spec,padded_left_spec by lia.
    rewrite Hp; apply progress_evstep,LC_Inc; lia.
  - destruct (PT.drop_prefix [1;0] tail) as [base|] eqn:Ht; inverts E.
    unfold physical_config; rewrite Hl,left_words_spec,Hp; unfold LC; rewrite BinDec_O.
    rewrite (PT.drop_prefix_spec _ _ _ Ht),PT.push_spec,!PT.cons_spec.
    apply progress_evstep,LOv_finite.
Qed.

Definition split_boundary r : option (N*N*PT.t) :=
  let '(h,r0):=PT.take_word (1,0,0) r in match PT.drop_prefix [1] r0 with
  | None=>None | Some r1=>let '(m,r2):=PT.take_word (1,0,0) r1 in Some (h,m,r2) end.
Lemma split_boundary_spec r h m tail:
  split_boundary r=Some (h,m,tail) ->
  PT.denote r=rd1^^(N.to_nat h) *> [1] *> rd1^^(N.to_nat m) *> PT.denote tail.
Proof.
  unfold split_boundary; intros E; pose proof (PT.take_word_spec (1,0,0) r) as Hh.
  destruct (PT.take_word (1,0,0) r) as [h0 r0].
  destruct (PT.drop_prefix [1] r0) as [r1|] eqn:H1; try discriminate.
  pose proof (PT.take_word_spec (1,0,0) r1) as Hm.
  destruct (PT.take_word (1,0,0) r1) as [m0 r2]; inverts E.
  rewrite Hh,(PT.drop_prefix_spec _ _ _ H1),Hm; reflexivity.
Qed.

Inductive edge_rule := E11 | E01 | E01111.
Definition edge_pattern rule : list Sym := match rule with
  | E11=>[1;1] | E01=>[0;1;0;0] | E01111=>[0;1;1;1;1;0;0;0;0;0;0] end.
Definition edge_base n l := PT.push (1,1,1) n (PT.push (0,1,1) 1 l).
Definition edge_result rule n l r : state := let base:=edge_base n l in match rule with
  | E11=>(false,base,r)
  | E01=>(true,base,PT.prepend [0;1] r)
  | E01111=>(true,PT.push (1,1,1) 2 (PT.push (0,1,1) 1 base),r) end.
Lemma edge_rule_spec rule h m l r:
  (PT.denote l |> rd1^^(N.to_nat h) *> [1] *> rd1^^(N.to_nat m) *>
    edge_pattern rule *> PT.denote r) -[tm]->*
  physical_config (edge_result rule (h+m)%N l r).
Proof.
  destruct rule; unfold edge_result,edge_base,physical_config,edge_pattern;
    rewrite !PT.push_spec,?PT.prepend_spec,N2Nat.inj_add;
    apply progress_evstep.
  - apply ROv11.
  - rewrite Nat.add_comm; apply ROv01.
  - rewrite Nat.add_comm; apply ROv01111.
Qed.
Fixpoint try_edges rules h m l r : option state := match rules with
  | []=>None | rule::rules=>match PT.drop_prefix (edge_pattern rule) r with
    | Some tail=>Some (edge_result rule (h+m)%N l tail)
    | None=>try_edges rules h m l r end end.
Lemma try_edges_spec rules h m l r s:
  try_edges rules h m l r=Some s ->
  (PT.denote l |> rd1^^(N.to_nat h) *> [1] *> rd1^^(N.to_nat m) *> PT.denote r)
    -[tm]->* physical_config s.
Proof.
  induction rules as [|rule rules IH]; cbn [try_edges]; intros E; [discriminate|].
  destruct (PT.drop_prefix (edge_pattern rule) r) as [tail|] eqn:H.
  - inverts E; rewrite (PT.drop_prefix_spec _ _ _ H); apply edge_rule_spec.
  - apply IH,E.
Qed.

Definition short_ones (r:PT.t) : option N := match r with
  | []=>Some 0%N
  | [(w,n)]=>if N.eqb n 1 then match w with
    | (S1,S0,S0)=>Some 1%N | (S1,S1,S0)=>Some 2%N | _=>None end else None
  | _=>None end.
Lemma short_ones_spec r n:
  short_ones r=Some n -> PT.denote r=[1]^^(N.to_nat n) *> 0inf.
Proof.
  destruct r as [|[[[a b] c] k] r]; cbn [short_ones]; intros E.
  - inverts E; reflexivity.
  - destruct r; try discriminate; destruct (N.eqb k 1) eqn:H; try discriminate.
    apply N.eqb_eq in H; subst k; destruct a,b,c; inverts E; solve_const0_eq.
Qed.
Definition all_ones r := let '(n,tail):=PT.take_word (1,1,1) r in
  match short_ones tail with Some m=>Some (n*3+m)%N | None=>None end.
Lemma all_ones_spec r n:
  all_ones r=Some n -> PT.denote r=[1]^^(N.to_nat n) *> 0inf.
Proof.
  unfold all_ones; intros E; pose proof (PT.take_word_spec (1,1,1) r) as H.
  destruct (PT.take_word (1,1,1) r) as [k tail].
  destruct (short_ones tail) as [m|] eqn:Hm; inverts E.
  rewrite H,(short_ones_spec _ _ Hm),N2Nat.inj_add,N2Nat.inj_mul,lpow_add,Str_app_assoc.
  rewrite (lpow_mul [1] (N.to_nat k) (N.to_nat 3)); reflexivity.
Qed.
Definition restart_result h m q l : state :=
  (true,PT.push (0,1,1) 2 (PT.cons 1
    (PT.repeat_symbol 0 (q-4)%N (PT.prepend [1;1] (edge_base (h+m)%N l)))),
    PT.push (1,0,0) 1 []).
Definition try_restart h m l r : option state := match PT.drop_prefix [0] r with
  | None=>None | Some tail=>match all_ones tail with
    | None=>None | Some q=>if N.leb 4 q then Some (restart_result h m q l) else None end end.
Lemma try_restart_spec h m l r s:
  try_restart h m l r=Some s ->
  (PT.denote l |> rd1^^(N.to_nat h) *> [1] *> rd1^^(N.to_nat m) *> PT.denote r)
    -[tm]->* physical_config s.
Proof.
  unfold try_restart; intros E; destruct (PT.drop_prefix [0] r) as [tail|] eqn:Hz; try discriminate.
  destruct (all_ones tail) as [q|] eqn:Hq; try discriminate.
  destruct (N.leb 4 q) eqn:Hb; inverts E; apply N.leb_le in Hb.
  rewrite (PT.drop_prefix_spec _ _ _ Hz),(all_ones_spec _ _ Hq).
  unfold restart_result,physical_config,edge_base.
  rewrite !PT.push_spec,PT.cons_spec,PT.repeat_symbol_spec,PT.prepend_spec,!PT.push_spec,N2Nat.inj_add.
  replace (N.to_nat q) with (4+N.to_nat (q-4)) by lia.
  rewrite (Nat.add_comm (N.to_nat h) (N.to_nat m)); apply progress_evstep,Prepare_restart.
Qed.

Definition boundary l r : option state := let '(n,tail):=PT.take_word (1,1,1) r in
  if N.eqb n 0 then match split_boundary r with
  | None=>None | Some (h,m,tail)=>match try_edges [E11;E01;E01111] h m l tail with
    | Some s=>Some s | None=>try_restart h m l tail end end
  else Some (false,PT.push (0,1,1) n l,tail).
Lemma boundary_spec l r s:
  boundary l r=Some s -> physical_config (false,l,r) -[tm]->* physical_config s.
Proof.
  unfold boundary; intros E; pose proof (PT.take_word_spec (1,1,1) r) as Hn.
  destruct (PT.take_word (1,1,1) r) as [n tail].
  destruct (N.eqb n 0).
  - destruct (split_boundary r) as [[[h m] rs]|] eqn:Hsplit; try discriminate.
    unfold physical_config at 1; rewrite (split_boundary_spec _ _ _ _ Hsplit).
    destruct (try_edges [E11;E01;E01111] h m l rs) as [s'|] eqn:He.
    + inverts E; eapply try_edges_spec,He.
    + apply try_restart_spec,E.
  - inverts E; unfold physical_config; rewrite Hn,PT.push_spec; apply RSkip.
Qed.

Definition step (s:state) : option state := let '(left,l,r):=s in
  if left then left_on_tapes l r else match right_on_tapes l r with
  | Some s'=>Some s' | None=>boundary l r end.
Lemma step_spec s s': step s=Some s' -> physical_config s -[tm]->* physical_config s'.
Proof.
  destruct s as [[left l] r]; cbn [step]; destruct left; intros E.
  - apply left_on_tapes_spec,E.
  - destruct (right_on_tapes l r) as [rs|] eqn:H.
    + inverts E; apply right_on_tapes_spec,H.
    + apply boundary_spec,E.
Qed.
Definition halted (s:state) := let '(left,l,r):=s in if left then false else
  match split_boundary r with
  | None=>false | Some (h,m,tail)=>match PT.drop_prefix [1;0;1] tail with
    | Some _=>true
    | None=>match PT.drop_prefix ([0]++[1]^^7++[0;0;0;1;0;0;0]) tail with
      | Some _=>true | None=>false end end end.
Lemma halted_spec s: halted s=true -> halts tm (physical_config s).
Proof.
  destruct s as [[left l] r]; cbn [halted]; destruct left; intros E; [discriminate|].
  destruct (split_boundary r) as [[[h m] tail]|] eqn:Hs; try discriminate.
  unfold physical_config; rewrite (split_boundary_spec _ _ _ _ Hs).
  destruct (PT.drop_prefix [1;0;1] tail) as [rs|] eqn:H.
  - rewrite (PT.drop_prefix_spec _ _ _ H); apply Bad_tail.
  - destruct (PT.drop_prefix ([0]++[1]^^7++[0;0;0;1;0;0;0]) tail) as [rs|] eqn:Hb; try discriminate.
    rewrite (PT.drop_prefix_spec _ _ _ Hb),!Str_app_assoc; apply Bad_restart.
Qed.
Fixpoint haltsb fuel s := match fuel with
  | O=>halted s | S fuel=>match step s with Some s'=>haltsb fuel s' | None=>halted s end end.
Lemma haltsb_spec fuel s: haltsb fuel s=true -> halts tm (physical_config s).
Proof.
  revert s; induction fuel; intros s E; cbn [haltsb] in E.
  - apply halted_spec,E.
  - destruct (step s) as [s'|] eqn:Hstep.
    + eapply halts_evstep; [apply IHfuel,E|apply step_spec,Hstep].
    + apply halted_spec,E.
Qed.
Definition seed : state := (true,[((0,1,1),2%N);((1,0,0),1%N)],[((1,0,0),1%N)]).
Lemma seed_spec: c0 -[tm]->* physical_config seed.
Proof.
  unfold seed,physical_config; cbn [PT.denote PT.bits].
  change (N.to_nat 2) with 2%nat; change (N.to_nat 1) with 1%nat.
  cbn [lpow Str_app app]; repeat rewrite <-const_unfold.
  pose proof init as H; cbn [lpow Str_app app] in H; repeat rewrite <-const_unfold in H; exact H.
Qed.

Theorem halt: halts tm c0.
Proof.
  eapply halts_evstep.
  - apply (haltsb_spec 40000 seed). native_compute; reflexivity.
  - apply seed_spec.
Qed.
End TM4.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull BinaryCounter_v2 SimplTape ES_v2.
Require Import String ZifyNat Lia PeanoNat NArith.

(* SOC33_Ex17.TM17 *)
Module TM112.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String ZifyNat Lia PeanoNat NArith.


(* Work directly in the archived mirror direction. *)
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Definition tm := Eval compute in (TM_from_str "1LB1LE_1LC0RA_0LD0LC_1RE0RB_1RF---_1LC1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <a| r" := (l <{{D}} [0;1;1;0;0;0;0] *> r) (at level 30).
Notation "l <b| r" := (l <{{D}} [0;1;1;1;0;0;0] *> r) (at level 30).
Notation "l <c| r" := (l <{{D}} [0;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LInc_a l r n:
  l <* ld0 <* ld1^^n <a| r -->+
  l <* ld1 <* ld0^^n <b| r.
Proof. es. Qed.

Lemma LInc_b l r n:
  l <* ld0 <* ld1^^n <b| r -->+
  l <* ld1 <* ld0^^n <c| r.
Proof. es. Qed.

Lemma LInc_c l r n:
  l <* ld0 <* ld1^^n <c| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <a| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_a r n:
  ldh <* ld1^^n <a| r -->+
  ldh <* ld0^^n <c| [0] *> r.
Proof. es. Qed.

Notation "l |2> r" := (l <* [1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LOv_c r n:
  ldh <* ld1^^(1+n) <c| r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |2> r.
Proof. es. Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^n <* ld1 |2> r.
Proof. es. Qed.

Lemma ROv'_1 l r n:
  l <* ld0 <* ld1^^n |2> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |2> r.
Proof. es. Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l |> [0] *> r.
Proof. es. Qed.

Lemma init_word:
  c0 -->* ldh <* ld0^^6 <* ld1^^4 |2> rd0^^2 *> rd1 *> rd0^^2 *> rd1 *> 0inf.
Proof. esx. Qed.


(* Numeric macros: each ordinary right increment costs three left decrements. *)
Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0] h n ([1;0;0] *> r).

Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
  solve[lia|nia|flia].
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first[follow10 HX|follow100 HX];
  st; repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,MC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.
Ltac exact_word H := let HX:=fresh "HX" in pose proof H as HX; gen HX;
  st; simpl_rotate; intro HX; first[exact HX|apply progress_evstep; exact HX].
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_split len k: 1+k<2^len -> exists l n,
  LC len (1+k)=l <* ld0 <* ld1^^n /\ LC len k=l <* ld1 <* ld0^^n.
Proof.
  unfold LC,BinDec; intros HK.
  assert (HE: Pos.of_nat (2^(len+1)-1-k)=Pos.succ (Pos.of_nat (2^(len+1)-1-(1+k)))) by arith.
  rewrite HE; eapply not_full_Inc; rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len); [rewrite pow2'_spec'; arith|arith].
Qed.
Lemma LC_a len k r: 1+k<2^len -> LC len (1+k) <a| r -->+ LC len k <b| r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  rewrite HA,HB; exact_word (LInc_a l r n).
Qed.
Lemma LC_b len k r: 1+k<2^len -> LC len (1+k) <b| r -->+ LC len k <c| r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  rewrite HA,HB; exact_word (LInc_b l r n).
Qed.
Lemma LC_c len k r: 1+k<2^len -> LC len (1+k) <c| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc_c. Qed.
Lemma LC_three len k r: k+3<2^len -> LC len (k+3) <a| r -->+ LC len k |> r.
Proof.
  intros HK; eapply progress_evstep_trans;
    [applys_eq (LC_a len (k+2)); [flia|lia]|].
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_b len (1+k)); [flia|lia]|].
  apply progress_evstep,LC_c; lia.
Qed.
Lemma RC_Inc l m: l |> RC m -->+ l <a| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l h n r: 1+n<2^(h+1) -> l |> MC h (1+n) r -->+ l <a| MC h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma MC_Incs len k h n r: k+n*3<2^len -> n<2^(h+1) ->
  LC len (k+n*3) |> MC h n r -->* LC len k |> MC h 0 r.
Proof.
  induction n; intros HK HN; [finish|].
  follow_inc MC_Inc.
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_three len (k+n*3)); [flia|lia]|].
  apply IHn; lia.
Qed.
Lemma RC_Incs len k n m: k+n*3<2^len ->
  LC len (k+n*3) |> RC m -->* LC len k |> RC (m+n).
Proof.
  gen m; induction n; intros m HK; [applys_eq evstep_refl; flia|].
  follow_inc RC_Inc.
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_three len (k+n*3)); [flia|lia]|].
  applys_eq (IHn (1+m)); [flia|lia].
Qed.
Lemma RC_finish_a len q: q*3<2^len ->
  LC len (q*3) |> 0inf -->+ LC len 0 <a| RC (q+1).
Proof.
  intros HK; change (LC len (q*3) |> RC 0 -->+ LC len 0 <a| RC (q+1)).
  eapply evstep_progress_trans; [applys_eq (RC_Incs len 0 q 0); try solve[flia]; lia|].
  applys_eq RC_Inc; flia.
Qed.
Lemma RC_finish_c len q: q*3+2<2^len ->
  LC len (q*3+2) |> 0inf -->+ LC len 0 <c| RC (q+1).
Proof.
  intros HK; change (LC len (q*3+2) |> RC 0 -->+ LC len 0 <c| RC (q+1)).
  eapply evstep_progress_trans; [applys_eq (RC_Incs len 2 q 0); [flia|lia]|].
  follow10 RC_Inc; follow_inc LC_a.
  apply progress_evstep; applys_eq LC_b; [flia|lia].
Qed.

Lemma U_odd_word len k r: 1+k<2^len ->
  LC len (1+k) |2> rd1 *> r -->+ LC (len+1) (k*2+1) |2> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  unfold LC; rw_Bin; try solve[arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite HA,HB; exact_word (ROv'_1 l r n).
Qed.
Lemma U_odd len k m: 1+k<2^len ->
  LC len (1+k) |2> RC (m*2+1) -->+ LC (len+1) (k*2+1) |2> RC m.
Proof. intros HK; unfold RC; rw_Bin; apply U_odd_word,HK. Qed.

Lemma MC_start h r: [0] *> rd0^^h *> rd1 *> r = MC h (2^(h+1)-1) r.
Proof. unfold MC; rw_Bin; cbv [d0 List.length List.repeat]; st; simpl_rotate; reflexivity. Qed.
Lemma MC_Ov len k h r: k<2^len ->
  LC len k |> MC h 0 r -->+
  LC (len+h+2) ((k*2+1)*2^(h+1)-2) |2> r.
Proof.
  replace (len+h+2) with (len+1+h+1) by lia.
  replace ((k*2+1)*2^(h+1)-2) with (((k*2+1)*2^h-1)*2) by arith.
  intros HK; unfold LC,MC; rw_Bin; try solve[arith]; exact_word (ROv (LC len k) r h).
Qed.
Lemma R_entry len k h r: k+(2^(h+1)-1)*3<2^len ->
  LC len (k+(2^(h+1)-1)*3) |> [0] *> rd0^^h *> rd1 *> r -->+
  LC (len+h+2) ((k*2+1)*2^(h+1)-2) |2> r.
Proof.
  intros HK; rewrite MC_start.
  eapply evstep_progress_trans; [apply MC_Incs; try lia; arith|].
  apply MC_Ov; lia.
Qed.
Lemma U_even len k h m: k+(2^(h+1)-1)*3<2^len ->
  LC len (k+(2^(h+1)-1)*3) |2> RC ((m*2+1)*2^(h+1)) -->+
  LC (len+h+2) ((k*2+1)*2^(h+1)-2) |2> RC m.
Proof.
  intros HK; unfold RC; rw_Bin; cbv [d0 List.length List.repeat].
  replace (h+1) with (1+h) by lia; cbn [lpow]; simpl_tape.
  follow10 ROv'_0; apply progress_evstep.
  replace (2^h+(2^h+0)) with (2^(h+1)) by arith.
  apply R_entry; exact HK.
Qed.

Lemma LC_Ov_a len r: LC len 0 <a| r -->+ LC len (2^len-1) <c| [0] *> r.
Proof. solve_rule LOv_a. Qed.
Lemma LC_Ov_c len r: LC (len+1) 0 <c| r -->+ LC (len+2) (2^(len+2)-3) |2> r.
Proof.
  replace (len+2) with (len+1+1) by lia.
  replace (2^(len+1+1)-3) with ((2^len-1)*2*2+1) by arith.
  unfold LC; rw_Bin; try solve[arith]; exact_word (LOv_c r len).
Qed.
Lemma F_a len m: 3<=len -> LC len 0 <a| RC (m*2+1) -->+
  LC (len+2) (2^(len+2)-20) |2> RC m.
Proof.
  intros HL; assert (HP: 2^3<=2^len) by (apply Nat.pow_le_mono_r; lia).
  follow10 LC_Ov_a.
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_c len (2^len-2)); [flia|lia]|].
  unfold RC; rw_Bin.
  apply progress_evstep; applys_eq (R_entry len (2^len-5) 0); try solve[flia|arith].
  cbn [lpow]; arith.
Qed.
Lemma F_c len m: 1<=len -> LC len 0 <c| RC (m*2+1) -->+
  LC (len+2) (2^(len+2)-7) |2> RC m.
Proof.
  intros HL; destruct len; [lia|]; replace (S len) with (len+1) in * by lia.
  follow10 LC_Ov_c.
  apply progress_evstep; applys_eq (U_odd (len+2) (2^(len+2)-4) m);
    try solve[flia]; arith.
Qed.

Close Scope sym.
(* Binary strings beginning with 10, plus the empty string. *)
Inductive Top: nat->nat->Prop :=
| Top_Z: Top 0 0
| Top_2: Top 2 2
| Top_E j m: Top j m -> 0<m -> Top (j+1) (m*2)
| Top_I j m: Top j m -> 0<m -> Top (j+1) (m*2+1).
Lemma Top_zero j: Top j 0 -> j=0.
Proof. intros H; inverts H; lia. Qed.
Lemma Top_build i m: 2^(i+1)<=m<2^i*3 -> Top (i+2) m.
Proof.
  gen m; induction i; intros m HM.
  - replace m with 2 by (cbn in HM; lia); constructor.
  - destruct (divmod2 m) as [m' a ->|m' a ->].
    + applys_eq (Top_E (i+2) a); [flia|apply IHi; arith|arith].
    + applys_eq (Top_I (i+2) a); [flia|apply IHi; arith|arith].
Qed.
Lemma Top_odd j m: Top j (m*2+1) -> exists i, Top i m /\ j=i+1 /\ 0<m.
Proof.
  intros H; inverts H; try lia.
  match goal with HN: Top _ _ |- _ =>
    eexists; split; [applys_eq HN; flia|split; lia] end.
Qed.
Lemma Top_cut h j m: Top j ((m*2+1)*2^(h+1)) ->
  exists i, Top i m /\ j=i+h+2.
Proof.
  gen j; induction h; intros j H.
  - replace ((m*2+1)*2^(0+1)) with ((m*2+1)*2) in H by lia.
    inverts H; try lia.
    + replace m with 0 by lia; exists 0; split; [constructor|lia].
    + match goal with HN: Top ?j0 _ |- _ =>
        assert (HT: Top j0 (m*2+1)) by (applys_eq HN; flia);
        destruct (Top_odd _ _ HT) as [i [HI [HJ HM]]];
        exists i; split; [exact HI|lia] end.
  - replace ((m*2+1)*2^(S h+1)) with (((m*2+1)*2^(h+1))*2) in H by arith.
    inverts H; try solve[arith].
    match goal with HN: Top ?j0 _ |- _ =>
      assert (HT: Top j0 ((m*2+1)*2^(h+1))) by (applys_eq HN; flia);
      destruct (IHh _ HT) as [i [HI HJ]];
      exists i; split; [exact HI|lia] end.
Qed.

Lemma pow2_mod3 n: 2^n mod 3<>0.
Proof. induction n; cbn [Nat.pow] in *; lia. Qed.
Lemma pow4_mod3 n: 4^n mod 3=1.
Proof. induction n; cbn [Nat.pow] in *; lia. Qed.
Lemma pow2_even_mod3 n: n mod 2=0 -> 2^n mod 3=1.
Proof.
  intros H; divmod2_cases n; [|lia].
  rewrite Nat.mul_comm,Nat.pow_mul_r; apply pow4_mod3.
Qed.
Lemma mod3_transfer k s: k mod 3<>1 -> s mod 3<>0 -> 2<=s ->
  ((k*2+1)*s-2) mod 3<>1.
Proof.
  intros HK HS Hs; assert (HA: (k*2+1) mod 3<>0) by lia.
  assert (HP: ((k*2+1)*s) mod 3<>0).
  { rewrite Nat.Div0.mul_mod.
    pose proof (Nat.mod_upper_bound (k*2+1) 3); pose proof (Nat.mod_upper_bound s 3).
    destruct ((k*2+1) mod 3) as [|[|[|a]]]; try lia;
      destruct (s mod 3) as [|[|[|b]]]; cbn; lia. }
  nia.
Qed.

Definition FB len m := 8<=len /\ len mod 2=0 /\ m mod 2=1 /\ 2^len<m*4 /\ m*3<2^len.
Definition UB len k m D := 4<=len /\ k<2^len /\ 2^len=k+D /\
  5<=D /\ (D+m*3)*4<=2^len /\ k mod 3<>1.
Ltac bounds := intros; unfold FB,UB in *;
  repeat match goal with H:_ /\ _ |- _ => destruct H end;
  repeat split; arith.
Lemma FB_top len m: FB len (m*2+1) -> Top (len-2) m.
Proof.
  intros [HL [HE [HM [HA HB]]]]; destruct len as [|[|[|[|i]]]]; try lia.
  replace (S (S (S (S i)))-2) with (i+2) by lia.
  apply Top_build; arith.
Qed.
Lemma FB_cap len m: FB len m -> 2^len mod 3=1 /\ 2^8<=2^len.
Proof.
  intros [HL [HE H]]; split.
  - apply pow2_even_mod3,HE.
  - apply Nat.pow_le_mono_r; lia.
Qed.
Lemma FB_a len m: FB len (m*2+1) -> UB (len+2) (2^(len+2)-20) m 20.
Proof. intros H; pose proof (FB_cap _ _ H); bounds. Qed.
Lemma FB_c len m: FB len (m*2+1) -> UB (len+2) (2^(len+2)-7) m 7.
Proof. intros H; pose proof (FB_cap _ _ H); bounds. Qed.
Lemma UB_odd len k m D: UB len (1+k) (m*2+1) D ->
  UB (len+1) (k*2+1) m (D*2+1).
Proof. bounds. Qed.
Lemma UB_even len k h m D: UB len (k+(2^(h+1)-1)*3) ((m*2+1)*2^(h+1)) D ->
  UB (len+h+2) ((k*2+1)*2^(h+1)-2) m ((D*2+2^(h+1)*6-7)*2^(h+1)+2).
Proof.
  intros H; assert (HM: ((k*2+1)*2^(h+1)-2) mod 3<>1).
  { apply mod3_transfer; [unfold UB in H; repeat destruct H as [? H]; lia|apply pow2_mod3|arith]. }
  bounds.
Qed.
Lemma UB_budget len k m D: UB len k m D -> m*3<=k /\ 0<k.
Proof. bounds. Qed.
Lemma UB_zero_a len q D: UB len (q*6) 0 D -> 8<=len -> len mod 2=0 ->
  FB len (q*2+1).
Proof. bounds. Qed.
Lemma UB_zero_c len q D: UB len (q*6+2) 0 D -> 8<=len -> len mod 2=0 ->
  FB len (q*2+1).
Proof. bounds. Qed.

Open Scope sym.
Open Scope nat_scope.

Inductive P: Q*tape->Prop :=
| PA len m: FB len m -> P (LC len 0 <a| RC m)
| PC len m: FB len m -> P (LC len 0 <c| RC m)
| PU len k m j D: Top j m -> UB len k m D ->
    (len+j) mod 2=0 -> 8<=len+j -> (m=0%nat -> k mod 2=0) ->
    P (LC len k |2> RC m).

Lemma A_step len m: FB len m -> exists c, LC len 0 <a| RC m -->+ c /\ P c.
Proof.
  intros H; pose proof H as [HL [HE [HM [HA HB]]]].
  destruct (divmod2 m) as [m' a ->|m' a ->]; [lia|].
  eexists; split; [apply F_a; lia|].
  eapply PU with (j:=len-2) (D:=20);
    [apply FB_top,H|apply FB_a,H|lia|lia|].
  intros ->; arith.
Qed.
Lemma C_step len m: FB len m -> exists c, LC len 0 <c| RC m -->+ c /\ P c.
Proof.
  intros H; pose proof H as [HL [HE [HM [HA HB]]]].
  destruct (divmod2 m) as [m' a ->|m' a ->]; [lia|].
  eexists; split; [apply F_c; lia|].
  eapply PU with (j:=len-2) (D:=7);
    [apply FB_top,H|apply FB_c,H|lia|lia|].
  intros ->; arith.
Qed.

Lemma U_zero_R l: l |2> 0inf -->+ l |> 0inf.
Proof. follow_rule (ROv'_0 l 0inf). Qed.

Lemma U_zero len k j D: Top j 0 -> UB len k 0 D ->
  (len+j) mod 2=0 -> 8<=len+j -> k mod 2=0 ->
  exists c, LC len k |2> RC 0 -->+ c /\ P c.
Proof.
  intros HT HB HE Hlen HK; apply Top_zero in HT; subst j.
  pose proof HB as [HL [HC [HD [HD0 [HB0 HM]]]]].
  pose proof (Nat.Div0.div_mod k 6) as HQ.
  pose proof (Nat.mod_upper_bound k 6) as HR.
  remember (k mod 6) as r; destruct r as [|[|[|[|[|[|r]]]]]]; try lia.
  - replace k with ((k/6*2)*3) by lia.
    exists (LC len 0 <a| RC (k/6*2+1)); split.
    + change (LC len (k/6*2*3) |2> 0inf -->+ LC len 0 <a| RC (k/6*2+1)).
      follow10 U_zero_R.
      apply progress_evstep,RC_finish_a; lia.
    + apply PA; eapply UB_zero_a; [applys_eq HB; flia|lia|lia].
  - replace k with ((k/6*2)*3+2) by lia.
    exists (LC len 0 <c| RC (k/6*2+1)); split.
    + change (LC len (k/6*2*3+2) |2> 0inf -->+ LC len 0 <c| RC (k/6*2+1)).
      follow10 U_zero_R.
      apply progress_evstep,RC_finish_c; lia.
    + apply PC; eapply UB_zero_c; [applys_eq HB; flia|lia|lia].
Qed.

Lemma U_step len k m j D: Top j m -> UB len k m D ->
  (len+j) mod 2=0 -> 8<=len+j -> (m=0%nat -> k mod 2=0) ->
  exists c, LC len k |2> RC m -->+ c /\ P c.
Proof.
  intros HT HB HE Hlen Hzero.
  destruct (Nat.eq_dec m 0%nat) as [->|HM]; [eapply U_zero; eauto|].
  pose proof (UB_budget _ _ _ _ HB) as [HK HK0].
  pose proof HB as [HL [HC Hrest]].
  destruct (divmod2 m) as [m' a ->|m' a ->].
  - lowbit_cases a; [lia|].
    replace ((x*2+1)*2^i*2) with ((x*2+1)*2^(i+1)) in * by arith.
    destruct (Top_cut i j x HT) as [j' [HT' ->]].
    set (q:=k-(2^(i+1)-1)*3).
    assert (Hq: k=q+(2^(i+1)-1)*3) by (unfold q; arith).
    exists (LC (len+i+2) ((q*2+1)*2^(i+1)-2) |2> RC x); split.
    + applys_eq (U_even len q i x); [flia|lia].
    + eapply PU; [exact HT'| |lia|lia|].
      * apply (UB_even len q i x D); applys_eq HB; flia.
      * intros; arith.
  - destruct k; [lia|].
    destruct (Top_odd j a HT) as [j' [HT' [-> Ha]]].
    eexists; split; [apply U_odd; lia|].
    eapply PU; [exact HT'|apply UB_odd,HB|lia|lia|intros; lia].
Qed.

Lemma closed c: P c -> exists c', c -->+ c' /\ P c'.
Proof.
  intros H; destruct H.
  - apply A_step; assumption.
  - apply C_step; assumption.
  - eapply U_step; eassumption.
Qed.

Lemma init_counter: c0 -->* LC 10 1008 |2> RC 36.
Proof. applys_eq init_word; vm_compute; reflexivity. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  eapply progress_nonhalt_cond with (C:=fun c=>c) (P:=P); [apply closed|].
  eapply PU with (j:=6) (D:=16).
  - applys_eq (Top_build 4 36); try solve[flia]; cbn; lia.
  - unfold UB; cbn; lia.
  - cbn; lia.
  - lia.
  - lia.
Qed.

End TM112.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull BinaryCounter_v2 SimplTape ES_v2 Eqb.
Require Import String ZifyNat Lia PeanoNat NArith List Wf_nat.

(* SOC33_Ex19.TM19 *)
Module TM113.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.Eqb.
Import String ZifyNat Lia PeanoNat NArith List Wf_nat.


Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1RD1RA_1LB---_1LF0RC_1RD0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;1;1;1;1;0;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;1;1;1;0;1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv r n:
  ldh <* ld1^^(1+n) <| r -->+
  ldh <* ld0^^n |> [1;1;0;0] *> r.
Proof. es. Qed.


Notation "l |C> r" := (l {{C}}> r) (at level 30).

Lemma C1 l r: l |C> rd1 *> r -->+ l <* ld1 |C> r.
Proof. es. Qed.
Lemma R_C l r n:
  l |> rd1^^n *> [1;1;0;0] *> r -->+
  l <* ld0^^2 <* ld1^^(n+2) <* ld0 <* ld1 |C> r.
Proof. es. Qed.
Lemma C0_even0 l r n:
  l <* ld0 <* ld1^^(n+2) |C> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1^^2 <* ld0 |C> r.
Proof. es. Qed.
Lemma C0_even2 l r n:
  l <* ld0 <* ld1^^n <* ld0 <* ld1 |C> rd0 *> r -->+
  l <* ld1 <* ld0^^(n+1) <* ld1 <* ld0 |C> r.
Proof. es. Qed.

Lemma C001 l r n:
  l <* ld0 <* ld1^^n |C> [0;0;1] *> r -->+
  l <* ld1 <* ld0^^(n+1) |C> r.
Proof. es. Qed.
Lemma C_edge l r n:
  l <* ld0^^2 <* ld1^^(n+1) <* ld0 |C> rd0 *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma R1 l r n:
  l |> rd1^^n *> [1] *> r -->+
  l <* ld0^^2 <* ld1^^(n+2) <* ld0 |C> r.
Proof. es. Qed.
Lemma C0_prepare l r n h:
  l <* ld0 <* ld1^^(n+1) <* ld0 <* ld1^^(h+1) <* ld0 |C> rd0 *> r -->+
  l <* ld1 <* ld0^^(n+2) <* ld1 |C> rd0^^(h+1) *> [0;0;1] *> r.
Proof. es. Qed.

Lemma init_word:
  c0 -->* ldh <* ld1^^3 <| rd0 *> rd1^^2 *> 0inf.
Proof. esx. Qed.


Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec rd0 rd1 h n ([1] *> r).

Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
  solve[lia|nia|flia].
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first[follow10 HX|follow100 HX];
  st; repeat (simpl_rotate || simpl_tape); finish.
Ltac exact_word H := let HX:=fresh "HX" in pose proof H as HX; gen HX;
  st; simpl_rotate; intro HX; first[exact HX|apply progress_evstep; exact HX].
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_split len k: 1+k<2^len -> exists l n,
  LC len (1+k)=l <* ld0 <* ld1^^n /\ LC len k=l <* ld1 <* ld0^^n.
Proof.
  unfold LC,BinDec; intros HK.
  assert (HE: Pos.of_nat (2^(len+1)-1-k)=Pos.succ (Pos.of_nat (2^(len+1)-1-(1+k)))) by arith.
  rewrite HE; eapply not_full_Inc; rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len); [rewrite pow2'_spec'; arith|arith].
Qed.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc l m: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l h n r: 1+n<2^h -> l |> MC h (1+n) r -->+ l <| MC h n r.
Proof. intros; apply RBinDec_spec; try lia; follow_rule RInc. Qed.

Lemma MC_Incs len k h n r: k+n<2^len -> n<2^h ->
  LC len (k+n) |> MC h n r -->* LC len k |> MC h 0 r.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc MC_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma RC_Incs len k m: k<2^len ->
  LC len k <| RC m -->* LC len 0 <| RC (m+k).
Proof.
  gen m; induction k; intros m HK; [applys_eq evstep_refl; flia|].
  follow_inc LC_Inc; follow_inc RC_Inc.
  applys_eq IHk; [flia|lia].
Qed.

Lemma C_one len k r: k<2^len ->
  LC len k |C> rd1 *> r -->+ LC (len+1) (k*2) |C> r.
Proof.
  intros HK; unfold LC; rw_Bin; try solve[arith]; exact_word (C1 (LC len k) r).
Qed.
Lemma C_001 len k r: 1+k<2^len ->
  LC len (1+k) |C> [0;0;1] *> r -->+ LC (len+1) (k*2+1) |C> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  unfold LC; rw_Bin; try solve[arith]; unfold LC in HA,HB.
  rewrite HA,HB; exact_word (C001 l r n).
Qed.
Lemma C_even0 len k r: 1+k<2^len ->
  LC (len+2) ((1+k)*4) |C> rd0 *> r -->+
  LC (len+3) (k*8+1) |C> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  replace ((1+k)*4) with ((1+k)*2^2) by (cbn; lia).
  replace (len+3) with (len+2+1) by lia.
  replace (k*8+1) with ((k*2^2)*2+1) by (cbn; lia).
  unfold LC; rw_Bin; try solve[arith].
  unfold LC in HA,HB; rewrite HA,HB; exact_word (C0_even0 l r n).
Qed.
Lemma C_even2 len k r: 1+k<2^len ->
  LC (len+2) ((1+k)*4+2) |C> rd0 *> r -->+
  LC (len+3) (k*8+5) |C> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  replace (len+2) with (len+1+1) by lia.
  replace ((1+k)*4+2) with (((1+k)*2+1)*2) by lia.
  replace (len+3) with (len+1+1+1) by lia.
  replace (k*8+5) with (((k*2+1)*2)*2+1) by lia.
  unfold LC; rw_Bin; try solve[arith].
  unfold LC in HA,HB; rewrite HA,HB; exact_word (C0_even2 l r n).
Qed.

Lemma C_even len k r: 4<=k -> Nat.Even k -> k<2^len ->
  LC len k |C> rd0 *> r -->+ LC (len+1) (k*2-7) |C> r.
Proof.
  intros HK [q HQ] HB; destruct len as [|[|len]]; try (cbn in HB; lia).
  replace (S (S len)) with (len+2) in * by lia.
  destruct (divmod2 q) as [q v HV|q v HV]; destruct v as [|v]; try lia;
    [applys_eq (C_even0 len v r)|applys_eq (C_even2 len v r)]; arith.
Qed.

Lemma C_exit len k h r: k<2^len ->
  LC (len+h+4) ((k*4+3)*2^(h+2)+1) |C> rd0 *> r -->+
  LC len k <| rd0^^h *> [1] *> r.
Proof.
  intros HK.
  replace (len+h+4) with (len+1+1+(h+1)+1) by lia.
  replace ((k*4+3)*2^(h+2)+1) with ((((k*2+1)*2+1)*2^(h+1))*2+1) by arith.
  unfold LC; rw_Bin; try solve[arith]; exact_word (C_edge (LC len k) r h).
Qed.
Lemma C_prepare len k h r: 1+k<2^len ->
  LC (len+h+4) (((1+k)*4+1)*2^(h+2)+1) |C> rd0 *> r -->+
  LC (len+3) (k*8+6) |C> rd0^^(h+1) *> [0;0;1] *> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  replace (len+h+4) with (len+1+1+(h+1)+1) by lia.
  replace (((1+k)*4+1)*2^(h+2)+1) with (((((1+k)*2)*2+1)*2^(h+1))*2+1) by arith.
  replace (len+3) with (len+1+1+1) by lia.
  replace (k*8+6) with (((k*2+1)*2+1)*2) by lia.
  unfold LC; rw_Bin; try solve[arith].
  unfold LC in HA,HB; rewrite HA,HB; exact_word (C0_prepare l r n h).
Qed.

Lemma MC_end len k h r: k<2^len ->
  LC len k |> MC h 0 r -->+
  LC (len+h+5) ((k*4+3)*2^(h+3)+1) |C> r.
Proof.
  intros HK.
  replace (len+h+5) with (len+1+1+(h+2)+1) by lia.
  replace ((k*4+3)*2^(h+3)+1) with ((((k*2+1)*2+1)*2^(h+2))*2+1) by arith.
  unfold LC,MC; rw_Bin; try solve[arith]; exact_word (R1 (LC len k) r h).
Qed.

Lemma C_zero3 len k h r: 2^h<=k -> k<2^len ->
  LC (len+h+4) ((k*4+3)*2^(h+2)+1) |C> rd0 *> r -->+
  LC (len+h+5) (((k*4+3)-2^(h+2))*2^(h+3)+1) |C> r.
Proof.
  intros HB HK; eapply progress_evstep_trans; [apply C_exit,HK|].
  replace (rd0^^h *> [1] *> r) with (MC h (2^h-1) r)
    by (unfold MC; rw_Bin; reflexivity).
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_Inc len (k-1)); [flia|lia]|].
  eapply evstep_trans; [applys_eq (MC_Incs len (k-2^h) h (2^h-1) r); [flia|lia|lia]|].
  apply progress_evstep; applys_eq MC_end; [arith|lia].
Qed.

Lemma C_zero h: forall len u r,
  Nat.Odd u -> 2^(h+2)<u -> u<2^(len+2) ->
  LC (len+h+4) (u*2^(h+2)+1) |C> rd0 *> r -->+
  LC (len+h+5) ((u-2^(h+2))*2^(h+3)+1) |C> r.
Proof.
  induction h using lt_wf_ind; intros len u r HO HL HU.
  assert (HR: forall i r', i<=h ->
    LC (len+4) ((u-4)*4+1) |C> rd0^^i *> r' -->*
    LC (len+i+4) ((u-2^(i+2))*2^(i+2)+1) |C> r').
  { induction i; intros r' HI; [applys_eq evstep_refl; cbn; flia|].
    rewrite lpow_S,Str_app_assoc,<-lpow_shift'.
    eapply evstep_trans; [apply IHi; lia|].
    assert (HP: 2^(i+3)<=2^(h+2)) by (apply Nat.pow_le_mono_r; lia).
    eapply progress_evstep; applys_eq (H i ltac:(lia) len (u-2^(i+2)) r').
    - repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; flia.
    - destruct HO as [v HV]; exists (v-2^(i+1)); arith.
    - arith.
    - lia. }
  destruct HO as [v HV].
  destruct (divmod2 v) as [v q HQ|v q HQ]; subst v.
  - destruct q as [|q]; [cbn in HV; subst; arith|].
    replace u with ((1+q)*4+1) in * by lia.
    eapply progress_evstep_trans; [apply C_prepare; arith|].
    replace (h+1) with (S h) by lia; rewrite lpow_S,Str_app_assoc.
    eapply evstep_trans; [apply progress_evstep;
      applys_eq (C_even2 (len+1) (q*2)); [flia|arith]|].
    eapply evstep_trans; [applys_eq (HR h ([0;0;1] *> r)); solve[flia|lia]|].
    apply progress_evstep; applys_eq
      (C_001 (len+h+4) (((1+q)*4+1-2^(h+2))*2^(h+2))); arith.
  - replace u with (q*4+3) by lia; apply C_zero3; arith.
Qed.

Lemma C_zeros t: forall len u h r,
  Nat.Odd u -> 2^(h+2)*(2^t-1)<u -> u<2^(len+2) ->
  LC (len+h+4) (u*2^(h+2)+1) |C> rd0^^t *> r -->*
  LC (len+h+t+4) ((u-2^(h+2)*(2^t-1))*2^(h+t+2)+1) |C> r.
Proof.
  induction t; intros len u h r HO HL HU; [applys_eq evstep_refl; cbn; flia|].
  rewrite lpow_S,Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep; apply C_zero; try assumption; arith|].
  applys_eq (IHt len (u-2^(h+2)) (h+1) r).
  - repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; flia.
  - replace (2^(h+2)*(2^S t-1)) with (2^(h+2)+2^(h+1+2)*(2^t-1)) by arith.
    rewrite Nat.sub_add_distr; flia.
  - destruct HO as [v HV]; exists (v-2^(h+1)); arith.
  - arith.
  - lia.
Qed.

Lemma F_start len m:
  LC (len+1) 0 <| RC m -->+ LC (len+6) (2^(len+6)-14) |C> RC m.
Proof.
  replace (2^(len+6)-14) with (((((2^len-1)*2+1)*2+1)*2^2*2+1)*2) by arith.
  replace (len+6) with (len+1+1+2+1+1) by lia.
  unfold LC; rw_Bin; try solve[arith].
  rewrite (Nat.add_comm len 1).
  follow10 (LOv (RC m) len); exact_word (R_C (ldh <* ld0^^len) (RC m) 0).
Qed.

Lemma RC_power h: rd0^^h *> [1] *> 0inf = RC (2^h).
Proof.
  unfold RC; rw_Bin; cbv [d0 List.length List.repeat].
  f_equal; solve_const0_eq.
Qed.

Lemma C_blank n q: 1+q<2^(n+1) ->
  LC (n+7) (2^(n+7)-(1+q)*32) |C> 0inf -->+
  LC (n+3) 0 <| RC (2^(n+3)-q*2-1).
Proof.
  intros HQ; replace 0inf with (rd0 *> 0inf) by solve_const0_eq.
  eapply progress_evstep_trans; [apply C_even;
    [arith|exists (2^(n+6)-(1+q)*16); arith|arith]|].
  replace 0inf with (rd0^^(n+1) *> 0inf) by apply lpow_all0_3.
  eapply evstep_trans; [applys_eq
    (C_zeros (n+1) (n+3) (2^(n+5)-(1+q)*8-1) 1 0inf);
    try solve[arith]; exists (2^(n+4)-(1+q)*4-1); arith|].
  replace 0inf with (rd0 *> 0inf) by solve_const0_eq.
  eapply evstep_trans; [apply progress_evstep; applys_eq
    (C_exit (n+3) (2^(n+2)-q*2-1) (n+2) 0inf); arith|].
  rewrite RC_power; applys_eq RC_Incs; arith.
Qed.


Ltac garith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
  solve[repeat first[reflexivity|nia|f_equal]].

(* h+2 is the valuation of the last odd deficit plus one; q counts
   subsequent input ones. The arithmetic remains visible to lia/nia. *)
Inductive Num : nat -> nat -> Prop :=
| num s h u q: h+q+2<=s ->
  Num s (((u*2+1)*2^(h+2)-1)*2^q).

Lemma num_one s d: Num s d -> Num (s+1) (d*2).
Proof.
  intros [s0 h u q HS]; applys_eq (num (s0+1) h u (q+1)); arith.
Qed.
Lemma num_zero_odd s h u: h+2<=s ->
  Num (s+1) (((u*2+1)*2^(h+2)-1)*2+2^(h+h+5)+1).
Proof.
  intros HS; applys_eq (num (s+1) (h+1) (u+2^(h+1)) 0); arith.
Qed.
Lemma num_zero_even s h u q: h+q+3<=s ->
  Num (s+1) ((((u*2+1)*2^(h+2)-1)*2^(q+1))*2+7).
Proof.
  intros HS; destruct q as [|[|q]].
  - applys_eq (num (s+1) 0 ((u*2+1)*2^(h+1)) 0); arith.
  - applys_eq (num (s+1) (h+3) u 0); arith.
  - applys_eq (num (s+1) 1 (((u*2+1)*2^(h+2)-1)*2^q) 0); arith.
Qed.

Lemma C_one_gap p d r: 0<d<2^p ->
  LC p (2^p-d) |C> rd1 *> r -->+
  LC (p+1) (2^(p+1)-d*2) |C> r.
Proof. intros HD; applys_eq C_one; arith. Qed.
Lemma C_even_gap p d r: 0<d -> d+4<=2^p -> Nat.Even d ->
  LC p (2^p-d) |C> rd0 *> r -->+
  LC (p+1) (2^(p+1)-(d*2+7)) |C> r.
Proof.
  intros HD HB [v HV]; destruct p; [cbn in HB; lia|].
  applys_eq C_even; try solve[arith]; exists (2^p-v); arith.
Qed.
Lemma C_odd_gap n h u r: (u*2+1)+2^(h+2)<2^(n+2) ->
  LC (n+h+4) (2^(n+h+4)-((u*2+1)*2^(h+2)-1)) |C> rd0 *> r -->+
  LC (n+h+5) (2^(n+h+5)-(((u*2+1)*2^(h+2)-1)*2+2^(h+h+5)+1)) |C> r.
Proof.
  intros HU; applys_eq (C_zero h n (2^(n+2)-(u*2+1)) r);
    try solve[garith]; exists (2^(n+1)-u-1); arith.
Qed.

Definition Bounds a s d := Num s d /\
  2^(a+a+s+7)<=d /\ d+7<=2^(a+a+s+8)+2^(s+s).

Lemma envelope_room p a s d:
  d+7<=2^(a+a+s+8)+2^(s+s) ->
  a+a+s+10<=p -> s+s+3<=p ->
  d+2^(s+s)+1<2^p /\ d+4<2^p.
Proof.
  intros HD HP HQ.
  assert (HA: 2^(a+a+s+10)<=2^p) by (apply Nat.pow_le_mono_r; lia).
  assert (HB: 2^(s+s+3)<=2^p) by (apply Nat.pow_le_mono_r; lia).
  split; arith.
Qed.

Lemma C_next p a s d (b:bool) r:
  Bounds a s d -> a+a+s+10<=p -> s+s+3<=p ->
  exists d', Bounds a (s+1) d' /\
    (b=false -> exists v,d'=v*4+3) /\
    LC p (2^p-d) |C> (if b then rd1 else rd0) *> r -->+
    LC (p+1) (2^(p+1)-d') |C> r.
Proof.
  intros [HN [HD HU]] HP HQ.
  destruct (envelope_room p a s d HU HP HQ) as [HB HE].
  destruct b.
  - exists (d*2); split.
    + split; [apply num_one,HN|split; arith].
    + split; [discriminate|apply C_one_gap; lia].
  - destruct HN as [s0 h u q HS]; destruct q as [|q].
    + cbn [Nat.pow Nat.mul] in *.
      assert (HF: 2^(h+h+4)<=2^(s0+s0)) by (apply Nat.pow_le_mono_r; lia).
      exists (((u*2+1)*2^(h+2)-1)*2+2^(h+h+5)+1); split.
      * split; [apply num_zero_odd; lia|split; arith].
      * split; [intros _; exists ((u*2+1)*2^(h+1)+2^(h+h+3)-1); arith|].
        assert (exists n,p=n+h+4) as [n ->] by (exists (p-h-4); lia).
        assert (HG: (u*2+1)+2^(h+2)<2^(n+2)).
        { assert (HX: (u*2+1)*2^(h+2)+2^(h+h+4)<2^(n+h+4)) by lia.
          clear -HX; arith. }
        clear -HG; applys_eq (C_odd_gap n h u r); solve[flia|exact HG].
    + exists ((((u*2+1)*2^(h+2)-1)*2^(S q))*2+7); split.
      * split; [applys_eq (num_zero_even s0 h u q); arith|clear -HD HU; split; arith].
      * split; [intros _; exists (((u*2+1)*2^(h+2)-1)*2^q+1); arith|].
        clear -HD HE; apply C_even_gap; try lia.
        exists (((u*2+1)*2^(h+2)-1)*2^q); arith.
Qed.

Definition Words (ls:list bool) := flat_map (fun b:bool=>if b then rd1 else rd0) ls.

Lemma C_scan xs: forall p a s d r,
  Bounds a s d -> a+a+s+10<=p -> s+s+length xs+3<=p ->
  exists d', Bounds a (s+length xs) d' /\
    LC p (2^p-d) |C> Words xs *> r -->*
    LC (p+length xs) (2^(p+length xs)-d') |C> r.
Proof.
  induction xs as [|b xs IH]; intros p a s d r HD HP HQ.
  - cbn [Words flat_map length Str_app].
    exists d; split; [applys_eq HD; flia|applys_eq evstep_refl; flia].
  - cbn [Words flat_map]; rewrite Str_app_assoc.
    destruct (C_next p a s d b (Words xs *> r) HD HP ltac:(cbn in HQ; lia))
      as [e [HE [_ HS]]].
    destruct (IH (p+1) a (s+1) e r HE ltac:(lia) ltac:(cbn in HQ; lia))
      as [v [HV HM]].
    exists v; split; [applys_eq HV; cbn; flia|].
    eapply evstep_trans; [apply progress_evstep,HS|applys_eq HM; cbn; flia].
Qed.

Lemma C_ones j: forall p d r, 0<d<2^p ->
  LC p (2^p-d) |C> rd1^^j *> r -->*
  LC (p+j) (2^(p+j)-d*2^j) |C> r.
Proof.
  induction j; intros p d r HD; [applys_eq evstep_refl; cbn; flia|].
  rewrite lpow_S,Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep,C_one_gap,HD|].
  applys_eq (IHj (p+1) (d*2) r); garith.
Qed.

Lemma prefix_bounds a: 8<=a ->
  Bounds a 2 (2^(a+6)*(2^(a+4)-63)+3).
Proof.
  intros HA; assert (HP: 2^8<=2^a) by (apply Nat.pow_le_mono_r; lia).
  split; [applys_eq (num 2 0 ((2^(a+4)-63)*2^(a+3)) 0); arith|split; arith].
Qed.

Lemma C_prefix p a r: 8<=a -> a+2<=p ->
  LC (p+6) (2^(p+6)-14) |C> rd1 *> rd0^^(a-1) *> rd1 *> rd0 *> r -->+
  LC (p+a+8) (2^(p+a+8)-(2^(a+6)*(2^(a+4)-63)+3)) |C> r.
Proof.
  intros HA HP.
  assert (HA2: 2^8<=2^a) by (apply Nat.pow_le_mono_r; lia).
  assert (HP2: 2^(a+4)<=2^(p+2)) by (apply Nat.pow_le_mono_r; lia).
  assert (HA4: 2^a=2^(a-2)*4) by (replace a with (a-2+2) at 1 by lia; arith).
  eapply progress_evstep_trans; [apply C_one_gap; arith|].
  replace (a-1) with (S (a-2)) by lia; rewrite lpow_S,Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep; applys_eq (C_even_gap (p+7) 28);
    try solve[garith]; exists 14; reflexivity|].
  eapply evstep_trans; [applys_eq (C_zeros (a-2) p (2^(p+2)-1) 4);
    try solve[garith]; exists (2^(p+1)-1); arith|].
  eapply evstep_trans; [apply progress_evstep; applys_eq
    (C_one_gap (p+a+6) (2^(a+4)*(2^(a+4)-63)-1)); garith|].
  apply progress_evstep; applys_eq
    (C_even_gap (p+a+7) ((2^(a+4)*(2^(a+4)-63)-1)*2) r);
    try solve[garith]; exists (2^(a+4)*(2^(a+4)-63)-1); arith.
Qed.

Lemma bounds_value a t v: 8<=a -> 6<=t -> Bounds a (t+3) (v*4+3) ->
  2^(a+a+t+8)<=v<2^(a+a+t+t+5).
Proof.
  intros HA HT [_ [HD HU]].
  assert (HP: 2^(a+a+t+11)<=2^(a+a+t+t+6)) by (apply Nat.pow_le_mono_r; lia).
  assert (HQ: 2^(t+t+6)<=2^(a+a+t+t+6)) by (apply Nat.pow_le_mono_r; lia).
  split; arith.
Qed.

Lemma C_sweep a j t xs: length xs=t -> 8<=a -> a+8<=j -> 6<=t ->
  exists v, 2^(a+a+t+8)<=v<2^(a+a+t+t+5) /\
    LC (a+j+t+8) (2^(a+j+t+8)-14) |C>
      rd1 *> rd0^^(a-1) *> rd1 *> rd0 *> Words xs *> rd0 *> rd1^^j *> 0inf -->+
    LC ((a+j+t+3)*2+5) (2^((a+j+t+3)*2+5)-(v*4+3)*2^j) |C> 0inf.
Proof.
  intros HX HA HJ HT.
  destruct (C_scan xs (a+j+t+a+10) a 2 (2^(a+6)*(2^(a+4)-63)+3)
    (rd0 *> rd1^^j *> 0inf) (prefix_bounds a HA) ltac:(lia) ltac:(rewrite HX; lia))
    as [d [HD HM]]; rewrite HX in HD,HM.
  destruct (C_next (a+j+t+a+10+t) a (2+t) d false (rd1^^j *> 0inf)
    HD ltac:(lia) ltac:(lia)) as [e [HE [HZ HS]]].
  destruct (HZ eq_refl) as [v ->].
  assert (HV: 2^(a+a+t+8)<=v<2^(a+a+t+t+5))
    by (apply bounds_value; try lia; applys_eq HE; flia).
  destruct HE as [_ [_ HU]].
  destruct (envelope_room (a+j+t+a+10+t+1) a (2+t+1) (v*4+3)
    HU ltac:(lia) ltac:(lia)) as [_ HB].
  exists v; split; [exact HV|].
  eapply progress_evstep_trans; [applys_eq (C_prefix (a+j+t+2) a); solve[flia|lia]|].
  eapply evstep_trans; [applys_eq HM; flia|].
  eapply evstep_trans; [apply progress_evstep,HS|].
  applys_eq (C_ones j (a+j+t+a+10+t+1) (v*4+3) 0inf); solve[flia|lia].
Qed.

Lemma C_blank_gap n k v: (v*4+3)*2^k<2^(n+1) ->
  LC (n+7) (2^(n+7)-(v*4+3)*2^(k+5)) |C> 0inf -->+
  LC (n+3) 0 <| RC (2^(n+3)-((v*4+3)*2^(k+1)-1)).
Proof. intros HV; applys_eq (C_blank n ((v*4+3)*2^k-1)); garith. Qed.

Lemma value_room a t k v: v<2^(a+a+t+t+5) ->
  (v*4+3)*2^k<2^((a+k+t+7)*2+1).
Proof.
  intros HV; assert (HP: v*4+3<2^(a+a+t+t+7)) by arith.
  eapply Nat.lt_le_trans with (m:=2^(a+a+t+t+7+k)).
  - rewrite Nat.pow_add_r; clear -HP; nia.
  - apply Nat.pow_le_mono_r; lia.
Qed.

Lemma C_round a j t xs: length xs=t -> 8<=a -> a+8<=j -> 6<=t ->
  exists v, 2^(a+a+t+8)<=v<2^(a+a+t+t+5) /\
    LC (a+j+t+8) (2^(a+j+t+8)-14) |C>
      rd1 *> rd0^^(a-1) *> rd1 *> rd0 *> Words xs *> rd0 *> rd1^^j *> 0inf -->+
    LC ((a+j+t+3)*2+1) 0 <|
      RC (2^((a+j+t+3)*2+1)-((v*4+3)*2^(j-4)-1)).
Proof.
  intros HX HA HJ HT.
  assert (exists k,j=k+5) as [k ->] by (exists (j-5); lia).
  destruct (C_sweep a (k+5) t xs HX HA HJ HT) as [v [HV HM]].
  exists v; split; [exact HV|].
  eapply progress_trans; [exact HM|].
  applys_eq (C_blank_gap ((a+k+t+7)*2) k v); try solve[flia].
  apply value_room; lia.
Qed.


Definition powN n := (2^N.of_nat n)%N.
Lemma powN_spec n: N.to_nat (powN n)=2^n.
Proof. unfold powN; rewrite N2Nat.inj_pow,Nat2N.id; reflexivity. Qed.

Inductive State := Fnum (p:nat) (m:N) | Cnum (p:nat) (k m:N).
Definition Config s := match s with
| Fnum p m => LC p 0 <| RC (N.to_nat m)
| Cnum p k m => LC p (N.to_nat k) |C> RC (N.to_nat m)
end.
Inductive Action := Start | One (r:N) | Even (q r:N)
  | Zero (len h:nat) (u r:N) | Exit (len h:nat) (q:N).

Definition act op s := match op,s with
| Start,Fnum p m =>
  if 1<=?p then Cnum (p+5) (powN (p+5)-14) m else s
| One r,Cnum p k m =>
  if (m=?r*2+1)%N && (k<?powN p)%N then Cnum (p+1) (k*2) r else s
| Even q r,Cnum p k m =>
  if (m=?r*2)%N && (k=?q*2)%N && (4<=?k)%N && (k<?powN p)%N
  then Cnum (p+1) (k*2-7) r else s
| Zero len h u r,Cnum p k m =>
  if (p=?len+h+4) && (k=?u*powN (h+2)+1)%N && (m=?r*2)%N &&
    (u=?u/2*2+1)%N && (powN (h+2)<?u)%N && (u<?powN (len+2))%N
  then Cnum (len+h+5) ((u-powN (h+2))*powN (h+3)+1) r else s
| Exit len h q,Cnum p k m =>
  if (p=?len+h+4) && (k=?(q*4+3)*powN (h+2)+1)%N &&
    (m=?0)%N && (q<?powN len)%N then Fnum len (powN h+q) else s
| _,_ => s end.

Ltac natify := autorewrite with Nnat in *; repeat rewrite powN_spec in *;
  cbn [N.to_nat Pos.to_nat] in *.
Ltac guards H := repeat rewrite and_true_iff in H;
  repeat match type of H with _ /\ _ => destruct H as [? H] end;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: (_ && _)=true |- _ => apply and_true_iff in H; destruct H
  | H: (_ =? _)%N=true |- _ => apply N.eqb_eq in H
  | H: (_ <? _)%N=true |- _ => apply N.ltb_lt in H
  | H: (_ <=? _)%N=true |- _ => apply N.leb_le in H
  | H: (_ =? _)=true |- _ => apply Nat.eqb_eq in H
  | H: (_ <=? _)=true |- _ => apply Nat.leb_le in H
  end.
Ltac Nfacts := repeat match goal with
  | H: @eq N ?x ?y |- _ => apply (f_equal N.to_nat) in H
  | H: (?x < ?y)%N |- _ => let HN:=fresh in
    assert (HN:N.to_nat x<N.to_nat y) by lia; clear H
  | H: (?x <= ?y)%N |- _ => let HN:=fresh in
    assert (HN:N.to_nat x<=N.to_nat y) by lia; clear H
  end.

Lemma act_spec op s: Config s -->* Config (act op s).
Proof.
  destruct op,s; cbn [act]; try apply evstep_refl;
    match goal with |- context[if ?b then _ else _] => destruct b eqn:HB end;
    try apply evstep_refl; guards HB; cbn [Config]; Nfacts; natify.
  - apply progress_evstep; applys_eq (F_start (p-1) (N.to_nat m)); try flia; lia.
  - replace (N.to_nat m) with (N.to_nat r*2+1) by lia.
    unfold RC; rewrite BinInc_mul2add1; apply progress_evstep,C_one; lia.
  - replace (N.to_nat m) with (N.to_nat r*2) by lia.
    unfold RC; rewrite BinInc_mul2; apply progress_evstep,C_even; try lia.
    exists (N.to_nat q); lia.
  - replace (N.to_nat m) with (N.to_nat r*2) by lia.
    unfold RC; rewrite BinInc_mul2; apply progress_evstep.
    applys_eq (C_zero h len (N.to_nat u)); try flia; try lia.
    exists (N.to_nat (u/2)); lia.
  - replace (N.to_nat m) with 0%nat by lia; change (RC 0) with 0inf.
    replace 0inf with (rd0 *> 0inf) by solve_const0_eq.
    eapply progress_evstep; eapply progress_evstep_trans.
    + applys_eq (C_exit len (N.to_nat q) h 0inf); try flia; lia.
    + rewrite RC_power; apply RC_Incs; lia.
Qed.

Fixpoint zeros (p:positive):nat := match p with
| xO p => 1+zeros p | _=>0 end.
Definition choose s := match s with
| Fnum _ _ => Start
| Cnum p k m =>
  if N.odd m then One (m/2) else
  if N.even k then Even (k/2) (m/2) else
  let h:=(match (k-1)%N with N0=>0 | Npos p=>zeros p end)-2 in
  let len:=p-h-4 in
  let u:=((k-1)/powN (h+2))%N in
  if (powN (h+2)<?u)%N then Zero len h u (m/2) else Exit len h (u/4)
end.

Definition at_target s p m := match s with
| Fnum q v => (p=?q) && (m=?v)%N | _=>false end.
Lemma at_target_spec s p m: at_target s p m=true -> s=Fnum p m.
Proof.
  destruct s; cbn [at_target]; intros H; try discriminate.
  apply and_true_iff in H; destruct H as [HP HM].
  apply Nat.eqb_eq in HP; apply N.eqb_eq in HM; subst; reflexivity.
Qed.
Fixpoint check (fuel:nat) s p m :=
  if at_target s p m then true else match fuel with
  | O=>false | S fuel=>check fuel (act (choose s) s) p m end.
Lemma check_spec fuel: forall s p m, check fuel s p m=true ->
  Config s -->* Config (Fnum p m).
Proof.
  induction fuel; intros s p m; cbn [check]; destruct (at_target s p m) eqn:H.
  - apply at_target_spec in H; subst; intros; apply evstep_refl.
  - discriminate.
  - apply at_target_spec in H; subst; intros; apply evstep_refl.
  - intros HC; eapply evstep_trans; [apply act_spec|apply IHfuel,HC].
Qed.

Lemma init_counter: c0 -->* Config (Fnum 3 6).
Proof. applys_eq init_word; vm_compute; reflexivity. Qed.

Definition entry_value := (powN 55-((109821*4+3)*powN 9-1))%N.
Lemma entry_checked: check 256 (Fnum 3 6) 55 entry_value=true.
Proof. vm_compute; reflexivity. Qed.
Lemma init_final: c0 -->* LC 55 0 <|
  RC (2^55-((109821*4+3)*2^9-1)).
Proof.
  eapply evstep_trans; [apply init_counter|].
  pose proof (check_spec 256 (Fnum 3 6) 55 entry_value entry_checked) as H.
  cbn [Config] in H; unfold entry_value in H; natify; exact H.
Qed.


Fixpoint Value (ls:list bool):nat :=
  match ls with []=>0 | b::xs=>Value xs*2+(if b then 1 else 0) end.

Lemma value_digits n: forall v, v<2^n ->
  exists xs,length xs=n /\ Value xs=v.
Proof.
  induction n; intros v HV; [exists ([]:list bool); cbn in *; lia|].
  destruct (divmod2 v) as [v0 w HW|v0 w HW];
    destruct (IHn w ltac:(cbn in HV; lia)) as [xs [HN HX]].
  - exists (false::xs); cbn; lia.
  - exists (true::xs); cbn; lia.
Qed.

Lemma RC_even v: RC (v*2)=rd0 *> RC v.
Proof. unfold RC; rewrite BinInc_mul2; reflexivity. Qed.
Lemma RC_odd v: RC (v*2+1)=rd1 *> RC v.
Proof. unfold RC; rewrite BinInc_mul2add1; reflexivity. Qed.
Lemma RC_shift v h: RC (v*2^h)=rd0^^h *> RC v.
Proof. unfold RC; rewrite BinInc_mulpow2; reflexivity. Qed.
Lemma RC_high j: RC (2^j-1)=rd1^^j *> 0inf.
Proof.
  induction j; [unfold RC; rw_Bin; reflexivity|].
  replace (2^S j-1) with ((2^j-1)*2+1) by (cbn [Nat.pow]; lia).
  rewrite RC_odd,IHj,lpow_S,Str_app_assoc; reflexivity.
Qed.

Lemma RC_words xs: forall m,
  RC (Value xs+m*2^length xs)=Words xs *> RC m.
Proof.
  unfold RC; induction xs as [|b xs IH]; intros m.
  - cbn [Value Words flat_map length Str_app]; f_equal; lia.
  - cbn [Value Words flat_map length]; rewrite Str_app_assoc.
    replace (Value xs*2+(if b then 1 else 0)+m*2^S (length xs))
      with ((Value xs+m*2^length xs)*2+(if b then 1 else 0)) by (cbn [Nat.pow]; lia).
    destruct b.
    + rewrite BinInc_mul2add1,IH; reflexivity.
    + rewrite Nat.add_0_r,BinInc_mul2,IH; reflexivity.
Qed.

Lemma RC_prefix a v: 1<=a ->
  RC ((v*4+1)*2^a+1)=rd1 *> rd0^^(a-1) *> rd1 *> rd0 *> RC v.
Proof.
  intros HA; destruct a; [lia|].
  replace (S a-1) with a by lia.
  replace ((v*4+1)*2^S a+1) with (((v*2*2+1)*2^a)*2+1) by (cbn [Nat.pow]; lia).
  rewrite RC_odd,RC_shift,RC_odd,RC_even; reflexivity.
Qed.

Lemma RC_middle t j u: 2^t<=u<2^(t+1) ->
  exists xs,length xs=t /\
    RC (2^(t+j+1)-u-1)=Words xs *> rd0 *> rd1^^j *> 0inf.
Proof.
  intros HU; destruct (value_digits t (2^(t+1)-u-1) ltac:(arith)) as [xs [HX HV]].
  exists xs; split; [exact HX|].
  rewrite <-(RC_high j),<-RC_even,<-RC_words.
  f_equal; rewrite HX,HV; arith.
Qed.

Lemma RC_state a j t u: 1<=a -> 2^t<=u<2^(t+1) ->
  exists xs,length xs=t /\
    RC (2^(a+j+t+3)-((u*4+3)*2^a-1))=
      rd1 *> rd0^^(a-1) *> rd1 *> rd0 *> Words xs *> rd0 *> rd1^^j *> 0inf.
Proof.
  intros HA HU; destruct (RC_middle t j u HU) as [xs [HX HR]].
  exists xs; split; [exact HX|].
  rewrite <-HR,<-RC_prefix by lia.
  assert (HP: 2^(t+1)<=2^(t+j+1)) by (apply Nat.pow_le_mono_r; lia).
  f_equal; arith.
Qed.

Lemma F_round a j t u: 8<=a -> a+8<=j -> 6<=t -> 2^t<=u<2^(t+1) ->
  exists v, 2^(a+a+t+8)<=v<2^(a+a+t+t+5) /\
    LC (a+j+t+3) 0 <| RC (2^(a+j+t+3)-((u*4+3)*2^a-1)) -->+
    LC ((a+j+t+3)*2+1) 0 <|
      RC (2^((a+j+t+3)*2+1)-((v*4+3)*2^(j-4)-1)).
Proof.
  intros HA HJ HT HU.
  destruct (RC_state a j t u ltac:(lia) HU) as [xs [HX HR]].
  destruct (C_round a j t xs HX HA HJ HT) as [v [HV HM]].
  exists v; split; [exact HV|].
  eapply progress_trans; [applys_eq (F_start (a+j+t+2)); flia|].
  rewrite HR; applys_eq HM; flia.
Qed.

Inductive P : Q*tape -> Prop :=
| PF a j t u: 8<=a -> a+8<=j -> 6<=t -> 2^t<=u<2^(t+1) ->
  P (LC (a+j+t+3) 0 <| RC (2^(a+j+t+3)-((u*4+3)*2^a-1))).

Lemma P_step c: P c -> exists c',P c' /\ c -->+ c'.
Proof.
  intros [a j t u HA HJ HT HU].
  destruct (F_round a j t u HA HJ HT HU) as [v [HV HM]].
  assert (Hpos: 0<v) by lia.
  pose proof (Nat.log2_spec v Hpos) as HW.
  assert (HL: a+a+t+8<=Nat.log2 v<a+a+t+t+5).
  { split; [apply (proj1 (Nat.log2_le_pow2 v _ Hpos)),HV|
      apply (proj1 (Nat.log2_lt_pow2 v _ Hpos)),HV]. }
  eexists; split; [|exact HM].
  applys_eq (PF (j-4) ((a+j+t+3)*2+1-(j-4)-Nat.log2 v-3) (Nat.log2 v) v);
    try solve[flia|lia].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_final|].
  eapply progress_nonhalt_cond with (C:=fun c=>c) (P:=P).
  - intros c HC; destruct (P_step c HC) as [c' [HP HM]]; eauto.
  - applys_eq (PF 9 27 16 109821); try reflexivity;
      try split; first [apply Nat.leb_le|apply Nat.ltb_lt]; vm_compute; reflexivity.
Qed.


End TM113.

From BusyCoq Require Import Individual62 BinaryCounter_v2 DivModCases.
Require Import ZifyNat Lia PeanoNat Wf_nat Compare_dec.
From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull BinaryCounter_v2 SimplTape ES_v2 DivModCases.
Require Import ZifyNat Lia PeanoNat NArith Wf_nat.
From BusyCoq Require Import Individual62 SimplTape ES_v2.
Require Import String.

(* Shared definitions from SOC_ExWeighted.v. *)
Module SOC_ExWeighted.
(* SOC_ex 15,16,18 (holdouts 909,146,796): nonhalting.
   Standalone proof; imports only BusyCoq and the Coq standard library.
   Informal argument and compilation/audit records: SOC_EX_WEIGHTED.md. *)

Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat Wf_nat Compare_dec.

Module Weight.
Local Open Scope nat_scope.
(* Num m w means w=W(m); Inc m d means W(m+1)=W(m)+d. *)
Inductive Num: nat->nat->Prop :=
| Num0: Num 0 0
| Num2 m w: Num m w -> Num (m*2) (m*4-w)
| Num21 m w: Num m w -> Num (m*2+1) (m*4-w+1).

Lemma Num_bounds m w: Num m w -> m<=w<=m*2.
Proof. induction 1; lia. Qed.
Lemma Num_ex m: exists w, Num m w.
Proof.
  induction m using lt_wf_ind.
  destruct m as [|m]; [exists 0%nat; constructor|].
  destruct (mod2 (S m)); subst.
  - edestruct (H a) as [w HW]; [lia|].
    eexists; applys_eq (Num2 _ _ HW); flia.
  - edestruct (H a) as [w HW]; [lia|].
    eexists; applys_eq (Num21 _ _ HW); flia.
Qed.

Lemma Num_unique m w: Num m w -> forall w', Num m w' -> w=w'.
Proof.
  induction 1 as [|m w HW IH|m w HW IH]; intros w' HW'.
  1: apply Num_bounds in HW'; lia.
  all: pose proof (Num_bounds _ _ HW);
    inversion HW' as [|m' v HV E|m' v HV E]; subst; try lia;
    assert (m'=m) by lia; subst; rewrite (IH _ HV); reflexivity.
Qed.

Inductive Inc: nat->nat->Prop :=
| Inc0 m: Inc (m*2) 1
| Inc1 m d: Inc m d -> Inc (m*2+1) (3-d).
Lemma Inc_bounds m d: Inc m d -> 1<=d<=2.
Proof. induction 1; lia. Qed.
Lemma Inc_unique m d: Inc m d -> forall e, Inc m e -> d=e.
Proof.
  induction 1; intros e HE; inversion HE; subst; try lia.
  assert (m0=m) by lia; subst; f_equal; auto.
Qed.
Lemma Num_succ m w: Num m w ->
  exists d, Inc m d /\ Num (m+1) (w+d).
Proof.
  induction 1 as [|m w HW IH|m w HW [d [HD HI]]].
  - exists 1; split; [apply (Inc0 0)|apply (Num21 _ _ Num0)].
  - exists 1; split; [constructor|constructor; assumption].
  - exists (3-d); split; [constructor; assumption|].
    pose proof (Num_bounds _ _ HW); pose proof (Inc_bounds _ _ HD).
    applys_eq (Num2 _ _ HI); flia.
Qed.

Lemma Num_mono m w: Num m w -> forall m' w',
  Num m' w' -> m<=m' -> w+(m'-m)<=w'.
Proof.
  intros HW m'; induction m' as [|m' IH]; intros w' HW' Hle.
  - assert (m=0) by lia; subst; apply Num_bounds in HW'; apply Num_bounds in HW; lia.
  - destruct (Nat.eq_dec m (S m')) as [->|Hne].
    + assert (w=w') by (eapply Num_unique; eassumption); lia.
    + destruct (Num_ex m') as [v HV].
      destruct (Num_succ _ _ HV) as [d [HD HI]].
      pose proof (Inc_bounds _ _ HD).
      specialize (IH v HV ltac:(lia)).
      assert (w'=v+d) by (apply (Num_unique _ _ HW'); applys_eq HI; flia).
      lia.
Qed.

Lemma Num_stop q: exists m w d,
  Num m w /\ Inc m d /\ w<=q<w+d.
Proof.
  induction q as [|q [m [w [d [HW [HD HB]]]]]].
  - exists 0, 0, 1; split; [constructor|split; [apply (Inc0 0)|lia]].
  - destruct (le_dec (w+d) (S q)).
    + destruct (Num_succ _ _ HW) as [e [HE HI]].
      assert (e=d) by (eapply Inc_unique; eassumption).
      subst e; destruct (Num_succ _ _ HI) as [e [HE' HI']].
      pose proof (Inc_bounds _ _ HE').
      exists (m+1), (w+d), e; split; [assumption|split; [assumption|lia]].
    + exists m, w, d; split; [assumption|split; [assumption|lia]].
Qed.

Fixpoint Full n : nat := match n with O=>0 | S n=>Full n*2+1+n mod 2 end.
Lemma Full_spec n: Full n*3+4+n mod 2=2^n*4.
Proof.
  induction n; [reflexivity|].
  assert (n mod 2+S n mod 2=1) by lia.
  cbn [Full Nat.pow]; nia.
Qed.

Lemma Full_num n: Num (2^n-1) (Full n).
Proof.
  induction n; [apply Num0|].
  pose proof (Full_spec n).
  applys_eq (Num21 _ _ IHn); cbn [Full Nat.pow]; flia.
Qed.
Lemma Num_power n: Num (2^n) (Full n+1+n mod 2).
Proof.
  induction n; [apply (Num21 _ _ Num0)|].
  pose proof (Full_spec n).
  assert (n mod 2+S n mod 2=1) by lia.
  applys_eq (Num2 _ _ IHn); cbn [Full Nat.pow]; flia.
Qed.
Lemma Num_lower_endpoint n: exists w,
  Num (2^(n+1)+1) w /\ w*3<=2^(n+1)*4+4.
Proof.
  destruct (Num_succ _ _ (Num_power (n+1))) as [d [HD HW]].
  assert (d=1).
  { apply (Inc_unique _ _ HD); rewrite pow2_S; constructor. }
  subst d; eexists; split; [eassumption|].
  pose proof (Full_spec (n+1)); lia.
Qed.
Lemma Num_upper_endpoint n:
  Num (2^n*3-1) (2^n*4-1-n mod 2).
Proof.
  induction n; [apply (Num2 _ _ (Num21 _ _ Num0))|].
  assert (n mod 2+S n mod 2=1) by lia.
  applys_eq (Num21 _ _ IHn); cbn [Nat.pow]; flia.
Qed.

(* l is bit length and g=2^l*T(u); no rational arithmetic is required. *)
Inductive Loss: nat->nat->nat->Prop :=
| Loss0: Loss 0 0 0
| LossS l u g h: Loss l u g ->
    Loss (l+(h+1)) ((u*2+1)*2^h)
      (Full (h+1)*2*2^(l+(h+1))+2^l+g).

Lemma Loss_zero u g: Loss 0 u g -> u=0 /\ g=0.
Proof. inversion 1; lia. Qed.
Lemma Loss_bounds l u g: Loss l u g ->
  u<2^l /\ (u=0 <-> l=0) /\ (0<l -> 2^l<=u*2).
Proof.
  induction 1 as [|l u g h HL [HU [HZ HB]]].
  - cbn; lia.
  - rewrite Nat.pow_add_r, pow2_S.
    destruct l; cbn [Nat.pow] in *; repeat apply conj; intros; nia.
Qed.
Lemma Loss_double l u g: Loss l u g -> 0<u ->
  exists g', Loss (l+1) (u*2) g'.
Proof.
  destruct 1 as [|l u g h HL]; [lia|]; intros.
  eexists; applys_eq (LossS _ _ _ (h+1) HL); rewrite ?pow2_S; flia.
Qed.
Lemma Loss_ex u: exists l g, Loss l u g.
Proof.
  induction u as [u IH] using lt_wf_ind.
  destruct u as [|u]; [exists 0, 0; constructor|].
  destruct (mod2 (S u)) as [a E|a E].
  - edestruct (IH a) as [l [g HL]]; [lia|].
    destruct (Loss_double _ _ _ HL ltac:(lia)) as [g' HG].
    exists (l+1), g'; applys_eq HG; flia.
  - edestruct (IH a) as [l [g HL]]; [lia|].
    eexists; eexists; applys_eq (LossS _ _ _ 0 HL); flia.
Qed.
Lemma Loss_length l u g j: Loss l u g -> 0<j ->
  2^j<=u*2<2^(j+1) -> l=j.
Proof.
  intros HL Hj HU; apply Loss_bounds in HL; destruct HL as [HL [HZ HB]].
  assert (0<l) by (destruct l; cbn in *; lia).
  assert (H1: 2^l<2^(j+1)) by lia.
  assert (H2: 2^j<2^(l+1)) by (rewrite pow2_S; lia).
  apply Nat.pow_lt_mono_r_iff in H1, H2; lia.
Qed.
Lemma Loss_one u g: Loss 1 u g -> u=1 /\ g=5.
Proof.
  inversion 1 as [|l q d h HL E]; subst.
  assert (E0: l=0 /\ h=0) by lia; destruct E0; subst.
  apply Loss_zero in HL; destruct HL; subst; split; reflexivity.
Qed.
Lemma Loss_two g: Loss 2 2 g -> g=33.
Proof.
  inversion 1 as [|l q d h HL E]; subst.
  assert (E0: l=0 /\ h=1 \/ l=1 /\ h=0) by lia.
  destruct E0 as [[-> ->]|[-> ->]].
  - apply Loss_zero in HL; destruct HL; subst; reflexivity.
  - apply Loss_one in HL; destruct HL; subst; cbn in *; lia.
Qed.

Ltac pow := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *.
(* Multiply the three scalar estimates before asking nia to combine them. *)
Lemma loss_step_bound p s f g e:
  f*3+4<=s*4 -> g*3+p*6<=p*p*8 ->
  8<=e*p -> 8<=e*s*s ->
  (f*2*(p*s)+p+g)*3+(p*s)*6<=(p*s)*(p*s)*(e*2).
Proof.
  intros HF HG HP HS.
  pose proof (Nat.mul_le_mono_r _ _ (p*s*2) HF).
  pose proof (Nat.mul_le_mono_r _ _ (p*s*s) HP).
  pose proof (Nat.mul_le_mono_r _ _ (p*p) HS).
  nia.
Qed.
Lemma Loss_lower l u g: Loss l u g -> 0<u -> 5*2^l<=g*2.
Proof.
  intros HL; destruct HL as [|l u g h HL]; [lia|].
  destruct h as [|h].
  - change (Full (0+1)) with 1; pow; nia.
  - pose proof (Full_spec (S h+1)).
    assert (4<=2^(S h+1)) by (rewrite pow2_S; cbn; lia).
    pose proof (Nat.mod_upper_bound (S h+1) 2 ltac:(lia)).
    rewrite Nat.pow_add_r; nia.
Qed.
Lemma Loss_upper l u g: Loss l u g ->
  g*3+2^l*6<=2^l*2^l*8.
Proof.
  induction 1 as [|l u g h HL IH]; [cbn; lia|].
  pose proof (Full_spec (h+1)) as HF.
  assert (2<=2^(h+1)) by (rewrite pow2_S; lia).
  destruct l as [|l].
  - apply Loss_zero in HL; destruct HL; subst.
    rewrite Nat.add_0_l; cbn [Nat.pow]; nia.
  - assert (2<=2^(S l)) by (cbn; lia).
    rewrite Nat.pow_add_r.
    apply (loss_step_bound _ _ _ _ 4); lia.
Qed.

Lemma Loss_nonpower l u g: Loss l u g -> u*2<>2^l ->
  g*3+2^l*3<=2^l*2^l*4.
Proof.
  intros HL; destruct HL as [|l u g h HL]; [cbn; lia|].
  pose proof (Loss_upper _ _ _ HL) as HU.
  pose proof (Full_spec (h+1)) as HF.
  destruct l as [|[|l]].
  - apply Loss_zero in HL; destruct HL; subst; pow; lia.
  - apply Loss_one in HL; destruct HL; subst.
    destruct h as [|h]; [cbn; lia|].
    assert (4<=2^(S h+1)) by (rewrite pow2_S; cbn; lia).
    rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
  - assert (4<=2^(S (S l))) by (cbn; lia).
    assert (2<=2^(h+1)) by (rewrite pow2_S; lia).
    rewrite Nat.pow_add_r.
    pose proof (loss_step_bound (2^(S (S l))) (2^(h+1)) (Full (h+1)) g 2).
    nia.
Qed.

Lemma Loss_interval l u g: Loss l u g -> 5<=l ->
  2^l+2<u*2 -> u*4<2^l*3 -> g*3+2^l*6<=2^l*2^l*2.
Proof.
  intros HL; destruct HL as [|l u g h HL]; [cbn; lia|].
  pose proof (Loss_bounds _ _ _ HL) as [HU [HZ HB]].
  pose proof (Full_spec (h+1)) as HF.
  assert (HP: 0<2^l) by lia.
  assert (HS: 0<2^h) by lia.
  intros Hlen Hlo Hhi.
  destruct h as [|h].
  - assert (HNP: u*2<>2^l) by (pow; nia).
    pose proof (Loss_nonpower _ _ _ HL HNP).
    assert (16<=2^l) by (change (2^4<=2^l); apply Nat.pow_le_mono_r; lia).
    change (Full (0+1)) with 1 in *; pow; nia.
  - destruct l as [|[|[|l]]].
    + apply Loss_zero in HL; destruct HL; subst; pow; nia.
    + apply Loss_one in HL; destruct HL; subst; pow; nia.
    + assert (u=2) by (pow; nia); subst.
      apply Loss_two in HL; subst.
      destruct h as [|[|h]]; try (cbn in *; lia).
      assert (16<=2^(S (S (S h))+1)) by (rewrite pow2_S; cbn; lia).
      rewrite Nat.pow_add_r; cbn [Nat.pow]; nia.
    + pose proof (Loss_upper _ _ _ HL).
      assert (8<=2^(S (S (S l)))) by (cbn; lia).
      assert (4<=2^(S h+1)) by (rewrite pow2_S; cbn; lia).
      rewrite Nat.pow_add_r.
      apply (loss_step_bound _ _ _ _ 1); nia.
Qed.
(* Every constructor includes the positive residual budget for its next marker. *)
Inductive Absorb: nat->nat->nat->nat->nat->Prop :=
| Absorb0 k: Absorb 0 k 0 0 k
| AbsorbS u k t l j K h:
    t<=1 -> 0<j -> k+t*2=Full (h+1)*2+j ->
    Absorb u (j*2^(h+1)-1) 0 l K ->
    Absorb ((u*2+1)*2^h) k t (l+(h+1)) K.

Lemma Absorb_ex l u g: Loss l u g -> forall k t,
  t<=1 -> (u=0 -> t=0) -> g<(k+t*2)*2^l ->
  exists K, Absorb u k t l K /\ K+g=(k+t*2)*2^l /\ 0<K.
Proof.
  induction 1 as [|l u g h HL IH]; intros k t HT HZ HG.
  - assert (t=0) by auto; subst; exists k; split; [constructor|cbn in *; lia].
  - rewrite Nat.pow_add_r in HG |- *.
    assert (HP: 0<2^l) by lia.
    assert (HS: 2<=2^(h+1)) by (rewrite pow2_S; lia).
    assert (HJ: Full (h+1)*2<k+t*2).
    { destruct (le_dec (k+t*2) (Full (h+1)*2)); [|lia].
      apply (Nat.mul_le_mono_r _ _ (2^l*2^(h+1))) in l0; lia. }
    set (j:=k+t*2-Full (h+1)*2).
    assert (E: k+t*2=Full (h+1)*2+j) by (unfold j; lia).
    assert (J: 0<j) by (unfold j; lia).
    destruct (IH (j*2^(h+1)-1) 0 ltac:(lia) ltac:(auto) ltac:(nia))
      as [K [HK [EK HPK]]].
    exists K; split; [eapply AbsorbS with (j:=j); eassumption|split; [|assumption]].
    nia.
Qed.
Lemma Absorb_odd u k t l K: Absorb u k t l K ->
  k mod 2=1 -> K mod 2=1.
Proof.
  induction 1; [auto|]; intros; apply IHAbsorb.
  rewrite pow2_S; lia.
Qed.
Lemma Absorb_capacity u k t l K: Absorb u k t l K ->
  forall n, k<2^n -> K<2^(n+l).
Proof.
  induction 1; intros n Hcap; [rewrite Nat.add_0_r; assumption|].
  pose proof (Full_spec (h+1)).
  assert (2<=2^(h+1)) by (rewrite pow2_S; lia).
  assert (j<=k) by lia.
  specialize (IHAbsorb (n+(h+1)) ltac:(rewrite (Nat.pow_add_r 2 n (h+1)); nia)).
  applys_eq IHAbsorb; flia.
Qed.
Lemma Absorb_window h m t: 3<=h -> 2^h*2<m -> m+1<2^h*3 -> t<=1 ->
  exists K, Absorb (m+1) (2^(h+3)-1) t (h+2) K /\ K mod 2=1 /\
    2^h*2^h*64+2^h*12<=K*3 /\ K*2+2^h*12<=2^h*2^h*64.
Proof.
  intros Hh Hlo Hhi Ht.
  assert (HP: 8<=2^h) by (change (2^3<=2^h); apply Nat.pow_le_mono_r; lia).
  destruct (Loss_ex (m+1)) as [l [g HL]].
  assert (l=h+2) by (eapply Loss_length; [eassumption|lia|pow; lia]); subst l.
  pose proof (Loss_interval _ _ _ HL ltac:(lia) ltac:(pow; lia) ltac:(pow; lia)) as HU.
  pose proof (Loss_lower _ _ _ HL ltac:(lia)) as HD.
  destruct (Absorb_ex _ _ _ HL (2^(h+3)-1) t Ht ltac:(lia) ltac:(pow; nia))
    as [K [HK [EK Hpos]]].
  exists K; split; [assumption|split].
  - eapply Absorb_odd; [eassumption|pow; lia].
  - pow; nia.
Qed.

Lemma Drain_window h K: 3<=h -> K mod 2=1 ->
  2^h*2^h*64+2^h*12<=K*3 -> K*2+2^h*12<=2^h*2^h*64 ->
  exists m w d k, Num m w /\ Inc m d /\ K=k+w*2 /\
    (k=1 \/ k=3) /\ k<=d*2 /\
    2^(h*2+2)*2<m /\ m+1<2^(h*2+2)*3.
Proof.
  intros Hh HK Hlo Hhi.
  assert (HP: 8<=2^h) by (change (2^3<=2^h); apply Nat.pow_le_mono_r; lia).
  assert (EP: 2^(h*2+2)=2^h*2^h*4).
  { replace (h*2+2) with (h+(h+2)) by lia; pow; nia. }
  destruct (mod2 K) as [q EQ|q EQ]; [lia|].
  destruct (Num_stop q) as [m [w [d [HW [HD HB]]]]].
  pose proof (Inc_bounds _ _ HD) as Hd.
  destruct (Num_lower_endpoint (h*2+2)) as [v [HV Hv]].
  assert (HMlo: 2^(h*2+2)*2<m).
  { destruct (le_dec m (2^(h*2+2)*2)); [|lia].
    pose proof (Num_mono _ _ HW _ _ HV ltac:(rewrite pow2_S; lia)).
    rewrite pow2_S, EP in *; nia. }
  pose proof (Num_upper_endpoint (h*2+2)) as HU.
  assert (HMhi: m+1<2^(h*2+2)*3).
  { destruct (le_dec (2^(h*2+2)*3-1) m); [|rewrite EP in *; nia].
    pose proof (Num_mono _ _ HU _ _ HW l).
    rewrite EP in *; nia. }
  exists m, w, d, (1+(q-w)*2); repeat apply conj; try assumption; lia.
Qed.
Inductive Overflow: nat->nat->nat->Prop :=
| OverflowA: Overflow 1 1 1
| OverflowB1: Overflow 1 2 0
| OverflowB3: Overflow 3 2 1.
Lemma Overflow_ex m d k: Inc m d -> (k=1 \/ k=3) -> k<=d*2 ->
  exists t, Overflow k d t /\ t<=1.
Proof.
  intros HD Hk Hle; apply Inc_bounds in HD.
  destruct Hk as [-> | ->].
  - destruct (Nat.eq_dec d 1) as [->|Hne].
    + exists 1; split; [constructor|lia].
    + assert (d=2) by lia; subst; exists 0; split; [constructor|lia].
  - assert (d=2) by lia; subst; exists 1; split; [constructor|lia].
Qed.
Inductive Region: nat->nat->nat->Prop :=
| RegionI h k m d: 3<=h -> Inc m d -> (k=1 \/ k=3) -> k<=d*2 ->
    2^h*2<m -> m+1<2^h*3 -> Region (h+3) k m.
Inductive Round: nat->nat->nat->nat->nat->nat->Prop :=
| RoundI n k m d t l K m' w' d' k':
    Inc m d -> Overflow k d t -> Absorb (m+1) (2^n-1) t l K ->
    Num m' w' -> Inc m' d' -> K=k'+w'*2 -> (k'=1 \/ k'=3) -> k'<=d'*2 ->
    Round n k m (n+l) k' m'.
Theorem Round_closed n k m: Region n k m ->
  exists n' k' m', Round n k m n' k' m' /\ Region n' k' m' /\ n'=n*2-1.
Proof.
  destruct 1 as [h k m d Hh HD Hk Hle Hlo Hhi].
  destruct (Overflow_ex _ _ _ HD Hk Hle) as [t [HO HT]].
  destruct (Absorb_window _ _ _ Hh Hlo Hhi HT) as [K [HA [HK [KL KH]]]].
  destruct (Drain_window _ _ Hh HK KL KH) as [m' [w' [d' [k' [HW [HD' [EK [Hk' [Hle' [HL' HH']]]]]]]]]].
  exists (h+3+(h+2)), k', m'; split.
  - econstructor; eassumption.
  - split; [|lia].
    replace (h+3+(h+2)) with (h*2+2+3) by lia.
    econstructor; try eassumption; lia.
Qed.
Lemma Region_seed_15_16: Region 9 1 157.
Proof. apply (RegionI 6 1 157 2); try (cbn; lia). apply (Inc1 78 1 (Inc0 39)). Qed.
Lemma Region_seed_18: Region 13 1 2657.
Proof. apply (RegionI 10 1 2657 2); try (cbn; lia). apply (Inc1 1328 1 (Inc0 664)). Qed.
End Weight.

(* Tape interpretation of the weighted arithmetic above. *)
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat NArith Wf_nat.

Import Weight.

Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition LC n k := BinDec ld0 ld1 n k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h m r := BinDec2 [1] [0] [0;0] h m r.
Definition Bit t : list Sym := match t with O=>[0] | _=>[1] end.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; solve [lia|nia|flia].
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first [follow10 HX|follow100 HX];
  st; repeat (simpl_rotate || simpl_tape); finish.

Lemma Inc_split m d: Inc m d -> exists q h,
  m=(q*2+1)*2^h-1 /\ d=1+h mod 2.
Proof.
  induction 1 as [m|m d HD [q [h [EM ED]]]].
  - exists m, O; cbn; lia.
  - exists q, (h+1); rewrite pow2_S.
    assert (h mod 2+(h+1) mod 2=1%nat) by lia; split; nia.
Qed.
Lemma LC_split n k: 1+k<2^n -> exists l h,
  LC n (1+k)=l <* ld0 <* ld1^^h /\ LC n k=l <* ld1 <* ld0^^h.
Proof.
  unfold LC,BinDec; intros HK.
  assert (HE: Pos.of_nat (2^(n+1)-1-k)=Pos.succ (Pos.of_nat (2^(n+1)-1-(1+k)))) by arith.
  rewrite HE; eapply not_full_Inc.
  rewrite not_full_iff_pow2'.
  erewrite (log2_spec' n); [rewrite pow2'_spec'; arith|arith].
Qed.
Lemma LC_one h: LC (h+1) 1=ldh <* ld1^^h <* ld0.
Proof.
  change (BinDec ld0 ld1 (h+1) (0*2+1) ldh=ldh <* ld1^^h <* ld0).
  rewrite BinDec_mul2add1,BinDec_O by arith; reflexivity.
Qed.
Lemma Num_small t: t<=1 -> Num t t.
Proof. destruct t as [|[|t]]; intros; [constructor|apply (Num21 _ _ Num0)|lia]. Qed.
Lemma MC_small h t r: t<=1 -> MC h t r=Bit t *> rd0^^h *> r.
Proof.
  destruct t as [|[|t]]; intros; [| |lia]; unfold MC; cbn [Bit].
  - change (BinDec2 [1] [0] [0;0] h (0*2) r = [0] *> rd0^^h *> r).
    rewrite BinDec2_mul2,BinDec_O; reflexivity.
  - change (BinDec2 [1] [0] [0;0] h (0*2+1) r = [1] *> rd0^^h *> r).
    rewrite BinDec2_mul2add1,BinDec_O; reflexivity.
Qed.
Lemma RC_shift h u t: t<=1 ->
  Bit t *> RC ((u*2+1)*2^h)=MC h t (rd1 *> RC u).
Proof.
  intros; rewrite MC_small by assumption; unfold RC.
  rewrite BinInc_mulpow2,BinInc_mul2add1; reflexivity.
Qed.

Section Core.
Variables (tm:TM) (QA QB QC QR:Q).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <a| r" := (l <{{QA}} [0] *> r) (at level 30).
Notation "l <b| r" := (l <{{QB}} [0] *> r) (at level 30).
Notation "l <c| r" := (l <{{QC}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{QR}}> r) (at level 30).
Definition cfgL d (l r:Stream Sym) := l <{{match d with S O=>QA | _=>QB end}} [0] *> r.

Hypothesis RInc0: forall l r h,
  l |> rd1^^(h*2) *> [0] *> r -->+ l <a| rd0^^(h*2) *> [1] *> r.
Hypothesis RInc1: forall l r h,
  l |> rd1^^(1+h*2) *> [0] *> r -->+ l <b| rd0^^(1+h*2) *> [1] *> r.
Hypothesis LInc: forall l r h,
  l <* ld0 <* ld1^^h <c| r -->+ l <* ld1 <* ld0^^h |> r.
Hypothesis AInc: forall l r h,
  l <* ld0 <* ld1^^h <* ld0 <a| r -->+ l <* ld1 <* ld0^^h <* ld0 |> r.
Hypothesis BInc0: forall l r h,
  l <* ld0 <* ld1^^h <* ld0 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^h <* ld0 <* ld0 |> r.
Hypothesis BInc1: forall l r h,
  l <* ld0 <* ld1^^h <* ld1 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^h <* ld1 <* ld0 |> r.
Hypothesis LOnes: forall l r h,
  l <* <[1]^^h <c| r -->* l <c| [1]^^h *> r.
Hypothesis ROnes: forall l r h,
  l |> [1;1;1]^^h *> r -->* l <* ld0^^h |> r.
Hypothesis RDigits: forall l r h,
  l |> rd1^^h *> r -->* l <* ld1^^h |> r.
Hypothesis R110: forall l r, l |> [1;1;0] *> r -->+ l <* <[1;1] <c| [1] *> r.
Hypothesis AOne: forall r n,
  ldh <* ld1^^n <* ld0 <a| r -->+ ldh <* ld0^^(1+n) |> [1] *> r.
Hypothesis BOne: forall r n,
  ldh <* ld1^^n <* ld0 <b| r -->+ ldh <* ld0^^(1+n) |> [0] *> r.
Hypothesis BThree: forall r n,
  ldh <* ld1^^n <* ld0 <* ld0 <b| r -->+ ldh <* ld0^^(2+n) |> [1] *> r.

Lemma RInc l r h:
  l |> rd1^^h *> [0] *> r -->+ cfgL (1+h mod 2) l (rd0^^h *> [1] *> r).
Proof.
  destruct (mod2 h) as [a ->|a ->]; unfold cfgL.
  - replace (1+(a*2) mod 2) with 1%nat by lia; apply RInc0.
  - replace (1+(1+a*2) mod 2) with 2%nat by lia; apply RInc1.
Qed.
Lemma RC_Inc l m d: Inc m d -> l |> RC m -->+ cfgL d l (RC (m+1)).
Proof.
  intros HD; destruct (Inc_split _ _ HD) as [q [h [-> ->]]].
  replace ((q*2+1)*2^h-1+1) with ((q*2+1)*2^h) by nia.
  unfold RC; rewrite BinInc_mulpow2sub1,BinInc_mulpow2,BinInc_mul2add1.
  cbn [d0 List.length List.repeat]; unfold cfgL; follow_rule RInc.
Qed.
Lemma LC_A n k r: (k+1)*2+1<2^(n+1) ->
  LC (n+1) ((k+1)*2+1) <a| r -->+ LC (n+1) (k*2+1) |> r.
Proof.
  intros HK; destruct (LC_split n k) as [l [h [HA HB]]]; [arith|].
  unfold LC; rw_Bin; try solve [arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule AInc.
Qed.
Lemma LC_B0 n k r: (k+1)*4+3<2^(n+2) ->
  LC (n+2) ((k+1)*4+3) <b| r -->+ LC (n+2) (k*4+3) |> r.
Proof.
  intros HK; destruct (LC_split n k) as [l [h [HA HB]]]; [arith|].
  replace (n+2) with (n+1+1) by lia.
  replace ((k+1)*4+3) with (((k+1)*2+1)*2+1) by lia.
  replace (k*4+3) with ((k*2+1)*2+1) by lia.
  unfold LC; rw_Bin; try solve [arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule BInc0.
Qed.
Lemma LC_B1 n k r: (k+1)*4+1<2^(n+2) ->
  LC (n+2) ((k+1)*4+1) <b| r -->+ LC (n+2) (k*4+1) |> r.
Proof.
  intros HK; destruct (LC_split n k) as [l [h [HA HB]]]; [arith|].
  replace (n+2) with (n+1+1) by lia.
  replace ((k+1)*4+1) with (((k+1)*2)*2+1) by lia.
  replace (k*4+1) with ((k*2)*2+1) by lia.
  unfold LC; rw_Bin; try solve [arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule BInc1.
Qed.
Lemma LC_Back n k d r: 1<=d<=2 -> k mod 2=1%nat -> d*2<k<2^n ->
  cfgL d (LC n k) r -->+ LC n (k-d*2) |> r.
Proof.
  intros Hd Hodd HK; destruct d as [|[|[|d]]]; try lia; unfold cfgL.
  - destruct n as [|n]; [cbn in HK; lia|].
    destruct (mod2 k) as [a E|a E]; [lia|].
    destruct a as [|a]; [lia|].
    applys_eq (LC_A n a r); flia.
  - destruct n as [|[|n]]; try (cbn in HK; lia).
    destruct (mod4 k) as [a E|a E|a E|a E]; try lia;
      destruct a as [|a]; try lia.
    + applys_eq (LC_B1 n a r); flia; try arith.
    + applys_eq (LC_B0 n a r); flia; try arith.
Qed.
Lemma MC_Inc l h m d r: Inc m d -> m+1<2^(h+1) ->
  l |> MC h m r -->+ cfgL d l (MC h (m+1) r).
Proof.
  intros HD HM; destruct (Inc_split _ _ HD) as [q [i [-> ->]]].
  replace ((q*2+1)*2^i-1+1) with ((q*2+1)*2^i) in * by nia.
  assert (HI: 2^i<2^(h+1)) by nia.
  apply Nat.pow_lt_mono_r_iff in HI; [|lia].
  remember (h-i) as j; replace h with (j+i) in * by lia.
  unfold MC; rewrite BinDec2_mulpow2sub1,BinDec2_mulpow2 by arith.
  cbn [List.app]; unfold cfgL; follow_rule RInc.
Qed.

Lemma Calls (T:nat->Stream Sym) b
  (Step: forall l m d, Inc m d -> m<b -> l |> T m -->+ cfgL d l (T (m+1)))
  n k m w j v: Num m w -> Num (m+j) v -> k mod 2=1%nat ->
  k+(v-w)*2<2^n -> m+j<=b ->
  LC n (k+(v-w)*2) |> T m -->* LC n k |> T (m+j).
Proof.
  gen m w; induction j as [|j IH]; intros m w HW HV Hk HK Hb.
  - assert (v=w) by (eapply (Num_unique m); [applys_eq HV; flia|exact HW]); subst.
    applys_eq (evstep_refl tm (LC n k |> T m)); flia.
  - destruct (Num_succ _ _ HW) as [d [HD HI]].
    pose proof (Inc_bounds _ _ HD) as Hd.
    pose proof (Num_mono _ _ HI _ _ HV ltac:(lia)) as Hwv.
    eapply evstep_trans; [apply progress_evstep,Step; [exact HD|lia]|].
    eapply evstep_trans; [apply progress_evstep,LC_Back; [exact Hd|lia|lia]|].
    applys_eq (IH (m+1) (w+d)); try eassumption; flia.
    applys_eq HV; flia.
Qed.
Lemma RC_Calls n k m w j v: Num m w -> Num (m+j) v -> k mod 2=1%nat ->
  k+(v-w)*2<2^n ->
  LC n (k+(v-w)*2) |> RC m -->* LC n k |> RC (m+j).
Proof. intros; eapply Calls with (b:=m+j); eauto using RC_Inc. Qed.
Lemma MC_Calls n k h m w j v r: Num m w -> Num (m+j) v -> k mod 2=1%nat ->
  k+(v-w)*2<2^n -> m+j<2^(h+1) ->
  LC n (k+(v-w)*2) |> MC h m r -->* LC n k |> MC h (m+j) r.
Proof.
  intros; eapply Calls with (T:=fun m=>MC h m r) (b:=2^(h+1)-1); try eassumption; [|lia].
  intros; apply MC_Inc; [assumption|lia].
Qed.

Lemma Marker l r i h:
  l <* ld0 <* ld1^^i |> rd1^^h *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(1+h+i) |> r.
Proof.
  eapply evstep_progress_trans; [apply RDigits|].
  follow10 R110; eapply evstep_trans; [apply (LOnes _ _ 2)|].
  st; rewrite lpow_add'.
  follow100 LInc; eapply evstep_trans; [apply (ROnes _ _ 1)|]; st; finish.
Qed.
Lemma LC_Marker n j h r: 0<j<2^n ->
  LC n j |> rd1^^h *> [1;1;0] *> r -->+
  LC (n+(h+1)) (j*2^(h+1)-1) |> r.
Proof.
  intros HJ; destruct j as [|j]; [lia|].
  destruct (LC_split n j) as [l [i [HA HB]]]; [lia|].
  replace (h+1) with (1+h) by lia.
  replace (S j*2^(1+h)-1) with ((j+1)*2^(1+h)-1) by lia.
  unfold LC; rewrite BinDec_mulpow2sub1' by arith.
  unfold LC in HA,HB; unfold Sym in *; cbn [Nat.add] in HA; rewrite HA,HB.
  follow_rule Marker.
Qed.
Lemma Absorb_step n k t u h j: t<=1 -> k mod 2=1%nat -> k<2^n ->
  0<j -> k+t*2=Full (h+1)*2+j ->
  LC n k |> Bit t *> RC ((u*2+1)*2^h) -->+
  LC (n+(h+1)) (j*2^(h+1)-1) |> Bit 0 *> RC u.
Proof.
  intros HT HK HC HJ E.
  assert (HF: t<=Full (h+1)).
  { pose proof (Full_spec (h+1)); assert (2<=2^(h+1)) by arith; lia. }
  assert (HB: t<=2^(h+1)-1) by (rewrite pow2_S; lia).
  rewrite RC_shift by assumption.
  eapply evstep_progress_trans with (c':=LC n j |> MC h (2^(h+1)-1) (rd1 *> RC u)).
  - applys_eq (MC_Calls n j h t t (2^(h+1)-1-t) (Full (h+1)) (rd1 *> RC u));
      try apply Num_small; try applys_eq (Full_num (h+1)); flia.
  - unfold MC; rewrite BinDec2_full; cbn [List.app Bit]; st.
    eapply progress_evstep_trans; [apply LC_Marker; lia|finish].
Qed.
Lemma Absorb_spec u k t l K: Absorb u k t l K -> forall n,
  k mod 2=1%nat -> k<2^n ->
  LC n k |> Bit t *> RC u -->* LC (n+l) K |> 0inf.
Proof.
  induction 1 as [k|u k t l j K h HT HJ E HA IH]; intros n HK HC.
  - unfold Bit,RC; rewrite Nat.add_0_r; st; finish.
  - eapply evstep_trans; [apply progress_evstep,Absorb_step; eassumption|].
    assert (HS: 2<=2^(h+1)) by arith.
    assert (HF: t<=Full (h+1)) by (pose proof (Full_spec (h+1)); lia).
    applys_eq (IH (n+(h+1))); flia; try arith.
Qed.

Lemma Overflow_spec n k d t r: Overflow k d t -> 2<=n ->
  cfgL d (LC n k) r -->+ LC n (2^n-1) |> Bit t *> r.
Proof.
  intros HO Hn; destruct HO; unfold cfgL; cbn [Bit].
  - remember (n-1) as h; replace n with (h+1) in * by lia.
    change (LC (h+1) (0*2+1) <a| r -->+ LC (h+1) (2^(h+1)-1) |> [1] *> r).
    unfold LC; rw_Bin; try solve [arith].
    applys_eq (AOne r h); flia.
  - remember (n-1) as h; replace n with (h+1) in * by lia.
    change (LC (h+1) (0*2+1) <b| r -->+ LC (h+1) (2^(h+1)-1) |> [0] *> r).
    unfold LC; rw_Bin; try solve [arith].
    applys_eq (BOne r h); flia.
  - remember (n-2) as h; replace n with (h+1+1) in * by lia.
    change (LC (h+1+1) ((0*2+1)*2+1) <b| r -->+ LC (h+1+1) (2^(h+1+1)-1) |> [1] *> r).
    unfold LC; rw_Bin; try solve [arith].
    applys_eq (BThree r h); flia.
Qed.
Lemma Round_spec n k m n' k' m': Round n k m n' k' m' -> 2<=n ->
  LC n k |> RC m -->+ LC n' k' |> RC m'.
Proof.
  destruct 1 as [n k m d t l K m' w' d' k' HD HO HA HW HD' EK Hk' Hguard]; intros Hn.
  assert (Hodd: (2^n-1) mod 2=1%nat) by (destruct n; [lia|cbn [Nat.pow]; lia]).
  follow10 (RC_Inc (LC n k) m d HD).
  eapply evstep_trans; [apply progress_evstep,Overflow_spec; eassumption|].
  eapply evstep_trans; [apply Absorb_spec; [exact HA|exact Hodd|lia]|].
  pose proof (Absorb_capacity _ _ _ _ _ HA n ltac:(lia)) as Hcap.
  applys_eq (RC_Calls (n+l) k' O O m' w'); try assumption; try constructor; flia.
Qed.
Inductive P: Q*tape -> Prop :=
| PI n k m: Region n k m -> P (LC n k |> RC m).
Lemma closed c: P c -> exists c', c -->+ c' /\ P c'.
Proof.
  destruct 1 as [n k m HR].
  assert (Hn: 2<=n) by (inversion HR; lia).
  destruct (Round_closed _ _ _ HR) as [n' [k' [m' [HS [HR' HE]]]]].
  eexists; split; [eapply Round_spec; eassumption|constructor; exact HR'].
Qed.
Theorem region_nonhalt n k m: Region n k m -> ~halts tm (LC n k |> RC m).
Proof.
  intros HR; eapply progress_nonhalt_cond with (C:=fun c=>c) (P:=P);
    [apply closed|constructor; exact HR].
Qed.
End Core.

Import BusyCoq.Individual62 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String.
End SOC_ExWeighted.

(* SOC_ExWeighted.TM15 *)
Module TM114.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat Wf_nat Compare_dec.

Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat NArith Wf_nat.

Import BusyCoq.Individual62 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String.

Import SOC_ExWeighted.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_0LF0LD_0RE0LC_1LC1RB_1RA0RE").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <a| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l <b| r" := (l <{{C}} [0] *> r) (at level 30).
Notation "l <c| r" := (l <{{F}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Lemma RInc0 l r n:
  l |> [1;0;0]^^(n*2) *> [0] *> r -->+ l <a| [0;0;0]^^(n*2) *> [1] *> r.
Proof. es. Qed.
Lemma RInc1 l r n:
  l |> [1;0;0]^^(1+n*2) *> [0] *> r -->+ l <b| [0;0;0]^^(1+n*2) *> [1] *> r.
Proof. es. Qed.
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <c| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma AInc l r n:
  l <* ld0 <* ld1^^n <* ld0 <a| r -->+ l <* ld1 <* ld0^^n <* ld0 |> r.
Proof. es. Qed.
Lemma BInc0 l r n:
  l <* ld0 <* ld1^^n <* ld0 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld0 <* ld0 |> r.
Proof. es. Qed.
Lemma BInc1 l r n:
  l <* ld0 <* ld1^^n <* ld1 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma LOnes l r n:
  l <* <[1]^^n <c| r -[tm]->* l <c| [1]^^n *> r.
Proof. es. Qed.
Lemma ROnes l r n:
  l |> [1;1;1]^^n *> r -[tm]->* l <* ld0^^n |> r.
Proof. es. Qed.
Lemma RDigits l r n:
  l |> [1;0;0]^^n *> r -[tm]->* l <* ld1^^n |> r.
Proof. es. Qed.
Lemma R110 l r: l |> [1;1;0] *> r -->+ l <* <[1;1] <c| [1] *> r.
Proof. es. Qed.
Lemma AOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <a| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [1] *> r.
Proof. es. Qed.
Lemma BOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.
Lemma BThree r n:
  0inf <* [1] <* ld1^^n <* ld0 <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(2+n) |> [1] *> r.
Proof. es. Qed.
Lemma init_word:
  c0 -[tm]->* 0inf <* [1] <* ld1^^8 <* ld0 |> [1;0;0;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.

Lemma init_counter: c0 -[tm]->* LC 9 1 <* [1] {{B}}> RC 157.
Proof.
  change (LC 9 1) with (LC (8+1) 1); rewrite LC_one.
  applys_eq init_word; vm_compute; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  eapply region_nonhalt with (QA:=D) (QB:=C) (QC:=F);
    eauto using RInc0, RInc1,
      LInc, AInc,
      BInc0, BInc1,
      LOnes, ROnes,
      RDigits, R110,
      AOne, BOne,
      BThree, Weight.Region_seed_15_16.
Qed.
End TM114.

(* SOC_ExWeighted.TM16 *)
Module TM115.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat Wf_nat Compare_dec.

Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat NArith Wf_nat.

Import BusyCoq.Individual62 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String.

Import SOC_ExWeighted.

Definition tm := Eval compute in (TM_from_str "1LB0LC_1LC1RD_0LD0LA_1RE0RF_1RB---_1LC1RB").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <a| r" := (l <{{A}} [0] *> r) (at level 30).
Notation "l <b| r" := (l <{{C}} [0] *> r) (at level 30).
Notation "l <c| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Lemma RInc0 l r n:
  l |> [1;0;0]^^(n*2) *> [0] *> r -->+ l <a| [0;0;0]^^(n*2) *> [1] *> r.
Proof. es. Qed.
Lemma RInc1 l r n:
  l |> [1;0;0]^^(1+n*2) *> [0] *> r -->+ l <b| [0;0;0]^^(1+n*2) *> [1] *> r.
Proof. es. Qed.
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <c| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma AInc l r n:
  l <* ld0 <* ld1^^n <* ld0 <a| r -->+ l <* ld1 <* ld0^^n <* ld0 |> r.
Proof. es. Qed.
Lemma BInc0 l r n:
  l <* ld0 <* ld1^^n <* ld0 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld0 <* ld0 |> r.
Proof. es. Qed.
Lemma BInc1 l r n:
  l <* ld0 <* ld1^^n <* ld1 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma LOnes l r n:
  l <* <[1]^^n <c| r -[tm]->* l <c| [1]^^n *> r.
Proof. es. Qed.
Lemma ROnes l r n:
  l |> [1;1;1]^^n *> r -[tm]->* l <* ld0^^n |> r.
Proof. es. Qed.
Lemma RDigits l r n:
  l |> [1;0;0]^^n *> r -[tm]->* l <* ld1^^n |> r.
Proof. es. Qed.
Lemma R110 l r: l |> [1;1;0] *> r -->+ l <* <[1;1] <c| [1] *> r.
Proof. es. Qed.
Lemma AOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <a| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [1] *> r.
Proof. es. Qed.
Lemma BOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.
Lemma BThree r n:
  0inf <* [1] <* ld1^^n <* ld0 <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(2+n) |> [1] *> r.
Proof. es. Qed.
Lemma init_word:
  c0 -[tm]->* 0inf <* [1] <* ld1^^8 <* ld0 |> [1;0;0;0;0;0;1;0;0;1;0;0;1;0;0;0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.

Lemma init_counter: c0 -[tm]->* LC 9 1 <* [1] {{B}}> RC 157.
Proof.
  change (LC 9 1) with (LC (8+1) 1); rewrite LC_one.
  applys_eq init_word; vm_compute; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  eapply region_nonhalt with (QA:=A) (QB:=C) (QC:=D);
    eauto using RInc0, RInc1,
      LInc, AInc,
      BInc0, BInc1,
      LOnes, ROnes,
      RDigits, R110,
      AOne, BOne,
      BThree, Weight.Region_seed_15_16.
Qed.
End TM115.

(* SOC_ExWeighted.TM18 *)
Module TM116.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat Wf_nat Compare_dec.

Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.DivModCases.
Import ZifyNat Lia PeanoNat NArith Wf_nat.

Import BusyCoq.Individual62 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String.

Import SOC_ExWeighted.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0LE0LD_1LB0LC_1RA0RF_1LC1RB").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <a| r" := (l <{{D}} [0] *> r) (at level 30).
Notation "l <b| r" := (l <{{C}} [0] *> r) (at level 30).
Notation "l <c| r" := (l <{{E}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{B}}> r) (at level 30).
Lemma RInc0 l r n:
  l |> [1;0;0]^^(n*2) *> [0] *> r -->+ l <a| [0;0;0]^^(n*2) *> [1] *> r.
Proof. es. Qed.
Lemma RInc1 l r n:
  l |> [1;0;0]^^(1+n*2) *> [0] *> r -->+ l <b| [0;0;0]^^(1+n*2) *> [1] *> r.
Proof. es. Qed.
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <c| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma AInc l r n:
  l <* ld0 <* ld1^^n <* ld0 <a| r -->+ l <* ld1 <* ld0^^n <* ld0 |> r.
Proof. es. Qed.
Lemma BInc0 l r n:
  l <* ld0 <* ld1^^n <* ld0 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld0 <* ld0 |> r.
Proof. es. Qed.
Lemma BInc1 l r n:
  l <* ld0 <* ld1^^n <* ld1 <* ld0 <b| r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0 |> r.
Proof. es. Qed.
Lemma LOnes l r n:
  l <* <[1]^^n <c| r -[tm]->* l <c| [1]^^n *> r.
Proof. es. Qed.
Lemma ROnes l r n:
  l |> [1;1;1]^^n *> r -[tm]->* l <* ld0^^n |> r.
Proof. es. Qed.
Lemma RDigits l r n:
  l |> [1;0;0]^^n *> r -[tm]->* l <* ld1^^n |> r.
Proof. es. Qed.
Lemma R110 l r: l |> [1;1;0] *> r -->+ l <* <[1;1] <c| [1] *> r.
Proof. es. Qed.
Lemma AOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <a| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [1] *> r.
Proof. es. Qed.
Lemma BOne r n:
  0inf <* [1] <* ld1^^n <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.
Lemma BThree r n:
  0inf <* [1] <* ld1^^n <* ld0 <* ld0 <b| r -->+
  0inf <* [1] <* ld0^^(2+n) |> [1] *> r.
Proof. es. Qed.
Lemma init_word:
  c0 -[tm]->* 0inf <* [1] <* ld1^^12 <* ld0 |> [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;1;0;0;0;0;0;0;0;0;1;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.

Lemma init_counter: c0 -[tm]->* LC 13 1 <* [1] {{B}}> RC 2657.
Proof.
  change (LC 13 1) with (LC (12+1) 1); rewrite LC_one.
  applys_eq init_word; vm_compute; reflexivity.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  eapply region_nonhalt with (QA:=D) (QB:=C) (QC:=E);
    eauto using RInc0, RInc1,
      LInc, AInc,
      BInc0, BInc1,
      LOnes, ROnes,
      RDigits, R110,
      AOne, BOne,
      BThree, Weight.Region_seed_18.
Qed.
End TM116.
