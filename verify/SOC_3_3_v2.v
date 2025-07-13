From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC' len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> BinInc rd1 m). 

Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD---_1RA0LD_1RD1RF_1LD0RB").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 6 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM48.


Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1RA---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 6 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM49.


Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RD_1LA---_1RF1RE_1LF0RB_1RA0LF").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{E}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 6 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM50.


Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_0RD1RF_1LE0RC_1RB0LE_1RA1RD").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 13 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM55.


Module TM56.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA---_1RA1RF_1LA0RC").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 13 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM56.


Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_1RD1RE_1LB---_1RA1RF_1LA0RC").
(* similar to TM35 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 13 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM57.


Module TM35.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_1RC---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).
Notation "l |2> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(2+i+lenR)) ((k*2+1)*2^(2+i+lenR)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (2+i+lenR) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_S lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)) |2> RC m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  remember (1+i) as v1.
  rw_Bin.
  2,3: solve_pow2_lt; lia.
  subst.
  es.
Qed.

Lemma RC_Ov2_O lenL k i m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2^i*2) -->+
  LC lenL k <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma RC_Ov2_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC lenL k <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) (((2^lenL-1)*2+1)*2^i*2) |2> RC n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  2,3,4: solve_pow2_lt.
  es.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
| cfgR2(lenL k m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
| cfgR2 lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 0 <= k+n < 2^lenL
| cfgR lenL k n => 0 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR2 lenL k n => n+1 <= k /\ k+1 < 2^lenL
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      eexists (cfgR2 _ _ _). split.
      1: apply LC_Ov.
      split.
      2: solve_pow2_lt.
      do 2 (apply mulpos_le_r; try lia).
      pose proof (pow2sub1_lt x i (2^lenL)).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      eexists (cfgR2 _ _ _). split.
      1: apply RC'_Ov; lia.
      split.
      2: {
        replace (2+i+lenR) with (i+lenR+1+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x i (k+1)).
      lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
  - lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by (cbn; lia).
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov2_O_0; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov2_O; lia.
        split.
        2: solve_pow2_lt.
        split.
        2: lia.
        pose proof (split_bound_v2 x0 i).
        lia.
    + eexists (cfgR2 _ _ _). split.
      1: apply RC_Ov2_S; lia.
      split.
      2: {
        replace (1+i) with (i+1) by lia.
        solve_pow2_lt.
      }
      apply mulpos_le_r; try lia.
      pose proof (pow2sub1_lt x (S i) k).
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 7 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM35.


Module TM82.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1LE1RD_1RB1RF_0LF0LE_1RA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov_SS lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_SS_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S lenL k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S_0 lenL k i:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_O lenL k i i0 m:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_O_0 lenL k i:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC 3.
Proof.
  pose O as i0.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x;
      destruct lenR as [|[|lenR]].
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_O_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_S_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_SS_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          rewrite nz_sub1add.
          2: rewrite <-Nat.neq_mul_0; lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          match goal with
          | |- ?a*2+3<_ => replace (a*2+3) with ((a+1)*2+1) by lia
          end.
          apply lt_mul2add1.
          rewrite <-Nat.add_assoc; cbn.
          match goal with
          | |- ?a*2+2<_ => replace (a*2+2) with ((a+1)*2) by lia
          end.
          apply lt_mul2.
          rewrite Nat.sub_add by lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_SS; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 3 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM82.


Module TM91.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_0RD0RA_1LE---_1RF1RC_1RA1LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov_SS lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_SS_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S lenL k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S_0 lenL k i:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_O lenL k i i0 m:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_O_0 lenL k i:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC 3.
Proof.
  pose O as i0.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x;
      destruct lenR as [|[|lenR]].
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_O_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_S_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_SS_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          rewrite nz_sub1add.
          2: rewrite <-Nat.neq_mul_0; lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          match goal with
          | |- ?a*2+3<_ => replace (a*2+3) with ((a+1)*2+1) by lia
          end.
          apply lt_mul2add1.
          rewrite <-Nat.add_assoc; cbn.
          match goal with
          | |- ?a*2+2<_ => replace (a*2+2) with ((a+1)*2) by lia
          end.
          apply lt_mul2.
          rewrite Nat.sub_add by lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_SS; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 54 4)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM91.


Module TM92.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RA_0LE0LD_1RF0RC_1LB---").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov_SS lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_SS_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S lenL k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S_0 lenL k i:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_O lenL k i i0 m:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_O_0 lenL k i:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC 3.
Proof.
  pose O as i0.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x;
      destruct lenR as [|[|lenR]].
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_O_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_S_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_SS_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          rewrite nz_sub1add.
          2: rewrite <-Nat.neq_mul_0; lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          match goal with
          | |- ?a*2+3<_ => replace (a*2+3) with ((a+1)*2+1) by lia
          end.
          apply lt_mul2add1.
          rewrite <-Nat.add_assoc; cbn.
          match goal with
          | |- ?a*2+2<_ => replace (a*2+2) with ((a+1)*2) by lia
          end.
          apply lt_mul2.
          rewrite Nat.sub_add by lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_SS; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 54 4)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM92.


Module TM104.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0LE0LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov_SS lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_SS_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S lenL k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S_0 lenL k i:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_O lenL k i i0 m:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_O_0 lenL k i:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC 3.
Proof.
  pose O as i0.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x;
      destruct lenR as [|[|lenR]].
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_O_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_S_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_SS_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          rewrite nz_sub1add.
          2: rewrite <-Nat.neq_mul_0; lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          match goal with
          | |- ?a*2+3<_ => replace (a*2+3) with ((a+1)*2+1) by lia
          end.
          apply lt_mul2add1.
          rewrite <-Nat.add_assoc; cbn.
          match goal with
          | |- ?a*2+2<_ => replace (a*2+2) with ((a+1)*2) by lia
          end.
          apply lt_mul2.
          rewrite Nat.sub_add by lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_SS; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 67 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM104.


Module TM105.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1LC_1LF1RE_1RC1RA_0LA0LF").
(* similar to TM82 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov_SS lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_SS_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (2+lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1+lenR+1+i) (((((k*2+1)*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S lenL k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_S_0 lenL k i:
  k<2^lenL ->
  LC lenL k |> RC' 1 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+1+(1+i)) ((k*2+1)*2^(1+i)-1) <| RC 3.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_O lenL k i i0 m:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 ((((m*2+1)*2^i0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC' (i0+1) ((2^i0-1)*2*2) m.
Proof.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_O_0 lenL k i:
  1<=k<2^lenL ->
  LC lenL k |> RC' 0 0 (((0*2+1)*2^i-1)) -->+
  LC (lenL+(1+i)) ((k)*2^(1+i)-1) <| RC 3.
Proof.
  pose O as i0.
  intros Hk.
  lowbit_cases k.
  1: lia.
  rewrite (lowbit_split x i1 lenL) by lia.
  pose proof (lowbit_split_lt x i1 lenL).
  unfold LC,RC,RC'.
  rw_Bin.
  rewrite <-(Nat.sub_add 1 ((x*2+1)*2^i1)) by lia.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
  rewrite Nat.sub_add; try lia.
  solve_pow2_lt; try lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x;
      destruct lenR as [|[|lenR]].
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_O_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_S_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        destruct i as [|i].
        1: cbn in *; lia.
        assert (k<>O) by lia.
        assert ((k+1)*(2^(2+i))<=2^lenL*2^(2+i)). {
          apply Nat.mul_le_mono_pos_r; cbn; lia.
        }
        cbn in *; lia.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_SS_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          rewrite nz_sub1add.
          2: rewrite <-Nat.neq_mul_0; lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          match goal with
          | |- ?a*2+3<_ => replace (a*2+3) with ((a+1)*2+1) by lia
          end.
          apply lt_mul2add1.
          rewrite <-Nat.add_assoc; cbn.
          match goal with
          | |- ?a*2+2<_ => replace (a*2+2) with ((a+1)*2) by lia
          end.
          apply lt_mul2.
          rewrite Nat.sub_add by lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        rewrite Nat.pow_succ_r by lia.
        assert (((x0*2+1)*2^i0*2+1)*2*2^i<=k*2) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        apply Nat.le_add_le_sub_r.
        rewrite Nat.mul_assoc.
        apply mulpos_le_r.
        1: lia.
        epose proof (Nat.le_mul_r (x0*2) (2^i0)).
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov_SS; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 67 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM105.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_0RD1RA_1LA---_1LF0RC_1RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 124 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1RD1RA_1LB---_1LF0RC_1RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{E}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 124 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0LB_1RD1RA_1LE---_1RC1LE_1LB0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 3 <= k+n+1 < 2^lenL
| cfgR lenL k n => 3 <= k+n+2 < 2^lenL
| cfgL' lenL k lenR n m => n+m+2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        rewrite nz_sub1add.
        2: rewrite <-Nat.neq_mul_0; lia.
        rewrite <-Nat.add_assoc; cbn.
        destruct i as [|i].
        -- apply muladd_lt; try lia.
          rewrite <-Nat.add_assoc; cbn.
          apply muladd_lt; try lia.
          apply muladd_lt; try lia.
        -- rewrite Nat.pow_succ_r by lia.
          repeat rewrite Nat.mul_assoc.
          cbn in *.
          apply muladd_lt; try lia.
          solve_pow2_lt; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 124 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM11.


Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O lenL n i i0:
  LC lenL O <| RC (((n*2+1)*2^i0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC' (i0+1) ((2^i0-1)*2*2+1) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_O; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O_0 lenL i:
  LC lenL O <| RC ((0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC 2.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  - epose proof (LOv_O 0inf lenL i) as I1.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    follow10 I1.
    finish.
  - remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S lenL n i i0 i1:
  LC lenL O <| RC ((((((n*2+1)*2^i1)*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC' (i1) ((2^i1-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S_0 lenL i i0:
  LC lenL O <| RC ((((0*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; rewrite Nat.add_comm; simpl_tape; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; try lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+2 /\ k<2^lenL
| cfgR lenL k n => 0 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbitS_cases x.
      destruct i0 as [|i0].
      * replace ((x0*2+1)*2^0-1) with (x0*2) in * by (cbn; lia).
        lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_O_0.
           remember (lenL+i) as v1.
           rewrite pow2_S.
           lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_O.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           rewrite Nat.pow_add_r.
           pose proof (split_bound_v2 x (i0+1)) as E1.
           rewrite pow2_S,Nat.mul_assoc in E1.
           remember ((x*2+1)*2^i0*2*2+1) as v1.
           epose proof (Nat.le_mul_r v1 (2^i)).
           epose proof (Nat.le_mul_r (2^lenL) (2^i)).
           lia.
      * lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_S_0.
           remember (lenL+i) as v1.
           repeat split; try lia.
           2: solve_pow2_lt.
           match goal with
           | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
           end; lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_S.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           pose proof (split_bound_v2 x i1).
           remember ((x*2+1)*2^i1*2+1) as v1.
           assert (v1<=(((2 ^ (lenL + i) - 1) * 2 * 2 + 1) * 2 + 1) * 2 ^ i0). {
             apply mulpos_le_r. 1: lia.
             rewrite Nat.pow_add_r.
             rewrite Nat.pow_succ_r in HP by lia.
             epose proof (Nat.le_mul_r (v1) (2^i0)).
             assert ((((v1 * (2 * 2 ^ i0) - 1) * 2 + 1) * 2 ^ i) <= 2 ^ lenL + 2) as E1 by lia. 
             epose proof (mulpos_le_l E1) as E2.
             assert (v1<=2^lenL+1) by lia.
             epose proof (Nat.le_mul_r (2^lenL) (2^i)).
             lia.
           }
           lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        2: solve_pow2_lt; lia.
        match goal with
        | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
        end.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k+1) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 3 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM28.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O lenL n i i0:
  LC lenL O <| RC (((n*2+1)*2^i0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC' (i0+1) ((2^i0-1)*2*2+1) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_O; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O_0 lenL i:
  LC lenL O <| RC ((0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC 2.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  - epose proof (LOv_O 0inf lenL i) as I1.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    follow10 I1.
    finish.
  - remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S lenL n i i0 i1:
  LC lenL O <| RC ((((((n*2+1)*2^i1)*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC' (i1) ((2^i1-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S_0 lenL i i0:
  LC lenL O <| RC ((((0*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; rewrite Nat.add_comm; simpl_tape; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; try lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+2 /\ k<2^lenL
| cfgR lenL k n => 0 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbitS_cases x.
      destruct i0 as [|i0].
      * replace ((x0*2+1)*2^0-1) with (x0*2) in * by (cbn; lia).
        lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_O_0.
           remember (lenL+i) as v1.
           rewrite pow2_S.
           lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_O.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           rewrite Nat.pow_add_r.
           pose proof (split_bound_v2 x (i0+1)) as E1.
           rewrite pow2_S,Nat.mul_assoc in E1.
           remember ((x*2+1)*2^i0*2*2+1) as v1.
           epose proof (Nat.le_mul_r v1 (2^i)).
           epose proof (Nat.le_mul_r (2^lenL) (2^i)).
           lia.
      * lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_S_0.
           remember (lenL+i) as v1.
           repeat split; try lia.
           2: solve_pow2_lt.
           match goal with
           | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
           end; lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_S.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           pose proof (split_bound_v2 x i1).
           remember ((x*2+1)*2^i1*2+1) as v1.
           assert (v1<=(((2 ^ (lenL + i) - 1) * 2 * 2 + 1) * 2 + 1) * 2 ^ i0). {
             apply mulpos_le_r. 1: lia.
             rewrite Nat.pow_add_r.
             rewrite Nat.pow_succ_r in HP by lia.
             epose proof (Nat.le_mul_r (v1) (2^i0)).
             assert ((((v1 * (2 * 2 ^ i0) - 1) * 2 + 1) * 2 ^ i) <= 2 ^ lenL + 2) as E1 by lia. 
             epose proof (mulpos_le_l E1) as E2.
             assert (v1<=2^lenL+1) by lia.
             epose proof (Nat.le_mul_r (2^lenL) (2^i)).
             lia.
           }
           lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        2: solve_pow2_lt; lia.
        match goal with
        | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
        end.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k+1) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 3 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM29.


Module TM102.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O lenL n i i0:
  LC lenL O <| RC (((n*2+1)*2^i0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC' (i0+1) ((2^i0-1)*2*2+1) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_O; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O_0 lenL i:
  LC lenL O <| RC ((0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC 2.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  - epose proof (LOv_O 0inf lenL i) as I1.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    follow10 I1.
    finish.
  - remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S lenL n i i0 i1:
  LC lenL O <| RC ((((((n*2+1)*2^i1)*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC' (i1) ((2^i1-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S_0 lenL i i0:
  LC lenL O <| RC ((((0*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; rewrite Nat.add_comm; simpl_tape; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; try lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+2 /\ k<2^lenL
| cfgR lenL k n => 0 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbitS_cases x.
      destruct i0 as [|i0].
      * replace ((x0*2+1)*2^0-1) with (x0*2) in * by (cbn; lia).
        lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_O_0.
           remember (lenL+i) as v1.
           rewrite pow2_S.
           lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_O.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           rewrite Nat.pow_add_r.
           pose proof (split_bound_v2 x (i0+1)) as E1.
           rewrite pow2_S,Nat.mul_assoc in E1.
           remember ((x*2+1)*2^i0*2*2+1) as v1.
           epose proof (Nat.le_mul_r v1 (2^i)).
           epose proof (Nat.le_mul_r (2^lenL) (2^i)).
           lia.
      * lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_S_0.
           remember (lenL+i) as v1.
           repeat split; try lia.
           2: solve_pow2_lt.
           match goal with
           | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
           end; lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_S.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           pose proof (split_bound_v2 x i1).
           remember ((x*2+1)*2^i1*2+1) as v1.
           assert (v1<=(((2 ^ (lenL + i) - 1) * 2 * 2 + 1) * 2 + 1) * 2 ^ i0). {
             apply mulpos_le_r. 1: lia.
             rewrite Nat.pow_add_r.
             rewrite Nat.pow_succ_r in HP by lia.
             epose proof (Nat.le_mul_r (v1) (2^i0)).
             assert ((((v1 * (2 * 2 ^ i0) - 1) * 2 + 1) * 2 ^ i) <= 2 ^ lenL + 2) as E1 by lia. 
             epose proof (mulpos_le_l E1) as E2.
             assert (v1<=2^lenL+1) by lia.
             epose proof (Nat.le_mul_r (2^lenL) (2^i)).
             lia.
           }
           lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        2: solve_pow2_lt; lia.
        match goal with
        | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
        end.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k+1) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM102.


Module TM103.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0RD---").
(* simular to TM102 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n m k:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <* ld0 <* ld1 <* ld0^^k <| [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_O r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> rd0 *> r -->+
  ldh <* ld0^^(m+n) <* ld1 <| rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0^^m <| [1] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR)*2+1)*2^i-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O lenL n i i0:
  LC lenL O <| RC (((n*2+1)*2^i0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC' (i0+1) ((2^i0-1)*2*2+1) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_O; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_O_0 lenL i:
  LC lenL O <| RC ((0*2*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^(lenL+i)-1)*2) <| RC 2.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  - epose proof (LOv_O 0inf lenL i) as I1.
    cbn in *.
    repeat rewrite <-const_unfold in *.
    follow10 I1.
    finish.
  - remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S lenL n i i0 i1:
  LC lenL O <| RC ((((((n*2+1)*2^i1)*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC' (i1) ((2^i1-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_S_0 lenL i i0:
  LC lenL O <| RC ((((0*2+1)*2^(1+i0)-1)*2+1)*2^i-1) -->+
  LC (lenL+i+1+1+1+i0) ((((2^(lenL+i)-1)*2*2+1)*2+1)*2^i0-1) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: follow10 LOv_S; rewrite Nat.add_comm; simpl_tape; finish.
  all: remember (lenL+i) as v1; solve_pow2_lt; try lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+2 /\ k<2^lenL
| cfgR lenL k n => 0 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbitS_cases x.
      destruct i0 as [|i0].
      * replace ((x0*2+1)*2^0-1) with (x0*2) in * by (cbn; lia).
        lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_O_0.
           remember (lenL+i) as v1.
           rewrite pow2_S.
           lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_O.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           rewrite Nat.pow_add_r.
           pose proof (split_bound_v2 x (i0+1)) as E1.
           rewrite pow2_S,Nat.mul_assoc in E1.
           remember ((x*2+1)*2^i0*2*2+1) as v1.
           epose proof (Nat.le_mul_r v1 (2^i)).
           epose proof (Nat.le_mul_r (2^lenL) (2^i)).
           lia.
      * lowbit_cases x0.
        -- eexists (cfgL _ _ _). split.
           1: apply LC_Ov_S_0.
           remember (lenL+i) as v1.
           repeat split; try lia.
           2: solve_pow2_lt.
           match goal with
           | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
           end; lia.
        -- eexists (cfgL' _ _ _ _ _). split.
           1: apply LC_Ov_S.
           repeat split.
           2,3: remember (lenL+i) as v1; solve_pow2_lt.
           pose proof (split_bound_v2 x i1).
           remember ((x*2+1)*2^i1*2+1) as v1.
           assert (v1<=(((2 ^ (lenL + i) - 1) * 2 * 2 + 1) * 2 + 1) * 2 ^ i0). {
             apply mulpos_le_r. 1: lia.
             rewrite Nat.pow_add_r.
             rewrite Nat.pow_succ_r in HP by lia.
             epose proof (Nat.le_mul_r (v1) (2^i0)).
             assert ((((v1 * (2 * 2 ^ i0) - 1) * 2 + 1) * 2 ^ i) <= 2 ^ lenL + 2) as E1 by lia. 
             epose proof (mulpos_le_l E1) as E2.
             assert (v1<=2^lenL+1) by lia.
             epose proof (Nat.le_mul_r (2^lenL) (2^i)).
             lia.
           }
           lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        2: solve_pow2_lt; lia.
        match goal with
        | |- ?a+1 < ?b+2 => assert (a<b) by (solve_pow2_lt; lia)
        end.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply mulpos_le_r. 1: lia.
        assert (((x0*2+1)*2^i0*2+1)*2^i<=k+1) as E1 by lia.
        epose proof (mulpos_le_l E1) as E2.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM103.


Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_1RD---").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2+1) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC 2.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k<2^lenL /\ 2 <= k+n+1 < 2^(lenL)*2 /\ k+n <> 2^lenL
| cfgR lenL k n => lenL<>O /\ k<2^lenL /\ k+n+2 < 2^(lenL)*2 /\ k+n+1 <> 2^lenL
| cfgL' lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=1 -> m=O -> k+1<>2^lenL) /\
    (lenR=1 -> n=O -> m=O -> k+1<>2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S in *.
      repeat split; try lia.
      * pose proof (split_bound_v3 x i lenL).
        lia.
      * intros.
        subst.
        cbn in *; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        -- solve_pow2_lt.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           pose proof (Nat.pow_le_mono_r 2 2 (lenL+1+lenR+i)).
           assert (2<=lenL+1+lenR+i \/ (lenL=0/\lenR=0/\i=0)) as [E1|E1] by lia.
           1: change (2^2) with 4 in *; lia.
           destruct E1 as [E1 [E2 E3]]; subst.
           lia.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           destruct i as [|i].
           2: {
             replace (S i) with (i+1) by lia.
             rewrite pow2_S.
             rewrite Nat.add_assoc.
             rewrite pow2_S.
             lia.
           }
           change (2^0) with 1.
           destruct lenR as [|[|lenR]].
           3: {
             replace (S (S lenR)) with (lenR+1+1) by lia.
             replace (lenL+1+(lenR+1+1)+0) with (lenL+lenR+1+1+1) by lia.
             repeat rewrite pow2_S.
             lia.
           }
           1,2: repeat rewrite Nat.pow_add_r; cbn in *; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1)).
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 22 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM39.


Module TM40.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_1LE---").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2+1) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC 2.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  solve_LOverflow.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k<2^lenL /\ 2 <= k+n+1 < 2^(lenL)*2 /\ k+n <> 2^lenL
| cfgR lenL k n => lenL<>O /\ k<2^lenL /\ k+n+2 < 2^(lenL)*2 /\ k+n+1 <> 2^lenL
| cfgL' lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=1 -> m=O -> k+1<>2^lenL) /\
    (lenR=1 -> n=O -> m=O -> k+1<>2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S in *.
      repeat split; try lia.
      * pose proof (split_bound_v3 x i lenL).
        lia.
      * intros.
        subst.
        cbn in *; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        -- solve_pow2_lt.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           pose proof (Nat.pow_le_mono_r 2 2 (lenL+1+lenR+i)).
           assert (2<=lenL+1+lenR+i \/ (lenL=0/\lenR=0/\i=0)) as [E1|E1] by lia.
           1: change (2^2) with 4 in *; lia.
           destruct E1 as [E1 [E2 E3]]; subst.
           lia.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           destruct i as [|i].
           2: {
             replace (S i) with (i+1) by lia.
             rewrite pow2_S.
             rewrite Nat.add_assoc.
             rewrite pow2_S.
             lia.
           }
           change (2^0) with 1.
           destruct lenR as [|[|lenR]].
           3: {
             replace (S (S lenR)) with (lenR+1+1) by lia.
             replace (lenL+1+(lenR+1+1)+0) with (lenL+lenR+1+1+1) by lia.
             repeat rewrite pow2_S.
             lia.
           }
           1,2: repeat rewrite Nat.pow_add_r; cbn in *; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1)).
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 22 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM40.


Module TM41.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC0RE_0RB1RA_---1RA").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2+1) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC 2.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k<2^lenL /\ 2 <= k+n+1 < 2^(lenL)*2 /\ k+n <> 2^lenL
| cfgR lenL k n => lenL<>O /\ k<2^lenL /\ k+n+2 < 2^(lenL)*2 /\ k+n+1 <> 2^lenL
| cfgL' lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=1 -> m=O -> k+1<>2^lenL) /\
    (lenR=1 -> n=O -> m=O -> k+1<>2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S in *.
      repeat split; try lia.
      * pose proof (split_bound_v3 x i lenL).
        lia.
      * intros.
        subst.
        cbn in *; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        -- solve_pow2_lt.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           pose proof (Nat.pow_le_mono_r 2 2 (lenL+1+lenR+i)).
           assert (2<=lenL+1+lenR+i \/ (lenL=0/\lenR=0/\i=0)) as [E1|E1] by lia.
           1: change (2^2) with 4 in *; lia.
           destruct E1 as [E1 [E2 E3]]; subst.
           lia.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           destruct i as [|i].
           2: {
             replace (S i) with (i+1) by lia.
             rewrite pow2_S.
             rewrite Nat.add_assoc.
             rewrite pow2_S.
             lia.
           }
           change (2^0) with 1.
           destruct lenR as [|[|lenR]].
           3: {
             replace (S (S lenR)) with (lenR+1+1) by lia.
             replace (lenL+1+(lenR+1+1)+0) with (lenL+lenR+1+1+1) by lia.
             repeat rewrite pow2_S.
             lia.
           }
           1,2: repeat rewrite Nat.pow_add_r; cbn in *; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1)).
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 22 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM41.


Module TM42.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA1LC_---1RA").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2+1) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC 2.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k<2^lenL /\ 2 <= k+n+1 < 2^(lenL)*2 /\ k+n <> 2^lenL
| cfgR lenL k n => lenL<>O /\ k<2^lenL /\ k+n+2 < 2^(lenL)*2 /\ k+n+1 <> 2^lenL
| cfgL' lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=1 -> m=O -> k+1<>2^lenL) /\
    (lenR=1 -> n=O -> m=O -> k+1<>2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S in *.
      repeat split; try lia.
      * pose proof (split_bound_v3 x i lenL).
        lia.
      * intros.
        subst.
        cbn in *; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        -- solve_pow2_lt.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           pose proof (Nat.pow_le_mono_r 2 2 (lenL+1+lenR+i)).
           assert (2<=lenL+1+lenR+i \/ (lenL=0/\lenR=0/\i=0)) as [E1|E1] by lia.
           1: change (2^2) with 4 in *; lia.
           destruct E1 as [E1 [E2 E3]]; subst.
           lia.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           destruct i as [|i].
           2: {
             replace (S i) with (i+1) by lia.
             rewrite pow2_S.
             rewrite Nat.add_assoc.
             rewrite pow2_S.
             lia.
           }
           change (2^0) with 1.
           destruct lenR as [|[|lenR]].
           3: {
             replace (S (S lenR)) with (lenR+1+1) by lia.
             replace (lenL+1+(lenR+1+1)+0) with (lenL+lenR+1+1+1) by lia.
             repeat rewrite pow2_S.
             lia.
           }
           1,2: repeat rewrite Nat.pow_add_r; cbn in *; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1)).
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 22 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM42.


Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC0RE_0RB1RA_---1LD").
(* similar to TM24 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{A}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC' (i0+1) ((2^i0-1)*2*2+1) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+i) (((((k*2+1))*2^lenR)+1)*2^i-1) <| RC 2.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k<2^lenL /\ 2 <= k+n+1 < 2^(lenL)*2 /\ k+n <> 2^lenL
| cfgR lenL k n => lenL<>O /\ k<2^lenL /\ k+n+2 < 2^(lenL)*2 /\ k+n+1 <> 2^lenL
| cfgL' lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=1 -> m=O -> k+1<>2^lenL) /\
    (lenR=1 -> n=O -> m=O -> k+1<>2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      rewrite pow2_S in *.
      repeat split; try lia.
      * pose proof (split_bound_v3 x i lenL).
        lia.
      * intros.
        subst.
        cbn in *; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split; try lia.
        -- solve_pow2_lt.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           pose proof (Nat.pow_le_mono_r 2 2 (lenL+1+lenR+i)).
           assert (2<=lenL+1+lenR+i \/ (lenL=0/\lenR=0/\i=0)) as [E1|E1] by lia.
           1: change (2^2) with 4 in *; lia.
           destruct E1 as [E1 [E2 E3]]; subst.
           lia.
        -- assert (((k*2+1)*2^lenR+1)*2^i-1 < 2^(lenL+1+lenR+i)) by solve_pow2_lt.
           destruct i as [|i].
           2: {
             replace (S i) with (i+1) by lia.
             rewrite pow2_S.
             rewrite Nat.add_assoc.
             rewrite pow2_S.
             lia.
           }
           change (2^0) with 1.
           destruct lenR as [|[|lenR]].
           3: {
             replace (S (S lenR)) with (lenR+1+1) by lia.
             replace (lenL+1+(lenR+1+1)+0) with (lenL+lenR+1+1+1) by lia.
             repeat rewrite pow2_S.
             lia.
           }
           1,2: repeat rewrite Nat.pow_add_r; cbn in *; lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt; lia.
        epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1)).
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        epose proof (Nat.le_mul_r (x0) (2^i0)).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 22 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM43.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0LB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM12.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA---_0LA1RF_1LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM24.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM25.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_1RD1RE_1LB---_0LA1RF_1LA0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM26.


Module TM98.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RE_1RD1LC_1LF1RB_0RA0RD_0RA0LF").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM98.


Module TM99.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1LC_1LF1RE_1RC1RA_0LE0LF").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM99.


Module TM109.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC---_1RD1LC_1LA1RE_1RC1RF_1RB0RD").
(* similar to TM12 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  es.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  es.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  es.
Qed.

Lemma RC_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC' (i0) ((2^i0-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; try lia.
Qed.

Lemma RC_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC' (lenR) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) (((((k*2+1))*2^lenR-1)*2+1)*2^i) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov lenL n i i0:
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC' i0 ((2^i0-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Lemma LC_Ov_0 lenL i:
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+i+1) ((2^lenL-1)*2^i*2) <| RC 1.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  1: es.
  all: solve_pow2_lt; lia.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n   < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m   <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (2^lenL) _).
        1: lia.
        epose proof (split_bound_v1 x0 i0 lenL).
        replace ((2^lenL-1)*2^i*2) with ((2^lenL-1)*2*2^i) by lia.
        apply mulpos_le_r. 1: lia.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC_Ov_0; lia.
        repeat split.
        1: apply Nat.le_add_l.
        cbn in HP.
        repeat rewrite Nat.pow_add_r.
        change (2^1) with 2.
        apply muladd_lt. 1: lia.
        match goal with
        | |- (?a-1)*2+1+1<_ => replace ((a-1)*2+1+1) with (a*2) by lia
        end.
        solve_pow2_lt.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        apply mulpos_le_r. 1: lia.
        rewrite <-Nat.add_le_mono_r.
        apply mulpos_le_r. 1: lia.
        apply Nat.le_add_le_sub_r.
        apply mulpos_le_r. 1: lia.
        unshelve epose proof (pow2sub1_lt ((x0*2+1)*2^i0) i (k+1) _).
        1: lia.
        epose proof (split_bound_v2 x0 i0).
        lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM109.


