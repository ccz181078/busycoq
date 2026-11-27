(** * 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC--- does not halt (translated cycler)

    BB(6) holdout, Holdout Guide #38.  From about 2.67e28 steps on the machine is a translated
    cycler with a left record: period 4,126,262,385,607,271,490,126,714 steps, shift
    2,428,193,875,694 cells.  Description, data and the simulators that found it:
    https://github.com/thomasreus-bb/BB6_TC_1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---

    Proof by computation with RWLAccT (RWLAcc with an arbitrary, never-read right end of the tape):
    - [pre]:   the blank tape reaches a restart configuration  0^inf {{C}}> S *> R0;
    - [cycle]: for every R, 0^inf {{C}}> S *> R  reaches  0^inf {{C}}> S *> R'  for some R'.
    Both are checked by the kernel's virtual machine in about 20 seconds. *)

From BusyCoq Require Import RWLAccT62.
(* first 4800 cells of the tape (from the head) at every restart of 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC--- *)
Require Import NArith List.
Import ListNotations.
Definition S48_runs : list (list sym * N) := [
  ([S0;S1;S0;S1;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0], 1%N);
  ([S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0], 79%N);
  ([S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S0;S0;S0;S0;S0], 1%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0], 3%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S1;S1;S0;S0;S0;S0;S0;S0], 1%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0], 1%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1], 1%N);
  ([S0;S0;S1;S1;S0;S0;S1;S0;S0;S1;S0;S0;S0;S1;S1;S0;S0;S1;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S0;S0;S0;S0;S0;S0;S0], 1%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0], 1%N);
  ([S0;S1;S0;S0;S0;S1;S1;S0;S0;S1;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S0;S0;S0;S0;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1], 1%N);
  ([S0;S0;S1;S1;S0;S0;S1;S0;S1;S0;S1;S0;S0;S1;S0;S0;S1;S0;S0;S1;S0;S1;S0;S0;S0;S1;S1;S0;S0;S1;S0;S1;S1;S0;S1;S1;S1;S0;S0;S1], 1%N);
  ([S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S0;S1;S1;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0], 1%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0], 9%N);
  ([S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1], 1%N);
  ([S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1;S0;S0;S1;S1], 18%N)
].


(** Helpers for the non-halting proof of 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---:
    cutting a cell window out of a compressed tape, a bounded cell-level search
    for the restart record, and the glue between both. *)

Require Import List Lia NArith.
Import ListNotations.

Section Window.
Hypothesis tm : TM.

(** take at least [n] cells from the front of a compressed side (counts taken with i = j = 0) *)
Fixpoint take_cells (k n:nat) (ls:RWL) : option (list Sym * RWL) :=
  match n with
  | O => Some ([], ls)
  | S _ =>
    match k with
    | O => None
    | S k =>
      match ls with
      | [] => None
      | (w,(a0,a1),b)::t =>
        match w with
        | [] => None
        | _ =>
          match b with
          | N0 => take_cells k n t
          | Npos p =>
            match take_cells k (n - length w) ((w,(0%N,0%N),N.pred (Npos p))::t) with
            | Some (XA,ls') => Some (w ++ XA, ls')
            | None => None
            end
          end
        end
      end
    end
  end.

Lemma lpow_succ_N {T} (w:list T) (p:positive) (r:Stream T) :
  w ^^ (N.to_nat (Npos p)) *> r = w *> w ^^ (N.to_nat (N.pred (Npos p))) *> r.
Proof.
  replace (N.to_nat (N.pos p)) with (S (N.to_nat (N.pred (N.pos p)))) by lia.
  cbn. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma take_cells_spec k n ls t XA ls':
  take_cells k n ls = Some (XA,ls') ->
  to_side_t 0 0 t ls = XA *> to_side_t 0 0 t ls'.
Proof.
  revert n ls XA ls'.
  induction k as [|k IH]; intros n ls XA ls' H.
  - destruct n; cbn in H; [inversion H; reflexivity | discriminate].
  - destruct n as [|n].
    { cbn in H. inversion H. reflexivity. }
    cbn in H.
    destruct ls as [|[[w [a0 a1]] b] tl]; [discriminate|].
    destruct w as [|x w]; [discriminate|].
    destruct b as [|p].
    + specialize (IH _ _ _ _ H).
      rewrite <-IH.
      unfold to_side_t. cbn [flat_map to_seg].
      replace (N.to_nat a0 * 0 + N.to_nat a1 * 0 + N.to_nat 0)%nat with 0%nat by lia.
      reflexivity.
    + match type of H with context [take_cells k ?m ?l] =>
        destruct (take_cells k m l) as [[XA0 ls0]|] eqn:E end;
        [|discriminate].
      inversion H; subst; clear H.
      specialize (IH _ _ _ _ E).
      unfold to_side_t in *. cbn in IH |- *.
      rewrite Str_app_assoc in IH |- *.
      replace (N.to_nat a0 * 0 + N.to_nat a1 * 0 + Pos.to_nat p)%nat with (S (N.to_nat (Pos.pred_N p))) by lia.
      cbn [lpow].
      rewrite Str_app_assoc.
      rewrite IH.
      change (x >> (w ++ XA0) *> flat_map (to_seg 0 0) ls' *> t) with (((x::w) ++ XA0) *> flat_map (to_seg 0 0) ls' *> t).
      rewrite Str_app_assoc.
      reflexivity.
Qed.

Definition flat0 (ls:RWL) : list Sym := flat_map (to_seg 0 0) ls.

Lemma to_side_flat0 t ls: to_side_t 0 0 t ls = flat0 ls *> t.
Proof. reflexivity. Qed.

(** the bounded window of a compressed configuration *)
Definition window (k n:nat) (c:RWL_config) : option (BoundedConfig.T * RWL) :=
  let '(l,r,s,sgn) := c in
  match sgn with
  | R =>
    match take_cells k n r with
    | Some (XB,rest) => Some (BoundedConfig.Build_T (flat0 l) XB s R, rest)
    | None => None
    end
  | L =>
    match take_cells k n l with
    | Some (XB,rest) => Some (BoundedConfig.Build_T XB (flat0 r) s L, rest)
    | None => None
    end
  end.

Lemma window_spec rt k n c x rest:
  window k n c = Some (x,rest) ->
  to_config rt 0 0 c = BoundedConfig.to_config x (Streams.const s0) (to_side_t 0 0 rt rest).
Proof.
  destruct c as [[[l r] s] sgn].
  destruct sgn; cbn.
  - destruct (take_cells k n l) as [[XB rest0]|] eqn:E; [|discriminate].
    intros H; inversion H; subst; clear H.
    rewrite (take_cells_spec _ _ _ _ _ _ E).
    reflexivity.
  - destruct (take_cells k n r) as [[XB rest0]|] eqn:E; [|discriminate].
    intros H; inversion H; subst; clear H.
    rewrite (take_cells_spec _ _ _ _ _ _ E).
    reflexivity.
Qed.

(** bounded cell-level search for a configuration satisfying [cond] (after at least one step) *)
Fixpoint find_bounded (cond:BoundedConfig.T -> bool) (k:nat) (x:BoundedConfig.T) : option BoundedConfig.T :=
  match k with
  | O => None
  | S k =>
    match BoundedConfig.step tm x with
    | None => None
    | Some x' => if cond x' then Some x' else find_bounded cond k x'
    end
  end.

Lemma find_spec cond k x x':
  find_bounded cond k x = Some x' ->
  cond x' = true /\
  forall l0 r0, BoundedConfig.to_config x l0 r0 -[ tm ]->+ BoundedConfig.to_config x' l0 r0.
Proof.
  revert x.
  induction k as [|k IH]; intros x H; [discriminate|].
  cbn in H.
  pose proof (BoundedConfig.step_spec tm x) as Hs.
  destruct (BoundedConfig.step tm x) as [x1|]; [|discriminate].
  destruct (cond x1) eqn:Ec.
  - inversion H; subst. split; [exact Ec|].
    intros. apply progress_base. apply Hs.
  - destruct (IH x1 H) as [Hc Hp]. split; [exact Hc|].
    intros. eapply progress_step. 1: apply Hs. apply Hp.
Qed.

End Window.

(** the restart record: state C, the head on a 0 with only zeros to its left, and the cells
    to its right start with [S1] *)
Definition is0 (x:Sym) : bool := match x with S0 => true | _ => false end.

Fixpoint prefixb (p l:list Sym) : bool :=
  match p, l with
  | [], _ => true
  | a::p', b::l' => (match a, b with S0,S0 | S1,S1 => true | _,_ => false end) && prefixb p' l'
  | _, [] => false
  end.

Lemma prefixb_spec p l: prefixb p l = true -> l = p ++ skipn (length p) l.
Proof.
  revert l. induction p as [|a p IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; [discriminate|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct a, b; try discriminate; cbn; f_equal; apply IH; exact H2.
Qed.

Lemma zeros_const (z:list Sym): forallb is0 z = true -> z *> Streams.const s0 = Streams.const s0.
Proof.
  induction z as [|a z IH]; intros H; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct a; [|discriminate].
  cbn. rewrite IH by exact H2.
  symmetry. apply const_unfold.
Qed.


(** The machine, the restart configuration and the generic "run, cut a window, find the restart" pipeline. *)

Require Import List Lia NArith String.
Import ListNotations.

Open Scope string.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC---").
Close Scope string.

(** the first 4800 cells (from the head) at every restart *)
Definition Srwl : RWL := map (fun '(w,n) => (w,(0%N,0%N),n)) S48_runs.
Definition Slist : list Sym := flat0 Srwl.
Definition S1 : list Sym := tl Slist.

(** a restart configuration with an arbitrary rest of the tape [R] *)
Definition cfg (R:side) : Q * tape := Streams.const s0 {{C}}> Slist *> R.

Definition cinit : RWL_config := ([], Srwl, C, R).

Lemma cinit_cfg rt: to_config rt 0 0 cinit = cfg rt.
Proof. reflexivity. Qed.

Definition dir_is_L (d:dir) : bool := match d with L => true | R => false end.
Definition state_is_C (q:Q) : bool := match q with C => true | _ => false end.

(** the restart record, seen from a bounded window in the L orientation *)
Definition cond (x:BoundedConfig.T) : bool :=
  match x with
  | BoundedConfig.Build_T l r s sgn =>
    state_is_C s && dir_is_L sgn &&
    match r with
    | S0::z => forallb is0 z
    | _ => false
    end && prefixb S1 l
  end.

Definition dropS1 (l:list Sym) : list Sym := skipn (List.length S1) l.
Arguments dropS1 : simpl never.

Lemma Slist_cons: Slist = S0 :: S1.
Proof. vm_compute. reflexivity. Qed.

Lemma cond_spec x r0:
  cond x = true ->
  match x with
  | BoundedConfig.Build_T l r s sgn =>
    BoundedConfig.to_config x (Streams.const s0) r0 = cfg (dropS1 l *> r0)
  end.
Proof.
  destruct x as [l r s sgn].
  unfold cond.
  intros H.
  apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  destruct s; try discriminate.
  destruct sgn; try discriminate.
  destruct r as [|x z]; [discriminate|].
  destruct x; [|discriminate].
  cbn [BoundedConfig.to_config].
  unfold cfg.
  rewrite Slist_cons.
  rewrite (prefixb_spec _ _ H4) at 1.
  fold (dropS1 l).
  rewrite Str_app_assoc.
  cbn.
  rewrite (zeros_const z H3).
  reflexivity.
Qed.

Section Pipeline.
Hypothesis T:N.
Hypothesis k n K:nat.

Definition run (c:RWL_config) : option (list Sym * RWL) :=
  match decide_evstep_from tm 40 100000 true 2 c T with
  | Some c' =>
    match window k n c' with
    | Some (x, rest) =>
      match find_bounded tm cond K x with
      | Some (BoundedConfig.Build_T l r s sgn) => Some (dropS1 l, rest)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Lemma run_spec c M rest rt:
  run c = Some (M, rest) ->
  to_config rt 0 0 c -[ tm ]->+ cfg (M *> to_side_t 0 0 rt rest).
Proof.
  unfold run.
  destruct (decide_evstep_from tm 40 100000 true 2 c T) as [c'|] eqn:E1; [|discriminate].
  destruct (window k n c') as [[x rest0]|] eqn:E2; [|discriminate].
  destruct (find_bounded tm cond K x) as [x'|] eqn:E3; [|discriminate].
  destruct x' as [l r s sgn] eqn:Ex'.
  intros H. injection H as <- <-.
  pose proof (decide_evstep_from_spec tm 40 100000 true 2 rt (to_config rt 0 0 c) c T c'
                (evstep_refl _ _) E1) as H1.
  rewrite (window_spec rt k n c' x rest0 E2) in H1.
  destruct (find_spec tm cond K x _ E3) as [Hc Hp].
  pose proof (cond_spec _ (to_side_t 0 0 rt rest0) Hc) as Heq.
  cbn beta iota in Heq.
  rewrite <-Heq.
  eapply evstep_progress_trans.
  1: exact H1.
  apply Hp.
Qed.

End Pipeline.


(** * 1RB1RD_1LC0LE_1LD0LB_0RB0RA_1RD1LF_0LC--- does not halt

    From about 2.67e28 steps on the machine is a translated cycler with a left record:
    every restart configuration  [cfg R = 0^inf {{C}}> S *> R]  (S = the 4800 cells in S48.v)
    reaches another restart configuration  [cfg (M *> R')]  without reading R
    (period 4,126,262,385,607,271,490,126,714 steps, shift 2,428,193,875,694 cells).

    Both facts are established by computation with RWLAccT, a variant of busycoq's RWLAcc
    (block-run tapes with chain steps and verified loop acceleration) whose right end is an
    arbitrary side that may never be read:
    - [pre]:   c0 -->+ cfg R0 for some R0, from the blank tape (blank right end given as a run
               of 10^20 zero blocks);
    - [cycle]: for every R, cfg R -->+ cfg R' for some R'. *)

Require Import List NArith.
Import ListNotations.

Definition zw : list Sym := repeat s0 40.
Definition cpre : RWL_config := ([], [(zw,(0%N,0%N),100000000000000000000%N)], A, R).

Lemma zw_pow_const n: zw ^^ n *> Streams.const s0 = Streams.const s0.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [lpow]. rewrite Str_app_assoc, IH.
  apply zeros_const. vm_compute. reflexivity.
Qed.

Lemma cpre_c0: to_config (Streams.const s0) 0 0 cpre = c0.
Proof.
  unfold cpre, to_config, to_side_t, tl_of, tr_of.
  cbn [flat_map].
  rewrite app_nil_r.
  unfold to_seg.
  generalize (N.to_nat 0 * 0 + N.to_nat 0 * 0 + N.to_nat 100000000000000000000%N)%nat as m.
  intros m. rewrite zw_pow_const.
  reflexivity.
Qed.

Definition Tpre : N := 130037%N.
Definition Tcyc : N := 199821%N.

Definition is_some {T} (o:option T) : bool := match o with Some _ => true | None => false end.

(** the two computations (checked by the kernel's virtual machine) *)
Lemma pre_ok: is_some (run Tpre 2000 4900 2000 cpre) = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Lemma cycle_ok: is_some (run Tcyc 2000 4900 2000 cinit) = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Lemma pre: exists R0, c0 -[ tm ]->+ cfg R0.
Proof.
  pose proof pre_ok as Hok.
  destruct (run Tpre 2000 4900 2000 cpre) as [[M rest]|] eqn:E.
  - exists (M *> to_side_t 0 0 (Streams.const s0) rest).
    rewrite <-cpre_c0.
    eapply run_spec. exact E.
  - discriminate Hok.
Qed.

Lemma cycle R: exists R', cfg R -[ tm ]->+ cfg R'.
Proof.
  pose proof cycle_ok as Hok.
  destruct (run Tcyc 2000 4900 2000 cinit) as [[M rest]|] eqn:E.
  - exists (M *> to_side_t 0 0 R rest).
    rewrite <-(cinit_cfg R).
    eapply run_spec. exact E.
  - discriminate Hok.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct pre as [R0 H0].
  eapply multistep_nonhalt.
  1: apply progress_evstep, H0.
  apply (progress_nonhalt tm (fun c => exists R, c = cfg R)).
  - intros c [R Hc]. subst c.
    destruct (cycle R) as [R' H].
    exists (cfg R'). split; [exists R'; reflexivity | exact H].
  - exists R0. reflexivity.
Qed.
