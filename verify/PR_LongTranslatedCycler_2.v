(** * 1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD--- does not halt (translated cycler)

    BB(6) holdout.  The machine is a translated cycler with a left record.  Write

      cfg R = 0^inf <{{A}} S *> R

    for the configuration with the head in state A at the left edge of the tape, about to read
    a blank, followed to the right by a fixed word S of 264 cells and an arbitrary rest R.

    Proof by computation with RWLAccT (RWLAcc with an arbitrary, never-read right end of the
    tape), block size 24, in the style of PR_LongTranslatedCycler.v:
    - [pre]:   the blank tape reaches  cfg R0  for some R0 (989 macro steps);
    - [cycle]: for every R,  cfg R  reaches  cfg R'  for some R', in at least one step and
               without reading R (about 1e6 macro steps, about 9.5e15 machine steps).

    The cycle is checked in 20 pieces of at most 50,000 macro steps.  The configurations between
    the pieces are computed when the file is compiled ([Eval vm_compute]); they are not part of
    the source.  Cutting the run this way keeps the memory of coqchk moderate.

    The cycle was found by a sweep over the remaining holdouts with a port of RWLAccT.

    AI assistance: this proof, the scripts and the checks were produced with the help of Claude
    (Anthropic). *)

From BusyCoq Require Import RWLAccT62.
Require Import List Lia NArith String.
Import ListNotations.

Open Scope string.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RD_0LD1LA_1LF0RE_1LB1RE_1RD---").
Close Scope string.

(** cutting whole blocks off the front of a compressed side *)
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
            match take_cells k (n - List.length w) ((w,(0%N,0%N),N.pred (Npos p))::t) with
            | Some (XA,ls') => Some (w ++ XA, ls')
            | None => None
            end
          end
        end
      end
    end
  end.

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

Fixpoint prefixb (p l:list Sym) : bool :=
  match p, l with
  | [], _ => true
  | a::p', b::l' => (match a, b with S0,S0 | S1,S1 => true | _,_ => false end) && prefixb p' l'
  | _, [] => false
  end.

Lemma prefixb_spec p l: prefixb p l = true -> l = p ++ skipn (List.length p) l.
Proof.
  revert l. induction p as [|a p IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; [discriminate|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct a, b; try discriminate; cbn; f_equal; apply IH; exact H2.
Qed.

Definition is0 (x:Sym) : bool := match x with S0 => true | _ => false end.

Lemma zeros_const (z:list Sym): forallb is0 z = true -> z *> Streams.const s0 = Streams.const s0.
Proof.
  induction z as [|a z IH]; intros H; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2].
  destruct a; [|discriminate].
  cbn. rewrite IH by exact H2.
  symmetry. apply const_unfold.
Qed.

(** the start of every period: 264 cells *)
Definition Srwl : RWL := [
  ([S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0], (0%N,0%N), 1%N);
  ([S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0], (0%N,0%N), 1%N);
  ([S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S0;S0;S0;S0;S1;S1;S1;S1;S1;S0;S1;S1], (0%N,0%N), 1%N);
  ([S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1], (0%N,0%N), 1%N);
  ([S1;S1;S1;S0;S0;S0;S0;S0;S0;S1;S1;S1;S1;S1;S0;S0;S1;S1;S1;S1;S1;S1;S1;S1], (0%N,0%N), 1%N);
  ([S1;S1;S0;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S0;S0;S1;S1;S1;S1;S1;S0], (0%N,0%N), 1%N);
  ([S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S0;S0;S0;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1], (0%N,0%N), 1%N);
  ([S0;S1;S1;S1;S1;S1;S0;S0;S0;S0;S0;S0;S0;S0;S0;S0;S1;S1;S1;S1;S1;S0;S0;S1], (0%N,0%N), 1%N);
  ([S1;S1;S1;S1;S0;S0;S0;S0;S0;S1;S1;S1;S1;S1;S0;S0;S0;S1;S1;S1;S1;S1;S0;S0], (0%N,0%N), 1%N);
  ([S0;S0;S0;S0;S0;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S0], (0%N,0%N), 1%N);
  ([S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0;S1;S1;S1;S1;S1], (0%N,0%N), 1%N)
].
Definition Slist : list Sym := flat_map (to_seg 0 0) Srwl.
Definition cfg (R:side) : Q * tape := Streams.const s0 <{{A}} Slist *> R.
Definition cinit : RWL_config := (Srwl, [], A, L).

Lemma cinit_cfg rt: to_config rt 0 0 cinit = cfg rt.
Proof. reflexivity. Qed.

Definition is_st (q:Q) : bool := match q with A => true | _ => false end.

Definition check (c:RWL_config) : option (list Sym * RWL) :=
  match c with
  | (l, [], q, L) =>
    if is_st q then
      match take_cells 49 264 l with
      | Some (XA, rest) => if prefixb Slist XA then Some (skipn (List.length Slist) XA, rest) else None
      | None => None
      end
    else None
  | _ => None
  end.

Lemma check_spec rt c M rest:
  check c = Some (M, rest) ->
  to_config rt 0 0 c = cfg (M *> to_side_t 0 0 rt rest).
Proof.
  destruct c as [[[l r] q] d].
  unfold check.
  destruct r as [|x r]; [|discriminate].
  destruct d; [|discriminate].
  destruct (is_st q) eqn:Eq; [|discriminate].
  destruct (take_cells 49 264 l) as [[XA rest0]|] eqn:E; [|discriminate].
  destruct (prefixb Slist XA) eqn:P; [|discriminate].
  intros H; inversion H; subst; clear H.
  destruct q; try discriminate Eq.
  cbn [to_config tl_of tr_of].
  rewrite (take_cells_spec _ _ _ _ _ _ E).
  unfold cfg.
  rewrite (prefixb_spec _ _ P) at 1.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

(** the blank tape, with its right end given as a long run of zero blocks *)
Definition zw : list Sym := repeat s0 24.
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

Section Pipeline.
Variable T : N.

Definition run_from (c:RWL_config) :=
  match decide_evstep_from tm 24 100000 true 2 c T with
  | Some c' => check c'
  | None => None
  end.

Lemma run_from_spec rt c M rest:
  run_from c = Some (M, rest) ->
  to_config rt 0 0 c -[ tm ]->* cfg (M *> to_side_t 0 0 rt rest).
Proof.
  unfold run_from.
  destruct (decide_evstep_from tm 24 100000 true 2 c T) as [c'|] eqn:E1; [|discriminate].
  intros E2.
  rewrite <- (check_spec rt c' M rest E2).
  exact (decide_evstep_from_spec tm 24 100000 true 2 rt _ c T c' (evstep_refl _ _) E1).
Qed.

End Pipeline.

Definition Tpre : N := 989%N.

Definition is_some {X} (o:option X) : bool := match o with Some _ => true | None => false end.

(** the two computations, checked by the kernel's virtual machine *)
Lemma pre_ok: is_some (run_from Tpre cpre) = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Lemma pre: exists R0, c0 -[ tm ]->* cfg R0.
Proof.
  pose proof pre_ok as Hok.
  destruct (run_from Tpre cpre) as [[M rest]|] eqn:E; [|discriminate Hok].
  exists (M *> to_side_t 0 0 (Streams.const s0) rest).
  rewrite <- cpre_c0.
  eapply run_from_spec. exact E.
Qed.

(** ** The cycle, in 20 pieces *)

(** one macro step, then [K] more; on failure the configuration is returned unchanged
    (the lemmas below would then fail) *)
Definition first_step (c:RWL_config) : RWL_config :=
  match RWL_step tm 24 100000 c with Some (inl c1) => c1 | _ => c end.
Definition adv (K:N) (c:RWL_config) : RWL_config :=
  match decide_evstep_from tm 24 100000 true 2 c K with Some c1 => c1 | None => c end.

Lemma step_spec c c1 rt: RWL_step tm 24 100000 c = Some (inl c1) ->
  to_config rt 0 0 c -[ tm ]->+ to_config rt 0 0 c1.
Proof.
  intros E. pose proof (RWL_step_spec tm 24 100000 rt 0 0 c) as Hs.
  rewrite E in Hs. exact Hs.
Qed.

Lemma chunk_spec c c1 (K:N) rt: decide_evstep_from tm 24 100000 true 2 c K = Some c1 ->
  to_config rt 0 0 c -[ tm ]->* to_config rt 0 0 c1.
Proof.
  intros E. exact (decide_evstep_from_spec tm 24 100000 true 2 rt _ c K c1 (evstep_refl _ _) E).
Qed.

Definition C0 : RWL_config := Eval vm_compute in first_step cinit.
Lemma step0: RWL_step tm 24 100000 cinit = Some (inl C0).
Proof. vm_cast_no_check (eq_refl (@Some (RWL_config + Q * Sym) (inl C0))). Qed.

Notation chunk K c c1 := (decide_evstep_from tm 24 100000 true 2 c K = Some c1).
Ltac chk c1 := vm_cast_no_check (eq_refl (Some c1)).

Definition C1 : RWL_config := Eval vm_compute in adv 50000 C0.
Lemma chunk0: chunk 50000%N C0 C1. Proof. chk C1. Qed.
Definition C2 : RWL_config := Eval vm_compute in adv 50000 C1.
Lemma chunk1: chunk 50000%N C1 C2. Proof. chk C2. Qed.
Definition C3 : RWL_config := Eval vm_compute in adv 50000 C2.
Lemma chunk2: chunk 50000%N C2 C3. Proof. chk C3. Qed.
Definition C4 : RWL_config := Eval vm_compute in adv 50000 C3.
Lemma chunk3: chunk 50000%N C3 C4. Proof. chk C4. Qed.
Definition C5 : RWL_config := Eval vm_compute in adv 50000 C4.
Lemma chunk4: chunk 50000%N C4 C5. Proof. chk C5. Qed.
Definition C6 : RWL_config := Eval vm_compute in adv 50000 C5.
Lemma chunk5: chunk 50000%N C5 C6. Proof. chk C6. Qed.
Definition C7 : RWL_config := Eval vm_compute in adv 50000 C6.
Lemma chunk6: chunk 50000%N C6 C7. Proof. chk C7. Qed.
Definition C8 : RWL_config := Eval vm_compute in adv 50000 C7.
Lemma chunk7: chunk 50000%N C7 C8. Proof. chk C8. Qed.
Definition C9 : RWL_config := Eval vm_compute in adv 50000 C8.
Lemma chunk8: chunk 50000%N C8 C9. Proof. chk C9. Qed.
Definition C10 : RWL_config := Eval vm_compute in adv 50000 C9.
Lemma chunk9: chunk 50000%N C9 C10. Proof. chk C10. Qed.
Definition C11 : RWL_config := Eval vm_compute in adv 50000 C10.
Lemma chunk10: chunk 50000%N C10 C11. Proof. chk C11. Qed.
Definition C12 : RWL_config := Eval vm_compute in adv 50000 C11.
Lemma chunk11: chunk 50000%N C11 C12. Proof. chk C12. Qed.
Definition C13 : RWL_config := Eval vm_compute in adv 50000 C12.
Lemma chunk12: chunk 50000%N C12 C13. Proof. chk C13. Qed.
Definition C14 : RWL_config := Eval vm_compute in adv 50000 C13.
Lemma chunk13: chunk 50000%N C13 C14. Proof. chk C14. Qed.
Definition C15 : RWL_config := Eval vm_compute in adv 50000 C14.
Lemma chunk14: chunk 50000%N C14 C15. Proof. chk C15. Qed.
Definition C16 : RWL_config := Eval vm_compute in adv 50000 C15.
Lemma chunk15: chunk 50000%N C15 C16. Proof. chk C16. Qed.
Definition C17 : RWL_config := Eval vm_compute in adv 50000 C16.
Lemma chunk16: chunk 50000%N C16 C17. Proof. chk C17. Qed.
Definition C18 : RWL_config := Eval vm_compute in adv 50000 C17.
Lemma chunk17: chunk 50000%N C17 C18. Proof. chk C18. Qed.
Definition C19 : RWL_config := Eval vm_compute in adv 50000 C18.
Lemma chunk18: chunk 50000%N C18 C19. Proof. chk C19. Qed.
Definition C20 : RWL_config := Eval vm_compute in adv 45931 C19.
Lemma chunk19: chunk 45931%N C19 C20. Proof. chk C20. Qed.

Lemma fin_ok: is_some (check C20) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cycle R: exists R', cfg R -[ tm ]->+ cfg R'.
Proof.
  pose proof fin_ok as Hok.
  destruct (check C20) as [[M rest]|] eqn:EF; [|discriminate Hok].
  exists (M *> to_side_t 0 0 R rest).
  rewrite <- (cinit_cfg R).
  rewrite <- (check_spec R C20 M rest EF).
  eapply progress_evstep_trans. 1: exact (step_spec _ _ R step0).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk0).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk1).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk2).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk3).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk4).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk5).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk6).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk7).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk8).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk9).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk10).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk11).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk12).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk13).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk14).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk15).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk16).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk17).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk18).
  eapply evstep_trans. 1: exact (chunk_spec _ _ _ R chunk19).
  apply evstep_refl.
Qed.

Theorem nonhalt: ~ halts tm c0.
Proof.
  destruct pre as [R0 H0].
  eapply multistep_nonhalt.
  1: exact H0.
  apply (progress_nonhalt tm (fun c => exists R, c = cfg R)).
  - intros c [R Hc]. subst c.
    destruct (cycle R) as [R' H].
    exists (cfg R'). split; [exists R'; reflexivity | exact H].
  - exists R0. reflexivity.
Qed.
