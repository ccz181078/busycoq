(* Classification: SOBC. Source: BusyCoq PR #34,
   commit 9cf9e8327ec04c3b5807cc39bed2ad3e41bc34f5.
   Original proof bodies preserved; local packaging only. *)

(* At its left records the tape is 0 0 1 1 (0 1)^N followed by a region of 1-runs (rec N zs). Most sweeps act
   on the region by one of three rules (R1, R2, RB), which give two absorption macros (binary counters). A
   computable driver applies them, runs each other sweep concretely on the last pairs of the long run and the
   region, and ends in a translated cycler (period 85, shift 1). *)
From BusyCoq Require Import Individual62.
Require Import Arith Lia List NArith String.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RB_0LA0LD_1LE0RB_1RF0RE_---0RD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Fixpoint reg (zs : list nat) : list Sym :=
  match zs with [] => [] | z :: t => 0 :: [1]^^z ++ reg t end.
Definition rec N zs := 0inf {{D}}> [0;0;1;1] *> [0;1]^^N *> reg zs *> 0inf.

Lemma reg_ones a zs : reg (repeat 1%nat a ++ zs) = [0;1]^^a ++ reg zs.
Proof. induction a; cbn; congruence. Qed.

Lemma R1 N a e zs : rec (N+8) ((a*2+7) :: e :: zs) -->+ rec (N+2+8) (4 :: repeat 1%nat a ++ (e+2) :: zs).
Proof. unfold rec. cbn [reg]. rewrite reg_ones. es. Qed.

Lemma R2 N y zs : rec (N+8) (4 :: 1%nat :: y :: zs) -->+ rec (N+1+8) ((y+8) :: zs).
Proof. es. Qed.

Lemma RB N b y zs : rec (N+8) (4 :: (b*2+3) :: y :: zs) -->+ rec (N+1+8) (7 :: repeat 1%nat b ++ (y+2) :: zs).
Proof. unfold rec. cbn [reg]. rewrite reg_ones. es. Qed.

Definition NH zs := forall N, ~halts tm (rec (N+8) zs).

Lemma NH_rule zs zs' k : (forall N, rec (N+8) zs -->+ rec (N+k+8) zs') -> NH zs' -> NH zs.
Proof. intros H H' N. eapply multistep_nonhalt; [apply progress_evstep, H | apply H']. Qed.

(* class I: X y -> (X+y+1) for odd X >= 9 *)
Definition PI a := forall y zs, NH ((a*2+10+y) :: zs) -> NH ((a*2+9) :: y :: zs).

Lemma onesI k : forall b zs, (forall i, b <= i < b+k -> PI i) ->
  NH (((b+k)*2+9) :: zs) -> NH ((b*2+9) :: repeat 1%nat k ++ zs).
Proof.
  induction k as [|k IH]; intros b zs H H'.
  - rewrite Nat.add_0_r in H'. exact H'.
  - apply H; [lia|]. replace (b*2+10+1) with (S b*2+9) by lia.
    apply IH; [intros i Hi; apply H; lia|]. replace (S b+k) with (b+S k) by lia. exact H'.
Qed.

Lemma classI a : PI a.
Proof.
  induction a as [a IH] using strong_induction. intros y zs H.
  replace (a*2+9) with (S a*2+7) by lia.
  apply (NH_rule _ _ 2 (fun N => R1 N (S a) y zs)).
  destruct a as [|a].
  - apply (NH_rule _ _ 1 (fun N => R2 N (y+2) zs)). replace (y+2+8) with (0*2+10+y) by lia. exact H.
  - apply (NH_rule _ _ 1 (fun N => R2 N 1 (repeat 1%nat a ++ (y+2) :: zs))).
    apply (onesI a 0); [intros i Hi; apply IH; lia|].
    apply (IH a); [lia|]. replace (a*2+10+(y+2)) with (S a*2+10+y) by lia. exact H.
Qed.

(* class II: 7 x y -> 7 (x+y+1) for odd x *)
Definition PII b := forall y zs, NH (7 :: (b*2+2+y) :: zs) -> NH (7 :: (b*2+1) :: y :: zs).

Lemma onesII k : forall b zs, (forall i, b <= i < b+k -> PII i) ->
  NH (7 :: ((b+k)*2+1) :: zs) -> NH (7 :: (b*2+1) :: repeat 1%nat k ++ zs).
Proof.
  induction k as [|k IH]; intros b zs H H'.
  - rewrite Nat.add_0_r in H'. exact H'.
  - apply H; [lia|]. replace (b*2+2+1) with (S b*2+1) by lia.
    apply IH; [intros i Hi; apply H; lia|]. replace (S b+k) with (b+S k) by lia. exact H'.
Qed.

Lemma classII b : PII b.
Proof.
  induction b as [b IH] using strong_induction. intros y zs H.
  apply (NH_rule _ _ 2 (fun N => R1 N 0 (b*2+1) (y :: zs))).
  replace (b*2+1+2) with (b*2+3) by lia.
  apply (NH_rule _ _ 1 (fun N => RB N b y zs)).
  destruct b as [|b].
  - replace (y+2) with (0*2+2+y) by lia. exact H.
  - apply (onesII b 0); [intros i Hi; apply IH; lia|].
    apply (IH b); [lia|]. replace (b*2+2+(y+2)) with (S b*2+2+y) by lia. exact H.
Qed.

Definition mstep (zs : list nat) : option (list nat) :=
  match zs with
  | X :: y :: t =>
    if Nat.eqb X (Nat.div2 (X-9)*2+9) then Some ((Nat.div2 (X-9)*2+10+y) :: t)
    else if Nat.eqb X 7 then
      match t with
      | y' :: t' =>
        if Nat.eqb y (Nat.div2 y*2+1) then Some (7 :: (Nat.div2 y*2+2+y') :: t') else Some (4 :: (y+2) :: t)
      | [] => Some (4 :: (y+2) :: t)
      end
    else if Nat.eqb X 4 then
      match t with
      | y' :: t' =>
        if Nat.eqb y 1 then Some ((y'+8) :: t')
        else if Nat.eqb y (Nat.div2 (y-3)*2+3) then Some (7 :: repeat 1%nat (Nat.div2 (y-3)) ++ (y'+2) :: t')
        else None
      | [] => None
      end
    else None
  | _ => None
  end.

Lemma mstep_spec zs zs' : mstep zs = Some zs' -> NH zs' -> NH zs.
Proof.
  unfold mstep. destruct zs as [|X [|y t]]; try discriminate.
  destruct (Nat.eqb_spec X (Nat.div2 (X-9)*2+9)) as [E|_].
  { intros [= <-]. revert E. generalize (Nat.div2 (X-9)). intros a ->. apply classI. }
  destruct (Nat.eqb_spec X 7) as [->|_].
  { destruct t as [|y' t].
    - intros [= <-]. apply (NH_rule _ _ 2 (fun N => R1 N 0 y [])).
    - destruct (Nat.eqb_spec y (Nat.div2 y*2+1)) as [E|_]; intros [= <-].
      + revert E. generalize (Nat.div2 y). intros b ->. apply classII.
      + apply (NH_rule _ _ 2 (fun N => R1 N 0 y (y' :: t))). }
  destruct (Nat.eqb_spec X 4) as [->|_]; [|discriminate].
  destruct t as [|y' t]; [discriminate|].
  destruct (Nat.eqb_spec y 1) as [->|_].
  { intros [= <-]. apply (NH_rule _ _ 1 (fun N => R2 N y' t)). }
  destruct (Nat.eqb_spec y (Nat.div2 (y-3)*2+3)) as [E|_]; [|discriminate].
  intros [= <-]. revert E. generalize (Nat.div2 (y-3)). intros b ->.
  apply (NH_rule _ _ 1 (fun N => RB N b y' t)).
Qed.

Lemma cross M r : 0inf {{D}}> [0;0;1;1] *> [0;1]^^M *> r -->+ 0inf <* [1] <* [1;1]^^M <* [1;0;0;1] {{B}}> r.
Proof. es. Qed.

Lemma back M r : 0inf <* [1] <* [1;1]^^M <{{D}} [0;0;1] *> r -->+ 0inf {{D}}> [0;0;1;1] *> [0;1]^^(1+M) *> r.
Proof. es. Qed.

(* concrete runs: blank to the right, any side l0 to the left; a run stops when the head stands on l0 *)
Definition one (x : BoundedConfig.T) :=
  match BoundedConfig.step_r0inf tm x with Some y => inl y | None => inr x end.
Definition run n x := match Eqb.N_iter_until one (inl x) n with inl y | inr y => y end.

Lemma run_spec n x l0 : BoundedConfig.to_config x l0 0inf -->* BoundedConfig.to_config (run n x) l0 0inf.
Proof.
  pose (G y := BoundedConfig.to_config x l0 0inf -->* BoundedConfig.to_config y l0 0inf).
  assert (H : match Eqb.N_iter_until one (inl x) n with inl y | inr y => G y end).
  { apply Eqb.N_iter_until_spec; [|apply evstep_refl].
    intros y Hy. unfold one. pose proof (BoundedConfig.step_r0inf_spec tm y) as S.
    destruct (BoundedConfig.step_r0inf tm y); [|exact Hy].
    eapply evstep_trans; [exact Hy | apply evstep_one, S]. }
  unfold run. destruct (Eqb.N_iter_until one (inl x) n); exact H.
Qed.

(* a sweep with no rule: the last 8 pairs of the long run and the region, run concretely *)
Definition frame zs := BoundedConfig.Build_T [1;0;0;1] ([0;1]^^8 ++ reg zs) B R.

Lemma to_frame M zs : rec (M+8) zs -->* BoundedConfig.to_config (frame zs) (0inf <* [1] <* [1;1]^^M) 0inf.
Proof. unfold rec. cbn. rewrite lpow_add, !Str_app_assoc. apply progress_evstep, cross. Qed.

Fixpoint dec (X : list Sym) : nat * list nat :=
  match X with
  | [] => (O, [])
  | 1 :: t => let (k, zs) := dec t in (S k, zs)
  | 0 :: t => let (k, zs) := dec t in (O, k :: zs)
  end.
Fixpoint strip (zs : list nat) : list nat :=
  match zs with [] => [] | z :: t => match strip t, z with [], O => [] | t', _ => z :: t' end end.
Fixpoint lead1 (zs : list nat) : nat * list nat :=
  match zs with 1%nat :: t => let (d, r) := lead1 t in (S d, r) | _ => (O, zs) end.

Definition special zs :=
  match run 33554432 (frame zs) with
  | BoundedConfig.Build_T l' [] D L =>
    let (d, zs') := lead1 (strip (snd (dec (skipn 3 l')))) in
    if Nat.leb 7 d then
      if cside_eqb l' ([0;0;1] ++ [0;1]^^d ++ reg zs') then Some (d-7, zs') else None
    else None
  | _ => None
  end.

Lemma special_spec zs k zs' : special zs = Some (k, zs') -> NH zs' -> NH zs.
Proof.
  unfold special. intros H H' M.
  pose proof (run_spec 33554432 (frame zs) (0inf <* [1] <* [1;1]^^M)) as E.
  destruct (run 33554432 (frame zs)) as [l' [|] [] []]; try discriminate.
  destruct (lead1 _) as [d zs0].
  destruct (Nat.leb_spec 7 d); [|discriminate].
  destruct (cside_eqb l' _) eqn:C; [|discriminate].
  injection H as <- <-. apply cside_eqb_spec in C.
  eapply multistep_nonhalt; [eapply evstep_trans; [apply to_frame | exact E]|].
  cbn. rewrite C, !Str_app_assoc.
  eapply multistep_nonhalt; [apply progress_evstep, back|].
  rewrite lpow_add'. replace (1+M+d) with (M+(d-7)+8) by lia. apply H'.
Qed.

(* the runaway: after 29582 steps the head is in state B on a new cell, with cyc behind it *)
Definition cyc : list Sym := [1;1;1;1;1;1;0;0;1;0;0;0;0;0].

Lemma cycle l : l <* cyc {{B}}> 0inf -->+ (l <* [0]) <* cyc {{B}}> 0inf.
Proof. unfold cyc. execute. Qed.

Definition final zs :=
  match run 29582 (frame zs) with
  | BoundedConfig.Build_T l' [] B R => match skip_prefix_list cyc l' with Some _ => true | None => false end
  | _ => false
  end.

Lemma final_spec zs : final zs = true -> NH zs.
Proof.
  unfold final. intros H M.
  pose proof (run_spec 29582 (frame zs) (0inf <* [1] <* [1;1]^^M)) as E.
  destruct (run 29582 (frame zs)) as [l' [|] [] []]; try discriminate.
  destruct (skip_prefix_list cyc l') as [t|] eqn:S; [|discriminate].
  apply skip_prefix_list_spec in S. subst l'.
  eapply multistep_nonhalt; [eapply evstep_trans; [apply to_frame | exact E]|].
  cbn [BoundedConfig.to_config]. rewrite Str_app_assoc.
  apply (progress_nonhalt_simple tm side (fun l => l <* cyc {{B}}> 0inf) (t *> 0inf <* [1] <* [1;1]^^M)).
  intro l. exists (l <* [0]). apply cycle.
Qed.

Fixpoint drive (n : nat) (zs : list nat) : bool :=
  match n with
  | O => false
  | S n =>
    match mstep zs with
    | Some zs' => drive n zs'
    | None =>
      if final zs then true else
      match special zs with Some (_, zs') => drive n zs' | None => false end
    end
  end.

Lemma drive_spec n : forall zs, drive n zs = true -> NH zs.
Proof.
  induction n as [|n IH]; intros zs H; [discriminate|]. cbn [drive] in H.
  destruct (mstep zs) as [zs'|] eqn:E; [exact (mstep_spec _ _ E (IH _ H))|].
  destruct (final zs) eqn:F; [exact (final_spec _ F)|].
  destruct (special zs) as [[k zs']|] eqn:S; [exact (special_spec _ _ _ S (IH _ H))|discriminate].
Qed.

(* the opening: 6800171 steps to rec 10 Z1 *)
Definition Z1 := 13 :: repeat 1%nat 1193 ++ [3; 9] ++ repeat 1%nat 8 ++ [2].

Definition open_ok :=
  match run 6800171 (BoundedConfig.Build_T ([0]^^2439) [] A R) with
  | BoundedConfig.Build_T l' [0] D L => cside_eqb l' ([0;1;1] ++ [0;1]^^10 ++ reg Z1)
  | _ => false
  end.

Lemma opening : open_ok = true -> c0 -->* rec 10 Z1.
Proof.
  unfold open_ok. intro H.
  pose proof (run_spec 6800171 (BoundedConfig.Build_T ([0]^^2439) [] A R) 0inf) as E.
  destruct (run 6800171 _) as [l' [|[] [|]] [] []]; try discriminate.
  apply cside_eqb_spec in H.
  cbn [BoundedConfig.to_config] in E. rewrite lpow_all0 in E by solve_const0_eq. rewrite H in E.
  unfold rec. rewrite !Str_app_assoc in E. exact E.
Qed.

Lemma open_ok_true : open_ok = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma drive_ok : drive (2^15) Z1 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [exact (opening open_ok_true)|].
  exact (drive_spec _ _ drive_ok 2).
Qed.

End TM1.
