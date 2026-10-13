(* 1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB--- never halts.
   Adapted from the proof of 1RB0RE_1LC0RE_1LD0LD_1RA0LC_1RA1RF_1RA--- (the parent), which is the
   mechanism of verify/SBCv6.v, Module TM21 (binary counter over digits (10)^v [00] (01)^u with a
   re-pairing overflow; Skelet 1-like Class 2).
   This machine is the parent's table with its states renamed sigma = (A,B,C,D,E,F) -> (B,C,D,A,E,F),
   no mirror, started in the parent's state D (equivalently the table of
   1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---, proved in verify/Skelet1LikeC2_1RB0LE_1RC0RC.v,
   mirrored, started in its state C). Delta from the parent's file, verify/Skelet1LikeC2_1RB0RE_1LC0RE.v
   (sha256 2dfa4337...8ff6): the TM string, sigma applied to every state name {{X}} (window lemmas,
   digit lemmas, sweeps, chunks, K), and the base: init is 687 steps to K [d1 1 9] 8 1 (class A)
   instead of 215 steps to K [d1 1 3] 4 1. Every proof script, the three rule specs (M_spec,
   Mdrop_spec, O_spec) and the abstract part (INV, closure, macro_step) are the parent's text.
   Informal proof: the accompanying write-up, a delta proof that cites the parent's write-up as P section n.
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import String.
Require Import List.
Require Import Arith.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

(* ---------- shift lemmas (one block, then shift_rule_L/R) ---------- *)
Lemma S1_1 l r: l <* [0;1] <{{D}} [] *> r -->* l <{{D}} [] *> [0;1] *> r.  Proof. es. Qed.
Lemma S2_1 l r: l <* [1;0] <{{A}} [] *> r -->* l <{{A}} [] *> [1;0] *> r.  Proof. es. Qed.
Lemma S3_1 l r: l <* [] {{B}}> [1;0] *> r -->* l <* [1;0] <* [] {{B}}> r.  Proof. es. Qed.
Lemma S4_1 l r: l <* [] {{E}}> [0;1] *> r -->* l <* [0;1] <* [] {{E}}> r.  Proof. es. Qed.
Lemma S6_1 l r: l <* [1;0] <{{D}} [0] *> r -->* l <{{D}} [0] *> [0;1] *> r.  Proof. es. Qed.
Lemma S5_1 l r: l <* [0;1] <* [1;1] <{{A}} r -->* l <* [1;1] <{{A}} [0;1] *> r.  Proof. es. Qed.

Definition S1 := shift_rule_L _ _ _ _ _ S1_1.
Definition S2 := shift_rule_L _ _ _ _ _ S2_1.
Definition S3 := shift_rule_R _ _ _ _ _ S3_1.
Definition S4 := shift_rule_R _ _ _ _ _ S4_1.
Definition S6 := shift_rule_L _ _ _ _ _ S6_1.

Lemma S5 n: forall l r, l <* [0;1]^^n <* [1;1] <{{A}} r -->* l <* [1;1] <{{A}} [0;1]^^n *> r.
Proof.
  induction n; intros.
  - finish.
  - simpl_tape. follow S5_1. follow IHn. rewrite lpow_shift'. finish.
Qed.

(* ---------- finite turns ---------- *)
Lemma T1 r: 0inf <{{D}} r -->* 0inf <* [0;1] {{E}}> r.  Proof. es. Qed.
Lemma T2 l r: l {{E}}> [0;0;0] *> r -->* l <{{D}} [0;0;1] *> r.  Proof. es. Qed.
Lemma T3 l r: l {{E}}> [0;0;1] *> r -->* l <* [0;1;1] {{E}}> r.  Proof. es. Qed.
Lemma T4 l r: l {{E}}> [1;0] *> r -->* l <* [1;1] {{B}}> r.  Proof. es. Qed.
Lemma T5 l r: l {{B}}> [0;1] *> r -->* l <* [0;1] {{E}}> r.  Proof. es. Qed.
Lemma T6 l r: l {{B}}> [0;0] *> r -->* l <{{A}} [0;1] *> r.  Proof. es. Qed.
Lemma T7 l r: l <* [1;1] <{{A}} r -->* l <{{A}} [0;0] *> r.  Proof. es. Qed.
Lemma T8 l r: l <* [1;1;0;1;1] <{{A}} r -->* l <{{D}} [0;0;0;0;1] *> r.  Proof. es. Qed.
Lemma T9 l: l {{E}}> [1;0;0;1] *> 0inf -->* l <{{D}} [0;0;0] *> [1;0;0;1] *> 0inf.  Proof. es. Qed.
Lemma T10 l r: l <* [1;1] <{{D}} r -->* l <{{D}} [0;0] *> r.  Proof. es. Qed.
Lemma T11 l r: l <* [0] <{{D}} r -->* l <{{A}} [1] *> r.  Proof. es. Qed.
Lemma T12 r: 0inf <* [1;1] <{{A}} r -->* 0inf <* [0;1;1;0;1] {{E}}> r.  Proof. es. Qed.
Lemma T13 l r: l {{E}}> [1;0;1] *> r -->* l <* [0;1;1] {{E}}> r.  Proof. es. Qed.
Lemma T14 l r: l <* [1;1;0;1] <{{D}} r -->* l <{{D}} [0;1;0;0] *> r.  Proof. es. Qed.

(* ---------- digit lemmas (P section 2.1), the parent's renamed by sigma ---------- *)
Lemma rot01 n (Y : side) : [0;1]^^n *> (0 >> Y) = 0 >> ([1;0]^^n *> Y).
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Lemma rot10 n (Y : side) : [1;0]^^n *> (1 >> Y) = 1 >> ([0;1]^^n *> Y).
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Ltac fin := apply evstep_refl'; simpl_tape; repeat (rewrite rot01 || rewrite rot10); try reflexivity.

Lemma Lb u v l r:
  l {{E}}> [1;0]^^(S v) *> [0;1]^^(S u) *> r -->*
  l <* [1;1] <* [1;0]^^v <* [0;1]^^(S u) {{E}}> r.
Proof. follow T4. follow S3. follow T5. follow S4. fin. Qed.

Lemma Lf u v l r:
  l {{E}}> [1;0]^^(S v) *> [0;0] *> [0;1]^^u *> r -->*
  l <* [1;1] <{{A}} [1;0]^^v *> [0;1]^^(S u) *> r.
Proof. follow T4. follow S3. follow T6. follow S2. fin. Qed.

Lemma Rb u v l r:
  l <* [1;1] <* [1;0]^^v <* [0;1]^^u <* [1;1] <{{A}} r -->*
  l <* [1;1] <{{A}} [1;0]^^v *> [0;0] *> [0;1]^^u *> r.
Proof. follow S5. follow T7. follow S2. fin. Qed.

Lemma Ro u v l r:
  l <* [1;1] <* [1;0]^^v <* [0;1]^^(S u) <{{D}} [0;0;0] *> r -->*
  l <{{D}} [0;0;0] *> [0;1]^^v *> [1;0]^^(S u) *> [0;0] *> r.
Proof. follow S1. follow S6. follow T10. fin. Qed.

(* ---------- the family K (P section 1) and the initial segment (write-up section 2) ---------- *)
Inductive dg := d0 (u v : nat) | d1 (u v : nat).

(* right-side lists are nearest-cell first: d0 u v reads (10)^v 00 (01)^u from the head side *)
Definition dr (d : dg) (r : side) : side :=
  match d with
  | d0 u v => [1;0]^^v *> [0;0] *> [0;1]^^u *> r
  | d1 u v => [1;0]^^v *> [0;1]^^u *> r
  end.

(* digit lists are least significant digit first, as in the parent *)
Fixpoint app_ds (r : side) (ds : list dg) : side :=
  match ds with
  | [] => r
  | d :: t => dr d (app_ds r t)
  end.

Definition R0 : side := [1;0;0;1] *> 0inf.

Definition K (ds : list dg) (a b : nat) : Q * tape :=
  0inf <{{D}} [0;1]^^b *> [0;0;0] *> [0;1]^^a *> app_ds R0 ds.

Lemma init: c0 -->* K [d1 1 9] 8 1.
Proof. unfold K, R0. cbn. solve_init. Qed.

(* ---------- the parent's orientation-free list definitions, verbatim ---------- *)
Definition map1 (os : list (nat*nat)) := map (fun '(u,v) => d1 (S u) (S v)) os.
Definition map0 (os : list (nat*nat)) := map (fun '(u,v) => d0 (S u) v) os.

(* ---------- the list sweeps (the parent's LbS, RbS, RoS, renamed by sigma) ---------- *)
(* left-side accumulator: what Lb leaves behind for each all-ones digit (u+1,1,v+1) *)
Fixpoint rw (os : list (nat*nat)) (l : side) : side :=
  match os with
  | [] => l
  | (u,v) :: t => rw t (l <* [1;1] <* [1;0]^^v <* [0;1]^^(S u))
  end.

Lemma app_ds_app r xs ys : app_ds r (xs ++ ys) = app_ds (app_ds r ys) xs.
Proof. induction xs; cbn; congruence. Qed.

Lemma LbS os: forall l r, l {{E}}> app_ds r (map1 os) -->* rw os l {{E}}> r.
Proof.
  induction os as [|[u v] t IH]; intros.
  - finish.
  - cbn [map1 map app_ds dr rw]. follow Lb. apply IH.
Qed.

Lemma RbS os: forall l r, rw os l <* [1;1] <{{A}} r -->* l <* [1;1] <{{A}} app_ds r (map0 os).
Proof.
  induction os as [|[u v] t IH]; intros.
  - finish.
  - cbn [map0 map app_ds dr rw]. follow IH. apply Rb.
Qed.

Fixpoint ro_out (os : list (nat*nat)) (r : side) : side :=
  match os with
  | [] => r
  | (u,v) :: t => [0;1]^^v *> [1;0]^^(S u) *> [0;0] *> ro_out t r
  end.

Lemma RoS os: forall l r, rw os l <{{D}} [0;0;0] *> r -->* l <{{D}} [0;0;0] *> ro_out os r.
Proof.
  induction os as [|[u v] t IH]; intros.
  - finish.
  - cbn [ro_out rw]. follow IH. apply Ro.
Qed.

Fixpoint Oz (t : list (nat*nat)) (u : nat) : list dg :=
  match t with
  | [] => [d0 0 u]
  | (a, b) :: t' => d0 b u :: Oz t' (S a)
  end.

Definition Oout (os : list (nat*nat)) (A : nat) : list dg :=
  match os with
  | [] => []
  | (u, v) :: t => d1 (S v) A :: Oz t (S u)
  end.

Lemma Ozeq t: forall u r, [1;0]^^u *> [0;0] *> ro_out t r = app_ds r (Oz t u).
Proof.
  induction t as [|[a b] t IH]; intros.
  - reflexivity.
  - cbn [ro_out Oz app_ds dr]. rewrite <- IH. reflexivity.
Qed.

(* ---------- edge chunks (the parent's chunkA, chunkC, chunkO, renamed by sigma) ---------- *)
(* left-edge chunk shared by M and O: <D (01)^b 000 (01)^a -> (10)^(b+2) 110 (10)^a E> *)
Lemma chunkA a b r:
  0inf <{{D}} [0;1]^^b *> [0;0;0] *> [0;1]^^a *> r -->+
  0inf <* [0;1]^^(S (S b)) <* [0;1;1] <* [0;1]^^a {{E}}> r.
Proof. es. Qed.

(* end of M: (10)^(b+2) 110 (10)^a 11 <A -> <D (01)^(b+2) 000 (01)^(a+1) *)
Lemma chunkC a b r:
  0inf <* [0;1]^^(S (S b)) <* [0;1;1] <* [0;1]^^a <* [1;1] <{{A}} r -->*
  0inf <{{D}} [0;1]^^(S (S b)) *> [0;0;0] *> [0;1]^^(S a) *> r.
Proof.
  follow S5. follow T8. follow S1. fin.
Qed.

(* end of O: (10)^(b+2) 110 (10)^(a+1) <D 000 -> <D 01 000 (01)^(b+3) (10)^(a+1) 01 *)
Lemma chunkO a b r:
  0inf <* [0;1]^^(S (S b)) <* [0;1;1] <* [0;1]^^(S a) <{{D}} [0;0;0] *> r -->*
  0inf <{{D}} [0;1] *> [0;0;0] *> [0;1]^^(S (S (S b))) *> [1;0]^^(S a) *> [0;1] *> r.
Proof.
  follow S1. follow T11. follow S5. follow T12. follow S4. follow T13. follow S4. follow T2. follow S1. follow S1_1.
  rewrite (rot01 (S (S b))).
  follow (S6 (0inf <* [1;1;0;1]) ([1] *> [0;1]^^a *> [0;0;1] *> r) (S (S (S b)))).
  follow T14. fin.
Qed.

(* ---------- the three rules, statements verbatim from the parent ---------- *)
(* M: carry *)
Lemma M_spec os u v rest a b:
  K (map1 os ++ d0 u (S v) :: rest) a b -->+
  K (map0 os ++ d1 (S u) v :: rest) (S a) (S (S b)).
Proof.
  unfold K. rewrite !app_ds_app.
  follow10 chunkA.
  follow LbS.
  cbn [app_ds dr].
  follow Lf.
  follow RbS.
  apply chunkC.
Qed.

(* M with the flipped digit dropping: (u+1,1,0) fuses into the digit below it *)
Lemma Mdrop_spec os u2 v2 u rest a b:
  K (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest) a b -->+
  K (map0 os ++ d0 (S u2 + S u) v2 :: rest) (S a) (S (S b)).
Proof.
  follow10 (M_spec (os ++ [(u2,v2)]) u 0 rest a b).
  assert (E: app_ds R0 (map0 (os ++ [(u2,v2)]) ++ d1 (S u) 0 :: rest) =
             app_ds R0 (map0 os ++ d0 (S u2 + S u) v2 :: rest)).
  { unfold map0. rewrite map_app, <- app_assoc. cbn [map app].
    rewrite !app_ds_app. f_equal. cbn [app_ds dr].
    rewrite (lpow_add _ (S u2) (S u)), Str_app_assoc. reflexivity. }
  unfold K. rewrite E. finish.
Qed.

(* O: overflow *)
Lemma O_spec os a b: os <> [] ->
  K (map1 os) (S a) b -->+ K (Oout os (S a)) (S (S (S b))) 1.
Proof.
  intro H. destruct os as [|[u v] t]; [congruence|].
  unfold K.
  follow10 chunkA.
  follow LbS.
  unfold R0. follow T9.
  follow RoS.
  follow chunkO.
  apply evstep_refl'. cbn [Oout app_ds dr ro_out]. rewrite <- Ozeq. reflexivity.
Qed.

(* ================= abstract invariant (P section 3) ================= *)
Open Scope nat_scope.

Definition bof d := match d with d0 _ _ => 0 | d1 _ _ => 1 end.
Definition vof d := match d with d0 _ v => v | d1 _ v => v end.

(* R of a list: carries still to come into its last (least significant) digit *)
Fixpoint Rof (ds : list dg) : nat :=
  match ds with
  | [] => 0
  | d0 _ _ :: t => 2 * Rof t + 1
  | d1 _ _ :: t => 2 * Rof t
  end.

(* per-digit quantities, r = Rof of the digits above *)
Definition Rd d r := match d with d0 _ _ => 2*r+1 | d1 _ _ => 2*r end.
Definition ub d r := match d with d0 u _ => u + r + 1 | d1 u _ => u + r end.

Fixpoint AllD (P : dg -> nat -> nat -> Prop) (ds : list dg) : Prop :=
  match ds with
  | [] => True
  | d :: t => AllD P t /\ P d (Rof t) (length t)
  end.

Definition canon d := match d with d0 _ v => v >= 1 | d1 u v => u >= 1 /\ v >= 1 end.

Definition PA d r p :=
  canon d /\ vof d >= Rd d r + 1 /\ ub d r mod 2 = 1 /\ (p = 0 -> ub d r = 1).
Definition PB k d r p :=
  canon d /\ (vof d + bof d) mod 2 = 1 /\ ub d r >= 2^(p+k) /\ (k = 0 -> p = 0 -> d = d0 0 1).

Definition LSBok ds := match ds with [] => False | d :: _ => vof d >= Rof ds + 1 end.

Definition INV (s : list dg * nat * nat) : Prop :=
  let '(ds, a, b) := s in
  ds <> [] /\ a >= 1 /\ b mod 2 = 1 /\ (a + Rof ds) mod 2 = 0 /\
  a + Rof ds + 2 >= 2^(S (length ds)) /\ b + 3 + 2 * Rof ds >= 2^(S (length ds)) /\ LSBok ds /\
  ( (AllD PA ds /\ a + Rof ds + 1 >= 2^(S (length ds)))
  \/ AllD (PB 0) ds
  \/ (AllD (PB 1) ds /\ a + Rof ds + 1 >= 2^(S (length ds)) /\ b + 1 + 2 * Rof ds >= 2^(S (length ds))) ).

Definition Kc (s : list dg * nat * nat) : Q * tape := let '(ds, a, b) := s in K ds a b.

(* ---------- arithmetic helpers ---------- *)
Lemma pow2S n : 2^(S n) = 2 * 2^n.
Proof. apply Nat.pow_succ_r'. Qed.
Lemma pow2pos n : 2^n >= 1.
Proof. pose proof (Nat.pow_nonzero 2 n). lia. Qed.

Lemma Rof_bound ds : Rof ds + 1 <= 2^(length ds).
Proof.
  induction ds as [|[u v|u v] t IH]; cbn [Rof length]; rewrite ?pow2S; cbn; lia.
Qed.

Lemma Rof_map1 os X : Rof (map1 os ++ X) = 2^(length os) * Rof X.
Proof.
  induction os as [|[u v] t IH]; cbn [map1 map app Rof length] in *.
  - cbn; lia.
  - unfold map1 in IH. rewrite IH, pow2S. lia.
Qed.

Lemma Rof_map1' os : Rof (map1 os) = 0.
Proof. rewrite <- (app_nil_r (map1 os)), Rof_map1. cbn. lia. Qed.

Lemma len_map1 os : length (map1 os) = length os.
Proof. apply length_map. Qed.
Lemma len_map0 os : length (map0 os) = length os.
Proof. apply length_map. Qed.

Lemma AllD_app P xs ys : AllD P (xs ++ ys) -> AllD P ys.
Proof. induction xs; cbn; tauto. Qed.

Lemma AllD_last P xs d : AllD P (xs ++ [d]) -> P d 0 0.
Proof. intro H. apply AllD_app in H. cbn in H. tauto. Qed.

Lemma AllD_canon (P : dg -> nat -> nat -> Prop) ds :
  (forall d r p, P d r p -> canon d) -> AllD P ds -> Forall canon ds.
Proof.
  intro HP. induction ds; cbn; intros; constructor; firstorder.
Qed.

Lemma decomp ds : Forall canon ds ->
  (exists os, ds = map1 os) \/ (exists os u v rest, ds = map1 os ++ d0 u (S v) :: rest).
Proof.
  induction ds as [|[u v|u v] t IH]; intro H.
  - left. exists (@nil (nat*nat)). reflexivity.
  - inversion H; subst. cbn in *. destruct v as [|v]; [lia|].
    right. exists (@nil (nat*nat)), u, v, t. reflexivity.
  - inversion H; subst. cbn in *. destruct u as [|u]; [lia|]. destruct v as [|v]; [lia|].
    destruct (IH ltac:(assumption)) as [[os E]|[os [u' [v' [rest E]]]]]; subst.
    + left. exists ((u,v)::os). reflexivity.
    + right. exists ((u,v)::os), u', v', rest. reflexivity.
Qed.

(* ---------- F1: a carry without a drop keeps every ubar/vbar ---------- *)
Lemma F1 (P : dg -> nat -> nat -> Prop) os u v rest:
  (forall u v r p, P (d0 u (S (S v))) r p -> P (d1 (S u) (S v)) r p) ->
  (forall u v r p, P (d1 (S u) (S v)) (S r) p -> P (d0 (S u) v) r p) ->
  AllD P (map1 os ++ d0 u (S (S v)) :: rest) ->
  AllD P (map0 os ++ d1 (S u) (S v) :: rest) /\
  Rof (map1 os ++ d0 u (S (S v)) :: rest) = S (Rof (map0 os ++ d1 (S u) (S v) :: rest)) /\
  length (map0 os ++ d1 (S u) (S v) :: rest) = length (map1 os ++ d0 u (S (S v)) :: rest).
Proof.
  intros H0 H1. induction os as [|[u' v'] t IH]; intros HA.
  - cbn [map1 map0 map app AllD Rof length] in *. destruct HA as [HA HP].
    repeat split; auto. lia.
  - unfold map1, map0 in *. cbn [map app AllD Rof length] in *. destruct HA as [HA HP].
    destruct (IH HA) as [IA [IR IL]].
    rewrite IR in HP. rewrite IL. repeat split; auto. lia.
Qed.

Lemma PA_touch0 u v r p : PA (d0 u (S (S v))) r p -> PA (d1 (S u) (S v)) r p.
Proof. unfold PA, canon, Rd, ub, vof. intros (H1 & H2 & H3 & H4).
  repeat split; try lia; intro E; specialize (H4 E); lia. Qed.

Lemma PA_touch1 u v r p : PA (d1 (S u) (S v)) (S r) p -> PA (d0 (S u) v) r p.
Proof. unfold PA, canon, Rd, ub, vof. intros (H1 & H2 & H3 & H4).
  repeat split; try lia; intro E; specialize (H4 E); lia. Qed.

Lemma PB_touch0 k u v r p : PB k (d0 u (S (S v))) r p -> PB k (d1 (S u) (S v)) r p.
Proof. unfold PB, canon, ub, vof, bof. intros (H1 & H2 & H3 & H4).
  repeat split; try lia; intros E1 E2; specialize (H4 E1 E2); discriminate. Qed.

Lemma PB_touch1 k u v r p : PB k (d1 (S u) (S v)) (S r) p -> PB k (d0 (S u) v) r p.
Proof. unfold PB, canon, ub, vof, bof. intros (H1 & H2 & H3 & H4).
  repeat split; try lia; intros E1 E2; specialize (H4 E1 E2); discriminate. Qed.

(* ---------- F2: a drop ---------- *)
Definition Rel r ro rn := rn + 1 <= ro /\ ro <= 2 * (rn + 1) /\ (r = 0 -> ro = rn + 1).

Lemma PB_chain k k' r u v ro rn p :
  (k' = k \/ (k = 0 /\ k' = 1 /\ r = 0)) -> Rel r ro rn -> p >= 1 ->
  PB k (d1 (S u) (S v)) ro (S p) -> PB k' (d0 (S u) v) rn p.
Proof.
  unfold PB, Rel, canon, ub, vof, bof. intros Hk (R1 & R2 & R3) Hp (H1 & H2 & H3 & H4).
  cbn [Nat.add] in H3. rewrite pow2S in H3.
  repeat split; try lia.
  destruct Hk as [Hk|(Hk & Hk' & Hr)]; subst.
  - lia.
  - specialize (R3 eq_refl). rewrite Nat.add_0_r in H3. rewrite (Nat.add_1_r p), pow2S. lia.
Qed.

Lemma PB_abs k k' r p u2 v2 u :
  ((k' = k /\ (k = 0 -> p >= 1)) \/ (k = 0 /\ k' = 1 /\ p = 0 /\ r = 0)) ->
  PB k (d0 u 1) r p -> PB k (d1 (S u2) (S v2)) (2*r+1) (S p) -> PB k' (d0 (S u2 + S u) v2) r p.
Proof.
  unfold PB, canon, ub, vof, bof. intros Hk (A1 & A2 & A3 & A4) (H1 & H2 & H3 & H4).
  destruct Hk as [(Hk & Hp)|(Hk & Hk' & Hp & Hr)]; subst.
  - repeat split; try lia; try (intros E1 E2; specialize (Hp E1); lia).
  - cbn [Nat.pow Nat.add] in *. repeat split; try lia; try (intros E1; discriminate).
Qed.

Lemma F2chain k k' r os X X' :
  (k' = k \/ (k = 0 /\ k' = 1 /\ r = 0)) -> X' <> [] ->
  AllD (PB k) (map1 os ++ X) -> AllD (PB k') X' -> Rel r (Rof X) (Rof X') -> length X = S (length X') ->
  AllD (PB k') (map0 os ++ X') /\ Rel r (Rof (map1 os ++ X)) (Rof (map0 os ++ X')) /\
  length (map1 os ++ X) = S (length (map0 os ++ X')).
Proof.
  intros Hk HX'. induction os as [|[u v] t IH]; intros HA HA' HR HL.
  - cbn [map1 map0 map app] in *. auto.
  - unfold map1, map0 in *. cbn [map app AllD Rof length] in *. destruct HA as [HA HP].
    destruct (IH HA HA' HR HL) as [IA [IR IL]].
    rewrite IL in HP.
    split; [split|split].
    + exact IA.
    + eapply PB_chain; eauto.
      rewrite length_app. destruct X'; [congruence|]. cbn. lia.
    + unfold Rel in *. destruct IR as (R1 & R2 & R3). repeat split; try lia;
      try (intro E; specialize (R3 E); lia).
    + lia.
Qed.

Lemma F2 k k' os u2 v2 u rest:
  ((k' = k /\ (k = 0 -> rest <> [])) \/ (k = 0 /\ k' = 1 /\ rest = [])) ->
  AllD (PB k) (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest) ->
  AllD (PB k') (map0 os ++ d0 (S u2 + S u) v2 :: rest) /\
  Rel (Rof rest) (Rof (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest))
      (Rof (map0 os ++ d0 (S u2 + S u) v2 :: rest)) /\
  length (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest) = S (length (map0 os ++ d0 (S u2 + S u) v2 :: rest)).
Proof.
  intros Hk HA.
  replace (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest)
    with (map1 os ++ (d1 (S u2) (S v2) :: d0 u 1 :: rest)) in *
    by (unfold map1; rewrite map_app, <- app_assoc; reflexivity).
  pose proof (AllD_app _ _ _ HA) as HX. cbn [AllD Rof length] in HX.
  destruct HX as [[Hrest Hdrop] Habs].
  apply (F2chain k k' (Rof rest)).
  - destruct Hk as [(Hk & _)|(Hk & Hk' & Hr)]; [left; auto|right; subst; auto].
  - congruence.
  - exact HA.
  - cbn [AllD Rof length]. split.
    + destruct Hk as [(Hk & _)|(Hk & Hk' & Hr)]; subst; [exact Hrest|exact I].
    + eapply PB_abs; [|exact Hdrop|exact Habs].
      destruct Hk as [(Hk & Hne)|(Hk & Hk' & Hr)]; subst.
      * left. split; auto. intro E. specialize (Hne E). destruct rest; [congruence|]. cbn. lia.
      * right. cbn. auto.
  - unfold Rel. cbn [Rof]. lia.
  - reflexivity.
Qed.

(* ---------- F3: the overflow ---------- *)
Lemma Oz_len t u : length (Oz t u) = S (length t).
Proof. revert u. induction t as [|[a b] t IH]; intro u; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma Oz_R t u : Rof (Oz t u) + 1 = 2^(S (length t)).
Proof.
  revert u. induction t as [|[a b] t IH]; intro u; cbn [Oz Rof length].
  - cbn. reflexivity.
  - specialize (IH (S a)). rewrite (pow2S (S (length t))). lia.
Qed.

Lemma Oz_AB t : forall u, AllD PA (map1 t) -> u mod 2 = 1 -> (t = [] -> u = 1) -> AllD (PB 0) (Oz t u).
Proof.
  induction t as [|[a b] t IH]; intros u HA Hu Ht.
  - cbn. split; [exact I|]. unfold PB, canon, ub, vof, bof. cbn.
    rewrite (Ht eq_refl). repeat split; lia.
  - unfold map1 in HA. cbn [map AllD] in HA. destruct HA as [HA HP]. fold (map1 t) in HA, HP.
    rewrite Rof_map1', len_map1 in HP. unfold PA, canon, Rd, ub, vof in HP. destruct HP as (P1 & P2 & P3 & P4).
    cbn [Oz AllD]. split.
    + apply IH; [exact HA | lia | intro E; subst t; specialize (P4 eq_refl); lia].
    + pose proof (Oz_R t (S a)) as HR. rewrite Oz_len.
      unfold PB, canon, ub, vof, bof. rewrite !Nat.add_0_r.
      repeat split; try lia; try (intros E1 E2; discriminate).
Qed.

Lemma Oz_CA t : forall u, AllD (PB 1) (map1 t) -> u >= 2^(S (length t)) -> AllD PA (Oz t u).
Proof.
  induction t as [|[a b] t IH]; intros u HA Hu.
  - cbn. split; [exact I|]. unfold PA, canon, Rd, ub, vof. cbn in *. repeat split; lia.
  - unfold map1 in HA. cbn [map AllD] in HA. destruct HA as [HA HP]. fold (map1 t) in HA, HP.
    rewrite Rof_map1', len_map1 in HP. unfold PB, canon, ub, vof, bof in HP. destruct HP as (P1 & P2 & P3 & P4).
    cbn [Oz AllD]. split.
    + apply IH; [exact HA|]. rewrite (Nat.add_1_r (length t)) in P3. lia.
    + pose proof (Oz_R t (S a)) as HR. rewrite Oz_len.
      cbn [length] in Hu. rewrite (pow2S (S (length t))), (pow2S (length t)) in Hu. rewrite (pow2S (length t)) in HR.
      unfold PA, canon, Rd, ub, vof.
      repeat split; try lia; try (intros E1; discriminate).
Qed.

(* ---------- bookkeeping for one carry ---------- *)
Lemma Rof_M os u v rest :
  Rof (map1 os ++ d0 u (S v) :: rest) = S (Rof (map0 os ++ d1 (S u) v :: rest)).
Proof.
  induction os as [|[a b] t IH]; unfold map1, map0 in *; cbn [map app Rof] in *; lia.
Qed.

Lemma len_M os u v w x rest :
  length (map0 os ++ d1 w x :: rest) = length (map1 os ++ d0 u v :: rest).
Proof. rewrite !length_app, len_map0, len_map1. reflexivity. Qed.

Lemma LSB_M os u v rest :
  LSBok (map1 os ++ d0 u (S (S v)) :: rest) -> LSBok (map0 os ++ d1 (S u) (S v) :: rest).
Proof.
  intro H. pose proof (Rof_M os u (S v) rest) as E.
  destruct os as [|[a b] t]; cbn [map1 map0 map app LSBok vof] in *; lia.
Qed.

Lemma Rof_head1 os X : os <> [] -> Rof (map1 os ++ X) mod 2 = 0.
Proof.
  destruct os as [|[u v] t]; [congruence|]. intros _. unfold map1. cbn [map app Rof]. lia.
Qed.

Lemma Rof_head0 os x y rest : Rof (map0 os ++ d0 x y :: rest) mod 2 = 1.
Proof. destruct os as [|[u v] t]; unfold map0; cbn [map app Rof]; lia. Qed.

Lemma LSB_drop os u2 v2 u rest r :
  LSBok (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest) ->
  Rel r (Rof (map1 (os ++ [(u2,v2)]) ++ d0 u 1 :: rest)) (Rof (map0 os ++ d0 (S u2 + S u) v2 :: rest)) ->
  LSBok (map0 os ++ d0 (S u2 + S u) v2 :: rest).
Proof.
  unfold Rel. intros H (R1 & R2 & R3).
  destruct os as [|[a b] t]; cbn [map1 map0 map app LSBok vof] in *; lia.
Qed.

Lemma app_cons_ne {A} (xs : list A) y ys : xs ++ y :: ys <> [].
Proof. destruct xs; discriminate. Qed.

Ltac pw := repeat (rewrite pow2S in *).

(* ---------- closure: every INV state takes a macro step into INV ---------- *)
Lemma macro_step s : INV s -> exists s', Kc s -->+ Kc s' /\ INV s'.
Proof.
  destruct s as [[ds a] b]. unfold INV.
  intros (Hne & Ha & Hb & Hpar & HS & HT & HL & Hcls).
  assert (Hc : Forall canon ds).
  { destruct Hcls as [[HA _]|[HB|[HC _]]]; (eapply AllD_canon; [|eassumption]);
    unfold PA, PB; intros; tauto. }
  destruct (decomp ds Hc) as [[os E]|[os [u [v [rest E]]]]]; subst ds.
  - (* all bits 1: overflow O *)
    destruct a as [|a]; [lia|].
    assert (Hos : os <> []) by (intro; subst; apply Hne; reflexivity).
    rewrite Rof_map1', len_map1 in *.
    destruct os as [|[u v] t]; [congruence|].
    pose proof (Oz_R t (S u)) as HR. pose proof (Oz_len t (S u)) as HLz.
    exists (Oout ((u,v)::t) (S a), S (S (S b)), 1). split.
    { apply O_spec. congruence. }
    unfold INV. cbn [Oout length Rof LSBok vof AllD] in *. rewrite HLz.
    destruct Hcls as [[HA HS1]|[HB|[HC [HS1 HT2]]]].
    + (* A -> B *)
      unfold map1 in HA. cbn [map AllD] in HA. fold (map1 t) in HA. destruct HA as [HA HP].
      rewrite Rof_map1', len_map1 in HP. unfold PA, canon, Rd, ub, vof in HP. destruct HP as (P1 & P2 & P3 & P4).
      assert (HB' : AllD (PB 0) (Oz t (S u))).
      { apply Oz_AB; [exact HA | lia | intro E; subst t; specialize (P4 eq_refl); lia]. }
      pw.
      repeat split; try lia; try discriminate.
      right. left. split; [exact HB'|].
      unfold PB, canon, ub, vof, bof. rewrite ?Nat.add_0_r. pw.
      repeat split; try lia; try (intros E1 E2; discriminate).
    + (* B cannot be all ones: its top is (0,0,1) *)
      exfalso. destruct (exists_last Hos) as [os' [o E]]. rewrite E in HB.
      unfold map1 in HB. rewrite map_app in HB. apply AllD_last in HB.
      destruct o as [x y]. unfold PB in HB. destruct HB as (_ & _ & _ & H4).
      specialize (H4 eq_refl eq_refl). discriminate.
    + (* C -> A *)
      unfold map1 in HC. cbn [map AllD] in HC. fold (map1 t) in HC. destruct HC as [HC HP].
      rewrite Rof_map1', len_map1 in HP. unfold PB, canon, ub, vof, bof in HP. destruct HP as (P1 & P2 & P3 & P4).
      assert (HA' : AllD PA (Oz t (S u))).
      { apply Oz_CA; [exact HC|]. rewrite (Nat.add_1_r (length t)) in P3. lia. }
      pw.
      repeat split; try lia; try discriminate.
      left. split; [split; [exact HA'|]|].
      * unfold PA, canon, Rd, ub, vof.
        repeat split; try lia; try (intros E1; discriminate).
      * lia.
  - (* some bit 0: carry M *)
    destruct v as [|v].
    + (* the flipped digit drops *)
      destruct Hcls as [[HA _]|[HB|[HC [HS1 HT2]]]].
      { exfalso. apply AllD_app in HA. cbn [AllD] in HA. destruct HA as [_ HP].
        unfold PA, Rd, vof in HP. lia. }
      all: destruct os as [|o os0] eqn:Eos;
        [ exfalso; cbn [map1 map app LSBok vof Rof] in HL; lia | ].
      all: assert (Hos : os <> []) by (subst os; discriminate).
      all: rewrite <- Eos in *; clear Eos o os0.
      all: destruct (exists_last Hos) as [os' [[u2 v2] Eo]]; subst os.
      all: exists (map0 os' ++ d0 (S u2 + S u) v2 :: rest, S a, S (S b)); split;
        [ apply Mdrop_spec | unfold INV ].
      * (* B *)
        destruct rest as [|d rest'] eqn:Er.
        -- (* top fall: B -> C *)
           rewrite <- Er in *.
           destruct (F2 0 1 os' u2 v2 u rest) as (HA' & HR & HLn); [right; auto | exact HB |].
           pose proof (Rof_bound (map0 os' ++ d0 (S u2 + S u) v2 :: rest)) as Hbd.
           pose proof (Rof_head1 (os' ++ [(u2,v2)]) (d0 u 1 :: rest) ltac:(apply app_cons_ne)) as Hp1.
           pose proof (Rof_head0 os' (S u2 + S u) v2 rest) as Hp0.
           pose proof (LSB_drop _ _ _ _ _ _ HL HR) as HL'.
           unfold Rel in HR. subst rest. cbn [Rof] in HR. destruct HR as (R1 & R2 & R3).
           specialize (R3 eq_refl).
           rewrite HLn in *. pw.
           repeat split; try lia; try apply app_cons_ne; auto.
           right. right. repeat split; auto; lia.
        -- (* B -> B *)
           rewrite <- Er in *.
           destruct (F2 0 0 os' u2 v2 u rest) as (HA' & HR & HLn);
             [left; split; auto; intros _; subst rest; discriminate | exact HB |].
           pose proof (Rof_bound (map0 os' ++ d0 (S u2 + S u) v2 :: rest)) as Hbd.
           pose proof (Rof_head1 (os' ++ [(u2,v2)]) (d0 u 1 :: rest) ltac:(apply app_cons_ne)) as Hp1.
           pose proof (Rof_head0 os' (S u2 + S u) v2 rest) as Hp0.
           pose proof (LSB_drop _ _ _ _ _ _ HL HR) as HL'.
           unfold Rel in HR. destruct HR as (R1 & R2 & R3).
           rewrite HLn in *. pw.
           repeat split; try lia; try apply app_cons_ne; auto.
      * (* C -> C *)
        destruct (F2 1 1 os' u2 v2 u rest) as (HA' & HR & HLn);
          [left; split; auto; intro E; discriminate | exact HC |].
        pose proof (Rof_bound (map0 os' ++ d0 (S u2 + S u) v2 :: rest)) as Hbd.
        pose proof (Rof_head1 (os' ++ [(u2,v2)]) (d0 u 1 :: rest) ltac:(apply app_cons_ne)) as Hp1.
        pose proof (Rof_head0 os' (S u2 + S u) v2 rest) as Hp0.
        pose proof (LSB_drop _ _ _ _ _ _ HL HR) as HL'.
        unfold Rel in HR. destruct HR as (R1 & R2 & R3).
        rewrite HLn in *. pw.
        repeat split; try lia; try apply app_cons_ne; auto.
        right. right. repeat split; auto; lia.
    + (* no drop *)
      exists (map0 os ++ d1 (S u) (S v) :: rest, S a, S (S b)). split; [apply M_spec | unfold INV].
      pose proof (Rof_M os u (S v) rest) as ER.
      pose proof (len_M os u (S (S v)) (S u) (S v) rest) as EL.
      pose proof (LSB_M os u v rest HL) as HL'.
      rewrite EL.
      destruct Hcls as [[HA HS1]|[HB|[HC [HS1 HT2]]]].
      * destruct (F1 PA os u v rest PA_touch0 PA_touch1 HA) as (HA' & _ & _).
        repeat split; try lia; try apply app_cons_ne; auto.
        left. split; [exact HA'|lia].
      * destruct (F1 (PB 0) os u v rest (PB_touch0 0) (PB_touch1 0) HB) as (HB' & _ & _).
        repeat split; try lia; try apply app_cons_ne; auto.
      * destruct (F1 (PB 1) os u v rest (PB_touch0 1) (PB_touch1 1) HC) as (HC' & _ & _).
        repeat split; try lia; try apply app_cons_ne; auto.
        right. right. repeat split; auto; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (K [d1 1 9] 8 1) with (Kc ([d1 1 9], 8, 1)).
  apply progress_nonhalt_cond with (P := INV).
  - exact macro_step.
  - unfold INV. cbn. repeat split; try lia; try discriminate.
    left. unfold PA, canon, Rd, ub, vof. cbn. repeat split; lia.
Qed.


(*
```
1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB---

K(d_1 .. d_m; a, b) := 0^inf <D (01)^b 000 (01)^a d~_m .. d~_1 1001 0^inf
digit (u,0,v) := (10)^v 00 (01)^u,   (u,1,v) := (10)^v (01)^u      (d_m least significant)
start: 0^inf A> 0^inf  -->*  K((1,1,9); 8, 1)                       (step 687)

M  (j* = last bit-0 digit):
   K(.., (u,0,v), (u_j,1,v_j)_{j>j*}; a, b) -->+ K(.., (u+1,1,v-1), (u_j,0,v_j-1)_{j>j*}; a+1, b+2)
   v = 1: (u+1,1,0) fuses into the next digit: (u',0,v'-1) becomes (u'+u+1,0,v'-1)
O  (all bits 1):
   K((u_1,1,v_1) .. (u_m,1,v_m); a, b) -->+ K((0,0,u_1), (v_1-1,0,u_2), .., (v_m,1,a); b+3, 1)

per digit, r = R of the digits above:  R = 2r+1-bit,  ubar = u + r + 1 - bit,  vbar = v - R
INV: m >= 1, a >= 1, b odd, a+R even, a+R+2 >= 2^(m+1), b+3+2R >= 2^(m+1), v_m >= R+1, and
  A: every digit canonical, v >= R+1, ubar odd, ubar_1 = 1;  a+R+1 >= 2^(m+1)
  B: every digit canonical, v+bit odd, ubar_j >= 2^(j-1), d_1 = (0,0,1)
  C: every digit canonical, v+bit odd, ubar_j >= 2^j;  a+R+1 >= 2^(m+1), b+1+2R >= 2^(m+1)
INV -> a macro step (M, M with a drop, or O) into INV   (A->A, A->B, B->B, B->C, C->C, C->A)
```
*)
