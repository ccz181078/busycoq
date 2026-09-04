From Coq Require Import Bool List Arith NArith ZArith ZifyNat Lia.
From BusyCoq Require Import
  Individual62 Longitudinal LongitudinalHalt ES_v3 Eqb FastRev.

Import ListNotations.

Ltac es_v3_pre ::= ut.


Module Loop4MonoFast.
Open Scope N_scope.

(* The four word families D1--D4.  Parameters stay below a few hundred in
   the certified runs, so machine integers are unnecessary here. *)
Inductive word := A (n:N) | B (n:N) | C (n:N) | D (n:N).

(* A standard two-stack FIFO.  [FastRev.fast_rev] makes every element move
   once per rebuild, so pop/snoc are amortised O(1). *)
Record dseq := DSeq { front : list N; back : list N }.

Definition contents (q:dseq) := front q ++ FastRev.fast_rev (back q).

Definition of_list xs := DSeq xs [].

Definition uncons (q:dseq) : option (N*dseq) :=
  match front q with
  | x::f => Some (x,DSeq f (back q))
  | [] =>
      match FastRev.fast_rev (back q) with
      | [] => None
      | x::xs => Some (x,DSeq xs [])
      end
  end.

Definition snoc (q:dseq) x := DSeq (front q) (x::back q).

(* [done] is the already crossed positive-A prefix, in reverse order.
   Keeping the cursor at the first non-A word makes every local h1 call
   amortised O(1), even when the logical prefix is long. *)
Record scan := Scan { done : list N; rest : list word }.

Fixpoint normalize_aux (d:list N) (r:list word) : scan :=
  match r with
  | A n::r' => if N.eqb n 0 then Scan d r
               else normalize_aux (n::d) r'
  | _ => Scan d r
  end.

Definition normalize s := normalize_aux (done s) (rest s).
Definition scan_list s := List.map A (FastRev.fast_rev (done s)) ++ rest s.

Definition call (s:scan) : option scan :=
  let s := normalize s in
  match rest s with
  | [] => Some (Scan (3::done s) [])
  | B n::r =>
      match r with
      | [] => Some (Scan (n+3::done s) [])
      | A m::r' => Some (normalize (Scan (n+3::done s) (C m::r')))
      | B m::r' => Some (normalize (Scan (n+3::done s) (D m::r')))
      | C m::r' => Some (normalize (Scan (done s) (B (n+m+3)::r')))
      | D m::r' => Some (normalize (Scan (n+m+4::done s) r'))
      end
  | C n::r =>
      if N.eqb n 0 then None else
        match done s with
        | m::d => Some (normalize (Scan (m+2::d) (B (N.pred n)::r)))
        | [] => None
        end
  | D n::r =>
      match done s with
        | m::d =>
            if N.eqb n 0
            then Some (normalize (Scan (m+2::d) (A 0::r)))
            else Some (normalize (Scan (n::m+2::d) r))
        | [] => None
      end
  | _ => None
  end.

(* Two successive calls on [B x; A y] are always D21 followed by D13.
   This pair accounts for over 96% of all local calls in both certificates,
   so execute the proved composite directly. *)
Fixpoint calls_nat_norm (fuel:nat) (d:list N) (r:list word) : option scan :=
  match fuel with
  | O => Some (Scan d r)
  | S fuel' =>
      match fuel' with
      | S fuel'' =>
          match r with
          | B x::A y::r' =>
              if N.eqb y 0 then
                match call (Scan d r) with
                | Some s' => calls_nat_norm fuel' (done s') (rest s')
                | None => None
                end
              else calls_nat_norm fuel''
                     (x+5::d) (B (N.pred y)::r')
          | _ =>
              match call (Scan d r) with
              | Some s' => calls_nat_norm fuel' (done s') (rest s')
              | None => None
              end
          end
      | O =>
          match call (Scan d r) with
          | Some s' => calls_nat_norm fuel' (done s') (rest s')
          | None => None
          end
      end
  end.

Definition calls (n:N) (s:scan) : option scan :=
  let s := normalize s in
  calls_nat_norm (N.to_nat n) (done s) (rest s).

Definition service (e:N) (edge:list word)
  : option (N*N*list word) :=
  match call (Scan [] edge) with
  | None => None
  | Some s1 =>
      match scan_list s1 with
      | A z::tail =>
          if N.eqb z 0 then None else
          match calls (e+7) (Scan [] (B (N.pred z)::tail)) with
          | None => None
          | Some s2 =>
              match scan_list s2 with
              | A x::A y::edge' =>
                  if (4 <=? x)%N && (2 <=? y)%N
                  then Some (x-4,y-2,edge') else None
              | _ => None
              end
          end
      | _ => None
      end
  end.

Record machine := Machine { queue : dseq; edge : list word }.
Inductive result := Halt | Failed.

Fixpoint all_A3 (r:list word) : bool :=
  match r with [] => true | A 3::r' => all_A3 r' | _ => false end.

Definition halt_edgeb (run:nat) (r:list word) : bool :=
  match r with
  | A 0::r' => Nat.eqb (length r') run && all_A3 r'
  | _ => false
  end.

(* The successful fast path above returns only its final scan.  On the unique
   terminal interval a D4(0) call returns D1(0), and the following h1 halts
   before the service returns.  This small fallback records that intermediate
   event; it is evaluated only after [service] has failed. *)
Fixpoint calls_haltb (run fuel:nat) (s:scan) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      let s := normalize s in
      match call s with
      | Some s' => calls_haltb run fuel' s'
      | None => halt_edgeb run (rest s)
      end
  end.

Definition service_haltb (run:nat) (e:N) (edge:list word) : bool :=
  match call (Scan [] edge) with
  | None => halt_edgeb run (rest (normalize (Scan [] edge)))
  | Some s1 =>
      match scan_list s1 with
      | A z::tail =>
          if N.eqb z 0 then false else
          calls_haltb run (N.to_nat (e+7))
            (Scan [] (B (N.pred z)::tail))
      | _ => false
      end
  end.

Definition step (run:nat) (m:machine) : machine+result :=
  match uncons (queue m) with
  | None => inr Failed
  | Some (e,q') =>
      match service e (edge m) with
      | Some p => let '(x,y,r') := p in
                  inl (Machine (snoc (snoc q' x) y) r')
      | None => if service_haltb run e (edge m)
                then inr Halt else inr Failed
      end
  end.

Fixpoint continue_steps (run:nat) (fuel:nat) (s:machine+result)
    : machine+result :=
  match fuel,s with
  | O,_ => s
  | S fuel',inl m => continue_steps run fuel' (step run m)
  | S _,inr _ => s
  end.

Definition step8 run m := continue_steps run 7 (step run m).

Definition init109 :=
  Machine (of_list [1;3;5]) [A 7;A 7;B 2;A 3;A 3].
Definition init109b :=
  Machine (of_list [1;3;5]) [A 7;B 2;A 3;A 3].
(* test_109 already has a valid two-item residual queue at reset 0. *)
Definition start109 :=
  Machine (of_list [1;1]) (repeat (A 3) 6).

Definition run8 runlen bound init :=
  N_iter_until (step8 runlen) (inl init) bound.

Definition stoppedb (x:machine+result) :=
  match x with inr Halt => true | _ => false end.

End Loop4MonoFast.


Open Scope N_scope.
Open Scope list_scope.
Open Scope sym_scope.

Module Loop4MonoProof.
Module P := Loop4MonoFast.

Definition D1 n := [0;0;1] ++ [1;1]^^n.
Definition D2 n := [0;0;1;1] ++ [1;1]^^n.
Definition D3 n := [0;1] ++ [1;1]^^n.
Definition D4 n := [0;1;1] ++ [1;1]^^n.

Definition word_bits w :=
  match w with
  | P.A n => D1 (N.to_nat n)
  | P.B n => D2 (N.to_nat n)
  | P.C n => D3 (N.to_nat n)
  | P.D n => D4 (N.to_nat n)
  end.

Fixpoint words_side (ws:list P.word) : side :=
  match ws with
  | [] => 0inf
  | w::ws' => word_bits w *> words_side ws'
  end.

Lemma uncons_contents q :
  match P.uncons q with
  | None => P.contents q=[]
  | Some (x,q') => P.contents q=x::P.contents q'
  end.
Proof.
  destruct q as [[|x front] back]; [|reflexivity].
  unfold P.uncons,P.contents. cbn [P.front P.back].
  destruct (FastRev.fast_rev back) as [|y ys] eqn:E.
  - reflexivity.
  - cbn [FastRev.fast_rev FastRev.fast_rev_append].
    rewrite app_nil_r. reflexivity.
Qed.

Lemma snoc_contents q x :
  P.contents (P.snoc q x)=P.contents q++[x].
Proof.
  destruct q as [front back]. unfold P.snoc,P.contents.
  cbn [P.front P.back]. rewrite FastRev.fast_rev_cons,app_assoc.
  reflexivity.
Qed.

Definition scan_words (s:P.scan) :=
  (List.map P.A (rev (P.done s)) ++ P.rest s)%list.

Lemma scan_words_eq s : scan_words s=P.scan_list s.
Proof.
  unfold scan_words,P.scan_list. rewrite FastRev.fast_rev_spec. reflexivity.
Qed.

Lemma normalize_aux_words d r :
  scan_words (P.normalize_aux d r)=
  (List.map P.A (rev d)++r)%list.
Proof.
  unfold scan_words.
  revert d; induction r as [|w r IH]; intros d;
    cbn [P.normalize_aux P.done P.rest].
  - rewrite app_nil_r. reflexivity.
  - destruct w as [n|n|n|n]; cbn [P.normalize_aux].
    + destruct (N.eqb n 0) eqn:E; cbn [P.done P.rest].
      * reflexivity.
      * rewrite IH. cbn. rewrite map_app.
        change ((List.map P.A (rev d)++[P.A n])++r =
                List.map P.A (rev d)++[P.A n]++r)%list.
        symmetry. apply app_assoc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma normalize_words s : scan_words (P.normalize s)=scan_words s.
Proof. destruct s. apply normalize_aux_words. Qed.

Definition positive (n:N) := (0<n)%N.
Definition valid_scan (s:P.scan) := Forall positive (P.done s).

Lemma normalize_aux_valid d r :
  Forall positive d -> valid_scan (P.normalize_aux d r).
Proof.
  revert d; induction r as [|w r IH]; intros d Hd; cbn [P.normalize_aux valid_scan].
  - exact Hd.
  - destruct w as [n|n|n|n]; cbn [P.normalize_aux valid_scan]; try exact Hd.
    destruct (N.eqb n 0) eqn:E; [exact Hd|].
    apply IH. constructor; [apply N.eqb_neq in E; apply N.neq_0_lt_0; exact E|exact Hd].
Qed.

Lemma normalize_valid s : valid_scan s -> valid_scan (P.normalize s).
Proof. destruct s. apply normalize_aux_valid. Qed.

Fixpoint layer (qs:list N) (tail:side) : side :=
  match qs with
  | [] => tail
  | e::qs' => D1 (N.to_nat e+2*S (length qs')) *> layer qs' tail
  end.

Definition denote_machine (m:P.machine) :=
  layer (P.contents (P.queue m)) (words_side (P.edge m)).

Section Rules.
Local Opaque D1 D2 D3 D4.
Variable tm:TM.
Variable h1:list (DH0*DH0).

Hypothesis H_D1 : forall n,
  segRLs tm h1 h1 (D1 (1+n)) (D1 (1+n)).
Hypothesis H_D13 : forall n n0 r,
  sideRLs tm h1 (D1 n *> D3 (1+n0) *> r)
                   (D1 (2+n) *> D2 n0 *> r).
Hypothesis H_rh : sideRLs tm h1 0inf (D1 3 *> 0inf).
Hypothesis H_D21 : forall n n0 r,
  sideRLs tm h1 (D2 n *> D1 n0 *> r)
                   (D1 (3+n) *> D3 n0 *> r).
Hypothesis H_D23 : forall n n0 r,
  sideRLs tm h1 (D2 n *> D3 n0 *> r)
                   (D2 (3+n+n0) *> r).
Hypothesis H_D2rh : forall n,
  sideRLs tm h1 (D2 n *> 0inf) (D1 (3+n) *> 0inf).
Hypothesis H_D14 : forall n n0 r,
  sideRLs tm h1 (D1 n *> D4 n0 *> r)
                   (D1 (2+n) *> D1 n0 *> r).
Hypothesis H_D22 : forall n n0 r,
  sideRLs tm h1 (D2 n *> D2 n0 *> r)
                   (D1 (3+n) *> D4 n0 *> r).
Hypothesis H_D24 : forall n n0 r,
  sideRLs tm h1 (D2 n *> D4 n0 *> r)
                   (D1 (4+n+n0) *> r).

Ltac fold_words :=
  try fold D1; try fold D2; try fold D3; try fold D4.

Lemma positive_nat_S n : positive n -> exists k, N.to_nat n=S k.
Proof.
  intros H. destruct (N.to_nat n) as [|k] eqn:E; [|eauto].
  assert (n=0)%N by (apply N2Nat.inj; exact E).
  subst n. unfold positive in H. lia.
Qed.

Lemma D1_positive n : positive n ->
  segRLs tm h1 h1 (D1 (N.to_nat n)) (D1 (N.to_nat n)).
Proof.
  intros H. destruct (positive_nat_S n H) as [k E].
  rewrite E. replace (S k) with (1+k)%nat by lia. apply H_D1.
Qed.

Lemma D1_positive_n n k : positive n ->
  segRLs tm (h1^^k) (h1^^k) (D1 (N.to_nat n)) (D1 (N.to_nat n)).
Proof.
  intros H. induction k; cbn [lpow].
  - constructor.
  - eapply segRLs_trans; [apply D1_positive;exact H|exact IHk].
Qed.

Fixpoint A_prefix (vals:list N) (r:side) : side :=
  match vals with
  | [] => r
  | v::vals' => D1 (N.to_nat v) *> A_prefix vals' r
  end.

Lemma words_side_A_prefix vals xs :
  words_side (List.map P.A vals++xs)=A_prefix vals (words_side xs).
Proof.
  induction vals as [|v vals IH]; cbn [A_prefix].
  - reflexivity.
  - change (D1 (N.to_nat v) *> words_side (List.map P.A vals++xs) =
            D1 (N.to_nat v) *> A_prefix vals (words_side xs)).
    rewrite IH. reflexivity.
Qed.

Lemma A_prefix_app xs ys r :
  A_prefix (xs++ys) r=A_prefix xs (A_prefix ys r).
Proof.
  induction xs as [|x xs IH]; cbn [A_prefix]; [reflexivity|].
  change (D1 (N.to_nat x) *> A_prefix (xs++ys) r =
          D1 (N.to_nat x) *> A_prefix xs (A_prefix ys r)).
  rewrite IH. reflexivity.
Qed.

Lemma A_prefix_rev_cons x xs r :
  A_prefix (rev (x::xs)) r=
  A_prefix (rev xs) (D1 (N.to_nat x) *> r).
Proof. cbn. rewrite A_prefix_app. reflexivity. Qed.

Definition scan_side (s:P.scan) :=
  A_prefix (rev (P.done s)) (words_side (P.rest s)).

Lemma scan_side_words s : words_side (scan_words s)=scan_side s.
Proof. unfold scan_side,scan_words. apply words_side_A_prefix. Qed.

Lemma normalize_side s : scan_side (P.normalize s)=scan_side s.
Proof.
  repeat rewrite <-scan_side_words. rewrite normalize_words. reflexivity.
Qed.

Lemma prefix_D1 vals r r' :
  Forall positive vals -> sideRLs tm h1 r r' ->
  sideRLs tm h1 (A_prefix vals r) (A_prefix vals r').
Proof.
  intros Hv H. induction Hv as [|v vals Hv Hvals IH]; cbn [A_prefix].
  - exact H.
  - eapply segRLs_sideRLs_concat; [apply D1_positive; exact Hv|exact IH].
Qed.

Lemma prefix_D1_n vals k r r' :
  Forall positive vals -> sideRLs tm (h1^^k) r r' ->
  sideRLs tm (h1^^k) (A_prefix vals r) (A_prefix vals r').
Proof.
  intros Hv H. induction Hv as [|v vals Hv Hvals IH]; cbn [A_prefix].
  - exact H.
  - eapply segRLs_sideRLs_concat; [apply D1_positive_n;exact Hv|exact IH].
Qed.

Lemma positive_to_nat_pred n : positive n ->
  (N.to_nat (N.pred n)+1)%nat=N.to_nat n.
Proof.
  intros H. rewrite Nnat.N2Nat.inj_pred.
  destruct (positive_nat_S n H) as [k E]. rewrite E. cbn. lia.
Qed.

Lemma call_sound s s' :
  valid_scan s -> P.call s=Some s' ->
  valid_scan s' /\
  sideRLs tm h1 (scan_side s) (scan_side s').
Proof.
  intros Hvalid Ecall.
  pose proof (normalize_valid s Hvalid) as Hnorm.
  pose proof (normalize_side s) as Enorm.
  unfold P.call in Ecall.
  remember (P.normalize s) as t eqn:Et.
  destruct t as [d r]. cbn [P.done P.rest] in *.
  destruct r as [|w r].
  - inverts Ecall. split; [constructor; [unfold positive; lia|exact Hnorm]|].
    rewrite <-Enorm. unfold scan_side. cbn [P.done P.rest].
    rewrite A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
    apply prefix_D1; [apply Forall_rev; exact Hnorm|exact H_rh].
  - destruct w as [n|n|n|n].
    + discriminate.
    + destruct r as [|w r].
      * inverts Ecall. split; [constructor; [unfold positive; lia|exact Hnorm]|].
        rewrite <-Enorm. unfold scan_side. cbn [P.done P.rest].
        rewrite A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
        apply prefix_D1; [apply Forall_rev; exact Hnorm|].
        rewrite Nnat.N2Nat.inj_add. cbn.
        applys_eq H_D2rh; flia.
      * destruct w as [m|m|m|m].
        -- inverts Ecall. split.
           ++ apply normalize_valid. constructor; [unfold positive; lia|exact Hnorm].
           ++ rewrite <-Enorm,normalize_side. unfold scan_side.
              cbn [P.done P.rest].
              rewrite A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
              apply prefix_D1; [apply Forall_rev; exact Hnorm|].
              rewrite Nnat.N2Nat.inj_add. cbn.
              applys_eq H_D21; flia.
        -- inverts Ecall. split.
           ++ apply normalize_valid. constructor; [unfold positive; lia|exact Hnorm].
           ++ rewrite <-Enorm,normalize_side. unfold scan_side.
              cbn [P.done P.rest].
              rewrite A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
              apply prefix_D1; [apply Forall_rev; exact Hnorm|].
              rewrite Nnat.N2Nat.inj_add. cbn.
              applys_eq H_D22; flia.
        -- inverts Ecall. split.
           ++ apply normalize_valid. exact Hnorm.
           ++ rewrite <-Enorm,normalize_side. unfold scan_side.
              cbn [P.done P.rest A_prefix word_bits words_side]. fold_words.
              apply prefix_D1; [apply Forall_rev; exact Hnorm|].
              repeat rewrite Nnat.N2Nat.inj_add. cbn.
              applys_eq H_D23; flia.
        -- inverts Ecall. split.
           ++ apply normalize_valid. constructor; [unfold positive; lia|exact Hnorm].
           ++ rewrite <-Enorm,normalize_side. unfold scan_side.
              cbn [P.done P.rest].
              rewrite A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
              apply prefix_D1; [apply Forall_rev; exact Hnorm|].
              repeat rewrite Nnat.N2Nat.inj_add. cbn.
              applys_eq H_D24; flia.
    + destruct (N.eqb n 0) eqn:En; [discriminate|].
      destruct d as [|m d]; [discriminate|].
      inverts Ecall. inversion Hnorm as [|? ? Hm Hd]; subst.
      apply N.eqb_neq in En. assert (Hn:positive n) by (apply N.neq_0_lt_0;exact En).
      split.
      * apply normalize_valid. constructor.
        -- unfold positive in *. destruct m; cbn in *; lia.
        -- exact Hd.
      * rewrite <-Enorm,normalize_side. unfold scan_side.
        cbn [P.done P.rest].
        rewrite !A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
        repeat rewrite Nnat.N2Nat.inj_add. cbn.
        apply prefix_D1; [apply Forall_rev; exact Hd|].
        pose proof (positive_to_nat_pred n Hn) as Ep.
        replace (N.to_nat n) with (1+N.to_nat (N.pred n))%nat by lia.
        applys_eq H_D13; flia.
    + destruct d as [|m d]; [discriminate|].
      destruct (N.eqb n 0) eqn:En.
      * apply N.eqb_eq in En. subst n. inverts Ecall.
        inversion Hnorm as [|? ? Hm Hd]; subst. split.
        -- apply normalize_valid. constructor.
           ++ unfold positive in *. destruct m; cbn in *; lia.
           ++ exact Hd.
        -- rewrite <-Enorm,normalize_side. unfold scan_side.
           cbn [P.done P.rest].
           rewrite !A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
           repeat rewrite Nnat.N2Nat.inj_add. cbn.
           apply prefix_D1; [apply Forall_rev;exact Hd|].
           applys_eq H_D14; flia.
      * inverts Ecall. inversion Hnorm as [|? ? Hm Hd]; subst.
        apply N.eqb_neq in En.
        assert (Hn:positive n) by (apply N.neq_0_lt_0;exact En).
        split.
        -- apply normalize_valid. repeat constructor; try exact Hd.
           ++ exact Hn.
           ++ unfold positive in *. destruct m; cbn in *; lia.
        -- rewrite <-Enorm,normalize_side. unfold scan_side.
           cbn [P.done P.rest].
           rewrite !A_prefix_rev_cons. cbn [A_prefix word_bits words_side]. fold_words.
           repeat rewrite Nnat.N2Nat.inj_add. cbn.
           apply prefix_D1; [apply Forall_rev; exact Hd|].
           applys_eq H_D14; flia.
Qed.

Lemma pair_sound d x y r :
  Forall positive d -> positive y ->
  valid_scan (P.Scan (x+5::d) (P.B (N.pred y)::r)) /\
  sideRLs tm (h1^^2)
    (scan_side (P.Scan d (P.B x::P.A y::r)))
    (scan_side (P.Scan (x+5::d) (P.B (N.pred y)::r))).
Proof.
  intros Hd Hy. split.
  - constructor; [unfold positive; destruct x; cbn; lia|exact Hd].
  - unfold scan_side. cbn [P.done P.rest words_side word_bits].
    rewrite A_prefix_rev_cons. fold_words.
    apply prefix_D1_n; [apply Forall_rev;exact Hd|].
    cbn [lpow]. eapply sideRLs_trans.
    + applys_eq H_D21; try (repeat rewrite Nnat.N2Nat.inj_add; cbn; flia).
    + pose proof (positive_to_nat_pred y Hy) as Epred.
      repeat rewrite Nnat.N2Nat.inj_add. cbn.
      replace (N.to_nat y) with (1+N.to_nat (N.pred y))%nat by lia.
      applys_eq H_D13; flia.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma calls_nat_norm_sound fuel d r s' :
  Forall positive d -> P.calls_nat_norm fuel d r=Some s' ->
  valid_scan s' /\
  sideRLs tm (h1^^fuel) (scan_side (P.Scan d r)) (scan_side s').
Proof.
  revert d r s'. induction fuel using lt_wf_ind; intros d r s' Hd E.
  destruct fuel as [|fuel]; cbn in E.
  - inverts E. split; [exact Hd|constructor].
  - destruct fuel as [|fuel].
    + destruct (P.call (P.Scan d r)) as [s1|] eqn:E1; [|discriminate].
      eapply call_sound in E1 as [Hv Hside]; [|exact Hd].
      pose proof (H O ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]. split; [exact Hv'|].
      cbn [lpow]. eapply sideRLs_trans; eassumption.
    + destruct r as [|w r].
      * destruct (P.call (P.Scan d [])) as [s1|] eqn:E1; [|discriminate].
        eapply call_sound in E1 as [Hv Hside]; [|exact Hd].
        pose proof (H (S fuel) ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]. split; [exact Hv'|].
        cbn [lpow]. eapply sideRLs_trans; eassumption.
      * destruct w as [a|a|a|a]; try (
          destruct (P.call (P.Scan d (_ a::r))) as [s1|] eqn:E1;
          [eapply call_sound in E1 as [Hv Hside]; [|exact Hd];
           pose proof (H (S fuel) ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]; split; [exact Hv'|];
           cbn [lpow]; eapply sideRLs_trans; eassumption
          |discriminate]).
        destruct r as [|w r].
        -- destruct (P.call (P.Scan d [P.B a])) as [s1|] eqn:E1; [|discriminate].
           eapply call_sound in E1 as [Hv Hside]; [|exact Hd].
           pose proof (H (S fuel) ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]. split; [exact Hv'|].
           cbn [lpow]. eapply sideRLs_trans; eassumption.
        -- destruct w as [y|y|y|y]; try (
             destruct (P.call (P.Scan d (P.B a::_ y::r))) as [s1|] eqn:E1;
             [eapply call_sound in E1 as [Hv Hside]; [|exact Hd];
              pose proof (H (S fuel) ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]; split; [exact Hv'|];
              cbn [lpow]; eapply sideRLs_trans; eassumption
             |discriminate]).
           destruct (N.eqb y 0) eqn:Ey.
           ++ destruct (P.call (P.Scan d (P.B a::P.A y::r))) as [s1|] eqn:E1;
                [|discriminate].
              eapply call_sound in E1 as [Hv Hside]; [|exact Hd].
              pose proof (H (S fuel) ltac:(lia) _ _ _ Hv E) as [Hv' Hrest]. split; [exact Hv'|].
              cbn [lpow]. eapply sideRLs_trans; eassumption.
           ++ apply N.eqb_neq in Ey.
              assert (Hy:positive y) by (apply N.neq_0_lt_0;exact Ey).
              pose proof (H fuel ltac:(lia) _ _ _
                (proj1 (pair_sound d a y r Hd Hy)) E) as [Hv Hrest].
              split; [exact Hv|]. replace (S (S fuel)) with (2+fuel)%nat by lia.
              rewrite lpow_add.
              eapply sideRLs_trans; [exact (proj2 (pair_sound d a y r Hd Hy))|exact Hrest].
Qed.

Lemma calls_sound n s s' :
  valid_scan s -> P.calls n s=Some s' ->
  valid_scan s' /\
  sideRLs tm (h1^^N.to_nat n) (scan_side s) (scan_side s').
Proof.
  intros Hv E. unfold P.calls in E.
  pose proof (normalize_valid s Hv) as Hvn.
  eapply calls_nat_norm_sound in E as [Hv' Hside]; [|exact Hvn].
  split; [exact Hv'|]. rewrite <-normalize_side. exact Hside.
Qed.

Lemma N_sub_add_small n k : (N.of_nat k<=n)%N ->
  (N.to_nat (n-N.of_nat k)+k)%nat=N.to_nat n.
Proof.
  intros H. pose proof (N.sub_add (N.of_nat k) n H) as E.
  apply (f_equal N.to_nat) in E.
  rewrite Nnat.N2Nat.inj_add,Nnat.Nat2N.id in E. exact E.
Qed.

Lemma service_sound e edge x y edge' :
  P.service e edge=Some (x,y,edge') ->
  exists z tail,
    positive z /\
    sideRLs tm h1 (words_side edge)
      (D1 (N.to_nat z) *> words_side tail) /\
    sideRLs tm (h1^^(N.to_nat e+7))
      (D2 (N.to_nat (N.pred z)) *> words_side tail)
      (D1 (N.to_nat x+4) *> D1 (N.to_nat y+2) *> words_side edge').
Proof.
  unfold P.service. intros E.
  destruct (P.call (P.Scan [] edge)) as [s1|] eqn:E1; [|discriminate].
  destruct (P.scan_list s1) as [|w tail] eqn:Es1; [discriminate|].
  destruct w as [z|z|z|z]; try discriminate.
  destruct (N.eqb z 0) eqn:Ez; [discriminate|].
  destruct (P.calls (e+7) (P.Scan [] (P.B (N.pred z)::tail)))
    as [s2|] eqn:E2; [|discriminate].
  destruct (P.scan_list s2) as [|w1 r1] eqn:Es2; [discriminate|].
  destruct w1 as [u|u|u|u]; try discriminate.
  destruct r1 as [|w2 r2]; [discriminate|].
  destruct w2 as [v|v|v|v]; try discriminate.
  destruct ((4<=?u)%N && (2<=?v)%N)%bool eqn:Eguard; [|discriminate].
  inverts E. exists z,tail.
  apply andb_true_iff in Eguard as [Hu Hv].
  apply N.leb_le in Hu,Hv. apply N.eqb_neq in Ez.
  assert (Hz:positive z) by (apply N.neq_0_lt_0;exact Ez).
  split; [exact Hz|]. split.
  - pose proof (call_sound (P.Scan [] edge) s1 (Forall_nil _) E1) as [_ H].
    repeat rewrite <-scan_side_words in H.
    assert (Es1':scan_words s1=P.A z::tail) by (rewrite scan_words_eq;exact Es1).
    rewrite Es1' in H. cbn [scan_words P.done P.rest words_side word_bits] in H.
    exact H.
  - pose proof (calls_sound (e+7) (P.Scan [] (P.B (N.pred z)::tail)) s2
      (Forall_nil _) E2) as [_ H].
    repeat rewrite <-scan_side_words in H.
    assert (Es2':scan_words s2=P.A u::P.A v::edge') by (rewrite scan_words_eq;exact Es2).
    rewrite Es2' in H. cbn [scan_words P.done P.rest words_side word_bits] in H.
    fold_words.
    repeat rewrite Nnat.N2Nat.inj_add in H. cbn in H.
    pose proof (N_sub_add_small u 4 Hu) as Eu.
    pose proof (N_sub_add_small v 2 Hv) as Ev.
    applys_eq H; flia.
Qed.

Lemma D2_D1_pair n p r :
  p<>O -> sideRLs tm (h1^^2)
    (D2 n *> D1 p *> r)
    (D1 (n+5) *> D2 (p-1) *> r).
Proof.
  intros Hp. destruct p as [|p]; [contradiction|].
  cbn [lpow]. eapply sideRLs_trans.
  - apply H_D21.
  - replace (S p) with (1+p)%nat by lia.
    applys_eq H_D13; flia.
  rewrite app_nil_r. reflexivity.
Qed.

Fixpoint layer_ext (extra:nat) (qs:list N) (tail:side) : side :=
  match qs with
  | [] => tail
  | e::qs' => D1 (N.to_nat e+2*(S (length qs')+extra)) *>
              layer_ext extra qs' tail
  end.

Lemma layer_ext_snoc qs x y tail :
  layer (qs++[x;y]) tail=
  layer_ext 2 qs (D1 (N.to_nat x+4) *> D1 (N.to_nat y+2) *> tail).
Proof.
  induction qs as [|q qs IH]; cbn [layer layer_ext].
  - reflexivity.
  - change (D1 (N.to_nat q+2*S (length (qs++[x;y]))) *>
            layer (qs++[x;y]) tail =
            D1 (N.to_nat q+2*(S (length qs)+2)) *>
            layer_ext 2 qs
              (D1 (N.to_nat x+4) *> D1 (N.to_nat y+2) *> tail)).
    rewrite IH. f_equal. f_equal. rewrite length_app. cbn. lia.
Qed.

Lemma cross_layer qs q z tail : positive z ->
  sideRLs tm (h1^^(2*S (length qs)))
    (D2 (N.to_nat q+2*S (length qs)-1) *>
       layer qs (D1 (N.to_nat z) *> tail))
    (layer_ext 2 (q::qs)
       (D2 (N.to_nat (N.pred z)) *> tail)).
Proof.
  revert q. induction qs as [|a qs IH]; intros q Hz; cbn [layer layer_ext].
  - replace (N.to_nat q+2*1-1)%nat with (N.to_nat q+1)%nat by lia.
    pose proof (positive_to_nat_pred z Hz) as Ez.
    replace (N.to_nat z) with (1+N.to_nat (N.pred z))%nat by lia.
    applys_eq D2_D1_pair; flia.
  - match goal with
    | |- sideRLs _ _ ?r1 ?r2 =>
        change (sideRLs tm (h1^^(2*S (S (length qs)))) r1 r2)
    end.
    replace (2*S (S (length qs)))%nat with (2+2*S (length qs))%nat by lia.
    rewrite lpow_add.
    eapply @sideRLs_trans with
      (r2:=D1 (N.to_nat q+2*S (S (length qs))-1+5) *>
            D2 (N.to_nat a+2*S (length qs)-1) *>
            layer qs (D1 (N.to_nat z) *> tail)).
    + apply D2_D1_pair. lia.
    + pose proof (prefix_D1_n
        [N.of_nat (N.to_nat q+2*S (S (length qs))-1+5)]
        (2*S (length qs)) _ _
        ltac:(constructor;
          [unfold positive; apply N.neq_0_lt_0; intro E0;
           apply (f_equal N.to_nat) in E0;
           rewrite Nnat.Nat2N.id in E0; cbn in E0; lia
          |constructor])
        (IH a Hz)) as HP.
      cbn [A_prefix] in HP.
      rewrite Nnat.Nat2N.id in HP.
      replace (N.to_nat q+2*(S (length (a::qs))+2))%nat with
        (N.to_nat q+2*S (S (length qs))-1+5)%nat by (cbn;lia).
      exact HP.
Qed.

Section Dynamics.
Variable Sconf:nat->side->Q*tape.
Hypothesis H_Inc : forall n r r', sideRLs tm h1 r r' ->
  progress tm (Sconf (S n) r) (Sconf n r').
Hypothesis H_Ov : forall n n0 r r',
  sideRLs tm h1 r (D1 n *> D1 (1+n0) *> r') ->
  progress tm (Sconf O r) (Sconf (5+n) (D2 n0 *> r')).

Lemma Inc_many k n r r' : sideRLs tm (h1^^k) r r' ->
  evstep tm (Sconf (k+n) r) (Sconf n r').
Proof.
  revert n r r'. induction k as [|k IH]; intros n r r' Hs.
  - cbn [lpow] in Hs. inverts Hs. constructor.
  - cbn [lpow] in Hs. apply sideRLs_split in Hs as [m [Hone Hrest]].
    eapply evstep_trans.
    + apply progress_evstep,H_Inc,Hone.
    + apply IH,Hrest.
Qed.

Lemma D1_nat_n p k : p<>O ->
  segRLs tm (h1^^k) (h1^^k) (D1 p) (D1 p).
Proof.
  intros Hp. destruct p as [|p]; [contradiction|].
  induction k; cbn [lpow]; [constructor|].
  eapply segRLs_trans; [apply H_D1|exact IHk].
Qed.

Lemma layer_ext_side_n extra qs k r r' :
  sideRLs tm (h1^^k) r r' ->
  sideRLs tm (h1^^k) (layer_ext extra qs r) (layer_ext extra qs r').
Proof.
  intros H. induction qs as [|q qs IH]; cbn [layer_ext]; [exact H|].
  eapply segRLs_sideRLs_concat; [apply D1_nat_n;lia|exact IH].
Qed.

Lemma layer_side qs r r' : sideRLs tm h1 r r' ->
  sideRLs tm h1 (layer qs r) (layer qs r').
Proof.
  intros H. induction qs as [|q qs IH]; cbn [layer]; [exact H|].
  eapply segRLs_sideRLs_concat; [|exact IH].
  replace (N.to_nat q+2*S (length qs))%nat with
    (1+(N.to_nat q+2*S (length qs)-1))%nat by lia.
  apply H_D1.
Qed.

Lemma reset_list_sound e q qs edge x y edge' :
  P.service e edge=Some (x,y,edge') ->
  progress tm
    (Sconf O (layer (e::q::qs) (words_side edge)))
    (Sconf O (layer ((q::qs)++[x;y]) (words_side edge'))).
Proof.
  intros Eservice.
  destruct (service_sound e edge x y edge' Eservice)
    as [z [tail [Hz [Hedge Hservice]]]].
  pose proof (layer_side (e::q::qs) _ _ Hedge) as Hfirst.
  cbn [layer] in Hfirst.
  replace (N.to_nat q+2*S (length qs))%nat with
    (1+(N.to_nat q+2*S (length qs)-1))%nat in Hfirst by lia.
  apply H_Ov in Hfirst.
  cbn [layer].
  replace (N.to_nat q+2*S (length qs))%nat with
    (1+(N.to_nat q+2*S (length qs)-1))%nat by lia.
  eapply progress_evstep_trans; [exact Hfirst|].
  pose proof (cross_layer qs q z (words_side tail) Hz) as Hcross.
  pose proof (layer_ext_side_n 2 (q::qs) (N.to_nat e+7) _ _ Hservice)
    as Hlocal.
  pose proof (sideRLs_trans Hcross Hlocal) as Hall.
  rewrite <-lpow_add in Hall.
  apply Inc_many with (n:=O) in Hall.
  rewrite <- (layer_ext_snoc (q::qs) x y (words_side edge')) in Hall.
  replace (2*S (length qs)+(N.to_nat e+7)+O)%nat with
    (5+(N.to_nat e+2*S (length (q::qs))))%nat in Hall by (cbn;lia).
  exact Hall.
Qed.

Lemma prefix_D1_halt vals r :
  Forall positive vals -> sideRLs_halt tm h1 r ->
  sideRLs_halt tm h1 (A_prefix vals r).
Proof.
  intros Hv Hhalt. induction Hv as [|v vals Hv Hvals IH]; cbn [A_prefix].
  - exact Hhalt.
  - eapply segRLs_sideRLs_halt_concat; [apply D1_positive;exact Hv|exact IH].
Qed.

Lemma layer_halt qs r : sideRLs_halt tm h1 r ->
  sideRLs_halt tm h1 (layer qs r).
Proof.
  intros Hhalt. induction qs as [|q qs IH]; cbn [layer]; [exact Hhalt|].
  eapply segRLs_sideRLs_halt_concat; [|exact IH].
  replace (N.to_nat q+2*S (length qs))%nat with
    (1+(N.to_nat q+2*S (length qs)-1))%nat by lia.
  apply H_D1.
Qed.

Lemma all_A3_shape r : P.all_A3 r=true ->
  r=repeat (P.A 3%N) (length r).
Proof.
  induction r as [|w r IH]; cbn [P.all_A3]; intros E; [reflexivity|].
  destruct w as [n|n|n|n]; try discriminate.
  destruct n as [|p]; try discriminate.
  destruct p; try discriminate.
  destruct p; try discriminate.
  cbn in E. cbn. f_equal. apply IH,E.
Qed.

Lemma words_side_A3 k :
  words_side (repeat (P.A 3%N) k)=(D1 3)^^k *> 0inf.
Proof.
  induction k; cbn [repeat words_side word_bits lpow]; [reflexivity|].
  rewrite IHk. reflexivity.
Qed.

Lemma halt_edge_sound run edge :
  sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf) ->
  P.halt_edgeb run (P.rest (P.normalize (P.Scan [] edge)))=true ->
  sideRLs_halt tm h1 (words_side edge).
Proof.
  intros Hterminal Ehalt.
  remember (P.normalize (P.Scan [] edge)) as s eqn:Es.
  destruct s as [d r]. unfold P.halt_edgeb in Ehalt. cbn [P.rest] in Ehalt.
  destruct r as [|w r]; [discriminate|].
  destruct w as [n|n|n|n]; try discriminate.
  destruct n as [|p]; [|discriminate].
  apply andb_true_iff in Ehalt as [Elen Eall].
  apply Nat.eqb_eq in Elen.
  pose proof (all_A3_shape r Eall) as Er.
  assert (Hnorm:sideRLs_halt tm h1 (scan_side (P.normalize (P.Scan [] edge)))).
  { rewrite <-Es. unfold scan_side. cbn [P.done P.rest words_side word_bits].
    rewrite Er,Elen,words_side_A3.
    apply prefix_D1_halt; [|exact Hterminal].
    apply Forall_rev.
    pose proof (normalize_valid (P.Scan [] edge) (Forall_nil _)) as Hd.
    rewrite <-Es in Hd. exact Hd. }
  rewrite normalize_side in Hnorm.
  unfold scan_side in Hnorm. cbn [P.done P.rest A_prefix] in Hnorm.
  exact Hnorm.
Qed.

Lemma halt_edgeb_normalize run r : P.halt_edgeb run r=true ->
  P.rest (P.normalize (P.Scan [] r))=r.
Proof.
  unfold P.halt_edgeb. destruct r as [|w r]; [discriminate|].
  destruct w as [n|n|n|n]; try discriminate.
  destruct n as [|p]; [reflexivity|discriminate].
Qed.

Lemma scan_halt_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) s :
  valid_scan s ->
  P.halt_edgeb run (P.rest (P.normalize s))=true ->
  sideRLs_halt tm h1 (scan_side s).
Proof.
  intros Hv Ehalt. rewrite <-normalize_side.
  unfold scan_side. apply prefix_D1_halt.
  - apply Forall_rev,normalize_valid,Hv.
  - eapply halt_edge_sound; [exact Hterminal|].
    rewrite (halt_edgeb_normalize run _ Ehalt). exact Ehalt.
Qed.

Lemma calls_haltb_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf))
  fuel s : valid_scan s -> P.calls_haltb run fuel s=true ->
  sideRLs_halt tm (h1^^fuel) (scan_side s).
Proof.
  revert s. induction fuel as [|fuel IH]; intros s Hv E; [discriminate|].
  cbn [P.calls_haltb] in E.
  destruct (P.call (P.normalize s)) as [s'|] eqn:Ecall.
  - pose proof (call_sound (P.normalize s) s'
      (normalize_valid s Hv) Ecall) as [_ Hone].
    pose proof (IH s' (proj1 (call_sound (P.normalize s) s'
      (normalize_valid s Hv) Ecall)) E) as Hrest.
    cbn [lpow]. eapply sideRLs_halt_app_right; [|exact Hrest].
    rewrite normalize_side in Hone. exact Hone.
  - cbn [lpow]. apply sideRLs_halt_app_left with (hs2:=h1^^fuel).
    apply (scan_halt_sound run Hterminal); assumption.
Qed.

Lemma service_haltb_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) e edge :
  P.service_haltb run e edge=true ->
  sideRLs_halt tm h1 (words_side edge) \/
  exists z tail, positive z /\
    sideRLs tm h1 (words_side edge)
      (D1 (N.to_nat z) *> words_side tail) /\
    sideRLs_halt tm (h1^^(N.to_nat e+7))
      (D2 (N.to_nat (N.pred z)) *> words_side tail).
Proof.
  unfold P.service_haltb. intros E.
  destruct (P.call (P.Scan [] edge)) as [s1|] eqn:E1.
  - destruct (P.scan_list s1) as [|w tail] eqn:Es1; [discriminate|].
    destruct w as [z|z|z|z]; try discriminate.
    destruct (N.eqb z 0) eqn:Ez; [discriminate|]. right.
    apply N.eqb_neq in Ez.
    assert (Hz:positive z) by (apply N.neq_0_lt_0;exact Ez).
    exists z,tail. split; [exact Hz|]. split.
    + pose proof (call_sound (P.Scan [] edge) s1 (Forall_nil _) E1) as [_ H].
      repeat rewrite <-scan_side_words in H.
      assert (Es1':scan_words s1=P.A z::tail) by
        (rewrite scan_words_eq;exact Es1).
      rewrite Es1' in H.
      cbn [scan_words P.done P.rest words_side word_bits] in H. exact H.
    + apply (calls_haltb_sound run Hterminal) in E;
        [|constructor].
      cbn [scan_side P.done P.rest A_prefix words_side word_bits] in E.
      rewrite Nnat.N2Nat.inj_add in E. cbn in E.
      exact E.
  - left. apply halt_edge_sound with (run:=run); assumption.
Qed.

Definition valid_machine (m:P.machine) :=
  (2<=length (P.contents (P.queue m)))%nat.

Lemma valid_init109 : valid_machine P.init109.
Proof.
  cbv [valid_machine P.init109 P.of_list P.contents P.queue].
  repeat constructor.
Qed.

Lemma valid_init109b : valid_machine P.init109b.
Proof.
  cbv [valid_machine P.init109b P.of_list P.contents P.queue].
  repeat constructor.
Qed.

Lemma valid_start109 : valid_machine P.start109.
Proof.
  cbv [valid_machine P.start109 P.of_list P.contents P.queue].
  repeat constructor.
Qed.

Variable c0:Q*tape.
Hypothesis H_halt_side : forall n r,
  sideRLs_halt tm h1 r -> halts tm (Sconf n r).

Lemma layer_ext_halt_n extra qs k r :
  sideRLs_halt tm (h1^^k) r ->
  sideRLs_halt tm (h1^^k) (layer_ext extra qs r).
Proof.
  intros Hhalt. induction qs as [|q qs IH]; cbn [layer_ext]; [exact Hhalt|].
  eapply segRLs_sideRLs_halt_concat; [|exact IH].
  apply D1_nat_n. lia.
Qed.

Lemma Inc_many_halt k n r :
  sideRLs_halt tm (h1^^k) r -> halts tm (Sconf (k+n) r).
Proof.
  revert n r. induction k as [|k IH]; intros n r Hhalt.
  - cbn [lpow] in Hhalt. inverts Hhalt.
  - cbn [lpow] in Hhalt. apply sideRLs_halt_split in Hhalt.
    destruct Hhalt as [Hnow|[r' [Hone Hrest]]].
    + apply H_halt_side,Hnow.
    + replace (S k+n)%nat with (S (k+n)) by lia.
      eapply halts_evstep; [apply IH,Hrest|].
      apply progress_evstep,H_Inc,Hone.
Qed.

Lemma reset_list_halt run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf))
  e q qs edge : P.service_haltb run e edge=true ->
  halts tm (Sconf O (layer (e::q::qs) (words_side edge))).
Proof.
  intros Ehalt.
  destruct (service_haltb_sound run Hterminal e edge Ehalt) as
    [Hedgehalt|[z [tail [Hz [Hedge Hcalls]]]]].
  - apply H_halt_side,layer_halt,Hedgehalt.
  - pose proof (layer_side (e::q::qs) _ _ Hedge) as Hfirst.
    cbn [layer] in Hfirst.
    replace (N.to_nat q+2*S (length qs))%nat with
      (1+(N.to_nat q+2*S (length qs)-1))%nat in Hfirst by lia.
    apply H_Ov in Hfirst.
    cbn [layer].
    replace (N.to_nat q+2*S (length qs))%nat with
      (1+(N.to_nat q+2*S (length qs)-1))%nat by lia.
    eapply halts_evstep; [|apply progress_evstep,Hfirst].
    pose proof (cross_layer qs q z (words_side tail) Hz) as Hcross.
    pose proof (layer_ext_halt_n 2 (q::qs) (N.to_nat e+7) _ Hcalls)
      as Hlocal.
    pose proof (sideRLs_halt_app_right tm _ _ _ _ Hcross Hlocal) as Hall.
    rewrite <-lpow_add in Hall.
    pose proof (Inc_many_halt _ O _ Hall) as Hfinal.
    replace (2*S (length qs)+(N.to_nat e+7)+O)%nat with
      (5+(N.to_nat e+2*S (length (q::qs))))%nat in Hfinal by (cbn;lia).
    exact Hfinal.
Qed.

Definition machine_prop (m:P.machine) :=
  valid_machine m /\ evstep tm c0 (Sconf O (denote_machine m)).

Definition result_prop (r:P.result) :=
  match r with P.Halt => halts tm c0 | P.Failed => True end.

Lemma step_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) m :
  machine_prop m ->
  match P.step run m with
  | inl m' => machine_prop m'
  | inr r => result_prop r
  end.
Proof.
  intros [Hvalid Hreach].
  unfold P.step.
  destruct (P.uncons (P.queue m)) as [[e q']|] eqn:Epop.
  2:{ exact I. }
  pose proof (uncons_contents (P.queue m)) as Econtents.
  rewrite Epop in Econtents.
  destruct (P.contents q') as [|q qs] eqn:Eqs.
  { unfold valid_machine in Hvalid. rewrite Econtents in Hvalid. cbn in Hvalid. lia. }
  destruct (P.service e (P.edge m)) as [[[x y] edge']|] eqn:Eservice.
  - split.
    + unfold valid_machine. cbn [P.queue].
      rewrite !snoc_contents,Eqs,!length_app. cbn. lia.
    + eapply evstep_trans; [exact Hreach|].
      apply progress_evstep.
      unfold denote_machine. cbn [P.queue P.edge].
      rewrite !snoc_contents,Eqs,Econtents.
      rewrite <-app_assoc. cbn.
      apply reset_list_sound,Eservice.
  - destruct (P.service_haltb run e (P.edge m)) eqn:Ehalt.
    + unfold result_prop.
      eapply halts_evstep; [|exact Hreach].
      unfold denote_machine. rewrite Econtents.
      apply (reset_list_halt run Hterminal),Ehalt.
    + exact I.
Qed.

Lemma continue_steps_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) fuel s :
  match s with inl m => machine_prop m | inr r => result_prop r end ->
  match P.continue_steps run fuel s with
  | inl m => machine_prop m
  | inr r => result_prop r
  end.
Proof.
  revert s. induction fuel as [|fuel IH].
  - intros [m|r] H; exact H.
  - intros [m|r] H.
    + cbn [P.continue_steps].
    remember (P.step run m) as t eqn:Et.
    pose proof (step_sound run Hterminal m H) as Hstep.
    rewrite <-Et in Hstep. destruct t as [m'|r'].
      * apply IH,Hstep.
      * destruct fuel; exact Hstep.
    + exact H.
Qed.

Lemma step8_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) m :
  machine_prop m ->
  match P.step8 run m with
  | inl m' => machine_prop m'
  | inr r => result_prop r
  end.
Proof.
  intros H. unfold P.step8.
  pose proof (step_sound run Hterminal m H) as Hstep.
  destruct (P.step run m); apply (continue_steps_sound run Hterminal);
    exact Hstep.
Qed.

Lemma run8_sound run
  (Hterminal:sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf)) bound init :
  machine_prop init ->
  match P.run8 run bound init with
  | inl m => machine_prop m
  | inr r => result_prop r
  end.
Proof.
  intros Hinit. unfold P.run8.
  eapply N_iter_until_spec with (P:=machine_prop) (P':=result_prop).
  - apply step8_sound,Hterminal.
  - exact Hinit.
Qed.

Lemma stopped_run8_halts run bound init :
  sideRLs_halt tm h1 (D1 0 *> (D1 3)^^run *> 0inf) ->
  machine_prop init -> P.stoppedb (P.run8 run bound init)=true ->
  halts tm c0.
Proof.
  intros Hterminal Hinit E.
  pose proof (run8_sound run Hterminal bound init Hinit) as Hsound.
  destruct (P.run8 run bound init) as [m|[|]]; cbn [P.stoppedb result_prop] in *;
    try discriminate; exact Hsound.
Qed.

End Dynamics.

End Rules.

End Loop4MonoProof.


Close Scope N_scope.

From Coq Require Import String.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1RA1LA_1LE1RD_0RE0RC_0RB0LF_0LB---").

Definition h1: list (DH0*DH0) :=
  [((D,<[0;1;0;1]),(B,[]))].

Definition D1 n := [0;0;1] ++ [1;1]^^n.
Definition D2 n := [0;0;1;1] ++ [1;1]^^n.
Definition D3 n := [0;1] ++ [1;1]^^n.
Definition D4 n := [0;1;1] ++ [1;1]^^n.

Lemma D1_Inc n:
  segRLs tm h1 h1 (D1 (1+n)) (D1 (1+n)).
Proof. esx. Qed.

Lemma D13_Inc n n0 r:
  sideRLs tm h1 (D1 n *> D3 (1+n0) *> r)
                  (D1 (2+n) *> D2 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma rh_Inc: sideRLs tm h1 0inf (D1 3 *> 0inf).
Proof. esx. Qed.

Lemma D21_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D1 n0 *> r)
                  (D1 (3+n) *> D3 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D23_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D3 n0 *> r)
                  (D2 (3+n+n0) *> r).
Proof. es' n n0 & r. Qed.

Lemma D2_rh_Inc n:
  sideRLs tm h1 (D2 n *> 0inf) (D1 (3+n) *> 0inf).
Proof. es' n. Qed.

(* These are the three missing one-h1 clauses needed by the exact
   D1--D4 forward simulator. *)
Lemma D14_Inc n n0 r:
  sideRLs tm h1 (D1 n *> D4 n0 *> r)
                  (D1 (2+n) *> D1 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D22_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D2 n0 *> r)
                  (D1 (3+n) *> D4 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D24_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D4 n0 *> r)
                  (D1 (4+n+n0) *> r).
Proof. es' n n0 & r. Qed.

(* The first low-parameter case reached by the strict FIFO model.  It is not
   another returning rule: with the actual A3 buffer it halts locally. *)
Lemma D1_0_A3_halt:
  sideRLs_halt tm h1 (D1 0 *> (D1 3)^^10 *> 0inf).
Proof.
  eapply sideRLs_halt_here.
  esx.
Qed.

Definition S' '(n,r) :=
  0inf <* <[0;1]^^n {{{ (D,<[0;1;0;1],R) }}} r.

Lemma Inc n r r':
  sideRLs tm h1 r r' ->
  progress tm (S' (1+n,r)) (S' (n,r')).
Proof.
  unfold S'. intros H. eapply sideRLs_1 in H. follow10 H. es' n & r'.
Qed.

Lemma Ov n n0 r r':
  sideRLs tm h1 r (D1 n *> D1 (1+n0) *> r') ->
  progress tm (S' (O,r)) (S' (5+n,D2 n0 *> r')).
Proof.
  unfold S'. intros H. eapply sideRLs_1 in H. follow10 H. es' n n0 & r'.
Qed.

Lemma init:
  c0 -[tm]->* S' (O,D1 5 *> (D1 3)^^7 *> 0inf).
Proof. esx. Qed.


Module P := Loop4MonoFast.
Module G := Loop4MonoProof.

Lemma R_D1 n:
  segRLs tm h1 h1 (G.D1 (1+n)) (G.D1 (1+n)).
Proof. exact (D1_Inc n). Qed.

Lemma R_D13 n n0 r:
  sideRLs tm h1 (G.D1 n *> G.D3 (1+n0) *> r)
    (G.D1 (2+n) *> G.D2 n0 *> r).
Proof. exact (D13_Inc n n0 r). Qed.

Lemma R_rh: sideRLs tm h1 0inf (G.D1 3 *> 0inf).
Proof. exact rh_Inc. Qed.

Lemma R_D21 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D1 n0 *> r)
    (G.D1 (3+n) *> G.D3 n0 *> r).
Proof. exact (D21_Inc n n0 r). Qed.

Lemma R_D23 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D3 n0 *> r)
    (G.D2 (3+n+n0) *> r).
Proof. exact (D23_Inc n n0 r). Qed.

Lemma R_D2rh n:
  sideRLs tm h1 (G.D2 n *> 0inf) (G.D1 (3+n) *> 0inf).
Proof. exact (D2_rh_Inc n). Qed.

Lemma R_D14 n n0 r:
  sideRLs tm h1 (G.D1 n *> G.D4 n0 *> r)
    (G.D1 (2+n) *> G.D1 n0 *> r).
Proof. exact (D14_Inc n n0 r). Qed.

Lemma R_D22 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D2 n0 *> r)
    (G.D1 (3+n) *> G.D4 n0 *> r).
Proof. exact (D22_Inc n n0 r). Qed.

Lemma R_D24 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D4 n0 *> r)
    (G.D1 (4+n+n0) *> r).
Proof. exact (D24_Inc n n0 r). Qed.

Definition Sconf n r := S' (n,r).

Lemma R_Inc n r r': sideRLs tm h1 r r' ->
  progress tm (Sconf (S n) r) (Sconf n r').
Proof. apply Inc. Qed.

Lemma R_Ov n n0 r r':
  sideRLs tm h1 r (G.D1 n *> G.D1 (1+n0) *> r') ->
  progress tm (Sconf O r) (Sconf (5+n) (G.D2 n0 *> r')).
Proof. apply Ov. Qed.

Lemma R_halt_side n r : sideRLs_halt tm h1 r ->
  halts tm (Sconf n r).
Proof.
  intros H. unfold Sconf,S'.
  eapply sideRLs_halt_single in H. exact H.
Qed.

Lemma denote_init :
  G.denote_machine P.start109 = G.D1 5 *> (G.D1 3)^^7 *> 0inf.
Proof.
  cbv [G.denote_machine P.start109 P.of_list P.contents
       P.queue P.edge G.layer G.words_side G.word_bits]. reflexivity.
Qed.

Lemma init_fast : c0 -[tm]->* Sconf O (G.denote_machine P.start109).
Proof.
  rewrite denote_init. exact init.
Qed.

Lemma start_prop : G.machine_prop tm Sconf c0 P.start109.
Proof. split; [apply G.valid_start109|exact init_fast]. Qed.

Definition init109_raw :=
  P.Machine (P.DSeq [1%N] [5%N;3%N])
    [P.A 7;P.A 7;P.B 2;P.A 3;P.A 3].

Lemma first_step : P.step 10 P.start109=inl init109_raw.
Proof. vm_compute. reflexivity. Qed.

Lemma raw_to_init : G.machine_prop tm Sconf c0 init109_raw ->
  G.machine_prop tm Sconf c0 P.init109.
Proof.
  intros [_ Hreach]. split; [apply G.valid_init109|].
  cbv [init109_raw G.denote_machine P.init109 P.contents P.queue P.edge
       G.layer G.words_side G.word_bits P.of_list] in Hreach |-.
  exact Hreach.
Qed.

Lemma init_prop : G.machine_prop tm Sconf c0 P.init109.
Proof.
  pose proof (G.step_sound tm h1
    R_D1 R_D13 R_rh R_D21 R_D23 R_D2rh R_D14 R_D22 R_D24
    Sconf R_Inc R_Ov c0 R_halt_side 10%nat D1_0_A3_halt
    P.start109 start_prop) as H.
  rewrite first_step in H. apply raw_to_init,H.
Qed.

Lemma certificate : P.stoppedb (P.run8 10 18000 P.init109)=true.
Proof. native_check_eq. Qed.

Theorem halt: halts tm c0.
Proof.
  eapply G.stopped_run8_halts with
    (tm:=tm) (h1:=h1) (Sconf:=Sconf) (c0:=c0)
    (run:=10%nat) (bound:=18000%N) (init:=P.init109).
  all: first
    [ exact R_D1 | exact R_D13 | exact R_rh | exact R_D21 | exact R_D23
    | exact R_D2rh | exact R_D14 | exact R_D22 | exact R_D24
    | exact R_Inc | exact R_Ov | exact R_halt_side
    | exact D1_0_A3_halt | exact init_prop | exact certificate ].
Qed.

End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LF_1RD1LD_1LC1LA_0RB0RA_0LC---").

Definition h1: list (DH0*DH0) :=
  [((E,<[0;1;0;1]),(C,[]))].

Definition D1 n := [0;0;1] ++ [1;1]^^n.
Definition D2 n := [0;0;1;1] ++ [1;1]^^n.
Definition D3 n := [0;1] ++ [1;1]^^n.
Definition D4 n := [0;1;1] ++ [1;1]^^n.

Lemma D1_Inc n:
  segRLs tm h1 h1 (D1 (1+n)) (D1 (1+n)).
Proof. esx. Qed.

Lemma D13_Inc n n0 r:
  sideRLs tm h1 (D1 n *> D3 (1+n0) *> r)
                  (D1 (2+n) *> D2 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma rh_Inc: sideRLs tm h1 0inf (D1 3 *> 0inf).
Proof. esx. Qed.

Lemma D21_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D1 n0 *> r)
                  (D1 (3+n) *> D3 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D23_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D3 n0 *> r)
                  (D2 (3+n+n0) *> r).
Proof. es' n n0 & r. Qed.

Lemma D2_rh_Inc n:
  sideRLs tm h1 (D2 n *> 0inf) (D1 (3+n) *> 0inf).
Proof. es' n. Qed.

(* Direct checks that the three clauses added for test_109 are unchanged
   under the state renaming A->D, B->C, C->A, D->E, E->B, F->F. *)
Lemma D14_Inc n n0 r:
  sideRLs tm h1 (D1 n *> D4 n0 *> r)
                  (D1 (2+n) *> D1 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D22_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D2 n0 *> r)
                  (D1 (3+n) *> D4 n0 *> r).
Proof. es' n n0 & r. Qed.

Lemma D24_Inc n n0 r:
  sideRLs tm h1 (D2 n *> D4 n0 *> r)
                  (D1 (4+n+n0) *> r).
Proof. es' n n0 & r. Qed.

Lemma D1_0_A3_halt:
  sideRLs_halt tm h1 (D1 0 *> (D1 3)^^27 *> 0inf).
Proof.
  eapply sideRLs_halt_here.
  esx.
Qed.

Definition S' '(n,r) :=
  0inf <* <[0;1]^^n {{{ (E,<[0;1;0;1],R) }}} r.

Lemma Inc n r r':
  sideRLs tm h1 r r' ->
  progress tm (S' (1+n,r)) (S' (n,r')).
Proof.
  unfold S'. intros H. eapply sideRLs_1 in H. follow10 H. es' n & r'.
Qed.

Lemma Ov n n0 r r':
  sideRLs tm h1 r (D1 n *> D1 (1+n0) *> r') ->
  progress tm (S' (O,r)) (S' (5+n,D2 n0 *> r')).
Proof.
  unfold S'. intros H. eapply sideRLs_1 in H. follow10 H. es' n n0 & r'.
Qed.

Lemma init:
  c0 -[tm]->* S' (O,(D1 3)^^7 *> 0inf).
Proof. esx. Qed.


Lemma bridge109b:
  S' (O,(D1 3)^^7 *> 0inf) -[tm]->*
  S' (O,(D1 7)^^4 *> D2 2 *> (D1 3)^^2 *> 0inf).
Proof. esx. Qed.

Module P := Loop4MonoFast.
Module G := Loop4MonoProof.

Lemma R_D1 n:
  segRLs tm h1 h1 (G.D1 (1+n)) (G.D1 (1+n)).
Proof. exact (D1_Inc n). Qed.

Lemma R_D13 n n0 r:
  sideRLs tm h1 (G.D1 n *> G.D3 (1+n0) *> r)
    (G.D1 (2+n) *> G.D2 n0 *> r).
Proof. exact (D13_Inc n n0 r). Qed.

Lemma R_rh: sideRLs tm h1 0inf (G.D1 3 *> 0inf).
Proof. exact rh_Inc. Qed.

Lemma R_D21 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D1 n0 *> r)
    (G.D1 (3+n) *> G.D3 n0 *> r).
Proof. exact (D21_Inc n n0 r). Qed.

Lemma R_D23 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D3 n0 *> r)
    (G.D2 (3+n+n0) *> r).
Proof. exact (D23_Inc n n0 r). Qed.

Lemma R_D2rh n:
  sideRLs tm h1 (G.D2 n *> 0inf) (G.D1 (3+n) *> 0inf).
Proof. exact (D2_rh_Inc n). Qed.

Lemma R_D14 n n0 r:
  sideRLs tm h1 (G.D1 n *> G.D4 n0 *> r)
    (G.D1 (2+n) *> G.D1 n0 *> r).
Proof. exact (D14_Inc n n0 r). Qed.

Lemma R_D22 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D2 n0 *> r)
    (G.D1 (3+n) *> G.D4 n0 *> r).
Proof. exact (D22_Inc n n0 r). Qed.

Lemma R_D24 n n0 r:
  sideRLs tm h1 (G.D2 n *> G.D4 n0 *> r)
    (G.D1 (4+n+n0) *> r).
Proof. exact (D24_Inc n n0 r). Qed.

Definition Sconf n r := S' (n,r).

Lemma R_Inc n r r': sideRLs tm h1 r r' ->
  progress tm (Sconf (S n) r) (Sconf n r').
Proof. apply Inc. Qed.

Lemma R_Ov n n0 r r':
  sideRLs tm h1 r (G.D1 n *> G.D1 (1+n0) *> r') ->
  progress tm (Sconf O r) (Sconf (5+n) (G.D2 n0 *> r')).
Proof. apply Ov. Qed.

Lemma R_halt_side n r : sideRLs_halt tm h1 r ->
  halts tm (Sconf n r).
Proof.
  intros H. unfold Sconf,S'.
  eapply sideRLs_halt_single in H. exact H.
Qed.

Lemma denote_init :
  G.denote_machine P.init109b =
  G.D1 7 *> G.D1 7 *> G.D1 7 *> G.D1 7 *>
  G.D2 2 *> G.D1 3 *> G.D1 3 *> 0inf.
Proof.
  cbv [G.denote_machine P.init109b P.of_list P.contents
       P.queue P.edge G.layer G.words_side G.word_bits]. reflexivity.
Qed.

Lemma init_fast : c0 -[tm]->* Sconf O (G.denote_machine P.init109b).
Proof.
  rewrite denote_init. unfold Sconf.
  eapply evstep_trans; [apply init|exact bridge109b].
Qed.

Lemma init_prop : G.machine_prop tm Sconf c0 P.init109b.
Proof. split; [apply G.valid_init109b|exact init_fast]. Qed.

Lemma certificate : P.stoppedb (P.run8 27 30000 P.init109b)=true.
Proof. native_check_eq. Qed.

Theorem halt: halts tm c0.
Proof.
  eapply G.stopped_run8_halts with
    (tm:=tm) (h1:=h1) (Sconf:=Sconf) (c0:=c0)
    (run:=27%nat) (bound:=30000%N) (init:=P.init109b).
  all: first
    [ exact R_D1 | exact R_D13 | exact R_rh | exact R_D21 | exact R_D23
    | exact R_D2rh | exact R_D14 | exact R_D22 | exact R_D24
    | exact R_Inc | exact R_Ov | exact R_halt_side
    | exact D1_0_A3_halt | exact init_prop | exact certificate ].
Qed.

End TM2.
