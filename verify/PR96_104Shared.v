(** Shared two-counter proof for PRs #104 and #96.
    Adapted from the two PR proofs. Their abstract machine and 32
    affine return rules are identical; only the realization of the
    bounded tape windows and the path from the blank tape differ. *)

From Coq Require Import Bool Lists.List NArith.BinNat PArith.BinPos Lia String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Module TM104.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---").

Module Shared.

(** Coordinates of #104. For #96, first change the two exceptional
    transitions, then mirror and rename the states at the interface. *)
Definition variant_tm (v : bool) '(q,s) : option (Sym * dir * Q) :=
  match q,s with
  | B,S0 => if v then Some (S1,L,D) else TM104.tm (q,s)
  | E,S1 => if v then Some (S1,L,C) else TM104.tm (q,s)
  | _,_ => TM104.tm (q,s)
  end.

Local Close Scope sym_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Arguments N.mul : simpl never.

(** ** Section 1: Concrete RLE Data Structures, Equality Reflection & Stack Operations *)

Inductive LTok : Type :=
| L_z (k : N)
| L_o (k : N)
| L_p (k : N)
| L_ab (k : N).

Inductive RTok : Type :=
| R_z (k : N)
| R_o (k : N)
| R_q (k : N)
| R_ba (k : N).

Inductive Mode : Type := mAL | mDR.

Record BaseState : Type := mkBase {
  mode : Mode;
  l : list LTok;
  r : list RTok
}.

Definition ltokBeq (x y : LTok) : bool :=
  match x, y with
  | L_z a, L_z b => N.eqb a b
  | L_o a, L_o b => N.eqb a b
  | L_p a, L_p b => N.eqb a b
  | L_ab a, L_ab b => N.eqb a b
  | _, _ => false
  end.

Definition rtokBeq (x y : RTok) : bool :=
  match x, y with
  | R_z a, R_z b => N.eqb a b
  | R_o a, R_o b => N.eqb a b
  | R_q a, R_q b => N.eqb a b
  | R_ba a, R_ba b => N.eqb a b
  | _, _ => false
  end.

Fixpoint listLBeq (xs ys : list LTok) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if ltokBeq x y then listLBeq xs' ys' else false
  | _, _ => false
  end.

Fixpoint listRBeq (xs ys : list RTok) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if rtokBeq x y then listRBeq xs' ys' else false
  | _, _ => false
  end.

Definition modeBeq (a b : Mode) : bool :=
  match a, b with
  | mAL, mAL => true
  | mDR, mDR => true
  | _, _ => false
  end.

Definition stateBeqK (a b : BaseState) : bool :=
  if modeBeq (mode a) (mode b) then
    if listLBeq (l a) (l b) then listRBeq (r a) (r b) else false
  else false.

Lemma ltokBeq_eq (x y : LTok) : ltokBeq x y = true -> x = y.
Proof.
  destruct x, y; cbn [ltokBeq]; try discriminate;
    intro H; apply N.eqb_eq in H; subst; reflexivity.
Qed.

Lemma rtokBeq_eq (x y : RTok) : rtokBeq x y = true -> x = y.
Proof.
  destruct x, y; cbn [rtokBeq]; try discriminate;
    intro H; apply N.eqb_eq in H; subst; reflexivity.
Qed.

Lemma rtokBeq_refl (x : RTok) : rtokBeq x x = true.
Proof.
  destruct x; cbn [rtokBeq]; apply N.eqb_refl.
Qed.

Lemma listLBeq_eq : forall (xs ys : list LTok), listLBeq xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [listLBeq] in H;
    try reflexivity; try discriminate.
  destruct (ltokBeq x y) eqn:Hxy; [| discriminate].
  f_equal; [exact (ltokBeq_eq x y Hxy) | exact (IH ys' H)].
Qed.

Lemma listRBeq_eq : forall (xs ys : list RTok), listRBeq xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [listRBeq] in H;
    try reflexivity; try discriminate.
  destruct (rtokBeq x y) eqn:Hxy; [| discriminate].
  f_equal; [exact (rtokBeq_eq x y Hxy) | exact (IH ys' H)].
Qed.

Lemma listRBeq_refl : forall (xs : list RTok), listRBeq xs xs = true.
Proof.
  induction xs as [| x xs' IH]; [reflexivity |].
  cbn [listRBeq]. rewrite rtokBeq_refl. exact IH.
Qed.

Lemma listRBeq_false_of_ne (xs ys : list RTok) : xs <> ys -> listRBeq xs ys = false.
Proof.
  intros Hne. destruct (listRBeq xs ys) eqn:Hb; [| reflexivity].
  exfalso. exact (Hne (listRBeq_eq xs ys Hb)).
Qed.

Lemma modeBeq_eq (a b : Mode) : modeBeq a b = true -> a = b.
Proof.
  destruct a, b; cbn [modeBeq]; intro H; try reflexivity; discriminate.
Qed.

Lemma stateBeqK_eq (a b : BaseState) : stateBeqK a b = true -> a = b.
Proof.
  destruct a as [ma la ra], b as [mb lb rb]; unfold stateBeqK; cbn [mode l r].
  destruct (modeBeq ma mb) eqn:Hm; [| discriminate].
  destruct (listLBeq la lb) eqn:Hl; [| discriminate].
  intro Hr.
  f_equal; [exact (modeBeq_eq _ _ Hm) | exact (listLBeq_eq _ _ Hl) | exact (listRBeq_eq _ _ Hr)].
Qed.

(** *** Coalescing Stack Operations *)

Definition pushPL (k : N) (ls : list LTok) : list LTok :=
  match ls with
  | L_p m :: rest => L_p (k + 1 + m) :: rest
  | rest => L_p k :: rest
  end.

Definition pushABL (k : N) (ls : list LTok) : list LTok :=
  match ls with
  | L_ab m :: rest => L_ab (k + 1 + m) :: rest
  | rest => L_ab k :: rest
  end.

Definition pushOL (k : N) (ls : list LTok) : list LTok :=
  match ls with
  | L_o m :: rest => L_o (k + 1 + m) :: rest
  | rest => L_o k :: rest
  end.

Definition pushZeroL (ls : list LTok) : list LTok :=
  match ls with
  | L_o k :: rest =>
    if N.eqb k 0 then L_z 0 :: L_o 0 :: rest
    else if N.eqb k 1 then pushPL 0 rest
    else L_p 0 :: L_o (k - 2) :: rest
  | L_z m :: rest => L_z (m + 1) :: rest
  | rest => L_z 0 :: rest
  end.

Definition pushOneL (ls : list LTok) : list LTok :=
  match ls with
  | L_z k :: rest =>
    if N.eqb k 0 then pushABL 0 rest
    else L_ab 0 :: L_z (k - 1) :: rest
  | L_o m :: rest => L_o (m + 1) :: rest
  | rest => L_o 0 :: rest
  end.

Definition popL (ls : list LTok) : bool * list LTok :=
  match ls with
  | [] => (false, [])
  | L_z k :: rest => if N.eqb k 0 then (false, rest) else (false, L_z (k - 1) :: rest)
  | L_o k :: rest => if N.eqb k 0 then (true, rest) else (true, L_o (k - 1) :: rest)
  | L_p k :: rest => if N.eqb k 0 then (false, pushOL 1 rest) else (false, pushOL 1 (L_p (k - 1) :: rest))
  | L_ab k :: rest => if N.eqb k 0 then (true, pushZeroL rest) else (true, pushZeroL (L_ab (k - 1) :: rest))
  end.

Definition pushQR (k : N) (rs : list RTok) : list RTok :=
  match rs with
  | R_q m :: rest => R_q (k + 1 + m) :: rest
  | rest => R_q k :: rest
  end.

Definition pushBAR (k : N) (rs : list RTok) : list RTok :=
  match rs with
  | R_ba m :: rest => R_ba (k + 1 + m) :: rest
  | rest => R_ba k :: rest
  end.

Definition pushZRawR (k : N) (rs : list RTok) : list RTok :=
  match rs with
  | R_z m :: rest => R_z (k + 1 + m) :: rest
  | rest => R_z k :: rest
  end.

Definition pushZeroR (rs : list RTok) : list RTok :=
  match rs with
  | R_o k :: rest =>
    if N.eqb k 0 then pushBAR 0 rest
    else R_ba 0 :: R_o (k - 1) :: rest
  | R_ba k :: rest =>
    if N.eqb k 0 then pushQR 0 rest
    else R_q 0 :: R_ba (k - 1) :: rest
  | R_z m :: rest => R_z (m + 1) :: rest
  | rest => R_z 0 :: rest
  end.

Definition pushOneR (rs : list RTok) : list RTok :=
  match rs with
  | R_o m :: rest => R_o (m + 1) :: rest
  | rest => R_o 0 :: rest
  end.

Definition pushZerosAtLeast1R (cnt : N) (rs : list RTok) : list RTok :=
  if N.eqb cnt 0 then pushZeroR rs
  else if N.eqb cnt 1 then pushZeroR (pushZeroR rs)
  else pushZRawR (cnt - 2) (pushZeroR (pushZeroR rs)).

Definition pushZerosAtLeast2R (cnt : N) (rs : list RTok) : list RTok :=
  if N.eqb cnt 0 then pushZeroR (pushZeroR rs)
  else pushZRawR (cnt - 1) (pushZeroR (pushZeroR rs)).

Definition push10RepeatR (cnt : N) (rs : list RTok) : list RTok :=
  if N.eqb cnt 0 then pushOneR (pushZeroR rs)
  else pushOneR (pushBAR (cnt - 1) (pushZeroR rs)).

Definition push100RepeatR (cnt : N) (rs : list RTok) : list RTok :=
  if N.eqb cnt 0 then pushOneR (pushZeroR (pushZeroR rs))
  else pushOneR (pushQR (cnt - 1) (pushZeroR (pushZeroR rs))).

Definition popR (rs : list RTok) : bool * list RTok :=
  match rs with
  | [] => (false, [])
  | R_z k :: rest => if N.eqb k 0 then (false, rest) else (false, R_z (k - 1) :: rest)
  | R_o k :: rest => if N.eqb k 0 then (true, rest) else (true, R_o (k - 1) :: rest)
  | R_q k :: rest => if N.eqb k 0 then (false, pushBAR 0 rest) else (false, pushBAR 0 (R_q (k - 1) :: rest))
  | R_ba k :: rest => if N.eqb k 0 then (false, pushOneR rest) else (false, pushOneR (R_ba (k - 1) :: rest))
  end.

Fixpoint splitLeadingOnesL (ls : list LTok) : N * list LTok :=
  match ls with
  | [] => (0, [])
  | L_o k :: rest =>
    let ih := splitLeadingOnesL rest in
    (k + 1 + fst ih, snd ih)
  | L_ab k :: rest =>
    if N.eqb k 0 then (1, pushZeroL rest)
    else (1, pushZeroL (L_ab (k - 1) :: rest))
  | L_z k :: rest => (0, L_z k :: rest)
  | L_p k :: rest => (0, L_p k :: rest)
  end.

Fixpoint sweepAL (ls : list LTok) (rs : list RTok) : list LTok * list RTok :=
  match ls with
  | L_ab k :: rest => sweepAL rest (push10RepeatR k rs)
  | L_o k :: rest =>
    if N.eqb k 0 then
      match rest with
      | [] => ([], push10RepeatR 0 rs)
      | L_z zk :: rest2 =>
        if N.eqb zk 0 then sweepAL rest2 (push10RepeatR 0 rs)
        else (L_z (zk - 1) :: rest2, push10RepeatR 0 rs)
      | L_p pk :: rest2 =>
        if N.eqb pk 0 then (pushOL 1 rest2, push10RepeatR 0 rs)
        else (L_o 1 :: L_p (pk - 1) :: rest2, push10RepeatR 0 rs)
      | _ => (ls, rs)
      end
    else (ls, rs)
  | _ => (ls, rs)
  end.

Definition isZeroHeadL (ls : list LTok) : bool :=
  match ls with
  | [] => true
  | L_z _ :: _ => true
  | L_p _ :: _ => true
  | _ => false
  end.

Definition stepALZeroFallback (ls : list LTok) (rs : list RTok) : option BaseState :=
  let r0 := popR rs in
  let lt := snd (popL ls) in
  if fst r0 then
    let r1 := popR (snd r0) in
    if fst r1 then None
    else
      let r2 := popR (snd r1) in
      let lBase := pushZeroL (pushOL 1 lt) in
      let lOut := if fst r2 then pushOneL lBase else pushZeroL lBase in
      Some (mkBase mDR lOut (snd r2))
  else
    let l1 := popL lt in
    if fst l1 then
      let sp := splitLeadingOnesL (snd l1) in
      let l3 := popL (snd sp) in
      Some (mkBase mAL (snd l3) (pushOneR (pushZerosAtLeast2R (fst sp) (pushOneR (snd r0)))))
    else
      Some (mkBase mAL (snd l1) (pushOneR (pushZeroR (pushOneR (snd r0))))).

Definition stepALElse (ls : list LTok) (rs : list RTok) : option BaseState :=
  if isZeroHeadL ls then
    match rs with
    | R_o ok :: R_z zk :: R_q k :: rt =>
      if N.eqb ok 0 then
        if N.eqb zk 0 then
          let lt := snd (popL ls) in
          Some (mkBase mAL (pushZeroL (pushPL k lt)) (pushOneR (pushZeroR rt)))
        else stepALZeroFallback ls rs
      else stepALZeroFallback ls rs
    | R_o ok :: R_q qk :: R_ba k :: rt =>
      if N.eqb ok 0 then
        if N.eqb qk 0 then
          let lt := snd (popL ls) in
          Some (mkBase mAL (pushZeroL (pushOL (2 * k + 3) lt)) (pushOneR (pushZeroR rt)))
        else stepALZeroFallback ls rs
      else stepALZeroFallback ls rs
    | _ => stepALZeroFallback ls rs
    end
  else
    let sw := sweepAL ls rs in
    let l0 := popL (fst sw) in
    if fst l0 then
      let l1 := popL (snd l0) in
      if fst l1 then
        let sp := splitLeadingOnesL (snd l1) in
        let l3 := popL (snd sp) in
        Some (mkBase mAL (snd l3) (pushOneR (pushZerosAtLeast2R (fst sp) (snd sw))))
      else
        Some (mkBase mAL (snd l1) (push10RepeatR 0 (snd sw)))
    else
      let r0 := popR (snd sw) in
      if fst r0 then
        let r1 := popR (snd r0) in
        if fst r1 then None
        else
          let r2 := popR (snd r1) in
          let lBase := pushZeroL (pushOL 1 (snd l0)) in
          let lOut := if fst r2 then pushOneL lBase else pushZeroL lBase in
          Some (mkBase mDR lOut (snd r2))
      else
        let l1 := popL (snd l0) in
        if fst l1 then
          let sp := splitLeadingOnesL (snd l1) in
          let l3 := popL (snd sp) in
          Some (mkBase mAL (snd l3) (pushOneR (pushZerosAtLeast2R (fst sp) (pushOneR (snd r0)))))
        else
          Some (mkBase mAL (snd l1) (pushOneR (pushZeroR (pushOneR (snd r0))))).

Definition stepDRFallback (ls : list LTok) (rs : list RTok) : option BaseState :=
  let r0 := popR rs in
  if fst r0 then
    let sp := splitLeadingOnesL ls in
    let l2 := popL (snd sp) in
    Some (mkBase mAL (snd l2) (pushOneR (pushZerosAtLeast1R (fst sp) (snd r0))))
  else
    let r1 := popR (snd r0) in
    if fst r1 then
      Some (mkBase mAL ls (pushOneR (pushZeroR (snd r1))))
    else
      let r2 := popR (snd r1) in
      if negb (fst r2) then
        Some (mkBase mAL ls (pushOneR (pushZeroR (pushOneR (snd r2)))))
      else
        let r3 := popR (snd r2) in
        if fst r3 then None
        else
          let r4 := popR (snd r3) in
          let lBase := pushZeroL (pushOL 1 (pushZeroL ls)) in
          let lOut := if fst r4 then pushOneL lBase else pushZeroL lBase in
          Some (mkBase mDR lOut (snd r4)).

Definition stepDRBase (ls : list LTok) (rs : list RTok) : option BaseState :=
  if isZeroHeadL ls then
    let lt := snd (popL ls) in
    match rs with
    | R_q qk :: rtail =>
      if N.eqb qk 0 then stepDRFallback ls rs
      else
        let crossElse :=
          if N.eqb qk 1 then
            Some (mkBase mAL (pushPL 0 (pushZeroL (pushZeroL lt))) (pushOneR (pushZeroR rtail)))
          else
            Some (mkBase mAL (pushZeroL (pushPL (qk - 2) (pushOL 1 (pushZeroL (pushZeroL lt))))) (pushOneR (pushZeroR rtail)))
        in
        match rtail with
        | R_z zk :: R_q v :: rt =>
          if N.eqb zk 1 then
            Some (mkBase mDR (pushZeroL (pushPL v lt)) (pushQR qk (pushZeroR (pushZeroR rt))))
          else crossElse
        | _ => crossElse
        end
    | _ => stepDRFallback ls rs
    end
  else stepDRFallback ls rs.

Definition stepBaseK (b : BaseState) : option BaseState :=
  match mode b with
  | mAL =>
    match l b with
    | L_o ok :: L_p k :: lt =>
      if N.eqb ok 1 then
        Some (mkBase mAL (pushOL 1 lt) (push100RepeatR k (r b)))
      else stepALElse (l b) (r b)
    | _ => stepALElse (l b) (r b)
    end
  | mDR => stepDRBase (l b) (r b)
  end.

(** ** Section 2: Direct Tape Decoding & Coalescing RLE Stack Soundness *)

Definition repWord (w : list Sym) (n : N) (acc : list Sym) : list Sym :=
  N.peano_rect (fun _ => list Sym) acc (fun _ rec => w ++ rec) n.

Lemma repWord_0 (w : list Sym) (acc : list Sym) :
  repWord w 0 acc = acc.
Proof. reflexivity. Qed.

Lemma repWord_succ (w : list Sym) (n : N) (acc : list Sym) :
  repWord w (n + 1) acc = w ++ repWord w n acc.
Proof.
  unfold repWord.
  replace (n + 1) with (N.succ n) by lia.
  rewrite N.peano_rect_succ.
  reflexivity.
Qed.

Lemma repWord_add (w : list Sym) (a b : N) (acc : list Sym) :
  repWord w (a + b) acc = repWord w a (repWord w b acc).
Proof.
  induction a as [| a IH] using N.peano_ind.
  - cbn. reflexivity.
  - replace (N.succ a + b) with ((a + b) + 1) by lia.
    replace (N.succ a) with (a + 1) by lia.
    rewrite !repWord_succ, IH.
    reflexivity.
Qed.

Lemma repWord_snoc (w : list Sym) (n : N) (acc : list Sym) :
  repWord w n (w ++ acc) = repWord w (n + 1) acc.
Proof.
  rewrite repWord_add.
  replace (repWord w 1 acc) with (repWord w (0 + 1) acc) by reflexivity.
  rewrite repWord_succ, repWord_0.
  reflexivity.
Qed.

Definition repZero := repWord [S0].
Definition repOne  := repWord [S1].
Definition repP    := repWord [S0; S1; S1].
Definition repAB   := repWord [S1; S0].
Definition repQ    := repWord [S0; S0; S1].
Definition repBA   := repWord [S0; S1].
Definition rep100  := repWord [S1; S0; S0].

Lemma repZero_0 acc : repZero 0 acc = acc. Proof. reflexivity. Qed.
Lemma repOne_0  acc : repOne  0 acc = acc. Proof. reflexivity. Qed.
Lemma repP_0    acc : repP    0 acc = acc. Proof. reflexivity. Qed.
Lemma repAB_0   acc : repAB   0 acc = acc. Proof. reflexivity. Qed.
Lemma repQ_0    acc : repQ    0 acc = acc. Proof. reflexivity. Qed.
Lemma repBA_0   acc : repBA   0 acc = acc. Proof. reflexivity. Qed.
Lemma rep100_0  acc : rep100  0 acc = acc. Proof. reflexivity. Qed.

Lemma repZero_succ n acc : repZero (n + 1) acc = S0 :: repZero n acc.
Proof. exact (repWord_succ [S0] n acc). Qed.
Lemma repOne_succ n acc : repOne (n + 1) acc = S1 :: repOne n acc.
Proof. exact (repWord_succ [S1] n acc). Qed.
Lemma repP_succ n acc : repP (n + 1) acc = S0 :: S1 :: S1 :: repP n acc.
Proof. exact (repWord_succ [S0; S1; S1] n acc). Qed.
Lemma repAB_succ n acc : repAB (n + 1) acc = S1 :: S0 :: repAB n acc.
Proof. exact (repWord_succ [S1; S0] n acc). Qed.
Lemma repQ_succ n acc : repQ (n + 1) acc = S0 :: S0 :: S1 :: repQ n acc.
Proof. exact (repWord_succ [S0; S0; S1] n acc). Qed.
Lemma repBA_succ n acc : repBA (n + 1) acc = S0 :: S1 :: repBA n acc.
Proof. exact (repWord_succ [S0; S1] n acc). Qed.
Lemma rep100_succ n acc : rep100 (n + 1) acc = S1 :: S0 :: S0 :: rep100 n acc.
Proof. exact (repWord_succ [S1; S0; S0] n acc). Qed.

Lemma repZero_add a b acc : repZero (a + b) acc = repZero a (repZero b acc).
Proof. exact (repWord_add [S0] a b acc). Qed.
Lemma repOne_add a b acc : repOne (a + b) acc = repOne a (repOne b acc).
Proof. exact (repWord_add [S1] a b acc). Qed.
Lemma repP_add a b acc : repP (a + b) acc = repP a (repP b acc).
Proof. exact (repWord_add [S0; S1; S1] a b acc). Qed.
Lemma repAB_add a b acc : repAB (a + b) acc = repAB a (repAB b acc).
Proof. exact (repWord_add [S1; S0] a b acc). Qed.
Lemma repQ_add a b acc : repQ (a + b) acc = repQ a (repQ b acc).
Proof. exact (repWord_add [S0; S0; S1] a b acc). Qed.
Lemma repBA_add a b acc : repBA (a + b) acc = repBA a (repBA b acc).
Proof. exact (repWord_add [S0; S1] a b acc). Qed.
Lemma rep100_add a b acc : rep100 (a + b) acc = rep100 a (rep100 b acc).
Proof. exact (repWord_add [S1; S0; S0] a b acc). Qed.

Lemma repZero_snoc n acc : repZero n (S0 :: acc) = repZero (n + 1) acc.
Proof. exact (repWord_snoc [S0] n acc). Qed.
Lemma repP_snoc n acc : repP n (S0 :: S1 :: S1 :: acc) = repP (n + 1) acc.
Proof. exact (repWord_snoc [S0; S1; S1] n acc). Qed.
Lemma repAB_snoc n acc : repAB n (S1 :: S0 :: acc) = repAB (n + 1) acc.
Proof. exact (repWord_snoc [S1; S0] n acc). Qed.
Lemma rep100_snoc n acc : rep100 n (S1 :: S0 :: S0 :: acc) = rep100 (n + 1) acc.
Proof. exact (repWord_snoc [S1; S0; S0] n acc). Qed.

Lemma repOne_snoc2 n acc : repOne (2 * n) (S1 :: S1 :: acc) = repOne (2 * (n + 1)) acc.
Proof.
  replace (2 * (n + 1)) with (2 * n + 2) by lia.
  rewrite repOne_add.
  reflexivity.
Qed.

Lemma one_repBA_zero (k : N) (acc : list Sym) :
  S1 :: repBA k (S0 :: acc) = repAB (k + 1) acc.
Proof.
  induction k as [| k IH] using N.peano_ind.
  - reflexivity.
  - replace (N.succ k) with (k + 1) by lia.
    rewrite repBA_succ, IH, <- repAB_succ.
    reflexivity.
Qed.

Lemma one_repQ_zero_zero (k : N) (acc : list Sym) :
  S1 :: repQ k (S0 :: S0 :: acc) = rep100 (k + 1) acc.
Proof.
  induction k as [| k IH] using N.peano_ind.
  - reflexivity.
  - replace (N.succ k) with (k + 1) by lia.
    rewrite repQ_succ, IH, <- rep100_succ.
    reflexivity.
Qed.

Lemma rep100_one (n : N) (rs : list Sym) :
  rep100 n (S1 :: rs) = S1 :: repQ n rs.
Proof.
  induction n as [| n IH] using N.peano_ind.
  - reflexivity.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite rep100_succ, IH, repQ_succ.
    reflexivity.
Qed.

Fixpoint decL (ls : list LTok) : list Sym :=
  match ls with
  | [] => []
  | L_z k :: rest => repZero (k + 1) (decL rest)
  | L_o k :: rest => repOne (k + 1) (decL rest)
  | L_p k :: rest => repP (k + 1) (decL rest)
  | L_ab k :: rest => repAB (k + 1) (decL rest)
  end.

Fixpoint decR (rs : list RTok) : list Sym :=
  match rs with
  | [] => []
  | R_z k :: rest => repZero (k + 1) (decR rest)
  | R_o k :: rest => repOne (k + 1) (decR rest)
  | R_q k :: rest => repQ (k + 1) (decR rest)
  | R_ba k :: rest => repBA (k + 1) (decR rest)
  end.

Fixpoint encTape (xs : list Sym) : side :=
  match xs with
  | [] => const S0
  | x :: xs' => x >> encTape xs'
  end.

Definition mEncL (q : Q) (ls rs : list Sym) : Q * tape :=
  (encTape ls) <{{ q }} (encTape rs).

Definition mEncR (q : Q) (ls rs : list Sym) : Q * tape :=
  (encTape ls) {{ q }}> (encTape rs).

Definition encodeBase (b : BaseState) : Q * tape :=
  match mode b with
  | mAL => mEncL A (decL (l b)) (decR (r b))
  | mDR => mEncR D (decL (l b)) (decR (r b))
  end.

Definition popBit (xs : list Sym) : Sym * list Sym :=
  match xs with
  | [] => (S0, [])
  | b :: xs' => (b, xs')
  end.

Definition bitOfBool (b : bool) : Sym :=
  if b then S1 else S0.

Fixpoint splitOnesBits (xs : list Sym) : N * list Sym :=
  match xs with
  | S1 :: xs' =>
    let res := splitOnesBits xs' in
    (fst res + 1, snd res)
  | _ => (0, xs)
  end.

Lemma popBit_hd_tl (xs : list Sym) :
  hd (encTape xs) = fst (popBit xs) /\ tl (encTape xs) = encTape (snd (popBit xs)).
Proof.
  destruct xs as [| b xs']; split; reflexivity.
Qed.

Lemma encTape_popBit_recons (xs : list Sym) :
  encTape (fst (popBit xs) :: snd (popBit xs)) = encTape xs.
Proof.
  destruct xs as [| b xs']; [cbn; symmetry; exact (const_unfold Sym S0) | reflexivity].
Qed.

Section TapeSteps.
Variable tab : TM.
Local Notation tm := tab.

Lemma step_mEncL_step {q q' : Q} {b : Sym} {ls rs : list Sym} :
  tm (q, fst (popBit ls)) = Some (b, L, q') ->
  mEncL q ls rs -[ tm ]-> mEncL q' (snd (popBit ls)) (b :: rs).
Proof.
  intro Htm. unfold mEncL.
  destruct (popBit_hd_tl ls) as [Hhd Htl].
  rewrite Hhd, Htl.
  exact (step_left Htm).
Qed.

Lemma step_mEncL_rev {q q' : Q} {b : Sym} {ls rs : list Sym} :
  tm (q, fst (popBit ls)) = Some (b, R, q') ->
  mEncL q ls rs -[ tm ]-> mEncR q' (b :: snd (popBit ls)) rs.
Proof.
  intro Htm. unfold mEncL.
  destruct (popBit_hd_tl ls) as [Hhd Htl].
  rewrite Hhd, Htl.
  exact (step_right Htm).
Qed.

Lemma step_mEncR_step {q q' : Q} {b : Sym} {ls rs : list Sym} :
  tm (q, fst (popBit rs)) = Some (b, R, q') ->
  mEncR q ls rs -[ tm ]-> mEncR q' (b :: ls) (snd (popBit rs)).
Proof.
  intro Htm. unfold mEncR.
  destruct (popBit_hd_tl rs) as [Hhd Htl].
  rewrite Hhd, Htl.
  exact (step_right Htm).
Qed.

Lemma step_mEncR_rev {q q' : Q} {b : Sym} {ls rs : list Sym} :
  tm (q, fst (popBit rs)) = Some (b, L, q') ->
  mEncR q ls rs -[ tm ]-> mEncL q' ls (b :: snd (popBit rs)).
Proof.
  intro Htm. unfold mEncR.
  destruct (popBit_hd_tl rs) as [Hhd Htl].
  rewrite Hhd, Htl.
  exact (step_left Htm).
Qed.

Lemma step_mEncL_cons_step {q q' : Q} {a b : Sym} {ls rs : list Sym} :
  tm (q, a) = Some (b, L, q') ->
  mEncL q (a :: ls) rs -[ tm ]-> mEncL q' ls (b :: rs).
Proof. exact (@step_mEncL_step q q' b (a :: ls) rs). Qed.

Lemma step_mEncL_cons_rev {q q' : Q} {a b : Sym} {ls rs : list Sym} :
  tm (q, a) = Some (b, R, q') ->
  mEncL q (a :: ls) rs -[ tm ]-> mEncR q' (b :: ls) rs.
Proof. exact (@step_mEncL_rev q q' b (a :: ls) rs). Qed.

Lemma step_mEncL_nil_step {q q' : Q} {b : Sym} {rs : list Sym} :
  tm (q, S0) = Some (b, L, q') ->
  mEncL q [] rs -[ tm ]-> mEncL q' [] (b :: rs).
Proof. exact (@step_mEncL_step q q' b [] rs). Qed.

Lemma step_mEncL_nil_rev {q q' : Q} {b : Sym} {rs : list Sym} :
  tm (q, S0) = Some (b, R, q') ->
  mEncL q [] rs -[ tm ]-> mEncR q' [b] rs.
Proof. exact (@step_mEncL_rev q q' b [] rs). Qed.

Lemma step_mEncR_cons_step {q q' : Q} {a b : Sym} {ls rs : list Sym} :
  tm (q, a) = Some (b, R, q') ->
  mEncR q ls (a :: rs) -[ tm ]-> mEncR q' (b :: ls) rs.
Proof. exact (@step_mEncR_step q q' b ls (a :: rs)). Qed.

Lemma step_mEncR_cons_rev {q q' : Q} {a b : Sym} {ls rs : list Sym} :
  tm (q, a) = Some (b, L, q') ->
  mEncR q ls (a :: rs) -[ tm ]-> mEncL q' ls (b :: rs).
Proof. exact (@step_mEncR_rev q q' b ls (a :: rs)). Qed.

End TapeSteps.
Arguments step_mEncL_step {tab q q' b ls rs} _.
Arguments step_mEncL_rev {tab q q' b ls rs} _.
Arguments step_mEncR_step {tab q q' b ls rs} _.
Arguments step_mEncR_rev {tab q q' b ls rs} _.
Arguments step_mEncL_cons_step {tab q q' a b ls rs} _.
Arguments step_mEncL_cons_rev {tab q q' a b ls rs} _.
Arguments step_mEncL_nil_step {tab q q' b rs} _.
Arguments step_mEncL_nil_rev {tab q q' b rs} _.
Arguments step_mEncR_cons_step {tab q q' a b ls rs} _.
Arguments step_mEncR_cons_rev {tab q q' a b ls rs} _.

(** *** Coalescing Stack Soundness Lemmas *)

Lemma decL_pushPL (k : N) (ls : list LTok) :
  decL (pushPL k ls) = repP (k + 1) (decL ls).
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [pushPL decL]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repP_add (k + 1) (m + 1) (decL rest)).
Qed.

Lemma decL_pushABL (k : N) (ls : list LTok) :
  decL (pushABL k ls) = repAB (k + 1) (decL ls).
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [pushABL decL]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repAB_add (k + 1) (m + 1) (decL rest)).
Qed.

Lemma decL_pushOL (k : N) (ls : list LTok) :
  decL (pushOL k ls) = repOne (k + 1) (decL ls).
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [pushOL decL]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repOne_add (k + 1) (m + 1) (decL rest)).
Qed.

Lemma decL_pushZeroL (ls : list LTok) :
  decL (pushZeroL ls) = S0 :: decL ls.
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [pushZeroL decL].
  - reflexivity.
  - replace (m + 1 + 1) with ((m + 1) + 1) by lia.
    rewrite repZero_succ. reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. reflexivity.
    + destruct (N.eqb m 1) eqn:Hm1.
      * apply N.eqb_eq in Hm1; subst m.
        rewrite decL_pushPL. reflexivity.
      * apply N.eqb_neq in Hm0. apply N.eqb_neq in Hm1.
        cbn [decL].
        replace (m + 1) with (((m - 2 + 1) + 1) + 1) by lia.
        rewrite (repOne_succ (m - 2 + 1 + 1)), (repOne_succ (m - 2 + 1)). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma decL_pushOneL (ls : list LTok) :
  decL (pushOneL ls) = S1 :: decL ls.
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [pushOneL decL].
  - reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m.
      rewrite decL_pushABL. reflexivity.
    + apply N.eqb_neq in Hm0. cbn [decL].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite (repZero_succ (m - 1 + 1)). reflexivity.
  - replace (m + 1 + 1) with ((m + 1) + 1) by lia.
    rewrite (repOne_succ (m + 1)). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma decL_popL (ls : list LTok) :
  bitOfBool (fst (popL ls)) = fst (popBit (decL ls)) /\
  decL (snd (popL ls)) = snd (popBit (decL ls)).
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [popL decL].
  - split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. split; reflexivity.
    + apply N.eqb_neq in Hm0.
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repZero_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. split; reflexivity.
    + apply N.eqb_neq in Hm0.
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repOne_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. cbn [fst snd].
      rewrite decL_pushOL. split; reflexivity.
    + apply N.eqb_neq in Hm0. cbn [fst snd].
      rewrite decL_pushOL. cbn [decL].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repP_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. cbn [fst snd].
      rewrite decL_pushZeroL. split; reflexivity.
    + apply N.eqb_neq in Hm0. cbn [fst snd].
      rewrite decL_pushZeroL. cbn [decL].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repAB_succ (m - 1 + 1)). split; reflexivity.
Qed.

Lemma isZeroHeadL_sound (ls : list LTok) :
  isZeroHeadL ls = true -> fst (popBit (decL ls)) = S0.
Proof.
  destruct ls as [| [m | m | m | m] rest]; cbn [isZeroHeadL decL]; intro H;
    try discriminate; try reflexivity;
    rewrite ?repZero_succ, ?repP_succ; reflexivity.
Qed.

Lemma decR_pushQR (k : N) (rs : list RTok) :
  decR (pushQR k rs) = repQ (k + 1) (decR rs).
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [pushQR decR]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repQ_add (k + 1) (m + 1) (decR rest)).
Qed.

Lemma decR_pushBAR (k : N) (rs : list RTok) :
  decR (pushBAR k rs) = repBA (k + 1) (decR rs).
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [pushBAR decR]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repBA_add (k + 1) (m + 1) (decR rest)).
Qed.

Lemma decR_pushZRawR (k : N) (rs : list RTok) :
  decR (pushZRawR k rs) = repZero (k + 1) (decR rs).
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [pushZRawR decR]; try reflexivity.
  replace (k + 1 + m + 1) with ((k + 1) + (m + 1)) by lia.
  exact (repZero_add (k + 1) (m + 1) (decR rest)).
Qed.

Lemma decR_pushZeroR (rs : list RTok) :
  decR (pushZeroR rs) = S0 :: decR rs.
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [pushZeroR decR].
  - reflexivity.
  - replace (m + 1 + 1) with ((m + 1) + 1) by lia.
    rewrite repZero_succ. reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m.
      rewrite decR_pushBAR. reflexivity.
    + apply N.eqb_neq in Hm0. cbn [decR].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite (repOne_succ (m - 1 + 1)). reflexivity.
  - reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m.
      rewrite decR_pushQR. reflexivity.
    + apply N.eqb_neq in Hm0. cbn [decR].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite (repBA_succ (m - 1 + 1)). reflexivity.
Qed.

Lemma decR_pushOneR (rs : list RTok) :
  decR (pushOneR rs) = S1 :: decR rs.
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [pushOneR decR]; try reflexivity.
  replace (m + 1 + 1) with ((m + 1) + 1) by lia.
  rewrite (repOne_succ (m + 1)). reflexivity.
Qed.

Lemma decR_pushZerosAtLeast1R (sp : N) (rs : list RTok) :
  decR (pushZerosAtLeast1R sp rs) = repZero (sp + 1) (decR rs).
Proof.
  unfold pushZerosAtLeast1R.
  destruct (N.eqb sp 0) eqn:H0.
  - apply N.eqb_eq in H0; subst sp. rewrite decR_pushZeroR. reflexivity.
  - destruct (N.eqb sp 1) eqn:H1.
    + apply N.eqb_eq in H1; subst sp. rewrite !decR_pushZeroR. reflexivity.
    + apply N.eqb_neq in H0. apply N.eqb_neq in H1.
      rewrite decR_pushZRawR, !decR_pushZeroR.
      change (S0 :: S0 :: decR rs) with (repZero 2 (decR rs)).
      rewrite <- repZero_add.
      f_equal; lia.
Qed.

Lemma decR_pushZerosAtLeast2R (sp : N) (rs : list RTok) :
  decR (pushZerosAtLeast2R sp rs) = repZero (sp + 2) (decR rs).
Proof.
  unfold pushZerosAtLeast2R.
  destruct (N.eqb sp 0) eqn:H0.
  - apply N.eqb_eq in H0; subst sp. rewrite !decR_pushZeroR. reflexivity.
  - apply N.eqb_neq in H0.
    rewrite decR_pushZRawR, !decR_pushZeroR.
    change (S0 :: S0 :: decR rs) with (repZero 2 (decR rs)).
    rewrite <- repZero_add.
    f_equal; lia.
Qed.

Lemma decR_push10RepeatR (k : N) (rs : list RTok) :
  decR (push10RepeatR k rs) = repAB (k + 1) (decR rs).
Proof.
  unfold push10RepeatR.
  destruct (N.eqb k 0) eqn:H0.
  - apply N.eqb_eq in H0; subst k.
    rewrite decR_pushOneR, decR_pushZeroR. reflexivity.
  - apply N.eqb_neq in H0.
    rewrite decR_pushOneR, decR_pushBAR, decR_pushZeroR, one_repBA_zero.
    f_equal; lia.
Qed.

Lemma decR_push100RepeatR (k : N) (rs : list RTok) :
  decR (push100RepeatR k rs) = rep100 (k + 1) (decR rs).
Proof.
  unfold push100RepeatR.
  destruct (N.eqb k 0) eqn:H0.
  - apply N.eqb_eq in H0; subst k.
    rewrite decR_pushOneR, !decR_pushZeroR. reflexivity.
  - apply N.eqb_neq in H0.
    rewrite decR_pushOneR, decR_pushQR, !decR_pushZeroR, one_repQ_zero_zero.
    f_equal; lia.
Qed.

Lemma decR_popR (rs : list RTok) :
  bitOfBool (fst (popR rs)) = fst (popBit (decR rs)) /\
  decR (snd (popR rs)) = snd (popBit (decR rs)).
Proof.
  destruct rs as [| [m | m | m | m] rest]; cbn [popR decR].
  - split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. split; reflexivity.
    + apply N.eqb_neq in Hm0.
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repZero_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. split; reflexivity.
    + apply N.eqb_neq in Hm0.
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repOne_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. cbn [fst snd].
      rewrite decR_pushBAR. split; reflexivity.
    + apply N.eqb_neq in Hm0. cbn [fst snd].
      rewrite decR_pushBAR. cbn [decR].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repQ_succ (m - 1 + 1)). split; reflexivity.
  - destruct (N.eqb m 0) eqn:Hm0.
    + apply N.eqb_eq in Hm0; subst m. cbn [fst snd].
      rewrite decR_pushOneR. split; reflexivity.
    + apply N.eqb_neq in Hm0. cbn [fst snd].
      rewrite decR_pushOneR. cbn [decR].
      replace (m + 1) with ((m - 1 + 1) + 1) by lia.
      rewrite !(repBA_succ (m - 1 + 1)). split; reflexivity.
Qed.

Lemma splitOnesBits_repOne (n : N) (xs : list Sym) :
  splitOnesBits (repOne n xs) = (fst (splitOnesBits xs) + n, snd (splitOnesBits xs)).
Proof.
  induction n as [| n IH] using N.peano_ind.
  - rewrite repOne_0. destruct (splitOnesBits xs) as [c r0]; cbn. f_equal; lia.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite repOne_succ. cbn [splitOnesBits].
    rewrite IH; cbn [fst snd]. f_equal; lia.
Qed.

Lemma splitLeadingOnesL_sound :
  forall ls : list LTok,
    fst (splitLeadingOnesL ls) = fst (splitOnesBits (decL ls)) /\
    decL (snd (splitLeadingOnesL ls)) = snd (splitOnesBits (decL ls)).
Proof.
  induction ls as [| [k | k | k | k] rest IH]; cbn [splitLeadingOnesL decL].
  - split; reflexivity.
  - cbn [fst snd decL]. rewrite !repZero_succ; cbn [splitOnesBits fst snd]. split; reflexivity.
  - rewrite splitOnesBits_repOne. cbn [fst snd].
    destruct IH as [IH1 IH2]. split; [lia | exact IH2].
  - cbn [fst snd decL]. rewrite !repP_succ; cbn [splitOnesBits fst snd]. split; reflexivity.
  - destruct (N.eqb k 0) eqn:Hk0.
    + apply N.eqb_eq in Hk0; subst k.
      cbn [fst snd]. rewrite decL_pushZeroL, repAB_succ; cbn [splitOnesBits fst snd].
      rewrite repAB_0. split; reflexivity.
    + apply N.eqb_neq in Hk0.
      cbn [fst snd]. rewrite decL_pushZeroL; cbn [decL].
      replace (k + 1) with ((k - 1 + 1) + 1) by lia.
      rewrite !(repAB_succ (k - 1 + 1)); cbn [splitOnesBits fst snd]. split; reflexivity.
Qed.

(** ** Section 3: Bounded Tape Windows, Sweeps & [stepBaseK_sound] *)

(** Bounded checks inspect only the stated finite prefixes. In the closed
    right boundary case the omitted right tail is known to be blank. Stop
    at the first matching target rather than prescribing a raw step count. *)

Definition Window := (bool * Q * list Sym * list Sym)%type.

Definition mEncDir (d : bool) (q : Q) (ls rs : list Sym) : Q * tape :=
  if d then mEncR q ls rs else mEncL q ls rs.

Definition windowCfg (blank : bool) (lt rt : list Sym) (x : Window) :=
  let '(d,q,lp,rp) := x in
  mEncDir d q (lp ++ lt) (if blank then rp else rp ++ rt).

Section BoundedWindows.
Variable tab : TM.
Local Notation tm := tab.

Definition windowStep (blank : bool) (x : Window) : option Window :=
  let '(d,q,lp,rp) := x in
  let p := if d then rp else lp in
  let bit : option Sym := match p with
    | b :: _ => Some b
    | [] => if d && blank then Some S0 else None
    end in
  match bit with
  | None => None
  | Some b =>
    match tm (q,b) with
    | Some (w,L,q') =>
      Some (false,q',if d then lp else List.tl lp,w :: if d then List.tl rp else rp)
    | Some (w,R,q') =>
      Some (true,q',w :: if d then lp else List.tl lp,if d then List.tl rp else rp)
    | None => None
    end
  end.

Lemma windowStep_sound blank lt rt x y :
  windowStep blank x = Some y ->
  windowCfg blank lt rt x -[ tm ]-> windowCfg blank lt rt y.
Proof.
  destruct x as [[[d q] lp] rp]; destruct d, blank; intro H.
  - destruct rp as [|b rest]; cbn [windowStep andb List.tl] in H.
    + destruct (tab (@pair Q Sym q S0)) as [[[w []] q']|] eqn:Htm; inversion H; subst.
      * exact (@step_mEncR_rev tab q q' w (lp ++ lt) [] Htm).
      * exact (@step_mEncR_step tab q q' w (lp ++ lt) [] Htm).
    + destruct (tab (q,b)) as [[[w []] q']|] eqn:Htm; inversion H; subst.
      * exact (step_mEncR_cons_rev Htm).
      * exact (step_mEncR_cons_step Htm).
  - destruct rp as [|b rest]; cbn [windowStep andb List.tl] in H; [discriminate|].
    destruct (tab (q,b)) as [[[w []] q']|] eqn:Htm; inversion H; subst.
    + exact (step_mEncR_cons_rev Htm).
    + exact (step_mEncR_cons_step Htm).
  - destruct lp as [|b rest]; cbn [windowStep andb List.tl] in H; [discriminate|].
    destruct (tab (q,b)) as [[[w []] q']|] eqn:Htm; inversion H; subst.
    + exact (step_mEncL_cons_step Htm).
    + exact (step_mEncL_cons_rev Htm).
  - destruct lp as [|b rest]; cbn [windowStep andb List.tl] in H; [discriminate|].
    destruct (tab (q,b)) as [[[w []] q']|] eqn:Htm; inversion H; subst.
    + exact (step_mEncL_cons_step Htm).
    + exact (step_mEncL_cons_rev Htm).
Qed.

Definition windowEqDec (x y : Window) : {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Fixpoint checkWindow blank fuel x target :=
  match fuel with
  | O => false
  | S fuel' =>
    match windowStep blank x with
    | None => false
    | Some y => if windowEqDec y target then true else checkWindow blank fuel' y target
    end
  end.

Lemma checkWindow_sound blank fuel lt rt x target :
  checkWindow blank fuel x target = true ->
  windowCfg blank lt rt x -[ tm ]->+ windowCfg blank lt rt target.
Proof.
  revert x; induction fuel as [|fuel IH]; intros x; cbn [checkWindow]; [discriminate|].
  destruct (windowStep blank x) as [y|] eqn:Hy; [|discriminate].
  pose proof (windowStep_sound blank lt rt x y Hy) as Hstep.
  destruct (windowEqDec y target) as [->|_]; [now constructor|].
  eauto using progress_step.
Qed.

Lemma reachOpen d q lp rp lt rt d' q' lp' rp' :
  checkWindow false 64%nat (d,q,lp,rp) (d',q',lp',rp') = true ->
  mEncDir d q (lp ++ lt) (rp ++ rt) -[ tm ]->+ mEncDir d' q' (lp' ++ lt) (rp' ++ rt).
Proof. exact (checkWindow_sound false 64%nat lt rt _ _). Qed.

Lemma reachClosed d q lp rs lt d' q' lp' rs' :
  checkWindow true 400%nat (d,q,lp,rs) (d',q',lp',rs') = true ->
  mEncDir d q (lp ++ lt) rs -[ tm ]->+ mEncDir d' q' (lp' ++ lt) rs'.
Proof. exact (checkWindow_sound true 400%nat lt [] _ _). Qed.

End BoundedWindows.

Section Family.
Variable variant : bool.
Local Notation tm := (variant_tm variant).

Local Ltac check_window := destruct variant; vm_compute; reflexivity.

Lemma encTape_of_pop xs b rest :
  popBit xs = (b,rest) -> encTape (b :: rest) = encTape xs.
Proof. intro H; pose proof (encTape_popBit_recons xs) as Ht; now rewrite H in Ht. Qed.

Local Tactic Notation "cut_bit" constr(xs) ident(b) ident(rest) ident(Hp) ident(Ht) :=
  destruct (popBit xs) as [b rest] eqn:Hp;
  pose proof (encTape_of_pop xs b rest Hp) as Ht;
  cbn [fst snd].

Local Ltac expose_tapes :=
  unfold mEncL, mEncR;
  repeat match goal with
  | H : encTape (_ :: _) = encTape ?xs |- context [encTape ?xs] =>
    rewrite <- H; cbn [encTape hd tl]
  end.

Lemma reach_E_one (xs rs : list Sym) :
  mEncL E (S1 :: xs) rs -[ tm ]->+ mEncL E xs (S0 :: rs).
Proof.
  destruct (popBit xs) as [b rest] eqn:Hx.
  pose proof (encTape_of_pop xs b rest Hx) as H.
  enough (Hrun : mEncL E (S1 :: b :: rest) rs -[ tm ]->+ mEncL E (b :: rest) (S0 :: rs)).
  { unfold mEncL in *; cbn [encTape] in H, Hrun; now rewrite H in Hrun. }
  destruct b.
  - apply (reachOpen tm false E [S1;S0] [] rest rs false E [S0] [S0]); check_window.
  - apply (reachOpen tm false E [S1;S1] [] rest rs false E [S1] [S0]); check_window.
Qed.

Lemma reach_E_splitBits (ls rs : list Sym) :
  mEncL E ls rs -[ tm ]->+
  mEncL A (snd (popBit (snd (splitOnesBits ls)))) (S1 :: repZero (fst (splitOnesBits ls)) rs).
Proof.
  revert rs.
  induction ls as [| a xs IH]; intros rs.
  - cbn [splitOnesBits fst snd popBit]. rewrite repZero_0.
    apply progress_base; eapply step_mEncL_nil_step; reflexivity.
  - destruct a.
    + cbn [splitOnesBits fst snd popBit]. rewrite repZero_0.
      apply progress_base; eapply step_mEncL_cons_step; reflexivity.
    + cbn [splitOnesBits fst snd].
      eapply progress_trans; [exact (reach_E_one xs rs) |].
      pose proof (IH (S0 :: rs)) as Hrest.
      rewrite repZero_snoc in Hrest.
      exact Hrest.
Qed.

Lemma reach_AL_pair10 (ls rs : list Sym) :
  mEncL A (S1 :: S0 :: ls) rs -[ tm ]->+ mEncL A ls (S1 :: S0 :: rs).
Proof.
  apply (reachOpen tm false A [S1; S0] [] ls rs false A [] [S1; S0]); check_window.
Qed.

Lemma reach_AL_single1 (rs : list Sym) :
  mEncL A [S1] rs -[ tm ]->+ mEncL A [] (S1 :: S0 :: rs).
Proof.
  eapply progress_step; [eapply step_mEncL_cons_step; reflexivity |].
  eapply progress_step; [eapply step_mEncL_nil_rev; reflexivity |].
  eapply progress_step; [eapply step_mEncR_cons_rev; reflexivity |].
  apply progress_base; eapply step_mEncL_cons_step; reflexivity.
Qed.

Lemma reach_AL_repAB (n : N) :
  forall (ls rs : list Sym),
    mEncL A (repAB n ls) rs -[ tm ]->* mEncL A ls (repAB n rs).
Proof.
  induction n as [| n IH] using N.peano_ind; intros ls rs.
  - rewrite !repAB_0. apply evstep_refl.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite repAB_succ.
    eapply evstep_trans; [exact (progress_evstep _ _ _ (reach_AL_pair10 (repAB n ls) rs)) |].
    pose proof (IH ls (S1 :: S0 :: rs)) as H2.
    rewrite repAB_snoc in H2. exact H2.
Qed.

Lemma reach_sweepAL_len :
  forall (bound : nat) (ls : list LTok) (rs : list RTok),
    (List.length ls <= bound)%nat ->
    mEncL A (decL ls) (decR rs) -[ tm ]->*
    mEncL A (decL (fst (sweepAL ls rs))) (decR (snd (sweepAL ls rs))).
Proof.
  induction bound as [| bound IH]; intros ls rs Hlen.
  - destruct ls; [apply evstep_refl | cbn [List.length] in Hlen; lia].
  - destruct ls as [| [k | k | k | k] rest]; cbn [sweepAL].
    + apply evstep_refl.
    + apply evstep_refl.
    + destruct (N.eqb k 0) eqn:Hk0; [| apply evstep_refl].
      apply N.eqb_eq in Hk0; subst k.
      destruct rest as [| [zk | ok | pk | ak] rest2].
      * cbn [fst snd decL]. rewrite repOne_succ, repOne_0, decR_push10RepeatR.
        exact (progress_evstep _ _ _ (reach_AL_single1 (decR rs))).
      * destruct (N.eqb zk 0) eqn:Hzk0.
        -- apply N.eqb_eq in Hzk0; subst zk.
           cbn [decL]. rewrite repOne_succ, repOne_0, repZero_succ, repZero_0.
           eapply evstep_trans.
           ++ pose proof (progress_evstep _ _ _ (reach_AL_pair10 (decL rest2) (decR rs))) as H1.
              change (S1 :: S0 :: decR rs) with (repAB (0 + 1) (decR rs)) in H1.
              rewrite <- (decR_push10RepeatR 0 rs) in H1. exact H1.
           ++ apply IH. cbn [List.length] in Hlen. lia.
        -- apply N.eqb_neq in Hzk0.
           cbn [fst snd decL].
           replace (zk + 1) with ((zk - 1 + 1) + 1) by lia.
           rewrite (repOne_succ 0), repOne_0, (repZero_succ (zk - 1 + 1)), decR_push10RepeatR.
           exact (progress_evstep _ _ _ (reach_AL_pair10 (repZero (zk - 1 + 1) (decL rest2)) (decR rs))).
      * apply evstep_refl.
      * destruct (N.eqb pk 0) eqn:Hpk0.
        -- apply N.eqb_eq in Hpk0; subst pk.
           cbn [fst snd decL]. rewrite decL_pushOL, decR_push10RepeatR.
           exact (progress_evstep _ _ _ (reach_AL_pair10 (S1 :: S1 :: decL rest2) (decR rs))).
        -- apply N.eqb_neq in Hpk0.
           cbn [fst snd decL].
           replace (pk + 1) with ((pk - 1 + 1) + 1) by lia.
           rewrite (repP_succ (pk - 1 + 1)), decR_push10RepeatR.
           exact (progress_evstep _ _ _ (reach_AL_pair10 (S1 :: S1 :: repP (pk - 1 + 1) (decL rest2)) (decR rs))).
      * apply evstep_refl.
    + apply evstep_refl.
    + cbn [decL].
      eapply evstep_trans.
      * pose proof (reach_AL_repAB (k + 1) (decL rest) (decR rs)) as H1.
        rewrite <- (decR_push10RepeatR k rs) in H1. exact H1.
      * apply IH. cbn [List.length] in Hlen. lia.
Qed.

Lemma reach_sweepAL (ls : list LTok) (rs : list RTok) :
  mEncL A (decL ls) (decR rs) -[ tm ]->*
  mEncL A (decL (fst (sweepAL ls rs))) (decR (snd (sweepAL ls rs))).
Proof.
  exact (reach_sweepAL_len (List.length ls) ls rs (le_n _)).
Qed.

Lemma reach_AL_crossP_step (lt rs : list Sym) :
  mEncL A (S1 :: S1 :: S0 :: S1 :: S1 :: lt) rs -[ tm ]->+
  mEncL A (S1 :: S1 :: lt) (S1 :: S0 :: S0 :: rs).
Proof.
  apply (reachOpen tm false A [S1; S1; S0; S1; S1] [] lt rs false A [S1; S1] [S1; S0; S0]); check_window.
Qed.

Lemma reach_AL_crossP_star (n : N) :
  forall (lt rs : list Sym),
    mEncL A (S1 :: S1 :: repP n lt) rs -[ tm ]->* mEncL A (S1 :: S1 :: lt) (rep100 n rs).
Proof.
  induction n as [| n IH] using N.peano_ind; intros lt rs.
  - rewrite repP_0, rep100_0. apply evstep_refl.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite repP_succ.
    eapply evstep_trans; [exact (progress_evstep _ _ _ (reach_AL_crossP_step (repP n lt) rs)) |].
    pose proof (IH lt (S1 :: S0 :: S0 :: rs)) as H2.
    rewrite rep100_snoc in H2. exact H2.
Qed.

Lemma reach_AL_crossP_plus (k : N) (lt rs : list Sym) :
  mEncL A (S1 :: S1 :: repP (k + 1) lt) rs -[ tm ]->+ mEncL A (S1 :: S1 :: lt) (rep100 (k + 1) rs).
Proof.
  rewrite repP_succ.
  eapply progress_evstep_trans; [exact (reach_AL_crossP_step (repP k lt) rs) |].
  pose proof (reach_AL_crossP_star k lt (S1 :: S0 :: S0 :: rs)) as H2.
  rewrite rep100_snoc in H2. exact H2.
Qed.

Lemma reach_AL01_step (b : Sym) (lt rs : list Sym) :
  mEncL A (S0 :: lt) (S1 :: S0 :: b :: rs) -[ tm ]->+ mEncR D (b :: S0 :: S1 :: S1 :: lt) rs.
Proof.
  destruct b.
  - apply (reachOpen tm false A [S0] [S1; S0; S0] lt rs true D [S0; S0; S1; S1] []); check_window.
  - apply (reachOpen tm false A [S0] [S1; S0; S1] lt rs true D [S1; S0; S1; S1] []); check_window.
Qed.

Lemma reach_DR01_step (ls rs : list Sym) :
  mEncR D ls (S0 :: S1 :: rs) -[ tm ]->+ mEncL A ls (S1 :: S0 :: rs).
Proof.
  apply (reachOpen tm true D [] [S0; S1] ls rs false A [] [S1; S0]); check_window.
Qed.

Lemma reach_AL_shuttleQ_one (lt rs : list Sym) :
  mEncL A (S0 :: lt) (S1 :: S0 :: S0 :: S0 :: S1 :: rs) -[ tm ]->+
  mEncL A (S0 :: S0 :: S1 :: S1 :: lt) (S1 :: S0 :: rs).
Proof.
  eapply progress_trans; [exact (reach_AL01_step S0 lt (S0 :: S1 :: rs)) |].
  exact (reach_DR01_step (S0 :: S0 :: S1 :: S1 :: lt) rs).
Qed.

Lemma reach_AL_shuttleQ_star (n : N) :
  forall (lt rs : list Sym),
    mEncL A (S0 :: lt) (S1 :: S0 :: repQ n rs) -[ tm ]->*
    mEncL A (S0 :: repP n lt) (S1 :: S0 :: rs).
Proof.
  induction n as [| n IH] using N.peano_ind; intros lt rs.
  - rewrite repQ_0, repP_0. apply evstep_refl.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite repQ_succ.
    eapply evstep_trans; [exact (progress_evstep _ _ _ (reach_AL_shuttleQ_one lt (repQ n rs))) |].
    pose proof (IH (S0 :: S1 :: S1 :: lt) rs) as H2.
    rewrite repP_snoc in H2. exact H2.
Qed.

Lemma reach_AL_shuttleQ_plus (k : N) (lt rs : list Sym) :
  mEncL A (S0 :: lt) (S1 :: S0 :: repQ (k + 1) rs) -[ tm ]->+
  mEncL A (S0 :: repP (k + 1) lt) (S1 :: S0 :: rs).
Proof.
  rewrite repQ_succ.
  eapply progress_evstep_trans; [exact (reach_AL_shuttleQ_one lt (repQ k rs)) |].
  pose proof (reach_AL_shuttleQ_star k (S0 :: S1 :: S1 :: lt) rs) as H2.
  rewrite repP_snoc in H2. exact H2.
Qed.

Lemma reach_AL_shuttleBA_one (lt rs : list Sym) :
  mEncL A (S0 :: lt) (S1 :: S0 :: S0 :: S1 :: rs) -[ tm ]->+
  mEncL A (S0 :: S1 :: S1 :: lt) (S1 :: S0 :: rs).
Proof.
  apply (reachOpen tm false A [S0] [S1; S0; S0; S1] lt rs false A [S0; S1; S1] [S1; S0]); check_window.
Qed.

Lemma reach_AL_shuttleBA_star (n : N) :
  forall (lt rs : list Sym),
    mEncL A (S0 :: lt) (S1 :: S0 :: repBA n rs) -[ tm ]->*
    mEncL A (S0 :: repOne (2 * n) lt) (S1 :: S0 :: rs).
Proof.
  induction n as [| n IH] using N.peano_ind; intros lt rs.
  - rewrite repBA_0, repOne_0. apply evstep_refl.
  - replace (N.succ n) with (n + 1) by lia.
    rewrite repBA_succ.
    eapply evstep_trans; [exact (progress_evstep _ _ _ (reach_AL_shuttleBA_one lt (repBA n rs))) |].
    pose proof (IH (S1 :: S1 :: lt) rs) as H2.
    rewrite repOne_snoc2 in H2. exact H2.
Qed.

Lemma reach_AL_shuttleBA_plus (k : N) (lt rs : list Sym) :
  mEncL A (S0 :: lt) (S1 :: S0 :: repBA (k + 1) rs) -[ tm ]->+
  mEncL A (S0 :: repOne (2 * (k + 1)) lt) (S1 :: S0 :: rs).
Proof.
  rewrite repBA_succ.
  eapply progress_evstep_trans; [exact (reach_AL_shuttleBA_one lt (repBA k rs)) |].
  pose proof (reach_AL_shuttleBA_star k (S1 :: S1 :: lt) rs) as H2.
  rewrite repOne_snoc2 in H2. exact H2.
Qed.

Lemma reach_DR_crossQ_zero (lt rs : list Sym) :
  mEncR D (S0 :: lt) (repQ 2 rs) -[ tm ]->+
  mEncL A (S0 :: S1 :: S1 :: S0 :: S0 :: lt) (S1 :: S0 :: rs).
Proof.
  apply (reachOpen tm true D [S0] [S0; S0; S1; S0; S0; S1] lt rs
           false A [S0; S1; S1; S0; S0] [S1; S0]); check_window.
Qed.

Lemma reach_DR_crossQ (u : N) (lt rs : list Sym) :
  mEncR D (S0 :: lt) (repQ (u + 2) rs) -[ tm ]->+
  mEncL A (S0 :: repP u (S1 :: S1 :: S0 :: S0 :: lt)) (S1 :: S0 :: rs).
Proof.
  replace (u + 2) with (2 + u) by lia.
  rewrite repQ_add.
  eapply progress_evstep_trans; [exact (reach_DR_crossQ_zero lt (repQ u rs)) |].
  exact (reach_AL_shuttleQ_star u (S1 :: S1 :: S0 :: S0 :: lt) rs).
Qed.

Definition inCfg (p : N) (lt rs : list Sym) : Q * tape :=
  mEncL A (S0 :: repP p lt) (S1 :: S0 :: rs).

Definition outCfg (qp : N) (lt rs' : list Sym) : Q * tape :=
  mEncL A (S1 :: S1 :: repP qp lt) (S1 :: rs').

Lemma reach_top_exit (qp : N) (lt rs' : list Sym) :
  outCfg qp (S1 :: S1 :: S0 :: S0 :: lt) rs' -[ tm ]->+
  mEncR D (S0 :: S0 :: S1 :: S1 :: lt) (repQ (qp + 1) rs').
Proof.
  unfold outCfg.
  eapply evstep_progress_trans;
    [exact (reach_AL_crossP_star qp (S1 :: S1 :: S0 :: S0 :: lt) (S1 :: rs')) |].
  rewrite rep100_one, repQ_succ.
  apply (reachOpen tm false A [S1; S1; S1; S1; S0; S0] [S1] lt (repQ qp rs')
           true D [S0; S0; S1; S1] [S0; S0; S1]); check_window.
Qed.

Lemma reach_top_pass {p qp : N} {lt rs rs' : list Sym}
  (H : inCfg p (S1 :: S1 :: S0 :: S0 :: lt) rs -[ tm ]->+
       outCfg qp (S1 :: S1 :: S0 :: S0 :: lt) rs') :
  mEncR D (S0 :: lt) (repQ (p + 2) rs) -[ tm ]->+
  mEncR D (S0 :: repP 1 lt) (repQ (qp + 1) rs').
Proof.
  eapply progress_trans; [exact (reach_DR_crossQ p lt rs) |].
  eapply progress_trans; [exact H |].
  exact (reach_top_exit qp lt rs').
Qed.

Lemma reach_Z2_leaf (p : N) (lt rs : list Sym) :
  inCfg p lt (S0 :: S0 :: S0 :: S0 :: S1 :: rs) -[ tm ]->+
  outCfg (p + 1) lt (S0 :: S0 :: rs).
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachOpen tm false A [S0] [S1; S0; S0; S0; S0; S0; S1] (repP p lt) rs
           false A [S1; S1; S0; S1; S1] [S1; S0; S0]); check_window.
Qed.

Lemma reach_DR_oneShuttleZ2 (u : N) (lt rs : list Sym) :
  mEncR D (S0 :: lt) (repQ (u + 2) (S0 :: S0 :: S0 :: S0 :: S1 :: rs)) -[ tm ]->+
  mEncR D (S0 :: S0 :: S1 :: S1 :: lt) (repQ (u + 2) (S0 :: S0 :: rs)).
Proof.
  replace (u + 2) with ((u + 1) + 1) at 2 by lia.
  exact (reach_top_pass (reach_Z2_leaf u (S1 :: S1 :: S0 :: S0 :: lt) rs)).
Qed.

Lemma reach_DR_multiShuttleZ2_plus (v u : N) :
  forall (lt rs : list Sym),
    mEncR D (S0 :: lt) (repQ (u + 2) (S0 :: S0 :: repQ (v + 1) rs)) -[ tm ]->+
    mEncR D (S0 :: repP (v + 1) lt) (repQ (u + 2) (S0 :: S0 :: rs)).
Proof.
  induction v as [| v IH] using N.peano_ind; intros lt rs.
  - rewrite repQ_succ, repQ_0, repP_succ, repP_0.
    exact (reach_DR_oneShuttleZ2 u lt rs).
  - replace (N.succ v) with (v + 1) by lia.
    rewrite (repQ_succ (v + 1)).
    eapply progress_trans; [exact (reach_DR_oneShuttleZ2 u lt (repQ (v + 1) rs)) |].
    pose proof (IH (S0 :: S1 :: S1 :: lt) rs) as H2.
    rewrite repP_snoc in H2. exact H2.
Qed.

(** *** Soundness of [stepBaseK] *)

Lemma reach_AL_zero_branch (ls rs : list Sym) (Hl0 : fst (popBit ls) = S0) :
  let lt := snd (popBit ls) in
  let r0 := popBit rs in
  match fst r0 with
  | S1 =>
    let r1 := popBit (snd r0) in
    match fst r1 with
    | S1 => True
    | S0 =>
      let r2 := popBit (snd r1) in
      mEncL A ls rs -[ tm ]->+ mEncR D (fst r2 :: S0 :: S1 :: S1 :: lt) (snd r2)
    end
  | S0 =>
    let l1 := popBit lt in
    match fst l1 with
    | S0 =>
      mEncL A ls rs -[ tm ]->+ mEncL A (snd l1) (S1 :: S0 :: S1 :: snd r0)
    | S1 =>
      let sp := splitOnesBits (snd l1) in
      mEncL A ls rs -[ tm ]->+
      mEncL A (snd (popBit (snd sp))) (S1 :: repZero (fst sp + 2) (S1 :: snd r0))
    end
  end.
Proof.
  cbn zeta.
  cut_bit ls a lt Hl El. cbn [fst] in Hl0; subst a.
  cut_bit rs b rt Hr Er. destruct b.
  - cut_bit lt b ll Hl' El'. destruct b.
    + expose_tapes.
      apply (reachOpen tm false A [S0;S0] [S0] ll rt false A [] [S1;S0;S1]); check_window.
    + assert (H : mEncL A ls rs -[ tm ]->+ mEncL E ll (S0 :: S0 :: S1 :: rt)).
      { cut_bit ll b lll Hl'' El''. destruct b; expose_tapes.
        - apply (reachOpen tm false A [S0;S1;S0] [S0] lll rt false E [S0] [S0;S0;S1]); check_window.
        - apply (reachOpen tm false A [S0;S1;S1] [S0] lll rt false E [S1] [S0;S0;S1]); check_window. }
      eapply progress_trans; [exact H|].
      pose proof (reach_E_splitBits ll (S0 :: S0 :: S1 :: rt)) as Hs.
      rewrite !repZero_snoc in Hs.
      replace (fst (splitOnesBits ll) + 1 + 1) with (fst (splitOnesBits ll) + 2) in Hs by lia.
      exact Hs.
  - cut_bit rt b rr Hr' Er'. destruct b; [|exact I].
    cut_bit rr b rrr Hr'' Er''. destruct b; expose_tapes.
    + apply (reachOpen tm false A [S0] [S1;S0;S0] lt rrr true D [S0;S0;S1;S1] []); check_window.
    + apply (reachOpen tm false A [S0] [S1;S0;S1] lt rrr true D [S1;S0;S1;S1] []); check_window.
Qed.

Lemma stepALZeroCore_sound (ls : list LTok) (rs : list RTok)
  (Hl0 : fst (popBit (decL ls)) = S0) (b' : BaseState) :
  stepALZeroFallback ls rs = Some b' ->
  mEncL A (decL ls) (decR rs) -[ tm ]->+ encodeBase b'.
Proof.
  intro H.
  pose proof (reach_AL_zero_branch (decL ls) (decR rs) Hl0) as Hbit; cbn zeta in Hbit.
  destruct (decL_popL ls) as [_ Hpl2].
  destruct (decR_popR rs) as [Hpr0_1 Hpr0_2].
  unfold stepALZeroFallback in H.
  destruct (fst (popR rs)) eqn:Hr0.
  - cbn [bitOfBool] in Hpr0_1. rewrite <- Hpr0_1 in Hbit.
    destruct (decR_popR (snd (popR rs))) as [Hpr1_1 Hpr1_2].
    rewrite Hpr0_2 in Hpr1_1, Hpr1_2.
    destruct (fst (popR (snd (popR rs)))) eqn:Hr1; [discriminate |].
    cbn [bitOfBool] in Hpr1_1. rewrite <- Hpr1_1 in Hbit.
    destruct (decR_popR (snd (popR (snd (popR rs))))) as [Hpr2_1 Hpr2_2].
    rewrite Hpr1_2 in Hpr2_1, Hpr2_2.
    destruct (fst (popR (snd (popR (snd (popR rs)))))) eqn:Hr2.
    + inversion H; subst b'; clear H.
      cbn [bitOfBool] in Hpr2_1. rewrite <- Hpr2_1 in Hbit.
      unfold encodeBase; cbn [mode l r].
      rewrite decL_pushOneL, decL_pushZeroL, decL_pushOL, Hpl2, Hpr2_2.
      exact Hbit.
    + inversion H; subst b'; clear H.
      cbn [bitOfBool] in Hpr2_1. rewrite <- Hpr2_1 in Hbit.
      unfold encodeBase; cbn [mode l r].
      rewrite !decL_pushZeroL, decL_pushOL, Hpl2, Hpr2_2.
      exact Hbit.
  - cbn [bitOfBool] in Hpr0_1. rewrite <- Hpr0_1 in Hbit.
    destruct (decL_popL (snd (popL ls))) as [Hpl1_1 Hpl1_2].
    rewrite Hpl2 in Hpl1_1, Hpl1_2.
    destruct (fst (popL (snd (popL ls)))) eqn:Hl1.
    + inversion H; subst b'; clear H.
      cbn [bitOfBool] in Hpl1_1. rewrite <- Hpl1_1 in Hbit.
      destruct (splitLeadingOnesL_sound (snd (popL (snd (popL ls))))) as [Hsp1 Hsp2].
      rewrite Hpl1_2 in Hsp1, Hsp2.
      destruct (decL_popL (snd (splitLeadingOnesL (snd (popL (snd (popL ls))))))) as [_ Hpl3_2].
      rewrite Hsp2 in Hpl3_2.
      unfold encodeBase; cbn [mode l r].
      rewrite Hpl3_2, decR_pushOneR, decR_pushZerosAtLeast2R, decR_pushOneR, Hsp1, Hpr0_2.
      exact Hbit.
    + inversion H; subst b'; clear H.
      cbn [bitOfBool] in Hpl1_1. rewrite <- Hpl1_1 in Hbit.
      unfold encodeBase; cbn [mode l r].
      rewrite Hpl1_2, decR_pushOneR, decR_pushZeroR, decR_pushOneR, Hpr0_2.
      exact Hbit.
Qed.

Lemma reach_DR_fallback (ls rs : list Sym) :
  let r0 := popBit rs in
  match fst r0 with
  | S1 =>
    let sp := splitOnesBits ls in
    mEncR D ls rs -[ tm ]->+
    mEncL A (snd (popBit (snd sp))) (S1 :: repZero (fst sp + 1) (snd r0))
  | S0 =>
    let r1 := popBit (snd r0) in
    match fst r1 with
    | S1 =>
      mEncR D ls rs -[ tm ]->+ mEncL A ls (S1 :: S0 :: snd r1)
    | S0 =>
      let r2 := popBit (snd r1) in
      match fst r2 with
      | S0 =>
        mEncR D ls rs -[ tm ]->+ mEncL A ls (S1 :: S0 :: S1 :: snd r2)
      | S1 =>
        let r3 := popBit (snd r2) in
        match fst r3 with
        | S1 => True
        | S0 =>
          let r4 := popBit (snd r3) in
          mEncR D ls rs -[ tm ]->+ mEncR D (fst r4 :: S0 :: S1 :: S1 :: S0 :: ls) (snd r4)
        end
      end
    end
  end.
Proof.
  cbn zeta.
  cut_bit rs b rt Hr Er. destruct b.
  - cut_bit rt b r2 Hr2 Er2. destruct b.
    + cut_bit r2 b r3 Hr3 Er3. destruct b.
      * expose_tapes.
        apply (reachOpen tm true D [] [S0;S0;S0] ls r3 false A [] [S1;S0;S1]); check_window.
      * cut_bit r3 b r4 Hr4 Er4. destruct b; [|exact I].
        cut_bit r4 b r5 Hr5 Er5. destruct b; expose_tapes.
        -- apply (reachOpen tm true D [] [S0;S0;S1;S0;S0] ls r5 true D [S0;S0;S1;S1;S0] []); check_window.
        -- apply (reachOpen tm true D [] [S0;S0;S1;S0;S1] ls r5 true D [S1;S0;S1;S1;S0] []); check_window.
    + expose_tapes.
      apply (reachOpen tm true D [] [S0;S1] ls r2 false A [] [S1;S0]); check_window.
  - eapply (@progress_step _ _ (mEncL E ls (S0 :: rt)) _).
    + expose_tapes. eapply step_mEncR_cons_rev; reflexivity.
    + pose proof (reach_E_splitBits ls (S0 :: rt)) as Hs.
      rewrite repZero_snoc in Hs. exact Hs.
Qed.

Lemma stepDRFallback_sound (ls : list LTok) (rs : list RTok) (b' : BaseState) :
  stepDRFallback ls rs = Some b' ->
  mEncR D (decL ls) (decR rs) -[ tm ]->+ encodeBase b'.
Proof.
  intro H.
  pose proof (reach_DR_fallback (decL ls) (decR rs)) as Hbit; cbn zeta in Hbit.
  destruct (decR_popR rs) as [Hpr0_1 Hpr0_2].
  unfold stepDRFallback in H.
  destruct (fst (popR rs)) eqn:Hr0.
  - inversion H; subst b'; clear H.
    cbn [bitOfBool] in Hpr0_1. rewrite <- Hpr0_1 in Hbit.
    destruct (splitLeadingOnesL_sound ls) as [Hsp1 Hsp2].
    destruct (decL_popL (snd (splitLeadingOnesL ls))) as [_ Hpl2_2].
    rewrite Hsp2 in Hpl2_2.
    unfold encodeBase; cbn [mode l r].
    rewrite Hpl2_2, decR_pushOneR, decR_pushZerosAtLeast1R, Hsp1, Hpr0_2.
    exact Hbit.
  - cbn [bitOfBool] in Hpr0_1. rewrite <- Hpr0_1 in Hbit.
    destruct (decR_popR (snd (popR rs))) as [Hpr1_1 Hpr1_2].
    rewrite Hpr0_2 in Hpr1_1, Hpr1_2.
    destruct (fst (popR (snd (popR rs)))) eqn:Hr1.
    + inversion H; subst b'; clear H.
      cbn [bitOfBool] in Hpr1_1. rewrite <- Hpr1_1 in Hbit.
      unfold encodeBase; cbn [mode l r].
      rewrite decR_pushOneR, decR_pushZeroR, Hpr1_2.
      exact Hbit.
    + cbn [bitOfBool] in Hpr1_1. rewrite <- Hpr1_1 in Hbit.
      destruct (decR_popR (snd (popR (snd (popR rs))))) as [Hpr2_1 Hpr2_2].
      rewrite Hpr1_2 in Hpr2_1, Hpr2_2.
      destruct (fst (popR (snd (popR (snd (popR rs)))))) eqn:Hr2; cbn [negb] in H.
      * cbn [bitOfBool] in Hpr2_1. rewrite <- Hpr2_1 in Hbit.
        destruct (decR_popR (snd (popR (snd (popR (snd (popR rs))))))) as [Hpr3_1 Hpr3_2].
        rewrite Hpr2_2 in Hpr3_1, Hpr3_2.
        destruct (fst (popR (snd (popR (snd (popR (snd (popR rs)))))))) eqn:Hr3; [discriminate |].
        cbn [bitOfBool] in Hpr3_1. rewrite <- Hpr3_1 in Hbit.
        destruct (decR_popR (snd (popR (snd (popR (snd (popR (snd (popR rs))))))))) as [Hpr4_1 Hpr4_2].
        rewrite Hpr3_2 in Hpr4_1, Hpr4_2.
        destruct (fst (popR (snd (popR (snd (popR (snd (popR (snd (popR rs)))))))))) eqn:Hr4;
          inversion H; subst b'; clear H;
          cbn [bitOfBool] in Hpr4_1; rewrite <- Hpr4_1 in Hbit;
          unfold encodeBase; cbn [mode l r];
          rewrite ?decL_pushOneL, !decL_pushZeroL, decL_pushOL, decL_pushZeroL, Hpr4_2;
          exact Hbit.
      * inversion H; subst b'; clear H.
        cbn [bitOfBool] in Hpr2_1. rewrite <- Hpr2_1 in Hbit.
        unfold encodeBase; cbn [mode l r].
        rewrite decR_pushOneR, decR_pushZeroR, decR_pushOneR, Hpr2_2.
        exact Hbit.
Qed.

Lemma mEncL_zero_head_expand (q : Q) (ls : list LTok) (rs : list Sym)
  (H0 : fst (popBit (decL ls)) = S0) :
  mEncL q (decL ls) rs = mEncL q (S0 :: snd (popBit (decL ls))) rs.
Proof.
  pose proof (encTape_popBit_recons (decL ls)) as Hrec.
  rewrite H0 in Hrec. unfold mEncL. rewrite <- Hrec. reflexivity.
Qed.

Lemma mEncR_zero_head_expand (q : Q) (ls : list LTok) (rs : list Sym)
  (H0 : fst (popBit (decL ls)) = S0) :
  mEncR q (decL ls) rs = mEncR q (S0 :: snd (popBit (decL ls))) rs.
Proof.
  pose proof (encTape_popBit_recons (decL ls)) as Hrec.
  rewrite H0 in Hrec. unfold mEncR. rewrite <- Hrec. reflexivity.
Qed.

Lemma stepALElse_sound (ls : list LTok) (rs : list RTok) (b' : BaseState) :
  stepALElse ls rs = Some b' ->
  mEncL A (decL ls) (decR rs) -[ tm ]->+ encodeBase b'.
Proof.
  intro H. unfold stepALElse in H.
  destruct (isZeroHeadL ls) eqn:Hz.
  - pose proof (isZeroHeadL_sound ls Hz) as Hl0.
    destruct (decL_popL ls) as [_ Hpl2].
    destruct rs as [| [k1 | ok | k1 | k1] [| [zk | k2 | qk | k2] [| rt3 rrest]]];
      try exact (stepALZeroCore_sound ls _ Hl0 b' H).
    + destruct rt3 as [k3 | k3 | q3 | k3];
        try exact (stepALZeroCore_sound ls _ Hl0 b' H).
      destruct (N.eqb ok 0) eqn:Hok; [| exact (stepALZeroCore_sound ls _ Hl0 b' H)].
      destruct (N.eqb zk 0) eqn:Hzk; [| exact (stepALZeroCore_sound ls _ Hl0 b' H)].
      apply N.eqb_eq in Hok; apply N.eqb_eq in Hzk; subst ok zk.
      inversion H; subst b'; clear H.
      rewrite (mEncL_zero_head_expand A ls _ Hl0), <- Hpl2.
      unfold encodeBase; cbn [mode l r decR].
      rewrite decL_pushZeroL, decL_pushPL, decR_pushOneR, decR_pushZeroR.
      exact (reach_AL_shuttleQ_plus q3 (decL (snd (popL ls))) (decR rrest)).
    + destruct rt3 as [k3 | k3 | k3 | b3];
        try exact (stepALZeroCore_sound ls _ Hl0 b' H).
      destruct (N.eqb ok 0) eqn:Hok; [| exact (stepALZeroCore_sound ls _ Hl0 b' H)].
      destruct (N.eqb qk 0) eqn:Hqk; [| exact (stepALZeroCore_sound ls _ Hl0 b' H)].
      apply N.eqb_eq in Hok; apply N.eqb_eq in Hqk; subst ok qk.
      inversion H; subst b'; clear H.
      rewrite (mEncL_zero_head_expand A ls _ Hl0), <- Hpl2.
      unfold encodeBase; cbn [mode l r decR].
      rewrite decL_pushZeroL, decL_pushOL, decR_pushOneR, decR_pushZeroR.
      pose proof (reach_AL_shuttleBA_plus (b3 + 1) (decL (snd (popL ls))) (decR rrest)) as Hsh.
      replace (2 * (b3 + 1 + 1)) with ((2 * b3 + 3) + 1) in Hsh by lia.
      rewrite (repBA_succ (b3 + 1)) in Hsh.
      exact Hsh.
  - pose proof (reach_sweepAL ls rs) as Hsw.
    set (swL := fst (sweepAL ls rs)) in *.
    set (swR := snd (sweepAL ls rs)) in *.
    destruct (decL_popL swL) as [Hpl0_1 Hpl0_2].
    destruct (fst (popL swL)) eqn:Hl0.
    + cbn [bitOfBool] in Hpl0_1. symmetry in Hpl0_1.
      destruct (decL_popL (snd (popL swL))) as [Hpl1_1 Hpl1_2].
      rewrite Hpl0_2 in Hpl1_1, Hpl1_2.
      destruct (fst (popL (snd (popL swL)))) eqn:Hl1.
      * inversion H; subst b'; clear H.
        cbn [bitOfBool] in Hpl1_1. symmetry in Hpl1_1.
        destruct (splitLeadingOnesL_sound (snd (popL (snd (popL swL))))) as [Hsp1 Hsp2].
        rewrite Hpl1_2 in Hsp1, Hsp2.
        destruct (decL_popL (snd (splitLeadingOnesL (snd (popL (snd (popL swL))))))) as [_ Hpl3_2].
        rewrite Hsp2 in Hpl3_2.
        eapply evstep_progress_trans; [exact Hsw |].
        assert (HA1 : mEncL A (decL swL) (decR swR) -[ tm ]->
                      mEncL C (snd (popBit (decL swL))) (S1 :: decR swR)).
        { apply step_mEncL_step. rewrite Hpl0_1. reflexivity. }
        assert (HC1 : mEncL C (snd (popBit (decL swL))) (S1 :: decR swR) -[ tm ]->
                      mEncR D (S1 :: snd (popBit (snd (popBit (decL swL))))) (S1 :: decR swR)).
        { apply step_mEncL_rev. rewrite Hpl1_1. reflexivity. }
        eapply progress_step; [exact HA1 |].
        eapply progress_step; [exact HC1 |].
        eapply progress_step; [eapply step_mEncR_cons_rev; reflexivity |].
        eapply progress_trans; [exact (reach_E_one (snd (popBit (snd (popBit (decL swL))))) (S0 :: decR swR)) |].
        pose proof (reach_E_splitBits (snd (popBit (snd (popBit (decL swL))))) (S0 :: S0 :: decR swR)) as Hsp.
        rewrite !repZero_snoc in Hsp.
        replace (fst (splitOnesBits (snd (popBit (snd (popBit (decL swL)))))) + 1 + 1)
          with (fst (splitOnesBits (snd (popBit (snd (popBit (decL swL)))))) + 2) in Hsp by lia.
        unfold encodeBase; cbn [mode l r].
        rewrite Hpl3_2, decR_pushOneR, decR_pushZerosAtLeast2R, Hsp1.
        exact Hsp.
      * inversion H; subst b'; clear H.
        cbn [bitOfBool] in Hpl1_1. symmetry in Hpl1_1.
        eapply evstep_progress_trans; [exact Hsw |].
        assert (HA1 : mEncL A (decL swL) (decR swR) -[ tm ]->
                      mEncL C (snd (popBit (decL swL))) (S1 :: decR swR)).
        { apply step_mEncL_step. rewrite Hpl0_1. reflexivity. }
        assert (HC0 : mEncL C (snd (popBit (decL swL))) (S1 :: decR swR) -[ tm ]->
                      mEncR D (S0 :: snd (popBit (snd (popBit (decL swL))))) (S1 :: decR swR)).
        { apply step_mEncL_rev. rewrite Hpl1_1. reflexivity. }
        eapply progress_step; [exact HA1 |].
        eapply progress_step; [exact HC0 |].
        eapply progress_step; [eapply step_mEncR_cons_rev; reflexivity |].
        unfold encodeBase; cbn [mode l r].
        rewrite Hpl1_2, decR_push10RepeatR.
        apply progress_base; eapply step_mEncL_cons_step; reflexivity.
    + cbn [bitOfBool] in Hpl0_1. symmetry in Hpl0_1.
      eapply evstep_progress_trans; [exact Hsw |].
      apply (stepALZeroCore_sound swL swR Hpl0_1 b').
      unfold stepALZeroFallback. exact H.
Qed.

Lemma stepDRBase_sound (ls : list LTok) (rs : list RTok) (b' : BaseState) :
  stepDRBase ls rs = Some b' ->
  mEncR D (decL ls) (decR rs) -[ tm ]->+ encodeBase b'.
Proof.
  intro H. unfold stepDRBase in H.
  destruct (isZeroHeadL ls) eqn:Hz; [| exact (stepDRFallback_sound ls rs b' H)].
  pose proof (isZeroHeadL_sound ls Hz) as Hl0.
  destruct (decL_popL ls) as [_ Hpl2].
  destruct rs as [| [k1 | k1 | qk | k1] rtail];
    try exact (stepDRFallback_sound ls _ b' H).
  destruct (N.eqb qk 0) eqn:Hqk0; [exact (stepDRFallback_sound ls _ b' H) |].
  apply N.eqb_neq in Hqk0.
  assert (Hcross : forall rtail' : list RTok,
    (if N.eqb qk 1 then
       Some (mkBase mAL (pushPL 0 (pushZeroL (pushZeroL (snd (popL ls))))) (pushOneR (pushZeroR rtail')))
     else
       Some (mkBase mAL (pushZeroL (pushPL (qk - 2) (pushOL 1 (pushZeroL (pushZeroL (snd (popL ls))))))) (pushOneR (pushZeroR rtail'))))
    = Some b' ->
    mEncR D (decL ls) (decR (R_q qk :: rtail')) -[ tm ]->+ encodeBase b').
  { intros rtail' Hm.
    destruct (N.eqb qk 1) eqn:Hqk1.
    - apply N.eqb_eq in Hqk1; subst qk.
      inversion Hm; subst b'; clear Hm.
      rewrite (mEncR_zero_head_expand D ls _ Hl0), <- Hpl2.
      unfold encodeBase; cbn [mode l r decR].
      rewrite decL_pushPL, !decL_pushZeroL, decR_pushOneR, decR_pushZeroR.
      exact (reach_DR_crossQ_zero (decL (snd (popL ls))) (decR rtail')).
    - apply N.eqb_neq in Hqk1.
      inversion Hm; subst b'; clear Hm.
      rewrite (mEncR_zero_head_expand D ls _ Hl0), <- Hpl2.
      unfold encodeBase; cbn [mode l r decR].
      rewrite decL_pushZeroL, decL_pushPL, decL_pushOL, !decL_pushZeroL, decR_pushOneR, decR_pushZeroR.
      replace (qk + 1) with ((qk - 2 + 1) + 2) by lia.
      exact (reach_DR_crossQ (qk - 2 + 1) (decL (snd (popL ls))) (decR rtail')). }
  destruct rtail as [| [zk | k2 | k2 | k2] [| [k3 | k3 | v | k3] rt]];
    try exact (Hcross _ H).
  destruct (N.eqb zk 1) eqn:Hzk1; [| exact (Hcross _ H)].
  apply N.eqb_eq in Hzk1; subst zk.
  inversion H; subst b'; clear H.
  rewrite (mEncR_zero_head_expand D ls _ Hl0), <- Hpl2.
  unfold encodeBase; cbn [mode l r decR].
  rewrite decL_pushZeroL, decL_pushPL, decR_pushQR, !decR_pushZeroR.
  replace (qk + 1) with ((qk - 1) + 2) by lia.
  exact (reach_DR_multiShuttleZ2_plus v (qk - 1) (decL (snd (popL ls))) (decR rt)).
Qed.

Lemma stepBaseK_sound (b b' : BaseState) :
  stepBaseK b = Some b' ->
  encodeBase b -[ tm ]->+ encodeBase b'.
Proof.
  destruct b as [[|] ls rs]; unfold stepBaseK; cbn [mode l r]; intro H.
  - destruct ls as [| [k1 | ok | k1 | k1] [| [k2 | k2 | pk | k2] lt]];
      try exact (stepALElse_sound _ rs b' H).
    destruct (N.eqb ok 1) eqn:Hok1; [| exact (stepALElse_sound _ rs b' H)].
    apply N.eqb_eq in Hok1; subst ok.
    inversion H; subst b'; clear H.
    unfold encodeBase; cbn [mode l r decL].
    rewrite decL_pushOL, decR_push100RepeatR.
    exact (reach_AL_crossP_plus pk (decL lt) (decR rs)).
  - exact (stepDRBase_sound ls rs b' H).
Qed.

(** ** Section 4: Mixed-Chain Accelerator [stepChainK], [SafeProg] & [stepChainK_sound] *)

Inductive SepKind : Type := sep_z6 | sep_ba3 | sep_z4 | sep_ba1z2.

Inductive ChainLeaf : Type :=
| lf_z2q (w1 : N) (rt : list RTok)
| lf_cap1 | lf_cap2 | lf_capZ21 | lf_capZ22 | lf_capB.

Definition cap1Toks : list RTok := [R_ba 0; R_q 1; R_ba 0; R_z 0; R_q 0; R_ba 1].
Definition cap2Toks : list RTok := [R_z 3; R_q 0; R_z 3; R_q 1; R_ba 1].
Definition capZ21Toks : list RTok := [R_z 1; R_q 0; R_z 1; R_q 0; R_z 3; R_q 1; R_ba 1].
Definition capZ22Toks : list RTok := [R_z 1; R_q 1; R_z 1; R_q 0; R_z 3; R_q 1; R_ba 1].
Definition capBToks : list RTok := [R_ba 0; R_q 3; R_ba 0; R_z 0; R_q 0; R_z 1; R_q 0; R_z 3; R_q 1; R_ba 1].

Definition matchCapLeaf (rem : list RTok) : option ChainLeaf :=
  if listRBeq rem cap1Toks then Some lf_cap1
  else if listRBeq rem cap2Toks then Some lf_cap2
  else if listRBeq rem capZ21Toks then Some lf_capZ21
  else if listRBeq rem capZ22Toks then Some lf_capZ22
  else if listRBeq rem capBToks then Some lf_capB
  else None.

Fixpoint parseChain (u0 : N) (rem : list RTok) : option (N * list (SepKind * N) * ChainLeaf) :=
  match matchCapLeaf rem with
  | Some lf => Some (u0, [], lf)
  | None =>
    match rem with
    | R_z zk :: R_q u1 :: r' =>
      if N.eqb zk 5 then
        match parseChain (u1 + 1) r' with
        | Some (uFirst, rest, lf) => Some (u0, (sep_z6, uFirst) :: rest, lf)
        | None => None
        end
      else if N.eqb zk 3 then
        match parseChain (u1 + 1) r' with
        | Some (uFirst, rest, lf) => Some (u0, (sep_z4, uFirst) :: rest, lf)
        | None => None
        end
      else if N.eqb zk 1 then
        Some (u0, [], lf_z2q (u1 + 1) r')
      else None
    | R_ba bk :: R_q u1 :: r' =>
      if N.eqb bk 2 then
        match parseChain (u1 + 1) r' with
        | Some (uFirst, rest, lf) => Some (u0, (sep_ba3, uFirst) :: rest, lf)
        | None => None
        end
      else None
    | R_ba bk :: R_z zk :: R_q u1 :: r' =>
      if N.eqb bk 0 then
        if N.eqb zk 1 then
          match parseChain (u1 + 1) r' with
          | Some (uFirst, rest, lf) => Some (u0, (sep_ba1z2, uFirst) :: rest, lf)
          | None => None
          end
        else None
      else None
    | _ => None
    end
  end.

Record SDelta : Type := mkSDelta {
  isNeg : bool;
  mag : N
}.

Definition sdeltaOfPosNeg (nPos nNeg : N) : SDelta :=
  if N.leb nNeg nPos then mkSDelta false (nPos - nNeg)
  else mkSDelta true (nNeg - nPos).

Definition minNK (a b : N) : N :=
  if N.leb a b then a else b.

Definition boundKWith (curK : option N) (u req : N) (sd : SDelta) : option (option N) :=
  if N.leb req u then
    if isNeg sd then
      if N.leb 1 (mag sd) then
        if N.leb (req + mag sd) u then
          let q := N.div (u - req) (mag sd) in
          match curK with
          | None => Some (Some q)
          | Some k0 => Some (Some (minNK k0 q))
          end
        else None
      else Some curK
    else Some curK
  else None.

Definition chainBaseReq {A : Type} (tl : list A) (lf : ChainLeaf) : N :=
  match tl, lf with
  | [], lf_capB => 4
  | [], lf_z2q _ _ => 1
  | _, _ => 2
  end.

Fixpoint foldChainRTL (pairs : list (SepKind * N)) (lf : ChainLeaf)
  : option (N * N * option N * list (SepKind * N * SDelta)) :=
  match pairs with
  | [] =>
    match lf with
    | lf_z2q w1 _ => Some (1, 0, Some w1, [])
    | lf_cap1 | lf_cap2 | lf_capZ21 | lf_capZ22 => Some (3, 1, None, [])
    | lf_capB => Some (5, 1, None, [])
    end
  | (sep, uNext) :: tl =>
    match foldChainRTL tl lf with
    | None => None
    | Some (nPos, nNeg, curK, acc) =>
      let baseReq := chainBaseReq tl lf in
      let nTot := nPos + nNeg in
      match sep with
      | sep_z6 | sep_ba3 =>
        let req := if N.leb 2 baseReq then baseReq else 2 in
        let sd := sdeltaOfPosNeg nPos nNeg in
        match boundKWith curK uNext req sd with
        | None => None
        | Some nextK => Some (nTot, nTot, nextK, (sep, uNext, sd) :: acc)
        end
      | sep_z4 | sep_ba1z2 =>
        let req := if N.leb 3 baseReq then baseReq else 3 in
        let sd := mkSDelta true (nPos + 3 * nNeg) in
        match boundKWith curK uNext req sd with
        | None => None
        | Some nextK => Some (3 * nTot, nTot, nextK, (sep, uNext, sd) :: acc)
        end
      end
    end
  end.

Definition applyDeltaK (u k : N) (sd : SDelta) : N :=
  if isNeg sd then u - k * mag sd else u + k * mag sd.

Fixpoint buildChainTail (items : list (SepKind * N * SDelta)) (k : N) (lf : ChainLeaf) (uCur : N)
  : list RTok :=
  match items with
  | [] =>
    let qLast := uCur - 1 in
    match lf with
    | lf_z2q w1 rt =>
      let remAfter :=
        if N.eqb w1 k then pushZeroR (pushZeroR rt)
        else R_z 1 :: R_q (w1 - k - 1) :: rt in
      pushQR qLast remAfter
    | lf_cap1 => R_q qLast :: cap1Toks
    | lf_cap2 => R_q qLast :: cap2Toks
    | lf_capZ21 => R_q qLast :: capZ21Toks
    | lf_capZ22 => R_q qLast :: capZ22Toks
    | lf_capB => R_q qLast :: capBToks
    end
  | (sep, uNext, sd) :: tl =>
    let qCur := uCur - 1 in
    let uNextNew := applyDeltaK uNext k sd in
    let tail := buildChainTail tl k lf uNextNew in
    match sep with
    | sep_z6 => R_q qCur :: R_z 5 :: tail
    | sep_ba3 => R_q qCur :: R_ba 2 :: tail
    | sep_z4 => R_q qCur :: R_z 3 :: tail
    | sep_ba1z2 => R_q qCur :: R_ba 0 :: R_z 1 :: tail
    end
  end.

Definition chainReq0 {A : Type} (pairs : list A) (lf : ChainLeaf) : N :=
  match pairs, lf with
  | [], lf_capB => 4
  | _, _ => 2
  end.

Definition stepChainK (b : BaseState) : option BaseState :=
  match mode b with
  | mAL => None
  | mDR =>
    if isZeroHeadL (l b) then
      match r b with
      | R_q u0_0 :: rem =>
        let u0 := u0_0 + 1 in
        match parseChain u0 rem with
        | None => None
        | Some (uFirst, pairs, lf) =>
          match foldChainRTL pairs lf with
          | None => None
          | Some (nPos, nNeg, curK, items) =>
            let req0 := chainReq0 pairs lf in
            let sd0 := mkSDelta true (2 * nNeg) in
            match boundKWith curK uFirst req0 sd0 with
            | Some (Some kVal) =>
              if N.leb 1 kVal then
                let n0 := nPos + nNeg in
                let pPush := kVal * n0 - 1 in
                let u0New := applyDeltaK uFirst kVal sd0 in
                let lt := snd (popL (l b)) in
                let newL := pushZeroL (pushPL pPush lt) in
                let newR := buildChainTail items kVal lf u0New in
                Some (mkBase mDR newL newR)
              else None
            | _ => None
            end
          end
        end
      | _ => None
      end
    else None
  end.

Definition stepAutoK (b : BaseState) : option BaseState :=
  match stepChainK b with
  | Some b' => Some b'
  | None => stepBaseK b
  end.

Definition stepAutoOpt (cur : option BaseState) : option BaseState :=
  match cur with
  | None => None
  | Some b => stepAutoK b
  end.

Definition runStepsPos (p : positive) (st : BaseState) : option BaseState :=
  Pos.iter stepAutoOpt (Some st) p.

(** *** Separator & Cap-Leaf Micro-Certificates *)

Lemma reach_Z5_absorb (p q : N) (lt rs : list Sym) :
  inCfg p lt (repZero 6 (repQ (q + 1) rs)) -[ tm ]->+
  outCfg (p + 1) lt (repBA 3 (repQ q rs)).
Proof.
  unfold inCfg, outCfg. rewrite repQ_succ, repP_succ.
  apply (reachOpen tm false A [S0] [S1; S0; S0; S0; S0; S0; S0; S0; S0; S0; S1]
           (repP p lt) (repQ q rs) false A [S1; S1; S0; S1; S1] [S1; S0; S1; S0; S1; S0; S1]); check_window.
Qed.

Lemma reach_BA2_down (p q : N) (lt rs : list Sym) :
  inCfg p lt (repBA 3 (repQ q rs)) -[ tm ]->+
  inCfg q (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP p lt) rs.
Proof.
  unfold inCfg.
  eapply progress_evstep_trans.
  - exact (reach_AL_shuttleBA_plus 2 (repP p lt) (repQ q rs)).
  - exact (reach_AL_shuttleQ_star q (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP p lt) rs).
Qed.

Lemma reach_BA2_up (p' qp : N) (lt rs' : list Sym) :
  outCfg qp (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt) rs' -[ tm ]->+
  outCfg p' lt (repZero 6 (repQ (qp + 1) rs')).
Proof.
  unfold outCfg.
  eapply evstep_progress_trans.
  - exact (reach_AL_crossP_star qp (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt) (S1 :: rs')).
  - rewrite rep100_one, repP_succ, repQ_succ.
    apply (reachOpen tm false A [S1; S1; S1; S1; S1; S1; S1; S1; S0; S1; S1] [S1]
             (repP p' lt) (repQ qp rs') false A [S1; S1] [S1; S0; S0; S0; S0; S0; S0; S0; S0; S1]); check_window.
Qed.

Lemma reach_Z3_down (p q : N) (lt rs : list Sym) :
  inCfg p lt (S0 :: S0 :: S0 :: S0 :: repQ (q + 2) rs) -[ tm ]->+
  inCfg q (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt) rs.
Proof.
  unfold inCfg.
  replace (q + 2) with (2 + q) by lia.
  rewrite repQ_add.
  replace (p + 2) with ((p + 1) + 1) by lia.
  rewrite !repP_succ.
  eapply progress_evstep_trans.
  - apply (reachOpen tm false A [S0] [S1; S0; S0; S0; S0; S0; S0; S0; S1; S0; S0; S1]
             (repP p lt) (repQ q rs)
             false A [S0; S1; S1; S0; S1; S0; S1; S1; S0; S1; S1] [S1; S0]); check_window.
  - exact (reach_AL_shuttleQ_star q (S1 :: S1 :: S0 :: S1 :: S0 :: S1 :: S1 :: S0 :: S1 :: S1 :: repP p lt) rs).
Qed.

Lemma reach_Z3_up (p qp : N) (lt rs' : list Sym) :
  outCfg qp (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt) rs' -[ tm ]->+
  outCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: repQ (qp + 1) rs').
Proof.
  unfold outCfg.
  eapply evstep_progress_trans.
  - exact (reach_AL_crossP_star qp (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt) (S1 :: rs')).
  - rewrite rep100_one.
    replace (p + 2) with ((p + 1) + 1) by lia.
    rewrite (repP_succ (p + 1)), repQ_succ.
    apply (reachOpen tm false A [S1; S1; S1; S1; S0; S1; S0; S1; S1] [S1]
             (repP (p + 1) lt) (repQ qp rs')
             false A [S1; S1] [S1; S0; S1; S0; S0; S0; S0; S1]); check_window.
Qed.

Lemma reach_BA0Z1_absorb (p : N) (lt rs : list Sym) :
  inCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: S0 :: S0 :: S1 :: rs) -[ tm ]->+
  outCfg p lt (S0 :: S0 :: repQ 2 (S0 :: S0 :: rs)).
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachOpen tm false A [S0; S0; S1; S1] [S1; S0; S0; S1; S0; S0; S0; S0; S1]
           (repP p lt) rs false A [S1; S1] [S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S0]); check_window.
Qed.

Definition capA0 : list Sym := decR cap1Toks.
Definition capA1 : list Sym := decR capZ22Toks.
Definition capA2 : list Sym := decR capZ21Toks.
Definition capA3 : list Sym := decR cap2Toks.
Definition capB0 : list Sym := decR capBToks.

Definition capB1 : list Sym :=
  [S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S1;
   S0; S0; S1; S0; S0; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S0; S1].
Definition capB2 : list Sym :=
  [S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1;
   S0; S0; S0; S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S0; S1].
Definition capB3 : list Sym :=
  [S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S0;
   S0; S0; S0; S1; S0; S0; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S0; S1].
Definition capB4 : list Sym :=
  [S0; S0; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S0; S0;
   S1; S0; S0; S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S0; S1].
Definition capB5 : list Sym :=
  [S0; S0; S0; S0; S0; S0; S1; S0; S0; S0; S0; S1; S0; S0; S1; S0; S0; S0; S0; S0; S0; S1; S0; S0;
   S0; S0; S0; S0; S1; S0; S0; S1; S0; S1; S0; S1].

Lemma reach_capA_0 (p' : N) (lt : list Sym) :
  inCfg (p' + 1) lt capA0 -[ tm ]->+ outCfg p' lt capA1.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0; S0; S1; S1] (S1 :: S0 :: capA0) (repP p' lt)
           false A [S1; S1] (S1 :: capA1)); check_window.
Qed.

Lemma reach_capA_1 (p : N) (lt : list Sym) :
  inCfg p lt capA1 -[ tm ]->+ outCfg (p + 1) lt capA2.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capA1) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capA2)); check_window.
Qed.

Lemma reach_capA_2 (p : N) (lt : list Sym) :
  inCfg p lt capA2 -[ tm ]->+ outCfg (p + 1) lt capA3.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capA2) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capA3)); check_window.
Qed.

Lemma reach_capA_3 (p : N) (lt : list Sym) :
  inCfg p lt capA3 -[ tm ]->+ outCfg (p + 1) lt capA0.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capA3) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capA0)); check_window.
Qed.

Lemma reach_capB_0 (p' : N) (lt : list Sym) :
  inCfg (p' + 1) lt capB0 -[ tm ]->+ outCfg p' lt capB1.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0; S0; S1; S1] (S1 :: S0 :: capB0) (repP p' lt)
           false A [S1; S1] (S1 :: capB1)); check_window.
Qed.

Lemma reach_capB_1 (p : N) (lt : list Sym) :
  inCfg p lt capB1 -[ tm ]->+ outCfg (p + 1) lt capB2.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capB1) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capB2)); check_window.
Qed.

Lemma reach_capB_2 (p : N) (lt : list Sym) :
  inCfg p lt capB2 -[ tm ]->+ outCfg (p + 1) lt capB3.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capB2) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capB3)); check_window.
Qed.

Lemma reach_capB_3 (p : N) (lt : list Sym) :
  inCfg p lt capB3 -[ tm ]->+ outCfg (p + 1) lt capB4.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capB3) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capB4)); check_window.
Qed.

Lemma reach_capB_4 (p : N) (lt : list Sym) :
  inCfg p lt capB4 -[ tm ]->+ outCfg (p + 1) lt capB5.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capB4) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capB5)); check_window.
Qed.

Lemma reach_capB_5 (p : N) (lt : list Sym) :
  inCfg p lt capB5 -[ tm ]->+ outCfg (p + 1) lt capB0.
Proof.
  unfold inCfg, outCfg. rewrite repP_succ.
  apply (reachClosed tm false A [S0] (S1 :: S0 :: capB5) (repP p lt)
           false A [S1; S1; S0; S1; S1] (S1 :: capB0)); check_window.
Qed.

(** *** [SafeProg] Combinators *)

Inductive SafeProg : N -> N -> N -> N -> list Sym -> list Sym -> Prop :=
| SP_nil (b : N) (r0 : list Sym) : SafeProg b b 0 0 r0 r0
| SP_pos {b0 b2 P M : N} {r0 r1 r2 : list Sym}
    (h0 : forall (p : N) (lt : list Sym), inCfg p lt r0 -[ tm ]->+ outCfg (p + 1) lt r1)
    (hrest : SafeProg (b0 + 1) b2 P M r1 r2) :
    SafeProg b0 b2 (P + 1) M r0 r2
| SP_neg {b0 b2 P M : N} {r0 r1 r2 : list Sym}
    (h0 : forall (p' : N) (lt : list Sym), inCfg (p' + 1) lt r0 -[ tm ]->+ outCfg p' lt r1)
    (hrest : SafeProg b0 b2 P M r1 r2) :
    SafeProg (b0 + 1) b2 P (M + 1) r0 r2.

Lemma sp_pos {b0 b2 P' M : N} {r0 r1 r2 : list Sym} :
  1 <= P' ->
  (forall (p : N) (lt : list Sym), inCfg p lt r0 -[ tm ]->+ outCfg (p + 1) lt r1) ->
  SafeProg (b0 + 1) b2 (P' - 1) M r1 r2 ->
  SafeProg b0 b2 P' M r0 r2.
Proof.
  intros HP H0 Hr.
  replace P' with ((P' - 1) + 1) by lia.
  exact (SP_pos H0 Hr).
Qed.

Lemma sp_neg {b0' b2 P M' : N} {r0 r1 r2 : list Sym} :
  1 <= b0' -> 1 <= M' ->
  (forall (p' : N) (lt : list Sym), inCfg (p' + 1) lt r0 -[ tm ]->+ outCfg p' lt r1) ->
  SafeProg (b0' - 1) b2 P (M' - 1) r1 r2 ->
  SafeProg b0' b2 P M' r0 r2.
Proof.
  intros Hb HM H0 Hr.
  replace b0' with ((b0' - 1) + 1) by lia.
  replace M' with ((M' - 1) + 1) by lia.
  exact (SP_neg H0 Hr).
Qed.

Lemma SP_append {b0 b1 b2 P1 M1 P2 M2 : N} {r0 r1 r2 : list Sym}
  (h1 : SafeProg b0 b1 P1 M1 r0 r1) (h2 : SafeProg b1 b2 P2 M2 r1 r2) :
  SafeProg b0 b2 (P1 + P2) (M1 + M2) r0 r2.
Proof.
  induction h1 as [b rA | b0 bMid P M rA rB rC h0 _ IH | b0 bMid P M rA rB rC h0 _ IH].
  - cbn. exact h2.
  - replace ((P + 1) + P2) with ((P + P2) + 1) by lia.
    exact (SP_pos h0 (IH h2)).
  - replace ((M + 1) + M2) with ((M + M2) + 1) by lia.
    exact (SP_neg h0 (IH h2)).
Qed.

Lemma SP_shift {b0 b1 P M : N} {r0 r1 : list Sym}
  (h : SafeProg b0 b1 P M r0 r1) (d : N) :
  SafeProg (b0 + d) (b1 + d) P M r0 r1.
Proof.
  induction h as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH].
  - exact (SP_nil (b + d) rA).
  - apply (SP_pos h0).
    replace ((bA + d) + 1) with ((bA + 1) + d) by lia.
    exact IH.
  - replace ((bA + 1) + d) with ((bA + d) + 1) by lia.
    exact (SP_neg h0 IH).
Qed.

Lemma SP_iter {delta P M : N} {r0 : list Sym}
  (h1 : SafeProg 1 (1 + delta) P M r0 r0) :
  forall kv : N, SafeProg 1 (1 + kv * delta) (kv * P) (kv * M) r0 r0.
Proof.
  induction kv as [| kv IH] using N.peano_ind.
  - cbn. exact (SP_nil 1 r0).
  - replace (N.succ kv) with (kv + 1) by lia.
    pose proof (SP_shift IH delta) as Hsh.
    replace ((1 + kv * delta) + delta) with (1 + (kv + 1) * delta) in Hsh by nia.
    pose proof (SP_append h1 Hsh) as Happ.
    replace (P + kv * P) with ((kv + 1) * P) in Happ by nia.
    replace (M + kv * M) with ((kv + 1) * M) in Happ by nia.
    exact Happ.
Qed.

Lemma safeProg_z2q_iter (kv : N) :
  forall (remW : N) (rt : list Sym),
    SafeProg 1 (1 + kv * 1) (kv * 1) (kv * 0)
      (S0 :: S0 :: repQ (kv + remW) rt) (S0 :: S0 :: repQ remW rt).
Proof.
  induction kv as [| kv IH] using N.peano_ind; intros remW rt.
  - cbn. exact (SP_nil 1 (S0 :: S0 :: repQ remW rt)).
  - replace (N.succ kv) with (kv + 1) by lia.
    assert (Hstep : SafeProg 1 2 1 0
              (S0 :: S0 :: repQ (kv + 1 + remW) rt) (S0 :: S0 :: repQ (kv + remW) rt)).
    { replace (kv + 1 + remW) with ((kv + remW) + 1) by lia.
      rewrite repQ_succ.
      eapply sp_pos; [lia | exact (fun p lt => reach_Z2_leaf p lt (repQ (kv + remW) rt)) | exact (SP_nil _ _)]. }
    pose proof (SP_shift (IH remW rt) 1) as Hsh.
    pose proof (SP_append Hstep Hsh) as Happ.
    replace ((1 + kv * 1) + 1) with (1 + (kv + 1) * 1) in Happ by lia.
    replace (1 + kv * 1) with ((kv + 1) * 1) in Happ by lia.
    replace (0 + kv * 0) with ((kv + 1) * 0) in Happ by lia.
    exact Happ.
Qed.

Lemma safeProg_cap1_one : SafeProg 1 (1 + 2) 3 1 capA0 capA0.
Proof.
  eapply sp_neg; [lia | lia | exact reach_capA_0 |].
  eapply sp_pos; [lia | exact reach_capA_1 |].
  eapply sp_pos; [lia | exact reach_capA_2 |].
  eapply sp_pos; [lia | exact reach_capA_3 | exact (SP_nil _ _)].
Qed.

Lemma safeProg_capZ22_one : SafeProg 1 (1 + 2) 3 1 capA1 capA1.
Proof.
  eapply sp_pos; [lia | exact reach_capA_1 |].
  eapply sp_pos; [lia | exact reach_capA_2 |].
  eapply sp_pos; [lia | exact reach_capA_3 |].
  eapply sp_neg; [lia | lia | exact reach_capA_0 | exact (SP_nil _ _)].
Qed.

Lemma safeProg_capZ21_one : SafeProg 1 (1 + 2) 3 1 capA2 capA2.
Proof.
  eapply sp_pos; [lia | exact reach_capA_2 |].
  eapply sp_pos; [lia | exact reach_capA_3 |].
  eapply sp_neg; [lia | lia | exact reach_capA_0 |].
  eapply sp_pos; [lia | exact reach_capA_1 | exact (SP_nil _ _)].
Qed.

Lemma safeProg_cap2_one : SafeProg 1 (1 + 2) 3 1 capA3 capA3.
Proof.
  eapply sp_pos; [lia | exact reach_capA_3 |].
  eapply sp_neg; [lia | lia | exact reach_capA_0 |].
  eapply sp_pos; [lia | exact reach_capA_1 |].
  eapply sp_pos; [lia | exact reach_capA_2 | exact (SP_nil _ _)].
Qed.

Lemma safeProg_capB_one : SafeProg 1 (1 + 4) 5 1 capB0 capB0.
Proof.
  eapply sp_neg; [lia | lia | exact reach_capB_0 |].
  eapply sp_pos; [lia | exact reach_capB_1 |].
  eapply sp_pos; [lia | exact reach_capB_2 |].
  eapply sp_pos; [lia | exact reach_capB_3 |].
  eapply sp_pos; [lia | exact reach_capB_4 |].
  eapply sp_pos; [lia | exact reach_capB_5 | exact (SP_nil _ _)].
Qed.

Lemma SP_liftZ6 {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) (uBase : N) (Hu : 1 <= uBase) :
  SafeProg 1 1 (P + M) (P + M)
    (repZero 6 (repQ (uBase + b0) r0)) (repZero 6 (repQ (uBase + b1) r1)).
Proof.
  induction hp as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH].
  - exact (SP_nil 1 _).
  - set (q := uBase + bA - 1).
    replace (uBase + bA) with (q + 1) by lia.
    replace (uBase + (bA + 1)) with (q + 2) in IH by lia.
    assert (Hstep2 : forall (p' : N) (lt : list Sym),
      inCfg (p' + 1) lt (repBA 3 (repQ q rA)) -[ tm ]->+
      outCfg p' lt (repZero 6 (repQ (q + 2) rB))).
    { intros p' lt.
      eapply progress_trans; [exact (reach_BA2_down (p' + 1) q lt rA) |].
      eapply progress_trans; [exact (h0 q (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt)) |].
      replace (q + 2) with ((q + 1) + 1) by lia.
      exact (reach_BA2_up p' (q + 1) lt rB). }
    assert (Hpair : SafeProg 1 1 1 1
              (repZero 6 (repQ (q + 1) rA)) (repZero 6 (repQ (q + 2) rB)))
      by exact (SP_pos (fun p lt => reach_Z5_absorb p q lt rA) (SP_neg Hstep2 (SP_nil 1 _))).
    pose proof (SP_append Hpair IH) as Happ.
    replace (1 + (P + M)) with ((P + 1) + M) in Happ by lia.
    exact Happ.
  - set (d := uBase + bA - 1).
    replace (uBase + (bA + 1)) with ((d + 1) + 1) by lia.
    replace (uBase + bA) with (d + 1) in IH by lia.
    assert (Hstep2 : forall (p' : N) (lt : list Sym),
      inCfg (p' + 1) lt (repBA 3 (repQ (d + 1) rA)) -[ tm ]->+
      outCfg p' lt (repZero 6 (repQ (d + 1) rB))).
    { intros p' lt.
      eapply progress_trans; [exact (reach_BA2_down (p' + 1) (d + 1) lt rA) |].
      eapply progress_trans; [exact (h0 d (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt)) |].
      exact (reach_BA2_up p' d lt rB). }
    assert (Hpair : SafeProg 1 1 1 1
              (repZero 6 (repQ ((d + 1) + 1) rA)) (repZero 6 (repQ (d + 1) rB)))
      by exact (SP_pos (fun p lt => reach_Z5_absorb p (d + 1) lt rA) (SP_neg Hstep2 (SP_nil 1 _))).
    pose proof (SP_append Hpair IH) as Happ.
    replace (1 + (P + M)) with (P + (M + 1)) in Happ by lia.
    exact Happ.
Qed.

Lemma SP_liftBA3 {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) (uBase : N) :
  SafeProg 1 1 (P + M) (P + M)
    (repBA 3 (repQ (uBase + b0) r0)) (repBA 3 (repQ (uBase + b1) r1)).
Proof.
  induction hp as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH].
  - exact (SP_nil 1 _).
  - set (q := uBase + bA).
    replace (uBase + (bA + 1)) with (q + 1) in IH by lia.
    assert (Hstep1 : forall (p' : N) (lt : list Sym),
      inCfg (p' + 1) lt (repBA 3 (repQ q rA)) -[ tm ]->+
      outCfg p' lt (repZero 6 (repQ ((q + 1) + 1) rB))).
    { intros p' lt.
      eapply progress_trans; [exact (reach_BA2_down (p' + 1) q lt rA) |].
      eapply progress_trans; [exact (h0 q (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt)) |].
      exact (reach_BA2_up p' (q + 1) lt rB). }
    assert (Hpair : SafeProg 1 1 1 1
              (repBA 3 (repQ q rA)) (repBA 3 (repQ (q + 1) rB))).
    { eapply sp_neg; [lia | lia | exact Hstep1 |]. eapply sp_pos; [lia | exact (fun p lt => reach_Z5_absorb p (q + 1) lt rB) | exact (SP_nil _ _)]. }
    pose proof (SP_append Hpair IH) as Happ.
    replace (1 + (P + M)) with ((P + 1) + M) in Happ by lia.
    exact Happ.
  - set (q := uBase + bA).
    replace (uBase + (bA + 1)) with (q + 1) by lia.
    assert (Hstep1 : forall (p' : N) (lt : list Sym),
      inCfg (p' + 1) lt (repBA 3 (repQ (q + 1) rA)) -[ tm ]->+
      outCfg p' lt (repZero 6 (repQ (q + 1) rB))).
    { intros p' lt.
      eapply progress_trans; [exact (reach_BA2_down (p' + 1) (q + 1) lt rA) |].
      eapply progress_trans; [exact (h0 q (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: repP (p' + 1) lt)) |].
      exact (reach_BA2_up p' q lt rB). }
    assert (Hpair : SafeProg 1 1 1 1
              (repBA 3 (repQ (q + 1) rA)) (repBA 3 (repQ q rB))).
    { eapply sp_neg; [lia | lia | exact Hstep1 |]. eapply sp_pos; [lia | exact (fun p lt => reach_Z5_absorb p q lt rB) | exact (SP_nil _ _)]. }
    pose proof (SP_append Hpair IH) as Happ.
    replace (1 + (P + M)) with (P + (M + 1)) in Happ by lia.
    exact Happ.
Qed.

Lemma safeProg_ba1z2_to_z4 (b : N) (rs : list Sym) :
  SafeProg 1 2 2 1
    (S0 :: S1 :: S0 :: S0 :: repQ (b + 2) rs)
    (S0 :: S0 :: S0 :: S0 :: repQ (b + 1) rs).
Proof.
  replace (b + 2) with ((b + 1) + 1) by lia.
  rewrite (repQ_succ (b + 1)).
  assert (H1 : forall (p' : N) (lt : list Sym),
    inCfg (p' + 1) lt (S0 :: S1 :: S0 :: S0 :: S0 :: S0 :: S1 :: repQ (b + 1) rs) -[ tm ]->+
    outCfg p' lt (S0 :: S0 :: repQ 2 (S0 :: S0 :: repQ (b + 1) rs)))
    by exact (fun p' lt => reach_BA0Z1_absorb p' lt (repQ (b + 1) rs)).
  assert (H2 : forall (p : N) (lt : list Sym),
    inCfg p lt (S0 :: S0 :: repQ 2 (S0 :: S0 :: repQ (b + 1) rs)) -[ tm ]->+
    outCfg (p + 1) lt (S0 :: S0 :: repQ 1 (S0 :: S0 :: repQ (b + 1) rs)))
    by exact (fun p lt => reach_Z2_leaf p lt (S0 :: S0 :: S1 :: S0 :: S0 :: repQ (b + 1) rs)).
  assert (H3 : forall (p : N) (lt : list Sym),
    inCfg p lt (S0 :: S0 :: repQ 1 (S0 :: S0 :: repQ (b + 1) rs)) -[ tm ]->+
    outCfg (p + 1) lt (S0 :: S0 :: S0 :: S0 :: repQ (b + 1) rs))
    by exact (fun p lt => reach_Z2_leaf p lt (S0 :: S0 :: repQ (b + 1) rs)).
  eapply sp_neg; [lia | lia | exact H1 |]. eapply sp_pos; [lia | exact H2 |]. eapply sp_pos; [lia | exact H3 | exact (SP_nil _ _)].
Qed.

Lemma SP_liftZ4 {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) :
  forall (uEnd : N), 1 <= uEnd ->
    SafeProg 1 (1 + 2 * (P + M)) (3 * (P + M)) (P + M)
      (S0 :: S0 :: S0 :: S0 :: repQ (uEnd + P + 3 * M) r0)
      (S0 :: S0 :: S0 :: S0 :: repQ uEnd r1).
Proof.
  induction hp as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH];
    intros uEnd Hu.
  - replace (uEnd + 0 + 3 * 0) with uEnd by lia.
    exact (SP_nil 1 (S0 :: S0 :: S0 :: S0 :: repQ uEnd rA)).
  - set (uMid := uEnd + P + 3 * M).
    assert (HuMid : 1 <= uMid) by lia.
    set (q := uMid - 1).
    replace (uEnd + (P + 1) + 3 * M) with (q + 2) by lia.
    assert (Hq1 : q + 1 = uMid) by lia.
    assert (Hz : forall (p : N) (lt : list Sym),
      inCfg p lt (S0 :: S0 :: S0 :: S0 :: repQ (q + 2) rA) -[ tm ]->+
      outCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: repQ (q + 2) rB)).
    { intros p lt.
      eapply progress_trans; [exact (reach_Z3_down p q lt rA) |].
      eapply progress_trans; [exact (h0 q (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt)) |].
      replace (q + 2) with ((q + 1) + 1) by lia.
      exact (reach_Z3_up p (q + 1) lt rB). }
    assert (H4 : SafeProg 1 3 3 1
              (S0 :: S0 :: S0 :: S0 :: repQ (q + 2) rA)
              (S0 :: S0 :: S0 :: S0 :: repQ uMid rB)).
    { pose proof (SP_shift (safeProg_ba1z2_to_z4 q rB) 1) as Hb.
      rewrite Hq1 in Hb. exact (SP_pos Hz Hb). }
    pose proof (SP_shift (IH uEnd Hu) 2) as Hrest.
    pose proof (SP_append H4 Hrest) as Happ.
    replace ((1 + 2 * (P + M)) + 2) with (1 + 2 * ((P + 1) + M)) in Happ by lia.
    replace (3 + 3 * (P + M)) with (3 * ((P + 1) + M)) in Happ by lia.
    replace (1 + (P + M)) with ((P + 1) + M) in Happ by lia.
    exact Happ.
  - set (uMid := uEnd + P + 3 * M).
    assert (HuMid : 1 <= uMid) by lia.
    set (d := uMid - 1).
    replace (uEnd + P + 3 * (M + 1)) with ((d + 2) + 2) by lia.
    assert (Hd1 : d + 1 = uMid) by lia.
    assert (Hz : forall (p : N) (lt : list Sym),
      inCfg p lt (S0 :: S0 :: S0 :: S0 :: repQ ((d + 2) + 2) rA) -[ tm ]->+
      outCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: repQ (d + 2) rB)).
    { intros p lt.
      eapply progress_trans; [exact (reach_Z3_down p (d + 2) lt rA) |].
      replace (d + 2) with ((d + 1) + 1) by lia.
      eapply progress_trans; [exact (h0 (d + 1) (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt)) |].
      exact (reach_Z3_up p (d + 1) lt rB). }
    assert (H4 : SafeProg 1 3 3 1
              (S0 :: S0 :: S0 :: S0 :: repQ ((d + 2) + 2) rA)
              (S0 :: S0 :: S0 :: S0 :: repQ uMid rB)).
    { pose proof (SP_shift (safeProg_ba1z2_to_z4 d rB) 1) as Hb.
      rewrite Hd1 in Hb. exact (SP_pos Hz Hb). }
    pose proof (SP_shift (IH uEnd Hu) 2) as Hrest.
    pose proof (SP_append H4 Hrest) as Happ.
    replace ((1 + 2 * (P + M)) + 2) with (1 + 2 * (P + (M + 1))) in Happ by lia.
    replace (3 + 3 * (P + M)) with (3 * (P + (M + 1))) in Happ by lia.
    replace (1 + (P + M)) with (P + (M + 1)) in Happ by lia.
    exact Happ.
Qed.

Lemma SP_liftBA1Z2 {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) :
  forall (uEnd : N), 3 <= uEnd ->
    SafeProg 1 (1 + 2 * (P + M)) (3 * (P + M)) (P + M)
      (S0 :: S1 :: S0 :: S0 :: repQ (uEnd + P + 3 * M) r0)
      (S0 :: S1 :: S0 :: S0 :: repQ uEnd r1).
Proof.
  induction hp as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH];
    intros uEnd Hu.
  - replace (uEnd + 0 + 3 * 0) with uEnd by lia.
    exact (SP_nil 1 (S0 :: S1 :: S0 :: S0 :: repQ uEnd rA)).
  - set (uMid := uEnd + P + 3 * M).
    assert (HuMid : 3 <= uMid) by lia.
    set (q := uMid - 2).
    replace (uEnd + (P + 1) + 3 * M) with ((q + 1) + 2) by lia.
    assert (Hq2 : (q + 1) + 1 = uMid) by lia.
    pose proof (safeProg_ba1z2_to_z4 (q + 1) rA) as Hba.
    replace ((q + 1) + 1) with (q + 2) in Hba by lia.
    assert (Hz : forall (p : N) (lt : list Sym),
      inCfg p lt (S0 :: S0 :: S0 :: S0 :: repQ (q + 2) rA) -[ tm ]->+
      outCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: repQ uMid rB)).
    { intros p lt. rewrite <- Hq2.
      eapply progress_trans; [exact (reach_Z3_down p q lt rA) |].
      eapply progress_trans; [exact (h0 q (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt)) |].
      exact (reach_Z3_up p (q + 1) lt rB). }
    assert (Hz_sp : SafeProg 2 3 1 0
              (S0 :: S0 :: S0 :: S0 :: repQ (q + 2) rA)
              (S0 :: S1 :: S0 :: S0 :: repQ uMid rB))
      by (eapply sp_pos; [lia | exact Hz | exact (SP_nil _ _)]).
    assert (H4 : SafeProg 1 3 3 1
              (S0 :: S1 :: S0 :: S0 :: repQ ((q + 1) + 2) rA)
              (S0 :: S1 :: S0 :: S0 :: repQ uMid rB))
      by exact (SP_append Hba Hz_sp).
    pose proof (SP_shift (IH uEnd Hu) 2) as Hrest.
    pose proof (SP_append H4 Hrest) as Happ.
    replace ((1 + 2 * (P + M)) + 2) with (1 + 2 * ((P + 1) + M)) in Happ by lia.
    replace (3 + 3 * (P + M)) with (3 * ((P + 1) + M)) in Happ by lia.
    replace (1 + (P + M)) with ((P + 1) + M) in Happ by lia.
    exact Happ.
  - set (uMid := uEnd + P + 3 * M).
    assert (HuMid : 3 <= uMid) by lia.
    set (d := uMid - 1).
    replace (uEnd + P + 3 * (M + 1)) with ((d + 2) + 2) by lia.
    assert (Hd1 : d + 1 = uMid) by lia.
    pose proof (safeProg_ba1z2_to_z4 (d + 2) rA) as Hba.
    replace ((d + 2) + 1) with ((d + 1) + 2) in Hba by lia.
    assert (Hz : forall (p : N) (lt : list Sym),
      inCfg p lt (S0 :: S0 :: S0 :: S0 :: repQ ((d + 1) + 2) rA) -[ tm ]->+
      outCfg (p + 1) lt (S0 :: S1 :: S0 :: S0 :: repQ uMid rB)).
    { intros p lt. rewrite <- Hd1.
      eapply progress_trans; [exact (reach_Z3_down p (d + 1) lt rA) |].
      eapply progress_trans; [exact (h0 d (S1 :: S1 :: S0 :: S1 :: repP (p + 2) lt)) |].
      exact (reach_Z3_up p d lt rB). }
    assert (Hz_sp : SafeProg 2 3 1 0
              (S0 :: S0 :: S0 :: S0 :: repQ ((d + 1) + 2) rA)
              (S0 :: S1 :: S0 :: S0 :: repQ uMid rB))
      by (eapply sp_pos; [lia | exact Hz | exact (SP_nil _ _)]).
    assert (H4 : SafeProg 1 3 3 1
              (S0 :: S1 :: S0 :: S0 :: repQ ((d + 2) + 2) rA)
              (S0 :: S1 :: S0 :: S0 :: repQ uMid rB))
      by exact (SP_append Hba Hz_sp).
    pose proof (SP_shift (IH uEnd Hu) 2) as Hrest.
    pose proof (SP_append H4 Hrest) as Happ.
    replace ((1 + 2 * (P + M)) + 2) with (1 + 2 * (P + (M + 1))) in Happ by lia.
    replace (3 + 3 * (P + M)) with (3 * (P + (M + 1))) in Happ by lia.
    replace (1 + (P + M)) with (P + (M + 1)) in Happ by lia.
    exact Happ.
Qed.

Lemma SP_runTopStar {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) :
  forall (u0End : N) (lt : list Sym), 2 <= u0End ->
    mEncR D (S0 :: lt) (repQ (u0End + 2 * M) r0) -[ tm ]->*
    mEncR D (S0 :: repP (P + M) lt) (repQ u0End r1).
Proof.
  induction hp as [b rA | bA bB P M rA rB rC h0 _ IH | bA bB P M rA rB rC h0 _ IH];
    intros u0End lt Hu.
  - replace (u0End + 2 * 0) with u0End by lia.
    rewrite repP_0. apply evstep_refl.
  - set (p := u0End + 2 * M - 2).
    pose proof (reach_top_pass (h0 p (S1 :: S1 :: S0 :: S0 :: lt))) as H1.
    replace (p + 2) with (u0End + 2 * M) in H1 by lia.
    replace ((p + 1) + 1) with (u0End + 2 * M) in H1 by lia.
    pose proof (IH u0End (repP 1 lt) Hu) as H2.
    rewrite <- repP_add in H2.
    replace ((P + M) + 1) with ((P + 1) + M) in H2 by lia.
    exact (progress_evstep _ _ _ (progress_evstep_trans _ _ _ _ H1 H2)).
  - set (p' := u0End + 2 * M - 1).
    pose proof (reach_top_pass (h0 p' (S1 :: S1 :: S0 :: S0 :: lt))) as H1.
    replace ((p' + 1) + 2) with (u0End + 2 * (M + 1)) in H1 by lia.
    replace (p' + 1) with (u0End + 2 * M) in H1 by lia.
    pose proof (IH u0End (repP 1 lt) Hu) as H2.
    rewrite <- repP_add in H2.
    replace ((P + M) + 1) with (P + (M + 1)) in H2 by lia.
    exact (progress_evstep _ _ _ (progress_evstep_trans _ _ _ _ H1 H2)).
Qed.

Lemma SP_runTopPlus {b0 b1 P M : N} {r0 r1 : list Sym}
  (hp : SafeProg b0 b1 P M r0 r1) (Hpos : 1 <= P + M)
  (u0End : N) (lt : list Sym) (Hu : 2 <= u0End) :
  mEncR D (S0 :: lt) (repQ (u0End + 2 * M) r0) -[ tm ]->+
  mEncR D (S0 :: repP (P + M) lt) (repQ u0End r1).
Proof.
  destruct hp as [b rA | bA bB P' M rA rB rC h0 hrest | bA bB P M' rA rB rC h0 hrest].
  - lia.
  - set (p := u0End + 2 * M - 2).
    pose proof (reach_top_pass (h0 p (S1 :: S1 :: S0 :: S0 :: lt))) as H1.
    replace (p + 2) with (u0End + 2 * M) in H1 by lia.
    replace ((p + 1) + 1) with (u0End + 2 * M) in H1 by lia.
    pose proof (SP_runTopStar hrest u0End (repP 1 lt) Hu) as H2.
    rewrite <- repP_add in H2.
    replace ((P' + M) + 1) with ((P' + 1) + M) in H2 by lia.
    exact (progress_evstep_trans _ _ _ _ H1 H2).
  - set (p' := u0End + 2 * M' - 1).
    pose proof (reach_top_pass (h0 p' (S1 :: S1 :: S0 :: S0 :: lt))) as H1.
    replace ((p' + 1) + 2) with (u0End + 2 * (M' + 1)) in H1 by lia.
    replace (p' + 1) with (u0End + 2 * M') in H1 by lia.
    pose proof (SP_runTopStar hrest u0End (repP 1 lt) Hu) as H2.
    rewrite <- repP_add in H2.
    replace ((P + M') + 1) with (P + (M' + 1)) in H2 by lia.
    exact (progress_evstep_trans _ _ _ _ H1 H2).
Qed.

(** *** Connecting [parseChain], [foldChainRTL], and [buildChainTail] to [SafeProg] *)

Definition sepToks (s : SepKind) : list RTok :=
  match s with
  | sep_z6 => [R_z 5]
  | sep_ba3 => [R_ba 2]
  | sep_z4 => [R_z 3]
  | sep_ba1z2 => [R_ba 0; R_z 1]
  end.

Fixpoint rawRemOf (pairs : list (SepKind * N)) (lf : ChainLeaf) : list RTok :=
  match pairs with
  | [] =>
    match lf with
    | lf_z2q w1 rt => R_z 1 :: R_q (w1 - 1) :: rt
    | lf_cap1 => cap1Toks
    | lf_cap2 => cap2Toks
    | lf_capZ21 => capZ21Toks
    | lf_capZ22 => capZ22Toks
    | lf_capB => capBToks
    end
  | (sep, uNext) :: tl => sepToks sep ++ (R_q (uNext - 1) :: rawRemOf tl lf)
  end.

Lemma matchCapLeaf_sound (rem : list RTok) (lf : ChainLeaf) :
  matchCapLeaf rem = Some lf ->
  rem = rawRemOf [] lf /\ (forall w1 rt, lf = lf_z2q w1 rt -> False).
Proof.
  unfold matchCapLeaf.
  destruct (listRBeq rem cap1Toks) eqn:H1.
  - intro H; inversion H; subst. split; [exact (listRBeq_eq _ _ H1) | intros; discriminate].
  - destruct (listRBeq rem cap2Toks) eqn:H2.
    + intro H; inversion H; subst. split; [exact (listRBeq_eq _ _ H2) | intros; discriminate].
    + destruct (listRBeq rem capZ21Toks) eqn:H3.
      * intro H; inversion H; subst. split; [exact (listRBeq_eq _ _ H3) | intros; discriminate].
      * destruct (listRBeq rem capZ22Toks) eqn:H4.
        -- intro H; inversion H; subst. split; [exact (listRBeq_eq _ _ H4) | intros; discriminate].
        -- destruct (listRBeq rem capBToks) eqn:H5; [| discriminate].
           intro H; inversion H; subst. split; [exact (listRBeq_eq _ _ H5) | intros; discriminate].
Qed.

Lemma parseChain_sound_len :
  forall (bound : nat) (u0 : N) (rem : list RTok)
    (uFirst : N) (pairs : list (SepKind * N)) (lf : ChainLeaf),
    (List.length rem <= bound)%nat ->
    parseChain u0 rem = Some (uFirst, pairs, lf) ->
    uFirst = u0 /\ rem = rawRemOf pairs lf /\ (forall w1 rt, lf = lf_z2q w1 rt -> 1 <= w1).
Proof.
  induction bound as [| bound IH]; intros u0 rem uFirst pairs lf Hlen H.
  - destruct rem; [| cbn [List.length] in Hlen; lia].
    cbn [parseChain matchCapLeaf listRBeq] in H. discriminate.
  - destruct rem as [| rt0 rem1]; [cbn [parseChain matchCapLeaf listRBeq] in H; discriminate |].
    cbn [parseChain] in H.
    destruct (matchCapLeaf (rt0 :: rem1)) as [lf0 |] eqn:Hm.
    + inversion H; subst.
      destruct (matchCapLeaf_sound _ _ Hm) as [Hrem Hno].
      split; [reflexivity | split; [exact Hrem | intros w1 rt Heq; exfalso; exact (Hno w1 rt Heq)]].
    + destruct rt0 as [zk | ok | qk | bk]; try discriminate.
      * destruct rem1 as [| [z2 | o2 | u1 | b2] r']; try discriminate.
        destruct (N.eqb zk 5) eqn:Hz5.
        -- apply N.eqb_eq in Hz5; subst zk.
           destruct (parseChain (u1 + 1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst.
           destruct (IH (u1 + 1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub)
             as [-> [Hr' Hw]].
           split; [reflexivity | split; [cbn [rawRemOf sepToks app]; replace (u1 + 1 - 1) with u1 by lia; rewrite Hr'; reflexivity | exact Hw]].
        -- destruct (N.eqb zk 3) eqn:Hz3.
           ++ apply N.eqb_eq in Hz3; subst zk.
              destruct (parseChain (u1 + 1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
              inversion H; subst.
              destruct (IH (u1 + 1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub)
                as [-> [Hr' Hw]].
              split; [reflexivity | split; [cbn [rawRemOf sepToks app]; replace (u1 + 1 - 1) with u1 by lia; rewrite Hr'; reflexivity | exact Hw]].
           ++ destruct (N.eqb zk 1) eqn:Hz1; [| discriminate].
              apply N.eqb_eq in Hz1; subst zk.
              inversion H; subst.
              split; [reflexivity | split].
              ** cbn [rawRemOf]. replace (u1 + 1 - 1) with u1 by lia. reflexivity.
              ** intros w1 rt Heq; inversion Heq; lia.
      * destruct rem1 as [| [zk | o2 | u1 | b2] r']; try discriminate.
        -- destruct r' as [| [z3 | o3 | u2 | b3] r2]; try discriminate.
           destruct (N.eqb bk 0) eqn:Hb0; [| discriminate].
           destruct (N.eqb zk 1) eqn:Hz1; [| discriminate].
           apply N.eqb_eq in Hb0; apply N.eqb_eq in Hz1; subst bk zk.
           destruct (parseChain (u2 + 1) r2) as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst.
           destruct (IH (u2 + 1) r2 uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub)
             as [-> [Hr2 Hw]].
           split; [reflexivity | split; [cbn [rawRemOf sepToks app]; replace (u2 + 1 - 1) with u2 by lia; rewrite Hr2; reflexivity | exact Hw]].
        -- destruct (N.eqb bk 2) eqn:Hb2; [| discriminate].
           apply N.eqb_eq in Hb2; subst bk.
           destruct (parseChain (u1 + 1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst.
           destruct (IH (u1 + 1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub)
             as [-> [Hr' Hw]].
           split; [reflexivity | split; [cbn [rawRemOf sepToks app]; replace (u1 + 1 - 1) with u1 by lia; rewrite Hr'; reflexivity | exact Hw]].
Qed.

Lemma parseChain_sound (u0 : N) (rem : list RTok)
  (uFirst : N) (pairs : list (SepKind * N)) (lf : ChainLeaf) :
  parseChain u0 rem = Some (uFirst, pairs, lf) ->
  uFirst = u0 /\ rem = rawRemOf pairs lf /\ (forall w1 rt, lf = lf_z2q w1 rt -> 1 <= w1).
Proof.
  exact (parseChain_sound_len (List.length rem) u0 rem uFirst pairs lf (le_n _)).
Qed.

Definition OptGe (opt : option N) (kv : N) : Prop :=
  match opt with
  | None => True
  | Some k0 => kv <= k0
  end.

Lemma minNK_le_iff (a b kv : N) : kv <= minNK a b <-> kv <= a /\ kv <= b.
Proof.
  unfold minNK. destruct (N.leb a b) eqn:Hab.
  - apply N.leb_le in Hab. lia.
  - apply N.leb_gt in Hab. lia.
Qed.

Lemma boundKWith_sound {curK nextK : option N} {u req kv : N} {sd : SDelta}
  (H : boundKWith curK u req sd = Some nextK) (Hge : OptGe nextK kv) :
  OptGe curK kv /\ req <= u /\ (isNeg sd = true -> kv * mag sd + req <= u).
Proof.
  unfold boundKWith in H.
  destruct (N.leb req u) eqn:Hreq; [| discriminate].
  apply N.leb_le in Hreq.
  destruct (isNeg sd) eqn:Hneg.
  - destruct (N.leb 1 (mag sd)) eqn:Hmag.
    + apply N.leb_le in Hmag.
      destruct (N.leb (req + mag sd) u) eqn:Hmin; [| discriminate].
      set (q := N.div (u - req) (mag sd)) in *.
      assert (Hmul : forall x, x <= q -> x * mag sd + req <= u).
      { intros x Hx.
        pose proof (N.div_mod (u - req) (mag sd) ltac:(lia)) as Hdm.
        fold q in Hdm. nia. }
      destruct curK as [k0 |]; inversion H; subst nextK; clear H.
      * apply minNK_le_iff in Hge. destruct Hge as [Hk0 Hq].
        split; [exact Hk0 | split; [exact Hreq | intros _; exact (Hmul kv Hq)]].
      * split; [exact I | split; [exact Hreq | intros _; exact (Hmul kv Hge)]].
    + apply N.leb_gt in Hmag. inversion H; subst nextK.
      split; [exact Hge | split; [exact Hreq | intros _; assert (mag sd = 0) by lia; nia]].
  - inversion H; subst nextK.
    split; [exact Hge | split; [exact Hreq | intro Hc; discriminate Hc]].
Qed.

Lemma decR_z2q_build (uLast w1 kv : N) (rt : list RTok)
  (Hu : 1 <= uLast) (Hkv : kv <= w1) :
  decR (buildChainTail [] kv (lf_z2q w1 rt) uLast) =
  repQ uLast (S0 :: S0 :: repQ (w1 - kv) (decR rt)).
Proof.
  cbn [buildChainTail].
  destruct (N.eqb w1 kv) eqn:Hwk.
  - apply N.eqb_eq in Hwk; subst kv.
    rewrite decR_pushQR, !decR_pushZeroR.
    replace (uLast - 1 + 1) with uLast by lia.
    replace (w1 - w1) with 0 by lia.
    rewrite repQ_0. reflexivity.
  - apply N.eqb_neq in Hwk.
    rewrite decR_pushQR; cbn [decR].
    replace (uLast - 1 + 1) with uLast by lia.
    replace (w1 - kv - 1 + 1) with (w1 - kv) by lia.
    reflexivity.
Qed.

Lemma max_const_le (c x : N) : c <= (if N.leb c x then x else c).
Proof.
  destruct (N.leb c x) eqn:Hcx; [apply N.leb_le in Hcx; lia | lia].
Qed.

Lemma foldChainRTL_sound :
  forall (pairs : list (SepKind * N)) (lf : ChainLeaf)
    (nPos nNeg : N) (optK : option N) (items : list (SepKind * N * SDelta)) (kv : N),
    (forall w1 rt, lf = lf_z2q w1 rt -> 1 <= w1) ->
    1 <= kv ->
    foldChainRTL pairs lf = Some (nPos, nNeg, optK, items) ->
    OptGe optK kv ->
    nNeg <= nPos /\ 1 <= nPos /\
    exists innerBitsOut : list Sym,
      SafeProg 1 (1 + kv * (nPos - nNeg)) (kv * nPos) (kv * nNeg)
        (decR (rawRemOf pairs lf)) innerBitsOut /\
      forall uCur : N, 1 <= uCur ->
        decR (buildChainTail items kv lf uCur) = repQ uCur innerBitsOut.
Proof.
  induction pairs as [| [sep uNext] tl IH];
    intros lf nPosOut nNegOut optKOut itemsOut kv Hlf Hkv Hfold Hge.
  - cbn [foldChainRTL] in Hfold.
    destruct lf as [w1 rt | | | | |]; injection Hfold as <- <- <- <-.
    + pose proof (Hlf w1 rt eq_refl) as Hw1.
      cbn [OptGe] in Hge.
      split; [nia | split; [nia |]].
      exists (S0 :: S0 :: repQ (w1 - kv) (decR rt)). split.
      * pose proof (safeProg_z2q_iter kv (w1 - kv) (decR rt)) as Hp.
        replace (kv + (w1 - kv)) with w1 in Hp by nia.
        cbn [rawRemOf decR].
        replace (w1 - 1 + 1) with w1 by nia.
        replace (1 - 0) with 1 by nia.
        exact Hp.
      * intros uCur Hu. exact (decR_z2q_build uCur w1 kv rt Hu Hge).
    + split; [nia | split; [nia |]].
      exists capA0. split.
      * exact (SP_iter safeProg_cap1_one kv).
      * intros uCur Hu. cbn [buildChainTail decR].
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + split; [nia | split; [nia |]].
      exists capA3. split.
      * exact (SP_iter safeProg_cap2_one kv).
      * intros uCur Hu. cbn [buildChainTail decR].
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + split; [nia | split; [nia |]].
      exists capA2. split.
      * exact (SP_iter safeProg_capZ21_one kv).
      * intros uCur Hu. cbn [buildChainTail decR].
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + split; [nia | split; [nia |]].
      exists capA1. split.
      * exact (SP_iter safeProg_capZ22_one kv).
      * intros uCur Hu. cbn [buildChainTail decR].
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + split; [nia | split; [nia |]].
      exists capB0. split.
      * exact (SP_iter safeProg_capB_one kv).
      * intros uCur Hu. cbn [buildChainTail decR].
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
  - cbn [foldChainRTL] in Hfold.
    destruct (foldChainRTL tl lf) as [[[[nPos nNeg] curK] acc] |] eqn:Hsub; [| discriminate].
    destruct sep.
    + destruct (boundKWith curK uNext (if N.leb 2 (chainBaseReq tl lf) then chainBaseReq tl lf else 2)
                  (sdeltaOfPosNeg nPos nNeg)) as [nextK |] eqn:Hbnd; [| discriminate].
      injection Hfold as <- <- <- <-.
      destruct (boundKWith_sound Hbnd Hge) as [HcurK [Hreq_u _]].
      destruct (IH lf nPos nNeg curK acc kv Hlf Hkv Hsub HcurK)
        as [Hle_pn [Hpos_p [subBits [HSafe HBuild]]]].
      pose proof (max_const_le 2 (chainBaseReq tl lf)) as H2le.
      assert (HuNext2 : 2 <= uNext) by nia.
      assert (Hsd : sdeltaOfPosNeg nPos nNeg = mkSDelta false (nPos - nNeg)).
      { unfold sdeltaOfPosNeg.
        destruct (N.leb nNeg nPos) eqn:He; [reflexivity | apply N.leb_gt in He; lia]. }
      set (uNextNew := uNext + kv * (nPos - nNeg)).
      pose proof (SP_liftZ6 HSafe (uNext - 1) ltac:(nia)) as Hlft.
      replace ((uNext - 1) + 1) with uNext in Hlft by nia.
      replace ((uNext - 1) + (1 + kv * (nPos - nNeg))) with uNextNew in Hlft by nia.
      replace (kv * nPos + kv * nNeg) with (kv * (nPos + nNeg)) in Hlft by nia.
      split; [nia | split; [nia |]].
      exists (repZero 6 (repQ uNextNew subBits)). split.
      * replace ((nPos + nNeg) - (nPos + nNeg)) with 0 by nia.
        replace (1 + kv * 0) with 1 by nia.
        cbn [rawRemOf sepToks app decR].
        replace (uNext - 1 + 1) with uNext by nia.
        exact Hlft.
      * intros uCur HuCur.
        cbn [buildChainTail]. rewrite Hsd; cbn [applyDeltaK isNeg mag decR].
        fold uNextNew. rewrite (HBuild uNextNew ltac:(nia)).
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + destruct (boundKWith curK uNext (if N.leb 2 (chainBaseReq tl lf) then chainBaseReq tl lf else 2)
                  (sdeltaOfPosNeg nPos nNeg)) as [nextK |] eqn:Hbnd; [| discriminate].
      injection Hfold as <- <- <- <-.
      destruct (boundKWith_sound Hbnd Hge) as [HcurK [Hreq_u _]].
      destruct (IH lf nPos nNeg curK acc kv Hlf Hkv Hsub HcurK)
        as [Hle_pn [Hpos_p [subBits [HSafe HBuild]]]].
      pose proof (max_const_le 2 (chainBaseReq tl lf)) as H2le.
      assert (HuNext2 : 2 <= uNext) by nia.
      assert (Hsd : sdeltaOfPosNeg nPos nNeg = mkSDelta false (nPos - nNeg)).
      { unfold sdeltaOfPosNeg.
        destruct (N.leb nNeg nPos) eqn:He; [reflexivity | apply N.leb_gt in He; lia]. }
      set (uNextNew := uNext + kv * (nPos - nNeg)).
      pose proof (SP_liftBA3 HSafe (uNext - 1)) as Hlft.
      replace ((uNext - 1) + 1) with uNext in Hlft by nia.
      replace ((uNext - 1) + (1 + kv * (nPos - nNeg))) with uNextNew in Hlft by nia.
      replace (kv * nPos + kv * nNeg) with (kv * (nPos + nNeg)) in Hlft by nia.
      split; [nia | split; [nia |]].
      exists (repBA 3 (repQ uNextNew subBits)). split.
      * replace ((nPos + nNeg) - (nPos + nNeg)) with 0 by nia.
        replace (1 + kv * 0) with 1 by nia.
        cbn [rawRemOf sepToks app decR].
        replace (uNext - 1 + 1) with uNext by nia.
        exact Hlft.
      * intros uCur HuCur.
        cbn [buildChainTail]. rewrite Hsd; cbn [applyDeltaK isNeg mag decR].
        fold uNextNew. rewrite (HBuild uNextNew ltac:(nia)).
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + destruct (boundKWith curK uNext (if N.leb 3 (chainBaseReq tl lf) then chainBaseReq tl lf else 3)
                  (mkSDelta true (nPos + 3 * nNeg))) as [nextK |] eqn:Hbnd; [| discriminate].
      injection Hfold as <- <- <- <-.
      destruct (boundKWith_sound Hbnd Hge) as [HcurK [Hreq_u Hneg_u]].
      destruct (IH lf nPos nNeg curK acc kv Hlf Hkv Hsub HcurK)
        as [Hle_pn [Hpos_p [subBits [HSafe HBuild]]]].
      pose proof (max_const_le 3 (chainBaseReq tl lf)) as H3le.
      pose proof (Hneg_u eq_refl) as Hmag_b; cbn [mag] in Hmag_b.
      set (uNextNew := uNext - kv * (nPos + 3 * nNeg)).
      assert (HuEnd1 : 1 <= uNextNew) by nia.
      pose proof (SP_liftZ4 HSafe uNextNew HuEnd1) as Hlft.
      replace (uNextNew + kv * nPos + 3 * (kv * nNeg)) with uNext in Hlft by nia.
      split; [nia | split; [nia |]].
      exists (S0 :: S0 :: S0 :: S0 :: repQ uNextNew subBits). split.
      * replace (1 + kv * (3 * (nPos + nNeg) - (nPos + nNeg)))
          with (1 + 2 * (kv * nPos + kv * nNeg)) by nia.
        replace (kv * (3 * (nPos + nNeg))) with (3 * (kv * nPos + kv * nNeg)) by nia.
        replace (kv * (nPos + nNeg)) with (kv * nPos + kv * nNeg) by nia.
        cbn [rawRemOf sepToks app decR].
        replace (uNext - 1 + 1) with uNext by nia.
        exact Hlft.
      * intros uCur HuCur.
        cbn [buildChainTail applyDeltaK isNeg mag decR].
        fold uNextNew. rewrite (HBuild uNextNew HuEnd1).
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
    + destruct (boundKWith curK uNext (if N.leb 3 (chainBaseReq tl lf) then chainBaseReq tl lf else 3)
                  (mkSDelta true (nPos + 3 * nNeg))) as [nextK |] eqn:Hbnd; [| discriminate].
      injection Hfold as <- <- <- <-.
      destruct (boundKWith_sound Hbnd Hge) as [HcurK [Hreq_u Hneg_u]].
      destruct (IH lf nPos nNeg curK acc kv Hlf Hkv Hsub HcurK)
        as [Hle_pn [Hpos_p [subBits [HSafe HBuild]]]].
      pose proof (max_const_le 3 (chainBaseReq tl lf)) as H3le.
      pose proof (Hneg_u eq_refl) as Hmag_b; cbn [mag] in Hmag_b.
      set (uNextNew := uNext - kv * (nPos + 3 * nNeg)).
      assert (HuEnd3 : 3 <= uNextNew) by nia.
      pose proof (SP_liftBA1Z2 HSafe uNextNew HuEnd3) as Hlft.
      replace (uNextNew + kv * nPos + 3 * (kv * nNeg)) with uNext in Hlft by nia.
      split; [nia | split; [nia |]].
      exists (S0 :: S1 :: S0 :: S0 :: repQ uNextNew subBits). split.
      * replace (1 + kv * (3 * (nPos + nNeg) - (nPos + nNeg)))
          with (1 + 2 * (kv * nPos + kv * nNeg)) by nia.
        replace (kv * (3 * (nPos + nNeg))) with (3 * (kv * nPos + kv * nNeg)) by nia.
        replace (kv * (nPos + nNeg)) with (kv * nPos + kv * nNeg) by nia.
        cbn [rawRemOf sepToks app decR].
        replace (uNext - 1 + 1) with uNext by nia.
        exact Hlft.
      * intros uCur HuCur.
        cbn [buildChainTail applyDeltaK isNeg mag decR].
        fold uNextNew. rewrite (HBuild uNextNew ltac:(nia)).
        replace (uCur - 1 + 1) with uCur by nia. reflexivity.
Qed.

Lemma stepChainK_sound (b b' : BaseState) :
  stepChainK b = Some b' ->
  encodeBase b -[ tm ]->+ encodeBase b'.
Proof.
  destruct b as [[|] ls rs]; unfold stepChainK; cbn [mode l r]; [discriminate |].
  destruct (isZeroHeadL ls) eqn:Hz; [| discriminate].
  destruct rs as [| [k0 | k0 | u0_0 | k0] rem]; try discriminate.
  destruct (parseChain (u0_0 + 1) rem) as [[[uFirst pairs] lf] |] eqn:Hp; [| discriminate].
  destruct (foldChainRTL pairs lf) as [[[[nPos nNeg] curK] items] |] eqn:Hf; [| discriminate].
  destruct (boundKWith curK uFirst (chainReq0 pairs lf) (mkSDelta true (2 * nNeg)))
    as [[kVal |] |] eqn:Hb0; try discriminate.
  destruct (N.leb 1 kVal) eqn:Hk1; [| discriminate].
  intro H; injection H as <-.
  apply N.leb_le in Hk1.
  destruct (parseChain_sound (u0_0 + 1) rem uFirst pairs lf Hp) as [-> [HremEq Hlf_w1]].
  destruct (boundKWith_sound Hb0 (N.le_refl kVal)) as [HcurK [Hreq0 Hneg0]].
  destruct (foldChainRTL_sound pairs lf nPos nNeg curK items kVal Hlf_w1 Hk1 Hf HcurK)
    as [Hle_pn [Hpos_p [innerBitsOut [HSafe HBuild]]]].
  assert (Hreq0_ge2 : 2 <= chainReq0 pairs lf)
    by (destruct pairs, lf; cbn [chainReq0]; lia).
  pose proof (Hneg0 eq_refl) as Hmag0; cbn [mag] in Hmag0.
  set (u0New := applyDeltaK (u0_0 + 1) kVal (mkSDelta true (2 * nNeg))).
  assert (Hu0New_eq : u0New = (u0_0 + 1) - kVal * (2 * nNeg)) by reflexivity.
  assert (Hu0New_ge2 : 2 <= u0New) by nia.
  assert (Hpos_tot : 1 <= kVal * nPos + kVal * nNeg) by nia.
  pose proof (SP_runTopPlus HSafe Hpos_tot u0New (decL (snd (popL ls))) Hu0New_ge2) as Hrun.
  replace (u0New + 2 * (kVal * nNeg)) with (u0_0 + 1) in Hrun by nia.
  rewrite <- HremEq in Hrun.
  pose proof (isZeroHeadL_sound ls Hz) as Hl0.
  destruct (decL_popL ls) as [_ Hpl2].
  unfold encodeBase; cbn [mode l r].
  change (decR (R_q u0_0 :: rem)) with (repQ (u0_0 + 1) (decR rem)).
  fold u0New.
  rewrite (mEncR_zero_head_expand D ls _ Hl0), <- Hpl2.
  rewrite decL_pushZeroL, decL_pushPL, (HBuild u0New ltac:(nia)).
  replace (kVal * (nPos + nNeg) - 1 + 1) with (kVal * nPos + kVal * nNeg) by nia.
  exact Hrun.
Qed.

Lemma stepAutoK_sound (b b' : BaseState) :
  stepAutoK b = Some b' ->
  encodeBase b -[ tm ]->+ encodeBase b'.
Proof.
  unfold stepAutoK.
  destruct (stepChainK b) as [bc |] eqn:Hc.
  - intro H; inversion H; subst b'. exact (stepChainK_sound b bc Hc).
  - exact (stepBaseK_sound b b').
Qed.

Lemma iter_stepAutoOpt_None (p : positive) :
  Pos.iter stepAutoOpt None p = None.
Proof.
  induction p as [p IHp | p IHp |]; cbn [Pos.iter]; rewrite ?IHp; reflexivity.
Qed.

Lemma iter_stepAutoOpt_sound (p : positive) :
  forall (st out : BaseState),
    Pos.iter stepAutoOpt (Some st) p = Some out ->
    encodeBase st -[ tm ]->* encodeBase out.
Proof.
  induction p as [p IHp | p IHp |]; intros st out Hiter; cbn [Pos.iter] in Hiter.
  - destruct (Pos.iter stepAutoOpt (Some st) p) as [b1 |] eqn:Hb1;
      [| rewrite iter_stepAutoOpt_None in Hiter; discriminate].
    destruct (Pos.iter stepAutoOpt (Some b1) p) as [b2 |] eqn:Hb2;
      [| discriminate].
    eapply evstep_trans; [exact (IHp st b1 Hb1) |].
    eapply evstep_trans; [exact (IHp b1 b2 Hb2) |].
    exact (progress_evstep _ _ _ (stepAutoK_sound b2 out Hiter)).
  - destruct (Pos.iter stepAutoOpt (Some st) p) as [b1 |] eqn:Hb1;
      [| rewrite iter_stepAutoOpt_None in Hiter; discriminate].
    eapply evstep_trans; [exact (IHp st b1 Hb1) | exact (IHp b1 out Hiter)].
  - exact (progress_evstep _ _ _ (stepAutoK_sound st out Hiter)).
Qed.

Lemma runStepsPos_sound (p : positive) (st out : BaseState) :
  runStepsPos p st = Some out ->
  encodeBase st -[ tm ]->* encodeBase out.
Proof.
  exact (iter_stepAutoOpt_sound p st out).
Qed.

(** ** Section 5: Symbolic Affine Evaluator ([SymNat]) & Commutation with [evalSym] *)

Record SymNat : Type := mkSym {
  sa : N;
  sb : N
}.

Inductive SymLTok : Type :=
| SL_z (k : SymNat)
| SL_o (k : SymNat)
| SL_p (k : SymNat)
| SL_ab (k : SymNat).

Inductive SymRTok : Type :=
| SR_z (k : SymNat)
| SR_o (k : SymNat)
| SR_q (k : SymNat)
| SR_ba (k : SymNat).

Record SymState : Type := mkSymState {
  smode : Mode;
  sl : list SymLTok;
  sr : list SymRTok
}.

Definition symNatBeq (x y : SymNat) : bool :=
  if N.eqb (sa x) (sa y) then N.eqb (sb x) (sb y) else false.

Definition symLTokBeq (x y : SymLTok) : bool :=
  match x, y with
  | SL_z a, SL_z b => symNatBeq a b
  | SL_o a, SL_o b => symNatBeq a b
  | SL_p a, SL_p b => symNatBeq a b
  | SL_ab a, SL_ab b => symNatBeq a b
  | _, _ => false
  end.

Definition symRTokBeq (x y : SymRTok) : bool :=
  match x, y with
  | SR_z a, SR_z b => symNatBeq a b
  | SR_o a, SR_o b => symNatBeq a b
  | SR_q a, SR_q b => symNatBeq a b
  | SR_ba a, SR_ba b => symNatBeq a b
  | _, _ => false
  end.

Fixpoint listSymLBeq (xs ys : list SymLTok) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if symLTokBeq x y then listSymLBeq xs' ys' else false
  | _, _ => false
  end.

Fixpoint listSymRBeq (xs ys : list SymRTok) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if symRTokBeq x y then listSymRBeq xs' ys' else false
  | _, _ => false
  end.

Definition symStateBeq (a b : SymState) : bool :=
  if modeBeq (smode a) (smode b) then
    if listSymLBeq (sl a) (sl b) then listSymRBeq (sr a) (sr b) else false
  else false.

Lemma symNatBeq_eq (x y : SymNat) : symNatBeq x y = true -> x = y.
Proof.
  destruct x as [xa xb], y as [ya yb]; unfold symNatBeq; cbn [sa sb].
  destruct (N.eqb xa ya) eqn:Ha; [| discriminate].
  intro Hb. apply N.eqb_eq in Ha; apply N.eqb_eq in Hb; subst; reflexivity.
Qed.

Lemma symNatBeq_false (x y : SymNat) : symNatBeq x y = false -> x <> y.
Proof.
  destruct x as [xa xb], y as [ya yb]; unfold symNatBeq; cbn [sa sb].
  destruct (N.eqb xa ya) eqn:Ha.
  - intro Hb; apply N.eqb_neq in Hb; congruence.
  - intros _; apply N.eqb_neq in Ha; congruence.
Qed.

Lemma symLTokBeq_eq (x y : SymLTok) : symLTokBeq x y = true -> x = y.
Proof.
  destruct x, y; cbn [symLTokBeq]; try discriminate;
    intro H; rewrite (symNatBeq_eq _ _ H); reflexivity.
Qed.

Lemma symRTokBeq_eq (x y : SymRTok) : symRTokBeq x y = true -> x = y.
Proof.
  destruct x, y; cbn [symRTokBeq]; try discriminate;
    intro H; rewrite (symNatBeq_eq _ _ H); reflexivity.
Qed.

Lemma listSymLBeq_eq : forall (xs ys : list SymLTok), listSymLBeq xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [listSymLBeq] in H;
    try reflexivity; try discriminate.
  destruct (symLTokBeq x y) eqn:Hxy; [| discriminate].
  f_equal; [exact (symLTokBeq_eq _ _ Hxy) | exact (IH _ H)].
Qed.

Lemma listSymRBeq_eq : forall (xs ys : list SymRTok), listSymRBeq xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H; cbn [listSymRBeq] in H;
    try reflexivity; try discriminate.
  destruct (symRTokBeq x y) eqn:Hxy; [| discriminate].
  f_equal; [exact (symRTokBeq_eq _ _ Hxy) | exact (IH _ H)].
Qed.

Lemma symStateBeq_eq (a b : SymState) : symStateBeq a b = true -> a = b.
Proof.
  destruct a as [ma la ra], b as [mb lb rb]; unfold symStateBeq; cbn [smode sl sr].
  destruct (modeBeq ma mb) eqn:Hm; [| discriminate].
  destruct (listSymLBeq la lb) eqn:Hl; [| discriminate].
  intro Hr.
  f_equal; [exact (modeBeq_eq _ _ Hm) | exact (listSymLBeq_eq _ _ Hl) | exact (listSymRBeq_eq _ _ Hr)].
Qed.

Definition evalSym (m : N) (x : SymNat) : N :=
  sa x * m + sb x.

Definition evalSymLTok (m : N) (t : SymLTok) : LTok :=
  match t with
  | SL_z x => L_z (evalSym m x)
  | SL_o x => L_o (evalSym m x)
  | SL_p x => L_p (evalSym m x)
  | SL_ab x => L_ab (evalSym m x)
  end.

Definition evalSymRTok (m : N) (t : SymRTok) : RTok :=
  match t with
  | SR_z x => R_z (evalSym m x)
  | SR_o x => R_o (evalSym m x)
  | SR_q x => R_q (evalSym m x)
  | SR_ba x => R_ba (evalSym m x)
  end.

Fixpoint evalSymL (m : N) (xs : list SymLTok) : list LTok :=
  match xs with
  | [] => []
  | x :: xs' => evalSymLTok m x :: evalSymL m xs'
  end.

Fixpoint evalSymR (m : N) (xs : list SymRTok) : list RTok :=
  match xs with
  | [] => []
  | x :: xs' => evalSymRTok m x :: evalSymR m xs'
  end.

Definition evalSymState (m : N) (s : SymState) : BaseState :=
  mkBase (smode s) (evalSymL m (sl s)) (evalSymR m (sr s)).

Definition symAdd1 (x y : SymNat) : SymNat :=
  mkSym (sa x + sa y) (sb x + 1 + sb y).

Definition symInc (x : SymNat) : SymNat :=
  mkSym (sa x) (sb x + 1).

Definition symCases01 (x : SymNat) : option (option SymNat) :=
  if N.eqb (sb x) 0 then
    if N.eqb (sa x) 0 then Some None else None
  else Some (Some (mkSym (sa x) (sb x - 1))).

Definition symCases012 (x : SymNat) : option (bool + SymNat) :=
  if N.eqb (sb x) 0 then
    if N.eqb (sa x) 0 then Some (inl false) else None
  else if N.eqb (sb x) 1 then
    if N.eqb (sa x) 0 then Some (inl true) else None
  else Some (inr (mkSym (sa x) (sb x - 2))).

Definition symPushPL (k : SymNat) (ls : list SymLTok) : list SymLTok :=
  match ls with
  | SL_p m :: rest => SL_p (symAdd1 k m) :: rest
  | rest => SL_p k :: rest
  end.

Definition symPushABL (k : SymNat) (ls : list SymLTok) : list SymLTok :=
  match ls with
  | SL_ab m :: rest => SL_ab (symAdd1 k m) :: rest
  | rest => SL_ab k :: rest
  end.

Definition symPushOL (k : SymNat) (ls : list SymLTok) : list SymLTok :=
  match ls with
  | SL_o m :: rest => SL_o (symAdd1 k m) :: rest
  | rest => SL_o k :: rest
  end.

Definition symPushZeroL (ls : list SymLTok) : option (list SymLTok) :=
  match ls with
  | SL_o x :: rest =>
    match symCases012 x with
    | Some (inl false) => Some (SL_z (mkSym 0 0) :: SL_o (mkSym 0 0) :: rest)
    | Some (inl true) => Some (symPushPL (mkSym 0 0) rest)
    | Some (inr mv) => Some (SL_p (mkSym 0 0) :: SL_o mv :: rest)
    | None => None
    end
  | SL_z m :: rest => Some (SL_z (symInc m) :: rest)
  | rest => Some (SL_z (mkSym 0 0) :: rest)
  end.

Definition symPushOneL (ls : list SymLTok) : option (list SymLTok) :=
  match ls with
  | SL_z x :: rest =>
    match symCases01 x with
    | Some None => Some (symPushABL (mkSym 0 0) rest)
    | Some (Some mv) => Some (SL_ab (mkSym 0 0) :: SL_z mv :: rest)
    | None => None
    end
  | SL_o m :: rest => Some (SL_o (symInc m) :: rest)
  | rest => Some (SL_o (mkSym 0 0) :: rest)
  end.

Definition symPopL (ls : list SymLTok) : option (bool * list SymLTok) :=
  match ls with
  | [] => Some (false, [])
  | SL_z x :: rest =>
    match symCases01 x with
    | Some None => Some (false, rest)
    | Some (Some mv) => Some (false, SL_z mv :: rest)
    | None => None
    end
  | SL_o x :: rest =>
    match symCases01 x with
    | Some None => Some (true, rest)
    | Some (Some mv) => Some (true, SL_o mv :: rest)
    | None => None
    end
  | SL_p x :: rest =>
    match symCases01 x with
    | Some None => Some (false, symPushOL (mkSym 0 1) rest)
    | Some (Some mv) => Some (false, symPushOL (mkSym 0 1) (SL_p mv :: rest))
    | None => None
    end
  | SL_ab x :: rest =>
    match symCases01 x with
    | Some None =>
      match symPushZeroL rest with
      | Some r' => Some (true, r')
      | None => None
      end
    | Some (Some mv) =>
      match symPushZeroL (SL_ab mv :: rest) with
      | Some r' => Some (true, r')
      | None => None
      end
    | None => None
    end
  end.

Definition symPushQR (k : SymNat) (rs : list SymRTok) : list SymRTok :=
  match rs with
  | SR_q m :: rest => SR_q (symAdd1 k m) :: rest
  | rest => SR_q k :: rest
  end.

Definition symPushBAR (k : SymNat) (rs : list SymRTok) : list SymRTok :=
  match rs with
  | SR_ba m :: rest => SR_ba (symAdd1 k m) :: rest
  | rest => SR_ba k :: rest
  end.

Definition symPushZRawR (k : SymNat) (rs : list SymRTok) : list SymRTok :=
  match rs with
  | SR_z m :: rest => SR_z (symAdd1 k m) :: rest
  | rest => SR_z k :: rest
  end.

Definition symPushZeroR (rs : list SymRTok) : option (list SymRTok) :=
  match rs with
  | SR_o x :: rest =>
    match symCases01 x with
    | Some None => Some (symPushBAR (mkSym 0 0) rest)
    | Some (Some mv) => Some (SR_ba (mkSym 0 0) :: SR_o mv :: rest)
    | None => None
    end
  | SR_ba x :: rest =>
    match symCases01 x with
    | Some None => Some (symPushQR (mkSym 0 0) rest)
    | Some (Some mv) => Some (SR_q (mkSym 0 0) :: SR_ba mv :: rest)
    | None => None
    end
  | SR_z m :: rest => Some (SR_z (symInc m) :: rest)
  | rest => Some (SR_z (mkSym 0 0) :: rest)
  end.

Definition symPushOneR (rs : list SymRTok) : list SymRTok :=
  match rs with
  | SR_o m :: rest => SR_o (symInc m) :: rest
  | rest => SR_o (mkSym 0 0) :: rest
  end.

Definition symPushZeroR2 (rs : list SymRTok) : option (list SymRTok) :=
  match symPushZeroR rs with
  | Some r1 => symPushZeroR r1
  | None => None
  end.

Definition symPushZerosAtLeast1R (cnt : N) (rs : list SymRTok) : option (list SymRTok) :=
  if N.eqb cnt 0 then symPushZeroR rs
  else if N.eqb cnt 1 then symPushZeroR2 rs
  else
    match symPushZeroR2 rs with
    | Some r2 => Some (symPushZRawR (mkSym 0 (cnt - 2)) r2)
    | None => None
    end.

Definition symPushZerosAtLeast2R (cnt : N) (rs : list SymRTok) : option (list SymRTok) :=
  if N.eqb cnt 0 then symPushZeroR2 rs
  else
    match symPushZeroR2 rs with
    | Some r2 => Some (symPushZRawR (mkSym 0 (cnt - 1)) r2)
    | None => None
    end.

Definition symPush10RepeatR (cnt : SymNat) (rs : list SymRTok) : option (list SymRTok) :=
  match symCases01 cnt, symPushZeroR rs with
  | Some None, Some r0 => Some (symPushOneR r0)
  | Some (Some mv), Some r0 => Some (symPushOneR (symPushBAR mv r0))
  | _, _ => None
  end.

Definition symPush100RepeatR (cnt : SymNat) (rs : list SymRTok) : option (list SymRTok) :=
  match symCases01 cnt, symPushZeroR2 rs with
  | Some None, Some r2 => Some (symPushOneR r2)
  | Some (Some mv), Some r2 => Some (symPushOneR (symPushQR mv r2))
  | _, _ => None
  end.

Definition symPopR (rs : list SymRTok) : option (bool * list SymRTok) :=
  match rs with
  | [] => Some (false, [])
  | SR_z x :: rest =>
    match symCases01 x with
    | Some None => Some (false, rest)
    | Some (Some mv) => Some (false, SR_z mv :: rest)
    | None => None
    end
  | SR_o x :: rest =>
    match symCases01 x with
    | Some None => Some (true, rest)
    | Some (Some mv) => Some (true, SR_o mv :: rest)
    | None => None
    end
  | SR_q x :: rest =>
    match symCases01 x with
    | Some None => Some (false, symPushBAR (mkSym 0 0) rest)
    | Some (Some mv) => Some (false, symPushBAR (mkSym 0 0) (SR_q mv :: rest))
    | None => None
    end
  | SR_ba x :: rest =>
    match symCases01 x with
    | Some None => Some (false, symPushOneR rest)
    | Some (Some mv) => Some (false, symPushOneR (SR_ba mv :: rest))
    | None => None
    end
  end.

Fixpoint symSplitLeadingOnesL (ls : list SymLTok) : option (N * list SymLTok) :=
  match ls with
  | [] => Some (0, [])
  | SL_o x :: rest =>
    if N.eqb (sa x) 0 then
      match symSplitLeadingOnesL rest with
      | Some ih => Some ((sb x + 1) + fst ih, snd ih)
      | None => None
      end
    else None
  | SL_ab x :: rest =>
    match symCases01 x with
    | Some None =>
      match symPushZeroL rest with
      | Some r' => Some (1, r')
      | None => None
      end
    | Some (Some mv) =>
      match symPushZeroL (SL_ab mv :: rest) with
      | Some r' => Some (1, r')
      | None => None
      end
    | None => None
    end
  | SL_z k :: rest => Some (0, SL_z k :: rest)
  | SL_p k :: rest => Some (0, SL_p k :: rest)
  end.

Fixpoint symSweepAL (ls : list SymLTok) (rs : list SymRTok) : option (list SymLTok * list SymRTok) :=
  match ls with
  | SL_ab k :: rest =>
    match symPush10RepeatR k rs with
    | Some r1 => symSweepAL rest r1
    | None => None
    end
  | SL_o x :: rest =>
    match symCases01 x with
    | None => None
    | Some (Some _) => Some (ls, rs)
    | Some None =>
      match rest with
      | [] =>
        match symPush10RepeatR (mkSym 0 0) rs with
        | Some r1 => Some ([], r1)
        | None => None
        end
      | SL_z zx :: rest2 =>
        match symCases01 zx with
        | Some None =>
          match symPush10RepeatR (mkSym 0 0) rs with
          | Some r1 => symSweepAL rest2 r1
          | None => None
          end
        | Some (Some mv) =>
          match symPush10RepeatR (mkSym 0 0) rs with
          | Some r1 => Some (SL_z mv :: rest2, r1)
          | None => None
          end
        | None => None
        end
      | SL_p px :: rest2 =>
        match symCases01 px with
        | Some None =>
          match symPush10RepeatR (mkSym 0 0) rs with
          | Some r1 => Some (symPushOL (mkSym 0 1) rest2, r1)
          | None => None
          end
        | Some (Some mv) =>
          match symPush10RepeatR (mkSym 0 0) rs with
          | Some r1 => Some (SL_o (mkSym 0 1) :: SL_p mv :: rest2, r1)
          | None => None
          end
        | None => None
        end
      | _ => Some (ls, rs)
      end
    end
  | _ => Some (ls, rs)
  end.

Definition symIsZeroHeadL (ls : list SymLTok) : bool :=
  match ls with
  | [] => true
  | SL_z _ :: _ => true
  | SL_p _ :: _ => true
  | _ => false
  end.

Definition symStepALZeroFallback (ls : list SymLTok) (rs : list SymRTok) : option SymState :=
  match symPopR rs, symPopL ls with
  | Some (false, r0), Some (_, lt) =>
    match symPopL lt with
    | Some (false, l1) =>
      match symPushZeroR (symPushOneR r0) with
      | Some rz => Some (mkSymState mAL l1 (symPushOneR rz))
      | None => None
      end
    | Some (true, l1) =>
      match symSplitLeadingOnesL l1 with
      | Some (spCnt, spL) =>
        match symPopL spL, symPushZerosAtLeast2R spCnt (symPushOneR r0) with
        | Some (_, l3), Some rz => Some (mkSymState mAL l3 (symPushOneR rz))
        | _, _ => None
        end
      | None => None
      end
    | None => None
    end
  | Some (true, r0), Some (_, lt) =>
    match symPopR r0 with
    | Some (false, r1) =>
      match symPopR r1, symPushZeroL (symPushOL (mkSym 0 1) lt) with
      | Some (b2, r2), Some lBase =>
        let lOutOpt := if b2 then symPushOneL lBase else symPushZeroL lBase in
        match lOutOpt with
        | Some lOut => Some (mkSymState mDR lOut r2)
        | None => None
        end
      | _, _ => None
      end
    | _ => None
    end
  | _, _ => None
  end.

Definition symStepALElse (ls : list SymLTok) (rs : list SymRTok) : option SymState :=
  if symIsZeroHeadL ls then
    match rs with
    | SR_o ox :: SR_z zx :: SR_q k :: rt =>
      match symCases01 ox, symCases01 zx with
      | Some None, Some None =>
        match symPopL ls, symPushZeroR rt with
        | Some (_, lt), Some rz =>
          match symPushZeroL (symPushPL k lt) with
          | Some lOut => Some (mkSymState mAL lOut (symPushOneR rz))
          | None => None
          end
        | _, _ => None
        end
      | Some (Some _), _ => symStepALZeroFallback ls rs
      | Some None, Some (Some _) => symStepALZeroFallback ls rs
      | _, _ => None
      end
    | SR_o ox :: SR_q qx :: SR_ba k :: rt =>
      match symCases01 ox, symCases01 qx with
      | Some None, Some None =>
        match symPopL ls, symPushZeroR rt with
        | Some (_, lt), Some rz =>
          let ok := mkSym (2 * sa k) (2 * sb k + 3) in
          match symPushZeroL (symPushOL ok lt) with
          | Some lOut => Some (mkSymState mAL lOut (symPushOneR rz))
          | None => None
          end
        | _, _ => None
        end
      | Some (Some _), _ => symStepALZeroFallback ls rs
      | Some None, Some (Some _) => symStepALZeroFallback ls rs
      | _, _ => None
      end
    | _ => symStepALZeroFallback ls rs
    end
  else
    match symSweepAL ls rs with
    | None => None
    | Some (swL, swR) =>
      match symPopL swL with
      | None => None
      | Some (true, l0) =>
        match symPopL l0 with
        | Some (false, l1) =>
          match symPush10RepeatR (mkSym 0 0) swR with
          | Some rOut => Some (mkSymState mAL l1 rOut)
          | None => None
          end
        | Some (true, l1) =>
          match symSplitLeadingOnesL l1 with
          | Some (spCnt, spL) =>
            match symPopL spL, symPushZerosAtLeast2R spCnt swR with
            | Some (_, l3), Some rz => Some (mkSymState mAL l3 (symPushOneR rz))
            | _, _ => None
            end
          | None => None
          end
        | None => None
        end
      | Some (false, l0) =>
        match symPopR swR with
        | Some (false, r0) =>
          match symPopL l0 with
          | Some (false, l1) =>
            match symPushZeroR (symPushOneR r0) with
            | Some rz => Some (mkSymState mAL l1 (symPushOneR rz))
            | None => None
            end
          | Some (true, l1) =>
            match symSplitLeadingOnesL l1 with
            | Some (spCnt, spL) =>
              match symPopL spL, symPushZerosAtLeast2R spCnt (symPushOneR r0) with
              | Some (_, l3), Some rz => Some (mkSymState mAL l3 (symPushOneR rz))
              | _, _ => None
              end
            | None => None
            end
          | None => None
          end
        | Some (true, r0) =>
          match symPopR r0 with
          | Some (false, r1) =>
            match symPopR r1, symPushZeroL (symPushOL (mkSym 0 1) l0) with
            | Some (b2, r2), Some lBase =>
              let lOutOpt := if b2 then symPushOneL lBase else symPushZeroL lBase in
              match lOutOpt with
              | Some lOut => Some (mkSymState mDR lOut r2)
              | None => None
              end
            | _, _ => None
            end
          | _ => None
          end
        | None => None
        end
      end
    end.

Definition symStepDRFallback (ls : list SymLTok) (rs : list SymRTok) : option SymState :=
  match symPopR rs with
  | None => None
  | Some (true, r0) =>
    match symSplitLeadingOnesL ls with
    | Some (spCnt, spL) =>
      match symPopL spL, symPushZerosAtLeast1R spCnt r0 with
      | Some (_, l2), Some rz => Some (mkSymState mAL l2 (symPushOneR rz))
      | _, _ => None
      end
    | None => None
    end
  | Some (false, r0) =>
    match symPopR r0 with
    | None => None
    | Some (true, r1) =>
      match symPushZeroR r1 with
      | Some rz => Some (mkSymState mAL ls (symPushOneR rz))
      | None => None
      end
    | Some (false, r1) =>
      match symPopR r1 with
      | None => None
      | Some (false, r2) =>
        match symPushZeroR (symPushOneR r2) with
        | Some rz => Some (mkSymState mAL ls (symPushOneR rz))
        | None => None
        end
      | Some (true, r2) =>
        match symPopR r2 with
        | Some (false, r3) =>
          match symPopR r3, symPushZeroL ls with
          | Some (b4, r4), Some lz =>
            match symPushZeroL (symPushOL (mkSym 0 1) lz) with
            | Some lBase =>
              let lOutOpt := if b4 then symPushOneL lBase else symPushZeroL lBase in
              match lOutOpt with
              | Some lOut => Some (mkSymState mDR lOut r4)
              | None => None
              end
            | None => None
            end
          | _, _ => None
          end
        | _ => None
        end
      end
    end
  end.

Definition symStepDRBase (ls : list SymLTok) (rs : list SymRTok) : option SymState :=
  if symIsZeroHeadL ls then
    match symPopL ls with
    | None => None
    | Some (_, lt) =>
      match rs with
      | SR_q qx :: rtail =>
        match symCases012 qx with
        | None => None
        | Some (inl false) => symStepDRFallback ls rs
        | Some (inl true) =>
          let elseBranch :=
            match symPushZeroL lt with
            | Some lz1 =>
              match symPushZeroL lz1, symPushZeroR rtail with
              | Some lz2, Some rz =>
                Some (mkSymState mAL (symPushPL (mkSym 0 0) lz2) (symPushOneR rz))
              | _, _ => None
              end
            | None => None
            end in
          match rtail with
          | SR_z zx :: SR_q v :: rt =>
            match symCases012 zx with
            | None => None
            | Some (inl true) =>
              match symPushZeroL (symPushPL v lt), symPushZeroR2 rt with
              | Some lOut, Some remAfterV =>
                Some (mkSymState mDR lOut (symPushQR (mkSym 0 1) remAfterV))
              | _, _ => None
              end
            | _ => elseBranch
            end
          | _ => elseBranch
          end
        | Some (inr mv) =>
          let u1 := mkSym (sa mv) (sb mv + 2) in
          let elseBranch :=
            match symPushZeroL lt with
            | Some lz1 =>
              match symPushZeroL lz1, symPushZeroR rtail with
              | Some lz2, Some rz =>
                match symPushZeroL (symPushPL mv (symPushOL (mkSym 0 1) lz2)) with
                | Some lOut => Some (mkSymState mAL lOut (symPushOneR rz))
                | None => None
                end
              | _, _ => None
              end
            | None => None
            end in
          match rtail with
          | SR_z zx :: SR_q v :: rt =>
            match symCases012 zx with
            | None => None
            | Some (inl true) =>
              match symPushZeroL (symPushPL v lt), symPushZeroR2 rt with
              | Some lOut, Some remAfterV =>
                Some (mkSymState mDR lOut (symPushQR u1 remAfterV))
              | _, _ => None
              end
            | _ => elseBranch
            end
          | _ => elseBranch
          end
        end
      | _ => symStepDRFallback ls rs
      end
    end
  else symStepDRFallback ls rs.

Definition symStepBaseK (s : SymState) : option SymState :=
  match smode s with
  | mAL =>
    match sl s with
    | SL_o ox :: SL_p k :: lt =>
      match symCases012 ox with
      | None => None
      | Some (inl true) =>
        match symPush100RepeatR k (sr s) with
        | Some rOut => Some (mkSymState mAL (symPushOL (mkSym 0 1) lt) rOut)
        | None => None
        end
      | _ => symStepALElse (sl s) (sr s)
      end
    | _ => symStepALElse (sl s) (sr s)
    end
  | mDR => symStepDRBase (sl s) (sr s)
  end.

(** *** Symbolic Mixed-Chain Accelerator [symStepChainK] *)

Inductive SymChainLeaf : Type :=
| slf_z2q (w1 : SymNat) (rt : list SymRTok)
| slf_cap1 | slf_cap2 | slf_capZ21 | slf_capZ22 | slf_capB.

Definition symCap1Toks : list SymRTok :=
  [SR_ba (mkSym 0 0); SR_q (mkSym 0 1); SR_ba (mkSym 0 0); SR_z (mkSym 0 0); SR_q (mkSym 0 0); SR_ba (mkSym 0 1)].
Definition symCap2Toks : list SymRTok :=
  [SR_z (mkSym 0 3); SR_q (mkSym 0 0); SR_z (mkSym 0 3); SR_q (mkSym 0 1); SR_ba (mkSym 0 1)].
Definition symCapZ21Toks : list SymRTok :=
  [SR_z (mkSym 0 1); SR_q (mkSym 0 0); SR_z (mkSym 0 1); SR_q (mkSym 0 0); SR_z (mkSym 0 3); SR_q (mkSym 0 1); SR_ba (mkSym 0 1)].
Definition symCapZ22Toks : list SymRTok :=
  [SR_z (mkSym 0 1); SR_q (mkSym 0 1); SR_z (mkSym 0 1); SR_q (mkSym 0 0); SR_z (mkSym 0 3); SR_q (mkSym 0 1); SR_ba (mkSym 0 1)].
Definition symCapBToks : list SymRTok :=
  [SR_ba (mkSym 0 0); SR_q (mkSym 0 3); SR_ba (mkSym 0 0); SR_z (mkSym 0 0); SR_q (mkSym 0 0); SR_z (mkSym 0 1); SR_q (mkSym 0 0); SR_z (mkSym 0 3); SR_q (mkSym 0 1); SR_ba (mkSym 0 1)].

Definition symNatNeqConst (x : SymNat) (c : N) : bool :=
  if (if N.eqb (sa x) 0 then negb (N.eqb (sb x) c) else false) then true
  else N.leb (c + 1) (sb x).

Definition symRTokNeqConst (x : SymRTok) (y : RTok) : bool :=
  match x, y with
  | SR_z sx, R_z c => symNatNeqConst sx c
  | SR_o sx, R_o c => symNatNeqConst sx c
  | SR_q sx, R_q c => symNatNeqConst sx c
  | SR_ba sx, R_ba c => symNatNeqConst sx c
  | _, _ => true
  end.

Fixpoint symListNeqConst (xs : list SymRTok) (ys : list RTok) : bool :=
  match xs, ys with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => true
  | x :: xs', y :: ys' =>
    if symRTokNeqConst x y then true else symListNeqConst xs' ys'
  end.

Definition symNotAnyCapLeaf (rs : list SymRTok) : bool :=
  if symListNeqConst rs cap1Toks then
    if symListNeqConst rs cap2Toks then
      if symListNeqConst rs capZ21Toks then
        if symListNeqConst rs capZ22Toks then
          symListNeqConst rs capBToks
        else false
      else false
    else false
  else false.

Definition symMatchCapLeaf (rs : list SymRTok) : option SymChainLeaf :=
  if listSymRBeq rs symCap1Toks then Some slf_cap1
  else if listSymRBeq rs symCap2Toks then Some slf_cap2
  else if listSymRBeq rs symCapZ21Toks then Some slf_capZ21
  else if listSymRBeq rs symCapZ22Toks then Some slf_capZ22
  else if listSymRBeq rs symCapBToks then Some slf_capB
  else None.

Fixpoint symParseChain (u : SymNat) (rs : list SymRTok)
  : option (SymNat * list (SepKind * SymNat) * SymChainLeaf) :=
  match symMatchCapLeaf rs with
  | Some lf => Some (u, [], lf)
  | None =>
    if symNotAnyCapLeaf rs then
      match rs with
      | SR_z zx :: SR_q u1 :: r' =>
        if symNatBeq zx (mkSym 0 5) then
          match symParseChain (symInc u1) r' with
          | Some (uFirst, rest, lf) => Some (u, (sep_z6, uFirst) :: rest, lf)
          | None => None
          end
        else if symNatBeq zx (mkSym 0 3) then
          match symParseChain (symInc u1) r' with
          | Some (uFirst, rest, lf) => Some (u, (sep_z4, uFirst) :: rest, lf)
          | None => None
          end
        else if symNatBeq zx (mkSym 0 1) then
          Some (u, [], slf_z2q (symInc u1) r')
        else None
      | SR_ba bx :: SR_q u1 :: r' =>
        if symNatBeq bx (mkSym 0 2) then
          match symParseChain (symInc u1) r' with
          | Some (uFirst, rest, lf) => Some (u, (sep_ba3, uFirst) :: rest, lf)
          | None => None
          end
        else None
      | SR_ba bx :: SR_z zx :: SR_q u1 :: r' =>
        if symNatBeq bx (mkSym 0 0) then
          if symNatBeq zx (mkSym 0 1) then
            match symParseChain (symInc u1) r' with
            | Some (uFirst, rest, lf) => Some (u, (sep_ba1z2, uFirst) :: rest, lf)
            | None => None
            end
          else None
        else None
      | _ => None
      end
    else None
  end.

Definition symMinNK (x y : SymNat) : option SymNat :=
  if (if N.leb (sa x) (sa y) then N.leb (sb x) (sb y) else false) then Some x
  else if (if N.leb (sa y) (sa x) then N.leb (sb y) (sb x) else false) then Some y
  else None.

Definition symBoundKWith (curK : option SymNat) (u : SymNat) (req : N) (sd : SDelta)
  : option (option SymNat) :=
  if N.leb req (sb u) then
    if negb (isNeg sd) then Some curK
    else if negb (N.leb 1 (mag sd)) then Some curK
    else
      let minStart := req + mag sd in
      if N.leb minStart (sb u) then
        if N.eqb (N.modulo (sa u) (mag sd)) 0 then
          let q := mkSym (N.div (sa u) (mag sd)) (N.div (sb u - req) (mag sd)) in
          match curK with
          | None => Some (Some q)
          | Some k0 =>
            match symMinNK k0 q with
            | Some km => Some (Some km)
            | None => None
            end
          end
        else None
      else None
  else None.

Definition symChainBaseReq {A : Type} (tl : list A) (lf : SymChainLeaf) : N :=
  match tl, lf with
  | [], slf_capB => 4
  | [], slf_z2q _ _ => 1
  | _, _ => 2
  end.

Fixpoint symFoldChainRTL (pairs : list (SepKind * SymNat)) (lf : SymChainLeaf)
  : option (N * N * option SymNat * list (SepKind * SymNat * SDelta)) :=
  match pairs with
  | [] =>
    match lf with
    | slf_z2q w1 _ => Some (1, 0, Some w1, [])
    | slf_cap1 | slf_cap2 | slf_capZ21 | slf_capZ22 => Some (3, 1, None, [])
    | slf_capB => Some (5, 1, None, [])
    end
  | (sep, uNext) :: tl =>
    match symFoldChainRTL tl lf with
    | None => None
    | Some (nPos, nNeg, curK, acc) =>
      let baseReq := symChainBaseReq tl lf in
      let nTot := nPos + nNeg in
      match sep with
      | sep_z6 | sep_ba3 =>
        let req := if N.leb 2 baseReq then baseReq else 2 in
        let sd := sdeltaOfPosNeg nPos nNeg in
        match symBoundKWith curK uNext req sd with
        | None => None
        | Some nextK => Some (nTot, nTot, nextK, (sep, uNext, sd) :: acc)
        end
      | sep_z4 | sep_ba1z2 =>
        let req := if N.leb 3 baseReq then baseReq else 3 in
        let sd := mkSDelta true (nPos + 3 * nNeg) in
        match symBoundKWith curK uNext req sd with
        | None => None
        | Some nextK => Some (3 * nTot, nTot, nextK, (sep, uNext, sd) :: acc)
        end
      end
    end
  end.

Definition symApplyDeltaK (u k : SymNat) (sd : SDelta) : option SymNat :=
  if negb (isNeg sd) then
    Some (mkSym (sa u + mag sd * sa k) (sb u + mag sd * sb k))
  else if N.leb (mag sd * sa k) (sa u) then
    if N.leb (mag sd * sb k) (sb u) then
      Some (mkSym (sa u - mag sd * sa k) (sb u - mag sd * sb k))
    else None
  else None.

Fixpoint symBuildChainTail (items : list (SepKind * SymNat * SDelta)) (k : SymNat)
  (lf : SymChainLeaf) (uCur : SymNat) : option (list SymRTok) :=
  match items with
  | [] =>
    if N.leb 1 (sb uCur) then
      let qLast := mkSym (sa uCur) (sb uCur - 1) in
      match lf with
      | slf_z2q w1 rt =>
        if symNatBeq w1 k then
          match symPushZeroR2 rt with
          | Some remAfter => Some (symPushQR qLast remAfter)
          | None => None
          end
        else if N.leb (sa k) (sa w1) then
          if N.leb (sb k + 1) (sb w1) then
            let wRem := mkSym (sa w1 - sa k) (sb w1 - sb k - 1) in
            Some (symPushQR qLast (SR_z (mkSym 0 1) :: SR_q wRem :: rt))
          else None
        else None
      | slf_cap1 => Some (SR_q qLast :: symCap1Toks)
      | slf_cap2 => Some (SR_q qLast :: symCap2Toks)
      | slf_capZ21 => Some (SR_q qLast :: symCapZ21Toks)
      | slf_capZ22 => Some (SR_q qLast :: symCapZ22Toks)
      | slf_capB => Some (SR_q qLast :: symCapBToks)
      end
    else None
  | (sep, uNext, sd) :: tl =>
    if N.leb 1 (sb uCur) then
      let qCur := mkSym (sa uCur) (sb uCur - 1) in
      match symApplyDeltaK uNext k sd with
      | None => None
      | Some uNextNew =>
        match symBuildChainTail tl k lf uNextNew with
        | None => None
        | Some tail =>
          match sep with
          | sep_z6 => Some (SR_q qCur :: SR_z (mkSym 0 5) :: tail)
          | sep_ba3 => Some (SR_q qCur :: SR_ba (mkSym 0 2) :: tail)
          | sep_z4 => Some (SR_q qCur :: SR_z (mkSym 0 3) :: tail)
          | sep_ba1z2 => Some (SR_q qCur :: SR_ba (mkSym 0 0) :: SR_z (mkSym 0 1) :: tail)
          end
        end
      end
    else None
  end.

Definition symChainReq0 {A : Type} (pairs : list A) (lf : SymChainLeaf) : N :=
  match pairs, lf with
  | [], slf_capB => 4
  | _, _ => 2
  end.

Definition symStepChainK (s : SymState) : option SymState :=
  match smode s with
  | mAL => None
  | mDR =>
    if symIsZeroHeadL (sl s) then
      match sr s with
      | SR_q u0_0 :: rem =>
        let u0 := symInc u0_0 in
        match symParseChain u0 rem with
        | None => None
        | Some (uFirst, pairs, lf) =>
          match symFoldChainRTL pairs lf with
          | None => None
          | Some (nPos, nNeg, curK, items) =>
            let req0 := symChainReq0 pairs lf in
            let sd0 := mkSDelta true (2 * nNeg) in
            match symBoundKWith curK uFirst req0 sd0 with
            | Some (Some kVal) =>
              if N.leb 1 (sb kVal) then
                let n0 := nPos + nNeg in
                if N.leb 1 (n0 * sb kVal) then
                  let pPush := mkSym (n0 * sa kVal) (n0 * sb kVal - 1) in
                  match symApplyDeltaK uFirst kVal sd0, symPopL (sl s) with
                  | Some u0New, Some (_, lt) =>
                    match symPushZeroL (symPushPL pPush lt), symBuildChainTail items kVal lf u0New with
                    | Some newL, Some newR => Some (mkSymState mDR newL newR)
                    | _, _ => None
                    end
                  | _, _ => None
                  end
                else None
              else None
            | _ => None
            end
          end
        end
      | _ => None
      end
    else None
  end.

Definition symStepAutoK (s : SymState) : option SymState :=
  match symStepChainK s with
  | Some s' => Some s'
  | None => symStepBaseK s
  end.

Definition symStepAutoOpt (cur : option SymState) : option SymState :=
  match cur with
  | None => None
  | Some s => symStepAutoK s
  end.

Definition symRunStepsPos (p : positive) (st : SymState) : option SymState :=
  Pos.iter symStepAutoOpt (Some st) p.

(** *** Commutation Proofs for [symStepBaseK] and [symStepChainK] *)

Lemma evalSym_const (m c : N) : evalSym m (mkSym 0 c) = c.
Proof. unfold evalSym; cbn [sa sb]; lia. Qed.

Lemma evalSym_symAdd1 (m : N) (x y : SymNat) :
  evalSym m (symAdd1 x y) = evalSym m x + 1 + evalSym m y.
Proof. unfold symAdd1, evalSym; cbn [sa sb]; nia. Qed.

Lemma evalSym_symInc (m : N) (x : SymNat) :
  evalSym m (symInc x) = evalSym m x + 1.
Proof. unfold symInc, evalSym; cbn [sa sb]; lia. Qed.

Lemma symCases01_none {x : SymNat} (H : symCases01 x = Some None) (m : N) :
  evalSym m x = 0.
Proof.
  unfold symCases01 in H.
  destruct (N.eqb (sb x) 0) eqn:Hb; [| discriminate].
  destruct (N.eqb (sa x) 0) eqn:Ha; [| discriminate].
  apply N.eqb_eq in Hb; apply N.eqb_eq in Ha.
  unfold evalSym; rewrite Ha, Hb; lia.
Qed.

Lemma symCases01_some {x mv : SymNat} (H : symCases01 x = Some (Some mv)) (m : N) :
  evalSym m x = evalSym m mv + 1 /\ N.eqb (evalSym m x) 0 = false.
Proof.
  unfold symCases01 in H.
  destruct (N.eqb (sb x) 0) eqn:Hb.
  - destruct (N.eqb (sa x) 0); discriminate.
  - inversion H; subst mv; clear H.
    apply N.eqb_neq in Hb. unfold evalSym; cbn [sa sb].
    split; [lia | apply N.eqb_neq; nia].
Qed.

Lemma symCases012_inl_false {x : SymNat} (H : symCases012 x = Some (inl false)) (m : N) :
  evalSym m x = 0.
Proof.
  unfold symCases012 in H.
  destruct (N.eqb (sb x) 0) eqn:Hb.
  - destruct (N.eqb (sa x) 0) eqn:Ha; [| discriminate].
    apply N.eqb_eq in Hb; apply N.eqb_eq in Ha.
    unfold evalSym; rewrite Ha, Hb; lia.
  - destruct (N.eqb (sb x) 1); [destruct (N.eqb (sa x) 0) |]; discriminate.
Qed.

Lemma symCases012_inl_true {x : SymNat} (H : symCases012 x = Some (inl true)) (m : N) :
  evalSym m x = 1.
Proof.
  unfold symCases012 in H.
  destruct (N.eqb (sb x) 0) eqn:Hb0.
  - destruct (N.eqb (sa x) 0); discriminate.
  - destruct (N.eqb (sb x) 1) eqn:Hb1; [| discriminate].
    destruct (N.eqb (sa x) 0) eqn:Ha; [| discriminate].
    apply N.eqb_eq in Hb1; apply N.eqb_eq in Ha.
    unfold evalSym; rewrite Ha, Hb1; lia.
Qed.

Lemma symCases012_inr {x mv : SymNat} (H : symCases012 x = Some (inr mv)) (m : N) :
  evalSym m x = evalSym m mv + 2 /\
  N.eqb (evalSym m x) 0 = false /\
  N.eqb (evalSym m x) 1 = false.
Proof.
  unfold symCases012 in H.
  destruct (N.eqb (sb x) 0) eqn:Hb0; [destruct (N.eqb (sa x) 0); discriminate |].
  destruct (N.eqb (sb x) 1) eqn:Hb1; [destruct (N.eqb (sa x) 0); discriminate |].
  inversion H; subst mv; clear H.
  apply N.eqb_neq in Hb0; apply N.eqb_neq in Hb1.
  unfold evalSym; cbn [sa sb].
  split; [lia | split; apply N.eqb_neq; nia].
Qed.

Lemma evalSymL_symPushPL (m : N) (k : SymNat) (ls : list SymLTok) :
  evalSymL m (symPushPL k ls) = pushPL (evalSym m k) (evalSymL m ls).
Proof.
  destruct ls as [| [x | x | x | x] rest]; cbn [symPushPL evalSymL List.map evalSymLTok pushPL];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymL_symPushABL (m : N) (k : SymNat) (ls : list SymLTok) :
  evalSymL m (symPushABL k ls) = pushABL (evalSym m k) (evalSymL m ls).
Proof.
  destruct ls as [| [x | x | x | x] rest]; cbn [symPushABL evalSymL List.map evalSymLTok pushABL];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymL_symPushOL (m : N) (k : SymNat) (ls : list SymLTok) :
  evalSymL m (symPushOL k ls) = pushOL (evalSym m k) (evalSymL m ls).
Proof.
  destruct ls as [| [x | x | x | x] rest]; cbn [symPushOL evalSymL List.map evalSymLTok pushOL];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymL_symPushZeroL {ls ls' : list SymLTok}
  (H : symPushZeroL ls = Some ls') (m : N) :
  evalSymL m ls' = pushZeroL (evalSymL m ls).
Proof.
  destruct ls as [| [zm | ox | pm | am] rest]; cbn [symPushZeroL] in H.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushZeroL]; rewrite evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushZeroL]; rewrite evalSym_symInc; reflexivity.
  - destruct (symCases012 ox) as [[bflag | mv] |] eqn:Hc; [| | discriminate].
    + destruct bflag; inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok pushZeroL].
      * rewrite (symCases012_inl_true Hc m); cbn [N.eqb Pos.eqb].
        rewrite evalSymL_symPushPL, evalSym_const; reflexivity.
      * rewrite (symCases012_inl_false Hc m); cbn [N.eqb Pos.eqb].
        rewrite !evalSym_const; reflexivity.
    + inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok pushZeroL].
      destruct (symCases012_inr Hc m) as [Hev [Hne0 Hne1]].
      rewrite Hne0, Hne1, evalSym_const, Hev.
      replace (evalSym m mv + 2 - 2) with (evalSym m mv) by lia. reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushZeroL]; rewrite evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushZeroL]; rewrite evalSym_const; reflexivity.
Qed.

Lemma evalSymL_symPushOneL {ls ls' : list SymLTok}
  (H : symPushOneL ls = Some ls') (m : N) :
  evalSymL m ls' = pushOneL (evalSymL m ls).
Proof.
  destruct ls as [| [zx | om | pm | am] rest]; cbn [symPushOneL] in H.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushOneL]; rewrite evalSym_const; reflexivity.
  - destruct (symCases01 zx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok pushOneL].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev.
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia. reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymL_symPushABL, evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushOneL]; rewrite evalSym_symInc; reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushOneL]; rewrite evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymL List.map evalSymLTok pushOneL]; rewrite evalSym_const; reflexivity.
Qed.

Lemma evalSymL_symPopL {ls : list SymLTok} {b : bool} {ls' : list SymLTok}
  (H : symPopL ls = Some (b, ls')) (m : N) :
  popL (evalSymL m ls) = (b, evalSymL m ls').
Proof.
  destruct ls as [| [zx | ox | px | ax] rest]; cbn [symPopL] in H.
  - inversion H; subst; reflexivity.
  - destruct (symCases01 zx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok popL].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); reflexivity.
  - destruct (symCases01 ox) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok popL].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); reflexivity.
  - destruct (symCases01 px) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok popL].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev; cbn [pushOL];
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymL_symPushOL, evalSym_const; reflexivity.
  - destruct (symCases01 ax) as [[mv |] |] eqn:Hc; [| | discriminate].
    + destruct (symPushZeroL (SL_ab mv :: rest)) as [r' |] eqn:Hz; [| discriminate].
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok popL].
      destruct (symCases01_some Hc m) as [Hev Hne0].
      pose proof (evalSymL_symPushZeroL Hz m) as Hz'; cbn [evalSymL List.map evalSymLTok] in Hz'.
      rewrite Hne0, Hz', Hev.
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + destruct (symPushZeroL rest) as [r' |] eqn:Hz; [| discriminate].
      inversion H; subst; clear H; cbn [evalSymL List.map evalSymLTok popL].
      rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite (evalSymL_symPushZeroL Hz m); reflexivity.
Qed.

Lemma evalSymR_symPushQR (m : N) (k : SymNat) (rs : list SymRTok) :
  evalSymR m (symPushQR k rs) = pushQR (evalSym m k) (evalSymR m rs).
Proof.
  destruct rs as [| [x | x | x | x] rest]; cbn [symPushQR evalSymR List.map evalSymRTok pushQR];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymR_symPushBAR (m : N) (k : SymNat) (rs : list SymRTok) :
  evalSymR m (symPushBAR k rs) = pushBAR (evalSym m k) (evalSymR m rs).
Proof.
  destruct rs as [| [x | x | x | x] rest]; cbn [symPushBAR evalSymR List.map evalSymRTok pushBAR];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymR_symPushZRawR (m : N) (k : SymNat) (rs : list SymRTok) :
  evalSymR m (symPushZRawR k rs) = pushZRawR (evalSym m k) (evalSymR m rs).
Proof.
  destruct rs as [| [x | x | x | x] rest]; cbn [symPushZRawR evalSymR List.map evalSymRTok pushZRawR];
    try reflexivity.
  rewrite evalSym_symAdd1; reflexivity.
Qed.

Lemma evalSymR_symPushOneR (m : N) (rs : list SymRTok) :
  evalSymR m (symPushOneR rs) = pushOneR (evalSymR m rs).
Proof.
  destruct rs as [| [x | x | x | x] rest]; cbn [symPushOneR evalSymR List.map evalSymRTok pushOneR];
    rewrite ?evalSym_const, ?evalSym_symInc; reflexivity.
Qed.

Lemma evalSymR_symPushZeroR {rs rs' : list SymRTok}
  (H : symPushZeroR rs = Some rs') (m : N) :
  evalSymR m rs' = pushZeroR (evalSymR m rs).
Proof.
  destruct rs as [| [zm | ox | qm | bx] rest]; cbn [symPushZeroR] in H.
  - inversion H; subst; cbn [evalSymR List.map evalSymRTok pushZeroR]; rewrite evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymR List.map evalSymRTok pushZeroR]; rewrite evalSym_symInc; reflexivity.
  - destruct (symCases01 ox) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok pushZeroR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymR_symPushBAR, evalSym_const; reflexivity.
  - inversion H; subst; cbn [evalSymR List.map evalSymRTok pushZeroR]; rewrite evalSym_const; reflexivity.
  - destruct (symCases01 bx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok pushZeroR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymR_symPushQR, evalSym_const; reflexivity.
Qed.

Lemma evalSymR_symPushZeroR2 {rs rs' : list SymRTok}
  (H : symPushZeroR2 rs = Some rs') (m : N) :
  evalSymR m rs' = pushZeroR (pushZeroR (evalSymR m rs)).
Proof.
  unfold symPushZeroR2 in H.
  destruct (symPushZeroR rs) as [r1 |] eqn:H1; [| discriminate].
  rewrite (evalSymR_symPushZeroR H m), (evalSymR_symPushZeroR H1 m); reflexivity.
Qed.

Lemma evalSymR_symPushZerosAtLeast1R {cnt : N} {rs rs' : list SymRTok}
  (H : symPushZerosAtLeast1R cnt rs = Some rs') (m : N) :
  evalSymR m rs' = pushZerosAtLeast1R cnt (evalSymR m rs).
Proof.
  unfold symPushZerosAtLeast1R in H; unfold pushZerosAtLeast1R.
  destruct (N.eqb cnt 0) eqn:H0; [exact (evalSymR_symPushZeroR H m) |].
  destruct (N.eqb cnt 1) eqn:H1; [exact (evalSymR_symPushZeroR2 H m) |].
  destruct (symPushZeroR2 rs) as [r2 |] eqn:Hr2; [| discriminate].
  inversion H; subst; clear H.
  rewrite evalSymR_symPushZRawR, evalSym_const, (evalSymR_symPushZeroR2 Hr2 m); reflexivity.
Qed.

Lemma evalSymR_symPushZerosAtLeast2R {cnt : N} {rs rs' : list SymRTok}
  (H : symPushZerosAtLeast2R cnt rs = Some rs') (m : N) :
  evalSymR m rs' = pushZerosAtLeast2R cnt (evalSymR m rs).
Proof.
  unfold symPushZerosAtLeast2R in H; unfold pushZerosAtLeast2R.
  destruct (N.eqb cnt 0) eqn:H0; [exact (evalSymR_symPushZeroR2 H m) |].
  destruct (symPushZeroR2 rs) as [r2 |] eqn:Hr2; [| discriminate].
  inversion H; subst; clear H.
  rewrite evalSymR_symPushZRawR, evalSym_const, (evalSymR_symPushZeroR2 Hr2 m); reflexivity.
Qed.

Lemma evalSymR_symPush10RepeatR {cnt : SymNat} {rs rs' : list SymRTok}
  (H : symPush10RepeatR cnt rs = Some rs') (m : N) :
  evalSymR m rs' = push10RepeatR (evalSym m cnt) (evalSymR m rs).
Proof.
  unfold symPush10RepeatR in H; unfold push10RepeatR.
  destruct (symCases01 cnt) as [[mv |] |] eqn:Hc;
    destruct (symPushZeroR rs) as [r0 |] eqn:Hr0; try discriminate;
    inversion H; subst; clear H.
  - destruct (symCases01_some Hc m) as [Hev Hne0].
    rewrite Hne0, evalSymR_symPushOneR, evalSymR_symPushBAR, (evalSymR_symPushZeroR Hr0 m), Hev.
    replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
  - rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
    rewrite evalSymR_symPushOneR, (evalSymR_symPushZeroR Hr0 m); reflexivity.
Qed.

Lemma evalSymR_symPush100RepeatR {cnt : SymNat} {rs rs' : list SymRTok}
  (H : symPush100RepeatR cnt rs = Some rs') (m : N) :
  evalSymR m rs' = push100RepeatR (evalSym m cnt) (evalSymR m rs).
Proof.
  unfold symPush100RepeatR in H; unfold push100RepeatR.
  destruct (symCases01 cnt) as [[mv |] |] eqn:Hc;
    destruct (symPushZeroR2 rs) as [r2 |] eqn:Hr2; try discriminate;
    inversion H; subst; clear H.
  - destruct (symCases01_some Hc m) as [Hev Hne0].
    rewrite Hne0, evalSymR_symPushOneR, evalSymR_symPushQR, (evalSymR_symPushZeroR2 Hr2 m), Hev.
    replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
  - rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
    rewrite evalSymR_symPushOneR, (evalSymR_symPushZeroR2 Hr2 m); reflexivity.
Qed.

Lemma evalSymR_symPopR {rs : list SymRTok} {b : bool} {rs' : list SymRTok}
  (H : symPopR rs = Some (b, rs')) (m : N) :
  popR (evalSymR m rs) = (b, evalSymR m rs').
Proof.
  destruct rs as [| [zx | ox | qx | bx] rest]; cbn [symPopR] in H.
  - inversion H; subst; reflexivity.
  - destruct (symCases01 zx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok popR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); reflexivity.
  - destruct (symCases01 ox) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok popR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, Hev; replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); reflexivity.
  - destruct (symCases01 qx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok popR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev; cbn [pushBAR];
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymR_symPushBAR, evalSym_const; reflexivity.
  - destruct (symCases01 bx) as [[mv |] |] eqn:Hc; [| | discriminate];
      inversion H; subst; clear H; cbn [evalSymR List.map evalSymRTok popR].
    + destruct (symCases01_some Hc m) as [Hev Hne0].
      rewrite Hne0, evalSym_const, Hev; cbn [pushOneR];
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite evalSymR_symPushOneR; reflexivity.
Qed.

Lemma evalSymL_symSplitLeadingOnesL :
  forall (ls : list SymLTok) (cnt : N) (ls' : list SymLTok),
    symSplitLeadingOnesL ls = Some (cnt, ls') ->
    forall m : N, splitLeadingOnesL (evalSymL m ls) = (cnt, evalSymL m ls').
Proof.
  induction ls as [| [k | x | k | ax] rest IH]; intros cnt ls' H m;
    cbn [symSplitLeadingOnesL] in H.
  - inversion H; subst; reflexivity.
  - inversion H; subst; reflexivity.
  - destruct (N.eqb (sa x) 0) eqn:Hsa; [| discriminate].
    apply N.eqb_eq in Hsa.
    destruct (symSplitLeadingOnesL rest) as [[c1 l1] |] eqn:Hsub; [| discriminate].
    inversion H; subst; clear H.
    cbn [evalSymL List.map evalSymLTok splitLeadingOnesL fst snd].
    rewrite (IH c1 ls' eq_refl m); cbn [fst snd].
    f_equal. unfold evalSym; rewrite Hsa; lia.
  - inversion H; subst; reflexivity.
  - destruct (symCases01 ax) as [[mv |] |] eqn:Hc; [| | discriminate].
    + destruct (symPushZeroL (SL_ab mv :: rest)) as [r' |] eqn:Hz; [| discriminate].
      inversion H; subst; clear H.
      cbn [evalSymL List.map evalSymLTok splitLeadingOnesL].
      destruct (symCases01_some Hc m) as [Hev Hne0].
      pose proof (evalSymL_symPushZeroL Hz m) as Hz'; cbn [evalSymL List.map evalSymLTok] in Hz'.
      rewrite Hne0, Hz', Hev.
      replace (evalSym m mv + 1 - 1) with (evalSym m mv) by lia; reflexivity.
    + destruct (symPushZeroL rest) as [r' |] eqn:Hz; [| discriminate].
      inversion H; subst; clear H.
      cbn [evalSymL List.map evalSymLTok splitLeadingOnesL].
      rewrite (symCases01_none Hc m); cbn [N.eqb Pos.eqb].
      rewrite (evalSymL_symPushZeroL Hz m); reflexivity.
Qed.

Lemma evalSym_symSweepAL_len :
  forall (bound : nat) (ls : list SymLTok) (rs : list SymRTok)
    (ls' : list SymLTok) (rs' : list SymRTok),
    (List.length ls <= bound)%nat ->
    symSweepAL ls rs = Some (ls', rs') ->
    forall m : N, sweepAL (evalSymL m ls) (evalSymR m rs) = (evalSymL m ls', evalSymR m rs').
Proof.
  induction bound as [| bound IH]; intros ls rs ls' rs' Hlen H m.
  - destruct ls; [cbn [symSweepAL] in H; inversion H; subst; reflexivity | cbn [List.length] in Hlen; lia].
  - destruct ls as [| [k | x | k | ak] rest]; cbn [symSweepAL] in H.
    + inversion H; subst; reflexivity.
    + inversion H; subst; reflexivity.
    + destruct (symCases01 x) as [[mv |] |] eqn:Hx; [| | discriminate].
      * inversion H; subst.
        cbn [evalSymL List.map evalSymLTok sweepAL].
        destruct (symCases01_some Hx m) as [_ Hne0].
        rewrite Hne0; reflexivity.
      * pose proof (symCases01_none Hx m) as Hx0.
        destruct rest as [| [zx | oy | px | ay] rest2].
        -- destruct (symPush10RepeatR (mkSym 0 0) rs) as [r1 |] eqn:Hr1; [| discriminate].
           inversion H; subst; clear H.
           cbn [evalSymL List.map evalSymLTok sweepAL].
           rewrite Hx0; cbn [N.eqb Pos.eqb].
           pose proof (evalSymR_symPush10RepeatR Hr1 m) as Hr1'.
           rewrite evalSym_const in Hr1'. rewrite Hr1'; reflexivity.
        -- destruct (symCases01 zx) as [[zmv |] |] eqn:Hzx; [| | discriminate];
             destruct (symPush10RepeatR (mkSym 0 0) rs) as [r1 |] eqn:Hr1; try discriminate.
           ++ inversion H; subst; clear H.
              cbn [evalSymL List.map evalSymLTok sweepAL].
              destruct (symCases01_some Hzx m) as [Hz_ev Hz_ne0].
              pose proof (evalSymR_symPush10RepeatR Hr1 m) as Hr1'; rewrite evalSym_const in Hr1'.
              rewrite Hx0; cbn [N.eqb Pos.eqb]. rewrite Hz_ne0, Hr1', Hz_ev.
              replace (evalSym m zmv + 1 - 1) with (evalSym m zmv) by lia; reflexivity.
           ++ cbn [evalSymL List.map evalSymLTok sweepAL].
              rewrite Hx0, (symCases01_none Hzx m); cbn [N.eqb Pos.eqb].
              pose proof (evalSymR_symPush10RepeatR Hr1 m) as Hr1'; rewrite evalSym_const in Hr1'.
              rewrite <- Hr1'.
              exact (IH rest2 r1 ls' rs' ltac:(cbn [List.length] in Hlen; lia) H m).
        -- inversion H; subst.
           cbn [evalSymL List.map evalSymLTok sweepAL]. rewrite Hx0; cbn [N.eqb Pos.eqb]; reflexivity.
        -- destruct (symCases01 px) as [[pmv |] |] eqn:Hpx; [| | discriminate];
             destruct (symPush10RepeatR (mkSym 0 0) rs) as [r1 |] eqn:Hr1; try discriminate;
             inversion H; subst; clear H.
           ++ cbn [evalSymL List.map evalSymLTok sweepAL].
              destruct (symCases01_some Hpx m) as [Hp_ev Hp_ne0].
              pose proof (evalSymR_symPush10RepeatR Hr1 m) as Hr1'; rewrite evalSym_const in Hr1'.
              rewrite Hx0; cbn [N.eqb Pos.eqb]. rewrite Hp_ne0, evalSym_const, Hr1', Hp_ev.
              replace (evalSym m pmv + 1 - 1) with (evalSym m pmv) by lia; reflexivity.
           ++ cbn [evalSymL List.map evalSymLTok sweepAL].
              rewrite Hx0, (symCases01_none Hpx m); cbn [N.eqb Pos.eqb].
              pose proof (evalSymR_symPush10RepeatR Hr1 m) as Hr1'; rewrite evalSym_const in Hr1'.
              rewrite evalSymL_symPushOL, evalSym_const, Hr1'; reflexivity.
        -- inversion H; subst.
           cbn [evalSymL List.map evalSymLTok sweepAL]. rewrite Hx0; cbn [N.eqb Pos.eqb]; reflexivity.
    + inversion H; subst; reflexivity.
    + destruct (symPush10RepeatR ak rs) as [r1 |] eqn:Hr1; [| discriminate].
      cbn [evalSymL List.map evalSymLTok sweepAL].
      rewrite <- (evalSymR_symPush10RepeatR Hr1 m).
      exact (IH rest r1 ls' rs' ltac:(cbn [List.length] in Hlen; lia) H m).
Qed.

Lemma evalSym_symSweepAL {ls : list SymLTok} {rs : list SymRTok}
  {ls' : list SymLTok} {rs' : list SymRTok}
  (H : symSweepAL ls rs = Some (ls', rs')) (m : N) :
  sweepAL (evalSymL m ls) (evalSymR m rs) = (evalSymL m ls', evalSymR m rs').
Proof.
  exact (evalSym_symSweepAL_len (List.length ls) ls rs ls' rs' (le_n _) H m).
Qed.

Lemma evalSymL_symIsZeroHeadL (m : N) (ls : list SymLTok) :
  isZeroHeadL (evalSymL m ls) = symIsZeroHeadL ls.
Proof.
  destruct ls as [| [x | x | x | x] rest]; reflexivity.
Qed.

Lemma symStepALZeroFallback_comm {ls : list SymLTok} {rs : list SymRTok} {s' : SymState}
  (H : symStepALZeroFallback ls rs = Some s') (m : N) :
  stepALZeroFallback (evalSymL m ls) (evalSymR m rs) = Some (evalSymState m s').
Proof.
  unfold symStepALZeroFallback in H; unfold stepALZeroFallback.
  destruct (symPopR rs) as [[b0 r0] |] eqn:Hpr; [| discriminate].
  destruct (symPopL ls) as [[bl lt] |] eqn:Hpl; [| destruct b0; discriminate].
  rewrite (evalSymR_symPopR Hpr m), (evalSymL_symPopL Hpl m); cbn [fst snd].
  destruct b0.
  - destruct (symPopR r0) as [[b1 r1] |] eqn:Hpr1; [| discriminate].
    rewrite (evalSymR_symPopR Hpr1 m); cbn [fst snd].
    destruct b1; [discriminate |].
    destruct (symPopR r1) as [[b2 r2] |] eqn:Hpr2; [| discriminate].
    destruct (symPushZeroL (symPushOL (mkSym 0 1) lt)) as [lBase |] eqn:Hlb; [| discriminate].
    rewrite (evalSymR_symPopR Hpr2 m); cbn [fst snd].
    pose proof (evalSymL_symPushZeroL Hlb m) as Hlb'.
    rewrite evalSymL_symPushOL, evalSym_const in Hlb'.
    destruct b2.
    + destruct (symPushOneL lBase) as [lOut |] eqn:Hlo; [| discriminate].
      inversion H; subst; clear H; unfold evalSymState; cbn [smode sl sr].
      rewrite (evalSymL_symPushOneL Hlo m), Hlb'; reflexivity.
    + destruct (symPushZeroL lBase) as [lOut |] eqn:Hlo; [| discriminate].
      inversion H; subst; clear H; unfold evalSymState; cbn [smode sl sr].
      rewrite (evalSymL_symPushZeroL Hlo m), Hlb'; reflexivity.
  - destruct (symPopL lt) as [[b1 l1] |] eqn:Hpl1; [| discriminate].
    rewrite (evalSymL_symPopL Hpl1 m); cbn [fst snd].
    destruct b1.
    + destruct (symSplitLeadingOnesL l1) as [[spCnt spL] |] eqn:Hsp; [| discriminate].
      destruct (symPopL spL) as [[b3 l3] |] eqn:Hpl3; [| discriminate].
      destruct (symPushZerosAtLeast2R spCnt (symPushOneR r0)) as [rz |] eqn:Hrz; [| discriminate].
      inversion H; subst; clear H.
      rewrite (evalSymL_symSplitLeadingOnesL _ _ _ Hsp m); cbn [fst snd].
      rewrite (evalSymL_symPopL Hpl3 m); cbn [snd].
      pose proof (evalSymR_symPushZerosAtLeast2R Hrz m) as Hrz'.
      rewrite evalSymR_symPushOneR in Hrz'.
      unfold evalSymState; cbn [smode sl sr].
      rewrite evalSymR_symPushOneR, Hrz'; reflexivity.
    + destruct (symPushZeroR (symPushOneR r0)) as [rz |] eqn:Hrz; [| discriminate].
      inversion H; subst; clear H.
      pose proof (evalSymR_symPushZeroR Hrz m) as Hrz'.
      rewrite evalSymR_symPushOneR in Hrz'.
      unfold evalSymState; cbn [smode sl sr].
      rewrite evalSymR_symPushOneR, Hrz'; reflexivity.
Qed.

Lemma symStepALElse_comm {ls : list SymLTok} {rs : list SymRTok} {s' : SymState}
  (H : symStepALElse ls rs = Some s') (m : N) :
  stepALElse (evalSymL m ls) (evalSymR m rs) = Some (evalSymState m s').
Proof.
  unfold symStepALElse in H; unfold stepALElse.
  rewrite evalSymL_symIsZeroHeadL.
  destruct (symIsZeroHeadL ls) eqn:Hz.
  - destruct rs as [| [k1 | ox | k1 | k1] [| [zx | k2 | qx | k2] [| rt3 rt]]];
      try exact (symStepALZeroFallback_comm H m).
      * destruct rt3 as [k3 | k3 | k | k3];
          try exact (symStepALZeroFallback_comm H m).
        destruct (symCases01 ox) as [[omv |] |] eqn:Hox; [| | destruct (symCases01 zx); discriminate].
        -- pose proof (symStepALZeroFallback_comm H m) as Hfb.
           cbn [evalSymR List.map evalSymRTok] in Hfb |- *.
           destruct (symCases01_some Hox m) as [_ Ho_ne0].
           rewrite Ho_ne0; exact Hfb.
        -- destruct (symCases01 zx) as [[zmv |] |] eqn:Hzx; [| | discriminate].
           ++ pose proof (symStepALZeroFallback_comm H m) as Hfb.
              cbn [evalSymR List.map evalSymRTok] in Hfb |- *.
              destruct (symCases01_some Hzx m) as [_ Hz_ne0].
              rewrite (symCases01_none Hox m) in Hfb |- *; cbn [N.eqb Pos.eqb]. rewrite Hz_ne0; exact Hfb.
           ++ destruct (symPopL ls) as [[bl lt] |] eqn:Hpl; [| discriminate].
              destruct (symPushZeroR rt) as [rz |] eqn:Hrz; [| discriminate].
              destruct (symPushZeroL (symPushPL k lt)) as [lOut |] eqn:Hlo; [| discriminate].
              inversion H; subst; clear H.
              cbn [evalSymR List.map evalSymRTok].
              rewrite (symCases01_none Hox m), (symCases01_none Hzx m); cbn [N.eqb Pos.eqb].
              rewrite (evalSymL_symPopL Hpl m); cbn [snd].
              pose proof (evalSymL_symPushZeroL Hlo m) as Hlo'.
              rewrite evalSymL_symPushPL in Hlo'.
              unfold evalSymState; cbn [smode sl sr].
              rewrite Hlo', evalSymR_symPushOneR, (evalSymR_symPushZeroR Hrz m); reflexivity.
      * destruct rt3 as [k3 | k3 | k3 | k];
          try exact (symStepALZeroFallback_comm H m).
        destruct (symCases01 ox) as [[omv |] |] eqn:Hox; [| | destruct (symCases01 qx); discriminate].
        -- pose proof (symStepALZeroFallback_comm H m) as Hfb.
           cbn [evalSymR List.map evalSymRTok] in Hfb |- *.
           destruct (symCases01_some Hox m) as [_ Ho_ne0].
           rewrite Ho_ne0; exact Hfb.
        -- destruct (symCases01 qx) as [[qmv |] |] eqn:Hqx; [| | discriminate].
           ++ pose proof (symStepALZeroFallback_comm H m) as Hfb.
              cbn [evalSymR List.map evalSymRTok] in Hfb |- *.
              destruct (symCases01_some Hqx m) as [_ Hq_ne0].
              rewrite (symCases01_none Hox m) in Hfb |- *; cbn [N.eqb Pos.eqb]. rewrite Hq_ne0; exact Hfb.
           ++ destruct (symPopL ls) as [[bl lt] |] eqn:Hpl; [| discriminate].
              destruct (symPushZeroR rt) as [rz |] eqn:Hrz; [| discriminate].
              destruct (symPushZeroL (symPushOL (mkSym (2 * sa k) (2 * sb k + 3)) lt))
                as [lOut |] eqn:Hlo; [| discriminate].
              inversion H; subst; clear H.
              cbn [evalSymR List.map evalSymRTok].
              rewrite (symCases01_none Hox m), (symCases01_none Hqx m); cbn [N.eqb Pos.eqb].
              rewrite (evalSymL_symPopL Hpl m); cbn [snd].
              pose proof (evalSymL_symPushZeroL Hlo m) as Hlo'.
              rewrite evalSymL_symPushOL in Hlo'.
              replace (evalSym m (mkSym (2 * sa k) (2 * sb k + 3)))
                with (2 * evalSym m k + 3) in Hlo' by (unfold evalSym; cbn [sa sb]; nia).
              unfold evalSymState; cbn [smode sl sr].
              rewrite Hlo', evalSymR_symPushOneR, (evalSymR_symPushZeroR Hrz m); reflexivity.
  - destruct (symSweepAL ls rs) as [[swL swR] |] eqn:Hsw; [| discriminate].
    rewrite (evalSym_symSweepAL Hsw m); cbn [fst snd].
    destruct (symPopL swL) as [[b0 l0] |] eqn:Hpl0; [| discriminate].
    rewrite (evalSymL_symPopL Hpl0 m); cbn [fst snd].
    destruct b0.
    + destruct (symPopL l0) as [[b1 l1] |] eqn:Hpl1; [| discriminate].
      rewrite (evalSymL_symPopL Hpl1 m); cbn [fst snd].
      destruct b1.
      * destruct (symSplitLeadingOnesL l1) as [[spCnt spL] |] eqn:Hsp; [| discriminate].
        destruct (symPopL spL) as [[b3 l3] |] eqn:Hpl3; [| discriminate].
        destruct (symPushZerosAtLeast2R spCnt swR) as [rz |] eqn:Hrz; [| discriminate].
        inversion H; subst; clear H.
        rewrite (evalSymL_symSplitLeadingOnesL _ _ _ Hsp m); cbn [fst snd].
        rewrite (evalSymL_symPopL Hpl3 m); cbn [snd].
        unfold evalSymState; cbn [smode sl sr].
        rewrite evalSymR_symPushOneR, (evalSymR_symPushZerosAtLeast2R Hrz m); reflexivity.
      * destruct (symPush10RepeatR (mkSym 0 0) swR) as [rOut |] eqn:Hro; [| discriminate].
        inversion H; subst; clear H.
        pose proof (evalSymR_symPush10RepeatR Hro m) as Hro'; rewrite evalSym_const in Hro'.
        unfold evalSymState; cbn [smode sl sr]. rewrite Hro'; reflexivity.
    + assert (Hfb : symStepALZeroFallback swL swR = Some s').
      { unfold symStepALZeroFallback; rewrite Hpl0.
        destruct (symPopR swR) as [[rb0 r0] |]; [destruct rb0 |]; exact H. }
      pose proof (symStepALZeroFallback_comm Hfb m) as Hcomm.
      unfold stepALZeroFallback in Hcomm.
      rewrite (evalSymL_symPopL Hpl0 m) in Hcomm; cbn [snd] in Hcomm.
      exact Hcomm.
Qed.

Lemma symStepDRFallback_comm {ls : list SymLTok} {rs : list SymRTok} {s' : SymState}
  (H : symStepDRFallback ls rs = Some s') (m : N) :
  stepDRFallback (evalSymL m ls) (evalSymR m rs) = Some (evalSymState m s').
Proof.
  unfold symStepDRFallback in H; unfold stepDRFallback.
  destruct (symPopR rs) as [[b0 r0] |] eqn:Hpr0; [| discriminate].
  rewrite (evalSymR_symPopR Hpr0 m); cbn [fst snd].
  destruct b0.
  - destruct (symSplitLeadingOnesL ls) as [[spCnt spL] |] eqn:Hsp; [| discriminate].
    destruct (symPopL spL) as [[b2 l2] |] eqn:Hpl2; [| discriminate].
    destruct (symPushZerosAtLeast1R spCnt r0) as [rz |] eqn:Hrz; [| discriminate].
    inversion H; subst; clear H.
    rewrite (evalSymL_symSplitLeadingOnesL _ _ _ Hsp m); cbn [fst snd].
    rewrite (evalSymL_symPopL Hpl2 m); cbn [snd].
    unfold evalSymState; cbn [smode sl sr].
    rewrite evalSymR_symPushOneR, (evalSymR_symPushZerosAtLeast1R Hrz m); reflexivity.
  - destruct (symPopR r0) as [[b1 r1] |] eqn:Hpr1; [| discriminate].
    rewrite (evalSymR_symPopR Hpr1 m); cbn [fst snd].
    destruct b1.
    + destruct (symPushZeroR r1) as [rz |] eqn:Hrz; [| discriminate].
      inversion H; subst; clear H.
      unfold evalSymState; cbn [smode sl sr].
      rewrite evalSymR_symPushOneR, (evalSymR_symPushZeroR Hrz m); reflexivity.
    + destruct (symPopR r1) as [[b2 r2] |] eqn:Hpr2; [| discriminate].
      rewrite (evalSymR_symPopR Hpr2 m); cbn [fst snd].
      destruct b2; cbn [negb].
      * destruct (symPopR r2) as [[b3 r3] |] eqn:Hpr3; [| discriminate].
        rewrite (evalSymR_symPopR Hpr3 m); cbn [fst snd].
        destruct b3; [discriminate |].
        destruct (symPopR r3) as [[b4 r4] |] eqn:Hpr4; [| discriminate].
        destruct (symPushZeroL ls) as [lz |] eqn:Hlz; [| discriminate].
        destruct (symPushZeroL (symPushOL (mkSym 0 1) lz)) as [lBase |] eqn:Hlb; [| discriminate].
        rewrite (evalSymR_symPopR Hpr4 m); cbn [fst snd].
        pose proof (evalSymL_symPushZeroL Hlb m) as Hlb'.
        rewrite evalSymL_symPushOL, evalSym_const, (evalSymL_symPushZeroL Hlz m) in Hlb'.
        destruct b4.
        -- destruct (symPushOneL lBase) as [lOut |] eqn:Hlo; [| discriminate].
           inversion H; subst; clear H; unfold evalSymState; cbn [smode sl sr].
           rewrite (evalSymL_symPushOneL Hlo m), Hlb'; reflexivity.
        -- destruct (symPushZeroL lBase) as [lOut |] eqn:Hlo; [| discriminate].
           inversion H; subst; clear H; unfold evalSymState; cbn [smode sl sr].
           rewrite (evalSymL_symPushZeroL Hlo m), Hlb'; reflexivity.
      * destruct (symPushZeroR (symPushOneR r2)) as [rz |] eqn:Hrz; [| discriminate].
        inversion H; subst; clear H.
        pose proof (evalSymR_symPushZeroR Hrz m) as Hrz'.
        rewrite evalSymR_symPushOneR in Hrz'.
        unfold evalSymState; cbn [smode sl sr].
        rewrite evalSymR_symPushOneR, Hrz'; reflexivity.
Qed.

Lemma symStepDRBase_comm {ls : list SymLTok} {rs : list SymRTok} {s' : SymState}
  (H : symStepDRBase ls rs = Some s') (m : N) :
  stepDRBase (evalSymL m ls) (evalSymR m rs) = Some (evalSymState m s').
Proof.
  unfold symStepDRBase in H; unfold stepDRBase.
  rewrite evalSymL_symIsZeroHeadL.
  destruct (symIsZeroHeadL ls) eqn:Hz; [| exact (symStepDRFallback_comm H m)].
  destruct (symPopL ls) as [[bl lt] |] eqn:Hpl; [| discriminate].
  destruct rs as [| [k1 | k1 | qx | k1] rtail];
    try exact (symStepDRFallback_comm H m).
  destruct (symCases012 qx) as [[bflag | qmv] |] eqn:Hqx; [| | discriminate].
  - destruct bflag.
    + pose proof (symCases012_inl_true Hqx m) as Hq1.
      cbn [evalSymR List.map evalSymRTok]. rewrite Hq1; cbn [N.eqb Pos.eqb].
      rewrite (evalSymL_symPopL Hpl m); cbn [snd].
      assert (Hq1_else :
        (match symPushZeroL lt with
         | Some lz1 =>
           match symPushZeroL lz1, symPushZeroR rtail with
           | Some lz2, Some rz =>
             Some (mkSymState mAL (symPushPL (mkSym 0 0) lz2) (symPushOneR rz))
           | _, _ => None
           end
         | None => None
         end) = Some s' ->
        Some (mkBase mAL (pushPL 0 (pushZeroL (pushZeroL (evalSymL m lt))))
                (pushOneR (pushZeroR (evalSymR m rtail)))) = Some (evalSymState m s')).
      { intro Hm.
        destruct (symPushZeroL lt) as [lz1 |] eqn:Hlz1; [| discriminate].
        destruct (symPushZeroL lz1) as [lz2 |] eqn:Hlz2; [| discriminate].
        destruct (symPushZeroR rtail) as [rz |] eqn:Hrz; [| discriminate].
        inversion Hm; subst; clear Hm.
        unfold evalSymState; cbn [smode sl sr].
        rewrite evalSymL_symPushPL, evalSym_const,
          (evalSymL_symPushZeroL Hlz2 m), (evalSymL_symPushZeroL Hlz1 m),
          evalSymR_symPushOneR, (evalSymR_symPushZeroR Hrz m); reflexivity. }
      destruct rtail as [| [zx | k2 | k2 | k2] [| [k3 | k3 | v | k3] rt]];
        try (cbn [evalSymR evalSymRTok]; exact (Hq1_else H)).
      destruct (symCases012 zx) as [[zflag | zmv] |] eqn:Hzx; [| | discriminate].
      * destruct zflag.
        -- destruct (symPushZeroL (symPushPL v lt)) as [lOut |] eqn:Hlo; [| discriminate].
           destruct (symPushZeroR2 rt) as [remAfterV |] eqn:Hr2; [| discriminate].
           inversion H; subst; clear H.
           cbn [evalSymR List.map evalSymRTok].
           rewrite (symCases012_inl_true Hzx m); cbn [N.eqb Pos.eqb].
           pose proof (evalSymL_symPushZeroL Hlo m) as Hlo'.
           rewrite evalSymL_symPushPL in Hlo'.
           unfold evalSymState; cbn [smode sl sr].
           rewrite Hlo', evalSymR_symPushQR, evalSym_const, (evalSymR_symPushZeroR2 Hr2 m); reflexivity.
        -- cbn [evalSymR evalSymRTok] in Hq1_else |- *.
           rewrite (symCases012_inl_false Hzx m) in Hq1_else |- *; cbn [N.eqb Pos.eqb].
           exact (Hq1_else H).
      * cbn [evalSymR List.map evalSymRTok].
        destruct (symCases012_inr Hzx m) as [_ [_ Hz_ne1]].
        rewrite Hz_ne1. exact (Hq1_else H).
    + pose proof (symStepDRFallback_comm H m) as Hfb.
      cbn [evalSymR List.map evalSymRTok] in Hfb |- *.
      rewrite (symCases012_inl_false Hqx m) in Hfb |- *; cbn [N.eqb Pos.eqb]; exact Hfb.
  - destruct (symCases012_inr Hqx m) as [Hq_ev [Hq_ne0 Hq_ne1]].
    cbn [evalSymR List.map evalSymRTok]. rewrite Hq_ne0, Hq_ne1.
    rewrite (evalSymL_symPopL Hpl m); cbn [snd].
    assert (Hq2_else :
      (match symPushZeroL lt with
       | Some lz1 =>
         match symPushZeroL lz1, symPushZeroR rtail with
         | Some lz2, Some rz =>
           match symPushZeroL (symPushPL qmv (symPushOL (mkSym 0 1) lz2)) with
           | Some lOut => Some (mkSymState mAL lOut (symPushOneR rz))
           | None => None
           end
         | _, _ => None
         end
       | None => None
       end) = Some s' ->
      Some (mkBase mAL (pushZeroL (pushPL (evalSym m qx - 2) (pushOL 1 (pushZeroL (pushZeroL (evalSymL m lt))))))
              (pushOneR (pushZeroR (evalSymR m rtail)))) = Some (evalSymState m s')).
    { intro Hm.
      destruct (symPushZeroL lt) as [lz1 |] eqn:Hlz1; [| discriminate].
      destruct (symPushZeroL lz1) as [lz2 |] eqn:Hlz2; [| discriminate].
      destruct (symPushZeroR rtail) as [rz |] eqn:Hrz; [| discriminate].
      destruct (symPushZeroL (symPushPL qmv (symPushOL (mkSym 0 1) lz2))) as [lOut |] eqn:Hlo; [| discriminate].
      inversion Hm; subst; clear Hm.
      pose proof (evalSymL_symPushZeroL Hlo m) as Hlo'.
      rewrite evalSymL_symPushPL, evalSymL_symPushOL, evalSym_const,
        (evalSymL_symPushZeroL Hlz2 m), (evalSymL_symPushZeroL Hlz1 m) in Hlo'.
      unfold evalSymState; cbn [smode sl sr].
      rewrite Hlo', evalSymR_symPushOneR, (evalSymR_symPushZeroR Hrz m), Hq_ev.
      replace (evalSym m qmv + 2 - 2) with (evalSym m qmv) by lia; reflexivity. }
    destruct rtail as [| [zx | k2 | k2 | k2] [| [k3 | k3 | v | k3] rt]];
      try (cbn [evalSymR evalSymRTok]; exact (Hq2_else H)).
    destruct (symCases012 zx) as [[zflag | zmv] |] eqn:Hzx; [| | discriminate].
    + destruct zflag.
      * destruct (symPushZeroL (symPushPL v lt)) as [lOut |] eqn:Hlo; [| discriminate].
        destruct (symPushZeroR2 rt) as [remAfterV |] eqn:Hr2; [| discriminate].
        inversion H; subst; clear H.
        cbn [evalSymR List.map evalSymRTok].
        rewrite (symCases012_inl_true Hzx m); cbn [N.eqb Pos.eqb].
        pose proof (evalSymL_symPushZeroL Hlo m) as Hlo'.
        rewrite evalSymL_symPushPL in Hlo'.
        unfold evalSymState; cbn [smode sl sr].
        rewrite Hlo', evalSymR_symPushQR, (evalSymR_symPushZeroR2 Hr2 m), Hq_ev.
        replace (evalSym m (mkSym (sa qmv) (sb qmv + 2)))
          with (evalSym m qmv + 2) by (unfold evalSym; cbn [sa sb]; lia).
        reflexivity.
      * cbn [evalSymR evalSymRTok] in Hq2_else |- *.
        rewrite (symCases012_inl_false Hzx m) in Hq2_else |- *; cbn [N.eqb Pos.eqb].
        exact (Hq2_else H).
    + cbn [evalSymR List.map evalSymRTok].
      destruct (symCases012_inr Hzx m) as [_ [_ Hz_ne1]].
      rewrite Hz_ne1. exact (Hq2_else H).
Qed.

Lemma symStepBaseK_comm {s s' : SymState}
  (H : symStepBaseK s = Some s') (m : N) :
  stepBaseK (evalSymState m s) = Some (evalSymState m s').
Proof.
  destruct s as [[|] ls rs]; unfold symStepBaseK in H; cbn [smode sl sr] in H.
  - unfold stepBaseK; cbn [evalSymState mode l r smode sl sr]; fold (evalSymState m s').
    destruct ls as [| [k1 | ox | k1 | k1] [| [k2 | k2 | pk | k2] lt]];
      try exact (symStepALElse_comm H m).
    destruct (symCases012 ox) as [[bflag | omv] |] eqn:Hox; [| | discriminate].
    + destruct bflag.
      * destruct (symPush100RepeatR pk rs) as [rOut |] eqn:Hro; [| discriminate].
        injection H as <-.
        unfold evalSymState; cbn [smode sl sr].
        rewrite evalSymL_symPushOL, evalSym_const, (evalSymR_symPush100RepeatR Hro m).
        cbn [evalSymL evalSymLTok].
        rewrite (symCases012_inl_true Hox m); cbn [N.eqb Pos.eqb]; reflexivity.
      * pose proof (symStepALElse_comm H m) as Hfb.
        cbn [evalSymL evalSymLTok] in Hfb |- *.
        rewrite (symCases012_inl_false Hox m) in Hfb |- *; cbn [N.eqb Pos.eqb]; exact Hfb.
    + pose proof (symStepALElse_comm H m) as Hfb.
      cbn [evalSymL evalSymLTok] in Hfb |- *.
      destruct (symCases012_inr Hox m) as [_ [_ Ho_ne1]].
      rewrite Ho_ne1; exact Hfb.
  - exact (symStepDRBase_comm H m).
Qed.

(** *** Symbolic Mixed-Chain Commutation [symStepChainK_comm] *)

Definition evalSymLeaf (m : N) (lf : SymChainLeaf) : ChainLeaf :=
  match lf with
  | slf_z2q w1 rt => lf_z2q (evalSym m w1) (evalSymR m rt)
  | slf_cap1 => lf_cap1
  | slf_cap2 => lf_cap2
  | slf_capZ21 => lf_capZ21
  | slf_capZ22 => lf_capZ22
  | slf_capB => lf_capB
  end.

Lemma symNatNeqConst_sound {x : SymNat} {c : N}
  (H : symNatNeqConst x c = true) (m : N) :
  evalSym m x <> c.
Proof.
  unfold symNatNeqConst in H.
  destruct (if N.eqb (sa x) 0 then negb (N.eqb (sb x) c) else false) eqn:H1.
  - destruct (N.eqb (sa x) 0) eqn:Ha; [| discriminate].
    apply N.eqb_eq in Ha.
    destruct (N.eqb (sb x) c) eqn:Hb; [discriminate |].
    apply N.eqb_neq in Hb. unfold evalSym; rewrite Ha; lia.
  - apply N.leb_le in H. unfold evalSym; nia.
Qed.

Lemma symRTokNeqConst_sound {x : SymRTok} {y : RTok}
  (H : symRTokNeqConst x y = true) (m : N) :
  evalSymRTok m x <> y.
Proof.
  destruct x, y; cbn [symRTokNeqConst evalSymRTok] in H |- *;
    try (intro Heq; discriminate Heq);
    intro Heq; injection Heq as Heq; exact (symNatNeqConst_sound H m Heq).
Qed.

Lemma symListNeqConst_sound :
  forall (xs : list SymRTok) (ys : list RTok),
    symListNeqConst xs ys = true ->
    forall m : N, evalSymR m xs <> ys.
Proof.
  induction xs as [| x xs' IH]; intros [| y ys'] H m; cbn [symListNeqConst] in H.
  - discriminate.
  - intro Heq; discriminate.
  - intro Heq; discriminate.
  - intro Heq; cbn [evalSymR List.map] in Heq; injection Heq as Hxy Hxys.
    destruct (symRTokNeqConst x y) eqn:Hc.
    + exact (symRTokNeqConst_sound Hc m Hxy).
    + exact (IH ys' H m Hxys).
Qed.

Lemma symNotAnyCapLeaf_sound {rs : list SymRTok}
  (H : symNotAnyCapLeaf rs = true) (m : N) :
  matchCapLeaf (evalSymR m rs) = None.
Proof.
  unfold symNotAnyCapLeaf in H.
  destruct (symListNeqConst rs cap1Toks) eqn:H1; [| discriminate].
  destruct (symListNeqConst rs cap2Toks) eqn:H2; [| discriminate].
  destruct (symListNeqConst rs capZ21Toks) eqn:H3; [| discriminate].
  destruct (symListNeqConst rs capZ22Toks) eqn:H4; [| discriminate].
  unfold matchCapLeaf.
  rewrite (listRBeq_false_of_ne _ _ (symListNeqConst_sound _ _ H1 m)).
  rewrite (listRBeq_false_of_ne _ _ (symListNeqConst_sound _ _ H2 m)).
  rewrite (listRBeq_false_of_ne _ _ (symListNeqConst_sound _ _ H3 m)).
  rewrite (listRBeq_false_of_ne _ _ (symListNeqConst_sound _ _ H4 m)).
  rewrite (listRBeq_false_of_ne _ _ (symListNeqConst_sound _ _ H m)).
  reflexivity.
Qed.

Lemma evalSymR_cap1 (m : N) : evalSymR m symCap1Toks = cap1Toks.
Proof. cbn [symCap1Toks cap1Toks evalSymR evalSymRTok]; rewrite !evalSym_const; reflexivity. Qed.
Lemma evalSymR_cap2 (m : N) : evalSymR m symCap2Toks = cap2Toks.
Proof. cbn [symCap2Toks cap2Toks evalSymR evalSymRTok]; rewrite !evalSym_const; reflexivity. Qed.
Lemma evalSymR_capZ21 (m : N) : evalSymR m symCapZ21Toks = capZ21Toks.
Proof. cbn [symCapZ21Toks capZ21Toks evalSymR evalSymRTok]; rewrite !evalSym_const; reflexivity. Qed.
Lemma evalSymR_capZ22 (m : N) : evalSymR m symCapZ22Toks = capZ22Toks.
Proof. cbn [symCapZ22Toks capZ22Toks evalSymR evalSymRTok]; rewrite !evalSym_const; reflexivity. Qed.
Lemma evalSymR_capB (m : N) : evalSymR m symCapBToks = capBToks.
Proof. cbn [symCapBToks capBToks evalSymR evalSymRTok]; rewrite !evalSym_const; reflexivity. Qed.

Lemma symMatchCapLeaf_sound {rs : list SymRTok} {lf : SymChainLeaf}
  (H : symMatchCapLeaf rs = Some lf) (m : N) :
  matchCapLeaf (evalSymR m rs) = Some (evalSymLeaf m lf).
Proof.
  unfold symMatchCapLeaf in H.
  destruct (listSymRBeq rs symCap1Toks) eqn:H1.
  - inversion H; subst; rewrite (listSymRBeq_eq _ _ H1), evalSymR_cap1. vm_compute; reflexivity.
  - destruct (listSymRBeq rs symCap2Toks) eqn:H2.
    + inversion H; subst; rewrite (listSymRBeq_eq _ _ H2), evalSymR_cap2. vm_compute; reflexivity.
    + destruct (listSymRBeq rs symCapZ21Toks) eqn:H3.
      * inversion H; subst; rewrite (listSymRBeq_eq _ _ H3), evalSymR_capZ21. vm_compute; reflexivity.
      * destruct (listSymRBeq rs symCapZ22Toks) eqn:H4.
        -- inversion H; subst; rewrite (listSymRBeq_eq _ _ H4), evalSymR_capZ22. vm_compute; reflexivity.
        -- destruct (listSymRBeq rs symCapBToks) eqn:H5; [| discriminate].
           inversion H; subst; rewrite (listSymRBeq_eq _ _ H5), evalSymR_capB. vm_compute; reflexivity.
Qed.

Lemma symParseChain_comm_len :
  forall (bound : nat) (u : SymNat) (rs : list SymRTok)
    (uFirst : SymNat) (pairs : list (SepKind * SymNat)) (lf : SymChainLeaf),
    (List.length rs <= bound)%nat ->
    symParseChain u rs = Some (uFirst, pairs, lf) ->
    forall m : N,
      parseChain (evalSym m u) (evalSymR m rs) =
      Some (evalSym m uFirst, List.map (fun p => (fst p, evalSym m (snd p))) pairs, evalSymLeaf m lf).
Proof.
  induction bound as [| bound IH]; intros u rs uFirst pairs lf Hlen H m.
  - destruct rs; [| cbn [List.length] in Hlen; lia].
    cbn [symParseChain symMatchCapLeaf listSymRBeq symNotAnyCapLeaf symListNeqConst] in H; discriminate.
  - destruct rs as [| rt0 rem1];
      [cbn [symParseChain symMatchCapLeaf listSymRBeq symNotAnyCapLeaf symListNeqConst] in H; discriminate |].
    cbn [symParseChain] in H.
    destruct (symMatchCapLeaf (rt0 :: rem1)) as [lf0 |] eqn:Hm.
    + inversion H; subst.
      cbn [parseChain evalSymR List.map].
      change (evalSymRTok m rt0 :: evalSymR m rem1) with (evalSymR m (rt0 :: rem1)).
      rewrite (symMatchCapLeaf_sound Hm m); reflexivity.
    + destruct (symNotAnyCapLeaf (rt0 :: rem1)) eqn:Hna; [| discriminate].
      cbn [parseChain evalSymR].
      change (evalSymRTok m rt0 :: evalSymR m rem1) with (evalSymR m (rt0 :: rem1)).
      rewrite (symNotAnyCapLeaf_sound Hna m).
      cbn [evalSymR].
      destruct rt0 as [zx | ox | qx | bx]; try discriminate.
      * destruct rem1 as [| [z2 | o2 | u1 | b2] r']; try discriminate.
        destruct (symNatBeq zx (mkSym 0 5)) eqn:Hz5.
        -- rewrite (symNatBeq_eq _ _ Hz5) in *.
           destruct (symParseChain (symInc u1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst; clear H.
           cbn [evalSymR List.map evalSymRTok]; rewrite evalSym_const; cbn [N.eqb Pos.eqb].
           pose proof (IH (symInc u1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub m) as Hih.
           rewrite evalSym_symInc in Hih. rewrite Hih; reflexivity.
        -- destruct (symNatBeq zx (mkSym 0 3)) eqn:Hz3.
           ++ rewrite (symNatBeq_eq _ _ Hz3) in *.
              destruct (symParseChain (symInc u1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
              inversion H; subst; clear H.
              cbn [evalSymR List.map evalSymRTok]; rewrite evalSym_const; cbn [N.eqb Pos.eqb].
              pose proof (IH (symInc u1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub m) as Hih.
              rewrite evalSym_symInc in Hih. rewrite Hih; reflexivity.
           ++ destruct (symNatBeq zx (mkSym 0 1)) eqn:Hz1; [| discriminate].
              rewrite (symNatBeq_eq _ _ Hz1) in *.
              inversion H; subst; clear H.
              cbn [evalSymR List.map evalSymRTok evalSymLeaf].
              rewrite evalSym_const, evalSym_symInc; cbn [N.eqb Pos.eqb]; reflexivity.
      * destruct rem1 as [| [zx | o2 | u1 | b2] r']; try discriminate.
        -- destruct r' as [| [z3 | o3 | u2 | b3] r2]; try discriminate.
           destruct (symNatBeq bx (mkSym 0 0)) eqn:Hb0; [| discriminate].
           destruct (symNatBeq zx (mkSym 0 1)) eqn:Hz1; [| discriminate].
           rewrite (symNatBeq_eq _ _ Hb0), (symNatBeq_eq _ _ Hz1) in *.
           destruct (symParseChain (symInc u2) r2) as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst; clear H.
           cbn [evalSymR List.map evalSymRTok]; rewrite !evalSym_const; cbn [N.eqb Pos.eqb].
           pose proof (IH (symInc u2) r2 uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub m) as Hih.
           rewrite evalSym_symInc in Hih. rewrite Hih; reflexivity.
        -- destruct (symNatBeq bx (mkSym 0 2)) eqn:Hb2; [| discriminate].
           rewrite (symNatBeq_eq _ _ Hb2) in *.
           destruct (symParseChain (symInc u1) r') as [[[uf rest] lf'] |] eqn:Hsub; [| discriminate].
           inversion H; subst; clear H.
           cbn [evalSymR List.map evalSymRTok]; rewrite evalSym_const; cbn [N.eqb Pos.eqb].
           pose proof (IH (symInc u1) r' uf rest lf ltac:(cbn [List.length] in Hlen; lia) Hsub m) as Hih.
           rewrite evalSym_symInc in Hih. rewrite Hih; reflexivity.
Qed.

Lemma symParseChain_comm (u : SymNat) (rs : list SymRTok)
  (uFirst : SymNat) (pairs : list (SepKind * SymNat)) (lf : SymChainLeaf) :
  symParseChain u rs = Some (uFirst, pairs, lf) ->
  forall m : N,
    parseChain (evalSym m u) (evalSymR m rs) =
    Some (evalSym m uFirst, List.map (fun p => (fst p, evalSym m (snd p))) pairs, evalSymLeaf m lf).
Proof.
  exact (symParseChain_comm_len (List.length rs) u rs uFirst pairs lf (le_n _)).
Qed.

Lemma symMinNK_comm {x y km : SymNat}
  (H : symMinNK x y = Some km) (m : N) :
  minNK (evalSym m x) (evalSym m y) = evalSym m km.
Proof.
  unfold symMinNK in H; unfold minNK.
  destruct (if N.leb (sa x) (sa y) then N.leb (sb x) (sb y) else false) eqn:H1.
  - inversion H; subst km; clear H.
    destruct (N.leb (sa x) (sa y)) eqn:Ha; [| discriminate].
    apply N.leb_le in Ha; apply N.leb_le in H1.
    assert (Hle : evalSym m x <= evalSym m y) by (unfold evalSym; nia).
    apply N.leb_le in Hle; rewrite Hle; reflexivity.
  - destruct (if N.leb (sa y) (sa x) then N.leb (sb y) (sb x) else false) eqn:H2; [| discriminate].
    inversion H; subst km; clear H.
    destruct (N.leb (sa y) (sa x)) eqn:Ha; [| discriminate].
    apply N.leb_le in Ha; apply N.leb_le in H2.
    assert (Hle : evalSym m y <= evalSym m x) by (unfold evalSym; nia).
    destruct (N.leb (evalSym m x) (evalSym m y)) eqn:Hxy; [apply N.leb_le in Hxy; lia | reflexivity].
Qed.

Lemma symBoundKWith_comm {curK nextK : option SymNat} {u : SymNat} {req : N} {sd : SDelta}
  (H : symBoundKWith curK u req sd = Some nextK) (m : N) :
  boundKWith (option_map (evalSym m) curK) (evalSym m u) req sd =
  Some (option_map (evalSym m) nextK).
Proof.
  unfold symBoundKWith in H; unfold boundKWith.
  destruct (N.leb req (sb u)) eqn:Hreq; [| discriminate].
  apply N.leb_le in Hreq.
  assert (Hreq_ev : N.leb req (evalSym m u) = true)
    by (apply N.leb_le; unfold evalSym; nia).
  rewrite Hreq_ev.
  destruct (isNeg sd) eqn:Hneg; cbn [negb] in H.
  - destruct (N.leb 1 (mag sd)) eqn:Hmag; cbn [negb] in H.
    + apply N.leb_le in Hmag.
      destruct (N.leb (req + mag sd) (sb u)) eqn:Hmin; [| discriminate].
      destruct (N.eqb (N.modulo (sa u) (mag sd)) 0) eqn:Hmod0; [| discriminate].
      apply N.leb_le in Hmin; apply N.eqb_eq in Hmod0.
      assert (Hmin_ev : N.leb (req + mag sd) (evalSym m u) = true)
        by (apply N.leb_le; unfold evalSym; nia).
      rewrite Hmin_ev.
      assert (Hdiv_eq : N.div (evalSym m u - req) (mag sd) =
                        evalSym m (mkSym (N.div (sa u) (mag sd)) (N.div (sb u - req) (mag sd)))).
      { pose proof (N.div_mod (sa u) (mag sd) ltac:(lia)) as Hdm.
        rewrite Hmod0, N.add_0_r in Hdm.
        assert (Hnum : evalSym m u - req = (sb u - req) + ((N.div (sa u) (mag sd)) * m) * (mag sd))
          by (unfold evalSym; nia).
        rewrite Hnum, N.div_add by lia.
        unfold evalSym; cbn [sa sb]; lia. }
      rewrite Hdiv_eq.
      destruct curK as [k0 |]; cbn [option_map].
      * destruct (symMinNK k0 (mkSym (N.div (sa u) (mag sd)) (N.div (sb u - req) (mag sd))))
          as [km |] eqn:Hmink; [| discriminate].
        inversion H; subst nextK; cbn [option_map].
        rewrite (symMinNK_comm Hmink m); reflexivity.
      * inversion H; subst nextK; reflexivity.
    + inversion H; subst nextK; reflexivity.
  - inversion H; subst nextK; reflexivity.
Qed.

Lemma chainBaseReq_evalSym (m : N) (tl : list (SepKind * SymNat)) (lf : SymChainLeaf) :
  chainBaseReq (List.map (fun p => (fst p, evalSym m (snd p))) tl) (evalSymLeaf m lf) =
  symChainBaseReq tl lf.
Proof.
  destruct tl, lf; reflexivity.
Qed.

Lemma symFoldChainRTL_comm :
  forall (pairs : list (SepKind * SymNat)) (lf : SymChainLeaf)
    (nPos nNeg : N) (optK : option SymNat) (items : list (SepKind * SymNat * SDelta)),
    symFoldChainRTL pairs lf = Some (nPos, nNeg, optK, items) ->
    forall m : N,
      foldChainRTL (List.map (fun p => (fst p, evalSym m (snd p))) pairs) (evalSymLeaf m lf) =
      Some (nPos, nNeg, option_map (evalSym m) optK,
            List.map (fun it => (fst (fst it), evalSym m (snd (fst it)), snd it)) items).
Proof.
  induction pairs as [| [sep uNext] tl IH];
    intros lf nPosOut nNegOut optKOut itemsOut H m.
  - cbn [symFoldChainRTL] in H; cbn [List.map foldChainRTL].
    destruct lf; inversion H; subst; reflexivity.
  - cbn [symFoldChainRTL] in H.
    destruct (symFoldChainRTL tl lf) as [[[[nPos nNeg] curK] acc] |] eqn:Hsub; [| discriminate].
    cbn [List.map fst snd foldChainRTL].
    rewrite (IH lf nPos nNeg curK acc Hsub m), chainBaseReq_evalSym.
    destruct sep;
      (destruct (symBoundKWith curK uNext _ _) as [nextK |] eqn:Hbnd; [| discriminate]);
      inversion H; subst; clear H;
      rewrite (symBoundKWith_comm Hbnd m); reflexivity.
Qed.

Lemma symApplyDeltaK_comm {u k out : SymNat} {sd : SDelta}
  (H : symApplyDeltaK u k sd = Some out) (m : N) :
  applyDeltaK (evalSym m u) (evalSym m k) sd = evalSym m out.
Proof.
  unfold symApplyDeltaK in H; unfold applyDeltaK.
  destruct (isNeg sd) eqn:Hneg; cbn [negb] in H.
  - destruct (N.leb (mag sd * sa k) (sa u)) eqn:Ha; [| discriminate].
    destruct (N.leb (mag sd * sb k) (sb u)) eqn:Hb; [| discriminate].
    inversion H; subst out; clear H.
    apply N.leb_le in Ha; apply N.leb_le in Hb.
    unfold evalSym; cbn [sa sb]; nia.
  - inversion H; subst out; clear H.
    unfold evalSym; cbn [sa sb]; nia.
Qed.

Lemma symBuildChainTail_comm :
  forall (items : list (SepKind * SymNat * SDelta)) (k : SymNat)
    (lf : SymChainLeaf) (uCur : SymNat) (out : list SymRTok),
    symBuildChainTail items k lf uCur = Some out ->
    forall m : N,
      buildChainTail (List.map (fun it => (fst (fst it), evalSym m (snd (fst it)), snd it)) items)
        (evalSym m k) (evalSymLeaf m lf) (evalSym m uCur) = evalSymR m out.
Proof.
  induction items as [| [[sep uNext] sd] tl IH]; intros k lf uCur out H m;
    cbn [symBuildChainTail] in H.
  - destruct (N.leb 1 (sb uCur)) eqn:Hub1; [| discriminate].
    apply N.leb_le in Hub1.
    assert (Hsub_u : evalSym m uCur - 1 = evalSym m (mkSym (sa uCur) (sb uCur - 1)))
      by (unfold evalSym; cbn [sa sb]; lia).
    cbn [List.map buildChainTail]. rewrite Hsub_u.
    destruct lf as [w1 rt | | | | |].
    + cbn [evalSymLeaf].
      destruct (symNatBeq w1 k) eqn:Hwk.
      * rewrite (symNatBeq_eq _ _ Hwk) in *.
        destruct (symPushZeroR2 rt) as [remAfter |] eqn:Hr2; [| discriminate].
        inversion H; subst out; clear H.
        rewrite N.eqb_refl, evalSymR_symPushQR, (evalSymR_symPushZeroR2 Hr2 m); reflexivity.
      * destruct (N.leb (sa k) (sa w1)) eqn:Hle_a; [| discriminate].
        destruct (N.leb (sb k + 1) (sb w1)) eqn:Hle_b; [| discriminate].
        inversion H; subst out; clear H.
        apply N.leb_le in Hle_a; apply N.leb_le in Hle_b.
        assert (Hne_ev : N.eqb (evalSym m w1) (evalSym m k) = false)
          by (apply N.eqb_neq; unfold evalSym; nia).
        rewrite Hne_ev; cbn [pushQR evalSymR evalSymRTok].
        rewrite evalSym_const.
        replace (evalSym m w1 - evalSym m k - 1)
          with (evalSym m (mkSym (sa w1 - sa k) (sb w1 - sb k - 1)))
          by (unfold evalSym; cbn [sa sb]; nia).
        reflexivity.
    + inversion H; subst; cbn [evalSymR List.map evalSymRTok]; rewrite evalSymR_cap1; reflexivity.
    + inversion H; subst; cbn [evalSymR List.map evalSymRTok]; rewrite evalSymR_cap2; reflexivity.
    + inversion H; subst; cbn [evalSymR List.map evalSymRTok]; rewrite evalSymR_capZ21; reflexivity.
    + inversion H; subst; cbn [evalSymR List.map evalSymRTok]; rewrite evalSymR_capZ22; reflexivity.
    + inversion H; subst; cbn [evalSymR List.map evalSymRTok]; rewrite evalSymR_capB; reflexivity.
  - destruct (N.leb 1 (sb uCur)) eqn:Hub1; [| discriminate].
    apply N.leb_le in Hub1.
    destruct (symApplyDeltaK uNext k sd) as [uNextNew |] eqn:Happ; [| discriminate].
    destruct (symBuildChainTail tl k lf uNextNew) as [tail |] eqn:Htl; [| discriminate].
    cbn [List.map fst snd buildChainTail].
    replace (evalSym m uCur - 1) with (evalSym m (mkSym (sa uCur) (sb uCur - 1)))
      by (unfold evalSym; cbn [sa sb]; lia).
    rewrite (symApplyDeltaK_comm Happ m), (IH k lf uNextNew tail Htl m).
    destruct sep; inversion H; subst out;
      cbn [evalSymR List.map evalSymRTok]; rewrite !evalSym_const; reflexivity.
Qed.

Lemma chainReq0_evalSym (m : N) (pairs : list (SepKind * SymNat)) (lf : SymChainLeaf) :
  chainReq0 (List.map (fun p => (fst p, evalSym m (snd p))) pairs) (evalSymLeaf m lf) =
  symChainReq0 pairs lf.
Proof.
  destruct pairs, lf; reflexivity.
Qed.

Lemma symStepChainK_comm {s s' : SymState}
  (H : symStepChainK s = Some s') (m : N) :
  stepChainK (evalSymState m s) = Some (evalSymState m s').
Proof.
  destruct s as [[|] ls rs]; unfold symStepChainK in H; cbn [smode sl sr] in H; [discriminate |].
  unfold evalSymState, stepChainK; cbn [mode l r smode sl sr].
  rewrite evalSymL_symIsZeroHeadL.
  destruct (symIsZeroHeadL ls) eqn:Hz; [| discriminate].
  destruct rs as [| [k0 | k0 | u0_0 | k0] rem]; try discriminate.
  destruct (symParseChain (symInc u0_0) rem) as [[[uFirst pairs] lf] |] eqn:Hp; [| discriminate].
  destruct (symFoldChainRTL pairs lf) as [[[[nPos nNeg] curK] items] |] eqn:Hf; [| discriminate].
  destruct (symBoundKWith curK uFirst (symChainReq0 pairs lf) (mkSDelta true (2 * nNeg)))
    as [[kVal |] |] eqn:Hb0; try discriminate.
  destruct (N.leb 1 (sb kVal)) eqn:Hk1; [| discriminate].
  destruct (N.leb 1 ((nPos + nNeg) * sb kVal)) eqn:Hnk1; [| discriminate].
  destruct (symApplyDeltaK uFirst kVal (mkSDelta true (2 * nNeg))) as [u0New |] eqn:Happ0; [| discriminate].
  destruct (symPopL ls) as [[bl lt] |] eqn:Hpl; [| discriminate].
  destruct (symPushZeroL (symPushPL (mkSym ((nPos + nNeg) * sa kVal) ((nPos + nNeg) * sb kVal - 1)) lt))
    as [newL |] eqn:Hnl; [| discriminate].
  destruct (symBuildChainTail items kVal lf u0New) as [newR |] eqn:Hnr; [| discriminate].
  inversion H; subst s'; clear H.
  cbn [evalSymR List.map evalSymRTok smode sl sr].
  pose proof (symParseChain_comm (symInc u0_0) rem uFirst pairs lf Hp m) as Hp'.
  rewrite evalSym_symInc in Hp'. rewrite Hp'.
  rewrite (symFoldChainRTL_comm pairs lf nPos nNeg curK items Hf m), chainReq0_evalSym.
  rewrite (symBoundKWith_comm Hb0 m); cbn [option_map].
  apply N.leb_le in Hk1; apply N.leb_le in Hnk1.
  assert (Hkv1 : N.leb 1 (evalSym m kVal) = true)
    by (apply N.leb_le; unfold evalSym; nia).
  rewrite Hkv1.
  rewrite (evalSymL_symPopL Hpl m); cbn [snd].
  pose proof (evalSymL_symPushZeroL Hnl m) as Hnl'.
  rewrite evalSymL_symPushPL in Hnl'.
  replace (evalSym m kVal * (nPos + nNeg) - 1)
    with (evalSym m (mkSym ((nPos + nNeg) * sa kVal) ((nPos + nNeg) * sb kVal - 1)))
    by (unfold evalSym; cbn [sa sb]; nia).
  rewrite <- Hnl', (symApplyDeltaK_comm Happ0 m),
    (symBuildChainTail_comm items kVal lf u0New newR Hnr m).
  reflexivity.
Qed.

Lemma symStepAutoK_sound {s s' : SymState}
  (H : symStepAutoK s = Some s') (m : N) :
  encodeBase (evalSymState m s) -[ tm ]->+ encodeBase (evalSymState m s').
Proof.
  unfold symStepAutoK in H.
  destruct (symStepChainK s) as [sc |] eqn:Hc.
  - inversion H; subst s'. exact (stepChainK_sound _ _ (symStepChainK_comm Hc m)).
  - exact (stepBaseK_sound _ _ (symStepBaseK_comm H m)).
Qed.

Lemma iter_symStepAutoOpt_None (p : positive) :
  Pos.iter symStepAutoOpt None p = None.
Proof.
  induction p as [p IHp | p IHp |]; cbn [Pos.iter]; rewrite ?IHp; reflexivity.
Qed.

Lemma symRunStepsPos_plus (p : positive) :
  forall (s out : SymState) (m : N),
    symRunStepsPos p s = Some out ->
    encodeBase (evalSymState m s) -[ tm ]->+ encodeBase (evalSymState m out).
Proof.
  unfold symRunStepsPos.
  induction p as [p IHp | p IHp |]; intros s out m Hiter; cbn [Pos.iter] in Hiter.
  - destruct (Pos.iter symStepAutoOpt (Some s) p) as [s1 |] eqn:Hs1;
      [| rewrite iter_symStepAutoOpt_None in Hiter; discriminate].
    destruct (Pos.iter symStepAutoOpt (Some s1) p) as [s2 |] eqn:Hs2;
      [| discriminate].
    eapply progress_trans; [exact (IHp s s1 m Hs1) |].
    eapply progress_trans; [exact (IHp s1 s2 m Hs2) |].
    exact (symStepAutoK_sound Hiter m).
  - destruct (Pos.iter symStepAutoOpt (Some s) p) as [s1 |] eqn:Hs1;
      [| rewrite iter_symStepAutoOpt_None in Hiter; discriminate].
    eapply progress_trans; [exact (IHp s s1 m Hs1) | exact (IHp s1 out m Hiter)].
  - exact (symStepAutoK_sound Hiter m).
Qed.

(** ** Section 6: 16-State Hub Family Closure, Transient Verification & [nonhalt] *)

Definition hubCapToks (idx : N) : list RTok :=
  if N.eqb idx 0 then cap1Toks
  else if N.eqb idx 1 then cap1Toks
  else if N.eqb idx 8 then cap1Toks
  else if N.eqb idx 9 then cap1Toks
  else if N.eqb idx 2 then cap2Toks
  else if N.eqb idx 3 then cap2Toks
  else if N.eqb idx 10 then cap2Toks
  else if N.eqb idx 11 then cap2Toks
  else if N.eqb idx 4 then capZ21Toks
  else if N.eqb idx 5 then capZ21Toks
  else if N.eqb idx 12 then capZ21Toks
  else if N.eqb idx 13 then capZ21Toks
  else capZ22Toks.

Definition hubSymCapToks (idx : N) : list SymRTok :=
  if N.eqb idx 0 then symCap1Toks
  else if N.eqb idx 1 then symCap1Toks
  else if N.eqb idx 8 then symCap1Toks
  else if N.eqb idx 9 then symCap1Toks
  else if N.eqb idx 2 then symCap2Toks
  else if N.eqb idx 3 then symCap2Toks
  else if N.eqb idx 10 then symCap2Toks
  else if N.eqb idx 11 then symCap2Toks
  else if N.eqb idx 4 then symCapZ21Toks
  else if N.eqb idx 5 then symCapZ21Toks
  else if N.eqb idx 12 then symCapZ21Toks
  else if N.eqb idx 13 then symCapZ21Toks
  else symCapZ22Toks.

Definition hubD (idx : N) : N :=
  if N.eqb idx 0 then 5 else if N.eqb idx 1 then 5
  else if N.eqb idx 2 then 7 else if N.eqb idx 3 then 7
  else if N.eqb idx 4 then 9 else if N.eqb idx 5 then 9
  else if N.eqb idx 6 then 11 else if N.eqb idx 7 then 11
  else if N.eqb idx 8 then 29 else if N.eqb idx 9 then 29
  else if N.eqb idx 10 then 31 else if N.eqb idx 11 then 31
  else if N.eqb idx 12 then 33 else if N.eqb idx 13 then 33
  else 35.

Definition hubR12 (idx : N) : N :=
  if N.eqb idx 0 then 0 else if N.eqb idx 8 then 0
  else if N.eqb idx 1 then 6 else if N.eqb idx 9 then 6
  else if N.eqb idx 2 then 1 else if N.eqb idx 10 then 1
  else if N.eqb idx 3 then 7 else if N.eqb idx 11 then 7
  else if N.eqb idx 4 then 2 else if N.eqb idx 12 then 2
  else if N.eqb idx 5 then 8 else if N.eqb idx 13 then 8
  else if N.eqb idx 6 then 3 else if N.eqb idx 14 then 3
  else 9.

Definition hubState (idx n : N) : BaseState :=
  let bVal := 12 * (n + 4) + hubR12 idx in
  let aVal := 4 * bVal + hubD idx in
  mkBase mAL [] (R_o 0 :: R_q (aVal - 1) :: R_ba 1 :: R_q (bVal - 1) :: hubCapToks idx).

Definition hubSymState (idx mulM addM : N) : SymState :=
  let bA := 12 * mulM in
  let bB := 12 * (addM + 4) + hubR12 idx in
  let aA := 4 * bA in
  let aB := 4 * bB + hubD idx in
  mkSymState mAL []
    (SR_o (mkSym 0 0) :: SR_q (mkSym aA (aB - 1)) :: SR_ba (mkSym 0 1) ::
     SR_q (mkSym bA (bB - 1)) :: hubSymCapToks idx).

Definition checkSymRuleK (steps : positive) (srcIdx parity dstIdx cOut : N) : bool :=
  match symRunStepsPos steps (hubSymState srcIdx 2 parity) with
  | Some out => symStateBeq out (hubSymState dstIdx 3 cOut)
  | None => false
  end.

Lemma evalSymR_hubSymCapToks (idx m : N) :
  evalSymR m (hubSymCapToks idx) = hubCapToks idx.
Proof.
  unfold hubSymCapToks, hubCapToks.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  rewrite ?evalSymR_cap1, ?evalSymR_cap2, ?evalSymR_capZ21, ?evalSymR_capZ22;
  reflexivity.
Qed.

Lemma evalSymState_hubSymState (idx mulM addM m : N) :
  evalSymState m (hubSymState idx mulM addM) = hubState idx (mulM * m + addM).
Proof.
  unfold hubSymState, hubState, evalSymState.
  remember (hubSymCapToks idx) as caps eqn:Hcaps.
  cbn [smode sl sr evalSymL evalSymR evalSymRTok].
  subst caps.
  rewrite !evalSym_const, evalSymR_hubSymCapToks.
  set (bA := 12 * mulM).
  set (bB := 12 * (addM + 4) + hubR12 idx).
  set (aA := 4 * bA).
  set (aB := 4 * bB + hubD idx).
  assert (HbB : 1 <= bB) by (subst bB; lia).
  assert (HaB : 1 <= aB) by (subst aB; lia).
  replace (evalSym m (mkSym bA (bB - 1))) with (12 * (mulM * m + addM + 4) + hubR12 idx - 1)
    by (unfold evalSym; cbn [sa sb]; subst bA bB; nia).
  replace (evalSym m (mkSym aA (aB - 1))) with (4 * (12 * (mulM * m + addM + 4) + hubR12 idx) + hubD idx - 1)
    by (unfold evalSym; cbn [sa sb]; subst aA aB bA bB; nia).
  reflexivity.
Qed.

Lemma checkSymRuleK_sound {steps : positive} {srcIdx parity dstIdx cOut : N}
  (H : checkSymRuleK steps srcIdx parity dstIdx cOut = true) (m : N) :
  encodeBase (hubState srcIdx (2 * m + parity)) -[ tm ]->+
  encodeBase (hubState dstIdx (3 * m + cOut)).
Proof.
  unfold checkSymRuleK in H.
  destruct (symRunStepsPos steps (hubSymState srcIdx 2 parity)) as [out |] eqn:Hr; [| discriminate].
  rewrite (symStateBeq_eq _ _ H) in Hr.
  pose proof (symRunStepsPos_plus steps _ _ m Hr) as Hplus.
  rewrite !evalSymState_hubSymState in Hplus.
  exact Hplus.
Qed.

Lemma sym_rule_0  : checkSymRuleK 1343%positive 0 0 15 1 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_1  : checkSymRuleK 1343%positive 0 1 14 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_2  : checkSymRuleK 1280%positive 1 0 11 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_3  : checkSymRuleK 1280%positive 1 1 10 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_4  : checkSymRuleK 967%positive  2 0  6 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_5  : checkSymRuleK 967%positive  2 1  7 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_6  : checkSymRuleK 904%positive  3 0  2 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_7  : checkSymRuleK 904%positive  3 1  3 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_8  : checkSymRuleK 1196%positive 4 0 12 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_9  : checkSymRuleK 1196%positive 4 1 13 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_10 : checkSymRuleK 1139%positive 5 0  8 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_11 : checkSymRuleK 1139%positive 5 1  9 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_12 : checkSymRuleK 963%positive  6 0  5 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_13 : checkSymRuleK 963%positive  6 1  4 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_14 : checkSymRuleK 906%positive  7 0  1 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_15 : checkSymRuleK 906%positive  7 1  0 5 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_16 : checkSymRuleK 1214%positive 8 0  9 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_17 : checkSymRuleK 1214%positive 8 1  8 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_18 : checkSymRuleK 1271%positive 9 0 12 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_19 : checkSymRuleK 1271%positive 9 1 13 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_20 : checkSymRuleK 846%positive 10 0  0 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_21 : checkSymRuleK 846%positive 10 1  1 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_22 : checkSymRuleK 903%positive 11 0  5 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_23 : checkSymRuleK 903%positive 11 1  4 5 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_24 : checkSymRuleK 1268%positive 12 0 15 2 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_25 : checkSymRuleK 1268%positive 12 1 14 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_26 : checkSymRuleK 1205%positive 13 0 11 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_27 : checkSymRuleK 1205%positive 13 1 10 5 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_28 : checkSymRuleK 1027%positive 14 0  6 3 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_29 : checkSymRuleK 1027%positive 14 1  7 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_30 : checkSymRuleK 964%positive 15 0  2 4 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sym_rule_31 : checkSymRuleK 964%positive 15 1  3 5 = true. Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma attractor_step_plus (idx n : N) (Hidx : idx < 16) :
  exists idx' n' : N,
    idx' < 16 /\ encodeBase (hubState idx n) -[ tm ]->+ encodeBase (hubState idx' n').
Proof.
  set (m := N.div n 2).
  pose proof (N.div_mod n 2 ltac:(lia)) as Hdm; fold m in Hdm.
  pose proof (N.mod_upper_bound n 2 ltac:(lia)) as Hmb.
  assert (Hpar : N.modulo n 2 = 0 \/ N.modulo n 2 = 1) by lia.
  assert (Hidx16 : idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/
                   idx = 4 \/ idx = 5 \/ idx = 6 \/ idx = 7 \/
                   idx = 8 \/ idx = 9 \/ idx = 10 \/ idx = 11 \/
                   idx = 12 \/ idx = 13 \/ idx = 14 \/ idx = 15) by lia.
  destruct Hpar as [Hp0 | Hp1].
  - replace n with (2 * m + 0) by lia.
    destruct Hidx16 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
                       [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]].
    + exists 15, (3 * m + 1); split; [lia | exact (checkSymRuleK_sound sym_rule_0 m)].
    + exists 11, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_2 m)].
    + exists  6, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_4 m)].
    + exists  2, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_6 m)].
    + exists 12, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_8 m)].
    + exists  8, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_10 m)].
    + exists  5, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_12 m)].
    + exists  1, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_14 m)].
    + exists  9, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_16 m)].
    + exists 12, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_18 m)].
    + exists  0, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_20 m)].
    + exists  5, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_22 m)].
    + exists 15, (3 * m + 2); split; [lia | exact (checkSymRuleK_sound sym_rule_24 m)].
    + exists 11, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_26 m)].
    + exists  6, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_28 m)].
    + exists  2, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_30 m)].
  - replace n with (2 * m + 1) by lia.
    destruct Hidx16 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
                       [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]].
    + exists 14, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_1 m)].
    + exists 10, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_3 m)].
    + exists  7, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_5 m)].
    + exists  3, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_7 m)].
    + exists 13, (3 * m + 3); split; [lia | exact (checkSymRuleK_sound sym_rule_9 m)].
    + exists  9, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_11 m)].
    + exists  4, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_13 m)].
    + exists  0, (3 * m + 5); split; [lia | exact (checkSymRuleK_sound sym_rule_15 m)].
    + exists  8, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_17 m)].
    + exists 13, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_19 m)].
    + exists  1, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_21 m)].
    + exists  4, (3 * m + 5); split; [lia | exact (checkSymRuleK_sound sym_rule_23 m)].
    + exists 14, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_25 m)].
    + exists 10, (3 * m + 5); split; [lia | exact (checkSymRuleK_sound sym_rule_27 m)].
    + exists  7, (3 * m + 4); split; [lia | exact (checkSymRuleK_sound sym_rule_29 m)].
    + exists  3, (3 * m + 5); split; [lia | exact (checkSymRuleK_sound sym_rule_31 m)].
Qed.

End Family.

Definition checkEntry start idx steps :=
  match runStepsPos steps start with
  | Some out =>
    match r out with
    | _ :: _ :: _ :: R_q bMinus1 :: _ =>
      stateBeqK out (hubState idx (N.div bMinus1 12 - 4))
    | _ => false
    end
  | None => false
  end.

Lemma checkEntry_sound v start idx steps :
  checkEntry start idx steps = true ->
  exists n, encodeBase start -[ variant_tm v ]->* encodeBase (hubState idx n).
Proof.
  unfold checkEntry.
  destruct (runStepsPos steps start) as [out|] eqn:Hrun; [|discriminate].
  destruct (r out) as [| t0 [| t1 [| t2 [| [k|k|bMinus1|k] rest]]]]; try discriminate.
  intro H. exists (N.div bMinus1 12 - 4).
  rewrite <- (stateBeqK_eq _ _ H).
  exact (runStepsPos_sound v steps start out Hrun).
Qed.

Lemma nonhalt_from_entry v target (f : Q * tape -> Q * tape)
    (Hstep : forall c c', c -[ variant_tm v ]-> c' -> f c -[ target ]-> f c')
    start idx fuel :
  c0 -[ target ]->* f (encodeBase start) ->
  idx < 16 -> checkEntry start idx fuel = true ->
  ~ halts target c0.
Proof.
  intros Hinit Hidx Hcheck.
  destruct (checkEntry_sound v start idx fuel Hcheck) as [n Hn].
  eapply multistep_nonhalt; [exact Hinit|].
  assert (He : forall c c', c -[ variant_tm v ]->* c' -> f c -[ target ]->* f c')
    by (intros c c' H; induction H; eauto using evstep).
  assert (Hp : forall c c', c -[ variant_tm v ]->+ c' -> f c -[ target ]->+ f c')
    by (intros c c' H; induction H; eauto using progress).
  eapply multistep_nonhalt; [exact (He _ _ Hn)|].
  eapply progress_nonhalt_cond with (i0 := (idx,n))
    (C := fun '(j,k) => f (encodeBase (hubState j k)))
    (P := fun '(j,_) => j < 16); [|exact Hidx].
  intros [j k] Hj.
  destruct (attractor_step_plus v j k Hj) as [j' [k' [Hj' Hrun]]].
  exists (j',k'); eauto.
Qed.

End Shared.

Lemma same_step c c' :
  c -[ Shared.variant_tm false ]-> c' -> c -[ tm ]-> c'.
Proof.
  destruct 1 as [q q' s s' l r H|q q' s s' l r H];
    constructor; destruct q,s; exact H.
Qed.

Definition start := Shared.mkBase Shared.mAL [] [].

Lemma init : c0 -[ tm ]->* Shared.encodeBase start.
Proof. eapply evstep_refl'; solve_const0_eq. Qed.

Lemma entry : Shared.checkEntry start 4%N 2122236%positive = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  exact (Shared.nonhalt_from_entry false tm (fun x => x) same_step
    start 4%N 2122236%positive init ltac:(lia) entry).
Qed.
End TM104.

Module TM96.
Definition tm := Eval compute in (TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1RD_0LD---").
Import TM104.Shared.

Definition ren (q : Q) : Q :=
  match q with A => C | B => A | C => D | D => B | E => E | F => F end.
Definition relocate '(q,t) : Q * tape := (ren q, flip_tape t).

Lemma mirror_step c c' :
  c -[ variant_tm true ]-> c' -> relocate c -[ tm ]-> relocate c'.
Proof.
  destruct 1 as [q q' s s' l r H|q q' s s' l r H]; cbn;
    [apply step_right|apply step_left];
    destruct q,s; cbn in H; inversion H; reflexivity.
Qed.

Definition start := mkBase mAL [L_o 0%N] [].

Lemma init : c0 -[ tm ]->* relocate (encodeBase start).
Proof.
  unfold c0, tape0, relocate, encodeBase, start, mEncL; cbn [mode l r decL decR].
  rewrite repOne_succ, repOne_0; cbn [encTape hd tl].
  eapply evstep_step; [exact (step_right (q := A) (q' := B) (s := S0) (s' := S1) eq_refl) |].
  cbn.
  eapply evstep_step; [exact (step_left (q := B) (q' := C) (s := S0) (s' := S0) eq_refl) |].
  eapply evstep_refl'; solve_const0_eq.
Qed.

Lemma entry : checkEntry start 2%N 3149825%positive = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  exact (nonhalt_from_entry true tm relocate mirror_step
    start 2%N 3149825%positive init ltac:(lia) entry).
Qed.
End TM96.
