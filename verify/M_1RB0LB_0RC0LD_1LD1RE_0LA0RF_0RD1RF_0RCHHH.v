(* 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---, 1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC--- and
   1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC--- halt from the blank tape.

   The visit law ([Vis]): the head enters a stream s from the left in state C (the cell left of it is 0) and comes
   back in state A one cell left of that 0, with s changed: visit(0 x) = 1 x, visit(100 x) = 000 visit(x),
   visit(110 x) = 000 visit(x), visit(1010 x) = 1010 visit(visit(x)); a visit that meets 1011 halts.  A round puts
   1 0 in front of the stream and makes one visit, so 2^j visits (j = k/2) cross the word V after (10)^k.  This is
   the rewriting system of the wiki's Beaver Math Olympiad problem 10 (first table).

   Tokens.  A round rewrites every block it crosses into d00 (a digit) or 1010 (L), so after the round the word is a
   list of tokens 0 = 000, 1 = 100, L = 1010.  The next round's blocks never share a boundary with them: each block
   is the end of one token (from offset 1 or 2) and the start of the next.  So a round is a transducer over tokens
   ([estep]): the state is the offset in the current token, the input the next token, the output one token.  While
   the count is 2^e - c with e large only c matters ([fstep]; c stays small).  Six tokens (three pairs) go through one
   lookup in a trie built in the VM from [fstep] ([table], [look2]); the end of the word is done with the exact count
   over tokens and then cells ([escan], [cscan]).  [check 161210] runs 161,210 rounds (1.65e10 tokens read) and finds
   that the next round meets 1011.

   The visit law and its counting lemmas ([VS], [law_Z] ... [hvs_1011]) are proved first. *)
From BusyCoq Require Import Individual62.
From Coq Require Import NArith Lia Bool PeanoNat String.
From Coq Require Import Lists.List. Import ListNotations.
Set Default Goal Selector "!".
Open Scope N_scope.

(* ======================= the computation ======================= *)

Inductive tok := T0 | T1 | TL.
Definition tcells (t : tok) : list bool :=
  match t with T0 => [false; false; false] | T1 => [true; false; false] | TL => [true; false; true; false] end.
Fixpoint tokcells (ts : list tok) : list bool := match ts with [] => [] | t :: ts => tcells t ++ tokcells ts end.
Definition dig (b : bool) : tok := if b then T1 else T0.

(* the round's block starts inside the current token at offset 1 (ph = true) or 2 (ph = false) *)
Inductive kind := K00 | K0 | K10 | KX.
Definition kindof (ph : bool) (t : tok) : kind :=
  match ph, t with true, TL => KX | true, _ => K00 | false, TL => K10 | false, _ => K0 end.
Definition nextph (k : kind) (t' : tok) : bool :=
  match k, t' with K00, T0 => true | K10, T0 => true | _, _ => false end.
Definition off (ph : bool) : nat := if ph then 1 else 2.

(* one block with the exact count n >= 1 *)
Inductive eres := ECont (o : tok) (n : N) | EDie (pre : list bool) | EBad.
Definition estep (k : kind) (n : N) (t' : tok) : eres :=
  match k with
  | K00 => match t' with
           | T0 => ECont (dig (N.odd n)) (N.div2 n)
           | _ => if N.eqb n 1 then EDie [true; false] else ECont TL (N.double (N.pred n))
           end
  | K0 => match t' with
          | T0 => ECont (dig (N.odd n)) (N.div2 n)
          | _ => if N.eqb n 1 then EDie [true] else ECont (dig (N.odd n)) (N.div2 n)
          end
  | K10 => match t' with
           | T0 => ECont (dig (N.even n)) (N.div2 (N.succ n))
           | _ => ECont TL (N.double n)
           end
  | KX => EBad
  end.

(* one block with the count 2^e - c, e large *)
Definition fstep (k : kind) (c : N) (t' : tok) : option (tok * N) :=
  match k with
  | K00 => match t' with T0 => Some (dig (N.odd c), N.div2 (N.succ c)) | _ => Some (TL, N.double (N.succ c)) end
  | K0 => Some (dig (N.odd c), N.div2 (N.succ c))
  | K10 => match t' with T0 => Some (dig (N.even c), N.div2 c) | _ => Some (TL, N.double c) end
  | KX => None
  end.

Fixpoint fsteps (ph : bool) (c : N) (t : tok) (ts : list tok) : option (list tok * bool * N) :=
  match ts with
  | [] => Some ([], ph, c)
  | t' :: ts' =>
    let k := kindof ph t in
    match fstep k c t' with
    | Some (o, c') => match fsteps (nextph k t') c' t' ts' with
                      | Some (os, ph', c'') => Some (o :: os, ph', c'')
                      | None => None
                      end
    | None => None
    end
  end.
Definition nL (l : list tok) : nat := length (filter (fun t => match t with TL => true | _ => false end) l).

(* chunks: eight tokens as four pairs, so that one trie level reads two tokens *)
Inductive pr := P00 | P01 | P0L | P10 | P11 | P1L | PL0 | PL1 | PLL.
Definition pfst (p : pr) : tok := match p with P00 | P01 | P0L => T0 | P10 | P11 | P1L => T1 | _ => TL end.
Definition psnd (p : pr) : tok := match p with P00 | P10 | PL0 => T0 | P01 | P11 | PL1 => T1 | _ => TL end.
Definition mkpr (a b : tok) : pr :=
  match a, b with
  | T0, T0 => P00 | T0, T1 => P01 | T0, TL => P0L | T1, T0 => P10 | T1, T1 => P11 | T1, TL => P1L
  | TL, T0 => PL0 | TL, T1 => PL1 | TL, TL => PLL
  end.
Inductive chunk := Ck (p0 p1 p2 : pr).
Definition ctoks (q : chunk) : list tok :=
  match q with Ck p0 p1 p2 => [pfst p0; psnd p0; pfst p1; psnd p1; pfst p2; psnd p2] end.
Definition cfirst (q : chunk) : tok := match q with Ck p0 _ _ => pfst p0 end.
Definition mkck (a0 a1 a2 a3 a4 a5 : tok) : chunk := Ck (mkpr a0 a1) (mkpr a2 a3) (mkpr a4 a5).
Definition cofl (l : list tok) : option chunk :=
  match l with [a0; a1; a2; a3; a4; a5] => Some (mkck a0 a1 a2 a3 a4 a5) | _ => None end.

(* np = number of L among the six outputs: e changes by 2 np - 6 *)
Inductive leaf := Leaf (o : chunk) (ph : bool) (c : N) (np : nat) | NoLeaf.
Definition cstep (ph : bool) (c : N) (q : chunk) (x : tok) : leaf :=
  match fsteps ph c (cfirst q) (tl (ctoks q) ++ [x]) with
  | Some (os, ph', c') => match cofl os with Some o => Leaf o ph' c' (nL os) | None => NoLeaf end
  | None => NoLeaf
  end.

(* the table: for c < 16 and both offsets, a trie over the three pairs and the next token *)
Inductive trie := TLf (l : leaf) | TN3 (t0 t1 tL : trie) | TN9 (t00 t01 t0L t10 t11 t1L tL0 tL1 tLL : trie).
Definition tb3 (f : list tok -> leaf) (pre : list tok) : trie :=
  TN3 (TLf (f (rev (T0 :: pre)))) (TLf (f (rev (T1 :: pre)))) (TLf (f (rev (TL :: pre)))).
Fixpoint tb9 (n : nat) (f : list tok -> leaf) (pre : list tok) : trie :=
  match n with
  | O => tb3 f pre
  | S n => TN9 (tb9 n f (T0 :: T0 :: pre)) (tb9 n f (T1 :: T0 :: pre)) (tb9 n f (TL :: T0 :: pre))
               (tb9 n f (T0 :: T1 :: pre)) (tb9 n f (T1 :: T1 :: pre)) (tb9 n f (TL :: T1 :: pre))
               (tb9 n f (T0 :: TL :: pre)) (tb9 n f (T1 :: TL :: pre)) (tb9 n f (TL :: TL :: pre))
  end.
Definition cleaf (ph : bool) (c : N) (l : list tok) : leaf :=
  match l with [a0; a1; a2; a3; a4; a5; x] => cstep ph c (mkck a0 a1 a2 a3 a4 a5) x | _ => NoLeaf end.
Definition ctries (c : N) : trie * trie := (tb9 3 (cleaf false c) [], tb9 3 (cleaf true c) []).
#[projections(primitive)] Record tab := Tab { g0 : trie * trie; g1 : trie * trie; g2 : trie * trie; g3 : trie * trie; g4 : trie * trie; g5 : trie * trie; g6 : trie * trie; g7 : trie * trie; g8 : trie * trie; g9 : trie * trie; g10 : trie * trie; g11 : trie * trie; g12 : trie * trie; g13 : trie * trie; g14 : trie * trie; g15 : trie * trie }.
Definition table : tab :=
  Tab (ctries 0) (ctries 1) (ctries 2) (ctries 3) (ctries 4) (ctries 5) (ctries 6) (ctries 7)
      (ctries 8) (ctries 9) (ctries 10) (ctries 11) (ctries 12) (ctries 13) (ctries 14) (ctries 15).
Definition sel (tb : tab) (c : N) : option (trie * trie) :=
  match c with
  | 0 => Some tb.(g0)
  | 1 => Some tb.(g1)
  | 2 => Some tb.(g2)
  | 3 => Some tb.(g3)
  | 4 => Some tb.(g4)
  | 5 => Some tb.(g5)
  | 6 => Some tb.(g6)
  | 7 => Some tb.(g7)
  | 8 => Some tb.(g8)
  | 9 => Some tb.(g9)
  | 10 => Some tb.(g10)
  | 11 => Some tb.(g11)
  | 12 => Some tb.(g12)
  | 13 => Some tb.(g13)
  | 14 => Some tb.(g14)
  | 15 => Some tb.(g15)
  | _ => None
  end.
Definition t9 (t : trie) (p : pr) : trie := match t with TN9 a b c d e f g h i => match p with P00 => a | P01 => b | P0L => c | P10 => d | P11 => e | P1L => f | PL0 => g | PL1 => h | PLL => i end | _ => TLf NoLeaf end.
Definition t3 (t : trie) (x : tok) : trie :=
  match t with TN3 a b c => match x with T0 => a | T1 => b | TL => c end | _ => TLf NoLeaf end.
Notation "t .{ p }" := (match t with TN9 a b c d e f g h i => match p with P00 => a | P01 => b | P0L => c | P10 => d | P11 => e | P1L => f | PL0 => g | PL1 => h | PLL => i end | _ => TLf NoLeaf end)
  (at level 2, left associativity, only parsing).
Notation "t .[ x ]" := (match t with TN3 a b c => match x with T0 => a | T1 => b | TL => c end | _ => TLf NoLeaf end)
  (at level 2, left associativity, only parsing).
Definition tlook (tr : trie) (q : chunk) (x : tok) : leaf :=
  match q with Ck p0 p1 p2 => match tr.{p0}.{p1}.{p2}.[x] with TLf l => l | _ => NoLeaf end end.
Definition cmax : N := 2 ^ 40.
Definition look (tb : tab) (ph : bool) (c : N) (q : chunk) (x : tok) : leaf :=
  match sel tb c with
  | Some (t0, t1) => tlook (if ph then t1 else t0) q x
  | None => if N.ltb c cmax then cstep ph c q x else NoLeaf
  end.
(* [look] as the VM runs it: no option boxes, the trie walk in place *)
Local Notation "'TLK' tp ph q x" := (match tp with (t0, t1) => let tr := (if ph then t1 else t0) in
  match q with Ck p0 p1 p2 => match tr.{p0}.{p1}.{p2}.[x] with TLf l => l | _ => NoLeaf end end end)
  (at level 10, tp at level 9, ph at level 9, q at level 9, x at level 9, only parsing).
Definition look2 (tb : tab) (ph : bool) (c : N) (q : chunk) (x : tok) : leaf :=
  match c with
  | 0 => TLK tb.(g0) ph q x
  | 1 => TLK tb.(g1) ph q x
  | 2 => TLK tb.(g2) ph q x
  | 3 => TLK tb.(g3) ph q x
  | 4 => TLK tb.(g4) ph q x
  | 5 => TLK tb.(g5) ph q x
  | 6 => TLK tb.(g6) ph q x
  | 7 => TLK tb.(g7) ph q x
  | 8 => TLK tb.(g8) ph q x
  | 9 => TLK tb.(g9) ph q x
  | 10 => TLK tb.(g10) ph q x
  | 11 => TLK tb.(g11) ph q x
  | 12 => TLK tb.(g12) ph q x
  | 13 => TLK tb.(g13) ph q x
  | 14 => TLK tb.(g14) ph q x
  | 15 => TLK tb.(g15) ph q x
  | _ => if N.ltb c cmax then cstep ph c q x else NoLeaf
  end.

(* e = 64 + b; a chunk with np L among its outputs takes b to b + 2 np - 6, which must stay >= 0 *)
Definition upd (np b : nat) : option nat :=
  match np with
  | 0%nat => match b with S (S (S (S (S (S b))))) => Some b | _ => None end
  | 1%nat => match b with S (S (S (S b))) => Some b | _ => None end
  | 2%nat => match b with S (S b) => Some b | _ => None end
  | 3%nat => Some b
  | 4%nat => Some (S (S b))
  | 5%nat => Some (S (S (S (S b))))
  | _ => Some (S (S (S (S (S (S b))))))
  end.

(* the word after a round: head tokens, chunks, then tail cells (older parses) *)
Inductive body := BNil (tl : list bool) | BCons (q : chunk) (b : body) | BStk | BBad.
Fixpoint btoks (b : body) : list tok := match b with BCons q b => ctoks q ++ btoks b | _ => [] end.
Fixpoint btail (b : body) : list bool := match b with BCons _ b => btail b | BNil tl => tl | _ => [] end.
Fixpoint bend (b : body) : body := match b with BCons _ b => bend b | _ => b end.
Definition proper (b : body) : bool := match bend b with BNil _ => true | _ => false end.

(* exact scan over cells; the caller pads w with four zeros *)
Inductive cres := CDone (outs : list tok) (lft : list bool) | CStk | CBad.
Fixpoint bitsP (p : positive) : list tok :=
  match p with xH => [T1] | xO p => T0 :: bitsP p | xI p => T1 :: bitsP p end.
Definition bits (n : N) : list tok := match n with N0 => [] | Npos p => bitsP p end.
Definition allzero (w : list bool) : bool := forallb negb w.
Fixpoint cscan (w : list bool) (n : N) (outs : list tok) : cres :=
  if N.eqb n 0 then CDone (rev outs) w else
  match w with
  | false :: ((b :: c :: ((d :: t) as t3)) as t1) =>
    if b || c then
      let n' := N.pred n in
      if N.eqb n' 0 then CDone (rev outs) (true :: t1) else
      if b then (if c then CBad else cscan t3 (N.div2 (N.succ n')) (dig (N.even n') :: outs))
      else (if d then CStk else cscan t (N.double n') (TL :: outs))
    else cscan t3 (N.div2 n) (dig (N.odd n) :: outs)
  | true :: ((b :: c :: ((d :: t) as t3)) as t1) =>
    if b then (if c then CBad else cscan t3 (N.div2 (N.succ n)) (dig (N.even n) :: outs))
    else if c then (if d then CStk else cscan t (N.double n) (TL :: outs))
    else cscan t3 (N.div2 (N.succ n)) (dig (N.even n) :: outs)
  | _ => if allzero w then CDone (rev_append outs (bits n)) [] else CBad
  end.
Definition zeros4 : list bool := [false; false; false; false].

(* exact scan over tokens, then over the tail cells *)
Fixpoint escan (ph : bool) (n : N) (t : tok) (ts : list tok) (tl : list bool) (outs : list tok) : cres :=
  match ts with
  | t' :: ts' =>
    let k := kindof ph t in
    match estep k n t' with
    | ECont o n' =>
      if N.eqb n' 0 then CDone (rev (o :: outs)) (skipn (off (nextph k t')) (tcells t') ++ tokcells ts' ++ tl)
      else escan (nextph k t') n' t' ts' tl (o :: outs)
    | EDie pre => CDone (rev outs) (pre ++ tcells t' ++ tokcells ts' ++ tl)
    | EBad => CBad
    end
  | [] => cscan (skipn (off ph) (tcells t) ++ tl ++ zeros4) n outs
  end.

Fixpoint regroup (outs : list tok) (lft : list bool) : body :=
  match outs with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: outs' => BCons (mkck a0 a1 a2 a3 a4 a5) (regroup outs' lft)
  | _ => BNil (tokcells outs ++ lft)
  end.
Definition cres_body (r : cres) : body :=
  match r with CDone outs lft => regroup outs lft | CStk => BStk | CBad => BBad end.

(* the exact count where the fast part stops: 2^(64 + b) - c *)
Definition ecount (b : nat) (c : N) : N := N.shiftl 1 (64 + N.of_nat b) - c.
Definition exact_from (ph : bool) (b : nat) (c : N) (q : chunk) (rest : body) : body :=
  if proper rest then cres_body (escan ph (ecount b c) (cfirst q) (tl (ctoks q) ++ btoks rest) (btail rest) [])
  else BBad.

(* fast scan over the chunks: offset ph and count 2^(64 + b) - c at the first token of q.
   ([upd] written in place: no option box per chunk) *)
Fixpoint fscan (tb : tab) (ph : bool) (c : N) (b : nat) (q : chunk) (rest : body) : body :=
  match rest with
  | BCons q2 rest2 =>
    match look2 tb ph c q (match q2 with Ck p _ _ => match p with P00 | P01 | P0L => T0 | P10 | P11 | P1L => T1 | _ => TL end end) with
    | Leaf o ph' c' np =>
      match np with
      | 0%nat => match b with S (S (S (S (S (S (b')))))) => BCons o (fscan tb ph' c' b' q2 rest2) | _ => exact_from ph b c q rest end
      | 1%nat => match b with S (S (S (S (b')))) => BCons o (fscan tb ph' c' b' q2 rest2) | _ => exact_from ph b c q rest end
      | 2%nat => match b with S (S (b')) => BCons o (fscan tb ph' c' b' q2 rest2) | _ => exact_from ph b c q rest end
      | 3%nat => BCons o (fscan tb ph' c' b q2 rest2)
      | 4%nat => BCons o (fscan tb ph' c' (S (S b)) q2 rest2)
      | 5%nat => BCons o (fscan tb ph' c' (S (S (S (S b)))) q2 rest2)
      | _ => BCons o (fscan tb ph' c' (S (S (S (S (S (S b)))))) q2 rest2)
      end
    | NoLeaf => BBad
    end
  | BNil _ => exact_from ph b c q rest
  | _ => BBad
  end.

(* a round: the count 2^j enters; odd rounds read a virtual L first *)
Inductive word := W (h : list tok) (b : body).

Definition split_out (nh : nat) (r : cres) : word :=
  match r with
  | CDone outs lft => W (firstn nh outs) (regroup (skipn nh outs) lft)
  | CStk => W [] BStk
  | CBad => W [] BBad
  end.

Definition hfix (w : word) : word :=
  match w with
  | W [a0; a1; a2; a3; a4; a5] b => W [] (BCons (mkck a0 a1 a2 a3 a4 a5) b)
  | _ => w
  end.

(* the whole round with the exact count (early rounds) *)
Definition eround (k : N) (ts : list tok) (b : body) : word :=
  match ts ++ btoks b with
  | [] => W [] BBad
  | t :: rest => if proper b then hfix (split_out (length ts) (escan false (N.shiftl 1 (N.div2 k)) t rest (btail b) []))
                 else W [] BBad
  end.

(* budget after the head: jn + 2 nL(houts) - length houts - 64 *)
Fixpoint subk (m b : nat) : option nat := match m with O => Some b | S m => match b with O => None | S b => subk m b end end.
Definition hbudget (jn : nat) (houts : list tok) : option nat :=
  subk (64 + length houts)%nat (nL houts + nL houts + jn)%nat.

(* jn = j = k / 2 as a nat, kept from round to round *)
Definition round (tb : tab) (k : N) (jn : nat) (w : word) : word :=
  match w with W h b =>
  let ts := if N.even k then h else TL :: h in
  if Nat.ltb jn 80 then eround k ts b else
  match ts, b with
  | [], BCons q b' => W [] (fscan tb false 0 (jn - 64)%nat q b')
  | t :: ts', BCons q b' =>
    if Nat.ltb 30 (length ts) then W [] BBad else
    match fsteps false 0 t (ts' ++ [cfirst q]) with
    | Some (houts, ph, c) =>
      match hbudget jn houts with
      | Some bud => hfix (W houts (fscan tb ph c bud q b'))
      | None => W [] BBad
      end
    | None => W [] BBad
    end
  | _, _ => eround k ts b
  end end.

(* odd rounds must give a word whose cells start with 1 0 *)
Definition headok (k : N) (w : word) : bool :=
  if N.even k then true else
  match w with
  | W (t :: _) _ => match t with T0 => false | _ => true end
  | W [] (BCons q _) => match cfirst q with T0 => false | _ => true end
  | _ => false
  end.
Definition wbody (w : word) : body := match w with W _ b => b end.

Fixpoint run (tb : tab) (n : nat) (k : N) (jn : nat) (w : word) : option (N * nat * word) :=
  match n with
  | O => Some (k, jn, w)
  | S n => let w' := round tb k jn w in
           if headok k w' then run tb n (N.succ k) (if N.even k then jn else S jn) w' else None
  end.

Definition check (n : nat) : bool :=
  let tb := table in
  match run tb n 1 0 (W [] (BNil [true])) with
  | Some (k, jn, w) => match bend (wbody (round tb k jn w)) with BStk => true | _ => false end
  | None => false
  end.

(* ======================= the proof ======================= *)

(* arithmetic helpers *)
Lemma div2_eq : forall a m, a = 2 * m \/ a = 2 * m + 1 -> N.div2 a = m.
Proof.
  intros a m [-> | ->].
  - rewrite <- N.double_spec. destruct m; reflexivity.
  - rewrite <- N.succ_double_spec. destruct m; reflexivity.
Qed.

Lemma odd_split : forall a, a = 2 * N.div2 a + N.b2n (N.odd a) /\ N.b2n (N.odd a) <= 1.
Proof. intros a. split; [apply N.div2_odd|destruct (N.odd a); simpl; lia]. Qed.

Lemma pow_succ_pred : forall e, 1 <= e -> 2 ^ e = 2 * 2 ^ N.pred e.
Proof. intros e H. rewrite <- N.pow_succ_r'. f_equal. lia. Qed.

Lemma pow_pos : forall e, 0 < 2 ^ e.
Proof. intros e. apply N.neq_0_lt_0. apply N.pow_nonzero. lia. Qed.

(* cells *)
Definition sym (b : bool) : Sym := if b then S1 else S0.
Fixpoint lw (w : list bool) (r : side) : side :=
  match w with [] => r | b :: w => sym b >> lw w r end.
Definition Zinf : side := const S0.
Lemma Zinf_unfold : Zinf = S0 >> Zinf.
Proof. apply const_unfold. Qed.

Lemma lw_app : forall a b r, lw (a ++ b) r = lw a (lw b r).
Proof. induction a as [|x a IH]; intros b r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma lw_zeros4 : forall w, lw (w ++ zeros4) Zinf = lw w Zinf.
Proof.
  intros w. rewrite lw_app. f_equal. unfold zeros4, Zinf. cbn [lw sym].
  repeat rewrite <- const_unfold. reflexivity.
Qed.

Lemma lw_allzero : forall w, allzero w = true -> lw w Zinf = Zinf.
Proof.
  induction w as [|x w IH]; intros H; [reflexivity|].
  cbn [allzero forallb negb] in H. destruct x; [discriminate|]. cbn [lw sym].
  rewrite IH by exact H. symmetry. apply Zinf_unfold.
Qed.

Lemma tokcells_app : forall a b, tokcells (a ++ b) = tokcells a ++ tokcells b.
Proof. induction a as [|t a IH]; intros b; [reflexivity|]. cbn [app tokcells]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma tcells_dig : forall b, tcells (dig b) = [b; false; false].
Proof. intros []; reflexivity. Qed.

Definition pc (ph : bool) (t : tok) (ts : list tok) (tl : list bool) : list bool :=
  skipn (off ph) (tcells t) ++ tokcells ts ++ tl.

Definition dE (o : tok) (e : N) : N := match o with TL => N.succ e | _ => N.pred e end.
Fixpoint eupd (os : list tok) (e : N) : N := match os with [] => e | o :: os => eupd os (dE o e) end.

(* the fast block is the exact block with the count 2^e - c *)
Lemma odd_sub : forall P c, c <= 2 * P -> N.odd (2 * P - c) = N.odd c.
Proof.
  intros P c H. destruct (odd_split (2 * P - c)) as [E1 B1]. destruct (odd_split c) as [E2 B2].
  destruct (N.odd (2 * P - c)), (N.odd c); cbn [N.b2n] in *; try reflexivity; lia.
Qed.

Lemma even_sub : forall P c, c <= 2 * P -> N.even (2 * P - c) = N.even c.
Proof. intros P c H. rewrite <- !N.negb_odd. f_equal. apply odd_sub. exact H. Qed.

Lemma div2_sub : forall P c, c + 1 <= 2 * P -> N.div2 (2 * P - c) = P - N.div2 (N.succ c).
Proof.
  intros P c H. destruct (odd_split c) as [E B]. apply div2_eq.
  destruct (N.odd c) eqn:Eo; cbn [N.b2n] in E.
  - assert (D : N.div2 (N.succ c) = N.div2 c + 1) by (apply div2_eq; left; lia). rewrite D. right. lia.
  - assert (D : N.div2 (N.succ c) = N.div2 c) by (apply div2_eq; right; lia). rewrite D. left. lia.
Qed.

Lemma div2_succ_sub : forall P c, c + 1 <= 2 * P -> N.div2 (N.succ (2 * P - c)) = P - N.div2 c.
Proof.
  intros P c H. destruct (odd_split c) as [E B]. apply div2_eq.
  destruct (N.odd c) eqn:Eo; cbn [N.b2n] in E; [left|right]; lia.
Qed.

Lemma dE_dig : forall b e, dE (dig b) e = N.pred e.
Proof. intros [] e; reflexivity. Qed.

Lemma fstep_estep : forall k c t' o c' e, fstep k c t' = Some (o, c') -> 1 <= e -> c + 2 <= 2 ^ e ->
  estep k (2 ^ e - c) t' = ECont o (2 ^ dE o e - c').
Proof.
  intros k c t' o c' e F He Hc.
  assert (P2 : 2 ^ e = 2 * 2 ^ N.pred e) by (apply pow_succ_pred; exact He).
  assert (P4 : 2 ^ N.succ e = 2 * (2 * 2 ^ N.pred e)) by (rewrite N.pow_succ_r', P2; reflexivity).
  set (P := 2 ^ N.pred e) in *. rewrite P2 in Hc |- *.
  assert (Ne : N.eqb (2 * P - c) 1 = false) by (apply N.eqb_neq; lia).
  assert (Zo : N.odd (2 * P - c) = N.odd c) by (apply odd_sub; lia).
  assert (Zd : N.div2 (2 * P - c) = P - N.div2 (N.succ c)) by (apply div2_sub; lia).
  assert (Ho : N.even (2 * P - c) = N.even c) by (apply even_sub; lia).
  assert (Hd : N.div2 (N.succ (2 * P - c)) = P - N.div2 c) by (apply div2_succ_sub; lia).
  assert (Ld : N.double (2 * P - c) = 2 * (2 * P) - N.double c) by (rewrite !N.double_spec; lia).
  assert (L'd : N.double (N.pred (2 * P - c)) = 2 * (2 * P) - N.double (N.succ c))
    by (rewrite !N.double_spec; lia).
  destruct k, t'; cbn [fstep estep] in F |- *; try discriminate F; injection F as <- <-;
    rewrite ?Ne; cbv beta iota; rewrite ?dE_dig; cbn [dE]; rewrite ?P4, ?Zo, ?Zd, ?Ho, ?Hd, ?Ld, ?L'd;
    reflexivity.
Qed.

Lemma fstep_cb : forall k c t' o c', fstep k c t' = Some (o, c') -> c' <= 2 * c + 2.
Proof.
  intros k c t' o c' F. destruct (odd_split c) as [E B]. destruct (odd_split (N.succ c)) as [E1 B1].
  destruct k, t'; cbn [fstep] in F; try discriminate F; injection F as <- <-;
    rewrite ?N.double_spec; lia.
Qed.

Lemma eupd_val : forall os e, N.of_nat (length os) <= e ->
  eupd os e + N.of_nat (length os) = e + 2 * N.of_nat (nL os).
Proof.
  unfold nL. induction os as [|o os IH]; intros e H; [cbn; lia|].
  cbn [eupd length filter] in *. rewrite Nat2N.inj_succ in *.
  destruct o; cbn [dE length] in *.
  - specialize (IH (N.pred e) ltac:(lia)). lia.
  - specialize (IH (N.pred e) ltac:(lia)). lia.
  - specialize (IH (N.succ e) ltac:(lia)). rewrite Nat2N.inj_succ. lia.
Qed.

Lemma nL_le : forall l, (nL l <= length l)%nat.
Proof. intros l. unfold nL. apply filter_length_le. Qed.

(* ---- the visit law and its counting lemmas ---- *)
Section Gen.
Variable tm : TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition Vis (s s' : side) : Prop :=
  forall x l, S0 >> x >> l {{C}}> s -->+ l {{A}}> x >> S0 >> s'.
Definition HV (s : side) : Prop :=
  forall x l, halts tm (S0 >> x >> l {{C}}> s).
Definition LE (s : side) : Q * tape := const S0 {{A}}> S1 >> S0 >> s.

Hypothesis vis_0 : forall r, Vis (S0 >> r) (S1 >> r).
Hypothesis vis_H : forall r r', Vis r r' -> Vis (S1 >> S0 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Hypothesis vis_G : forall r r', Vis r r' -> Vis (S1 >> S1 >> S0 >> r) (S0 >> S0 >> S0 >> r').
Hypothesis vis_L : forall r r1 r2, Vis r r1 -> Vis r1 r2 ->
  Vis (S1 >> S0 >> S1 >> S0 >> r) (S1 >> S0 >> S1 >> S0 >> r2).
Hypothesis hv_1011 : forall r, HV (S1 >> S0 >> S1 >> S1 >> r).
Hypothesis hv_H : forall r, HV r -> HV (S1 >> S0 >> S0 >> r).
Hypothesis hv_G : forall r, HV r -> HV (S1 >> S1 >> S0 >> r).
Hypothesis hv_L1 : forall r, HV r -> HV (S1 >> S0 >> S1 >> S0 >> r).
Hypothesis hv_L2 : forall r r1, Vis r r1 -> HV r1 -> HV (S1 >> S0 >> S1 >> S0 >> r).
Hypothesis round_step : forall s s', Vis (S1 >> S0 >> s) s' -> LE s -->+ LE s'.
Hypothesis round_halt : forall s, HV (S1 >> S0 >> s) -> halts tm (LE s).
Hypothesis blank_start : c0 -->+ LE (S1 >> const S0).

(* n visits in a row *)
Inductive VS : N -> side -> side -> Prop :=
  | VS_0 : forall s, VS 0 s s
  | VS_S : forall n s s1 s2, Vis s s1 -> VS n s1 s2 -> VS (N.succ n) s s2.

Lemma VS_1 : forall s s', Vis s s' -> VS 1 s s'.
Proof. intros s s' H. apply (VS_S 0 s s' s'); [exact H|apply VS_0]. Qed.

Lemma VS_add : forall a b s s1 s2, VS a s s1 -> VS b s1 s2 -> VS (a + b) s s2.
Proof.
  intros a b s s1 s2 H1. revert b s2. induction H1 as [s|n s s3 s1 HV' _ IH]; intros b s2 H2.
  - exact H2.
  - replace (N.succ n + b) with (N.succ (n + b)) by lia.
    eapply VS_S; [exact HV'|]. apply IH. exact H2.
Qed.

Lemma VS_inv : forall n s s', VS (N.succ n) s s' -> exists s1, Vis s s1 /\ VS n s1 s'.
Proof.
  intros n s s' H. inversion H as [s0 E1 E2 E3|n0 s0 s1 s2 HV' HR E1 E2 E3]; subst.
  - lia.
  - apply N.succ_inj in E1. subst. exists s1. split; assumption.
Qed.

Lemma VS_inv0 : forall s s', VS 0 s s' -> s = s'.
Proof.
  intros s s' H. inversion H as [s0 E1 E2|n0 s0 s1 s2 HV' HR E1 E2 E3]; subst.
  - reflexivity.
  - lia.
Qed.

Lemma VS_split : forall a b s s2, VS (a + b) s s2 -> exists s1, VS a s s1 /\ VS b s1 s2.
Proof.
  induction a as [|a IH] using N.peano_ind; intros b s s2 H.
  - exists s. split; [apply VS_0|exact H].
  - replace (N.succ a + b) with (N.succ (a + b)) in H by lia.
    destruct (VS_inv _ _ _ H) as [s1 [H1 H2]].
    destruct (IH _ _ _ H2) as [s3 [H3 H4]].
    exists s3. split; [eapply VS_S; eassumption|exact H4].
Qed.

Lemma VS1_vis : forall s s', VS 1 s s' -> Vis s s'.
Proof.
  intros s s' H. replace 1 with (N.succ 0) in H by reflexivity.
  destruct (VS_inv _ _ _ H) as [s1 [H1 H2]]. rewrite <- (VS_inv0 _ _ H2). exact H1.
Qed.

Notation Lt r := (S1 >> S0 >> S1 >> S0 >> r).
Notation Ht r := (S1 >> S0 >> S0 >> r).
Notation Zt r := (S0 >> S0 >> S0 >> r).
Notation Gt r := (S1 >> S1 >> S0 >> r).
Definition Dt (b : bool) (r : side) : side := sym b >> S0 >> S0 >> r.

Lemma VS_L : forall n r r', VS (2 * n) r r' -> VS n (Lt r) (Lt r').
Proof.
  induction n as [|n IH] using N.peano_ind; intros r r' H.
  - replace (2 * 0) with 0 in H by lia. rewrite (VS_inv0 _ _ H). apply VS_0.
  - replace (2 * N.succ n) with (N.succ (N.succ (2 * n))) in H by lia.
    destruct (VS_inv _ _ _ H) as [r1 [H1 H2]].
    destruct (VS_inv _ _ _ H2) as [r2 [H3 H4]].
    eapply VS_S; [eapply vis_L; eassumption | apply IH; exact H4].
Qed.

Lemma VS_ZZ : forall n r r', VS n r r' -> VS (2 * n) (Zt r) (Zt r').
Proof.
  intros n r r' H. induction H as [r|n r r1 r' HV' _ IH].
  - apply VS_0.
  - replace (2 * N.succ n) with (N.succ (N.succ (2 * n))) by lia.
    eapply VS_S; [apply vis_0|].
    eapply VS_S; [apply vis_H; exact HV'|exact IH].
Qed.

Lemma VS_HH : forall n r r', VS n r r' -> VS (2 * n) (Ht r) (Ht r').
Proof.
  intros n r r' H. induction H as [r|n r r1 r' HV' _ IH].
  - apply VS_0.
  - replace (2 * N.succ n) with (N.succ (N.succ (2 * n))) by lia.
    eapply VS_S; [apply vis_H; exact HV'|].
    eapply VS_S; [apply vis_0|exact IH].
Qed.

Lemma VS_ZH : forall n r r', VS n r r' -> VS (2 * n + 1) (Zt r) (Ht r').
Proof.
  intros n r r' H. eapply VS_add; [apply VS_ZZ; exact H|]. apply VS_1. apply vis_0.
Qed.

Lemma VS_HZ : forall n r r', VS (N.succ n) r r' -> VS (2 * n + 1) (Ht r) (Zt r').
Proof.
  intros n r r' H. destruct (VS_inv _ _ _ H) as [r1 [H1 H2]].
  replace (2 * n + 1) with (2 * n + 1 + 0) by lia.
  eapply VS_add; [|apply VS_0].
  replace (2 * n + 1) with (N.succ (2 * n)) by lia.
  eapply VS_S; [apply vis_H; exact H1|].
  (* now Zt r1 with 2n visits: Z, H alternate *)
  clear H H1. revert r1 r' H2. induction n as [|n IH] using N.peano_ind; intros r1 r' H2.
  - rewrite (VS_inv0 _ _ H2). apply VS_0.
  - destruct (VS_inv _ _ _ H2) as [r3 [H3 H4]].
    replace (2 * N.succ n) with (N.succ (N.succ (2 * n))) by lia.
    eapply VS_S; [apply vis_0|].
    eapply VS_S; [apply vis_H; exact H3|]. apply IH. exact H4.
Qed.

Lemma law_Z : forall n r r', VS (N.div2 n) r r' -> VS n (Zt r) (Dt (N.odd n) r').
Proof.
  intros n r r' H. destruct (odd_split n) as [E B].
  destruct (N.odd n); cbn [N.b2n] in E; unfold Dt, sym.
  - rewrite E. apply VS_ZH. exact H.
  - rewrite E, N.add_0_r. apply VS_ZZ. exact H.
Qed.

Lemma law_H : forall n r r', VS (N.div2 (n + 1)) r r' -> VS n (Ht r) (Dt (negb (N.odd n)) r').
Proof.
  intros n r r' H. destruct (odd_split n) as [E B].
  destruct (N.odd n) eqn:Eo; cbn [N.b2n negb] in *; unfold Dt, sym.
  - assert (D : N.div2 (n + 1) = N.succ (N.div2 n)) by (apply div2_eq; left; lia).
    rewrite D in H. rewrite E. apply VS_HZ. exact H.
  - assert (D : N.div2 (n + 1) = N.div2 n) by (apply div2_eq; right; lia).
    rewrite D in H. rewrite E, N.add_0_r. apply VS_HH. exact H.
Qed.

Lemma law_G : forall n r r', 1 <= n -> VS (N.div2 (n + 1)) r r' -> VS n (Gt r) (Dt (negb (N.odd n)) r').
Proof.
  intros n r r' Hn H. destruct (odd_split n) as [E B].
  assert (D : N.div2 (n + 1) = N.succ (N.div2 (n - 1))).
  { apply div2_eq. destruct (odd_split (n - 1)) as [E1 B1].
    destruct (N.odd n), (N.odd (n - 1)); cbn [N.b2n] in *; lia. }
  rewrite D in H. destruct (VS_inv _ _ _ H) as [r1 [H1 H2]].
  replace n with (N.succ (n - 1)) at 1 by lia.
  eapply VS_S; [apply vis_G; exact H1|].
  assert (O : negb (N.odd n) = N.odd (n - 1)).
  { destruct (odd_split (n - 1)) as [E1 B1].
    destruct (N.odd n), (N.odd (n - 1)); cbn [N.b2n negb] in *; try reflexivity; lia. }
  rewrite O. apply law_Z. exact H2.
Qed.

Lemma law_0 : forall n s s', 1 <= n -> VS (n - 1) (S1 >> s) s' -> VS n (S0 >> s) s'.
Proof.
  intros n s s' Hn H. replace n with (N.succ (n - 1)) by lia.
  eapply VS_S; [apply vis_0|exact H].
Qed.

(* one of n visits in a row halts *)
Definition HVS (n : N) (s : side) : Prop := exists m s1, m < n /\ VS m s s1 /\ HV s1.

Lemma hvs_Z : forall n r, HVS (N.div2 n) r -> HVS n (Zt r).
Proof.
  intros n r [m [r1 [Hm [H1 H2]]]]. destruct (odd_split n) as [E B].
  exists (2 * m + 1), (Ht r1). split; [lia|]. split; [apply VS_ZH; exact H1|apply hv_H; exact H2].
Qed.

Lemma hvs_H : forall n r, HVS (N.div2 (n + 1)) r -> HVS n (Ht r).
Proof.
  intros n r [m [r1 [Hm [H1 H2]]]]. destruct (odd_split (n + 1)) as [E B].
  exists (2 * m), (Ht r1). split; [lia|]. split; [apply VS_HH; exact H1|apply hv_H; exact H2].
Qed.

Lemma hvs_G : forall n r, 1 <= n -> HVS (N.div2 (n + 1)) r -> HVS n (Gt r).
Proof.
  intros n r Hn [m [r1 [Hm [H1 H2]]]].
  destruct (N.eq_dec m 0) as [->|Hm0].
  - rewrite (VS_inv0 _ _ H1) in *. exists 0, (Gt r1). split; [lia|]. split; [apply VS_0|apply hv_G; exact H2].
  - replace m with (N.succ (m - 1)) in H1 by lia.
    destruct (VS_inv _ _ _ H1) as [ra [Ha Hb]].
    assert (Hz : HVS (N.div2 (n - 1)) ra).
    { exists (m - 1), r1. split; [|split; assumption].
      destruct (odd_split (n + 1)) as [E1 B1]. destruct (odd_split (n - 1)) as [E2 B2].
      destruct (N.odd (n + 1)), (N.odd (n - 1)); cbn [N.b2n] in *; lia. }
    destruct (hvs_Z _ _ Hz) as [m2 [s2 [Hm2 [H3 H4]]]].
    exists (N.succ m2), s2. split; [lia|]. split; [eapply VS_S; [apply vis_G; exact Ha|exact H3]|exact H4].
Qed.

Lemma hvs_L : forall n r, HVS (2 * n) r -> HVS n (Lt r).
Proof.
  intros n r [m [r1 [Hm [H1 H2]]]]. destruct (odd_split m) as [E B].
  destruct (N.odd m); cbn [N.b2n] in E.
  - rewrite E in H1. destruct (VS_split _ _ _ _ H1) as [ra [Ha Hb]].
    exists (N.div2 m), (Lt ra). split; [lia|]. split; [apply VS_L; exact Ha|].
    apply (hv_L2 ra r1); [apply VS1_vis; exact Hb|exact H2].
  - rewrite E, N.add_0_r in H1.
    exists (N.div2 m), (Lt r1). split; [lia|]. split; [apply VS_L; exact H1|apply hv_L1; exact H2].
Qed.

Lemma hvs_0 : forall n s, 1 <= n -> HVS (n - 1) (S1 >> s) -> HVS n (S0 >> s).
Proof.
  intros n s Hn [m [s1 [Hm [H1 H2]]]].
  exists (N.succ m), s1. split; [lia|]. split; [eapply VS_S; [apply vis_0|exact H1]|exact H2].
Qed.

Lemma hvs_1011 : forall n r, 1 <= n -> HVS n (S1 >> S0 >> S1 >> S1 >> r).
Proof. intros n r Hn. exists 0, (S1 >> S0 >> S1 >> S1 >> r). split; [lia|]. split; [apply VS_0|apply hv_1011]. Qed.


(* ---- one block over tokens ---- *)
Lemma lZ : forall n r r', VS (N.div2 n) r r' -> VS n (S0 >> S0 >> S0 >> r) (lw (tcells (dig (N.odd n))) r').
Proof. intros n r r' H. rewrite tcells_dig. exact (law_Z _ _ _ H). Qed.

Lemma lG' : forall n r r', 2 <= n -> VS (N.div2 n) r r' -> VS n (S0 >> S1 >> S0 >> r) (lw (tcells (dig (N.odd n))) r').
Proof.
  intros n r r' Hn H. rewrite tcells_dig. apply law_0; [lia|].
  assert (E1 : N.div2 (n - 1 + 1) = N.div2 n) by (f_equal; lia).
  assert (E2 : negb (N.odd (n - 1)) = N.odd n).
  { destruct (odd_split n) as [A _]. destruct (odd_split (n - 1)) as [B _].
    destruct (N.odd n), (N.odd (n - 1)); cbn [N.b2n negb] in *; try reflexivity; lia. }
  rewrite <- E2. apply law_G; [lia|]. rewrite E1. exact H.
Qed.

Lemma lL' : forall n r r', 2 <= n -> VS (N.double (N.pred n)) r r' -> VS n (S0 >> S0 >> S1 >> S0 >> r) (lw (tcells TL) r').
Proof.
  intros n r r' Hn H. apply law_0; [lia|]. apply VS_L. rewrite N.double_spec, N.pred_sub in H. exact H.
Qed.

Lemma lH : forall n r r', VS (N.div2 (N.succ n)) r r' -> VS n (S1 >> S0 >> S0 >> r) (lw (tcells (dig (N.even n))) r').
Proof. intros n r r' H. rewrite tcells_dig, <- N.negb_odd. apply law_H. rewrite N.add_1_r. exact H. Qed.

Lemma lL : forall n r r', VS (N.double n) r r' -> VS n (S1 >> S0 >> S1 >> S0 >> r) (lw (tcells TL) r').
Proof. intros n r r' H. apply VS_L. rewrite N.double_spec in H. exact H. Qed.

Lemma hZ : forall n r, HVS (N.div2 n) r -> HVS n (S0 >> S0 >> S0 >> r).
Proof. intros n r H. exact (hvs_Z _ _ H). Qed.

Lemma hG' : forall n r, 2 <= n -> HVS (N.div2 n) r -> HVS n (S0 >> S1 >> S0 >> r).
Proof.
  intros n r Hn H. apply hvs_0; [lia|]. apply hvs_G; [lia|].
  assert (E1 : N.div2 (n - 1 + 1) = N.div2 n) by (f_equal; lia). rewrite E1. exact H.
Qed.

Lemma hL' : forall n r, 2 <= n -> HVS (N.double (N.pred n)) r -> HVS n (S0 >> S0 >> S1 >> S0 >> r).
Proof. intros n r Hn H. apply hvs_0; [lia|]. apply hvs_L. rewrite N.double_spec, N.pred_sub in H. exact H. Qed.

Lemma hH : forall n r, HVS (N.div2 (N.succ n)) r -> HVS n (S1 >> S0 >> S0 >> r).
Proof. intros n r H. apply hvs_H. rewrite N.add_1_r. exact H. Qed.

Lemma hL : forall n r, HVS (N.double n) r -> HVS n (S1 >> S0 >> S1 >> S0 >> r).
Proof. intros n r H. apply hvs_L. rewrite N.double_spec in H. exact H. Qed.

Ltac blk_simpl E H :=
  repeat match type of E with
  | context [N.eqb ?n 1] => let E1 := fresh "E1" in
      destruct (N.eqb n 1) eqn:E1; [try discriminate E|apply N.eqb_neq in E1]
  end.

Lemma estep_vs : forall ph t t' n o n' R w',
  estep (kindof ph t) n t' = ECont o n' -> 1 <= n ->
  VS n' (lw (skipn (off (nextph (kindof ph t) t')) (tcells t') ++ R) Zinf) (lw w' Zinf) ->
  VS n (lw (skipn (off ph) (tcells t) ++ tcells t' ++ R) Zinf) (lw (tcells o ++ w') Zinf).
Proof.
  intros ph t t' n o n' R w' E Hn H. rewrite (lw_app (tcells o)).
  destruct ph, t, t'; cbn [kindof nextph estep off] in E, H; try discriminate E; blk_simpl E H;
    injection E as <- <-; cbn [skipn tcells app lw sym] in H |- *.
  all: first [ exact (lZ _ _ _ H) | exact (lH _ _ _ H) | exact (lL _ _ _ H)
             | apply lG'; [lia|exact H] | apply lL'; [lia|exact H] ].
Qed.

Lemma estep_hvs : forall ph t t' n o n' R,
  estep (kindof ph t) n t' = ECont o n' -> 1 <= n ->
  HVS n' (lw (skipn (off (nextph (kindof ph t) t')) (tcells t') ++ R) Zinf) ->
  HVS n (lw (skipn (off ph) (tcells t) ++ tcells t' ++ R) Zinf).
Proof.
  intros ph t t' n o n' R E Hn H.
  destruct ph, t, t'; cbn [kindof nextph estep off] in E, H; try discriminate E; blk_simpl E H;
    injection E as <- <-; cbn [skipn tcells app lw sym] in H |- *.
  all: first [ exact (hZ _ _ H) | exact (hH _ _ H) | exact (hL _ _ H)
             | apply hG'; [lia|exact H] | apply hL'; [lia|exact H] ].
Qed.

Lemma estep_die : forall ph t t' n pre R,
  estep (kindof ph t) n t' = EDie pre ->
  VS n (lw (skipn (off ph) (tcells t) ++ tcells t' ++ R) Zinf) (lw (pre ++ tcells t' ++ R) Zinf).
Proof.
  intros ph t t' n pre R E.
  destruct ph, t, t'; cbn [kindof nextph estep off] in E; try discriminate E;
    destruct (N.eqb n 1) eqn:E1; try discriminate E; apply N.eqb_eq in E1; subst n;
    injection E as <-; cbn [skipn tcells app lw sym]; apply VS_1; apply vis_0.
Qed.

(* ---- the fast blocks ---- *)
Lemma dE_ge : forall o e, e - 1 <= dE o e /\ dE o e <= e + 1.
Proof. intros [] e; cbn [dE]; lia. Qed.

Lemma fsteps_step : forall ph c t t1 ts os ph' c',
  fsteps ph c t (t1 :: ts) = Some (os, ph', c') ->
  exists o c1 os', fstep (kindof ph t) c t1 = Some (o, c1) /\ os = o :: os' /\
    fsteps (nextph (kindof ph t) t1) c1 t1 ts = Some (os', ph', c').
Proof.
  intros ph c t t1 ts os ph' c' F. cbn [fsteps] in F.
  destruct (fstep (kindof ph t) c t1) as [[o c1]|]; [|discriminate F].
  destruct (fsteps (nextph (kindof ph t) t1) c1 t1 ts) as [[[os' ph''] c'']|] eqn:F2; [|discriminate F].
  injection F as <- <- <-. exists o, c1, os'. auto.
Qed.

Lemma exp_step : forall e r c c1 o, N.of_nat (2 * r) + 3 <= e -> c + 2 <= 2 ^ (e - (N.of_nat (2 * r) + 2)) ->
  c1 <= 2 * c + 2 -> N.of_nat (2 * r) + 1 <= dE o e /\ c1 + 2 <= 2 ^ (dE o e - N.of_nat (2 * r)).
Proof.
  intros e r c c1 o He Hc Hc1. destruct (dE_ge o e) as [D1 D2]. split; [lia|].
  set (m := e - (N.of_nat (2 * r) + 2)) in *.
  assert (Hm : 2 ^ N.succ m = 2 * 2 ^ m) by apply N.pow_succ_r'.
  eapply N.le_trans; [|apply (N.pow_le_mono_r 2 (N.succ m)); lia]. lia.
Qed.

Lemma fsteps_vs : forall ts x ph c t os ph' c' e R w',
  fsteps ph c t (ts ++ [x]) = Some (os, ph', c') ->
  N.of_nat (2 * length (ts ++ [x])) + 1 <= e ->
  c + 2 <= 2 ^ (e - N.of_nat (2 * length (ts ++ [x]))) ->
  VS (2 ^ eupd os e - c') (lw (skipn (off ph') (tcells x) ++ R) Zinf) (lw w' Zinf) ->
  VS (2 ^ e - c) (lw (skipn (off ph) (tcells t) ++ tokcells (ts ++ [x]) ++ R) Zinf) (lw (tokcells os ++ w') Zinf).
Proof.
  induction ts as [|t1 ts IH]; intros x ph c t os ph' c' e R w' F He Hc H.
  - cbn [app] in F. destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    cbn [fsteps] in F2. injection F2 as <- <- <-.
    change (tokcells ([] ++ [x])) with (tcells x ++ []). change (tokcells [o]) with (tcells o ++ []).
    cbn [eupd] in H. rewrite !app_nil_r.
    assert (He1 : 1 <= e) by (cbn in He; lia).
    assert (Hc1 : c + 2 <= 2 ^ e) by (eapply N.le_trans; [exact Hc|]; apply N.pow_le_mono_r; lia).
    apply (estep_vs _ _ _ _ _ (2 ^ dE o e - c1)); [apply fstep_estep with (1 := F1); assumption|lia|exact H].
  - cbn [app] in F. destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    set (r := length (ts ++ [x])) in *.
    assert (Lr : length ((t1 :: ts) ++ [x]) = S r) by reflexivity. rewrite Lr in He, Hc.
    replace (N.of_nat (2 * S r)) with (N.of_nat (2 * r) + 2) in He, Hc by lia.
    assert (He1 : 1 <= e) by lia.
    assert (Hc1 : c + 2 <= 2 ^ e) by (eapply N.le_trans; [exact Hc|]; apply N.pow_le_mono_r; lia).
    destruct (exp_step e r c c1 o ltac:(lia) Hc (fstep_cb _ _ _ _ _ F1)) as [E1 E2].
    specialize (IH x _ _ _ _ _ _ (dE o e) R w' F2 E1 E2 H).
    cbn [tokcells app]. rewrite <- !app_assoc.
    apply (estep_vs _ _ _ _ _ (2 ^ dE o e - c1)); [apply fstep_estep with (1 := F1); assumption|lia|exact IH].
Qed.

Lemma fsteps_hvs : forall ts x ph c t os ph' c' e R,
  fsteps ph c t (ts ++ [x]) = Some (os, ph', c') ->
  N.of_nat (2 * length (ts ++ [x])) + 1 <= e ->
  c + 2 <= 2 ^ (e - N.of_nat (2 * length (ts ++ [x]))) ->
  HVS (2 ^ eupd os e - c') (lw (skipn (off ph') (tcells x) ++ R) Zinf) ->
  HVS (2 ^ e - c) (lw (skipn (off ph) (tcells t) ++ tokcells (ts ++ [x]) ++ R) Zinf).
Proof.
  induction ts as [|t1 ts IH]; intros x ph c t os ph' c' e R F He Hc H.
  - cbn [app] in F. destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    cbn [fsteps] in F2. injection F2 as <- <- <-.
    change (tokcells ([] ++ [x])) with (tcells x ++ []).
    cbn [eupd] in H. rewrite !app_nil_r.
    assert (He1 : 1 <= e) by (cbn in He; lia).
    assert (Hc1 : c + 2 <= 2 ^ e) by (eapply N.le_trans; [exact Hc|]; apply N.pow_le_mono_r; lia).
    apply (estep_hvs _ _ _ _ o (2 ^ dE o e - c1)); [apply fstep_estep with (1 := F1); assumption|lia|exact H].
  - cbn [app] in F. destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    set (r := length (ts ++ [x])) in *.
    assert (Lr : length ((t1 :: ts) ++ [x]) = S r) by reflexivity. rewrite Lr in He, Hc.
    replace (N.of_nat (2 * S r)) with (N.of_nat (2 * r) + 2) in He, Hc by lia.
    assert (He1 : 1 <= e) by lia.
    assert (Hc1 : c + 2 <= 2 ^ e) by (eapply N.le_trans; [exact Hc|]; apply N.pow_le_mono_r; lia).
    destruct (exp_step e r c c1 o ltac:(lia) Hc (fstep_cb _ _ _ _ _ F1)) as [E1 E2].
    specialize (IH x _ _ _ _ _ _ (dE o e) R F2 E1 E2 H).
    cbn [tokcells app]. rewrite <- !app_assoc.
    apply (estep_hvs _ _ _ _ o (2 ^ dE o e - c1)); [apply fstep_estep with (1 := F1); assumption|lia|exact IH].
Qed.

Lemma fsteps_cb : forall ts ph c t os ph' c', fsteps ph c t ts = Some (os, ph', c') ->
  c' + 2 <= 2 ^ N.of_nat (length ts) * (c + 2).
Proof.
  induction ts as [|t1 ts IH]; intros ph c t os ph' c' F.
  - cbn [fsteps] in F. injection F as <- <- <-. cbn [length N.of_nat]. rewrite N.pow_0_r. lia.
  - destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    specialize (IH _ _ _ _ _ _ F2). pose proof (fstep_cb _ _ _ _ _ F1) as B.
    cbn [length]. rewrite Nat2N.inj_succ, N.pow_succ_r'. nia.
Qed.

Lemma fsteps_len : forall ts ph c t os ph' c', fsteps ph c t ts = Some (os, ph', c') -> length os = length ts.
Proof.
  induction ts as [|t1 ts IH]; intros ph c t os ph' c' F.
  - cbn [fsteps] in F. injection F as <- <- <-. reflexivity.
  - destruct (fsteps_step _ _ _ _ _ _ _ _ F) as [o [c1 [os' [F1 [-> F2]]]]].
    cbn [length]. f_equal. exact (IH _ _ _ _ _ _ F2).
Qed.

(* ---- chunks, trie and table ---- *)
Lemma pfst_mkpr : forall a b, pfst (mkpr a b) = a.
Proof. intros [] []; reflexivity. Qed.
Lemma psnd_mkpr : forall a b, psnd (mkpr a b) = b.
Proof. intros [] []; reflexivity. Qed.
Lemma mkpr_eta : forall p, mkpr (pfst p) (psnd p) = p.
Proof. intros []; reflexivity. Qed.
Lemma ctoks_mkck : forall a0 a1 a2 a3 a4 a5, ctoks (mkck a0 a1 a2 a3 a4 a5) = [a0; a1; a2; a3; a4; a5].
Proof. intros. unfold mkck, ctoks. rewrite !pfst_mkpr, !psnd_mkpr. reflexivity. Qed.

Lemma cofl_ok : forall l o, cofl l = Some o -> ctoks o = l.
Proof.
  intros l o H. do 6 (destruct l as [|? l]; [discriminate H|]).
  destruct l; [|discriminate H]. injection H as <-. apply ctoks_mkck.
Qed.

Lemma t9_tb9 : forall n f pre p, t9 (tb9 (S n) f pre) p = tb9 n f (psnd p :: pfst p :: pre).
Proof. intros n f pre []; reflexivity. Qed.
Lemma t3_tb3 : forall f pre x, t3 (tb3 f pre) x = TLf (f (rev (x :: pre))).
Proof. intros f pre []; reflexivity. Qed.

Lemma tlook_tb : forall f q x, tlook (tb9 3 f []) q x = f (ctoks q ++ [x]).
Proof.
  intros f [p0 p1 p2] x.
  change (tlook (tb9 3 f []) (Ck p0 p1 p2) x) with
    (match t3 (t9 (t9 (t9 (tb9 3 f []) p0) p1) p2) x with TLf l => l | _ => NoLeaf end).
  rewrite !t9_tb9, t3_tb3. reflexivity.
Qed.

Lemma cleaf_ok : forall ph c q x, cleaf ph c (ctoks q ++ [x]) = cstep ph c q x.
Proof. intros ph c [p0 p1 p2] x. unfold cleaf, mkck. cbn [ctoks app]. rewrite !mkpr_eta. reflexivity. Qed.

Lemma sel_table : forall c p, sel table c = Some p -> p = ctries c /\ c < 16.
Proof.
  intros c p H. cbv beta iota delta [sel] in H.
  destruct c as [|p0]; cbv beta iota in H.
  { injection H as <-. split; [reflexivity|lia]. }
  destruct p0 as [p0|p0|]; cbv beta iota in H.
  all: try (destruct p0 as [p0|p0|]; cbv beta iota in H).
  all: try (destruct p0 as [p0|p0|]; cbv beta iota in H).
  all: try (destruct p0 as [p0|p0|]; cbv beta iota in H).
  all: first [discriminate H | injection H as <-; split; [reflexivity|lia]].
Qed.

Lemma cmax16 : 16 < cmax.
Proof. vm_compute. reflexivity. Qed.

Lemma look_ok : forall ph c q x o ph' c' np, look table ph c q x = Leaf o ph' c' np ->
  c < cmax /\ cstep ph c q x = Leaf o ph' c' np.
Proof.
  intros ph c q x o ph' c' np H. unfold look in H.
  destruct (sel table c) as [[t0 t1]|] eqn:E.
  - apply sel_table in E as [E1 E2].
    assert (A0 : t0 = tb9 3 (cleaf false c) []) by (change t0 with (fst (t0, t1)); rewrite E1; reflexivity).
    assert (A1 : t1 = tb9 3 (cleaf true c) []) by (change t1 with (snd (t0, t1)); rewrite E1; reflexivity).
    subst t0 t1. split; [pose proof cmax16; lia|]. rewrite <- H.
    destruct ph; rewrite tlook_tb, cleaf_ok; reflexivity.
  - destruct (N.ltb c cmax) eqn:E2; [|discriminate H]. apply N.ltb_lt in E2. auto.
Qed.

Lemma look2_ok : forall tb ph c q x, look2 tb ph c q x = look tb ph c q x.
Proof.
  intros tb ph c q x. unfold look2, look, sel, tlook.
  destruct c as [|p0]; [reflexivity|].
  destruct p0 as [p0|p0|]; [| |reflexivity].
  all: destruct p0 as [p0|p0|]; [| |reflexivity].
  all: destruct p0 as [p0|p0|]; [| |reflexivity].
  all: destruct p0 as [p0|p0|]; [| |reflexivity].
  all: reflexivity.
Qed.

Lemma fscan_unfold : forall tb ph c b q q2 rest2, fscan tb ph c b q (BCons q2 rest2) =
  match look2 tb ph c q (cfirst q2) with
  | Leaf o ph' c' np =>
    match upd np b with
    | Some b' => BCons o (fscan tb ph' c' b' q2 rest2)
    | None => exact_from ph b c q (BCons q2 rest2)
    end
  | NoLeaf => BBad
  end.
Proof.
  intros tb ph c b q [p0 p1 p2] rest2. cbn [fscan cfirst]. unfold pfst.
  destruct (look2 _ _ _ _ _) as [o ph' c' np|]; [|reflexivity].
  destruct np as [|[|[|[|[|[|np]]]]]]; cbn [upd]; try reflexivity;
    destruct b as [|[|[|[|[|[|b]]]]]]; reflexivity.
Qed.
Lemma upd_spec : forall np b b', (np <= 6)%nat -> upd np b = Some b' -> N.of_nat b' + 6 = N.of_nat b + 2 * N.of_nat np.
Proof.
  intros np b b' Hn H.
  destruct np as [|[|[|[|[|[|[|np]]]]]]]; cbn [upd] in H; try lia;
    repeat (destruct b as [|b]; cbv beta iota in H; [discriminate H|]);
    injection H as <-; lia.
Qed.

Lemma upd_ok : forall os b b', length os = 6%nat -> upd (nL os) b = Some b' ->
  eupd os (64 + N.of_nat b) = 64 + N.of_nat b'.
Proof.
  intros os b b' L U. pose proof (eupd_val os (64 + N.of_nat b)) as E. rewrite L in E.
  specialize (E ltac:(lia)). pose proof (nL_le os) as B. rewrite L in B.
  pose proof (upd_spec _ _ _ B U) as S. lia.
Qed.

Lemma ecount_pow : forall b c, ecount b c = 2 ^ (64 + N.of_nat b) - c.
Proof. intros b c. unfold ecount. rewrite N.shiftl_1_l. reflexivity. Qed.

Lemma chunk_vs : forall ph c q x o ph' c' np b b' R w',
  cstep ph c q x = Leaf o ph' c' np -> c < cmax -> upd np b = Some b' ->
  VS (ecount b' c') (lw (skipn (off ph') (tcells x) ++ R) Zinf) (lw w' Zinf) ->
  VS (ecount b c) (lw (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q)) ++ tcells x ++ R) Zinf)
     (lw (tokcells (ctoks o) ++ w') Zinf).
Proof.
  intros ph c q x o ph' c' np b b' R w' H Hc U V. unfold cstep in H.
  destruct (fsteps ph c (cfirst q) (tl (ctoks q) ++ [x])) as [[[os ph1] c1]|] eqn:F; [|discriminate H].
  destruct (cofl os) as [o1|] eqn:Co; [|discriminate H]. injection H as <- <- <- <-.
  apply cofl_ok in Co. rewrite Co. rewrite !ecount_pow in *.
  assert (Lq : length (tl (ctoks q) ++ [x]) = 6%nat) by (destruct q; reflexivity).
  assert (Lo : length os = 6%nat) by (rewrite (fsteps_len _ _ _ _ _ _ _ F); exact Lq).
  rewrite <- (upd_ok os b b' Lo U) in V.
  replace (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q)) ++ tcells x ++ R)
    with (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q) ++ [x]) ++ R)
    by (rewrite tokcells_app; cbn [tokcells]; rewrite app_nil_r, <- app_assoc; reflexivity).
  apply (fsteps_vs _ _ _ _ _ _ _ _ _ _ _ F); [rewrite Lq; lia| |exact V].
  rewrite Lq. unfold cmax in Hc. eapply N.le_trans; [|apply (N.pow_le_mono_r 2 48); lia].
  assert (P : 2 ^ 40 + 2 <= 2 ^ 48) by (vm_compute; discriminate). lia.
Qed.

Lemma chunk_hvs : forall ph c q x o ph' c' np b b' R,
  cstep ph c q x = Leaf o ph' c' np -> c < cmax -> upd np b = Some b' ->
  HVS (ecount b' c') (lw (skipn (off ph') (tcells x) ++ R) Zinf) ->
  HVS (ecount b c) (lw (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q)) ++ tcells x ++ R) Zinf).
Proof.
  intros ph c q x o ph' c' np b b' R H Hc U V. unfold cstep in H.
  destruct (fsteps ph c (cfirst q) (tl (ctoks q) ++ [x])) as [[[os ph1] c1]|] eqn:F; [|discriminate H].
  destruct (cofl os) as [o1|] eqn:Co; [|discriminate H]. injection H as <- <- <- <-.
  apply cofl_ok in Co. rewrite !ecount_pow in *.
  assert (Lq : length (tl (ctoks q) ++ [x]) = 6%nat) by (destruct q; reflexivity).
  assert (Lo : length os = 6%nat) by (rewrite (fsteps_len _ _ _ _ _ _ _ F); exact Lq).
  rewrite <- (upd_ok os b b' Lo U) in V.
  replace (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q)) ++ tcells x ++ R)
    with (skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q) ++ [x]) ++ R)
    by (rewrite tokcells_app; cbn [tokcells]; rewrite app_nil_r, <- app_assoc; reflexivity).
  apply (fsteps_hvs _ _ _ _ _ _ _ _ _ _ F); [rewrite Lq; lia| |exact V].
  rewrite Lq. unfold cmax in Hc. eapply N.le_trans; [|apply (N.pow_le_mono_r 2 48); lia].
  assert (P : 2 ^ 40 + 2 <= 2 ^ 48) by (vm_compute; discriminate). lia.
Qed.

Lemma chunk_cb : forall ph c q x o ph' c' np, cstep ph c q x = Leaf o ph' c' np -> c < cmax -> c' < 2 ^ 50.
Proof.
  intros ph c q x o ph' c' np H Hc. unfold cstep in H.
  destruct (fsteps ph c (cfirst q) (tl (ctoks q) ++ [x])) as [[[os ph1] c1]|] eqn:F; [|discriminate H].
  destruct (cofl os); [|discriminate H]. injection H as <- <- <- <-.
  pose proof (fsteps_cb _ _ _ _ _ _ _ F) as B.
  assert (Lq : length (tl (ctoks q) ++ [x]) = 6%nat) by (destruct q; reflexivity). rewrite Lq in B.
  unfold cmax in Hc. assert (P : 2 ^ N.of_nat 6 * (2 ^ 40 + 2) < 2 ^ 50) by (vm_compute; reflexivity). nia.
Qed.

(* ---- the exact end: cells ---- *)
Lemma bits_vs : forall n, VS n Zinf (lw (tokcells (bits n)) Zinf).
Proof.
  assert (Z3 : Zinf = S0 >> S0 >> S0 >> Zinf) by (rewrite <- !Zinf_unfold; reflexivity).
  intros [|p]; [apply VS_0|]. cbn [bits].
  induction p as [p IH|p IH|]; cbn [bitsP tokcells]; rewrite lw_app; cbn [tcells lw sym].
  - pattern Zinf at 1. rewrite Z3. change (Npos p~1) with (Npos p~1).
    pose proof (law_Z (Npos p~1) Zinf _ IH) as L. exact L.
  - pattern Zinf at 1. rewrite Z3. exact (law_Z (Npos p~0) Zinf _ IH).
  - pattern Zinf at 1. rewrite Z3. exact (law_Z 1 Zinf Zinf (VS_0 _)).
Qed.

Lemma cscan_unfold : forall w n outs, cscan w n outs =
  if N.eqb n 0 then CDone (rev outs) w else
  match w with
  | false :: ((b :: c :: ((d :: t) as t3)) as t1) =>
    if b || c then
      let n' := N.pred n in
      if N.eqb n' 0 then CDone (rev outs) (true :: t1) else
      if b then (if c then CBad else cscan t3 (N.div2 (N.succ n')) (dig (N.even n') :: outs))
      else (if d then CStk else cscan t (N.double n') (TL :: outs))
    else cscan t3 (N.div2 n) (dig (N.odd n) :: outs)
  | true :: ((b :: c :: ((d :: t) as t3)) as t1) =>
    if b then (if c then CBad else cscan t3 (N.div2 (N.succ n)) (dig (N.even n) :: outs))
    else if c then (if d then CStk else cscan t (N.double n) (TL :: outs))
    else cscan t3 (N.div2 (N.succ n)) (dig (N.even n) :: outs)
  | _ => if allzero w then CDone (rev_append outs (bits n)) [] else CBad
  end.
Proof. intros w n outs. destruct w; reflexivity. Qed.

Lemma lG : forall n r r', 1 <= n -> VS (N.div2 (N.succ n)) r r' -> VS n (S1 >> S1 >> S0 >> r) (lw (tcells (dig (N.even n))) r').
Proof. intros n r r' Hn H. rewrite tcells_dig, <- N.negb_odd. apply law_G; [exact Hn|]. rewrite N.add_1_r. exact H. Qed.

Lemma hG : forall n r, 1 <= n -> HVS (N.div2 (N.succ n)) r -> HVS n (S1 >> S1 >> S0 >> r).
Proof. intros n r Hn H. apply hvs_G; [exact Hn|]. rewrite N.add_1_r. exact H. Qed.

Lemma pred_facts : forall n, 2 <= n -> N.even (N.pred n) = N.odd n /\ N.div2 (N.succ (N.pred n)) = N.div2 n.
Proof.
  intros n Hn. rewrite N.succ_pred by lia. split; [|reflexivity].
  rewrite <- (N.succ_pred n) at 2 by lia. rewrite N.odd_succ. reflexivity.
Qed.

Definition CInv (n0 : N) (w0 : list bool) (n : N) (w : list bool) (outs : list tok) : Prop :=
  forall w', VS n (lw w Zinf) (lw w' Zinf) -> VS n0 (lw w0 Zinf) (lw (tokcells (rev outs) ++ w') Zinf).

Lemma cinv_step : forall n0 w0 n w outs n' w1 o,
  CInv n0 w0 n w outs ->
  (forall w', VS n' (lw w1 Zinf) (lw w' Zinf) -> VS n (lw w Zinf) (lw (tcells o) (lw w' Zinf))) ->
  CInv n0 w0 n' w1 (o :: outs).
Proof.
  intros n0 w0 n w outs n' w1 o HI HL w' H. cbn [rev]. rewrite tokcells_app, <- app_assoc.
  apply HI. cbn [tokcells]. rewrite app_nil_r, lw_app. apply HL. exact H.
Qed.

Lemma cscan_done : forall len w n outs outs' lft n0 w0, (length w <= len)%nat ->
  CInv n0 w0 n w outs -> cscan w n outs = CDone outs' lft -> VS n0 (lw w0 Zinf) (lw (tokcells outs' ++ lft) Zinf).
Proof.
  induction len as [|len IH]; intros w n outs outs' lft n0 w0 Hl HI Hs; rewrite cscan_unfold in Hs;
    destruct (N.eqb n 0) eqn:Ez.
  1, 3: injection Hs as <- <-; apply HI; apply N.eqb_eq in Ez; subst n; apply VS_0.
  - destruct w; [|cbn [length] in Hl; lia]. cbn in Hs. injection Hs as <- <-.
    rewrite rev_append_rev, tokcells_app, app_nil_r. apply HI. apply bits_vs.
  - apply N.eqb_neq in Ez.
    destruct w as [|a [|b [|c [|d t]]]].
    1-4: repeat match goal with x : bool |- _ => destruct x end;
         cbv beta iota delta [allzero forallb negb andb] in Hs;
         first [discriminate Hs | injection Hs as <- <-; rewrite rev_append_rev, tokcells_app, app_nil_r;
                apply HI; rewrite lw_allzero by reflexivity; apply bits_vs].
    cbn [length] in Hl.
    destruct a, b, c; cbn [orb] in Hs.
    + discriminate Hs.
    + eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [cbn [length]; lia|].
      intros w' H. cbn [lw sym]. apply lG; [lia|exact H].
    + destruct d; [discriminate Hs|].
      eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [lia|].
      intros w' H. cbn [lw sym]. apply lL. exact H.
    + eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [cbn [length]; lia|].
      intros w' H. cbn [lw sym]. apply lH. exact H.
    + destruct (N.eqb (N.pred n) 0) eqn:Ep; [|discriminate Hs].
      injection Hs as <- <-. apply HI. apply N.eqb_eq in Ep. replace n with 1 by lia.
      apply VS_1. apply vis_0.
    + destruct (N.eqb (N.pred n) 0) eqn:Ep.
      * injection Hs as <- <-. apply HI. apply N.eqb_eq in Ep. replace n with 1 by lia.
        apply VS_1. apply vis_0.
      * apply N.eqb_neq in Ep. destruct (pred_facts n ltac:(lia)) as [P1 P2]. rewrite P1, P2 in Hs.
        eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [cbn [length]; lia|].
        intros w' H. cbn [lw sym]. apply lG'; [lia|exact H].
    + destruct (N.eqb (N.pred n) 0) eqn:Ep.
      * injection Hs as <- <-. apply HI. apply N.eqb_eq in Ep. replace n with 1 by lia.
        apply VS_1. apply vis_0.
      * destruct d; [discriminate Hs|]. apply N.eqb_neq in Ep.
        eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [lia|].
        intros w' H. cbn [lw sym]. apply lL'; [lia|exact H].
    + eapply IH; [|eapply cinv_step; [exact HI|]|exact Hs]; [cbn [length]; lia|].
      intros w' H. cbn [lw sym]. apply lZ. exact H.
Qed.

Lemma cscan_stk : forall len w n outs n0 w0, (length w <= len)%nat ->
  (HVS n (lw w Zinf) -> HVS n0 (lw w0 Zinf)) -> cscan w n outs = CStk -> HVS n0 (lw w0 Zinf).
Proof.
  induction len as [|len IH]; intros w n outs n0 w0 Hl HI Hs; rewrite cscan_unfold in Hs;
    destruct (N.eqb n 0) eqn:Ez; try discriminate Hs.
  - destruct w; [|cbn [length] in Hl; lia]. cbn in Hs. discriminate Hs.
  - apply N.eqb_neq in Ez.
    destruct w as [|a [|b [|c [|d t]]]].
    1-4: repeat match goal with x : bool |- _ => destruct x end;
         cbv beta iota delta [allzero forallb negb andb] in Hs; discriminate Hs.
    cbn [length] in Hl.
    destruct a, b, c; cbn [orb] in Hs.
    + discriminate Hs.
    + refine (IH _ _ _ _ _ _ _ Hs); [cbn [length]; lia|intros H; apply HI; cbn [lw sym]; apply hG; [lia|exact H]].
    + destruct d.
      * apply HI. apply hvs_1011. lia.
      * refine (IH _ _ _ _ _ _ _ Hs); [lia|intros H; apply HI; cbn [lw sym]; apply hL; exact H].
    + refine (IH _ _ _ _ _ _ _ Hs); [cbn [length]; lia|intros H; apply HI; cbn [lw sym]; apply hH; exact H].
    + destruct (N.eqb (N.pred n) 0); discriminate Hs.
    + destruct (N.eqb (N.pred n) 0) eqn:Ep; [discriminate Hs|]. apply N.eqb_neq in Ep.
      destruct (pred_facts n ltac:(lia)) as [P1 P2]. rewrite P2 in Hs.
      refine (IH _ _ _ _ _ _ _ Hs); [cbn [length]; lia|intros H; apply HI; cbn [lw sym]; apply hG'; [lia|exact H]].
    + destruct (N.eqb (N.pred n) 0) eqn:Ep; [discriminate Hs|]. apply N.eqb_neq in Ep.
      destruct d.
      * apply HI. cbn [lw sym]. apply hvs_0; [lia|]. apply hvs_1011. lia.
      * refine (IH _ _ _ _ _ _ _ Hs); [lia|intros H; apply HI; cbn [lw sym]; apply hL'; [lia|exact H]].
    + refine (IH _ _ _ _ _ _ _ Hs); [cbn [length]; lia|intros H; apply HI; cbn [lw sym]; apply hZ; exact H].
Qed.

(* ---- the exact end: tokens ---- *)
Lemma escan_done : forall ts ph n t tl outs outs' lft n0 w0,
  CInv n0 w0 n (pc ph t ts tl) outs -> 1 <= n ->
  escan ph n t ts tl outs = CDone outs' lft -> VS n0 (lw w0 Zinf) (lw (tokcells outs' ++ lft) Zinf).
Proof.
  induction ts as [|t' ts IH]; intros ph n t tl outs outs' lft n0 w0 HI Hn Hs; cbn [escan] in Hs.
  - refine (cscan_done (length (skipn (off ph) (tcells t) ++ tl ++ zeros4)) _ _ _ _ _ _ _ (le_n _) _ Hs).
    intros w' H. apply HI. unfold pc. cbn [tokcells app].
    rewrite <- (lw_zeros4 (skipn (off ph) (tcells t) ++ tl)), <- app_assoc. exact H.
  - destruct (estep (kindof ph t) n t') as [o n'|pre|] eqn:E; [| |discriminate Hs].
    + destruct (N.eqb n' 0) eqn:Ez.
      * injection Hs as <- <-. apply N.eqb_eq in Ez. subst n'.
        cbn [rev]. rewrite tokcells_app, <- app_assoc. apply HI. unfold pc. cbn [tokcells].
        rewrite app_nil_r, <- app_assoc. apply (estep_vs _ _ _ _ _ 0 _ _ E Hn). apply VS_0.
      * apply N.eqb_neq in Ez. refine (IH _ _ _ _ _ _ _ _ _ _ _ Hs); [|lia].
        eapply cinv_step; [exact HI|]. intros w' H. unfold pc in *. rewrite <- lw_app.
        cbn [tokcells]. rewrite <- app_assoc. apply (estep_vs _ _ _ _ _ n' _ _ E Hn). exact H.
    + injection Hs as <- <-. apply HI. unfold pc. cbn [tokcells]. rewrite <- app_assoc.
      apply (estep_die _ _ _ _ _ _ E).
Qed.

Lemma escan_stk : forall ts ph n t tl outs n0 w0,
  (HVS n (lw (pc ph t ts tl) Zinf) -> HVS n0 (lw w0 Zinf)) -> 1 <= n ->
  escan ph n t ts tl outs = CStk -> HVS n0 (lw w0 Zinf).
Proof.
  induction ts as [|t' ts IH]; intros ph n t tl outs n0 w0 HI Hn Hs; cbn [escan] in Hs.
  - refine (cscan_stk (length (skipn (off ph) (tcells t) ++ tl ++ zeros4)) _ _ _ _ _ (le_n _) _ Hs).
    intros H. apply HI. unfold pc. cbn [tokcells app].
    rewrite <- (lw_zeros4 (skipn (off ph) (tcells t) ++ tl)), <- app_assoc. exact H.
  - destruct (estep (kindof ph t) n t') as [o n'|pre|] eqn:E; [| discriminate Hs | discriminate Hs].
    destruct (N.eqb n' 0) eqn:Ez; [discriminate Hs|]. apply N.eqb_neq in Ez.
    refine (IH _ _ _ _ _ _ _ _ _ Hs); [|lia]. intros H. apply HI. unfold pc in *. cbn [tokcells].
    rewrite <- app_assoc. apply (estep_hvs _ _ _ _ _ n' _ E Hn). exact H.
Qed.

Lemma regroup_ok : forall m outs lft, (length outs <= m)%nat ->
  tokcells (btoks (regroup outs lft)) ++ btail (regroup outs lft) = tokcells outs ++ lft /\
  proper (regroup outs lft) = true.
Proof.
  induction m as [|m IH]; intros outs lft Hl.
  - destruct outs; [|cbn in Hl; lia]. split; reflexivity.
  - destruct outs as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 outs']]]]]];
      try (split; reflexivity).
    destruct (IH outs' lft ltac:(cbn in Hl; lia)) as [E P]. cbn [regroup btoks btail proper bend].
    split; [|exact P].
    replace (tokcells (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: outs'))
      with (tokcells [a0; a1; a2; a3; a4; a5] ++ tokcells outs') by (rewrite <- tokcells_app; reflexivity).
    rewrite ctoks_mkck, tokcells_app, <- app_assoc, E, app_assoc. reflexivity.
Qed.

Definition fcells (ph : bool) (q : chunk) (rest : body) : list bool := pc ph (cfirst q) (tl (ctoks q) ++ btoks rest) (btail rest).
Definition bcells (b : body) : list bool := tokcells (btoks b) ++ btail b.

Lemma proper_bend : forall b, proper b = true -> bend b <> BStk.
Proof. intros b P E. unfold proper in P. rewrite E in P. discriminate P. Qed.

Lemma ecount_pos : forall b c, c < 2 ^ 50 -> 1 <= ecount b c.
Proof.
  intros b c Hc. rewrite ecount_pow.
  assert (P : 2 ^ 50 <= 2 ^ (64 + N.of_nat b)) by (apply N.pow_le_mono_r; lia). lia.
Qed.

Lemma exact_sound : forall ph b c q rest, c < 2 ^ 50 ->
  (proper (exact_from ph b c q rest) = true ->
     VS (ecount b c) (lw (fcells ph q rest) Zinf) (lw (bcells (exact_from ph b c q rest)) Zinf)) /\
  (bend (exact_from ph b c q rest) = BStk -> HVS (ecount b c) (lw (fcells ph q rest) Zinf)).
Proof.
  intros ph b c q rest Hc. pose proof (ecount_pos b c Hc) as Hn. unfold exact_from.
  destruct (proper rest) eqn:Pr; [|split; intros H; discriminate H].
  destruct (escan ph (ecount b c) (cfirst q) (tl (ctoks q) ++ btoks rest) (btail rest) []) as [outs lft| |] eqn:E;
    cbn [cres_body].
  - destruct (regroup_ok (length outs) outs lft (le_n _)) as [R1 R2]. split.
    + intros _. unfold bcells. rewrite R1.
      assert (CI : CInv (ecount b c) (fcells ph q rest) (ecount b c)
                     (pc ph (cfirst q) (tl (ctoks q) ++ btoks rest) (btail rest)) []) by (intros w' H; exact H).
      exact (escan_done _ _ _ _ _ _ _ _ _ _ CI Hn E).
    + intros H. exfalso. exact (proper_bend _ R2 H).
  - split; [intros H; discriminate H|]. intros _.
    assert (CI : HVS (ecount b c) (lw (pc ph (cfirst q) (tl (ctoks q) ++ btoks rest) (btail rest)) Zinf) ->
                 HVS (ecount b c) (lw (fcells ph q rest) Zinf)) by (intros H; exact H).
    exact (escan_stk _ _ _ _ _ _ _ _ CI Hn E).
  - split; intros H; discriminate H.
Qed.

Lemma tokcells_ctoks : forall q, tokcells (ctoks q) = tcells (cfirst q) ++ tokcells (tl (ctoks q)).
Proof. intros []. reflexivity. Qed.

Lemma fscan_sound : forall rest ph c b q, c < 2 ^ 50 ->
  (proper (fscan table ph c b q rest) = true ->
     VS (ecount b c) (lw (fcells ph q rest) Zinf) (lw (bcells (fscan table ph c b q rest)) Zinf)) /\
  (bend (fscan table ph c b q rest) = BStk -> HVS (ecount b c) (lw (fcells ph q rest) Zinf)).
Proof.
  induction rest as [tl0|q2 rest2 IH| |]; intros ph c b q Hc; [cbn [fscan]| |cbn [fscan]|cbn [fscan]].
  - apply exact_sound; exact Hc.
  - rewrite fscan_unfold, look2_ok.
    destruct (look table ph c q (cfirst q2)) as [o ph' c' np|] eqn:L; [|split; intros H; discriminate H].
    destruct (look_ok _ _ _ _ _ _ _ _ L) as [Lc L'].
    destruct (upd np b) as [b'|] eqn:U; [|apply exact_sound; exact Hc].
    destruct (IH ph' c' b' q2 (chunk_cb _ _ _ _ _ _ _ _ L' Lc)) as [IH1 IH2].
    assert (Ec : fcells ph q (BCons q2 rest2) = skipn (off ph) (tcells (cfirst q)) ++ tokcells (tl (ctoks q)) ++
              tcells (cfirst q2) ++ (tokcells (tl (ctoks q2)) ++ tokcells (btoks rest2) ++ btail rest2)).
    { unfold fcells, pc. cbn [btoks btail]. rewrite !tokcells_app, tokcells_ctoks, !app_assoc. reflexivity. }
    assert (Ec2 : fcells ph' q2 rest2 = skipn (off ph') (tcells (cfirst q2)) ++
              (tokcells (tl (ctoks q2)) ++ tokcells (btoks rest2) ++ btail rest2)).
    { unfold fcells, pc. rewrite tokcells_app, !app_assoc. reflexivity. }
    split.
    + intros P. specialize (IH1 P). rewrite Ec2 in IH1. rewrite Ec.
      unfold bcells in *. cbn [btoks btail]. rewrite tokcells_app, <- app_assoc.
      exact (chunk_vs _ _ _ _ _ _ _ _ _ _ _ _ L' Lc U IH1).
    + intros S. specialize (IH2 S). rewrite Ec2 in IH2. rewrite Ec.
      exact (chunk_hvs _ _ _ _ _ _ _ _ _ _ _ L' Lc U IH2).
  - split; intros H; discriminate H.
  - split; intros H; discriminate H.
Qed.

Lemma fscan_improper : forall rest ph c b q, proper rest = false -> bend (fscan table ph c b q rest) = BBad.
Proof.
  induction rest as [tl0|q2 rest2 IH| |]; intros ph c b q P; [cbn [fscan]| |cbn [fscan]|cbn [fscan]].
  - discriminate P.
  - rewrite fscan_unfold, look2_ok.
    destruct (look table ph c q (cfirst q2)) as [o ph' c' np|]; [|reflexivity].
    destruct (upd np b) as [b'|].
    + cbn [bend]. apply IH. exact P.
    + unfold exact_from. rewrite P. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* the head run of 1010 *)
Fixpoint Lp (j : nat) (r : side) : side := match j with O => r | S j => Lt (Lp j r) end.

Lemma VS_Lp : forall j n r r', VS (2 ^ N.of_nat j * n) r r' -> VS n (Lp j r) (Lp j r').
Proof.
  induction j as [|j IH]; intros n r r' H.
  - cbn [Lp N.of_nat] in *. rewrite N.pow_0_r, N.mul_1_l in H. exact H.
  - cbn [Lp]. apply VS_L. apply IH. rewrite Nat2N.inj_succ, N.pow_succ_r' in H.
    replace (2 ^ N.of_nat j * (2 * n)) with (2 * 2 ^ N.of_nat j * n) by lia. exact H.
Qed.

Lemma hvs_Lp : forall j n r, HVS (2 ^ N.of_nat j * n) r -> HVS n (Lp j r).
Proof.
  induction j as [|j IH]; intros n r H.
  - cbn [Lp N.of_nat] in *. rewrite N.pow_0_r, N.mul_1_l in H. exact H.
  - cbn [Lp]. apply hvs_L. apply IH. rewrite Nat2N.inj_succ, N.pow_succ_r' in H.
    replace (2 ^ N.of_nat j * (2 * n)) with (2 * 2 ^ N.of_nat j * n) by lia. exact H.
Qed.

Fixpoint strm (k : nat) (V : list bool) : side :=
  match k with O => lw V Zinf | S k => S1 >> S0 >> strm k V end.

Lemma strm_even : forall j V, strm (2 * j) V = Lp j (lw V Zinf).
Proof.
  induction j as [|j IH]; intros V; [reflexivity|].
  replace (2 * S j)%nat with (S (S (2 * j))) by lia. cbn [strm Lp]. rewrite IH. reflexivity.
Qed.

Lemma strm_odd : forall j V, strm (2 * j + 1) V = Lp j (lw (true :: false :: V) Zinf).
Proof.
  induction j as [|j IH]; intros V; [reflexivity|].
  replace (2 * S j + 1)%nat with (S (S (2 * j + 1))) by lia. cbn [strm Lp]. rewrite IH. reflexivity.
Qed.

Definition config (k : nat) (V : list bool) : Q * tape := LE (strm (Nat.pred k) V).

Lemma parity : forall k : nat, exists j, (k = 2 * j \/ k = 2 * j + 1)%nat.
Proof.
  induction k as [|k [j [E|E]]].
  - exists 0%nat. left. reflexivity.
  - exists j. right. lia.
  - exists (S j). left. lia.
Qed.

Lemma half_N : forall j : nat, N.div2 (N.of_nat (2 * j)) = N.of_nat j /\ N.div2 (N.of_nat (2 * j + 1)) = N.of_nat j.
Proof. intros j. split; apply div2_eq; [left|right]; lia. Qed.

Lemma even_N : forall j : nat, N.even (N.of_nat (2 * j)) = true /\ N.even (N.of_nat (2 * j + 1)) = false.
Proof.
  intros j. rewrite Nat2N.inj_add, Nat2N.inj_mul. cbn [N.of_nat Pos.of_succ_nat].
  split; [apply N.even_mul|]. rewrite N.even_add, N.even_mul. reflexivity.
Qed.

(* ---- rounds ---- *)
Definition wcells (w : word) : list bool := match w with W h b => tokcells (h ++ btoks b) ++ btail b end.
Definition scan (k : N) (w : word) : list bool := if N.even k then skipn 2 (wcells w) else true :: false :: wcells w.

Lemma scan_eq : forall k h b t rest, (if N.even k then h else TL :: h) ++ btoks b = t :: rest ->
  scan k (W h b) = pc false t rest (btail b).
Proof.
  intros k h b t rest E. unfold scan, wcells, pc. destruct (N.even k).
  - rewrite E. cbn [tokcells off]. rewrite <- app_assoc. destruct t; reflexivity.
  - cbn [app] in E. injection E as <- <-. reflexivity.
Qed.

Lemma hfix_ok : forall w, (wcells (hfix w) = wcells w /\ wbody (hfix w) = wbody w) \/
  (exists q, wcells (hfix w) = wcells w /\ wbody (hfix w) = BCons q (wbody w)).
Proof.
  intros [h b]. unfold hfix.
  destruct h as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 h]]]]]]]; try (left; split; reflexivity).
  right. eexists. split; [|reflexivity]. cbn [wcells app btoks btail]. rewrite ctoks_mkck. reflexivity.
Qed.

Lemma hfix_cells : forall w, wcells (hfix w) = wcells w.
Proof. intros w. destruct (hfix_ok w) as [[E _]|[q [E _]]]; exact E. Qed.
Lemma hfix_proper : forall w, proper (wbody (hfix w)) = proper (wbody w).
Proof. intros w. destruct (hfix_ok w) as [[_ E]|[q [_ E]]]; rewrite E; reflexivity. Qed.
Lemma hfix_bend : forall w, bend (wbody (hfix w)) = bend (wbody w).
Proof. intros w. destruct (hfix_ok w) as [[_ E]|[q [_ E]]]; rewrite E; reflexivity. Qed.

Lemma split_out_ok : forall nh outs lft,
  wcells (split_out nh (CDone outs lft)) = tokcells outs ++ lft /\ proper (wbody (split_out nh (CDone outs lft))) = true.
Proof.
  intros nh outs lft. cbn [split_out wcells wbody].
  destruct (regroup_ok (length (skipn nh outs)) (skipn nh outs) lft (le_n _)) as [R1 R2]. split; [|exact R2].
  rewrite tokcells_app, <- app_assoc, R1, app_assoc, <- tokcells_app, firstn_skipn. reflexivity.
Qed.

Lemma subk_spec : forall m b b', subk m b = Some b' -> b = (m + b')%nat.
Proof.
  induction m as [|m IH]; intros b b' H; cbn [subk] in H; [injection H as <-; reflexivity|].
  destruct b as [|b]; [discriminate H|]. rewrite (IH _ _ H). reflexivity.
Qed.

Lemma hbudget_ok : forall jn houts bud, (length houts <= jn)%nat -> hbudget jn houts = Some bud ->
  eupd houts (N.of_nat jn) = 64 + N.of_nat bud.
Proof.
  intros jn houts bud L H. unfold hbudget in H. apply subk_spec in H.
  pose proof (eupd_val houts (N.of_nat jn) ltac:(lia)) as E. lia.
Qed.

Lemma eround_ok : forall k h b ts, ts = (if N.even k then h else TL :: h) ->
  (proper (wbody (eround k ts b)) = true ->
     VS (2 ^ N.div2 k) (lw (scan k (W h b)) Zinf) (lw (wcells (eround k ts b)) Zinf)) /\
  (bend (wbody (eround k ts b)) = BStk -> HVS (2 ^ N.div2 k) (lw (scan k (W h b)) Zinf)).
Proof.
  intros k h b ts Ets. unfold eround.
  destruct (ts ++ btoks b) as [|t rest] eqn:E; [split; intros H; discriminate H|].
  destruct (proper b) eqn:Pb; [|split; intros H; discriminate H].
  rewrite Ets in E. rewrite (scan_eq k h b t rest E). rewrite N.shiftl_1_l.
  assert (Hn : 1 <= 2 ^ N.div2 k) by (pose proof (pow_pos (N.div2 k)); lia).
  destruct (escan false (2 ^ N.div2 k) t rest (btail b) []) as [outs lft| |] eqn:Es.
  - rewrite hfix_proper, hfix_bend, hfix_cells.
    destruct (split_out_ok (length ts) outs lft) as [S1 S2]. split.
    + intros _. rewrite S1. refine (escan_done _ _ _ _ _ _ _ _ _ _ _ Hn Es). intros w' H; exact H.
    + intros Hb. exfalso. exact (proper_bend _ S2 Hb).
  - cbn [split_out hfix wbody bend proper]. split; [intros H; discriminate H|].
    intros _. refine (escan_stk _ _ _ _ _ _ _ _ _ Hn Es). intros H; exact H.
  - cbn [split_out hfix wbody bend proper]. split; intros H; discriminate H.
Qed.

Lemma round_improper : forall k jn w, proper (wbody w) = false -> bend (wbody (round table k jn w)) = BBad.
Proof.
  intros k jn [h b] P. cbn [wbody] in P. unfold round. cbv zeta.
  assert (Ee : forall ts, bend (wbody (eround k ts b)) = BBad).
  { intros ts. unfold eround. destruct (ts ++ btoks b); [reflexivity|]. rewrite P. reflexivity. }
  destruct (Nat.ltb jn 80); [apply Ee|].
  destruct (if N.even k then h else TL :: h) as [|t ts']; destruct b as [tl0|q b'| |]; try apply Ee.
  - cbn [wbody]. apply fscan_improper. exact P.
  - destruct (Nat.ltb 30 (length (t :: ts'))); [reflexivity|].
    destruct (fsteps false 0 t (ts' ++ [cfirst q])) as [[[houts ph] c]|]; [|reflexivity].
    destruct (hbudget jn houts); [|reflexivity].
    rewrite hfix_bend. cbn [wbody]. apply fscan_improper. exact P.
Qed.

Lemma round_sound : forall k jn w, jn = N.to_nat (N.div2 k) ->
  (proper (wbody (round table k jn w)) = true ->
     VS (2 ^ N.div2 k) (lw (scan k w) Zinf) (lw (wcells (round table k jn w)) Zinf)) /\
  (bend (wbody (round table k jn w)) = BStk -> HVS (2 ^ N.div2 k) (lw (scan k w) Zinf)).
Proof.
  intros k jn [h b] Hj. unfold round. cbv zeta.
  destruct (Nat.ltb jn 80) eqn:Hl; [apply eround_ok; reflexivity|]. apply Nat.ltb_ge in Hl.
  assert (Hjn : 2 ^ N.div2 k = 2 ^ N.of_nat jn) by (rewrite Hj, N2Nat.id; reflexivity).
  destruct (if N.even k then h else TL :: h) as [|t ts'] eqn:Ets.
  - destruct b as [tl0|q b'| |]; try (apply eround_ok; rewrite Ets; reflexivity).
    assert (Ek : N.even k = true) by (destruct (N.even k); [reflexivity|discriminate Ets]).
    rewrite Ek in Ets. subst h.
    assert (Sc : scan k (W [] (BCons q b')) = fcells false q b').
    { unfold scan, wcells, fcells, pc. rewrite Ek. cbn [app btoks btail].
      rewrite !tokcells_app, tokcells_ctoks, <- !app_assoc. destruct (cfirst q); reflexivity. }
    assert (Ec : ecount (jn - 64) 0 = 2 ^ N.div2 k) by (rewrite ecount_pow, Hjn, N.sub_0_r; f_equal; lia).
    destruct (fscan_sound b' false 0 (jn - 64) q ltac:(pose proof (pow_pos 50); lia)) as [F1 F2].
    rewrite Ec in F1, F2. cbn [wbody]. rewrite Sc. split; [exact F1|exact F2].
  - destruct b as [tl0|q b'| |]; try (apply eround_ok; rewrite Ets; reflexivity).
    destruct (Nat.ltb 30 (length (t :: ts'))) eqn:L30; [split; intros H; discriminate H|].
    apply Nat.ltb_ge in L30.
    destruct (fsteps false 0 t (ts' ++ [cfirst q])) as [[[houts ph] c]|] eqn:F; [|split; intros H; discriminate H].
    pose proof (fsteps_len _ _ _ _ _ _ _ F) as Lh. rewrite length_app in Lh. cbn [length] in Lh, L30.
    destruct (hbudget jn houts) as [bud|] eqn:Hb; [|split; intros H; discriminate H].
    pose proof (hbudget_ok jn houts bud ltac:(lia) Hb) as Eb.
    pose proof (fsteps_cb _ _ _ _ _ _ _ F) as Bc. rewrite length_app in Bc. cbn [length] in Bc.
    assert (Hc : c < 2 ^ 50).
    { assert (P : 2 ^ N.of_nat (length ts' + 1) <= 2 ^ 31) by (apply N.pow_le_mono_r; lia).
      assert (P2 : 2 ^ 31 * 2 < 2 ^ 50) by (vm_compute; reflexivity). nia. }
    destruct (fscan_sound b' ph c bud q Hc) as [F1 F2].
    assert (Sc : scan k (W h (BCons q b')) = skipn (off false) (tcells t) ++ tokcells (ts' ++ [cfirst q]) ++
               (tokcells (tl (ctoks q)) ++ tokcells (btoks b') ++ btail b')).
    { assert (E2 : (if N.even k then h else TL :: h) ++ btoks (BCons q b') = t :: (ts' ++ btoks (BCons q b')))
        by (rewrite Ets; reflexivity).
      rewrite (scan_eq _ _ _ _ _ E2). unfold pc. cbn [btoks btail].
      rewrite !tokcells_app, tokcells_ctoks. cbn [tokcells]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
    assert (Fc : forall ph', fcells ph' q b' = skipn (off ph') (tcells (cfirst q)) ++
               (tokcells (tl (ctoks q)) ++ tokcells (btoks b') ++ btail b')).
    { intros ph'. unfold fcells, pc. rewrite tokcells_app, <- !app_assoc. reflexivity. }
    rewrite hfix_proper, hfix_bend, hfix_cells. cbn [wbody wcells]. rewrite Sc.
    assert (Eh : 2 ^ N.div2 k = 2 ^ N.of_nat jn - 0) by (rewrite Hjn; lia).
    assert (B1 : N.of_nat (2 * length (ts' ++ [cfirst q])) + 1 <= N.of_nat jn)
      by (rewrite length_app; cbn [length]; lia).
    assert (B2 : 0 + 2 <= 2 ^ (N.of_nat jn - N.of_nat (2 * length (ts' ++ [cfirst q])))).
    { rewrite length_app. cbn [length].
      assert (P : 2 ^ 1 <= 2 ^ (N.of_nat jn - N.of_nat (2 * (length ts' + 1)))) by (apply N.pow_le_mono_r; lia).
      rewrite N.pow_1_r in P. lia. }
    split.
    + intros P. specialize (F1 P). rewrite Fc, ecount_pow, <- Eb in F1.
      unfold bcells in F1. rewrite (tokcells_app houts), <- (app_assoc (tokcells houts)). rewrite Eh.
      exact (fsteps_vs _ _ _ _ _ _ _ _ _ _ _ F B1 B2 F1).
    + intros S. specialize (F2 S). rewrite Fc, ecount_pow, <- Eb in F2. rewrite Eh.
      exact (fsteps_hvs _ _ _ _ _ _ _ _ _ _ F B1 B2 F2).
Qed.

(* ---- the run ---- *)
Definition Vof (k : N) (w : word) : list bool := if N.even k then skipn 2 (wcells w) else wcells w.

Lemma round_ok : forall kn V V', (1 <= kn)%nat ->
  VS (2 ^ N.div2 (N.of_nat kn)) (lw (if N.even (N.of_nat kn) then V else true :: false :: V) Zinf)
     (lw (if N.even (N.of_nat kn) then V' else true :: false :: V') Zinf) ->
  config kn V -->+ config (S kn) V'.
Proof.
  intros kn V V' Hk H. unfold config.
  replace (Nat.pred (S kn)) with kn by lia.
  apply round_step.
  replace (S1 >> S0 >> strm (Nat.pred kn) V) with (strm kn V)
    by (destruct kn as [|kn]; [exfalso; lia|reflexivity]).
  apply VS1_vis. destruct (parity kn) as [j [-> | ->]]; destruct (half_N j) as [h0 h1]; destruct (even_N j) as [e0 e1].
  - rewrite e0, h0 in H. rewrite !strm_even. apply VS_Lp. rewrite N.mul_1_r. exact H.
  - rewrite e1, h1 in H. rewrite !strm_odd. apply VS_Lp. rewrite N.mul_1_r. exact H.
Qed.

Lemma stuck_ok : forall kn V, (1 <= kn)%nat ->
  HVS (2 ^ N.div2 (N.of_nat kn)) (lw (if N.even (N.of_nat kn) then V else true :: false :: V) Zinf) ->
  halts tm (config kn V).
Proof.
  intros kn V Hk H. unfold config. apply round_halt.
  replace (S1 >> S0 >> strm (Nat.pred kn) V) with (strm kn V)
    by (destruct kn as [|kn]; [exfalso; lia|reflexivity]).
  assert (HV1 : HVS 1 (strm kn V)).
  { destruct (parity kn) as [j [-> | ->]]; destruct (half_N j) as [h0 h1]; destruct (even_N j) as [e0 e1].
    - rewrite e0, h0 in H. rewrite strm_even. apply hvs_Lp. rewrite N.mul_1_r. exact H.
    - rewrite e1, h1 in H. rewrite strm_odd. apply hvs_Lp. rewrite N.mul_1_r. exact H. }
  destruct HV1 as [m [s1 [Hm [H1 H2]]]]. replace m with 0 in H1 by lia.
  rewrite (VS_inv0 _ _ H1). exact H2.
Qed.

Lemma scan_Vof : forall k w, scan k w = if N.even k then Vof k w else true :: false :: Vof k w.
Proof. intros k w. unfold scan, Vof. destruct (N.even k); reflexivity. Qed.

Lemma out_Vof : forall k w', headok k w' = true ->
  wcells w' = if N.even k then Vof (N.succ k) w' else true :: false :: Vof (N.succ k) w'.
Proof.
  intros k w' H. unfold Vof. rewrite N.even_succ, <- N.negb_even. unfold headok in H.
  destruct (N.even k); cbn [negb]; [reflexivity|].
  destruct w' as [[|t h] b].
  - destruct b as [tl0|q b| |]; try discriminate H. cbn [wcells app btoks btail].
    rewrite tokcells_app, tokcells_ctoks. destruct (cfirst q); [discriminate H|reflexivity|reflexivity].
  - cbn [wcells app tokcells]. destruct t; [discriminate H|reflexivity|reflexivity].
Qed.

Lemma jn_next : forall k, N.to_nat (N.div2 (N.succ k)) = if N.even k then N.to_nat (N.div2 k) else S (N.to_nat (N.div2 k)).
Proof.
  intros k. destruct (odd_split k) as [E B]. rewrite <- N.negb_odd.
  destruct (N.odd k) eqn:Eo; cbn [negb N.b2n] in *.
  - rewrite (div2_eq (N.succ k) (N.div2 k + 1)) by (left; lia). lia.
  - rewrite (div2_eq (N.succ k) (N.div2 k)) by (right; lia). reflexivity.
Qed.

Lemma run_proper : forall n k jn w k' jn' w', run table n k jn w = Some (k', jn', w') ->
  proper (wbody w') = true -> proper (wbody w) = true.
Proof.
  induction n as [|n IH]; intros k jn w k' jn' w' H P; cbn [run] in H.
  - injection H as _ _ <-. exact P.
  - destruct (headok k (round table k jn w)); [|discriminate H].
    specialize (IH _ _ _ _ _ _ H P).
    destruct (proper (wbody w)) eqn:Pw; [reflexivity|].
    pose proof (round_improper k jn w Pw) as B. unfold proper in IH. rewrite B in IH. discriminate IH.
Qed.

Lemma run_ok : forall n kn jn w k' jn' w', (1 <= kn)%nat -> jn = N.to_nat (N.div2 (N.of_nat kn)) ->
  run table n (N.of_nat kn) jn w = Some (k', jn', w') -> proper (wbody w') = true ->
  config kn (Vof (N.of_nat kn) w) -->* config (kn + n) (Vof k' w') /\ k' = N.of_nat (kn + n) /\
  jn' = N.to_nat (N.div2 k').
Proof.
  induction n as [|n IH]; intros kn jn w k' jn' w' Hk Hj H P; cbn [run] in H.
  - injection H as <- <- <-. replace (kn + 0)%nat with kn by lia. split; [apply evstep_refl|split; auto].
  - destruct (headok (N.of_nat kn) (round table (N.of_nat kn) jn w)) eqn:Hh; [|discriminate H].
    rewrite <- Nat2N.inj_succ in H.
    assert (Hj' : (if N.even (N.of_nat kn) then jn else S jn) = N.to_nat (N.div2 (N.of_nat (S kn))))
      by (rewrite Nat2N.inj_succ, jn_next, Hj; reflexivity).
    rewrite Hj' in H.
    destruct (IH (S kn) _ _ _ _ _ ltac:(lia) eq_refl H P) as [R1 [R2 R3]].
    pose proof (run_proper _ _ _ _ _ _ _ H P) as P1.
    destruct (round_sound (N.of_nat kn) jn w Hj) as [S1 _]. specialize (S1 P1).
    rewrite scan_Vof, (out_Vof _ _ Hh) in S1. rewrite <- Nat2N.inj_succ in S1.
    replace (kn + S n)%nat with (S kn + n)%nat by lia. split; [|split; assumption].
    eapply evstep_trans; [apply progress_evstep; apply round_ok; [exact Hk|]|exact R1].
    destruct (N.even (N.of_nat kn)); exact S1.
Qed.

Theorem halts_of_check : forall n, check n = true -> halts tm c0.
Proof.
  intros n H. unfold check in H.
  destruct (run table n 1 0 (W [] (BNil [true]))) as [[[k jn] w]|] eqn:E; [|discriminate H].
  destruct (bend (wbody (round table k jn w))) eqn:B; try discriminate H.
  assert (P : proper (wbody w) = true).
  { destruct (proper (wbody w)) eqn:Pw; [reflexivity|]. rewrite (round_improper k jn w Pw) in B. discriminate B. }
  change 1 with (N.of_nat 1) in E.
  destruct (run_ok n 1 0 _ _ _ _ (le_n 1) eq_refl E P) as [R1 [R2 R3]].
  destruct (round_sound k jn w R3) as [_ S]. specialize (S B).
  rewrite scan_Vof in S. subst k.
  eapply halts_evstep; [apply (stuck_ok (1 + n) (Vof (N.of_nat (1 + n)) w)); [lia|exact S]|].
  eapply evstep_trans; [apply progress_evstep; exact blank_start|]. exact R1.
Qed.

End Gen.

(* ---- the three tables: their visit law by execution (one set of tactics) ---- *)
Ltac run_to H := repeat (first [solve [finish] | eapply evstep_trans; [apply progress_evstep; apply H|] | step]).
Ltac run_to2 H1 H2 :=
  repeat (first [solve [finish] | eapply evstep_trans; [apply progress_evstep; apply H1|]
                | eapply evstep_trans; [apply progress_evstep; apply H2|] | step]).
Ltac run_halt := repeat (first [apply evstep_refl | eapply evstep_step; [prove_step|simpl_tape]]).
Ltac run_halt1 H := repeat (first [apply evstep_refl | eapply evstep_trans; [apply progress_evstep; apply H|]
                                  | eapply evstep_step; [prove_step|simpl_tape]]).
Ltac law :=
  first
  [ solve [intros r x l; execute]
  | solve [let H := fresh "H" in intros r r' H x l; eapply progress_intro; [prove_step|simpl_tape]; run_to H]
  | solve [let H1 := fresh "H" in let H2 := fresh "H" in
           intros r r1 r2 H1 H2 x l; eapply progress_intro; [prove_step|simpl_tape]; run_to2 H1 H2]
  | solve [intros r x l; solve_halt]
  | solve [let H := fresh "H" in intros r H x l; eapply halts_evstep; [apply H|]; run_halt]
  | solve [let H1 := fresh "H" in let H2 := fresh "H" in
           intros r r1 H1 H2 x l; eapply halts_evstep; [apply H2|]; run_halt1 H1]
  | solve [let H := fresh "H" in intros s s' H; unfold LE; eapply progress_intro; [prove_step|simpl_tape];
           repeat (first [apply progress_evstep; apply H | step])]
  | solve [let H := fresh "H" in intros s H; unfold LE; eapply halts_evstep; [apply H|]; run_halt]
  | solve [unfold c0, LE, tape0; eapply progress_intro; [prove_step|simpl_tape]; repeat (first [solve [finish] | step])]
  ].

Module T343.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---"%string).
Theorem halts_if : check 161210 = true -> halts tm c0.
Proof. intros H. eapply (halts_of_check tm); [law..|exact H]. Qed.
End T343.
Module T100.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---"%string).
Theorem halts_if : check 161210 = true -> halts tm c0.
Proof. intros H. eapply (halts_of_check tm); [law..|exact H]. Qed.
End T100.
Module T493.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---"%string).
Theorem halts_if : check 161210 = true -> halts tm c0.
Proof. intros H. eapply (halts_of_check tm); [law..|exact H]. Qed.
End T493.

(* ---- the run ---- *)
Lemma check_ok : check 161210 = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.

Theorem halts343 : halts T343.tm c0.
Proof. exact (T343.halts_if check_ok). Qed.
Theorem halts100 : halts T100.tm c0.
Proof. exact (T100.halts_if check_ok). Qed.
Theorem halts493 : halts T493.tm c0.
Proof. exact (T493.halts_if check_ok). Qed.
