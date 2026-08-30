From Coq Require Import Bool List Arith NArith ZArith Lia.
From BusyCoq Require Import Eqb.
Import ListNotations.

Module NCount.
  Definition t := N.
  Definition zero := 0%N.
  Definition one := 1%N.
  Definition of_nat := N.of_nat.
  Definition is_zero (x : t) := N.eqb x 0.
  Definition is_one (x : t) := N.eqb x 1.
  Definition leb := N.leb.
  Definition ltb := N.ltb.
  Definition add := N.add.
  Definition sub := N.sub.
  Definition mul := N.mul.
  Definition pred := N.pred.
  Definition succ := N.succ.
  Definition div2 := N.div2.
  Definition odd := N.odd.
End NCount.

Module TM101PersistentSim.

Inductive Q := A | B | C | D | E | F.
Inductive Dir := L | R.

Inductive Word :=
| W0011 | W00111 | W001111 | W0110 | W01101 | W0111 | W01111
| W10110 | W110110.

Definition word_eqb (x y : Word) : bool :=
  match x, y with
  | W0011,W0011 | W00111,W00111 | W001111,W001111
  | W0110,W0110 | W01101,W01101 | W0111,W0111
  | W01111,W01111 | W10110,W10110 | W110110,W110110 => true
  | _,_ => false
  end.

Definition spelling (w : Word) : list bool :=
  match w with
  | W0011 => [false;false;true;true]
  | W00111 => [false;false;true;true;true]
  | W001111 => [false;false;true;true;true;true]
  | W0110 => [false;true;true;false]
  | W01101 => [false;true;true;false;true]
  | W0111 => [false;true;true;true]
  | W01111 => [false;true;true;true;true]
  | W10110 => [true;false;true;true;false]
  | W110110 => [true;true;false;true;true;false]
  end.

Definition sep : list bool := [true;true;true;true].

(* A two-stack deque.  [front] is stored in logical order and [back] in
   reverse logical order.  Push and reversal never inspect or rebalance the
   opposite stack.  A half split is performed only when a pop finds its own
   stack empty; this is the usual amortised-O(1) implementation. *)
Record DSeq := dseq {
  ds_front : list NCount.t;
  ds_back : list NCount.t
}.

Definition ds_len (s : DSeq) : nat :=
  List.length (ds_front s) + List.length (ds_back s).

Definition ds_list (s : DSeq) : list NCount.t :=
  ds_front s ++ rev (ds_back s).

Definition ds_rebuild (xs : list NCount.t) : DSeq :=
  let n := List.length xs in
  let nf := Nat.div (S n) 2 in
  let f := firstn nf xs in
  let b := rev (skipn nf xs) in
  dseq f b.

(* Kept as a compatibility name for the representation lemmas.  Unlike the
   earlier implementation it deliberately performs no size comparison. *)
Definition ds_balance (nf : nat) (f : list NCount.t)
    (nb : nat) (b : list NCount.t) : DSeq :=
  dseq f b.

Definition ds_of_list (xs : list NCount.t) : DSeq := ds_rebuild xs.

Definition ds_rev (s : DSeq) : DSeq :=
  dseq (ds_back s) (ds_front s).

Definition ds_uncons (s : DSeq) : option (NCount.t * DSeq) :=
  match ds_front s with
  | x :: f => Some (x,dseq f (ds_back s))
  | [] =>
      match rev (ds_back s) with
      | [] => None
      | x :: xs => Some (x,ds_rebuild xs)
      end
  end.

Definition ds_cons (x : NCount.t) (s : DSeq) : DSeq :=
  dseq (x :: ds_front s) (ds_back s).

Definition ds_snoc (s : DSeq) (x : NCount.t) : DSeq :=
  dseq (ds_front s) (x :: ds_back s).

Definition ds_prepend (xs : list NCount.t) (s : DSeq) : DSeq :=
  fold_right ds_cons s xs.

Definition ds_nonempty (s : DSeq) : bool :=
  match ds_front s,ds_back s with
  | [],[] => false
  | _,_ => true
  end.

Definition ds_singleton (s : DSeq) : option NCount.t :=
  match ds_front s,ds_back s with
  | [x],[] | [],[x] => Some x
  | _,_ => None
  end.

Definition ds_at_least_two (s : DSeq) : bool :=
  match ds_front s,ds_back s with
  | _::_::_,_ | _,_::_::_ | _::_,_::_ => true
  | _,_ => false
  end.

Definition ds_unsnoc (s : DSeq) : option (DSeq * NCount.t) :=
  match ds_back s with
  | x :: b => Some (dseq (ds_front s) b,x)
  | [] =>
      match rev (ds_front s) with
      | [] => None
      | x :: xs => Some (ds_rebuild (rev xs),x)
      end
  end.

Inductive Block :=
| Lit (bits : list bool)
| Run (word : Word) (copies : NCount.t)
| Chain (word : Word) (counts : DSeq).

Definition Side := list Block.

Definition push_lit (bits : list bool) (s : Side) : Side :=
  match bits, s with
  | [], _ => s
  | _, Lit more :: rest => Lit (bits ++ more) :: rest
  | _, _ => Lit bits :: s
  end.

Definition push_bit (b : bool) (s : Side) : Side :=
  match s with
  | Lit more :: rest => Lit (b :: more) :: rest
  | _ => Lit [b] :: s
  end.

Definition push_run (w : Word) (n : NCount.t) (s : Side) : Side :=
  if NCount.is_zero n then s else
  match s with
  | Run w' n' :: rest =>
      if word_eqb w w' then Run w (NCount.add n n') :: rest else Run w n :: s
  | _ => Run w n :: s
  end.

Definition push_chain (w : Word) (ns : DSeq) (s : Side) : Side :=
  Chain w ns :: s.

Definition chain_expose (w : Word) (ns : DSeq) (s : Side) : Side :=
  match ds_uncons ns with
  | None => s
  | Some (n, rest) =>
      match ds_uncons rest with
      | None => push_run w n s
      | Some _ => push_run w n (Lit sep :: Chain w rest :: s)
      end
  end.

Fixpoint pop_bit_fuel (fuel : nat) (s : Side) : bool * Side :=
  match fuel with
  | O => (false,s)
  | S fuel' =>
      match s with
      | [] => (false,[])
      | Lit [] :: rest => pop_bit_fuel fuel' rest
      | Lit (b::bits) :: rest =>
          (b, match bits with [] => rest | _ => Lit bits :: rest end)
      | Run w n :: rest =>
          match spelling w with
          | [] => pop_bit_fuel fuel' rest
          | b :: bits =>
              let rest' := push_run w (NCount.pred n) rest in
              (b, push_lit bits rest')
          end
      | Chain w ns :: rest =>
          pop_bit_fuel fuel' (chain_expose w ns rest)
      end
  end.

Definition pop_bit := pop_bit_fuel 4.

Fixpoint strip_bits (bits : list bool) (s : Side) : option Side :=
  match bits with
  | [] => Some s
  | b :: bits' =>
      let '(b',s') := pop_bit s in
      if Bool.eqb b b' then strip_bits bits' s' else None
  end.

Definition starts (bits : list bool) (s : Side) : bool :=
  match strip_bits bits s with Some _ => true | None => false end.

Fixpoint strip_prefix (needle haystack : list bool) : option (list bool) :=
  match needle, haystack with
  | [], _ => Some haystack
  | _, [] => None
  | x::xs, y::ys => if Bool.eqb x y then strip_prefix xs ys else None
  end.

Fixpoint consume_lit_fuel (fuel : nat) (word bits : list bool)
    : nat * list bool :=
  match fuel with
  | O => (O,bits)
  | S fuel' =>
      match strip_prefix word bits with
      | Some bits' =>
          let '(n,rest) := consume_lit_fuel fuel' word bits' in (S n,rest)
      | None => (O,bits)
      end
  end.

Definition consume_lit (word bits : list bool) : nat * list bool :=
  consume_lit_fuel (List.length bits) word bits.

Definition expose_chain_after_first (w : Word) (ns : DSeq)
    (rest : Side) : NCount.t * Side :=
  match ds_uncons ns with
  | None => (NCount.zero, rest)
  | Some (n, ns') =>
      match ds_uncons ns' with
      | None => (n,rest)
      | Some _ => (n, Lit sep :: Chain w ns' :: rest)
      end
  end.

Fixpoint consume_word_fuel (fuel : nat) (w : Word) (s : Side)
    : NCount.t * Side :=
  match fuel with
  | O => (NCount.zero,s)
  | S fuel' =>
      match s with
      | Lit bits :: rest =>
          let '(k,bits') := consume_lit (spelling w) bits in
          match k with
          | O => (NCount.zero,s)
          | S k' =>
              let s' := match bits' with [] => rest | _ => Lit bits'::rest end in
              let '(n,s'') := consume_word_fuel fuel' w s' in
              (NCount.add (NCount.of_nat (S k')) n, s'')
          end
      | Run w' n :: rest =>
          if word_eqb w w' then
            let '(m,s') := consume_word_fuel fuel' w rest in
            (NCount.add n m,s')
          else (NCount.zero,s)
      | Chain w' ns :: rest =>
          if word_eqb w w' then expose_chain_after_first w ns rest
          else (NCount.zero,s)
      | [] => (NCount.zero,[])
      end
  end.

Definition consume_word := consume_word_fuel 8.

Definition one_sequence (w : Word) (n : NCount.t) (tail : Side) : Side :=
  push_run w n tail.

Fixpoint bits_eqb (xs ys : list bool) : bool :=
  match xs,ys with
  | [],[] => true
  | x::xs',y::ys' => Bool.eqb x y && bits_eqb xs' ys'
  | _,_ => false
  end.

Definition push_sequence (w : Word) (ns : DSeq) (tail : Side) : Side :=
  match ds_singleton ns with
  | Some n => one_sequence w n tail
  | None => if ds_nonempty ns then push_chain w ns tail else tail
  end.

Fixpoint collect_runs (fuel : nat) (w : Word) (s : Side)
    : option (DSeq * Side) :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | Chain w' ns :: rest =>
          if word_eqb w w' then
            Some (ns,rest)
          else None
      | Run w' n :: rest =>
          if word_eqb w w' then
            match rest with
            | Lit bits :: after_sep =>
                if bits_eqb bits sep then
                  match collect_runs fuel' w after_sep with
                  | Some (ns,tail) => Some (ds_cons n ns,tail)
                  | None => Some (ds_of_list [n],rest)
                  end
                else Some (ds_of_list [n],rest)
            | _ => Some (ds_of_list [n],rest)
            end
          else None
      | _ => None
      end
  end.

Definition collect_chain (w : Word) (s : Side) : option (DSeq * Side) :=
  collect_runs (S (List.length s)) w s.

Record Machine := {
  m_state : Q;
  m_dir : Dir;
  m_left : Side;
  m_right : Side;
  m_incs : N
}.

Definition machine (q : Q) (d : Dir) (l r : Side) (incs : N) : Machine :=
  {| m_state := q; m_dir := d; m_left := l; m_right := r;
     m_incs := incs |}.

Definition active (m : Machine) : Side :=
  match m_dir m with L => m_left m | R => m_right m end.

Definition Transition := (bool * Dir * Q)%type.

Definition trans (q : Q) (b : bool) : option Transition :=
  match q,b with
  | A,false => Some (true,L,B) | A,true => Some (true,L,F)
  | B,false => Some (true,L,C) | B,true => Some (true,L,B)
  | C,false => Some (true,R,D) | C,true => Some (false,L,A)
  | D,false => Some (true,R,A) | D,true => Some (true,R,E)
  | E,false => None | E,true => Some (false,R,F)
  | F,false => Some (false,R,C) | F,true => Some (true,R,F)
  end.

Definition raw_step (m : Machine) : option Machine :=
  let '(b,act') := pop_bit (active m) in
  let '(l,r) :=
    match m_dir m with
    | L => (act',m_right m)
    | R => (m_left m,act')
    end in
  match trans (m_state m) b with
  | None => None
  | Some (write,L,q) =>
      Some (machine q L l (push_bit write r) (m_incs m))
  | Some (write,R,q) =>
      Some (machine q R (push_bit write l) r (m_incs m))
  end.

Definition apply_right_shift (m : Machine) (input output : Word)
    : option Machine :=
  let '(n,r) := consume_word input (m_right m) in
  if NCount.is_zero n then None else
  Some (machine (m_state m) R (push_run output n (m_left m)) r
          (m_incs m)).

Definition apply_left_shift (m : Machine) (fixed : list bool)
    (input output : Word) : option Machine :=
  match strip_bits fixed (m_right m) with
  | None => None
  | Some r =>
      let '(n,l) := consume_word input (m_left m) in
      if NCount.is_zero n then None else
      Some (machine (m_state m) L l (push_lit fixed (push_run output n r))
              (m_incs m))
  end.

Definition first_some {A0} (x y : option A0) : option A0 :=
  match x with Some _ => x | None => y end.

Definition apply_shift (m : Machine) : option Machine :=
  match m_state m, m_dir m with
  | F,R =>
      match apply_right_shift m W001111 W110110 with
      | Some m' => Some m'
      | None =>
          match apply_right_shift m W00111 W10110 with
          | Some m' => Some m'
          | None => apply_right_shift m W0011 W0110
          end
      end
  | B,L =>
      match apply_left_shift m [true] W110110 W001111 with
      | Some m' => Some m'
      | None =>
          match apply_left_shift m [true] W0110 W0011 with
          | Some m' => Some m'
          | None => apply_left_shift m [true] W10110 W00111
          end
      end
  | C,L =>
      match apply_left_shift m sep W110110 W001111 with
      | Some m' => Some m'
      | None =>
          match apply_left_shift m sep W10110 W01111 with
          | Some m' => Some m'
          | None => apply_left_shift m
              [true;true;true;true;true;false;true;true;true;true]
              W0110 W0111
          end
      end
  | _,_ => None
  end.

Definition literal_drop (bits prefix : list bool) (rest : Side)
    : option Side :=
  match strip_prefix prefix bits with
  | None => None
  | Some bits' =>
      Some (match bits' with [] => rest | _ => Lit bits' :: rest end)
  end.

Fixpoint collect_chain_chunks (fuel : nat) (w : Word) (s : Side)
    : option (list DSeq * Side) :=
  match fuel with
  | O => None
  | S fuel' =>
      let continue (ns : DSeq) (rest : Side) :=
        match rest with
        | Lit bits :: after_sep =>
            if bits_eqb bits sep then
              match collect_chain_chunks fuel' w after_sep with
              | Some (chunks,tail) => Some (ns::chunks,tail)
              | None => Some ([ns],rest)
              end
            else Some ([ns],rest)
        | _ => Some ([ns],rest)
        end in
      match s with
      | Run w' n :: rest =>
          if word_eqb w w' && negb (NCount.is_zero n)
          then continue (ds_of_list [n]) rest else None
      | Chain w' ns :: rest =>
          if word_eqb w w' && ds_nonempty ns
          then continue ns rest else None
      | _ => None
      end
  end.

Fixpoint chunks_at_least_two (chunks : list DSeq) : bool :=
  match chunks with
  | [] => false
  | ns :: chunks' =>
      if ds_at_least_two ns then true else
      if ds_nonempty ns then
        match chunks' with [] => false | _ => true end
      else chunks_at_least_two chunks'
  end.

Fixpoint push_chunks (w : Word) (chunks : list DSeq) (tail : Side) : Side :=
  match chunks with
  | [] => tail
  | [ns] => push_sequence w ns tail
  | ns :: chunks' =>
      push_sequence w ns (Lit sep :: push_chunks w chunks' tail)
  end.

Definition chunks_cons (x : NCount.t) (chunks : list DSeq) : list DSeq :=
  match chunks with
  | [] => [ds_of_list [x]]
  | ns :: chunks' => ds_cons x ns :: chunks'
  end.

Fixpoint chunks_uncons (chunks : list DSeq)
    : option (NCount.t * list DSeq) :=
  match chunks with
  | [] => None
  | ns :: chunks' =>
      match ds_uncons ns with
      | None => chunks_uncons chunks'
      | Some (x,ns') =>
          if negb (ds_nonempty ns')
          then Some (x,chunks') else Some (x,ns'::chunks')
      end
  end.

Fixpoint chunks_unsnoc (chunks : list DSeq)
    : option (list DSeq * NCount.t) :=
  match chunks with
  | [] => None
  | [ns] =>
      match ds_unsnoc ns with
      | None => None
      | Some (ns',x) =>
          if negb (ds_nonempty ns')
          then Some ([],x) else Some ([ns'],x)
      end
  | ns :: chunks' =>
      match chunks_unsnoc chunks' with
      | Some (prefix,x) => Some (ns::prefix,x)
      | None =>
          match ds_unsnoc ns with
          | None => None
          | Some (ns',x) =>
              if negb (ds_nonempty ns')
              then Some ([],x) else Some ([ns'],x)
          end
      end
  end.

Fixpoint take_last_chunks (count : nat) (chunks : list DSeq)
    (acc : list NCount.t) : option (list DSeq * list NCount.t) :=
  match count with
  | O => Some (chunks,acc)
  | S count' =>
      match chunks_unsnoc chunks with
      | Some (prefix,x) => take_last_chunks count' prefix (x::acc)
      | None => None
      end
  end.

(* If chunks denote S1++...++Sk, this constructs rev(Sk)++...++rev(S1)
   with one explicit separator between adjacent chunks, without copying any
   exponent list. *)
Definition apply_chain_right (m : Machine) : option Machine :=
  match collect_chain W001111 (m_right m) with
  | None => None
  | Some (ns,rest) =>
      match rest with
      | Lit bits :: tail =>
          match literal_drop bits sep tail with
          | Some r =>
              Some (machine F R
                (push_lit sep
                  (push_sequence W110110 (ds_rev ns) (m_left m)))
                r (m_incs m))
          | None =>
              if ds_at_least_two ns then
                Some (machine F R
                  (push_sequence W110110 (ds_rev ns) (m_left m))
                  rest (m_incs m))
              else None
          end
      | _ =>
          if ds_at_least_two ns then
            Some (machine F R
              (push_sequence W110110 (ds_rev ns) (m_left m))
              rest (m_incs m))
          else None
      end
  end.

Definition apply_chain_left (m : Machine) : option Machine :=
  match strip_bits [true] (m_right m) with
  | None => None
  | Some r =>
      match m_left m with
      | Lit bits :: after_lit =>
          if bits_eqb bits sep then
            match collect_chain W110110 after_lit with
            | Some (ns,l) =>
                Some (machine B L l
                  (push_lit [true]
                    (push_sequence W001111 (ds_rev ns)
                      (push_lit sep r)))
                  (m_incs m))
            | None =>
                match collect_chain W110110 (m_left m) with
                | Some (ns,l) =>
                    if ds_at_least_two ns then
                      Some (machine B L l
                        (push_lit [true]
                          (push_sequence W001111 (ds_rev ns) r))
                        (m_incs m))
                    else None
                | None => None
                end
            end
          else
            match collect_chain W110110 (m_left m) with
            | Some (ns,l) =>
                if ds_at_least_two ns then
                  Some (machine B L l
                    (push_lit [true]
                      (push_sequence W001111 (ds_rev ns) r))
                    (m_incs m))
                else None
            | None => None
            end
      | _ =>
          match collect_chain W110110 (m_left m) with
          | Some (ns,l) =>
              if ds_at_least_two ns then
                Some (machine B L l
                  (push_lit [true]
                    (push_sequence W001111 (ds_rev ns) r))
                  (m_incs m))
              else None
          | None => None
          end
      end
  end.

Definition apply_chain (m : Machine) : option Machine :=
  match m_state m,m_dir m with
  | F,R => apply_chain_right m
  | B,L => apply_chain_left m
  | _,_ => None
  end.

Record BoundaryPrefix := {
  bp_a : NCount.t;
  bp_header : Side;
  bp_xs : DSeq;
  bp_tail : Side
}.

Record BoundaryChunks := {
  bc_a : NCount.t;
  bc_header : Side;
  bc_xs : list DSeq;
  bc_tail : Side
}.

Definition positive_run (w : Word) (b : Block) : bool :=
  match b with
  | Run w' n => word_eqb w w' && negb (NCount.is_zero n)
  | _ => false
  end.

Definition parse_boundary_header (r1 : Side) : Side * Side :=
  match r1 with
  | Run W001111 n :: Run W00111 b :: rest =>
      if negb (NCount.is_zero n) && negb (NCount.is_zero b)
      then ([Run W001111 n;Run W00111 b],rest) else ([],r1)
  | Chain W001111 ns :: Run W00111 b :: rest =>
      if ds_nonempty ns &&
         negb (NCount.is_zero b)
      then ([Chain W001111 ns;Run W00111 b],rest) else ([],r1)
  | Lit bits :: b :: c :: rest =>
      if bits_eqb bits [true;true;true] &&
         positive_run W00111 b && positive_run W0011 c
      then ([Lit bits;b;c],rest) else ([],r1)
  | _ => ([],r1)
  end.

Definition parse_boundary_prefix (m : Machine) : option BoundaryPrefix :=
  match m_state m,m_dir m,m_left m with
  | C,L,[] =>
      match strip_bits [true;true] (m_right m) with
      | None => None
      | Some r0 =>
          let '(a,r1) := consume_word W0011 r0 in
          let '(header,r2) := parse_boundary_header r1 in
          match collect_chain W001111 r2 with
          | None => None
          | Some (xs,tail) =>
              Some {| bp_a:=a; bp_header:=header; bp_xs:=xs;
                      bp_tail:=tail |}
          end
      end
  | _,_,_ => None
  end.

Definition parse_boundary_chunks (m : Machine) : option BoundaryChunks :=
  match m_state m,m_dir m,m_left m with
  | C,L,[] =>
      match strip_bits [true;true] (m_right m) with
      | None => None
      | Some r0 =>
          let '(a,r1) := consume_word W0011 r0 in
          let '(header,r2) := parse_boundary_header r1 in
          match collect_chain_chunks (S (List.length r2)) W001111 r2 with
          | None => None
          | Some (xs,tail) =>
              Some {| bc_a:=a; bc_header:=header; bc_xs:=xs;
                      bc_tail:=tail |}
          end
      end
  | _,_,_ => None
  end.

Definition make_boundary_right (a : NCount.t) (header : Side) (xs : DSeq)
    (tail : Side) : Side :=
  push_lit [true;true]
    (push_run W0011 a (header ++ push_sequence W001111 xs tail)).

Definition make_boundary_chunks_right (a : NCount.t) (header : Side)
    (xs : list DSeq) (tail : Side) : Side :=
  push_lit [true;true]
    (push_run W0011 a (header ++ push_chunks W001111 xs tail)).

Fixpoint take_ones (bits : list bool) : nat * list bool :=
  match bits with
  | true :: rest => let '(n,tail) := take_ones rest in (S n,tail)
  | _ => (O,bits)
  end.

Fixpoint ones (n : nat) : list bool :=
  match n with O => [] | S n' => true :: ones n' end.

Definition phase_counts (bits : list bool) : option (nat * nat) :=
  let '(p,rest) := take_ones bits in
  match rest with
  | false :: suffix =>
      let '(k,tail) := take_ones suffix in
      match k,tail with O,_ => None | S _,[] => Some (p,k) | _,_ => None end
  | _ => None
  end.

Definition zero_leading (b : Block) : bool :=
  match b with
  | Lit (false::_) => true
  | Run w n | Chain w n =>
      match spelling w with false::_ => true | _ => false end
  | _ => false
  end.

Definition apply_boundary_delete (m : Machine) : option Machine :=
  match parse_boundary_prefix m with
  | None => None
  | Some p =>
      match bp_tail p with
      | Lit bits :: tail =>
          match phase_counts bits with
          | None => None
          | Some (leading,k) =>
              if match tail with [] => true | b::_ => zero_leading b end then
                let marker := Lit (ones leading ++ [false]) in
                let right := make_boundary_right
                  (NCount.add (bp_a p) (NCount.of_nat k))
                  (bp_header p) (bp_xs p)
                  (marker::tail) in
                Some (machine C L [] right (m_incs m))
              else None
          end
      | _ => None
      end
  end.

Definition literal_minor_left (bits : list bool) : option nat :=
  match bits with
  | [true;false] => Some 1
  | [true;true;false] => Some 2
  | [true;true;true;false] => Some 3
  | _ => None
  end.

Definition minor_right_bits (p : nat) :=
  [true;true;true;false] ++ ones p.

Definition apply_boundary_minor (m : Machine) : option Machine :=
  match parse_boundary_prefix m with
  | None => None
  | Some p =>
      match bp_tail p with
      | Lit left_phase :: Run W001111 n :: Lit right_phase :: context :: tail =>
          match literal_minor_left left_phase with
          | None => None
          | Some k =>
              if NCount.leb (NCount.of_nat 2) n &&
                 bits_eqb right_phase (minor_right_bits k) &&
                 match context with
                 | Run W001111 q =>
                     negb (NCount.is_zero q)
                 | Chain W001111 _ => true
                 | _ => false
                 end then
                let new_tail :=
                  Lit (ones (Nat.pred k) ++ [false]) ::
                  Run W001111 (NCount.pred n) ::
                  Lit (minor_right_bits (Nat.pred k)) :: context :: tail in
                let right := make_boundary_right
                  (NCount.add (bp_a p) (NCount.of_nat 8))
                  (bp_header p) (bp_xs p) new_tail in
                Some (machine C L [] right (m_incs m))
              else None
          end
      | _ => None
      end
  end.

Definition apply_boundary_transfer (m : Machine) : option Machine :=
  match parse_boundary_prefix m with
  | None => None
  | Some p =>
      match bp_tail p with
      | Lit marker :: rest =>
          if bits_eqb marker
            [true;true;false;true;true;true;true;true;true;true] &&
             ds_at_least_two (bp_xs p) then
            match ds_unsnoc (bp_xs p) with
            | Some (lhs,x) =>
              if NCount.leb (NCount.of_nat 2) x then
              match collect_chain W001111 rest with
              | None => None
              | Some (rhs,after_rhs) =>
                  if ds_at_least_two rhs then
                    match ds_uncons rhs,after_rhs with
                    | Some (r0,rhs_tail), Lit phase :: tail =>
                        match phase_counts phase with
                        | Some (leading,k) =>
                            if NCount.leb (NCount.of_nat 4) r0 && Nat.leb 4 k then
                              let rhs' := ds_cons (NCount.pred x)
                                (ds_cons (NCount.sub r0 (NCount.of_nat 3))
                                  rhs_tail) in
                              let phase' := Lit
                                (ones leading ++ [false] ++
                                 ones (k-4)) in
                              let right := make_boundary_right
                                (NCount.add (bp_a p) (NCount.of_nat 28))
                                (bp_header p) lhs
                                (Lit marker ::
                                 push_sequence W001111 rhs'
                                   (phase'::tail)) in
                              Some (machine C L [] right (m_incs m))
                            else None
                        | None => None
                        end
                    | _,_ => None
                    end
                  else None
              end
              else None
            | None => None
            end
          else None
      | _ => None
      end
  end.

Definition h_local_step (m : Machine) : option Machine :=
  match apply_chain m with
  | Some m' => Some m'
  | None =>
      match apply_shift m with
      | Some m' => Some m'
      | None => raw_step m
      end
  end.

Definition h_returned (m : Machine) : option Side :=
  match m_state m,m_dir m,m_left m with
  | B,L,[] => strip_bits [true] (m_right m)
  | _,_,_ => None
  end.

Definition crossed_left_boundary (m : Machine) : bool :=
  match m_dir m,m_left m with
  | L,[] => true
  | _,_ => false
  end.

Fixpoint run_h_fuel (fuel : nat) (m : Machine) : option Side :=
  if crossed_left_boundary m then h_returned m else
      match fuel with
      | O => None
      | S fuel' =>
          match h_local_step m with
          | Some m' => run_h_fuel fuel' m'
          | None => None
          end
      end
  .

Definition run_h (r : Side) : option Side :=
  run_h_fuel 4096 (machine F R [] r 0%N).

Fixpoint run_hs (calls : nat) (r : Side) : option Side :=
  match calls with
  | O => Some r
  | S calls' =>
      match run_h r with
      | Some r' => run_hs calls' r'
      | None => None
      end
  end.

(* The horizontal core28 rule keeps [k] last RHS groups in the suffix.  The
   actual trajectory needs k=1 or k=2; trying both is deterministic and was
   independently checked by the C++ executor against every one of the first
   ten thousand candidates. *)
Definition apply_boundary_core_split_chunks (k : nat) (p : BoundaryChunks)
    (marker : list bool) (rhs : list DSeq) (after_rhs : Side)
    : option Machine :=
  match chunks_unsnoc (bc_xs p),take_last_chunks k rhs [] with
  | Some (lhs,x),Some (main,tail_counts) =>
      match chunks_uncons main with
      | Some (r0,middle) =>
          if NCount.leb (NCount.of_nat 2) x &&
             NCount.leb (NCount.of_nat 4) r0 then
            let tail_input :=
              push_sequence W001111 (ds_of_list tail_counts) after_rhs in
            match run_hs 4 tail_input with
            | Some tail_output =>
                let rhs' := chunks_cons (NCount.pred x)
                  (chunks_cons (NCount.sub r0 (NCount.of_nat 3)) middle) in
                let right := make_boundary_chunks_right
                  (NCount.add (bc_a p) (NCount.of_nat 28))
                  (bc_header p) lhs
                  (Lit marker :: push_chunks W001111 rhs'
                    (Lit sep :: tail_output)) in
                Some (machine C L [] right 0%N)
            | None => None
            end
          else None
      | None => None
      end
  | _,_ => None
  end.

Definition apply_boundary_core_chunks (m : Machine) : option Machine :=
  match parse_boundary_chunks m with
  | Some p =>
      match bc_tail p with
      | Lit marker :: rest =>
          if bits_eqb marker
               [true;true;false;true;true;true;true;true;true;true] &&
             chunks_at_least_two (bc_xs p) then
            match collect_chain_chunks (S (List.length rest)) W001111 rest with
            | Some (rhs,after_rhs) =>
                match apply_boundary_core_split_chunks 1 p marker rhs after_rhs
                with
                | Some m' =>
                    Some (machine (m_state m') (m_dir m') (m_left m')
                      (m_right m') (m_incs m))
                | None =>
                    match apply_boundary_core_split_chunks 2 p marker rhs
                            after_rhs with
                    | Some m' =>
                        Some (machine (m_state m') (m_dir m') (m_left m')
                          (m_right m') (m_incs m))
                    | None => None
                    end
                end
            | None => None
            end
          else None
      | _ => None
      end
  | None => None
  end.

Definition apply_boundary_core (m : Machine) : option Machine :=
  apply_boundary_core_chunks m.

Definition apply_boundary_plain (m : Machine) : option Machine :=
  match apply_boundary_transfer m with
  | Some m' => Some m'
  | None =>
      match apply_boundary_delete m with
      | Some m' => Some m'
      | None => apply_boundary_minor m
      end
  end.

Definition apply_boundary (m : Machine) : option Machine :=
  (* [core28] already closes the same forward orbit.  The optional 196-phase
     super-rule saves very few events but would duplicate a large proof, so
     the certified executor deliberately keeps the smaller proof kernel. *)
  match apply_boundary_core m with
  | Some m' => Some m'
  | None => apply_boundary_plain m
  end.

Inductive IncKind := Inc1 | Inc2.
Record IncMatch := {
  im_kind : IncKind;
  im_a : NCount.t; im_b : NCount.t; im_c : NCount.t;
  im_rest : Side
}.

Definition ge2 (n : NCount.t) : bool := NCount.leb (NCount.of_nat 2) n.
Definition ge3 (n : NCount.t) : bool := NCount.leb (NCount.of_nat 3) n.

Definition match_inc1 (k : NCount.t) (s : Side) : option IncMatch :=
  if NCount.is_zero k then None else
  match strip_bits [true;true;true] s with
  | None => None
  | Some s1 =>
      let '(b,s2) := consume_word W00111 s1 in
      let '(c,s3) := consume_word W0111 s2 in
      if ge2 c then
        Some {| im_kind:=Inc1; im_a:=NCount.pred k; im_b:=b; im_c:=c;
                im_rest:=s3 |}
      else None
  end.

Definition match_inc2 (k : NCount.t) (s : Side) : option IncMatch :=
  let '(a,b,s1) :=
    match strip_bits [true;true] s with
    | Some s' =>
        if NCount.is_zero k then (k,NCount.zero,s) else
        let '(n,s'') := consume_word W001111 s' in
        (NCount.pred k,NCount.succ n,s'')
    | None =>
        let '(n,s') := consume_word W001111 s in (k,n,s')
    end in
  match s1 with
  | Lit [false] :: rest =>
      let '(c,s2) := consume_word W01111 rest in
      if ge3 c then
        Some {| im_kind:=Inc2; im_a:=a; im_b:=NCount.succ b;
                im_c:=NCount.pred c; im_rest:=s2 |}
      else None
  | _ =>
      let '(c,s2) := consume_word W01111 s1 in
      if ge2 c then
        Some {| im_kind:=Inc2; im_a:=a; im_b:=b; im_c:=c;
                im_rest:=s2 |}
      else None
  end.

Definition match_inc (m : Machine) : option IncMatch :=
  match m_state m, m_dir m, m_left m with
  | C,L,[] =>
      match strip_bits [true;true] (m_right m) with
      | None => None
      | Some s =>
          let '(k,s') := consume_word W0011 s in
          match match_inc1 k s' with
          | Some im => Some im
          | None => match_inc2 k s'
          end
      end
  | _,_,_ => None
  end.

Definition parity (n : NCount.t) : NCount.t :=
  if NCount.odd n then NCount.one else NCount.zero.

Definition apply_inc (m : Machine) : option Machine :=
  match match_inc m with
  | None => None
  | Some im =>
      let q := NCount.div2 (im_c im) in
      let c := parity (im_c im) in
      let out :=
        match im_kind im with
        | Inc1 =>
            push_lit [true;true]
             (push_run W0011
                (NCount.add (im_a im) (NCount.mul (NCount.of_nat 3) q))
              (push_lit [false;false;true;true;true;true;true]
               (push_run W00111 (NCount.add (im_b im) q)
                (push_run W0111 c (im_rest im)))))
        | Inc2 =>
            push_lit [true;true]
             (push_run W0011
                (NCount.add (im_a im) (NCount.mul (NCount.of_nat 4) q))
              (push_run W001111 (NCount.add (im_b im) q)
               (push_run W01111 c (im_rest im))))
        end in
      Some (machine C L [] out (N.succ (m_incs m)))
  end.

Definition at_left_boundary (m : Machine) : bool :=
  match m_state m,m_dir m,m_left m with
  | C,L,[] => true
  | _,_,_ => false
  end.

Definition active_literal (m : Machine) : bool :=
  match m_dir m with
  | L => match m_left m with Lit _ :: _ => true | _ => false end
  | R => match m_right m with Lit _ :: _ => true | _ => false end
  end.

Fixpoint raw_burst_more (fuel : nat) (m : Machine) : Machine :=
  match fuel with
  | O => m
  | S fuel' =>
      if at_left_boundary m || negb (active_literal m) then m else
      match raw_step m with
      | Some m' => raw_burst_more fuel' m'
      | None => m
      end
  end.

Definition raw_burst (m : Machine) : option Machine :=
  match raw_step m with
  | Some m' => Some (raw_burst_more 255 m')
  | None => None
  end.

Definition astep (m : Machine) : option Machine :=
  match apply_inc m with
  | Some m' => Some m'
  | None =>
      match apply_boundary m with
      | Some m' => Some m'
      | None =>
          match apply_chain m with
          | Some m' => Some m'
          | None =>
              match apply_shift m with
              | Some m' => Some m'
              | None => raw_burst m
              end
          end
      end
  end.

Definition init : Machine := machine A R [] [] 0.

Definition exec_until_step (m : Machine) : Machine + Machine :=
  match astep m with
  | Some m' => inl m'
  | None => inr m
  end.

(* A tail-recursive outer loop bounds the live native-computation stack.  A
   single very large [N_iter_until] is extensionally fine, but its binary
   recursion can retain a logarithmic collection of old, heavily shared
   machine states.  Million-event chunks let the OCaml GC reclaim each such
   collection before the next chunk. *)
Fixpoint exec_until_chunks (chunk_size : N) (chunks : nat)
    (s : Machine + Machine)
    : Machine + Machine :=
  match chunks with
  | O => s
  | S chunks' =>
      match s with
      | inr _ => s
      | inl _ =>
          exec_until_chunks chunk_size chunks'
            (N_iter_until exec_until_step s chunk_size)
      end
  end.

Definition run_exec_until_chunks (chunks : nat) : Machine + Machine :=
  exec_until_chunks 1000000%N chunks (inl init).

End TM101PersistentSim.

Require Import ZifyNat String List.
From BusyCoq Require Import Individual62 Longitudinal ES_v3.

Definition tm := Eval compute in (TM_from_str "1LB1LF_1LC1LB_1RD0LA_1RA1RE_---0RF_0RC1RF").

Module TM101.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 a b c r :=
  0inf <{{C}} [1;1] *> [0;0;1;1]^^a *> [0;0;1;1;1;1;1] *>
  [0;0;1;1;1]^^b *> [0;1;1;1]^^c *> r.

Definition S2 a b c r :=
  0inf <{{C}} [1;1] *> [0;0;1;1]^^a *> [0;0;1;1;1;1]^^b *>
  [0;1;1;1;1]^^c *> r.

Lemma Inc1 a b c r:
  S1 a b (2+c) r -->* S1 (3+a) (1+b) c r.
Proof.
  unfold S1.
  es' a b c & r.
Qed.

Lemma Inc2 a b c r:
  S2 a b (2+c) r -->* S2 (4+a) (1+b) c r.
Proof.
  unfold S2.
  es' a b c & r.
Qed.

Lemma Inc1s q a b c r:
  S1 a b (2*q+c) r -->*
  S1 (3*q+a) (q+b) c r.
Proof.
  gen a b.
  induction q as [|q IH]; intros a b.
  - cbn; finish.
  - change (S1 a b (2 * S q + c) r -->*
            S1 (3 * S q + a) (S q + b) c r).
    replace (2 * S q + c) with (2 + (2*q+c)) by lia.
    eapply evstep_trans.
    1: apply Inc1.
    eapply evstep_trans.
    1: apply IH.
    replace (3 * S q + a) with (3*q+(3+a)) by lia.
    replace (S q + b) with (q+(1+b)) by lia.
    finish.
Qed.

Lemma Inc2s q a b c r:
  S2 a b (2*q+c) r -->*
  S2 (4*q+a) (q+b) c r.
Proof.
  gen a b.
  induction q as [|q IH]; intros a b.
  - cbn; finish.
  - change (S2 a b (2 * S q + c) r -->*
            S2 (4 * S q + a) (S q + b) c r).
    replace (2 * S q + c) with (2 + (2*q+c)) by lia.
    eapply evstep_trans.
    1: apply Inc2.
    eapply evstep_trans.
    1: apply IH.
    replace (4 * S q + a) with (4*q+(4+a)) by lia.
    replace (S q + b) with (q+(1+b)) by lia.
    finish.
Qed.



Lemma FR_001111 n l r:
  l {{F}}> [0;0;1;1;1;1]^^n *> r -->*
  l <* [1;1;0;1;1;0]^^n {{F}}> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma FR_00111 n l r:
  l {{F}}> [0;0;1;1;1]^^n *> r -->*
  l <* [1;0;1;1;0]^^n {{F}}> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma FR_0011 n l r:
  l {{F}}> [0;0;1;1]^^n *> r -->*
  l <* [0;1;1;0]^^n {{F}}> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma BL_011011_1 n l r:
  l <* [1;1;0;1;1;0]^^n <{{B}} [1] *> r -->*
  l <{{B}} [1] *> [0;0;1;1;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma BL_0110_1 n l r:
  l <* [0;1;1;0]^^n <{{B}} [1] *> r -->*
  l <{{B}} [1] *> [0;0;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma BL_01101_1 n l r:
  l <* [1;0;1;1;0]^^n <{{B}} [1] *> r -->*
  l <{{B}} [1] *> [0;0;1;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma CL_011011_1111 n l r:
  l <* [1;1;0;1;1;0]^^n <{{C}} [1;1;1;1] *> r -->*
  l <{{C}} [1;1;1;1] *> [0;0;1;1;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma CL_01101_1111 n l r:
  l <* [1;0;1;1;0]^^n <{{C}} [1;1;1;1] *> r -->*
  l <{{C}} [1;1;1;1] *> [0;1;1;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Lemma CL_0110_1111101111 n l r:
  l <* [0;1;1;0]^^n <{{C}} [1;1;1;1;1;0;1;1;1;1] *> r -->*
  l <{{C}} [1;1;1;1;1;0;1;1;1;1] *> [0;1;1;1]^^n *> r.
Proof.
  shift_rule.
  intros l0 r0.
  es' & l0 r0.
Qed.

Definition X : list Sym := [0;0;1;1;1;1].
Definition YL : list Sym := [1;1;0;1;1;0].
Definition Sep : list Sym := [1;1;1;1].

Fixpoint RGroups (ns : list nat) (r : side) : side :=
  match ns with
  | [] => r
  | n :: ns => X^^n *> Sep *> RGroups ns r
  end.

Fixpoint LGroups (ns : list nat) (l : side) : side :=
  match ns with
  | [] => l
  | n :: ns => LGroups ns (l <* YL^^n <* Sep)
  end.

Lemma RGroups_snoc ns n r:
  RGroups (ns ++ [n]) r = RGroups ns (X^^n *> Sep *> r).
Proof. induction ns; cbn; [reflexivity|rewrite IHns; reflexivity]. Qed.

Lemma FR_groups ns l r:
  l {{F}}> RGroups ns r -->*
  LGroups ns l {{F}}> r.
Proof.
  gen l.
  induction ns as [|n ns IH]; intros l; cbn [RGroups LGroups].
  - finish.
  - unfold X, YL, Sep.
    follow FR_001111.
    do 4 step1.
    fold X YL Sep.
    follow IH.
    finish.
Qed.

Lemma BL_groups ns l r:
  LGroups ns l <{{B}} [1] *> r -->*
  l <{{B}} [1] *> RGroups ns r.
Proof.
  gen l.
  induction ns as [|n ns IH]; intros l; cbn [RGroups LGroups].
  - finish.
  - follow IH.
    unfold Sep, YL, X.
    do 4 step1.
    follow BL_011011_1.
    finish.
Qed.

(* The hot single-column case used by the high-level transducer.  Keeping
   these as named interfaces prevents later proofs from reopening the list
   induction merely to cross one [X^n Sep] column. *)
Lemma FR_group n l r:
  l {{F}}> X^^n *> Sep *> r -->*
  l <* YL^^n <* Sep {{F}}> r.
Proof. exact (FR_groups [n] l r). Qed.

Lemma BL_group n l r:
  l <* YL^^n <* Sep <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X^^n *> Sep *> r.
Proof. exact (BL_groups [n] l r). Qed.

Lemma FR_chain ns n l r:
  l {{F}}> RGroups ns (X^^n *> r) -->*
  LGroups ns l <* YL^^n {{F}}> r.
Proof.
  follow FR_groups.
  unfold X, YL.
  follow FR_001111.
  finish.
Qed.

Lemma BL_chain ns n l r:
  LGroups ns l <* YL^^n <{{B}} [1] *> r -->*
  l <{{B}} [1] *> RGroups ns (X^^n *> r).
Proof.
  unfold YL, X.
  follow BL_011011_1.
  fold YL X.
  follow BL_groups.
  finish.
Qed.

Definition Bnd a r :=
  0inf <{{C}} [1;1] *> [0;0;1;1]^^a *> r.

(* A left-boundary return has one fixed launcher and closer.  The only
   machine-specific work in between is therefore a local F-right/B1-left
   rule for the first nontransparent suffix. *)
Lemma Bnd_start a r:
  Bnd a r -->*
  (0 >> 1 >> 1 >> 0inf) {{F}}> [0;0;1;1]^^a *> r.
Proof.
  unfold Bnd.
  do 3 step1.
  finish.
Qed.

Lemma Bnd_launch a r:
  Bnd a r -->*
  (0 >> 1 >> 1 >> 0inf) <* [0;1;1;0]^^a {{F}}> r.
Proof.
  follow Bnd_start.
  follow FR_0011.
  finish.
Qed.

Lemma Bnd_close0 r:
  (0 >> 1 >> 1 >> 0inf) <{{B}} [1] *> r -->*
  0inf <{{C}} [1;1;0;0;1;1] *> r.
Proof. es' & r. Qed.

Lemma Bnd_close a r:
  (0 >> 1 >> 1 >> 0inf) <{{B}} [1] *>
    [0;0;1;1]^^a *> r -->*
  Bnd (S a) r.
Proof.
  follow Bnd_close0.
  cbn [Bnd].
  finish.
Qed.










Lemma local_delete_one0 l r:
  l {{F}}> [0;1] *> r -->*
  l <{{B}} [1;0] *> r.
Proof. es' & l r. Qed.

Lemma local_delete_one p l r:
  l {{F}}> [1]^^p *> [0;1] *> r -->*
  l <{{B}} [1] *> [1]^^p *> [0] *> r.
Proof.
  gen l.
  induction p as [|p IH]; intros l; cbn.
  - apply local_delete_one0.
  - step1.
    follow IH.
    step1.
    finish.
Qed.





Lemma local_minor1_start l r:
  l {{F}}> [1;0] *> X *> r -->*
  l <* [1;1;1;1;1;1;0;1] {{F}}> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor1_turn l r:
  l {{F}}> [1;1;1;0;1] *> X *> r -->*
  l <{{B}} [1] *> [1;1;1;0] *> X *> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor1_finish0 l r:
  l <* YL <* [1;1;1;1;1;1;0;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X *> [0] *> [1]^^7 *> r.
Proof. unfold X, YL; es' & l r. Qed.

Lemma local_minor1_finish s l r:
  l <* YL^^(S s) <* [1;1;1;1;1;1;0;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [0] *> [1]^^7 *> r.
Proof.
  cbn.
  follow local_minor1_finish0.
  follow BL_011011_1.
  fold X.
  rewrite lpow_shift'.
  cbn.
  finish.
Qed.

Lemma local_minor1 s n l r:
  l {{F}}> X^^(S s) *> [1;0] *> X^^(S n) *>
    [1;1;1;0;1] *> X *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [0] *> [1]^^7 *> X^^n *>
    [1;1;1;0] *> X *> r.
Proof.
  follow FR_001111.
  follow local_minor1_start.
  follow FR_001111.
  follow local_minor1_turn.
  follow BL_011011_1.
  apply local_minor1_finish.
Qed.

Lemma local_minor2_start l r:
  l {{F}}> [1;1;0] *> X *> r -->*
  l <* [1;1;1;1;1;1;0;1;1] {{F}}> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor2_turn l r:
  l {{F}}> [1;1;1;0;1;1] *> X *> r -->*
  l <{{B}} [1] *> [1;1;1;0;1] *> X *> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor2_finish0 l r:
  l <* YL <* [1;1;1;1;1;1;0;1;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X *> [1;0] *> [1]^^7 *> r.
Proof. unfold X, YL; es' & l r. Qed.

Lemma local_minor2_finish s l r:
  l <* YL^^(S s) <* [1;1;1;1;1;1;0;1;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [1;0] *> [1]^^7 *> r.
Proof.
  cbn.
  follow local_minor2_finish0.
  follow BL_011011_1.
  fold X.
  rewrite lpow_shift'.
  cbn.
  finish.
Qed.

Lemma local_minor2 s n l r:
  l {{F}}> X^^(S s) *> [1;1;0] *> X^^(S n) *>
    [1;1;1;0;1;1] *> X *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [1;0] *> [1]^^7 *> X^^n *>
    [1;1;1;0;1] *> X *> r.
Proof.
  follow FR_001111.
  follow local_minor2_start.
  follow FR_001111.
  follow local_minor2_turn.
  follow BL_011011_1.
  apply local_minor2_finish.
Qed.

Lemma local_minor3_start l r:
  l {{F}}> [1;1;1;0] *> X *> r -->*
  l <* [1;1;1;1;1;1;0;1;1;1] {{F}}> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor3_turn l r:
  l {{F}}> [1;1;1;0;1;1;1] *> X *> r -->*
  l <{{B}} [1] *> [1;1;1;0;1;1] *> X *> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_minor3_finish0 l r:
  l <* YL <* [1;1;1;1;1;1;0;1;1;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X *> [1;1;0] *> [1]^^7 *> r.
Proof. unfold X, YL; es' & l r. Qed.

Lemma local_minor3_finish s l r:
  l <* YL^^(S s) <* [1;1;1;1;1;1;0;1;1;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [1;1;0] *> [1]^^7 *> r.
Proof.
  cbn.
  follow local_minor3_finish0.
  follow BL_011011_1.
  fold X.
  rewrite lpow_shift'.
  cbn.
  finish.
Qed.

Lemma local_minor3 s n l r:
  l {{F}}> X^^(S s) *> [1;1;1;0] *> X^^(S n) *>
    [1;1;1;0;1;1;1] *> X *> r -->*
  l <{{B}} [1] *> X^^(S s) *> [1;1;0] *> [1]^^7 *> X^^n *>
    [1;1;1;0;1;1] *> X *> r.
Proof.
  follow FR_001111.
  follow local_minor3_start.
  follow FR_001111.
  follow local_minor3_turn.
  follow BL_011011_1.
  apply local_minor3_finish.
Qed.




(* The four one-return phases used by the 28-return transfer.  The first two
   keep the column boundary fixed; the last two move the final left column
   across the distinguished marker. *)


Lemma local_transfer3_start l r:
  l {{F}}> [0] *> X *> r -->*
  l <* [1;1;1;1;1;1;0] {{F}}> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_transfer3_turn l r:
  l <* [1;1;1;1;1;1;0] <{{B}} [1] *> r -->*
  l <{{C}} [1;1;1;1;1;1;1;1] *> r.
Proof. es' & l r. Qed.

Lemma local_transfer3_finish l r:
  l <* Sep <{{C}} [1;1;1;1] *> r -->*
  l <{{B}} [1] *> [1;1;1;0;1;1;1] *> r.
Proof. unfold Sep; es' & l r. Qed.


Lemma local_transfer4_start l r:
  l {{F}}> [1;1;1;0] *> X *> r -->*
  l <* [1;1;1;1;1;1;0;1;1;1] {{F}}> r.
Proof. unfold X; es' & l r. Qed.

Lemma local_transfer4_finish l r:
  l <* [1;1;1;1;1;1;0;1;1;1] <{{B}} [1] *> r -->*
  l <{{B}} [1] *> [1;1;0;1;1;1;1;1;1;1] *> r.
Proof. es' & l r. Qed.


(* One complete transfer is the literal schedule
   7 + 1 + 7 + 1 + 7 + 1 + 3 + 1.  The hypotheses that the displayed
   exponents have four and two successors are exactly the positivity guards
   used by the compressed simulator. *)

(* The next 28-return phase reaches the first recursive-node marker.  Its one
   nonstandard return reads exactly one terminal [YL] word; the remaining
   exponent is again a parameter. *)










(* The fifth recursive-frame phase reaches the right blank.  Each fixed
   interface below is constant size; the RLE runs between them are crossed by
   the shift/segment rules above. *)






(* Horizontal proof of one 28-return column phase. *)
Notation hF := ((F, nil) : DH0).
Notation hB := ((B, [1]) : DH0).
Notation h := ([((hF, hB) : DH0 * DH0)]).
Notation hC := ((C, [1;1;1;1]) : DH0).
Notation g := ([((hF, hC) : DH0 * DH0)]).

Ltac esc :=
  apply BoundedConfig.segRLs_c_spec with (T:=1000); reflexivity.

Lemma seg_delete7_0:
  segRLs tm (h^^7) [] ([0] ++ [1]^^7) [0].
Proof. esc. Qed.

Lemma seg_delete7_1:
  segRLs tm (h^^7) [] ([1;0] ++ [1]^^7) [1;0].
Proof. esc. Qed.

Lemma seg_delete7_2:
  segRLs tm (h^^7) [] ([1;1;0] ++ [1]^^7) [1;1;0].
Proof. esc. Qed.

Lemma seg_delete3_3:
  segRLs tm (h^^3) [] ([1;1;1;0] ++ [1]^^3) [1;1;1;0].
Proof. esc. Qed.

Lemma seg_0011:
  segRLs tm h h [0;0;1;1] [0;0;1;1].
Proof. esc. Qed.

Lemma seg_1:
  segRLs tm h h [1] [1].
Proof. esc. Qed.

Lemma seg_empty:
  segRLs tm h h [] [].
Proof. esc. Qed.

Lemma seg_1_pow n:
  segRLs tm h h ([1]^^n) ([1]^^n).
Proof.
  induction n as [|n IH]; cbn [lpow].
  - apply seg_empty.
  - eapply segRLs_concat; [apply seg_1|apply IH].
Qed.

Lemma seg_X:
  segRLs tm h h X X.
Proof.
  change (segRLs tm h h ([0;0;1;1] ++ [1]^^2)
    ([0;0;1;1] ++ [1]^^2)).
  eapply segRLs_concat; [apply seg_0011|apply seg_1_pow].
Qed.

Lemma seg_Sep:
  segRLs tm h h Sep Sep.
Proof.
  change (segRLs tm h h ([1]^^4) ([1]^^4)).
  apply seg_1_pow.
Qed.

Lemma seg_X_pow n:
  segRLs tm h h (X^^n) (X^^n).
Proof.
  induction n as [|n IH]; cbn [lpow].
  - apply seg_empty.
  - eapply segRLs_concat; [apply seg_X|apply IH].
Qed.

Fixpoint WGroups (ns : list nat) : list Sym :=
  match ns with
  | [] => []
  | n :: ns => X^^n ++ Sep ++ WGroups ns
  end.



Lemma seg_WGroups ns:
  segRLs tm h h (WGroups ns) (WGroups ns).
Proof.
  induction ns as [|n ns IH]; cbn [WGroups].
  - apply seg_empty.
  - eapply segRLs_concat; [apply seg_X_pow|].
    eapply segRLs_concat; [apply seg_Sep|apply IH].
Qed.

Lemma seg_prefix ns n:
  segRLs tm h h
    (WGroups ns ++ X^^n) (WGroups ns ++ X^^n).
Proof. eapply segRLs_concat; [apply seg_WGroups|apply seg_X_pow]. Qed.

Lemma seg_repeat k w:
  segRLs tm h h w w ->
  segRLs tm (h^^k) (h^^k) w w.
Proof.
  intro H.
  induction k as [|k IH]; cbn [lpow].
  - constructor.
  - eapply segRLs_trans; [apply H|apply IH].
Qed.

Lemma seg_prefix_repeat k ns n:
  segRLs tm (h^^k) (h^^k)
    (WGroups ns ++ X^^n) (WGroups ns ++ X^^n).
Proof. apply seg_repeat, seg_prefix. Qed.

Lemma seg_minor2:
  segRLs tm h h
    (X ++ [1;1;0] ++ X)
    (X ++ [1;0] ++ [1]^^7).
Proof. unfold X; esc. Qed.

Lemma seg_minor1:
  segRLs tm h h
    (X ++ [1;0] ++ X)
    (X ++ [0] ++ [1]^^7).
Proof. unfold X; esc. Qed.

Lemma seg_t3_left:
  segRLs tm h g Sep [1;1;1;0;1;1;1].
Proof. unfold Sep; esc. Qed.

Lemma seg_X_g:
  segRLs tm g g X X.
Proof. unfold X; esc. Qed.

Lemma seg_X_pow_g n:
  segRLs tm g g (X^^n) (X^^n).
Proof.
  induction n as [|n IH]; cbn [lpow].
  - esc.
  - eapply segRLs_concat; [apply seg_X_g|apply IH].
Qed.

Lemma seg_t3_right:
  segRLs tm g h ([0] ++ X) Sep.
Proof. unfold X, Sep; esc. Qed.

Lemma seg_t4:
  segRLs tm h h
    ([1;1;1;0] ++ X)
    [1;1;0;1;1;1;1;1;1;1].
Proof. unfold X; esc. Qed.

Definition M0 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [1;1;0] ++ [1]^^7 ++
    X ++ X^^(S (S (S r0))) ++ Sep.
Definition M1 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [1;1;0] ++
    X ++ X^^(S (S (S r0))) ++ Sep.
Definition M2 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [1;0] ++ [1]^^7 ++
    X^^(S (S (S r0))) ++ Sep.
Definition M3 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [1;0] ++
    X^^(S (S (S r0))) ++ Sep.
Definition M4 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [0] ++ [1]^^7 ++
    X^^(S (S r0)) ++ Sep.
Definition M5 x r0 :=
  Sep ++ X^^(S x) ++ X ++ [0] ++ X^^(S (S r0)) ++ Sep.
Definition M6 x r0 :=
  [1;1;1;0;1;1;1] ++ X^^(S x) ++ X ++ Sep ++
    X^^(S r0) ++ Sep.
Definition M7 x r0 :=
  [1;1;1;0] ++ X^^(S x) ++ X ++ Sep ++ X^^(S r0) ++ Sep.
Definition M8 x r0 :=
  [1;1;0;1;1;1;1;1;1;1] ++ X^^x ++ X ++ Sep ++
    X^^(S r0) ++ Sep.

Lemma seg_Sep_X n:
  segRLs tm h h (Sep ++ X^^n) (Sep ++ X^^n).
Proof. eapply segRLs_concat; [apply seg_Sep|apply seg_X_pow]. Qed.

Lemma seg_X_Sep n:
  segRLs tm h h (X^^n ++ Sep) (X^^n ++ Sep).
Proof. eapply segRLs_concat; [apply seg_X_pow|apply seg_Sep]. Qed.

Lemma seg_Sep_X_X n:
  segRLs tm h h (Sep ++ X^^n ++ X) (Sep ++ X^^n ++ X).
Proof.
  eapply (@segRLs_concat tm h h h
    (Sep ++ X^^n) (Sep ++ X^^n)); [apply seg_Sep_X|apply seg_X].
Qed.

Lemma seg_closed_suffix t {hs w1 w2}:
  segRLs tm hs [] w1 w2 ->
  segRLs tm hs [] (w1 ++ t) (w2 ++ t).
Proof. intro H; eapply segRLs_concat; [apply H|constructor]. Qed.

Lemma seg_main0 x r0:
  segRLs tm (h^^7) [] (M0 x r0) (M1 x r0).
Proof.
  unfold M0, M1.
  applys_eq (segRLs_concat
    (seg_repeat 7 _ (seg_Sep_X_X (S x)))
    (seg_closed_suffix (X ++ X^^(S (S (S r0))) ++ Sep)
      seg_delete7_2)).
  all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main1 x r0:
  segRLs tm h h (M1 x r0) (M2 x r0).
Proof.
  unfold M1, M2.
  applys_eq (segRLs_concat (seg_Sep_X (S x))
    (segRLs_concat seg_minor2 (seg_X_Sep (S (S (S r0)))))).
  all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main2 x r0:
  segRLs tm (h^^7) [] (M2 x r0) (M3 x r0).
Proof.
  unfold M2, M3.
  applys_eq (segRLs_concat
    (seg_repeat 7 _ (seg_Sep_X_X (S x)))
    (seg_closed_suffix (X^^(S (S (S r0))) ++ Sep) seg_delete7_1)).
  all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main3 x r0:
  segRLs tm h h (M3 x r0) (M4 x r0).
Proof.
  unfold M3, M4.
  applys_eq (segRLs_concat (seg_Sep_X (S x))
    (segRLs_concat seg_minor1 (seg_X_Sep (S (S r0))))).
  all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main4 x r0:
  segRLs tm (h^^7) [] (M4 x r0) (M5 x r0).
Proof.
  unfold M4, M5.
  applys_eq (segRLs_concat
    (seg_repeat 7 _ (seg_Sep_X_X (S x)))
    (seg_closed_suffix (X^^(S (S r0)) ++ Sep) seg_delete7_0)).
  all: repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main5 x r0:
  segRLs tm h h (M5 x r0) (M6 x r0).
Proof.
  unfold M5, M6.
  applys_eq (segRLs_concat seg_t3_left
    (segRLs_concat (seg_X_pow_g (S x))
      (segRLs_concat seg_X_g
        (segRLs_concat seg_t3_right (seg_X_Sep (S r0)))))).
  all: cbn [lpow]; repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main6 x r0:
  segRLs tm (h^^3) [] (M6 x r0) (M7 x r0).
Proof.
  unfold M6, M7.
  applys_eq (seg_closed_suffix
    (X^^(S x) ++ X ++ Sep ++ X^^(S r0) ++ Sep) seg_delete3_3).
  all: cbn [lpow]; repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main7 x r0:
  segRLs tm h h (M7 x r0) (M8 x r0).
Proof.
  unfold M7, M8.
  applys_eq (segRLs_concat seg_t4
    (segRLs_concat (seg_X_pow x)
      (segRLs_concat seg_X
        (segRLs_concat seg_Sep (seg_X_Sep (S r0)))))).
  all: cbn [lpow]; repeat rewrite app_assoc; reflexivity.
Qed.

Lemma seg_main28 x r0:
  segRLs tm (h^^28) (h^^4) (M0 x r0) (M8 x r0).
Proof.
  applys_eq (segRLs_trans (seg_main0 x r0)
    (segRLs_trans (seg_main1 x r0)
      (segRLs_trans (seg_main2 x r0)
        (segRLs_trans (seg_main3 x r0)
          (segRLs_trans (seg_main4 x r0)
            (segRLs_trans (seg_main5 x r0)
              (segRLs_trans (seg_main6 x r0) (seg_main7 x r0)))))))).
  all: cbn [lpow]; reflexivity.
Qed.

(* One complete horizontal phase of the main counter.  [Core] deliberately
   hides all intermediate scans: seven adjacent local columns consume 196
   incoming signals and expose only the 28 signals sent to the right suffix. *)
Definition Core (ls : list nat) y (rs : list nat) :=
  WGroups ls ++ X^^y ++ ([1;1;0] ++ [1]^^7) ++ WGroups rs.

Definition GSnoc (ns : list nat) n := ns ++ [n].

Lemma WGroups_app ns ms:
  WGroups (ns ++ ms) = WGroups ns ++ WGroups ms.
Proof.
  induction ns as [|n ns IH]; [reflexivity|].
  change (X^^n ++ Sep ++ WGroups (ns ++ ms) =
    (X^^n ++ Sep ++ WGroups ns) ++ WGroups ms).
  rewrite IH. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma lpow_S_right n: X^^(S n) = X^^n ++ X.
Proof. cbn [lpow]. symmetry; apply lpow_shift. Qed.

Lemma lpow_shift_prefix pre n:
  (pre ++ X^^n) ++ X = (pre ++ X) ++ X^^n.
Proof.
  rewrite <- app_assoc, lpow_shift, app_assoc; reflexivity.
Qed.

Lemma lpow_unshift_prefix pre n:
  (pre ++ X) ++ X^^n = (pre ++ X^^n) ++ X.
Proof. symmetry; apply lpow_shift_prefix. Qed.

Lemma main_marker_eq:
  [1;1;0] ++ [1]^^7 = [1;1;0;1;1;1;1;1;1;1].
Proof. reflexivity. Qed.

Lemma main_marker_middle pre post:
  pre ++ [1;1;0] ++ [1]^^7 ++ post =
  pre ++ [1;1;0;1;1;1;1;1;1;1] ++ post.
Proof.
  induction pre as [|a pre IH].
  - change ([1;1;0] ++ [1]^^7 ++ post =
      [1;1;0;1;1;1;1;1;1;1] ++ post).
    rewrite app_assoc, main_marker_eq; reflexivity.
  - change (a :: (pre ++ [1;1;0] ++ [1]^^7 ++ post) =
      a :: (pre ++ [1;1;0;1;1;1;1;1;1;1] ++ post)).
    f_equal; apply IH.
Qed.

Lemma seg_core28 ls y x r0 rs:
  segRLs tm (h^^28) (h^^4)
    (Core (ls++[y]) (S (S x)) (S (S (S (S r0)))::rs))
    (Core ls y (S x::S r0::rs)).
Proof.
  applys_eq (segRLs_concat
    (segRLs_concat (seg_prefix_repeat 28 ls y) (seg_main28 x r0))
    (seg_repeat 4 _ (seg_WGroups rs))).
  all: unfold Core, M0, M8.
  all: try rewrite WGroups_app.
  all: repeat rewrite main_marker_middle.
  all: repeat rewrite main_marker_eq.
  all: autorewrite with tape_post.
  all: repeat rewrite lpow_S_right.
  all: cbn [WGroups lpow].
  all: autorewrite with tape_post.
  all: repeat rewrite app_assoc.
  all: repeat rewrite (lpow_shift_prefix _ r0).
  all: repeat rewrite (lpow_unshift_prefix _ x).
  all: repeat rewrite app_nil_r.
  all: reflexivity.
Qed.











Lemma Bnd_sideRLs1 a r1 r2:
  sideRLs tm h r1 r2 ->
  Bnd a r1 -->* Bnd (S a) r2.
Proof.
  intro H.
  follow Bnd_launch.
  eapply evstep_trans.
  1: apply progress_evstep, (sideRLs_1 tm hF hB r1 r2 H).
  follow BL_0110_1.
  apply Bnd_close.
Qed.

Lemma Bnd_sideRLs k a r1 r2:
  sideRLs tm (h^^k) r1 r2 ->
  Bnd a r1 -->* Bnd (k+a) r2.
Proof.
  gen a r1 r2.
  induction k as [|k IH]; intros a r1 r2 H.
  - cbn [lpow] in H; inverts H; finish.
  - change (sideRLs tm (h ++ h^^k) r1 r2) in H.
    destruct (sideRLs_split H) as [r3 [H1 H2]].
    follow (Bnd_sideRLs1 a r1 r3 H1).
    applys_eq (IH (S a) r3 r2 H2); flia.
Qed.

End TM101.

Module P := TM101PersistentSim.
Module T := TM101.


(* Logical meaning of the persistent executable representation.  No part of
   the evaluator ever materialises these lists: they occur only in proofs. *)
Definition sym_of_bool (b : bool) : Sym := if b then 1 else 0.

Definition word_bits (w : P.Word) : list Sym :=
  List.map sym_of_bool (P.spelling w).

Definition copies (w : list Sym) (n : N) : list Sym :=
  w^^(N.to_nat n).

Fixpoint count_bits (w : P.Word) (ns : list N) : list Sym :=
  match ns with
  | [] => []
  | [n] => copies (word_bits w) n
  | n :: ns' => copies (word_bits w) n ++ [1;1;1;1] ++ count_bits w ns'
  end.

Definition block_bits (b : P.Block) : list Sym :=
  match b with
  | P.Lit bits => List.map sym_of_bool bits
  | P.Run w n => copies (word_bits w) n
  | P.Chain w ns => count_bits w (P.ds_list ns)
  end.

Fixpoint side_bits (s : P.Side) : list Sym :=
  match s with
  | [] => []
  | b :: s' => block_bits b ++ side_bits s'
  end.

Definition denote_side (s : P.Side) : side := side_bits s *> 0inf.

Definition denote_q (q : P.Q) : state :=
  match q with
  | P.A => A | P.B => B | P.C => C
  | P.D => D | P.E => E | P.F => F
  end.

Definition denote_machine (m : P.Machine) : state * tape :=
  match P.m_dir m with
  | P.L => denote_side (P.m_left m) <{{ denote_q (P.m_state m) }}
             denote_side (P.m_right m)
  | P.R => denote_side (P.m_left m) {{ denote_q (P.m_state m) }}>
             denote_side (P.m_right m)
  end.

Definition valid_dseq (_ : P.DSeq) : Prop := True.

Definition positive_count (n : N) : Prop := (0 < n)%N.

Definition valid_block (b : P.Block) : Prop :=
  match b with
  | P.Lit bits => bits <> []
  | P.Run _ n => (0 < n)%N
  | P.Chain _ ns =>
      valid_dseq ns /\
      List.Forall positive_count (P.ds_list ns) /\
      1 <= P.ds_len ns
  end.

Definition valid_side (s : P.Side) : Prop := List.Forall valid_block s.

Definition valid_machine (m : P.Machine) : Prop :=
  valid_side (P.m_left m) /\ valid_side (P.m_right m).

Lemma denote_init : denote_machine P.init = c0.
Proof.
  cbn [denote_machine P.init P.machine denote_side side_bits c0
       tape0].
  repeat rewrite <- const_unfold.
  reflexivity.
Qed.

Lemma valid_init : valid_machine P.init.
Proof. cbn [valid_machine valid_side P.init P.machine]. repeat constructor. Qed.

Lemma ds_rebuild_list xs : P.ds_list (P.ds_rebuild xs) = xs.
Proof.
  unfold P.ds_rebuild, P.ds_list; cbn.
  rewrite rev_involutive, firstn_skipn. reflexivity.
Qed.

Lemma ds_rebuild_valid xs : valid_dseq (P.ds_rebuild xs).
Proof. exact I. Qed.



Lemma valid_dseq_len s :
  valid_dseq s -> P.ds_len s = length (P.ds_list s).
Proof.
  destruct s as [f b]. unfold P.ds_len, P.ds_list.
  cbn. intros _. rewrite length_app, rev_length. reflexivity.
Qed.

Lemma ds_uncons_ok s :
  match P.ds_uncons s with
  | None => P.ds_list s = []
  | Some (x,s') => P.ds_list s = x :: P.ds_list s'
  end.
Proof.
  destruct s as [[|x f] b].
  - unfold P.ds_uncons; cbn.
    destruct (rev b) as [|x xs] eqn:E.
    + reflexivity.
    + rewrite ds_rebuild_list. reflexivity.
  - reflexivity.
Qed.

Lemma ds_unsnoc_ok s :
  match P.ds_unsnoc s with
  | None => P.ds_list s = []
  | Some (s',x) => P.ds_list s = P.ds_list s' ++ [x]
  end.
Proof.
  destruct s as [f [|x b]].
  - unfold P.ds_unsnoc; cbn.
    destruct (rev f) as [|x xs] eqn:E.
    + apply (f_equal (@rev N)) in E.
      rewrite rev_involutive in E. subst f. reflexivity.
    + rewrite ds_rebuild_list.
      apply (f_equal (@rev N)) in E.
      rewrite rev_involutive in E. subst f. cbn. rewrite app_nil_r.
      reflexivity.
  - unfold P.ds_unsnoc, P.ds_list; cbn.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma ds_list_cons x s :
  P.ds_list (P.ds_cons x s) = x :: P.ds_list s.
Proof. destruct s. reflexivity. Qed.





Lemma ds_list_rev s :
  P.ds_list (P.ds_rev s) = rev (P.ds_list s).
Proof.
  destruct s as [f b]. unfold P.ds_rev, P.ds_list; cbn.
  rewrite rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma ds_list_of_list xs : P.ds_list (P.ds_of_list xs) = xs.
Proof. apply ds_rebuild_list. Qed.

Lemma ds_cons_valid x s : valid_dseq s -> valid_dseq (P.ds_cons x s).
Proof. intros. exact I. Qed.



Lemma ds_rev_valid s : valid_dseq s -> valid_dseq (P.ds_rev s).
Proof. intros. exact I. Qed.

Lemma ds_uncons_valid s x s' :
  valid_dseq s -> P.ds_uncons s = Some (x,s') -> valid_dseq s'.
Proof.
  intros. exact I.
Qed.

Lemma ds_unsnoc_valid s s' x :
  valid_dseq s -> P.ds_unsnoc s = Some (s',x) -> valid_dseq s'.
Proof.
  intros. exact I.
Qed.










Lemma word_eqb_eq x y : P.word_eqb x y = true -> x = y.
Proof. destruct x, y; cbn; congruence. Qed.


Lemma copies_add w n m :
  copies w (n+m)%N = copies w n ++ copies w m.
Proof.
  unfold copies. rewrite N2Nat.inj_add, lpow_add. reflexivity.
Qed.

Lemma side_bits_push_lit bits s :
  side_bits (P.push_lit bits s) =
  List.map sym_of_bool bits ++ side_bits s.
Proof.
  destruct bits as [|b bits]; cbn [P.push_lit side_bits].
  - reflexivity.
  - destruct s as [|block s].
    + reflexivity.
    + destruct block; cbn [P.push_lit side_bits block_bits];
        rewrite ?map_app, ?app_assoc; reflexivity.
Qed.

Lemma side_bits_push_bit bit s :
  side_bits (P.push_bit bit s) = sym_of_bool bit :: side_bits s.
Proof.
  destruct s as [|block s].
  - reflexivity.
  - destruct block; cbn [P.push_bit side_bits block_bits]; reflexivity.
Qed.

Lemma side_bits_push_run w n s :
  side_bits (P.push_run w n s) = copies (word_bits w) n ++ side_bits s.
Proof.
  unfold P.push_run, NCount.is_zero.
  cbn [N.of_nat].
  destruct (N.eqb n 0) eqn:Hn.
  - apply N.eqb_eq in Hn. subst. reflexivity.
  - destruct s as [|block s].
    + reflexivity.
    + destruct block as [bits|w' n'|w' ns]; cbn [side_bits block_bits].
      * reflexivity.
      * destruct (P.word_eqb w w') eqn:Hw.
        -- apply word_eqb_eq in Hw. subst w'.
           change (copies (word_bits w) (n+n')%N ++ side_bits s =
             copies (word_bits w) n ++ copies (word_bits w) n' ++
               side_bits s).
           rewrite copies_add, app_assoc.
           reflexivity.
        -- reflexivity.
      * reflexivity.
Qed.


Lemma valid_push_lit bits s :
  valid_side s -> valid_side (P.push_lit bits s).
Proof.
  intros Hs. destruct bits as [|b bits]; cbn [P.push_lit]; auto.
  inversion Hs as [|block s' Hb Hs']; subst.
  - constructor; [discriminate|constructor].
  - destruct block as [more|w n|w ns]; cbn [P.push_lit valid_block].
    + constructor; [discriminate|exact Hs'].
    + constructor; [discriminate|constructor; assumption].
    + constructor; [discriminate|constructor; assumption].
Qed.

Lemma valid_push_bit bit s :
  valid_side s -> valid_side (P.push_bit bit s).
Proof.
  intro Hs. inversion Hs as [|block s' Hb Hs']; subst.
  - cbn [P.push_bit valid_side valid_block]. repeat constructor. discriminate.
  - destruct block; cbn [P.push_bit valid_side valid_block];
      constructor; auto; discriminate.
Qed.

Lemma valid_push_run w n s :
  valid_side s -> valid_side (P.push_run w n s).
Proof.
  intro Hs.
  unfold P.push_run, NCount.is_zero. cbn.
  destruct (N.eqb n 0) eqn:Hn; auto.
  assert (Hpos : (0 < n)%N) by
    (apply N.neq_0_lt_0; intro; subst; discriminate).
  inversion Hs as [|block s' Hb Hs']; subst.
  - constructor; [exact Hpos|constructor].
  - destruct block as [bits|w' n'|w' ns]; cbn [valid_block].
    + constructor; auto.
    + destruct (P.word_eqb w w').
      * constructor; [apply N.add_pos_l; exact Hpos|exact Hs'].
      * constructor; auto.
    + constructor; auto.
Qed.

Lemma valid_push_chain w ns s :
  valid_dseq ns -> List.Forall positive_count (P.ds_list ns) ->
  1 <= P.ds_len ns -> valid_side s ->
  valid_side (P.push_chain w ns s).
Proof. intros. constructor; cbn [valid_block]; auto. Qed.



Lemma ds_singleton_some s n :
  P.ds_singleton s = Some n -> P.ds_list s = [n].
Proof.
  destruct s as [[|x [|y f]] [|z [|u b]]]; cbn
    [P.ds_singleton P.ds_list]; try discriminate; intro E;
    inversion E; reflexivity.
Qed.

Lemma ds_nonempty_false s :
  P.ds_nonempty s = false -> P.ds_list s = [].
Proof.
  destruct s as [[|x f] [|y b]]; cbn [P.ds_nonempty];
    intro H; try discriminate; reflexivity.
Qed.

Lemma ds_nonempty_len s :
  P.ds_nonempty s = true -> 1 <= P.ds_len s.
Proof.
  destruct s as [[|x f] [|y b]]; cbn [P.ds_nonempty];
    intro H; try discriminate; unfold P.ds_len; cbn; lia.
Qed.

Lemma ds_at_least_two_spec s :
  P.ds_at_least_two s = true <-> 2 <= P.ds_len s.
Proof.
  destruct s as [f b].
  destruct f as [|x [|y f]]; destruct b as [|z [|u b]];
    unfold P.ds_at_least_two, P.ds_len; cbn;
    split; intro H; try reflexivity; try discriminate; lia.
Qed.

Lemma side_bits_push_sequence w ns s :
  valid_dseq ns ->
  side_bits (P.push_sequence w ns s) =
    count_bits w (P.ds_list ns) ++ side_bits s.
Proof.
  intro Hvalid. unfold P.push_sequence.
  destruct (P.ds_singleton ns) as [n|] eqn:Hsingle.
  - rewrite (ds_singleton_some ns n Hsingle).
    cbn [P.one_sequence count_bits]. apply side_bits_push_run.
  - destruct (P.ds_nonempty ns) eqn:Hnonempty.
    + reflexivity.
    + rewrite (ds_nonempty_false ns Hnonempty). reflexivity.
Qed.

Lemma valid_push_sequence w ns s :
  valid_dseq ns -> List.Forall positive_count (P.ds_list ns) ->
  valid_side s -> valid_side (P.push_sequence w ns s).
Proof.
  intros Hvalid Hpos Hs. unfold P.push_sequence.
  destruct (P.ds_singleton ns) as [n|] eqn:Hsingle.
  - apply valid_push_run; exact Hs.
  - destruct (P.ds_nonempty ns) eqn:Hnonempty.
    + apply valid_push_chain; auto using ds_nonempty_len.
    + exact Hs.
Qed.

Lemma chain_expose_same w ns s :
  side_bits (P.chain_expose w ns s) =
  count_bits w (P.ds_list ns) ++ side_bits s.
Proof.
  unfold P.chain_expose.
  destruct (P.ds_uncons ns) as [[n rest]|] eqn:E1.
  - pose proof (ds_uncons_ok ns) as H1. rewrite E1 in H1.
    destruct (P.ds_uncons rest) as [[m rest']|] eqn:E2.
    + pose proof (ds_uncons_ok rest) as H2. rewrite E2 in H2.
      rewrite side_bits_push_run, H1.
      cbn [side_bits block_bits count_bits]. rewrite H2.
      unfold P.sep.
      change (List.map sym_of_bool [true;true;true;true]) with [1;1;1;1].
      cbn [count_bits].
      repeat rewrite app_assoc. reflexivity.
    + pose proof (ds_uncons_ok rest) as H2. rewrite E2 in H2.
      rewrite side_bits_push_run, H1.
      cbn [side_bits block_bits count_bits]. rewrite H2. reflexivity.
  - pose proof (ds_uncons_ok ns) as H1. rewrite E1 in H1.
    rewrite H1. reflexivity.
Qed.

Lemma copies_succ_pred w n :
  (0 < n)%N ->
  copies w n = w ++ copies w (N.pred n).
Proof.
  intro Hn. rewrite <- (N.succ_pred n) at 1 by lia.
  rewrite <- N.add_1_l, copies_add.
  replace (copies w 1%N) with w; [reflexivity|].
  unfold copies. change (w = w ++ []). symmetry. apply app_nil_r.
Qed.

Lemma pop_run_bits fuel w n s :
  (0 < n)%N ->
  let '(b,s') := P.pop_bit_fuel (S fuel) (P.Run w n :: s) in
  side_bits (P.Run w n :: s) = sym_of_bool b :: side_bits s'.
Proof.
  intro Hn. destruct w;
    cbn [P.pop_bit_fuel P.spelling side_bits block_bits word_bits];
    rewrite side_bits_push_lit, side_bits_push_run,
      (copies_succ_pred _ _ Hn);
    reflexivity.
Qed.

Lemma pop_push_run_bits fuel w n s :
  (0 < n)%N ->
  let '(b,s') := P.pop_bit_fuel (S fuel) (P.push_run w n s) in
  side_bits (P.push_run w n s) = sym_of_bool b :: side_bits s'.
Proof.
  intro Hn. unfold P.push_run, NCount.is_zero.
  cbn [N.of_nat].
  destruct (N.eqb n 0) eqn:Ez.
  { apply N.eqb_eq in Ez. lia. }
  destruct s as [|block tail].
  - apply pop_run_bits. exact Hn.
  - destruct block as [bits|w' n'|w' ns].
    + apply pop_run_bits. exact Hn.
    + destruct (P.word_eqb w w').
      * apply pop_run_bits. unfold NCount.add. lia.
      * apply pop_run_bits. exact Hn.
    + apply pop_run_bits. exact Hn.
Qed.

Lemma ds_uncons_forall {A : N -> Prop} s x s' :
  List.Forall A (P.ds_list s) ->
  P.ds_uncons s = Some (x,s') ->
  A x /\ List.Forall A (P.ds_list s').
Proof.
  intros Hall E. pose proof (ds_uncons_ok s) as Hlist.
  rewrite E in Hlist. rewrite Hlist in Hall. inversion Hall; auto.
Qed.

Lemma pop_bit_bits_nonempty s :
  valid_side s -> s <> [] ->
  let '(b,s') := P.pop_bit s in
  side_bits s = sym_of_bool b :: side_bits s'.
Proof.
  intros Hvalid Hnonempty. destruct s as [|block tail]; [contradiction|].
  inversion Hvalid as [|? ? Hblock Htail]; subst.
  destruct block as [bits|w n|w ns].
  - destruct bits as [|b bits]; [contradiction|].
    destruct bits; reflexivity.
  - apply pop_run_bits. exact Hblock.
  - destruct Hblock as [Hds [Hpos Hlen]].
    assert (Hsame : side_bits (P.Chain w ns :: tail) =
      side_bits (P.chain_expose w ns tail)).
    { cbn [side_bits block_bits]. symmetry. apply chain_expose_same. }
    destruct (P.ds_uncons ns) as [[n rest]|] eqn:E1.
    + pose proof (ds_uncons_forall ns n rest Hpos E1) as [Hn _].
      destruct (P.ds_uncons rest) as [[m rest']|] eqn:E2;
        unfold P.pop_bit;
        change (let '(b,s') :=
          P.pop_bit_fuel 3 (P.chain_expose w ns tail) in
          side_bits (P.Chain w ns :: tail) =
            sym_of_bool b :: side_bits s');
        rewrite Hsame;
        unfold P.chain_expose; rewrite E1, E2;
        apply pop_push_run_bits; exact Hn.
    + pose proof (ds_uncons_ok ns) as Hlist. rewrite E1 in Hlist.
      pose proof (valid_dseq_len ns Hds) as Hlength.
      rewrite Hlist in Hlength. cbn in Hlength.
      rewrite Hlength in Hlen. inversion Hlen.
Qed.

Lemma pop_bit_same s :
  valid_side s ->
  let '(b,s') := P.pop_bit s in
  denote_side s = sym_of_bool b >> denote_side s'.
Proof.
  intro Hvalid. destruct s as [|block tail].
  - cbn [P.pop_bit P.pop_bit_fuel denote_side side_bits sym_of_bool].
    rewrite <- const_unfold. reflexivity.
  - destruct (P.pop_bit (block::tail)) as [b s'] eqn:E.
    pose proof (pop_bit_bits_nonempty (block::tail) Hvalid
      (ltac:(discriminate))) as Hbits.
    rewrite E in Hbits. unfold denote_side. rewrite Hbits. reflexivity.
Qed.

Lemma raw_step_sound m m' :
  valid_machine m -> P.raw_step m = Some m' ->
  denote_machine m -[ tm ]->* denote_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hstep. destruct d.
  - destruct (P.pop_bit l) as [bit l'] eqn:Epop.
    pose proof (pop_bit_same l Hl) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,l')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep.
    rewrite Epop0 in Hstep. cbn [P.active] in Hstep.
    destruct q, bit; cbn [P.trans] in Hstep; try discriminate;
      inversion Hstep; subst; clear Hstep;
      unfold denote_machine;
      cbv delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
        iota zeta;
      cbn [denote_q]; unfold denote_side in Hpop |- *; rewrite Hpop;
      rewrite side_bits_push_bit; step1; finish.
  - destruct (P.pop_bit r) as [bit r'] eqn:Epop.
    pose proof (pop_bit_same r Hr) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,r')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep.
    rewrite Epop0 in Hstep. cbn [P.active] in Hstep.
    destruct q, bit; cbn [P.trans] in Hstep; try discriminate;
      inversion Hstep; subst; clear Hstep;
      unfold denote_machine;
      cbv delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
        iota zeta;
      cbn [denote_q];
      unfold denote_side in Hpop |- *; rewrite Hpop;
      rewrite side_bits_push_bit; step1; finish.
Qed.

Lemma pop_run_valid fuel w n s :
  valid_side s ->
  let '(_,s') := P.pop_bit_fuel (S fuel) (P.Run w n :: s) in
  valid_side s'.
Proof.
  intro Hs. destruct w;
    cbn [P.pop_bit_fuel P.spelling];
    apply valid_push_lit, valid_push_run; exact Hs.
Qed.

Lemma pop_push_run_valid fuel w n s :
  (0 < n)%N -> valid_side s ->
  let '(_,s') := P.pop_bit_fuel (S fuel) (P.push_run w n s) in
  valid_side s'.
Proof.
  intros Hn Hs. unfold P.push_run, NCount.is_zero.
  cbn [N.of_nat].
  destruct (N.eqb n 0) eqn:Ez.
  { apply N.eqb_eq in Ez. lia. }
  destruct s as [|block tail].
  - apply pop_run_valid. constructor.
  - inversion Hs as [|? ? Hblock Htail]; subst.
    destruct block as [bits|w' n'|w' ns].
    + apply pop_run_valid. constructor; assumption.
    + destruct (P.word_eqb w w').
      * apply pop_run_valid. exact Htail.
      * apply pop_run_valid. constructor; assumption.
    + apply pop_run_valid. constructor; assumption.
Qed.


Lemma pop_bit_valid s :
  valid_side s ->
  let '(_,s') := P.pop_bit s in valid_side s'.
Proof.
  intro Hvalid. destruct s as [|block tail].
  - constructor.
  - inversion Hvalid as [|? ? Hblock Htail]; subst.
    destruct block as [bits|w n|w ns].
    + destruct bits as [|b bits]; [contradiction|].
      destruct bits; assumption || (constructor; [discriminate|assumption]).
    + apply pop_run_valid. exact Htail.
    + destruct Hblock as [Hds [Hpos Hlen]].
      destruct (P.ds_uncons ns) as [[n rest]|] eqn:E1.
      * pose proof (ds_uncons_forall ns n rest Hpos E1) as [Hn _].
        destruct (P.ds_uncons rest) as [[m rest']|] eqn:E2.
        -- unfold P.pop_bit;
          change (let '(_,s') :=
            P.pop_bit_fuel 3 (P.chain_expose w ns tail) in valid_side s');
          unfold P.chain_expose; rewrite E1, E2;
          apply pop_push_run_valid; [exact Hn|].
           constructor; [discriminate|]. constructor.
           ++ change (valid_dseq rest /\
                List.Forall positive_count (P.ds_list rest) /\
                1 <= P.ds_len rest).
              split.
              ** apply ds_uncons_valid with (s:=ns) (x:=n); assumption.
              ** split.
                 --- exact (proj2 (ds_uncons_forall ns n rest Hpos E1)).
                 --- pose proof (ds_uncons_ok rest) as Hlist.
                     rewrite E2 in Hlist.
                     pose proof (ds_uncons_valid ns n rest Hds E1) as Hrvalid.
                     pose proof (valid_dseq_len rest Hrvalid) as Hlength.
                     rewrite Hlist in Hlength. rewrite Hlength. cbn. lia.
           ++ exact Htail.
        -- unfold P.pop_bit;
           change (let '(_,s') :=
             P.pop_bit_fuel 3 (P.chain_expose w ns tail) in valid_side s');
           unfold P.chain_expose; rewrite E1, E2;
           apply pop_push_run_valid; [exact Hn|exact Htail].
      * pose proof (ds_uncons_ok ns) as Hlist. rewrite E1 in Hlist.
        pose proof (valid_dseq_len ns Hds) as Hlength.
        rewrite Hlist in Hlength. cbn in Hlength.
        rewrite Hlength in Hlen. inversion Hlen.
Qed.

Lemma raw_step_valid m m' :
  valid_machine m -> P.raw_step m = Some m' -> valid_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hstep. destruct d.
  - destruct (P.pop_bit l) as [bit l'] eqn:Epop.
    pose proof (pop_bit_valid l Hl) as Hl'. rewrite Epop in Hl'.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,l')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep. rewrite Epop0 in Hstep.
    cbn [P.active] in Hstep. destruct q, bit; cbn [P.trans] in Hstep;
      try discriminate; inversion Hstep; subst; unfold valid_machine;
      cbv delta [P.machine P.m_left P.m_right] iota zeta;
      auto using valid_push_bit.
  - destruct (P.pop_bit r) as [bit r'] eqn:Epop.
    pose proof (pop_bit_valid r Hr) as Hr'. rewrite Epop in Hr'.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,r')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep. rewrite Epop0 in Hstep.
    cbn [P.active] in Hstep. destruct q, bit; cbn [P.trans] in Hstep;
      try discriminate; inversion Hstep; subst; unfold valid_machine;
      cbv delta [P.machine P.m_left P.m_right] iota zeta;
      auto using valid_push_bit.
Qed.

Lemma strip_bits_same bits s s' :
  valid_side s -> P.strip_bits bits s = Some s' ->
  denote_side s = List.map sym_of_bool bits *> denote_side s'.
Proof.
  revert s s'. induction bits as [|b bits IH]; intros s s' Hvalid E.
  - cbn [P.strip_bits] in E. inversion E; subst. reflexivity.
  - cbn [P.strip_bits] in E.
    destruct (P.pop_bit s) as [b' rest] eqn:Epop.
    destruct (Bool.eqb b b') eqn:Eb; [|discriminate].
    pose proof (Bool.eqb_prop _ _ Eb) as Heq. subst b'.
    pose proof (pop_bit_same s Hvalid) as Hpop. rewrite Epop in Hpop.
    pose proof (pop_bit_valid s Hvalid) as Hrest. rewrite Epop in Hrest.
    specialize (IH rest s' Hrest E). rewrite Hpop, IH. reflexivity.
Qed.

Lemma strip_bits_valid bits s s' :
  valid_side s -> P.strip_bits bits s = Some s' -> valid_side s'.
Proof.
  revert s s'. induction bits as [|b bits IH]; intros s s' Hvalid E.
  - cbn [P.strip_bits] in E. inversion E; subst. exact Hvalid.
  - cbn [P.strip_bits] in E.
    destruct (P.pop_bit s) as [b' rest] eqn:Epop.
    destruct (Bool.eqb b b'); [|discriminate].
    apply IH with (s:=rest); [|exact E].
    pose proof (pop_bit_valid s Hvalid) as Hrest. rewrite Epop in Hrest.
    exact Hrest.
Qed.

Lemma strip_prefix_some needle haystack rest :
  P.strip_prefix needle haystack = Some rest ->
  haystack = needle ++ rest.
Proof.
  revert haystack rest. induction needle as [|x xs IH].
  - intros haystack rest E. cbn [P.strip_prefix] in E.
    inversion E; subst. reflexivity.
  - intros [|y ys] rest E; cbn [P.strip_prefix] in E; [discriminate|].
    destruct (Bool.eqb x y) eqn:Exy; [|discriminate].
    destruct x, y; cbn in Exy; try discriminate;
      cbn; f_equal; apply IH; exact E.
Qed.

Lemma consume_lit_fuel_some fuel word bits k rest :
  P.consume_lit_fuel fuel word bits = (k,rest) ->
  bits = word^^k ++ rest.
Proof.
  revert bits k rest. induction fuel as [|fuel IH]; intros bits k rest E.
  - cbn [P.consume_lit_fuel] in E. inversion E; subst. reflexivity.
  - cbn [P.consume_lit_fuel] in E.
    destruct (P.strip_prefix word bits) as [bits'|] eqn:Epre.
    + destruct (P.consume_lit_fuel fuel word bits') as [k' rest'] eqn:Erec.
      inversion E; subst k rest'.
      pose proof (strip_prefix_some word bits bits' Epre) as ->.
      pose proof (IH bits' k' rest Erec) as ->.
      cbn [lpow]. repeat rewrite app_assoc. reflexivity.
    + inversion E; subst. reflexivity.
Qed.

Lemma consume_lit_some word bits k rest :
  P.consume_lit word bits = (k,rest) -> bits = word^^k ++ rest.
Proof. unfold P.consume_lit. apply consume_lit_fuel_some. Qed.

Lemma map_lpow {A B0} (f : A -> B0) xs n :
  List.map f (xs^^n) = (List.map f xs)^^n.
Proof.
  induction n as [|n IH]; cbn [lpow]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

Lemma copies_of_nat w n : copies w (N.of_nat n) = w^^n.
Proof. unfold copies. rewrite Nat2N.id. reflexivity. Qed.

Lemma expose_chain_after_first_same w ns s :
  let '(n,s') := P.expose_chain_after_first w ns s in
  side_bits (P.Chain w ns :: s) =
    copies (word_bits w) n ++ side_bits s'.
Proof.
  unfold P.expose_chain_after_first.
  destruct (P.ds_uncons ns) as [[n rest]|] eqn:E1.
  - pose proof (ds_uncons_ok ns) as H1. rewrite E1 in H1.
    destruct (P.ds_uncons rest) as [[m rest']|] eqn:E2.
    + pose proof (ds_uncons_ok rest) as H2. rewrite E2 in H2.
      cbn [side_bits block_bits count_bits]. rewrite H1, H2.
      unfold P.sep.
      change (List.map sym_of_bool [true;true;true;true]) with [1;1;1;1].
      cbn [count_bits]. repeat rewrite app_assoc. reflexivity.
    + pose proof (ds_uncons_ok rest) as H2. rewrite E2 in H2.
      cbn [side_bits block_bits count_bits]. rewrite H1, H2. reflexivity.
  - pose proof (ds_uncons_ok ns) as H1. rewrite E1 in H1.
    cbn [side_bits block_bits]. rewrite H1. reflexivity.
Qed.

Lemma expose_chain_after_first_valid w ns s :
  valid_dseq ns ->
  List.Forall positive_count (P.ds_list ns) ->
  1 <= P.ds_len ns -> valid_side s ->
  let '(n,s') := P.expose_chain_after_first w ns s in
  positive_count n /\ valid_side s'.
Proof.
  intros Hds Hpos Hlen Hs. unfold P.expose_chain_after_first.
  destruct (P.ds_uncons ns) as [[n rest]|] eqn:E1.
  - pose proof (ds_uncons_forall ns n rest Hpos E1) as [Hn Hrestpos].
    pose proof (ds_uncons_valid ns n rest Hds E1) as Hrestvalid.
    destruct (P.ds_uncons rest) as [[m rest']|] eqn:E2.
    + split; [exact Hn|]. constructor; [discriminate|]. constructor.
      * change (valid_dseq rest /\
          List.Forall positive_count (P.ds_list rest) /\
          1 <= P.ds_len rest). split; [exact Hrestvalid|].
        split; [exact Hrestpos|].
        pose proof (ds_uncons_ok rest) as Hlist. rewrite E2 in Hlist.
        pose proof (valid_dseq_len rest Hrestvalid) as Hlength.
        rewrite Hlist in Hlength. rewrite Hlength. cbn. lia.
      * exact Hs.
    + split; [exact Hn|exact Hs].
  - pose proof (ds_uncons_ok ns) as Hlist. rewrite E1 in Hlist.
    pose proof (valid_dseq_len ns Hds) as Hlength.
    rewrite Hlist in Hlength. cbn in Hlength.
    rewrite Hlength in Hlen. inversion Hlen.
Qed.

Lemma side_bits_lit_remainder bits s :
  side_bits (match bits with [] => s | _ => P.Lit bits :: s end) =
  List.map sym_of_bool bits ++ side_bits s.
Proof. destruct bits; reflexivity. Qed.

Lemma valid_lit_remainder bits s :
  valid_side s ->
  valid_side (match bits with [] => s | _ => P.Lit bits :: s end).
Proof.
  intro Hs. destruct bits; [exact Hs|]. constructor; [discriminate|exact Hs].
Qed.

Lemma consume_word_fuel_spec fuel w s :
  valid_side s ->
  let '(n,s') := P.consume_word_fuel fuel w s in
  valid_side s' /\
  side_bits s = copies (word_bits w) n ++ side_bits s'.
Proof.
  revert s. induction fuel as [|fuel IH]; intro s; intro Hvalid.
  - cbn [P.consume_word_fuel]. split; [exact Hvalid|reflexivity].
  - destruct s as [|block tail].
    + cbn [P.consume_word_fuel]. split; [constructor|reflexivity].
    + inversion Hvalid as [|? ? Hblock Htail]; subst.
      destruct block as [bits|w' n|w' ns].
      * cbn [P.consume_word_fuel].
        destruct (P.consume_lit (P.spelling w) bits) as [k bits'] eqn:Econsume.
        pose proof (consume_lit_some (P.spelling w) bits k bits' Econsume)
          as Hbits.
        destruct k as [|k].
        -- split; [constructor; assumption|reflexivity].
        -- set (rem :=
             match bits' with [] => tail | _ => P.Lit bits' :: tail end).
           destruct (P.consume_word_fuel fuel w rem) as [n' s'] eqn:Erec.
           pose proof (valid_lit_remainder bits' tail Htail) as Hrem.
           pose proof (IH rem Hrem) as Hrec. rewrite Erec in Hrec.
           destruct Hrec as [Hs' Hrec]. subst rem.
           rewrite side_bits_lit_remainder in Hrec.
           split; [exact Hs'|].
           cbn [side_bits block_bits]. rewrite Hbits, map_app, map_lpow.
           change (List.map sym_of_bool (P.spelling w)) with (word_bits w).
           rewrite <- app_assoc, Hrec, copies_add,
             copies_of_nat.
           repeat rewrite app_assoc. reflexivity.
      * cbn [P.consume_word_fuel]. destruct (P.word_eqb w w') eqn:Ew.
        -- apply word_eqb_eq in Ew. subst w'.
           destruct (P.consume_word_fuel fuel w tail) as [m s'] eqn:Erec.
           pose proof (IH tail Htail) as Hrec. rewrite Erec in Hrec.
           destruct Hrec as [Hs' Hrec]. split; [exact Hs'|].
           cbn [side_bits block_bits]. rewrite Hrec, copies_add.
           repeat rewrite app_assoc. reflexivity.
        -- split; [constructor; assumption|reflexivity].
      * cbn [P.consume_word_fuel]. destruct (P.word_eqb w w') eqn:Ew.
        -- apply word_eqb_eq in Ew. subst w'.
           destruct Hblock as [Hds [Hpos Hlen]].
           destruct (P.expose_chain_after_first w ns tail) as [n s'] eqn:Eexp.
           pose proof (expose_chain_after_first_same w ns tail) as Hsame.
           rewrite Eexp in Hsame.
           pose proof (expose_chain_after_first_valid w ns tail
             Hds Hpos Hlen Htail) as Hout. rewrite Eexp in Hout.
           split; [exact (proj2 Hout)|exact Hsame].
        -- split; [constructor; assumption|reflexivity].
Qed.

Lemma consume_word_spec w s :
  valid_side s ->
  let '(n,s') := P.consume_word w s in
  valid_side s' /\
  side_bits s = copies (word_bits w) n ++ side_bits s'.
Proof. unfold P.consume_word. apply consume_word_fuel_spec. Qed.

Lemma denote_side_push_lit bits s :
  denote_side (P.push_lit bits s) =
  List.map sym_of_bool bits *> denote_side s.
Proof.
  unfold denote_side. rewrite side_bits_push_lit, Str_app_assoc. reflexivity.
Qed.

Lemma denote_side_push_run w n s :
  denote_side (P.push_run w n s) =
  copies (word_bits w) n *> denote_side s.
Proof.
  unfold denote_side. rewrite side_bits_push_run, Str_app_assoc. reflexivity.
Qed.

Lemma consume_word_denote w s n s' :
  valid_side s -> P.consume_word w s = (n,s') ->
  valid_side s' /\
  denote_side s = copies (word_bits w) n *> denote_side s'.
Proof.
  intros Hvalid E. pose proof (consume_word_spec w s Hvalid) as H.
  rewrite E in H. destruct H as [Hs Hbits]. split; [exact Hs|].
  unfold denote_side. rewrite Hbits, Str_app_assoc. reflexivity.
Qed.

Lemma apply_right_shift_sound m m' input output :
  valid_machine m -> P.m_dir m = P.R ->
  (forall n l r,
    l {{denote_q (P.m_state m)}}> (word_bits input)^^n *> r
      -[ tm ]->*
    l <* (word_bits output)^^n {{denote_q (P.m_state m)}}> r) ->
  P.apply_right_shift m input output = Some m' ->
  denote_machine m -[ tm ]->* denote_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hd Hshift E. destruct d; [discriminate|clear Hd].
  destruct (P.consume_word input r) as [n r'] eqn:Econsume.
  assert (Econsume0 :
    P.consume_word input
      (P.m_right {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = (n,r')).
  { cbn. exact Econsume. }
  unfold P.apply_right_shift in E. rewrite Econsume0 in E.
  destruct (NCount.is_zero n) eqn:En;
    cbn in E; [discriminate|].
  inversion E; subst; clear E.
  pose proof (consume_word_denote input r n r' Hr Econsume)
    as [_ Hright].
  unfold denote_machine.
  cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
    iota zeta.
  rewrite Hright, denote_side_push_run.
  exact (Hshift (N.to_nat n) (denote_side l) (denote_side r')).
Qed.

Lemma apply_right_shift_valid m m' input output :
  valid_machine m -> P.apply_right_shift m input output = Some m' ->
  valid_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E.
  destruct (P.consume_word input r) as [n r'] eqn:Econsume.
  assert (Econsume0 :
    P.consume_word input
      (P.m_right {| P.m_state:=q; P.m_dir:=d; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = (n,r')).
  { cbn. exact Econsume. }
  unfold P.apply_right_shift in E. rewrite Econsume0 in E.
  destruct (NCount.is_zero n); cbn in E;
    [discriminate|]. inversion E; subst.
  pose proof (consume_word_denote input r n r' Hr Econsume) as [Hr' _].
  unfold valid_machine.
  cbv delta [P.machine P.m_left P.m_right] iota zeta.
  split; [apply valid_push_run|]; assumption.
Qed.

Lemma strip_bits_denote bits s s' :
  valid_side s -> P.strip_bits bits s = Some s' ->
  valid_side s' /\
  denote_side s = List.map sym_of_bool bits *> denote_side s'.
Proof.
  intros Hvalid E. split.
  - exact (strip_bits_valid bits s s' Hvalid E).
  - exact (strip_bits_same bits s s' Hvalid E).
Qed.

Lemma apply_left_shift_sound m m' fixed input output :
  valid_machine m -> P.m_dir m = P.L ->
  (forall n l r,
    l <* (word_bits input)^^n <{{denote_q (P.m_state m)}}
        (List.map sym_of_bool fixed) *> r
      -[ tm ]->*
    l <{{denote_q (P.m_state m)}} (List.map sym_of_bool fixed) *>
        (word_bits output)^^n *> r) ->
  P.apply_left_shift m fixed input output = Some m' ->
  denote_machine m -[ tm ]->* denote_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hd Hshift E. destruct d; [clear Hd|discriminate].
  destruct (P.strip_bits fixed r) as [r'|] eqn:Estrip.
  2: {
    assert (Estrip0 :
      P.strip_bits fixed
        (P.m_right {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                      P.m_right:=r; P.m_incs:=inc |}) = None).
    { cbn. exact Estrip. }
    unfold P.apply_left_shift in E. rewrite Estrip0 in E. discriminate. }
  destruct (P.consume_word input l) as [n l'] eqn:Econsume.
  assert (Estrip0 :
    P.strip_bits fixed
      (P.m_right {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = Some r').
  { cbn. exact Estrip. }
  assert (Econsume0 :
    P.consume_word input
      (P.m_left {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                   P.m_right:=r; P.m_incs:=inc |}) = (n,l')).
  { cbn. exact Econsume. }
  unfold P.apply_left_shift in E. rewrite Estrip0, Econsume0 in E.
  destruct (NCount.is_zero n); cbn in E;
    [discriminate|].
  inversion E; subst; clear E.
  pose proof (strip_bits_denote fixed r r' Hr Estrip) as [_ Hright].
  pose proof (consume_word_denote input l n l' Hl Econsume) as [_ Hleft].
  unfold denote_machine.
  cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
    iota zeta.
  rewrite Hleft, Hright, denote_side_push_lit, denote_side_push_run.
  exact (Hshift (N.to_nat n) (denote_side l') (denote_side r')).
Qed.

Lemma apply_left_shift_valid m m' fixed input output :
  valid_machine m -> P.apply_left_shift m fixed input output = Some m' ->
  valid_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E.
  destruct (P.strip_bits fixed r) as [r'|] eqn:Estrip.
  2: {
    assert (Estrip0 :
      P.strip_bits fixed
        (P.m_right {| P.m_state:=q; P.m_dir:=d; P.m_left:=l;
                      P.m_right:=r; P.m_incs:=inc |}) = None).
    { cbn. exact Estrip. }
    unfold P.apply_left_shift in E. rewrite Estrip0 in E. discriminate. }
  destruct (P.consume_word input l) as [n l'] eqn:Econsume.
  assert (Estrip0 :
    P.strip_bits fixed
      (P.m_right {| P.m_state:=q; P.m_dir:=d; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = Some r').
  { cbn. exact Estrip. }
  assert (Econsume0 :
    P.consume_word input
      (P.m_left {| P.m_state:=q; P.m_dir:=d; P.m_left:=l;
                   P.m_right:=r; P.m_incs:=inc |}) = (n,l')).
  { cbn. exact Econsume. }
  unfold P.apply_left_shift in E. rewrite Estrip0, Econsume0 in E.
  destruct (NCount.is_zero n); cbn in E;
    [discriminate|]. inversion E; subst.
  pose proof (strip_bits_valid fixed r r' Hr Estrip) as Hr'.
  pose proof (consume_word_denote input l n l' Hl Econsume) as [Hl' _].
  unfold valid_machine.
  cbv beta delta [P.machine P.m_left P.m_right] iota zeta.
  split; [exact Hl'|]. apply valid_push_lit, valid_push_run. exact Hr'.
Qed.

Lemma apply_shift_sound m m' :
  valid_machine m -> P.apply_shift m = Some m' ->
  denote_machine m -[ tm ]->* denote_machine m'.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq, (P.m_dir m) eqn:Hd;
    unfold P.apply_shift in E; rewrite ?Hq, ?Hd in E; try discriminate.
  - destruct (P.apply_left_shift m [true] P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_sound; eauto.
      intros n l r. rewrite Hq. cbn [denote_q word_bits P.spelling sym_of_bool].
      apply T.BL_011011_1.
    + destruct (P.apply_left_shift m [true] P.W0110 P.W0011)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.BL_0110_1.
      * eapply apply_left_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.BL_01101_1.
  - destruct (P.apply_left_shift m P.sep P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_sound; eauto.
      intros n l r. rewrite Hq.
      cbn [denote_q word_bits P.spelling P.sep sym_of_bool].
      apply T.CL_011011_1111.
    + destruct (P.apply_left_shift m P.sep P.W10110 P.W01111)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling P.sep sym_of_bool].
        apply T.CL_01101_1111.
      * eapply apply_left_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool].
        apply T.CL_0110_1111101111.
  - destruct (P.apply_right_shift m P.W001111 P.W110110)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_right_shift_sound; eauto.
      intros n l r. rewrite Hq.
      cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_001111.
    + destruct (P.apply_right_shift m P.W00111 P.W10110)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_right_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_00111.
      * eapply apply_right_shift_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_0011.
Qed.

Lemma apply_shift_valid m m' :
  valid_machine m -> P.apply_shift m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq, (P.m_dir m) eqn:Hd;
    unfold P.apply_shift in E; rewrite ?Hq, ?Hd in E; try discriminate.
  - destruct (P.apply_left_shift m [true] P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_valid; eauto.
    + destruct (P.apply_left_shift m [true] P.W0110 P.W0011)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_valid; eauto.
      * eapply apply_left_shift_valid; eauto.
  - destruct (P.apply_left_shift m P.sep P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_valid; eauto.
    + destruct (P.apply_left_shift m P.sep P.W10110 P.W01111)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_valid; eauto.
      * eapply apply_left_shift_valid; eauto.
  - destruct (P.apply_right_shift m P.W001111 P.W110110)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_right_shift_valid; eauto.
    + destruct (P.apply_right_shift m P.W00111 P.W10110)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_right_shift_valid; eauto.
      * eapply apply_right_shift_valid; eauto.
Qed.

Lemma bits_eqb_eq xs ys : P.bits_eqb xs ys = true -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn; try discriminate.
  - reflexivity.
  - destruct x, y; cbn; intro E; try discriminate;
      f_equal; apply IH; exact E.
Qed.

Lemma valid_dseq_nonempty s :
  valid_dseq s -> 1 <= P.ds_len s -> P.ds_list s <> [].
Proof.
  intros Hvalid Hlen E. pose proof (valid_dseq_len s Hvalid) as H.
  rewrite E in H. cbn in H. lia.
Qed.

Lemma count_bits_cons w n ns :
  ns <> [] -> count_bits w (n :: ns) =
    copies (word_bits w) n ++ [1;1;1;1] ++ count_bits w ns.
Proof. destruct ns; [contradiction|reflexivity]. Qed.

Lemma collect_singleton_spec w n rest :
  positive_count n -> valid_side rest ->
  valid_dseq (P.ds_of_list [n]) /\
  List.Forall positive_count (P.ds_list (P.ds_of_list [n])) /\
  1 <= P.ds_len (P.ds_of_list [n]) /\ valid_side rest /\
  side_bits (P.Run w n :: rest) =
    count_bits w (P.ds_list (P.ds_of_list [n])) ++ side_bits rest.
Proof.
  intros Hn Hrest. split; [apply ds_rebuild_valid|].
  rewrite ds_list_of_list. split; [constructor; auto|].
  split.
  - change (1 <= P.ds_len (P.ds_rebuild [n])).
    pose proof (valid_dseq_len _ (ds_rebuild_valid [n])) as Hlen.
    rewrite ds_rebuild_list in Hlen. rewrite Hlen. cbn. lia.
  - split; [exact Hrest|reflexivity].
Qed.

Lemma collect_runs_spec fuel w s ns tail :
  valid_side s -> P.collect_runs fuel w s = Some (ns,tail) ->
  valid_dseq ns /\ List.Forall positive_count (P.ds_list ns) /\
  1 <= P.ds_len ns /\ valid_side tail /\
  side_bits s = count_bits w (P.ds_list ns) ++ side_bits tail.
Proof.
  revert s ns tail. induction fuel as [|fuel IH]; intros s ns tail Hvalid E.
  { discriminate. }
  destruct s as [|block rest]; [discriminate|].
  inversion Hvalid as [|? ? Hblock Hrest]; subst.
  destruct block as [bits|w' n|w' ds].
  - discriminate.
  - cbn [P.collect_runs] in E.
    destruct (P.word_eqb w w') eqn:Ew; [apply word_eqb_eq in Ew; subst w'|discriminate].
    destruct rest as [|next after].
    { inversion E; subst. apply collect_singleton_spec; assumption. }
    destruct next as [bits|w0 n0|w0 ds0].
    2-3: inversion E; subst; apply collect_singleton_spec; assumption.
    destruct (P.bits_eqb bits P.sep) eqn:Esep.
    2: inversion E; subst; apply collect_singleton_spec; assumption.
    apply bits_eqb_eq in Esep. subst bits.
    destruct (P.collect_runs fuel w after) as [[ns0 tail0]|] eqn:Erec.
    2: inversion E; subst; apply collect_singleton_spec; assumption.
    inversion Hrest as [|? ? Hsep Hafter]; subst.
    pose proof (IH after ns0 tail0 Hafter Erec)
      as [Hds [Hpos [Hlen [Htail Hsame]]]].
    inversion E; subst ns tail; clear E.
    split; [apply ds_cons_valid; exact Hds|].
    split.
    { rewrite ds_list_cons. constructor; assumption. }
    split.
    { pose proof (valid_dseq_len (P.ds_cons n ns0)
        (ds_cons_valid n ns0 Hds)) as Hlength.
      rewrite ds_list_cons in Hlength. rewrite Hlength. cbn. lia. }
    split; [exact Htail|].
    cbn [side_bits block_bits].
    rewrite ds_list_cons, count_bits_cons by
      (eapply valid_dseq_nonempty; eassumption).
    unfold P.sep at 1. cbn [sym_of_bool]. rewrite Hsame.
    repeat rewrite app_assoc. reflexivity.
  - cbn [P.collect_runs] in E.
    destruct (P.word_eqb w w') eqn:Ew; [|discriminate].
    apply word_eqb_eq in Ew. subst w'. inversion E; subst.
    destruct Hblock as [Hds [Hpos Hlen]].
    split; [exact Hds|]. split; [exact Hpos|]. split; [exact Hlen|].
    split; [exact Hrest|reflexivity].
Qed.

Lemma collect_chain_spec w s ns tail :
  valid_side s -> P.collect_chain w s = Some (ns,tail) ->
  valid_dseq ns /\ List.Forall positive_count (P.ds_list ns) /\
  1 <= P.ds_len ns /\ valid_side tail /\
  side_bits s = count_bits w (P.ds_list ns) ++ side_bits tail.
Proof. unfold P.collect_chain. apply collect_runs_spec. Qed.

Fixpoint rgroup_bits (w : P.Word) (ns : list N) : list Sym :=
  match ns with
  | [] => []
  | n :: ns' => copies (word_bits w) n ++ [1;1;1;1] ++ rgroup_bits w ns'
  end.

Fixpoint lgroup_bits (w : P.Word) (ns : list N) : list Sym :=
  match ns with
  | [] => []
  | n :: ns' => lgroup_bits w ns' ++ [1;1;1;1] ++ copies (word_bits w) n
  end.

Lemma RGroups_bits ns tail :
  T.RGroups (List.map N.to_nat ns) (tail *> 0inf) =
    (rgroup_bits P.W001111 ns ++ tail) *> 0inf.
Proof.
  induction ns as [|n ns IH]; cbn [List.map T.RGroups rgroup_bits].
  - reflexivity.
  - rewrite IH. unfold T.X, T.Sep, copies, word_bits.
    cbn [P.spelling sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma LGroups_bits ns tail :
  T.LGroups (List.map N.to_nat ns) (tail *> 0inf) =
    (lgroup_bits P.W110110 ns ++ tail) *> 0inf.
Proof.
  revert tail. induction ns as [|n ns IH]; intro tail;
    cbn [List.map T.LGroups lgroup_bits].
  - reflexivity.
  - unfold T.YL, T.Sep, copies, word_bits.
    cbn [P.spelling sym_of_bool]. rewrite <- !Str_app_assoc.
    rewrite IH. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma count_bits_snoc w ns n : ns <> [] ->
  count_bits w (ns ++ [n]) =
    count_bits w ns ++ [1;1;1;1] ++ copies (word_bits w) n.
Proof.
  induction ns as [|x ns IH]; intro Hnonempty; [contradiction|].
  destruct ns as [|y ns].
  - reflexivity.
  - change (copies (word_bits w) x ++ [1;1;1;1] ++
        count_bits w ((y :: ns) ++ [n]) =
      (copies (word_bits w) x ++ [1;1;1;1] ++ count_bits w (y :: ns)) ++
        [1;1;1;1] ++ copies (word_bits w) n).
    rewrite IH by discriminate.
    repeat rewrite app_assoc. reflexivity.
Qed.

Lemma rgroup_bits_count w ns : ns <> [] ->
  rgroup_bits w ns = count_bits w ns ++ [1;1;1;1].
Proof.
  induction ns as [|n ns IH]; intro Hnonempty; [contradiction|].
  destruct ns as [|m ns].
  - cbn [rgroup_bits count_bits]. rewrite app_nil_r. reflexivity.
  - change (copies (word_bits w) n ++ [1;1;1;1] ++
        rgroup_bits w (m :: ns) =
      (copies (word_bits w) n ++ [1;1;1;1] ++ count_bits w (m :: ns)) ++
        [1;1;1;1]).
    rewrite IH by discriminate.
    repeat rewrite app_assoc. reflexivity.
Qed.

Lemma lgroup_bits_count w ns : ns <> [] ->
  lgroup_bits w ns = [1;1;1;1] ++ count_bits w (rev ns).
Proof.
  induction ns as [|n ns IH]; intro Hnonempty; [contradiction|].
  destruct ns as [|m ns].
  - reflexivity.
  - change (lgroup_bits w (m :: ns) ++ [1;1;1;1] ++
      copies (word_bits w) n = [1;1;1;1] ++
      count_bits w (rev (n :: m :: ns))).
    rewrite IH by discriminate.
    change (rev (n :: m :: ns)) with (rev (m :: ns) ++ [n]).
    rewrite count_bits_snoc by
      (intro E; apply (f_equal (@length N)) in E;
       rewrite length_rev in E; cbn in E; lia).
    repeat rewrite app_assoc. reflexivity.
Qed.

Lemma count_bits_rev_snoc w prefix n : prefix <> [] ->
  count_bits w (rev (prefix ++ [n])) =
    copies (word_bits w) n ++ [1;1;1;1] ++ count_bits w (rev prefix).
Proof.
  intro Hprefix. rewrite rev_app_distr.
  change (count_bits w (n :: rev prefix) =
    copies (word_bits w) n ++ [1;1;1;1] ++ count_bits w (rev prefix)).
  rewrite count_bits_cons.
  - reflexivity.
  - intro E. apply (f_equal (@length N)) in E.
    rewrite length_rev in E. destruct prefix; cbn in E; contradiction || lia.
Qed.

Lemma literal_drop_spec bits prefix rest out :
  valid_side (P.Lit bits :: rest) ->
  P.literal_drop bits prefix rest = Some out ->
  valid_side out /\
  side_bits (P.Lit bits :: rest) =
    List.map sym_of_bool prefix ++ side_bits out.
Proof.
  intros Hvalid E. inversion Hvalid as [|? ? Hbits Hrest]; subst.
  unfold P.literal_drop in E.
  destruct (P.strip_prefix prefix bits) as [bits'|] eqn:Eprefix;
    [|discriminate].
  inversion E; subst out; clear E.
  split; [apply valid_lit_remainder; exact Hrest|].
  pose proof (strip_prefix_some prefix bits bits' Eprefix) as ->.
  cbn [side_bits block_bits]. rewrite map_app, side_bits_lit_remainder.
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma FR_groups_N ns lb rb : ns <> [] ->
  (lb *> 0inf) {{F}}> (count_bits P.W001111 ns ++ [1;1;1;1] ++ rb) *> 0inf
  -[ tm ]->*
  ([1;1;1;1] ++ count_bits P.W110110 (rev ns) ++ lb) *> 0inf
    {{F}}> rb *> 0inf.
Proof.
  intro Hnonempty.
  replace ((count_bits P.W001111 ns ++ [1;1;1;1] ++ rb) *> 0inf)
    with (T.RGroups (List.map N.to_nat ns) (rb *> 0inf)).
  2: { rewrite RGroups_bits, rgroup_bits_count by exact Hnonempty.
       rewrite app_assoc. reflexivity. }
  replace (([1;1;1;1] ++ count_bits P.W110110 (rev ns) ++ lb) *> 0inf)
    with (T.LGroups (List.map N.to_nat ns) (lb *> 0inf)).
  2: { rewrite LGroups_bits, lgroup_bits_count by exact Hnonempty.
       rewrite app_assoc. reflexivity. }
  apply T.FR_groups.
Qed.

Lemma BL_groups_N ns lb rb : ns <> [] ->
  ([1;1;1;1] ++ count_bits P.W110110 (rev ns) ++ lb) *> 0inf
    <{{B}} [1] *> rb *> 0inf
  -[ tm ]->*
  (lb *> 0inf) <{{B}} [1] *>
    (count_bits P.W001111 ns ++ [1;1;1;1] ++ rb) *> 0inf.
Proof.
  intro Hnonempty.
  replace (([1;1;1;1] ++ count_bits P.W110110 (rev ns) ++ lb) *> 0inf)
    with (T.LGroups (List.map N.to_nat ns) (lb *> 0inf)).
  2: { rewrite LGroups_bits, lgroup_bits_count by exact Hnonempty.
       rewrite app_assoc. reflexivity. }
  replace ((count_bits P.W001111 ns ++ [1;1;1;1] ++ rb) *> 0inf)
    with (T.RGroups (List.map N.to_nat ns) (rb *> 0inf)).
  2: { rewrite RGroups_bits, rgroup_bits_count by exact Hnonempty.
       rewrite app_assoc. reflexivity. }
  apply T.BL_groups.
Qed.

Lemma FR_chain_N prefix n lb rb : prefix <> [] ->
  (lb *> 0inf) {{F}}>
    (count_bits P.W001111 (prefix ++ [n]) ++ rb) *> 0inf
  -[ tm ]->*
  (count_bits P.W110110 (rev (prefix ++ [n])) ++ lb) *> 0inf
    {{F}}> rb *> 0inf.
Proof.
  intro Hprefix.
  replace ((count_bits P.W001111 (prefix ++ [n]) ++ rb) *> 0inf)
    with (T.RGroups (List.map N.to_nat prefix)
      (T.X^^(N.to_nat n) *> rb *> 0inf)).
  2: { rewrite <- Str_app_assoc.
       rewrite RGroups_bits, rgroup_bits_count by exact Hprefix.
       rewrite count_bits_snoc by exact Hprefix.
       unfold T.X, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  replace ((count_bits P.W110110 (rev (prefix ++ [n])) ++ lb) *> 0inf)
    with (T.LGroups (List.map N.to_nat prefix) (lb *> 0inf)
      <* T.YL^^(N.to_nat n)).
  2: { rewrite LGroups_bits, lgroup_bits_count by exact Hprefix.
       rewrite count_bits_rev_snoc by exact Hprefix.
       unfold T.YL, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  apply T.FR_chain.
Qed.

Lemma BL_chain_N prefix n lb rb : prefix <> [] ->
  (count_bits P.W110110 (rev (prefix ++ [n])) ++ lb) *> 0inf
    <{{B}} [1] *> rb *> 0inf
  -[ tm ]->*
  (lb *> 0inf) <{{B}} [1] *>
    (count_bits P.W001111 (prefix ++ [n]) ++ rb) *> 0inf.
Proof.
  intro Hprefix.
  replace ((count_bits P.W110110 (rev (prefix ++ [n])) ++ lb) *> 0inf)
    with (T.LGroups (List.map N.to_nat prefix) (lb *> 0inf)
      <* T.YL^^(N.to_nat n)).
  2: { rewrite LGroups_bits, lgroup_bits_count by exact Hprefix.
       rewrite count_bits_rev_snoc by exact Hprefix.
       unfold T.YL, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  replace ((count_bits P.W001111 (prefix ++ [n]) ++ rb) *> 0inf)
    with (T.RGroups (List.map N.to_nat prefix)
      (T.X^^(N.to_nat n) *> rb *> 0inf)).
  2: { rewrite <- Str_app_assoc.
       rewrite RGroups_bits, rgroup_bits_count by exact Hprefix.
       rewrite count_bits_snoc by exact Hprefix.
       unfold T.X, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  apply T.BL_chain.
Qed.

Lemma ds_two_last s :
  valid_dseq s -> P.ds_at_least_two s = true ->
  exists prefix n, P.ds_list s = prefix ++ [n] /\ prefix <> [].
Proof.
  intros Hvalid Htwo.
  apply ds_at_least_two_spec in Htwo.
  pose proof (valid_dseq_len s Hvalid) as Hlen.
  assert (Hnonempty : P.ds_list s <> []).
  { intro E. rewrite E in Hlen. cbn in Hlen. lia. }
  destruct (exists_last Hnonempty) as [prefix [n E]].
  exists prefix,n. split; [exact E|].
  intro Ep. subst prefix. rewrite E in Hlen. cbn in Hlen. lia.
Qed.

Lemma ds_rev_positive s :
  List.Forall positive_count (P.ds_list s) ->
  List.Forall positive_count (P.ds_list (P.ds_rev s)).
Proof. rewrite ds_list_rev. apply Forall_rev. Qed.

Lemma denote_side_push_sequence w ns s : valid_dseq ns ->
  denote_side (P.push_sequence w ns s) =
    count_bits w (P.ds_list ns) *> denote_side s.
Proof.
  intro Hvalid. unfold denote_side.
  rewrite side_bits_push_sequence by exact Hvalid.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma apply_chain_right_sound m m' :
  valid_machine m -> P.m_state m = P.F -> P.m_dir m = P.R ->
  P.apply_chain_right m = Some m' ->
  denote_machine m -[ tm ]->* denote_machine m'.
Proof.
  destruct m as [q d l r inc].
  cbn [valid_machine P.m_state P.m_dir] in *.
  intros [Hl Hr] Hq Hd E. subst q d.
  unfold P.apply_chain_right in E; cbn [P.m_right] in E.
  destruct (P.collect_chain P.W001111 r) as [[ns rest]|] eqn:Ecollect;
    [|discriminate].
  pose proof (collect_chain_spec P.W001111 r ns rest Hr Ecollect)
    as [Hds [Hpos [Hlen [Hrest Hsame]]]].
  assert (Hnonempty : P.ds_list ns <> []) by
    (eapply valid_dseq_nonempty; eassumption).
  destruct rest as [|block tail].
  - destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    destruct (ds_two_last ns Hds Htwo) as [prefix [n [Hlast Hprefix]]].
    unfold denote_machine; cbv beta delta
      [P.machine P.m_dir P.m_left P.m_right P.m_state] iota zeta.
    rewrite denote_side_push_sequence by (apply ds_rev_valid; exact Hds).
    unfold denote_side.
    rewrite ds_list_rev, Hsame, Hlast.
    cbn [denote_q side_bits]. repeat rewrite <- Str_app_assoc.
    repeat rewrite <- app_assoc.
    apply FR_chain_N. exact Hprefix.
  - destruct block as [bits|w n|w ds0].
    + destruct (P.literal_drop bits P.sep tail) as [r'|] eqn:Edrop.
      * inversion E; subst; clear E.
        pose proof (literal_drop_spec bits P.sep tail r' Hrest Edrop)
          as [_ Hdrop].
        change (denote_side l {{F}}> denote_side r -[tm]->*
          denote_side (P.push_lit P.sep
            (P.push_sequence P.W110110 (P.ds_rev ns) l))
            {{F}}> denote_side r').
        rewrite denote_side_push_lit,
          denote_side_push_sequence by (apply ds_rev_valid; exact Hds).
        unfold denote_side.
        rewrite ds_list_rev, Hsame, Hdrop.
        unfold P.sep. cbn [List.map denote_q side_bits sym_of_bool].
        repeat rewrite <- Str_app_assoc. repeat rewrite <- app_assoc.
        apply FR_groups_N. exact Hnonempty.
      * destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
        inversion E; subst; clear E.
        destruct (ds_two_last ns Hds Htwo)
          as [prefix [last [Hlast Hprefix]]].
        unfold denote_machine; cbv beta delta
          [P.machine P.m_dir P.m_left P.m_right P.m_state] iota zeta.
        rewrite denote_side_push_sequence by (apply ds_rev_valid; exact Hds).
        unfold denote_side.
        rewrite ds_list_rev, Hsame, Hlast.
        cbn [denote_q side_bits]. repeat rewrite <- Str_app_assoc.
        repeat rewrite <- app_assoc.
        apply FR_chain_N. exact Hprefix.
    + destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      destruct (ds_two_last ns Hds Htwo)
        as [prefix [last [Hlast Hprefix]]].
      unfold denote_machine; cbv beta delta
        [P.machine P.m_dir P.m_left P.m_right P.m_state] iota zeta.
      rewrite denote_side_push_sequence by (apply ds_rev_valid; exact Hds).
      unfold denote_side.
      rewrite ds_list_rev, Hsame, Hlast.
      cbn [denote_q side_bits]. repeat rewrite <- Str_app_assoc.
      repeat rewrite <- app_assoc.
      apply FR_chain_N. exact Hprefix.
    + destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      destruct (ds_two_last ns Hds Htwo)
        as [prefix [last [Hlast Hprefix]]].
      unfold denote_machine; cbv beta delta
        [P.machine P.m_dir P.m_left P.m_right P.m_state] iota zeta.
      rewrite denote_side_push_sequence by (apply ds_rev_valid; exact Hds).
      unfold denote_side.
      rewrite ds_list_rev, Hsame, Hlast.
      cbn [denote_q side_bits]. repeat rewrite <- Str_app_assoc.
      repeat rewrite <- app_assoc.
      apply FR_chain_N. exact Hprefix.
Qed.

Lemma apply_chain_right_valid m m' :
  valid_machine m -> P.apply_chain_right m = Some m' -> valid_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. unfold P.apply_chain_right in E; cbn [P.m_right] in E.
  destruct (P.collect_chain P.W001111 r) as [[ns rest]|] eqn:Ecollect;
    [|discriminate].
  pose proof (collect_chain_spec P.W001111 r ns rest Hr Ecollect)
    as [Hds [Hpos [Hlen [Hrest Hsame]]]].
  assert (Hrev : valid_dseq (P.ds_rev ns)) by
    (apply ds_rev_valid; exact Hds).
  assert (Hrevpos : List.Forall positive_count (P.ds_list (P.ds_rev ns))) by
    (apply ds_rev_positive; exact Hpos).
  destruct rest as [|block tail].
  - destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
    split; [apply valid_push_sequence; assumption|constructor].
  - destruct block as [bits|w n|w ds0].
    + destruct (P.literal_drop bits P.sep tail) as [r'|] eqn:Edrop.
      * inversion E; subst. split.
        -- change (valid_side (P.push_lit P.sep
             (P.push_sequence P.W110110 (P.ds_rev ns) l))).
           apply valid_push_lit, valid_push_sequence; assumption.
        -- exact (proj1 (literal_drop_spec bits P.sep tail r' Hrest Edrop)).
      * destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
        split; [apply valid_push_sequence; assumption|exact Hrest].
    + destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
      split; [apply valid_push_sequence; assumption|exact Hrest].
    + destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
      split; [apply valid_push_sequence; assumption|exact Hrest].
Qed.

Lemma ds_two_rev_last s :
  valid_dseq s -> P.ds_at_least_two s = true ->
  exists prefix n, P.ds_list s = rev (prefix ++ [n]) /\ prefix <> [].
Proof.
  intros Hvalid Htwo.
  assert (Hrevvalid : valid_dseq (P.ds_rev s)) by
    (apply ds_rev_valid; exact Hvalid).
  assert (Hrevlen : P.ds_at_least_two (P.ds_rev s) = true).
  { apply ds_at_least_two_spec in Htwo. apply ds_at_least_two_spec.
    destruct s. unfold P.ds_len, P.ds_rev in *. cbn in *. lia. }
  destruct (ds_two_last (P.ds_rev s) Hrevvalid Hrevlen)
    as [prefix [n [E Hprefix]]].
  exists prefix,n. split; [|exact Hprefix].
  rewrite ds_list_rev in E. apply (f_equal (@rev N)) in E.
  rewrite rev_involutive in E. exact E.
Qed.

Lemma BL_groups_sides left right ns ltail rtail :
  valid_dseq ns -> 1 <= P.ds_len ns ->
  side_bits left = [1;1;1;1] ++
    count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail ->
  denote_side right = [1] *> denote_side rtail ->
  denote_side left <{{B}} denote_side right -[tm]->*
  denote_side ltail <{{B}}
    denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns)
        (P.push_lit P.sep rtail))).
Proof.
  intros Hds Hlen Hleft Hright.
  assert (Hrevvalid : valid_dseq (P.ds_rev ns)) by
    (apply ds_rev_valid; exact Hds).
  assert (Hnonempty : rev (P.ds_list ns) <> []).
  { intro E. apply (f_equal (@length N)) in E. rewrite length_rev in E.
    pose proof (valid_dseq_len ns Hds) as Hlength.
    rewrite E in Hlength. cbn in Hlength. lia. }
  assert (Hleftden : denote_side left =
      ([1;1;1;1] ++ count_bits P.W110110 (P.ds_list ns) ++
        side_bits ltail) *> 0inf).
  { unfold denote_side. rewrite Hleft. reflexivity. }
  assert (Hout : denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns)
        (P.push_lit P.sep rtail))) =
      [1] *> (count_bits P.W001111 (rev (P.ds_list ns)) ++
        [1;1;1;1] ++ side_bits rtail) *> 0inf).
  { rewrite denote_side_push_lit,
      denote_side_push_sequence by exact Hrevvalid.
    rewrite ds_list_rev, denote_side_push_lit.
    unfold denote_side, P.sep. cbn [List.map sym_of_bool].
    repeat rewrite Str_app_assoc. reflexivity. }
  rewrite Hleftden, Hright, Hout.
  pose proof (BL_groups_N (rev (P.ds_list ns))
    (side_bits ltail) (side_bits rtail) Hnonempty) as Hrule.
  rewrite rev_involutive in Hrule. exact Hrule.
Qed.

Lemma BL_chain_sides left right ns ltail rtail :
  valid_dseq ns -> P.ds_at_least_two ns = true ->
  side_bits left = count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail ->
  denote_side right = [1] *> denote_side rtail ->
  denote_side left <{{B}} denote_side right -[tm]->*
  denote_side ltail <{{B}}
    denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns) rtail)).
Proof.
  intros Hds Htwo Hleft Hright.
  destruct (ds_two_rev_last ns Hds Htwo)
    as [prefix [n [Hshape Hprefix]]].
  assert (Hrevvalid : valid_dseq (P.ds_rev ns)) by
    (apply ds_rev_valid; exact Hds).
  assert (Hleftden : denote_side left =
      (count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail) *> 0inf).
  { unfold denote_side. rewrite Hleft. reflexivity. }
  assert (Hout : denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns) rtail)) =
      [1] *> (count_bits P.W001111 (rev (P.ds_list ns)) ++
        side_bits rtail) *> 0inf).
  { rewrite denote_side_push_lit,
      denote_side_push_sequence by exact Hrevvalid.
    rewrite ds_list_rev. unfold denote_side. cbn [List.map sym_of_bool].
    repeat rewrite Str_app_assoc. reflexivity. }
  rewrite Hleftden, Hright, Hout, Hshape.
  rewrite rev_involutive.
  apply BL_chain_N. exact Hprefix.
Qed.

Lemma apply_chain_left_sound m m' :
  valid_machine m -> P.m_state m = P.B -> P.m_dir m = P.L ->
  P.apply_chain_left m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  destruct m as [q d l r inc].
  cbn [valid_machine P.m_state P.m_dir] in *.
  intros [Hl Hr] Hq Hd E. subst q d.
  unfold P.apply_chain_left in E; cbn [P.m_right P.m_left] in E.
  destruct (P.strip_bits [true] r) as [r0|] eqn:Estrip; [|discriminate].
  pose proof (strip_bits_denote [true] r r0 Hr Estrip) as [Hr0 Hright].
  destruct l as [|block after].
  { cbn [P.collect_chain P.collect_runs] in E. discriminate. }
  inversion Hl as [|? ? Hblock Hafter]; subst.
  destruct block as [bits|w n|w ds0].
  - destruct (P.bits_eqb bits P.sep) eqn:Esep.
    + apply bits_eqb_eq in Esep. subst bits.
      destruct (P.collect_chain P.W110110 after)
        as [[ns lout]|] eqn:Ecollect.
      * inversion E; subst; clear E.
        pose proof (collect_chain_spec P.W110110 after ns lout Hafter Ecollect)
          as [Hds [Hpos [Hlen [Hlout Hsame]]]].
        assert (Hleft : side_bits (P.Lit P.sep :: after) =
          [1;1;1;1] ++ count_bits P.W110110 (P.ds_list ns) ++
            side_bits lout).
        { cbn [side_bits block_bits P.sep List.map sym_of_bool].
          rewrite Hsame. reflexivity. }
        change (denote_side (P.Lit P.sep :: after) <{{B}} denote_side r
          -[tm]->* denote_side lout <{{B}}
          denote_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns)
              (P.push_lit P.sep r0)))).
        eapply BL_groups_sides; eassumption.
      * destruct (P.collect_chain P.W110110 (P.Lit P.sep :: after))
          as [[ns lout]|] eqn:Ecollect0; [|discriminate].
        destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
        inversion E; subst; clear E.
        pose proof (collect_chain_spec P.W110110
          (P.Lit P.sep :: after) ns lout Hl Ecollect0)
          as [Hds [Hpos [Hlen [Hlout Hleft]]]].
        change (denote_side (P.Lit P.sep :: after) <{{B}} denote_side r
          -[tm]->* denote_side lout <{{B}}
          denote_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
        eapply BL_chain_sides; eassumption.
    + destruct (P.collect_chain P.W110110 (P.Lit bits :: after))
        as [[ns lout]|] eqn:Ecollect; [|discriminate].
      destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      pose proof (collect_chain_spec P.W110110
        (P.Lit bits :: after) ns lout Hl Ecollect)
        as [Hds [Hpos [Hlen [Hlout Hleft]]]].
      change (denote_side (P.Lit bits :: after) <{{B}} denote_side r
        -[tm]->* denote_side lout <{{B}}
        denote_side (P.push_lit [true]
          (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
      eapply BL_chain_sides; eassumption.
  - destruct (P.collect_chain P.W110110 (P.Run w n :: after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    pose proof (collect_chain_spec P.W110110
      (P.Run w n :: after) ns lout Hl Ecollect)
      as [Hds [Hpos [Hlen [Hlout Hleft]]]].
    change (denote_side (P.Run w n :: after) <{{B}} denote_side r
      -[tm]->* denote_side lout <{{B}}
      denote_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    eapply BL_chain_sides; eassumption.
  - destruct (P.collect_chain P.W110110 (P.Chain w ds0 :: after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    pose proof (collect_chain_spec P.W110110
      (P.Chain w ds0 :: after) ns lout Hl Ecollect)
      as [Hds [Hpos [Hlen [Hlout Hleft]]]].
    change (denote_side (P.Chain w ds0 :: after) <{{B}} denote_side r
      -[tm]->* denote_side lout <{{B}}
      denote_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    eapply BL_chain_sides; eassumption.
Qed.

Lemma apply_chain_left_valid m m' :
  valid_machine m -> P.apply_chain_left m = Some m' -> valid_machine m'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. unfold P.apply_chain_left in E;
    cbn [P.m_right P.m_left] in E.
  destruct (P.strip_bits [true] r) as [r0|] eqn:Estrip; [|discriminate].
  pose proof (strip_bits_denote [true] r r0 Hr Estrip) as [Hr0 Hright].
  destruct l as [|block after].
  { cbn [P.collect_chain P.collect_runs] in E. discriminate. }
  inversion Hl as [|? ? Hblock Hafter]; subst.
  destruct block as [bits|w n|w ds0].
  - destruct (P.bits_eqb bits P.sep) eqn:Esep.
    + destruct (P.collect_chain P.W110110 after)
        as [[ns lout]|] eqn:Ecollect.
      * inversion E; subst.
        pose proof (collect_chain_spec P.W110110 after ns lout Hafter Ecollect)
          as [Hds [Hpos [Hlen [Hlout Hsame]]]].
        assert (Hrev : valid_dseq (P.ds_rev ns)) by
          (apply ds_rev_valid; exact Hds).
        assert (Hrevpos : List.Forall positive_count
          (P.ds_list (P.ds_rev ns))) by (apply ds_rev_positive; exact Hpos).
        change (valid_side lout /\
          valid_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns)
              (P.push_lit P.sep r0)))).
        split; [exact Hlout|].
        apply valid_push_lit, valid_push_sequence; try assumption.
        apply valid_push_lit. exact Hr0.
      * destruct (P.collect_chain P.W110110 (P.Lit bits :: after))
          as [[ns lout]|] eqn:Ecollect0; [|discriminate].
        destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
        pose proof (collect_chain_spec P.W110110
          (P.Lit bits :: after) ns lout Hl Ecollect0)
          as [Hds [Hpos [Hlen [Hlout Hsame]]]].
        assert (Hrev : valid_dseq (P.ds_rev ns)) by
          (apply ds_rev_valid; exact Hds).
        assert (Hrevpos : List.Forall positive_count
          (P.ds_list (P.ds_rev ns))) by (apply ds_rev_positive; exact Hpos).
        change (valid_side lout /\
          valid_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
        split; [exact Hlout|].
        apply valid_push_lit, valid_push_sequence; assumption.
    + destruct (P.collect_chain P.W110110 (P.Lit bits :: after))
        as [[ns lout]|] eqn:Ecollect; [|discriminate].
      destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
      pose proof (collect_chain_spec P.W110110
        (P.Lit bits :: after) ns lout Hl Ecollect)
        as [Hds [Hpos [Hlen [Hlout Hsame]]]].
      assert (Hrev : valid_dseq (P.ds_rev ns)) by
        (apply ds_rev_valid; exact Hds).
      assert (Hrevpos : List.Forall positive_count
        (P.ds_list (P.ds_rev ns))) by (apply ds_rev_positive; exact Hpos).
      change (valid_side lout /\
        valid_side (P.push_lit [true]
          (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
      split; [exact Hlout|].
      apply valid_push_lit, valid_push_sequence; assumption.
  - destruct (P.collect_chain P.W110110 (P.Run w n :: after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
    pose proof (collect_chain_spec P.W110110
      (P.Run w n :: after) ns lout Hl Ecollect)
      as [Hds [Hpos [Hlen [Hlout Hsame]]]].
    assert (Hrev : valid_dseq (P.ds_rev ns)) by
      (apply ds_rev_valid; exact Hds).
    assert (Hrevpos : List.Forall positive_count
      (P.ds_list (P.ds_rev ns))) by (apply ds_rev_positive; exact Hpos).
    change (valid_side lout /\
      valid_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    split; [exact Hlout|]. apply valid_push_lit, valid_push_sequence; assumption.
  - destruct (P.collect_chain P.W110110 (P.Chain w ds0 :: after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns); [|discriminate]. inversion E; subst.
    pose proof (collect_chain_spec P.W110110
      (P.Chain w ds0 :: after) ns lout Hl Ecollect)
      as [Hds [Hpos [Hlen [Hlout Hsame]]]].
    assert (Hrev : valid_dseq (P.ds_rev ns)) by
      (apply ds_rev_valid; exact Hds).
    assert (Hrevpos : List.Forall positive_count
      (P.ds_list (P.ds_rev ns))) by (apply ds_rev_positive; exact Hpos).
    change (valid_side lout /\
      valid_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    split; [exact Hlout|]. apply valid_push_lit, valid_push_sequence; assumption.
Qed.

Lemma apply_chain_sound m m' :
  valid_machine m -> P.apply_chain m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq, (P.m_dir m) eqn:Hd;
    unfold P.apply_chain in E; rewrite ?Hq, ?Hd in E; try discriminate.
  - eapply apply_chain_left_sound; eauto.
  - eapply apply_chain_right_sound; eauto.
Qed.

Lemma apply_chain_valid m m' :
  valid_machine m -> P.apply_chain m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq, (P.m_dir m) eqn:Hd;
    unfold P.apply_chain in E; rewrite ?Hq, ?Hd in E; try discriminate.
  - eapply apply_chain_left_valid; eauto.
  - eapply apply_chain_right_valid; eauto.
Qed.

Lemma RGroups_stream ns r :
  T.RGroups (List.map N.to_nat ns) r = rgroup_bits P.W001111 ns *> r.
Proof.
  induction ns as [|n ns IH]; cbn [List.map T.RGroups rgroup_bits].
  - reflexivity.
  - rewrite IH. unfold T.X, T.Sep, copies, word_bits.
    cbn [P.spelling sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma LGroups_stream ns l :
  T.LGroups (List.map N.to_nat ns) l = lgroup_bits P.W110110 ns *> l.
Proof.
  revert l. induction ns as [|n ns IH]; intro l;
    cbn [List.map T.LGroups lgroup_bits].
  - reflexivity.
  - unfold T.YL, T.Sep, copies, word_bits.
    cbn [P.spelling sym_of_bool]. rewrite <- !Str_app_assoc.
    rewrite IH. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma FR_chain_side_N prefix n l r : prefix <> [] ->
  l {{F}}> count_bits P.W001111 (prefix ++ [n]) *> r -[tm]->*
  count_bits P.W110110 (rev (prefix ++ [n])) *> l {{F}}> r.
Proof.
  intro Hprefix.
  replace (count_bits P.W001111 (prefix ++ [n]) *> r)
    with (T.RGroups (List.map N.to_nat prefix) (T.X^^(N.to_nat n) *> r)).
  2: { rewrite RGroups_stream, rgroup_bits_count by exact Hprefix.
       rewrite count_bits_snoc by exact Hprefix.
       unfold T.X, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  replace (count_bits P.W110110 (rev (prefix ++ [n])) *> l)
    with (T.LGroups (List.map N.to_nat prefix) l <* T.YL^^(N.to_nat n)).
  2: { rewrite LGroups_stream, lgroup_bits_count by exact Hprefix.
       rewrite count_bits_rev_snoc by exact Hprefix.
       unfold T.YL, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  apply T.FR_chain.
Qed.

Lemma BL_chain_side_N prefix n l r : prefix <> [] ->
  count_bits P.W110110 (rev (prefix ++ [n])) *> l <{{B}} [1] *> r
  -[tm]->* l <{{B}} [1] *>
    count_bits P.W001111 (prefix ++ [n]) *> r.
Proof.
  intro Hprefix.
  replace (count_bits P.W110110 (rev (prefix ++ [n])) *> l)
    with (T.LGroups (List.map N.to_nat prefix) l <* T.YL^^(N.to_nat n)).
  2: { rewrite LGroups_stream, lgroup_bits_count by exact Hprefix.
       rewrite count_bits_rev_snoc by exact Hprefix.
       unfold T.YL, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  replace (count_bits P.W001111 (prefix ++ [n]) *> r)
    with (T.RGroups (List.map N.to_nat prefix) (T.X^^(N.to_nat n) *> r)).
  2: { rewrite RGroups_stream, rgroup_bits_count by exact Hprefix.
       rewrite count_bits_snoc by exact Hprefix.
       unfold T.X, copies, word_bits. cbn [P.spelling sym_of_bool].
       repeat rewrite Str_app_assoc. reflexivity. }
  apply T.BL_chain.
Qed.

Lemma FR_chain_all_N ns l r : ns <> [] ->
  l {{F}}> count_bits P.W001111 ns *> r -[tm]->*
  count_bits P.W110110 (rev ns) *> l {{F}}> r.
Proof.
  destruct ns as [|n ns]; [contradiction|]. intros _.
  destruct ns as [|m ns].
  - cbn [count_bits rev]. unfold copies, word_bits, T.X, T.YL.
    cbn [P.spelling sym_of_bool]. apply T.FR_001111.
  - assert (Hne : n :: m :: ns <> []) by discriminate.
    destruct (exists_last Hne) as [prefix [last E]].
    assert (Hprefix : prefix <> []).
    { intro Ep. subst prefix. apply (f_equal (@length N)) in E.
      cbn in E. lia. }
    rewrite E. apply FR_chain_side_N. exact Hprefix.
Qed.

Lemma BL_chain_all_N ns l r : ns <> [] ->
  count_bits P.W110110 (rev ns) *> l <{{B}} [1] *> r -[tm]->*
  l <{{B}} [1] *> count_bits P.W001111 ns *> r.
Proof.
  destruct ns as [|n ns]; [contradiction|]. intros _.
  destruct ns as [|m ns].
  - cbn [count_bits rev]. unfold copies, word_bits, T.X, T.YL.
    cbn [P.spelling sym_of_bool]. apply T.BL_011011_1.
  - assert (Hne : n :: m :: ns <> []) by discriminate.
    destruct (exists_last Hne) as [prefix [last E]].
    assert (Hprefix : prefix <> []).
    { intro Ep. subst prefix. apply (f_equal (@length N)) in E.
      cbn in E. lia. }
    rewrite E. apply BL_chain_side_N. exact Hprefix.
Qed.

Definition header_pass (x y : list Sym) : Prop :=
  (forall l r, l {{F}}> x *> r -[tm]->* y *> l {{F}}> r) /\
  (forall l r, y *> l <{{B}} [1] *> r -[tm]->*
               l <{{B}} [1] *> x *> r).

Lemma header_pass_nil : header_pass [] [].
Proof. split; intros; finish. Qed.

Lemma header_pass_compose x1 y1 x2 y2 :
  header_pass x1 y1 -> header_pass x2 y2 ->
  header_pass (x1 ++ x2) (y2 ++ y1).
Proof.
  intros [HF1 HB1] [HF2 HB2]. split; intros l r.
  - rewrite Str_app_assoc. follow HF1. follow HF2.
    rewrite Str_app_assoc. finish.
  - rewrite Str_app_assoc. follow HB2. follow HB1.
    rewrite Str_app_assoc. finish.
Qed.

Lemma header_pass_ones3 : header_pass [1;1;1] [1;1;1].
Proof.
  split; intros l r.
  - do 3 step1. finish.
  - do 3 step1. finish.
Qed.

Lemma header_pass_X_run n :
  header_pass (copies (word_bits P.W001111) n)
              (copies (word_bits P.W110110) n).
Proof.
  split; intros l r; unfold copies, word_bits, T.X, T.YL;
    cbn [P.spelling sym_of_bool].
  - apply T.FR_001111.
  - apply T.BL_011011_1.
Qed.

Lemma header_pass_X_chain ns : ns <> [] ->
  header_pass (count_bits P.W001111 ns)
              (count_bits P.W110110 (rev ns)).
Proof.
  intro Hnonempty. split; intros l r.
  - apply FR_chain_all_N. exact Hnonempty.
  - apply BL_chain_all_N. exact Hnonempty.
Qed.

Lemma header_pass_00111_run n :
  header_pass (copies (word_bits P.W00111) n)
              (copies (word_bits P.W10110) n).
Proof.
  split; intros l r; unfold copies, word_bits;
    cbn [P.spelling sym_of_bool].
  - apply T.FR_00111.
  - apply T.BL_01101_1.
Qed.

Lemma header_pass_0011_run n :
  header_pass (copies (word_bits P.W0011) n)
              (copies (word_bits P.W0110) n).
Proof.
  split; intros l r; unfold copies, word_bits;
    cbn [P.spelling sym_of_bool].
  - apply T.FR_0011.
  - apply T.BL_0110_1.
Qed.

Definition transparent_header (h : P.Side) : Prop :=
  exists y, header_pass (side_bits h) y.

Lemma side_bits_app x y : side_bits (x ++ y) = side_bits x ++ side_bits y.
Proof.
  induction x as [|b x IH]; [reflexivity|].
  change (block_bits b ++ side_bits (x ++ y) =
    (block_bits b ++ side_bits x) ++ side_bits y).
  rewrite IH. apply app_assoc.
Qed.

Lemma header_fallback_spec r : valid_side r ->
  valid_side ([] : P.Side) /\ valid_side r /\
  side_bits r = side_bits ([] : P.Side) ++ side_bits r /\
  transparent_header ([] : P.Side).
Proof.
  intro Hr. split; [constructor|]. split; [exact Hr|].
  split; [reflexivity|]. exists ([] : list Sym). apply header_pass_nil.
Qed.

Lemma header_run_spec n b rest :
  positive_count n -> positive_count b -> valid_side rest ->
  valid_side [P.Run P.W001111 n; P.Run P.W00111 b] /\
  valid_side rest /\
  side_bits (P.Run P.W001111 n :: P.Run P.W00111 b :: rest) =
    side_bits [P.Run P.W001111 n; P.Run P.W00111 b] ++ side_bits rest /\
  transparent_header [P.Run P.W001111 n; P.Run P.W00111 b].
Proof.
  intros Hn Hb Hr. split; [repeat constructor; assumption|].
  split; [exact Hr|]. split.
  { change (side_bits ([P.Run P.W001111 n; P.Run P.W00111 b] ++ rest) =
      side_bits [P.Run P.W001111 n; P.Run P.W00111 b] ++ side_bits rest).
    apply side_bits_app. }
  exists (copies (word_bits P.W10110) b ++
          copies (word_bits P.W110110) n).
  cbn [side_bits block_bits]. repeat rewrite app_nil_r.
  apply header_pass_compose; [apply header_pass_X_run|apply header_pass_00111_run].
Qed.

Lemma header_chain_spec ns b rest :
  valid_dseq ns -> List.Forall positive_count (P.ds_list ns) ->
  1 <= P.ds_len ns -> positive_count b -> valid_side rest ->
  valid_side [P.Chain P.W001111 ns; P.Run P.W00111 b] /\
  valid_side rest /\
  side_bits (P.Chain P.W001111 ns :: P.Run P.W00111 b :: rest) =
    side_bits [P.Chain P.W001111 ns; P.Run P.W00111 b] ++ side_bits rest /\
  transparent_header [P.Chain P.W001111 ns; P.Run P.W00111 b].
Proof.
  intros Hds Hpos Hlen Hb Hr.
  split; [constructor; [cbn [valid_block]; auto|constructor; auto]|].
  split; [exact Hr|]. split.
  { change (side_bits ([P.Chain P.W001111 ns; P.Run P.W00111 b] ++ rest) =
      side_bits [P.Chain P.W001111 ns; P.Run P.W00111 b] ++ side_bits rest).
    apply side_bits_app. }
  assert (Hnonempty : P.ds_list ns <> []) by
    (eapply valid_dseq_nonempty; eassumption).
  exists (copies (word_bits P.W10110) b ++
          count_bits P.W110110 (rev (P.ds_list ns))).
  cbn [side_bits block_bits]. repeat rewrite app_nil_r.
  apply header_pass_compose;
    [apply header_pass_X_chain; exact Hnonempty|apply header_pass_00111_run].
Qed.

Lemma header_lit_spec b c rest :
  positive_count b -> positive_count c -> valid_side rest ->
  valid_side [P.Lit [true;true;true]; P.Run P.W00111 b; P.Run P.W0011 c] /\
  valid_side rest /\
  side_bits (P.Lit [true;true;true] :: P.Run P.W00111 b ::
    P.Run P.W0011 c :: rest) =
    side_bits [P.Lit [true;true;true]; P.Run P.W00111 b; P.Run P.W0011 c] ++
      side_bits rest /\
  transparent_header
    [P.Lit [true;true;true]; P.Run P.W00111 b; P.Run P.W0011 c].
Proof.
  intros Hb Hc Hr. split.
  { repeat constructor; try discriminate; assumption. }
  split; [exact Hr|]. split.
  { change (side_bits ([P.Lit [true;true;true]; P.Run P.W00111 b;
        P.Run P.W0011 c] ++ rest) =
      side_bits [P.Lit [true;true;true]; P.Run P.W00111 b;
        P.Run P.W0011 c] ++ side_bits rest).
    apply side_bits_app. }
  exists (copies (word_bits P.W0110) c ++
    copies (word_bits P.W10110) b ++ [1;1;1]).
  cbn [side_bits block_bits List.map sym_of_bool]. repeat rewrite app_nil_r.
  pose proof (header_pass_compose _ _ _ _ header_pass_ones3
    (header_pass_00111_run b)) as H12.
  pose proof (header_pass_compose _ _ _ _ H12
    (header_pass_0011_run c)) as H123.
  rewrite <- app_assoc in H123. exact H123.
Qed.

Lemma positive_run_true w b : P.positive_run w b = true ->
  exists n, b = P.Run w n /\ positive_count n.
Proof.
  destruct b as [bits|w' n|w' ns]; cbn [P.positive_run]; try discriminate.
  intro E. apply Bool.andb_true_iff in E. destruct E as [Ew En].
  apply word_eqb_eq in Ew. subst w'.
  apply Bool.negb_true_iff, N.eqb_neq in En.
  exists n. split; [reflexivity|].
  unfold positive_count. apply N.neq_0_lt_0. exact En.
Qed.

Lemma parse_boundary_header_spec r h tail :
  valid_side r -> P.parse_boundary_header r = (h,tail) ->
  valid_side h /\ valid_side tail /\
  side_bits r = side_bits h ++ side_bits tail /\ transparent_header h.
Proof.
  intros Hvalid E.
  destruct r as [|b1 r].
  { inversion E; subst. apply header_fallback_spec. exact Hvalid. }
  destruct b1 as [bits|w n|w ns].
  - destruct r as [|b2 r].
    { inversion E; subst. apply header_fallback_spec. exact Hvalid. }
    destruct r as [|b3 rest].
    { inversion E; subst. apply header_fallback_spec. exact Hvalid. }
    cbn [P.parse_boundary_header] in E.
    destruct (if (if P.bits_eqb bits [true;true;true]
                  then P.positive_run P.W00111 b2 else false)
              then P.positive_run P.W0011 b3 else false) eqn:Htest.
    + cbn in E. inversion E; subst; clear E.
      repeat rewrite and_true_iff in Htest.
      destruct Htest as [[Hbits Hb] Hc].
      apply bits_eqb_eq in Hbits. subst bits.
      destruct (positive_run_true P.W00111 b2 Hb) as [bn [-> Hbn]].
      destruct (positive_run_true P.W0011 b3 Hc) as [cn [-> Hcn]].
      inversion Hvalid as [|? ? H1 Hrest1]; subst.
      inversion Hrest1 as [|? ? H2 Hrest2]; subst.
      inversion Hrest2 as [|? ? H3 Hrest].
      apply header_lit_spec; assumption.
    + cbn in E. inversion E; subst.
      apply header_fallback_spec. exact Hvalid.
  - destruct r as [|b2 rest].
    { destruct w; inversion E; subst; apply header_fallback_spec; exact Hvalid. }
    destruct w; cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct b2 as [bits2|w2 b|w2 ds2];
      cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct w2; cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct (negb (NCount.is_zero n) &&
      negb (NCount.is_zero b))%bool eqn:Htest.
    + cbn in E. inversion E; subst; clear E.
      apply and_true_iff in Htest. destruct Htest as [Hn Hb].
      apply Bool.negb_true_iff, N.eqb_neq in Hn.
      apply Bool.negb_true_iff, N.eqb_neq in Hb.
      inversion Hvalid as [|? ? H1 Hrest1]; subst.
      inversion Hrest1 as [|? ? H2 Hrest].
      apply header_run_spec; unfold positive_count; try lia; assumption.
    + cbn in E. inversion E; subst.
      apply header_fallback_spec. exact Hvalid.
  - destruct r as [|b2 rest].
    { destruct w; inversion E; subst; apply header_fallback_spec; exact Hvalid. }
    destruct w; cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct b2 as [bits2|w2 b|w2 ds2];
      cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct w2; cbn [P.parse_boundary_header] in E;
      try (inversion E; subst; apply header_fallback_spec; exact Hvalid).
    destruct (P.ds_nonempty ns &&
      negb (NCount.is_zero b))%bool
      eqn:Htest.
    + cbn in E. inversion E; subst; clear E.
      apply and_true_iff in Htest. destruct Htest as [Hnonempty Hb].
      apply Bool.negb_true_iff, N.eqb_neq in Hb.
      inversion Hvalid as [|? ? H1 Hrest1]; subst.
      inversion Hrest1 as [|? ? H2 Hrest].
      destruct H1 as [Hds [Hpos Hlen]].
      apply header_chain_spec; try assumption.
    + cbn in E. inversion E; subst.
      apply header_fallback_spec. exact Hvalid.
Qed.

Lemma parse_boundary_prefix_spec m p :
  valid_machine m -> P.parse_boundary_prefix m = Some p ->
  P.m_state m = P.C /\ P.m_dir m = P.L /\ P.m_left m = [] /\
  valid_side (P.bp_header p) /\ valid_dseq (P.bp_xs p) /\
  List.Forall positive_count (P.ds_list (P.bp_xs p)) /\
  1 <= P.ds_len (P.bp_xs p) /\ valid_side (P.bp_tail p) /\
  transparent_header (P.bp_header p) /\
  denote_side (P.m_right m) = [1;1] *>
    copies (word_bits P.W0011) (P.bp_a p) *>
    side_bits (P.bp_header p) *>
    count_bits P.W001111 (P.ds_list (P.bp_xs p)) *>
    denote_side (P.bp_tail p).
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E.
  unfold P.parse_boundary_prefix in E.
  destruct q, d, l;
    cbv beta delta [P.m_state P.m_dir P.m_left P.m_right] iota zeta in E;
    try discriminate.
  destruct (P.strip_bits [true;true] r) as [r0|] eqn:Estrip;
    [|discriminate].
  destruct (P.consume_word P.W0011 r0) as [a r1] eqn:Econsume.
  destruct (P.parse_boundary_header r1) as [header r2] eqn:Eheader.
  destruct (P.collect_chain P.W001111 r2) as [[xs tail]|] eqn:Ecollect;
    [|discriminate].
  inversion E; subst p; clear E.
  pose proof (strip_bits_denote [true;true] r r0 Hr Estrip)
    as [Hr0 Hstrip].
  pose proof (consume_word_denote P.W0011 r0 a r1 Hr0 Econsume)
    as [Hr1 Hconsume].
  pose proof (parse_boundary_header_spec r1 header r2 Hr1 Eheader)
    as [Hheader [Hr2 [Hheadersame Htransparent]]].
  pose proof (collect_chain_spec P.W001111 r2 xs tail Hr2 Ecollect)
    as [Hds [Hpos [Hlen [Htail Hcollect]]]].
  assert (Hheaderden : denote_side r1 = side_bits header *> denote_side r2).
  { unfold denote_side. rewrite Hheadersame, Str_app_assoc. reflexivity. }
  assert (Hcollectden : denote_side r2 =
      count_bits P.W001111 (P.ds_list xs) *> denote_side tail).
  { unfold denote_side. rewrite Hcollect, Str_app_assoc. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hheader|]. split; [exact Hds|]. split; [exact Hpos|].
  split; [exact Hlen|]. split; [exact Htail|].
  split; [exact Htransparent|].
  change (denote_side r = [1;1] *> copies (word_bits P.W0011) a *>
    side_bits header *> count_bits P.W001111 (P.ds_list xs) *>
    denote_side tail).
  rewrite Hstrip, Hconsume, Hheaderden, Hcollectden.
  cbn [List.map sym_of_bool]. reflexivity.
Qed.

Lemma Bnd_frame_header x y a ns u v :
  header_pass x y ->
  (forall l, l {{F}}> u -[tm]->* l <{{B}} [1] *> v) ->
  T.Bnd a (x *> T.RGroups ns u) -[tm]->*
  T.Bnd (S a) (x *> T.RGroups ns v).
Proof.
  intros [HF HB] Hlocal.
  follow T.Bnd_launch. follow HF. follow T.FR_groups. follow Hlocal.
  follow T.BL_groups. follow HB. follow T.BL_0110_1. apply T.Bnd_close.
Qed.

Lemma Bnd_frame_run_header x y a ns n u v :
  header_pass x y ->
  (forall l, l {{F}}> u -[tm]->* l <{{B}} [1] *> v) ->
  T.Bnd a (x *> T.RGroups ns (T.X^^n *> u)) -[tm]->*
  T.Bnd (S a) (x *> T.RGroups ns (T.X^^n *> v)).
Proof.
  intros [HF HB] Hlocal.
  follow T.Bnd_launch. follow HF. follow T.FR_chain. follow Hlocal.
  follow T.BL_chain. follow HB. follow T.BL_0110_1. apply T.Bnd_close.
Qed.

Lemma Bnd_delete_one_run_header x y a ns n p r :
  header_pass x y ->
  T.Bnd a (x *> T.RGroups ns
    (T.X^^n *> [1]^^p *> [0;1] *> r)) -[tm]->*
  T.Bnd (S a) (x *> T.RGroups ns
    (T.X^^n *> [1]^^p *> [0] *> r)).
Proof.
  intro Hheader. eapply Bnd_frame_run_header; [exact Hheader|].
  intro l. apply T.local_delete_one.
Qed.

Lemma Bnd_delete_ones_run_header k x y a ns n p r :
  header_pass x y ->
  T.Bnd a (x *> T.RGroups ns
    (T.X^^n *> [1]^^p *> [0] *> [1]^^k *> r)) -[tm]->*
  T.Bnd (k+a) (x *> T.RGroups ns
    (T.X^^n *> [1]^^p *> [0] *> r)).
Proof.
  intro Hheader. revert a. induction k as [|k IH]; intro a; cbn.
  - finish.
  - follow (Bnd_delete_one_run_header x y a ns n p ([1]^^k *> r) Hheader).
    follow IH. replace (k + S a) with (S k + a) by lia. finish.
Qed.

Lemma Bnd_minor1_header x y a ns s n r :
  header_pass x y ->
  T.Bnd a (x *> T.RGroups ns
    (T.X^^(S s) *> [1;0] *> T.X^^(S n) *>
      [1;1;1;0;1] *> T.X *> r)) -[tm]->*
  T.Bnd (8+a) (x *> T.RGroups ns
    (T.X^^(S s) *> [0] *> T.X^^n *> [1;1;1;0] *> T.X *> r)).
Proof.
  intro Hheader. eapply evstep_trans.
  - eapply Bnd_frame_header; [exact Hheader|]. intro l. apply T.local_minor1.
  - eapply evstep_trans.
    + apply (Bnd_delete_ones_run_header 7 x y (S a) ns (S s) 0
        (T.X^^n *> [1;1;1;0] *> T.X *> r) Hheader).
    + replace (7 + S a) with (8+a) by lia. finish.
Qed.

Lemma Bnd_minor2_header x y a ns s n r :
  header_pass x y ->
  T.Bnd a (x *> T.RGroups ns
    (T.X^^(S s) *> [1;1;0] *> T.X^^(S n) *>
      [1;1;1;0;1;1] *> T.X *> r)) -[tm]->*
  T.Bnd (8+a) (x *> T.RGroups ns
    (T.X^^(S s) *> [1;0] *> T.X^^n *> [1;1;1;0;1] *> T.X *> r)).
Proof.
  intro Hheader. eapply evstep_trans.
  - eapply Bnd_frame_header; [exact Hheader|]. intro l. apply T.local_minor2.
  - eapply evstep_trans.
    + apply (Bnd_delete_ones_run_header 7 x y (S a) ns (S s) 1
        (T.X^^n *> [1;1;1;0;1] *> T.X *> r) Hheader).
    + replace (7 + S a) with (8+a) by lia. finish.
Qed.

Lemma Bnd_minor3_header x y a ns s n r :
  header_pass x y ->
  T.Bnd a (x *> T.RGroups ns
    (T.X^^(S s) *> [1;1;1;0] *> T.X^^(S n) *>
      [1;1;1;0;1;1;1] *> T.X *> r)) -[tm]->*
  T.Bnd (8+a) (x *> T.RGroups ns
    (T.X^^(S s) *> [1;1;0] *> T.X^^n *>
      [1;1;1;0;1;1] *> T.X *> r)).
Proof.
  intro Hheader. eapply evstep_trans.
  - eapply Bnd_frame_header; [exact Hheader|]. intro l. apply T.local_minor3.
  - eapply evstep_trans.
    + apply (Bnd_delete_ones_run_header 7 x y (S a) ns (S s) 2
        (T.X^^n *> [1;1;1;0;1;1] *> T.X *> r) Hheader).
    + replace (7 + S a) with (8+a) by lia. finish.
Qed.

Lemma Bnd_transfer1_header hx hy a ls x r0 rs z p k r :
  header_pass hx hy ->
  T.Bnd a (hx *> T.RGroups ls
    (T.X^^(S x) *> [1;1;0] *>
      T.RGroups ((S r0)::rs)
        (T.X^^z *> [1]^^p *> [0;1] *> [1]^^k *> r))) -[tm]->*
  T.Bnd (S a) (hx *> T.RGroups ls
    (T.X^^(S x) *> [1;0] *> [1]^^7 *>
      T.RGroups (r0::rs)
        (T.X^^z *> [1]^^p *> [0] *> [1]^^k *> r))).
Proof.
  intros [HF HB].
  follow T.Bnd_launch. follow HF. follow T.FR_chain.
  follow T.local_minor2_start. fold T.RGroups.
  eapply evstep_trans. 1: apply (T.FR_chain (r0::rs) z).
  eapply evstep_trans. 1: apply (T.local_delete_one p).
  eapply evstep_trans. 1: apply (T.BL_chain (r0::rs) z).
  eapply evstep_trans. 1: apply (T.local_minor2_finish x).
  eapply evstep_trans. 1: apply (T.BL_groups ls).
  follow HB. eapply evstep_trans. 1: apply (T.BL_0110_1 a).
  apply T.Bnd_close.
Qed.

Lemma Bnd_transfer2_header hx hy a ls x r0 rs z p k r :
  header_pass hx hy ->
  T.Bnd a (hx *> T.RGroups ls
    (T.X^^(S x) *> [1;0] *>
      T.RGroups ((S r0)::rs)
        (T.X^^z *> [1]^^p *> [0;1] *> [1]^^k *> r))) -[tm]->*
  T.Bnd (S a) (hx *> T.RGroups ls
    (T.X^^(S x) *> [0] *> [1]^^7 *>
      T.RGroups (r0::rs)
        (T.X^^z *> [1]^^p *> [0] *> [1]^^k *> r))).
Proof.
  intros [HF HB].
  follow T.Bnd_launch. follow HF. follow T.FR_chain.
  follow T.local_minor1_start. fold T.RGroups.
  eapply evstep_trans. 1: apply (T.FR_chain (r0::rs) z).
  eapply evstep_trans. 1: apply (T.local_delete_one p).
  eapply evstep_trans. 1: apply (T.BL_chain (r0::rs) z).
  eapply evstep_trans. 1: apply (T.local_minor1_finish x).
  eapply evstep_trans. 1: apply (T.BL_groups ls).
  follow HB. eapply evstep_trans. 1: apply (T.BL_0110_1 a).
  apply T.Bnd_close.
Qed.

Lemma Bnd_transfer3_header hx hy a ls y x r0 rs z p k r :
  header_pass hx hy ->
  T.Bnd a (hx *> T.RGroups ls
    (T.X^^y *> T.Sep *> T.X^^(S x) *> [0] *>
      T.RGroups ((S r0)::rs)
        (T.X^^z *> [1]^^p *> [0;1] *> [1]^^k *> r))) -[tm]->*
  T.Bnd (S a) (hx *> T.RGroups ls
    (T.X^^y *> [1;1;1;0;1;1;1] *> T.X^^(S x) *> T.Sep *>
      T.RGroups (r0::rs)
        (T.X^^z *> [1]^^p *> [0] *> [1]^^k *> r))).
Proof.
  intros [HF HB].
  follow T.Bnd_launch. follow HF.
  eapply evstep_trans. 1: apply (T.FR_groups ls).
  eapply evstep_trans. 1: apply (T.FR_group y).
  eapply evstep_trans. 1: apply (T.FR_001111 (S x)).
  follow T.local_transfer3_start.
  eapply evstep_trans. 1: apply (T.FR_chain (r0::rs) z).
  eapply evstep_trans. 1: apply (T.local_delete_one p).
  eapply evstep_trans. 1: apply (T.BL_chain (r0::rs) z).
  follow T.local_transfer3_turn.
  eapply evstep_trans. 1: apply (T.CL_011011_1111 (S x)).
  follow T.local_transfer3_finish.
  eapply evstep_trans. 1: apply (T.BL_chain ls y).
  follow HB. eapply evstep_trans. 1: apply (T.BL_0110_1 a).
  apply T.Bnd_close.
Qed.

Lemma Bnd_transfer4_header hx hy a ls y x ns z p k r :
  header_pass hx hy ->
  T.Bnd a (hx *> T.RGroups ls
    (T.X^^y *> [1;1;1;0] *> T.X^^(S x) *> T.Sep *>
      T.RGroups ns (T.X^^z *> [1]^^p *> [0;1] *> [1]^^k *> r)))
    -[tm]->*
  T.Bnd (S a) (hx *> T.RGroups ls
    (T.X^^y *> [1;1;0;1;1;1;1;1;1;1] *>
      T.RGroups (x::ns)
        (T.X^^z *> [1]^^p *> [0] *> [1]^^k *> r))).
Proof.
  intros [HF HB].
  follow T.Bnd_launch. follow HF.
  eapply evstep_trans. 1: apply (T.FR_groups ls).
  eapply evstep_trans. 1: apply (T.FR_001111 y).
  follow T.local_transfer4_start.
  eapply evstep_trans. 1: apply (T.FR_chain (x::ns) z).
  eapply evstep_trans. 1: apply (T.local_delete_one p).
  eapply evstep_trans. 1: apply (T.BL_chain (x::ns) z).
  follow T.local_transfer4_finish.
  eapply evstep_trans. 1: apply (T.BL_chain ls y).
  follow HB. eapply evstep_trans. 1: apply (T.BL_0110_1 a).
  apply T.Bnd_close.
Qed.

Lemma Bnd_transfer28_header hx hy a ls y x r0 rs z p k r :
  header_pass hx hy ->
  T.Bnd a (hx *> T.RGroups ls
    (T.X^^y *> T.Sep *> T.X^^(S (S x)) *> [1;1;0] *> [1]^^7 *>
      T.RGroups (S (S (S (S r0)))::rs)
        (T.X^^z *> [1]^^p *> [0;1] *> [1]^^(3+k) *> r))) -[tm]->*
  T.Bnd (28+a) (hx *> T.RGroups ls
    (T.X^^y *> [1;1;0;1;1;1;1;1;1;1] *>
      T.RGroups (S x::S r0::rs)
        (T.X^^z *> [1]^^p *> [0] *> [1]^^k *> r))).
Proof.
  intro Hheader.
  eapply evstep_trans.
  - rewrite <- T.RGroups_snoc.
    apply (Bnd_delete_ones_run_header 7 hx hy a (ls++[y])
      (S (S x)) 2
      (T.RGroups (S (S (S (S r0)))::rs)
        (T.X^^z *> [1]^^p *> [0;1] *> [1]^^(3+k) *> r)) Hheader).
  - eapply evstep_trans.
    + cbn.
      apply (Bnd_transfer1_header hx hy (7+a) (ls++[y]) (S x)
        (S (S (S r0))) rs z p (3+k) r Hheader).
    + eapply evstep_trans.
      * apply (Bnd_delete_ones_run_header 7 hx hy (S (7+a))
          (ls++[y]) (S (S x)) 1
          (T.RGroups (S (S (S r0))::rs)
            (T.X^^z *> [1]^^p *> [0] *> [1]^^(3+k) *> r)) Hheader).
      * eapply evstep_trans.
        -- cbn.
           apply (Bnd_transfer2_header hx hy (7 + S (7+a)) (ls++[y])
             (S x) (S (S r0)) rs z p (2+k) r Hheader).
        -- eapply evstep_trans.
           ++ cbn.
              apply (Bnd_delete_ones_run_header 7 hx hy
                (S (7 + S (7+a))) (ls++[y]) (S (S x)) 0
                (T.RGroups (S (S r0)::rs)
                  (T.X^^z *> [1]^^p *> [0] *> [1]^^(2+k) *> r))
                Hheader).
           ++ eapply evstep_trans.
              ** rewrite T.RGroups_snoc. cbn.
                 apply (Bnd_transfer3_header hx hy
                   (7 + S (7 + S (7+a))) ls y (S x) (S r0) rs z p
                   (1+k) r Hheader).
              ** eapply evstep_trans.
                 --- cbn.
                     apply (Bnd_delete_ones_run_header 3 hx hy
                       (S (7 + S (7 + S (7+a)))) ls y 3
                       (T.X^^(S (S x)) *> T.Sep *>
                         T.RGroups (S r0::rs)
                           (T.X^^z *> [1]^^p *> [0] *> [1]^^(1+k) *> r))
                       Hheader).
                 --- eapply evstep_trans.
                     +++ cbn.
                         apply (Bnd_transfer4_header hx hy
                           (3 + S (7 + S (7 + S (7+a))))
                           ls y (S x) (S r0::rs) z p k r Hheader).
                     +++ replace
                           (S (3 + S (7 + S (7 + S (7+a)))))
                           with (28+a) by lia.
                         finish.
Qed.

Lemma take_ones_eq bits n rest :
  P.take_ones bits = (n,rest) -> bits = P.ones n ++ rest.
Proof.
  revert n rest. induction bits as [|b bits IH]; intros n rest E.
  - cbn [P.take_ones] in E. inversion E. reflexivity.
  - destruct b.
    + cbn [P.take_ones] in E.
      destruct (P.take_ones bits) as [n' rest'] eqn:Erec.
      inversion E; subst n rest.
      change (true :: bits = true :: (P.ones n' ++ rest')). f_equal.
      apply IH. reflexivity.
    + cbn [P.take_ones] in E. inversion E. reflexivity.
Qed.

Lemma take_ones_spec bits :
  let '(n,rest) := P.take_ones bits in bits = P.ones n ++ rest.
Proof.
  destruct (P.take_ones bits) as [n rest] eqn:E.
  apply take_ones_eq. exact E.
Qed.

Lemma map_ones n :
  List.map sym_of_bool (P.ones n) = [1]^^n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (1 :: List.map sym_of_bool (P.ones n) = 1 :: [1]^^n).
    f_equal. exact IH.
Qed.

Lemma N_to_nat_le a b : (a <= b)%N -> N.to_nat a <= N.to_nat b.
Proof.
  intro H. apply Nat.compare_le_iff.
  rewrite <- N2Nat.inj_compare. apply N.compare_le_iff. exact H.
Qed.

Lemma ds_unsnoc_forall {A : N -> Prop} s s' x :
  List.Forall A (P.ds_list s) -> P.ds_unsnoc s = Some (s',x) ->
  List.Forall A (P.ds_list s') /\ A x.
Proof.
  intros Hall E. pose proof (ds_unsnoc_ok s) as Hlist.
  rewrite E in Hlist. rewrite Hlist in Hall. apply Forall_app in Hall.
  destruct Hall as [Hprefix Hlast]. inversion Hlast; auto.
Qed.

Lemma ds_unsnoc_prefix_nonempty s s' x :
  valid_dseq s -> P.ds_at_least_two s = true ->
  P.ds_unsnoc s = Some (s',x) -> P.ds_list s' <> [].
Proof.
  intros Hvalid Htwo E Hnil.
  apply ds_at_least_two_spec in Htwo.
  pose proof (valid_dseq_len s Hvalid) as Hlen.
  pose proof (ds_unsnoc_ok s) as Hlist. rewrite E, Hnil in Hlist.
  rewrite Hlist in Hlen. cbn in Hlen. lia.
Qed.

Lemma ds_uncons_tail_nonempty s x s' :
  valid_dseq s -> P.ds_at_least_two s = true ->
  P.ds_uncons s = Some (x,s') -> P.ds_list s' <> [].
Proof.
  intros Hvalid Htwo E Hnil.
  apply ds_at_least_two_spec in Htwo.
  pose proof (valid_dseq_len s Hvalid) as Hlen.
  pose proof (ds_uncons_ok s) as Hlist. rewrite E, Hnil in Hlist.
  rewrite Hlist in Hlen. cbn in Hlen. lia.
Qed.

Lemma phase_counts_spec bits p k :
  P.phase_counts bits = Some (p,k) ->
  bits = P.ones p ++ false :: P.ones k /\ 1 <= k.
Proof.
  unfold P.phase_counts.
  destruct (P.take_ones bits) as [p' rest] eqn:Eprefix.
  pose proof (take_ones_spec bits) as Hprefix. rewrite Eprefix in Hprefix.
  destruct rest as [|b suffix]; [discriminate|].
  destruct b; [discriminate|].
  destruct (P.take_ones suffix) as [k' tail] eqn:Esuffix.
  pose proof (take_ones_spec suffix) as Hsuffix. rewrite Esuffix in Hsuffix.
  destruct k' as [|k']; [discriminate|].
  destruct tail as [|b tail]; [|discriminate].
  intro E. inversion E; subst p k. split; [|lia].
  rewrite app_nil_r in Hsuffix. rewrite Hprefix, Hsuffix. reflexivity.
Qed.

Lemma make_boundary_right_bits a header xs tail :
  valid_dseq xs ->
  side_bits (P.make_boundary_right a header xs tail) =
    [1;1] ++ copies (word_bits P.W0011) a ++ side_bits header ++
    count_bits P.W001111 (P.ds_list xs) ++ side_bits tail.
Proof.
  intro Hxs. unfold P.make_boundary_right.
  rewrite side_bits_push_lit, side_bits_push_run, side_bits_app,
    side_bits_push_sequence by exact Hxs.
  cbn [List.map sym_of_bool]. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma make_boundary_right_valid a header xs tail :
  valid_side header -> valid_dseq xs ->
  List.Forall positive_count (P.ds_list xs) -> valid_side tail ->
  valid_side (P.make_boundary_right a header xs tail).
Proof.
  intros Hheader Hxs Hpos Htail. unfold P.make_boundary_right.
  apply valid_push_lit, valid_push_run.
  unfold valid_side in *. rewrite Forall_app. split; [exact Hheader|].
  apply valid_push_sequence; assumption.
Qed.

Lemma count_bits_last w prefix n :
  count_bits w (prefix ++ [n]) =
    rgroup_bits w prefix ++ copies (word_bits w) n.
Proof.
  destruct prefix as [|x prefix].
  - reflexivity.
  - rewrite count_bits_snoc by discriminate.
    rewrite rgroup_bits_count by discriminate.
    repeat rewrite app_assoc. reflexivity.
Qed.

Lemma Bnd_count_bits a header prefix n tail :
  T.Bnd (N.to_nat a)
    (side_bits header *>
      T.RGroups (List.map N.to_nat prefix)
        (T.X^^(N.to_nat n) *> tail)) =
  0inf <{{C}} [1;1] *> copies (word_bits P.W0011) a *>
    side_bits header *> count_bits P.W001111 (prefix ++ [n]) *> tail.
Proof.
  unfold T.Bnd. rewrite RGroups_stream, count_bits_last.
  unfold copies, word_bits, T.X.
  cbn [P.spelling sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_side_make_boundary a header xs tail :
  valid_dseq xs ->
  denote_side (P.make_boundary_right a header xs tail) =
  [1;1] *> copies (word_bits P.W0011) a *> side_bits header *>
    count_bits P.W001111 (P.ds_list xs) *> denote_side tail.
Proof.
  intro Hxs. unfold denote_side at 1.
  rewrite make_boundary_right_bits by exact Hxs.
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_make_boundary a header xs prefix n tail inc :
  valid_dseq xs -> P.ds_list xs = prefix ++ [n] ->
  denote_machine (P.machine P.C P.L []
    (P.make_boundary_right a header xs tail) inc) =
  T.Bnd (N.to_nat a)
    (side_bits header *>
      T.RGroups (List.map N.to_nat prefix)
        (T.X^^(N.to_nat n) *> denote_side tail)).
Proof.
  intros Hxs Hlist.
  change (denote_side [] <{{C}}
    denote_side (P.make_boundary_right a header xs tail) =
    T.Bnd (N.to_nat a)
      (side_bits header *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat n) *> denote_side tail))).
  rewrite denote_side_make_boundary by exact Hxs. rewrite Hlist.
  rewrite Bnd_count_bits. unfold denote_side at 1. cbn [side_bits].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_parsed_boundary m p prefix n :
  valid_machine m -> P.parse_boundary_prefix m = Some p ->
  P.ds_list (P.bp_xs p) = prefix ++ [n] ->
  denote_machine m =
  T.Bnd (N.to_nat (P.bp_a p))
    (side_bits (P.bp_header p) *>
      T.RGroups (List.map N.to_nat prefix)
        (T.X^^(N.to_nat n) *> denote_side (P.bp_tail p))).
Proof.
  intros Hvalid Eparse Hlist.
  pose proof (parse_boundary_prefix_spec m p Hvalid Eparse)
    as [Hq [Hd [Hl [_ [_ [_ [_ [_ [_ Hbits]]]]]]]]].
  destruct m as [q d left right inc].
  cbn [P.m_state P.m_dir P.m_left P.m_right] in Hq,Hd,Hl,Hbits.
  subst q d left.
  change (denote_side [] <{{C}} denote_side right =
    T.Bnd (N.to_nat (P.bp_a p))
      (side_bits (P.bp_header p) *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat n) *> denote_side (P.bp_tail p)))).
  rewrite Hbits, Hlist, Bnd_count_bits.
  unfold denote_side at 1. cbn [side_bits].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_lit_phase bits tail p k :
  P.phase_counts bits = Some (p,k) ->
  denote_side (P.Lit bits :: tail) =
    [1]^^p *> [0] *> [1]^^k *> denote_side tail.
Proof.
  intro E. pose proof (phase_counts_spec bits p k E) as [Hbits _].
  unfold denote_side at 1. cbn [side_bits block_bits]. rewrite Hbits.
  rewrite map_app, map_ones. cbn [List.map sym_of_bool]. rewrite map_ones.
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_lit_phase_form p k tail :
  denote_side (P.Lit (P.ones p ++ [false] ++ P.ones k) :: tail) =
    [1]^^p *> [0] *> [1]^^k *> denote_side tail.
Proof.
  unfold denote_side. cbn [side_bits block_bits].
  rewrite !map_app, !map_ones. cbn [List.map sym_of_bool].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_lit_marker p tail :
  denote_side (P.Lit (P.ones p ++ [false]) :: tail) =
    [1]^^p *> [0] *> denote_side tail.
Proof.
  unfold denote_side. cbn [side_bits block_bits].
  rewrite map_app, map_ones. cbn [List.map sym_of_bool].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma apply_boundary_delete_sound m m' :
  valid_machine m -> P.apply_boundary_delete m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_delete in E.
  destruct (P.parse_boundary_prefix m) as [p|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p Hvalid Eparse)
    as Hspec.
  destruct p as [a header xs boundary_tail]. cbn in *.
  destruct Hspec as [_ [_ [_ [Hheader [Hxs [Hpos [Hlen
    [Hboundary [Htransparent Hbits]]]]]]]]].
  destruct boundary_tail as [|block tail]; [discriminate|].
  destruct block as [bits|w q|w qs]; try discriminate.
  destruct (P.phase_counts bits) as [[leading k]|] eqn:Ephase;
    [|discriminate].
  destruct (match tail with
            | [] => true
            | b :: _ => P.zero_leading b
            end) eqn:Ezero; [|discriminate].
  inversion E; subst m'; clear E.
  assert (Hnonempty : P.ds_list xs <> []).
  { apply valid_dseq_nonempty; assumption. }
  destruct (exists_last Hnonempty) as [prefix [n Hlist]].
  assert (Hsource : denote_machine m =
    T.Bnd (N.to_nat a)
      (side_bits header *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat n) *>
            denote_side (P.Lit bits :: tail)))).
  { apply (denote_parsed_boundary m
      {| P.bp_a:=a; P.bp_header:=header; P.bp_xs:=xs;
         P.bp_tail:=P.Lit bits::tail |} prefix n Hvalid Eparse Hlist). }
  assert (Htarget :
    denote_machine
      (P.machine P.C P.L []
        (P.make_boundary_right (a + N.of_nat k)%N header xs
          (P.Lit (P.ones leading ++ [false]) :: tail))
        (P.m_incs m)) =
    T.Bnd (N.to_nat (a + N.of_nat k)%N)
      (side_bits header *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat n) *>
            denote_side (P.Lit (P.ones leading ++ [false]) :: tail)))).
  { eapply denote_make_boundary; eassumption. }
  rewrite Hsource.
  change (T.Bnd (N.to_nat a)
    (side_bits header *>
      T.RGroups (List.map N.to_nat prefix)
        (T.X^^(N.to_nat n) *> denote_side (P.Lit bits :: tail)))
    -[tm]->*
    denote_machine
      (P.machine P.C P.L []
        (P.make_boundary_right (a + N.of_nat k)%N header xs
          (P.Lit (P.ones leading ++ [false]) :: tail))
        (P.m_incs m))).
  rewrite Htarget, (denote_lit_phase bits tail leading k Ephase),
    denote_lit_marker.
  destruct Htransparent as [hy Hpass].
  replace (N.to_nat (a + N.of_nat k)%N) with (k + N.to_nat a).
  2: { rewrite N2Nat.inj_add, Nat2N.id. lia. }
  apply (Bnd_delete_ones_run_header k (side_bits header) hy
    (N.to_nat a) (List.map N.to_nat prefix) (N.to_nat n) leading
    (denote_side tail) Hpass).
Qed.

Lemma apply_boundary_delete_valid m m' :
  valid_machine m -> P.apply_boundary_delete m = Some m' ->
  valid_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_delete in E.
  destruct (P.parse_boundary_prefix m) as [p|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p Hvalid Eparse)
    as [_ [_ [_ [Hheader [Hxs [Hpos [_ [Hboundary _]]]]]]]].
  destruct p as [a header xs boundary_tail]. cbn in *.
  destruct boundary_tail as [|block tail]; [discriminate|].
  destruct block as [bits|w q|w qs]; try discriminate.
  destruct (P.phase_counts bits) as [[leading k]|] eqn:Ephase;
    [|discriminate].
  destruct (match tail with
            | [] => true
            | b :: _ => P.zero_leading b
            end); [|discriminate].
  inversion E; subst m'; clear E.
  inversion Hboundary as [|? ? Hlit Htail]; subst.
  change (valid_side [] /\
    valid_side
      (P.make_boundary_right (a + N.of_nat k)%N header xs
        (P.Lit (P.ones leading ++ [false]) :: tail))).
  split; [constructor|]. apply make_boundary_right_valid; try assumption.
  constructor; [destruct leading; discriminate|exact Htail].
Qed.

Lemma literal_minor_left_spec bits k :
  P.literal_minor_left bits = Some k ->
  (k = 1%nat /\ bits = [true;false]) \/
  (k = 2%nat /\ bits = [true;true;false]) \/
  (k = 3%nat /\ bits = [true;true;true;false]).
Proof.
  destruct bits as [|b1 bits]; [cbn [P.literal_minor_left]; discriminate|].
  destruct bits as [|b2 bits];
    [destruct b1; cbn [P.literal_minor_left]; discriminate|].
  destruct bits as [|b3 bits].
  - destruct b1,b2; cbn; intro E; try discriminate;
      inversion E; subst; left; split; reflexivity.
  - destruct bits as [|b4 bits].
    + destruct b1,b2,b3; cbn; intro E; try discriminate;
        inversion E; subst; right; left; split; reflexivity.
    + destruct bits as [|b5 bits].
      * destruct b1,b2,b3,b4; cbn; intro E; try discriminate;
          inversion E; subst; right; right; split; reflexivity.
      * destruct b1,b2,b3,b4,b5; cbn [P.literal_minor_left]; discriminate.
Qed.

Lemma count_bits_positive_head w n ns :
  positive_count n -> exists rest,
  count_bits w (n::ns) = word_bits w ++ rest.
Proof.
  intro Hn. destruct ns as [|m ns].
  - cbn [count_bits]. rewrite (copies_succ_pred (word_bits w) n Hn).
    exists (copies (word_bits w) (N.pred n)). reflexivity.
  - cbn [count_bits]. rewrite (copies_succ_pred (word_bits w) n Hn).
    exists (copies (word_bits w) (N.pred n) ++ [1;1;1;1] ++
      count_bits w (m::ns)).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma boundary_context_X context tail :
  valid_side (context::tail) ->
  (match context with
   | P.Run P.W001111 q => negb (N.eqb q 0)
   | P.Chain P.W001111 _ => true
   | _ => false
   end) = true ->
  exists r, denote_side (context::tail) = T.X *> r.
Proof.
  intros Hvalid Htest.
  inversion Hvalid as [|? ? Hblock Htail]; subst.
  destruct context as [bits|w q|w qs]; try discriminate.
  - destruct w; try discriminate.
    exists (copies (word_bits P.W001111) (N.pred q) *> denote_side tail).
    unfold denote_side at 1. cbn [side_bits block_bits].
    rewrite (copies_succ_pred (word_bits P.W001111) q Hblock).
    unfold T.X. repeat rewrite Str_app_assoc. reflexivity.
  - destruct w; try discriminate.
    destruct Hblock as [Hqs [Hpos Hlen]].
    assert (Hnonempty : P.ds_list qs <> []).
    { apply valid_dseq_nonempty; assumption. }
    destruct (P.ds_list qs) as [|n ns] eqn:Hlist; [contradiction|].
    inversion Hpos as [|? ? Hn Hns]; subst.
    destruct (count_bits_positive_head P.W001111 n ns Hn)
      as [rest Hcount].
    exists ((rest ++ side_bits tail) *> 0inf).
    unfold denote_side at 1. cbn [side_bits block_bits].
    rewrite Hlist.
    transitivity ((word_bits P.W001111 ++ rest ++ side_bits tail) *> 0inf).
    { f_equal. exact (f_equal (fun z => z ++ side_bits tail) Hcount). }
    unfold T.X, word_bits. cbn [P.spelling sym_of_bool List.map].
    repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_minor_blocks left n right context tail :
  denote_side (P.Lit left :: P.Run P.W001111 n ::
    P.Lit right :: context :: tail) =
  List.map sym_of_bool left *> T.X^^(N.to_nat n) *>
    List.map sym_of_bool right *> denote_side (context::tail).
Proof.
  unfold denote_side. cbn [side_bits block_bits].
  unfold copies, word_bits, T.X. cbn [P.spelling sym_of_bool].
  change (List.map sym_of_bool
    [false;false;true;true;true;true]) with ([0;0;1;1;1;1] : list Sym).
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_lit_cons bits tail :
  denote_side (P.Lit bits :: tail) =
  List.map sym_of_bool bits *> denote_side tail.
Proof.
  unfold denote_side. cbn [side_bits block_bits].
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma RGroups_count_bits prefix n tail :
  T.RGroups (List.map N.to_nat prefix)
    (T.X^^(N.to_nat n) *> tail) =
  count_bits P.W001111 (prefix ++ [n]) *> tail.
Proof.
  rewrite RGroups_stream, count_bits_last.
  unfold copies, word_bits, T.X. cbn [P.spelling sym_of_bool].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_push_sequence_last ds prefix n tail :
  valid_dseq ds -> P.ds_list ds = prefix ++ [n] ->
  denote_side (P.push_sequence P.W001111 ds tail) =
  T.RGroups (List.map N.to_nat prefix)
    (T.X^^(N.to_nat n) *> denote_side tail).
Proof.
  intros Hds Hlist. rewrite denote_side_push_sequence by exact Hds.
  rewrite Hlist, RGroups_count_bits. reflexivity.
Qed.

Lemma apply_boundary_minor_sound m m' :
  valid_machine m -> P.apply_boundary_minor m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_minor in E.
  destruct (P.parse_boundary_prefix m) as [p0|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p0 Hvalid Eparse) as Hspec.
  destruct p0 as [a header xs boundary_tail]. cbn in *.
  destruct Hspec as [_ [_ [_ [Hheader [Hxs [Hpos [Hlen
    [Hboundary [Htransparent Hbits]]]]]]]]].
  destruct boundary_tail as [|b0 rest]; cbn in E; try discriminate.
  destruct b0 as [left_phase|w0 q0|w0 qs0]; cbn in E; try discriminate.
  destruct rest as [|b1 rest]; cbn in E; try discriminate.
  destruct b1 as [bits1|w1 n|w1 ns1]; cbn in E; try discriminate.
  destruct w1;
    [solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |idtac
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]].
  destruct rest as [|b2 rest]; cbn in E; try discriminate.
  destruct b2 as [right_phase|w2 q2|w2 qs2]; cbn in E; try discriminate.
  destruct rest as [|context tail]; cbn in E; try discriminate.
  destruct (P.literal_minor_left left_phase) as [phase|] eqn:Eleft;
    [|cbn in E; discriminate].
  change
    ((if (N.leb 2 n &&
         P.bits_eqb right_phase (P.minor_right_bits phase) &&
         match context with
         | P.Run P.W001111 q => negb (N.eqb q 0)
         | P.Chain P.W001111 _ => true
         | _ => false
         end)%bool
     then Some (P.machine P.C P.L []
       (P.make_boundary_right (a + 8)%N header xs
         (P.Lit (P.ones (Nat.pred phase) ++ [false]) ::
          P.Run P.W001111 (N.pred n) ::
          P.Lit (P.minor_right_bits (Nat.pred phase)) :: context :: tail))
       (P.m_incs m))
     else None) = Some m') in E.
  remember (N.leb 2 n &&
            P.bits_eqb right_phase (P.minor_right_bits phase) &&
            match context with
            | P.Run P.W001111 q => negb (N.eqb q 0)
            | P.Chain P.W001111 _ => true
            | _ => false
            end)%bool as guard eqn:Eguard.
  destruct guard.
  2: { discriminate E. }
  inversion E; subst m'; clear E.
  symmetry in Eguard.
  repeat rewrite and_true_iff in Eguard.
  destruct Eguard as [[Hn Hright] Hcontext].
  apply N.leb_le in Hn. apply bits_eqb_eq in Hright.
  pose proof (boundary_context_X context tail) as Hcontext_spec.
  assert (Hcontext_valid : valid_side (context::tail)).
  { inversion Hboundary as [|? ? _ H1]; subst.
    inversion H1 as [|? ? _ H2]; subst.
    inversion H2 as [|? ? _ H3]; subst. exact H3. }
  destruct (Hcontext_spec Hcontext_valid Hcontext) as [r Hcontext_bits].
  assert (Hnonempty : P.ds_list xs <> []).
  { apply valid_dseq_nonempty; assumption. }
  destruct (exists_last Hnonempty) as [prefix [last Hlist]].
  rewrite Hlist in Hpos. apply Forall_app in Hpos.
  destruct Hpos as [Hprefix Hlasts].
  assert (Hlast : positive_count last).
  { inversion Hlasts; assumption. }
  assert (Hlast_nat : N.to_nat last = S (Nat.pred (N.to_nat last))).
  { assert (Hnz : N.to_nat last <> 0%nat).
    { intro Hz. change (N.to_nat last = N.to_nat 0%N) in Hz.
      apply N2Nat.inj in Hz. subst last. exact (N.lt_irrefl 0%N Hlast). }
    lia. }
  assert (Hn_nat : N.to_nat n = S (N.to_nat (N.pred n))).
  { rewrite <- (N.succ_pred n) at 1 by lia.
    rewrite N2Nat.inj_succ. reflexivity. }
  assert (Hsource : denote_machine m =
    T.Bnd (N.to_nat a)
      (side_bits header *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat last) *>
            denote_side (P.Lit left_phase :: P.Run P.W001111 n ::
              P.Lit right_phase :: context :: tail)))).
  { apply (denote_parsed_boundary m
      {| P.bp_a:=a; P.bp_header:=header; P.bp_xs:=xs;
         P.bp_tail:=P.Lit left_phase :: P.Run P.W001111 n ::
           P.Lit right_phase :: context :: tail |}
      prefix last Hvalid Eparse Hlist). }
  set (new_tail :=
    P.Lit (P.ones (Nat.pred phase) ++ [false]) ::
    P.Run P.W001111 (N.pred n) ::
    P.Lit (P.minor_right_bits (Nat.pred phase)) :: context :: tail).
  assert (Htarget :
    denote_machine (P.machine P.C P.L []
      (P.make_boundary_right (a + 8)%N header xs new_tail)
      (P.m_incs m)) =
    T.Bnd (N.to_nat (a + 8)%N)
      (side_bits header *>
        T.RGroups (List.map N.to_nat prefix)
          (T.X^^(N.to_nat last) *> denote_side new_tail))).
  { eapply denote_make_boundary; eassumption. }
  rewrite Hsource.
  change (T.Bnd (N.to_nat a)
    (side_bits header *>
      T.RGroups (List.map N.to_nat prefix)
        (T.X^^(N.to_nat last) *>
          denote_side (P.Lit left_phase :: P.Run P.W001111 n ::
            P.Lit right_phase :: context :: tail))) -[tm]->*
    denote_machine (P.machine P.C P.L []
      (P.make_boundary_right (a + 8)%N header xs new_tail)
      (P.m_incs m))).
  rewrite Htarget. unfold new_tail.
  rewrite !denote_minor_blocks, Hcontext_bits, Hlast_nat, Hn_nat.
  destruct Htransparent as [hy Hpass].
  replace (N.to_nat (a + 8)%N) with (8 + N.to_nat a) by
    (rewrite N2Nat.inj_add; cbn; lia).
  destruct (literal_minor_left_spec left_phase phase Eleft)
    as [[-> ->]|[[-> ->]|[-> ->]]]; subst right_phase;
    cbn [P.ones P.minor_right_bits sym_of_bool List.map Nat.pred].
  - apply (Bnd_minor1_header (side_bits header) hy (N.to_nat a)
      (List.map N.to_nat prefix) (Nat.pred (N.to_nat last))
      (N.to_nat (N.pred n)) r Hpass).
  - apply (Bnd_minor2_header (side_bits header) hy (N.to_nat a)
      (List.map N.to_nat prefix) (Nat.pred (N.to_nat last))
      (N.to_nat (N.pred n)) r Hpass).
  - apply (Bnd_minor3_header (side_bits header) hy (N.to_nat a)
      (List.map N.to_nat prefix) (Nat.pred (N.to_nat last))
      (N.to_nat (N.pred n)) r Hpass).
Qed.

Lemma apply_boundary_minor_valid m m' :
  valid_machine m -> P.apply_boundary_minor m = Some m' ->
  valid_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_minor in E.
  destruct (P.parse_boundary_prefix m) as [p0|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p0 Hvalid Eparse) as Hspec.
  destruct p0 as [a header xs boundary_tail]. cbn in *.
  destruct Hspec as [_ [_ [_ [Hheader [Hxs [Hpos [_ [Hboundary _]]]]]]]].
  destruct boundary_tail as [|b0 rest]; cbn in E; try discriminate.
  destruct b0 as [left_phase|w0 q0|w0 qs0]; cbn in E; try discriminate.
  destruct rest as [|b1 rest]; cbn in E; try discriminate.
  destruct b1 as [bits1|w1 n|w1 ns1]; cbn in E; try discriminate.
  destruct w1;
    [solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |idtac
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]
    |solve [cbn in E; discriminate]].
  destruct rest as [|b2 rest]; cbn in E; try discriminate.
  destruct b2 as [right_phase|w2 q2|w2 qs2]; cbn in E; try discriminate.
  destruct rest as [|context tail]; cbn in E; try discriminate.
  destruct (P.literal_minor_left left_phase) as [phase|] eqn:Eleft;
    [|cbn in E; discriminate].
  change ((if (N.leb 2 n &&
      P.bits_eqb right_phase (P.minor_right_bits phase) &&
      match context with
      | P.Run P.W001111 q => negb (N.eqb q 0)
      | P.Chain P.W001111 _ => true
      | _ => false
      end)%bool
    then Some (P.machine P.C P.L []
      (P.make_boundary_right (a + 8)%N header xs
        (P.Lit (P.ones (Nat.pred phase) ++ [false]) ::
         P.Run P.W001111 (N.pred n) ::
         P.Lit (P.minor_right_bits (Nat.pred phase)) :: context :: tail))
      (P.m_incs m))
    else None) = Some m') in E.
  remember (N.leb 2 n &&
    P.bits_eqb right_phase (P.minor_right_bits phase) &&
    match context with
    | P.Run P.W001111 q => negb (N.eqb q 0)
    | P.Chain P.W001111 _ => true
    | _ => false
    end)%bool as guard eqn:Eguard.
  destruct guard; [|discriminate E].
  inversion E; subst m'; clear E.
  symmetry in Eguard. repeat rewrite and_true_iff in Eguard.
  destruct Eguard as [[Hn _] _]. apply N.leb_le in Hn.
  inversion Hboundary as [|? ? _ H1]; subst.
  inversion H1 as [|? ? _ H2]; subst.
  inversion H2 as [|? ? _ Hcontext_tail]; subst.
  change (valid_side [] /\
    valid_side (P.make_boundary_right (a + 8)%N header xs
      (P.Lit (P.ones (Nat.pred phase) ++ [false]) ::
       P.Run P.W001111 (N.pred n) ::
       P.Lit (P.minor_right_bits (Nat.pred phase)) :: context :: tail))).
  split; [constructor|]. apply make_boundary_right_valid; try assumption.
  constructor.
  - destruct (Nat.pred phase); discriminate.
  - constructor.
    + unfold positive_count. apply N.neq_0_lt_0. intro Hpred.
      apply (f_equal N.to_nat) in Hpred.
      rewrite N2Nat.inj_pred in Hpred. cbn in Hpred.
      pose proof (N_to_nat_le 2 n Hn) as Hnat. cbn in Hnat. lia.
    + constructor.
      * unfold P.minor_right_bits. discriminate.
      * exact Hcontext_tail.
Qed.

Lemma apply_boundary_transfer_sound m m' :
  valid_machine m -> P.apply_boundary_transfer m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_transfer in E.
  destruct (P.parse_boundary_prefix m) as [p0|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p0 Hvalid Eparse) as Hspec.
  destruct p0 as [a header xs boundary_tail]. cbn in *.
  destruct Hspec as [_ [_ [_ [Hheader [Hxs [Hxspos [Hxslen
    [Hboundary [Htransparent Hbits]]]]]]]]].
  destruct boundary_tail as [|marker_block rest];
    [cbn in E; discriminate|].
  destruct marker_block as [marker|wm qm|wm qms];
    [|cbn in E; discriminate|cbn in E; discriminate].
  change ((if (P.bits_eqb marker
      [true;true;false;true;true;true;true;true;true;true] &&
      P.ds_at_least_two xs)%bool
    then match P.ds_unsnoc xs with
         | Some (lhs,x) =>
             if N.leb 2 x then
             match P.collect_chain P.W001111 rest with
             | Some (rhs,after_rhs) =>
                 if P.ds_at_least_two rhs then
                 match P.ds_uncons rhs,after_rhs with
                 | Some (r0,rhs_tail),P.Lit phase_bits::tail =>
                     match P.phase_counts phase_bits with
                     | Some (leading,k) =>
                         if (N.leb 4 r0 && Nat.leb 4 k)%bool then
                           Some (P.machine P.C P.L []
                             (P.make_boundary_right (a + 28)%N header lhs
                               (P.Lit marker ::
                                P.push_sequence P.W001111
                                  (P.ds_cons (N.pred x)
                                    (P.ds_cons (N.sub r0 3) rhs_tail))
                                  (P.Lit (P.ones leading ++ [false] ++
                                    P.ones (k-4)) :: tail)))
                             (P.m_incs m))
                         else None
                     | None => None
                     end
                 | _,_ => None
                 end
             else None
             | None => None
             end
             else None
         | None => None
         end
    else None) = Some m') in E.
  remember (P.bits_eqb marker
      [true;true;false;true;true;true;true;true;true;true] &&
      P.ds_at_least_two xs)%bool as outer_guard eqn:Eouter.
  destruct outer_guard; [|discriminate E].
  symmetry in Eouter. apply Bool.andb_true_iff in Eouter.
  destruct Eouter as [Hmarker Hxstwo]. apply bits_eqb_eq in Hmarker.
  destruct (P.ds_unsnoc xs) as [[lhs x]|] eqn:Eunsnoc;
    [|discriminate E].
  remember (N.leb 2 x) as x_guard eqn:Exguard.
  destruct x_guard; [|discriminate E].
  symmetry in Exguard. apply N.leb_le in Exguard.
  destruct (P.collect_chain P.W001111 rest)
    as [[rhs after_rhs]|] eqn:Ecollect; [|discriminate E].
  assert (Hrest : valid_side rest).
  { inversion Hboundary; subst. assumption. }
  pose proof (collect_chain_spec P.W001111 rest rhs after_rhs
    Hrest Ecollect) as [Hrhs [Hrhspos [Hrhslen [Hafter Hcollect]]]].
  remember (P.ds_at_least_two rhs) as rhs_guard eqn:Erhstwo.
  destruct rhs_guard; [|discriminate E].
  symmetry in Erhstwo.
  destruct (P.ds_uncons rhs) as [[r0 rhs_tail]|] eqn:Euncons;
    [|discriminate E].
  destruct after_rhs as [|phase_block tail]; [discriminate E|].
  destruct phase_block as [phase_bits|wp qp|wp qps];
    [|discriminate E|discriminate E].
  destruct (P.phase_counts phase_bits) as [[leading k]|] eqn:Ephase;
    [|discriminate E].
  remember (N.leb 4 r0 && Nat.leb 4 k)%bool
    as final_guard eqn:Efinal.
  destruct final_guard; [|discriminate E].
  inversion E; subst m'; clear E.
  symmetry in Efinal. apply Bool.andb_true_iff in Efinal.
  destruct Efinal as [Hr0 Hk].
  apply N.leb_le in Hr0. apply Nat.leb_le in Hk.

  pose proof (ds_unsnoc_valid xs lhs x Hxs Eunsnoc) as Hlhs.
  pose proof (ds_unsnoc_forall xs lhs x Hxspos Eunsnoc)
    as [Hlhspos Hxpos].
  pose proof (ds_unsnoc_prefix_nonempty xs lhs x Hxs Hxstwo Eunsnoc)
    as Hlhsnonempty.
  destruct (exists_last Hlhsnonempty) as [lsN [y Hlhslist]].
  pose proof (ds_uncons_valid rhs r0 rhs_tail Hrhs Euncons) as Hrtail.
  pose proof (ds_uncons_forall rhs r0 rhs_tail Hrhspos Euncons)
    as [Hr0pos Hrtailpos].
  pose proof (ds_uncons_tail_nonempty rhs r0 rhs_tail Hrhs Erhstwo Euncons)
    as Hrtailnonempty.
  destruct (exists_last Hrtailnonempty) as [rsN [z Hrtlist]].
  pose proof (ds_unsnoc_ok xs) as Hxslist. rewrite Eunsnoc in Hxslist.
  pose proof (ds_uncons_ok rhs) as Hrhslist. rewrite Euncons in Hrhslist.
  rewrite Hrtlist in Hrhslist.

  assert (Hsource : denote_machine m =
    T.Bnd (N.to_nat a)
      (side_bits header *>
        T.RGroups (List.map N.to_nat (P.ds_list lhs))
          (T.X^^(N.to_nat x) *>
            denote_side (P.Lit marker :: rest)))).
  { apply (denote_parsed_boundary m
      {| P.bp_a:=a; P.bp_header:=header; P.bp_xs:=xs;
         P.bp_tail:=P.Lit marker::rest |}
      (P.ds_list lhs) x Hvalid Eparse Hxslist). }
  assert (Hcollectden : denote_side rest =
    count_bits P.W001111 (P.ds_list rhs) *>
      denote_side (P.Lit phase_bits :: tail)).
  { unfold denote_side. rewrite Hcollect.
    repeat rewrite Str_app_assoc. reflexivity. }
  assert (Hrestden : denote_side rest =
    T.RGroups (N.to_nat r0 :: List.map N.to_nat rsN)
      (T.X^^(N.to_nat z) *>
        [1]^^leading *> [0] *> [1]^^k *> denote_side tail)).
  { rewrite Hcollectden, Hrhslist.
    change (count_bits P.W001111 ((r0::rsN) ++ [z]) *>
      denote_side (P.Lit phase_bits :: tail) =
      T.RGroups (N.to_nat r0 :: List.map N.to_nat rsN)
        (T.X^^(N.to_nat z) *>
          [1]^^leading *> [0] *> [1]^^k *> denote_side tail)).
    transitivity (T.RGroups (N.to_nat r0 :: List.map N.to_nat rsN)
      (T.X^^(N.to_nat z) *> denote_side (P.Lit phase_bits :: tail))).
    { symmetry. exact (RGroups_count_bits (r0::rsN) z
        (denote_side (P.Lit phase_bits :: tail))). }
    rewrite (denote_lit_phase phase_bits tail leading k Ephase).
    reflexivity. }

  set (rhs' := P.ds_cons (N.pred x)
    (P.ds_cons (N.sub r0 3) rhs_tail)).
  assert (Hrhs' : valid_dseq rhs').
  { apply ds_cons_valid, ds_cons_valid. exact Hrtail. }
  assert (Hrhs'list : P.ds_list rhs' =
    (N.pred x) :: (N.sub r0 3) :: rsN ++ [z]).
  { unfold rhs'. rewrite !ds_list_cons, Hrtlist. reflexivity. }
  set (phase' := P.Lit (P.ones leading ++ [false] ++
    P.ones (k-4)) :: tail).
  assert (Hsequenceden :
    denote_side (P.push_sequence P.W001111 rhs' phase') =
    T.RGroups (N.to_nat (N.pred x) :: N.to_nat (N.sub r0 3) ::
      List.map N.to_nat rsN)
      (T.X^^(N.to_nat z) *> denote_side phase')).
  { apply (denote_push_sequence_last rhs'
      ((N.pred x)::(N.sub r0 3)::rsN) z phase' Hrhs' Hrhs'list). }
  assert (Htarget :
    denote_machine (P.machine P.C P.L []
      (P.make_boundary_right (a + 28)%N header lhs
        (P.Lit marker :: P.push_sequence P.W001111 rhs' phase'))
      (P.m_incs m)) =
    T.Bnd (N.to_nat (a + 28)%N)
      (side_bits header *>
        T.RGroups (List.map N.to_nat lsN)
          (T.X^^(N.to_nat y) *>
            denote_side (P.Lit marker ::
              P.push_sequence P.W001111 rhs' phase')))).
  { apply (denote_make_boundary (a+28)%N header lhs lsN y
      (P.Lit marker :: P.push_sequence P.W001111 rhs' phase')
      (P.m_incs m) Hlhs Hlhslist). }

  pose proof (N_to_nat_le 2 x Exguard) as Hxnat.
  pose proof (N_to_nat_le 4 r0 Hr0) as Hr0nat.
  set (xb := N.to_nat x - 2).
  set (rb := N.to_nat r0 - 4).
  set (kb := k - 4).
  assert (Hx0 : N.to_nat x = S (S xb)) by (unfold xb; cbn in Hxnat; lia).
  assert (Hx1 : N.to_nat (N.pred x) = S xb).
  { rewrite N2Nat.inj_pred, Hx0. reflexivity. }
  assert (Hr00 : N.to_nat r0 = S (S (S (S rb)))) by
    (unfold rb; cbn in Hr0nat; lia).
  assert (Hr01 : N.to_nat (N.sub r0 3) = S rb).
  { rewrite N2Nat.inj_sub, Hr00. reflexivity. }
  assert (Hk0 : k = 4 + kb) by (unfold kb; lia).
  destruct Htransparent as [hy Hpass].

  rewrite Hsource.
  change (T.Bnd (N.to_nat a)
    (side_bits header *>
      T.RGroups (List.map N.to_nat (P.ds_list lhs))
        (T.X^^(N.to_nat x) *> denote_side (P.Lit marker :: rest)))
    -[tm]->*
    denote_machine (P.machine P.C P.L []
      (P.make_boundary_right (a + 28)%N header lhs
        (P.Lit marker :: P.push_sequence P.W001111 rhs' phase'))
      (P.m_incs m))).
  rewrite Htarget, Hlhslist, map_app. cbn [List.map].
  rewrite !T.RGroups_snoc, !denote_lit_cons, Hsequenceden, Hrestden,
    Hmarker, Hx0, Hx1, Hr00, Hr01, Hk0.
  unfold phase'. rewrite denote_lit_phase_form.
  cbn [List.map sym_of_bool].
  replace (N.to_nat (a + 28)%N) with (28 + N.to_nat a) by
    (rewrite N2Nat.inj_add; cbn; lia).
  apply (Bnd_transfer28_header (side_bits header) hy (N.to_nat a)
    (List.map N.to_nat lsN) (N.to_nat y) xb rb
    (List.map N.to_nat rsN) (N.to_nat z) leading kb
    (denote_side tail) Hpass).
Qed.

Lemma N_pred_pos2 n : (2 <= n)%N -> positive_count (N.pred n).
Proof.
  intro H. unfold positive_count. apply N.neq_0_lt_0. intro E.
  apply (f_equal N.to_nat) in E. rewrite N2Nat.inj_pred in E. cbn in E.
  pose proof (N_to_nat_le 2 n H) as Hnat. cbn in Hnat. lia.
Qed.

Lemma N_sub3_pos4 n : (4 <= n)%N -> positive_count (N.sub n 3).
Proof.
  intro H. unfold positive_count. apply N.neq_0_lt_0. intro E.
  apply (f_equal N.to_nat) in E. rewrite N2Nat.inj_sub in E. cbn in E.
  pose proof (N_to_nat_le 4 n H) as Hnat. cbn in Hnat. lia.
Qed.

Lemma transfer_output_valid a header lhs marker x r0 rhs_tail leading k tail inc :
  valid_side header -> valid_dseq lhs ->
  List.Forall positive_count (P.ds_list lhs) ->
  marker <> [] -> (2 <= x)%N -> (4 <= r0)%N ->
  valid_dseq rhs_tail ->
  List.Forall positive_count (P.ds_list rhs_tail) -> valid_side tail ->
  valid_machine (P.machine P.C P.L []
    (P.make_boundary_right (a + 28)%N header lhs
      (P.Lit marker ::
       P.push_sequence P.W001111
         (P.ds_cons (N.pred x) (P.ds_cons (N.sub r0 3) rhs_tail))
         (P.Lit (P.ones leading ++ [false] ++ P.ones (k-4)) :: tail)))
    inc).
Proof.
  intros Hheader Hlhs Hlhspos Hmarker Hx Hr0 Hrtail Hrtailpos Htail.
  change (valid_side [] /\ valid_side
    (P.make_boundary_right (a + 28)%N header lhs
      (P.Lit marker ::
       P.push_sequence P.W001111
         (P.ds_cons (N.pred x) (P.ds_cons (N.sub r0 3) rhs_tail))
         (P.Lit (P.ones leading ++ [false] ++ P.ones (k-4)) :: tail)))).
  split; [constructor|]. apply make_boundary_right_valid; try assumption.
  constructor; [exact Hmarker|].
  apply valid_push_sequence.
  - apply ds_cons_valid, ds_cons_valid. exact Hrtail.
  - rewrite !ds_list_cons. repeat constructor; auto using N_pred_pos2,
      N_sub3_pos4.
  - constructor.
    + intro E. apply app_eq_nil in E as [_ E]. discriminate.
    + exact Htail.
Qed.

Lemma apply_boundary_transfer_valid m m' :
  valid_machine m -> P.apply_boundary_transfer m = Some m' ->
  valid_machine m'.
Proof.
  intros Hvalid E.
  unfold P.apply_boundary_transfer in E.
  destruct (P.parse_boundary_prefix m) as [p0|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_prefix_spec m p0 Hvalid Eparse) as Hspec.
  destruct p0 as [a header xs boundary_tail]. cbn in *.
  destruct Hspec as [_ [_ [_ [Hheader [Hxs [Hxspos [_
    [Hboundary _]]]]]]]].
  destruct boundary_tail as [|marker_block rest];
    [cbn in E; discriminate|].
  destruct marker_block as [marker|wm qm|wm qms];
    [|cbn in E; discriminate|cbn in E; discriminate].
  change ((if (P.bits_eqb marker
      [true;true;false;true;true;true;true;true;true;true] &&
      P.ds_at_least_two xs)%bool
    then match P.ds_unsnoc xs with
         | Some (lhs,x) =>
             if N.leb 2 x then
             match P.collect_chain P.W001111 rest with
             | Some (rhs,after_rhs) =>
                 if P.ds_at_least_two rhs then
                 match P.ds_uncons rhs,after_rhs with
                 | Some (r0,rhs_tail),P.Lit phase_bits::tail =>
                     match P.phase_counts phase_bits with
                     | Some (leading,k) =>
                         if (N.leb 4 r0 && Nat.leb 4 k)%bool then
                           Some (P.machine P.C P.L []
                             (P.make_boundary_right (a + 28)%N header lhs
                               (P.Lit marker ::
                                P.push_sequence P.W001111
                                  (P.ds_cons (N.pred x)
                                    (P.ds_cons (N.sub r0 3) rhs_tail))
                                  (P.Lit (P.ones leading ++ [false] ++
                                    P.ones (k-4)) :: tail)))
                             (P.m_incs m))
                         else None
                     | None => None
                     end
                 | _,_ => None
                 end
             else None
             | None => None
             end
             else None
         | None => None
         end
    else None) = Some m') in E.
  remember (P.bits_eqb marker
      [true;true;false;true;true;true;true;true;true;true] &&
      P.ds_at_least_two xs)%bool as outer_guard eqn:Eouter.
  destruct outer_guard; [|discriminate E].
  symmetry in Eouter. apply Bool.andb_true_iff in Eouter.
  destruct Eouter as [Hmarker Hxstwo]. apply bits_eqb_eq in Hmarker.
  destruct (P.ds_unsnoc xs) as [[lhs x]|] eqn:Eunsnoc;
    [|discriminate E].
  remember (N.leb 2 x) as x_guard eqn:Exguard.
  destruct x_guard; [|discriminate E].
  symmetry in Exguard. apply N.leb_le in Exguard.
  destruct (P.collect_chain P.W001111 rest)
    as [[rhs after_rhs]|] eqn:Ecollect; [|discriminate E].
  assert (Hrest : valid_side rest).
  { inversion Hboundary; subst. assumption. }
  pose proof (collect_chain_spec P.W001111 rest rhs after_rhs
    Hrest Ecollect) as [Hrhs [Hrhspos [_ [Hafter _]]]].
  remember (P.ds_at_least_two rhs) as rhs_guard eqn:Erhstwo.
  destruct rhs_guard; [|discriminate E].
  destruct (P.ds_uncons rhs) as [[r0 rhs_tail]|] eqn:Euncons;
    [|discriminate E].
  destruct after_rhs as [|phase_block tail]; [discriminate E|].
  destruct phase_block as [phase_bits|wp qp|wp qps];
    [|discriminate E|discriminate E].
  destruct (P.phase_counts phase_bits) as [[leading k]|] eqn:Ephase;
    [|discriminate E].
  remember (N.leb 4 r0 && Nat.leb 4 k)%bool
    as final_guard eqn:Efinal.
  destruct final_guard; [|discriminate E].
  inversion E; subst m'; clear E.
  symmetry in Efinal. apply Bool.andb_true_iff in Efinal.
  destruct Efinal as [Hr0 Hk]. apply N.leb_le in Hr0.
  pose proof (ds_unsnoc_valid xs lhs x Hxs Eunsnoc) as Hlhs.
  pose proof (ds_unsnoc_forall xs lhs x Hxspos Eunsnoc)
    as [Hlhspos Hxpos].
  pose proof (ds_uncons_valid rhs r0 rhs_tail Hrhs Euncons) as Hrtail.
  pose proof (ds_uncons_forall rhs r0 rhs_tail Hrhspos Euncons)
    as [Hr0pos Hrtailpos].
  assert (Htail : valid_side tail).
  { inversion Hafter; assumption. }
  apply (transfer_output_valid a header lhs marker x r0 rhs_tail
    leading k tail (P.m_incs m)); try assumption.
  subst marker. discriminate.
Qed.

Lemma apply_boundary_plain_sound m m' :
  valid_machine m -> P.apply_boundary_plain m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_boundary_plain in E.
  destruct (P.apply_boundary_transfer m) as [m1|] eqn:Etransfer.
  - inversion E; subst. eapply apply_boundary_transfer_sound; eassumption.
  - destruct (P.apply_boundary_delete m) as [m2|] eqn:Edelete.
    + inversion E; subst. eapply apply_boundary_delete_sound; eassumption.
    + eapply apply_boundary_minor_sound; eassumption.
Qed.

Lemma apply_boundary_plain_valid m m' :
  valid_machine m -> P.apply_boundary_plain m = Some m' ->
  valid_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_boundary_plain in E.
  destruct (P.apply_boundary_transfer m) as [m1|] eqn:Etransfer.
  - inversion E; subst. eapply apply_boundary_transfer_valid; eassumption.
  - destruct (P.apply_boundary_delete m) as [m2|] eqn:Edelete.
    + inversion E; subst. eapply apply_boundary_delete_valid; eassumption.
    + eapply apply_boundary_minor_valid; eassumption.
Qed.


(* The local evaluator used by [run_h] must be parametric in the tape to the
   left of its isolated suffix.  This is the framed counterpart of
   [denote_machine]; at the top level the frame is [0inf]. *)
Definition denote_side_on (s : P.Side) (z : side) : side :=
  side_bits s *> z.

Definition denote_machine_on (m : P.Machine) (z : side) : state * tape :=
  match P.m_dir m with
  | P.L => denote_side_on (P.m_left m) z
             <{{denote_q (P.m_state m)}} denote_side (P.m_right m)
  | P.R => denote_side_on (P.m_left m) z
             {{denote_q (P.m_state m)}}> denote_side (P.m_right m)
  end.


Lemma pop_bit_on s z :
  valid_side s -> s <> [] ->
  let '(b,s') := P.pop_bit s in
  denote_side_on s z = sym_of_bool b >> denote_side_on s' z.
Proof.
  intros Hvalid Hne. destruct (P.pop_bit s) as [b s'] eqn:E.
  pose proof (pop_bit_bits_nonempty s Hvalid Hne) as H; rewrite E in H.
  unfold denote_side_on. rewrite H. reflexivity.
Qed.

Lemma raw_step_on_sound m m' z :
  valid_machine m -> P.crossed_left_boundary m = false ->
  P.raw_step m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hinside Hstep. destruct d.
  - destruct (P.pop_bit l) as [bit l'] eqn:Epop.
    assert (Hlne : l <> []).
    { intro El. subst l. cbn [P.crossed_left_boundary] in Hinside.
      discriminate. }
    pose proof (pop_bit_on l z Hl Hlne) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,l')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep; rewrite Epop0 in Hstep; cbn [P.active] in Hstep.
    destruct q,bit; cbn [P.trans] in Hstep; try discriminate;
      inversion Hstep; subst; clear Hstep;
      unfold denote_machine_on;
      cbv delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
        iota zeta;
      cbn [denote_q]; unfold denote_side_on, denote_side in Hpop |- *;
      rewrite Hpop;
      rewrite side_bits_push_bit; step1; finish.
  - destruct (P.pop_bit r) as [bit r'] eqn:Epop.
    pose proof (pop_bit_same r Hr) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,r')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in Hstep; rewrite Epop0 in Hstep; cbn [P.active] in Hstep.
    destruct q,bit; cbn [P.trans] in Hstep; try discriminate;
      inversion Hstep; subst; clear Hstep;
      unfold denote_machine_on;
      cbv delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
        iota zeta;
      cbn [denote_q]; unfold denote_side_on, denote_side in Hpop |- *;
      rewrite Hpop;
      rewrite side_bits_push_bit; step1; finish.
Qed.


(* Plain bursts are only an execution grouping; stopping early because a
   macro boundary is reached is semantically the identity. *)
Lemma raw_burst_more_sound fuel m :
  valid_machine m ->
  denote_machine m -[tm]->* denote_machine (P.raw_burst_more fuel m).
Proof.
  revert m. induction fuel as [|fuel IH]; intros m Hvalid; cbn.
  - finish.
  - destruct (P.at_left_boundary m || negb (P.active_literal m))%bool
      eqn:Eguard; [finish|].
    destruct (P.raw_step m) as [m'|] eqn:Eraw; [|finish].
    eapply evstep_trans.
    + eapply raw_step_sound; eassumption.
    + apply IH. eapply raw_step_valid; eassumption.
Qed.

Lemma raw_burst_sound m m' :
  valid_machine m -> P.raw_burst m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.raw_burst in E.
  destruct (P.raw_step m) as [m1|] eqn:Eraw; [|discriminate].
  inversion E; subst m'; clear E.
  eapply evstep_trans.
  - eapply raw_step_sound; eassumption.
  - exact (raw_burst_more_sound 255 m1
      (raw_step_valid m m1 Hvalid Eraw)).
Qed.

Lemma raw_burst_more_valid fuel m :
  valid_machine m -> valid_machine (P.raw_burst_more fuel m).
Proof.
  revert m. induction fuel as [|fuel IH]; intros m Hvalid; cbn; [exact Hvalid|].
  destruct (P.at_left_boundary m || negb (P.active_literal m))%bool;
    [exact Hvalid|].
  destruct (P.raw_step m) as [m'|] eqn:E; [|exact Hvalid].
  apply IH. eapply raw_step_valid; eassumption.
Qed.

Lemma raw_burst_valid m m' :
  valid_machine m -> P.raw_burst m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E. unfold P.raw_burst in E.
  destruct (P.raw_step m) as [m1|] eqn:Eraw; [|discriminate].
  inversion E; subst m'; clear E.
  exact (raw_burst_more_valid 255 m1
    (raw_step_valid m m1 Hvalid Eraw)).
Qed.

Lemma denote_side_on_push_lit bits s z :
  denote_side_on (P.push_lit bits s) z =
  List.map sym_of_bool bits *> denote_side_on s z.
Proof.
  unfold denote_side_on. rewrite side_bits_push_lit, Str_app_assoc.
  reflexivity.
Qed.

Lemma denote_side_on_push_run w n s z :
  denote_side_on (P.push_run w n s) z =
  copies (word_bits w) n *> denote_side_on s z.
Proof.
  unfold denote_side_on. rewrite side_bits_push_run, Str_app_assoc.
  reflexivity.
Qed.

Lemma consume_word_on w s n s' z :
  valid_side s -> P.consume_word w s = (n,s') ->
  valid_side s' /\
  denote_side_on s z = copies (word_bits w) n *> denote_side_on s' z.
Proof.
  intros Hvalid E. pose proof (consume_word_spec w s Hvalid) as H.
  rewrite E in H. destruct H as [Hs Hbits]. split; [exact Hs|].
  unfold denote_side_on. rewrite Hbits, Str_app_assoc. reflexivity.
Qed.

Lemma apply_right_shift_on_sound m m' input output z :
  valid_machine m -> P.m_dir m = P.R ->
  (forall n l r,
    l {{denote_q (P.m_state m)}}> (word_bits input)^^n *> r
      -[tm]->*
    l <* (word_bits output)^^n {{denote_q (P.m_state m)}}> r) ->
  P.apply_right_shift m input output = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hd Hshift E. destruct d; [discriminate|clear Hd].
  destruct (P.consume_word input r) as [n r'] eqn:Econsume.
  assert (Econsume0 :
    P.consume_word input
      (P.m_right {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = (n,r')).
  { cbn. exact Econsume. }
  unfold P.apply_right_shift in E; rewrite Econsume0 in E.
  destruct (NCount.is_zero n) eqn:En; [discriminate|].
  inversion E; subst; clear E.
  pose proof (consume_word_denote input r n r' Hr Econsume) as [_ Hright].
  unfold denote_machine_on.
  cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
    iota zeta.
  rewrite Hright, denote_side_on_push_run.
  exact (Hshift (N.to_nat n) (denote_side_on l z) (denote_side r')).
Qed.

Lemma apply_left_shift_on_sound m m' fixed input output z :
  valid_machine m -> P.m_dir m = P.L ->
  (forall n l r,
    l <* (word_bits input)^^n <{{denote_q (P.m_state m)}}
        (List.map sym_of_bool fixed) *> r
      -[tm]->*
    l <{{denote_q (P.m_state m)}} (List.map sym_of_bool fixed) *>
        (word_bits output)^^n *> r) ->
  P.apply_left_shift m fixed input output = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] Hd Hshift E. destruct d; [clear Hd|discriminate].
  destruct (P.strip_bits fixed r) as [r'|] eqn:Estrip.
  2: {
    assert (Estrip0 :
      P.strip_bits fixed
        (P.m_right {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                      P.m_right:=r; P.m_incs:=inc |}) = None).
    { cbn. exact Estrip. }
    unfold P.apply_left_shift in E. rewrite Estrip0 in E. discriminate. }
  destruct (P.consume_word input l) as [n l'] eqn:Econsume.
  assert (Estrip0 :
    P.strip_bits fixed
      (P.m_right {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                    P.m_right:=r; P.m_incs:=inc |}) = Some r').
  { cbn. exact Estrip. }
  assert (Econsume0 :
    P.consume_word input
      (P.m_left {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
                   P.m_right:=r; P.m_incs:=inc |}) = (n,l')).
  { cbn. exact Econsume. }
  unfold P.apply_left_shift in E; rewrite Estrip0,Econsume0 in E.
  destruct (NCount.is_zero n) eqn:En; [discriminate|].
  inversion E; subst; clear E.
  pose proof (strip_bits_denote fixed r r' Hr Estrip) as [_ Hright].
  pose proof (consume_word_on input l n l' z Hl Econsume) as [_ Hleft].
  unfold denote_machine_on.
  cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
    iota zeta.
  rewrite Hleft,Hright,denote_side_push_lit,denote_side_push_run.
  exact (Hshift (N.to_nat n) (denote_side_on l' z) (denote_side r')).
Qed.

Lemma apply_shift_on_sound m m' z :
  valid_machine m -> P.apply_shift m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq, (P.m_dir m) eqn:Hd;
    unfold P.apply_shift in E; rewrite ?Hq,?Hd in E; try discriminate.
  - destruct (P.apply_left_shift m [true] P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_on_sound; eauto.
      intros n l r. rewrite Hq.
      cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.BL_011011_1.
    + destruct (P.apply_left_shift m [true] P.W0110 P.W0011)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.BL_0110_1.
      * eapply apply_left_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.BL_01101_1.
  - destruct (P.apply_left_shift m P.sep P.W110110 P.W001111)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_left_shift_on_sound; eauto.
      intros n l r. rewrite Hq.
      cbn [denote_q word_bits P.spelling P.sep sym_of_bool].
      apply T.CL_011011_1111.
    + destruct (P.apply_left_shift m P.sep P.W10110 P.W01111)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_left_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling P.sep sym_of_bool].
        apply T.CL_01101_1111.
      * eapply apply_left_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool].
        apply T.CL_0110_1111101111.
  - destruct (P.apply_right_shift m P.W001111 P.W110110)
      as [m1|] eqn:E1.
    + inversion E; subst. eapply apply_right_shift_on_sound; eauto.
      intros n l r. rewrite Hq.
      cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_001111.
    + destruct (P.apply_right_shift m P.W00111 P.W10110)
        as [m2|] eqn:E2.
      * inversion E; subst. eapply apply_right_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_00111.
      * eapply apply_right_shift_on_sound; eauto.
        intros n l r. rewrite Hq.
        cbn [denote_q word_bits P.spelling sym_of_bool]. apply T.FR_0011.
Qed.

Lemma denote_side_on_push_sequence w ns s z : valid_dseq ns ->
  denote_side_on (P.push_sequence w ns s) z =
    count_bits w (P.ds_list ns) *> denote_side_on s z.
Proof.
  intro Hvalid. unfold denote_side_on.
  rewrite side_bits_push_sequence by exact Hvalid.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma FR_groups_all_N ns l r : ns <> [] ->
  l {{F}}> (count_bits P.W001111 ns ++ [1;1;1;1]) *> r -[tm]->*
  ([1;1;1;1] ++ count_bits P.W110110 (rev ns)) *> l {{F}}> r.
Proof.
  intro Hne.
  rewrite <- (rgroup_bits_count P.W001111 ns Hne).
  rewrite <- (lgroup_bits_count P.W110110 ns Hne).
  rewrite <- RGroups_stream, <- LGroups_stream. apply T.FR_groups.
Qed.

Lemma BL_groups_all_N ns l r : ns <> [] ->
  ([1;1;1;1] ++ count_bits P.W110110 (rev ns)) *> l
    <{{B}} [1] *> r -[tm]->*
  l <{{B}} [1] *>
    (count_bits P.W001111 ns ++ [1;1;1;1]) *> r.
Proof.
  intro Hne.
  rewrite <- (rgroup_bits_count P.W001111 ns Hne).
  rewrite <- (lgroup_bits_count P.W110110 ns Hne).
  rewrite <- RGroups_stream, <- LGroups_stream. apply T.BL_groups.
Qed.

Lemma apply_chain_right_on_sound m m' z :
  valid_machine m -> P.m_state m = P.F -> P.m_dir m = P.R ->
  P.apply_chain_right m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine P.m_state P.m_dir] in *.
  intros [Hl Hr] Hq Hd E. subst q d.
  unfold P.apply_chain_right in E; cbn [P.m_right] in E.
  destruct (P.collect_chain P.W001111 r) as [[ns rest]|] eqn:Ecollect;
    [|discriminate].
  pose proof (collect_chain_spec P.W001111 r ns rest Hr Ecollect)
    as [Hds [Hpos [Hlen [Hrest Hsame]]]].
  assert (Hnonempty : P.ds_list ns <> []) by
    (eapply valid_dseq_nonempty; eassumption).
  destruct rest as [|block tail].
  - destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    unfold denote_machine_on;
      cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
        iota zeta.
    rewrite denote_side_on_push_sequence by (apply ds_rev_valid; exact Hds).
    unfold denote_side, denote_side_on. rewrite ds_list_rev,Hsame.
    cbn [denote_q side_bits]. rewrite app_nil_r.
    repeat rewrite Str_app_assoc.
    apply FR_chain_all_N. exact Hnonempty.
  - destruct block as [bits|w n|w ds0].
    + destruct (P.literal_drop bits P.sep tail) as [r'|] eqn:Edrop.
      * inversion E; subst; clear E.
        pose proof (literal_drop_spec bits P.sep tail r' Hrest Edrop)
          as [_ Hdrop].
        change (denote_side_on l z {{F}}> denote_side r -[tm]->*
          denote_side_on (P.push_lit P.sep
            (P.push_sequence P.W110110 (P.ds_rev ns) l)) z
            {{F}}> denote_side r').
        rewrite denote_side_on_push_lit,
          denote_side_on_push_sequence by (apply ds_rev_valid; exact Hds).
        unfold denote_side,denote_side_on. rewrite ds_list_rev,Hsame,Hdrop.
        unfold P.sep. cbn [List.map denote_q side_bits sym_of_bool].
        repeat rewrite Str_app_assoc.
        pose proof (FR_groups_all_N (P.ds_list ns)
          (side_bits l *> z) (side_bits r' *> 0inf) Hnonempty) as Hrule.
        repeat rewrite Str_app_assoc in Hrule. exact Hrule.
      * destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
        inversion E; subst; clear E.
        unfold denote_machine_on;
          cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
            iota zeta.
        rewrite denote_side_on_push_sequence by (apply ds_rev_valid; exact Hds).
        unfold denote_side,denote_side_on. rewrite ds_list_rev,Hsame.
        cbn [denote_q side_bits]. repeat rewrite Str_app_assoc.
        pose proof (FR_chain_all_N (P.ds_list ns) (side_bits l *> z)
          ((block_bits (P.Lit bits) ++ side_bits tail) *> 0inf)
          Hnonempty) as Hrule.
        repeat rewrite Str_app_assoc in Hrule. exact Hrule.
    + destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      unfold denote_machine_on;
        cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
          iota zeta.
      rewrite denote_side_on_push_sequence by (apply ds_rev_valid; exact Hds).
      unfold denote_side,denote_side_on. rewrite ds_list_rev,Hsame.
      cbn [denote_q side_bits]. repeat rewrite Str_app_assoc.
      pose proof (FR_chain_all_N (P.ds_list ns) (side_bits l *> z)
        ((block_bits (P.Run w n) ++ side_bits tail) *> 0inf)
        Hnonempty) as Hrule.
      repeat rewrite Str_app_assoc in Hrule. exact Hrule.
    + destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      unfold denote_machine_on;
        cbv beta delta [P.machine P.m_dir P.m_left P.m_right P.m_state]
          iota zeta.
      rewrite denote_side_on_push_sequence by (apply ds_rev_valid; exact Hds).
      unfold denote_side,denote_side_on. rewrite ds_list_rev,Hsame.
      cbn [denote_q side_bits]. repeat rewrite Str_app_assoc.
      pose proof (FR_chain_all_N (P.ds_list ns) (side_bits l *> z)
        ((block_bits (P.Chain w ds0) ++ side_bits tail) *> 0inf)
        Hnonempty) as Hrule.
      repeat rewrite Str_app_assoc in Hrule. exact Hrule.
Qed.

Lemma BL_groups_sides_on left right ns ltail rtail z :
  valid_dseq ns -> 1 <= P.ds_len ns ->
  side_bits left = [1;1;1;1] ++
    count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail ->
  denote_side right = [1] *> denote_side rtail ->
  denote_side_on left z <{{B}} denote_side right -[tm]->*
  denote_side_on ltail z <{{B}}
    denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns)
        (P.push_lit P.sep rtail))).
Proof.
  intros Hds Hlen Hleft Hright.
  assert (Hrevvalid : valid_dseq (P.ds_rev ns)) by
    (apply ds_rev_valid; exact Hds).
  assert (Hnonempty : rev (P.ds_list ns) <> []).
  { intro E. apply (f_equal (@length N)) in E. rewrite length_rev in E.
    pose proof (valid_dseq_len ns Hds) as Hlength.
    rewrite E in Hlength. cbn in Hlength. lia. }
  assert (Hleftden : denote_side_on left z =
      ([1;1;1;1] ++ count_bits P.W110110 (P.ds_list ns) ++
        side_bits ltail) *> z).
  { unfold denote_side_on. rewrite Hleft. reflexivity. }
  rewrite Hleftden,Hright.
  rewrite denote_side_push_lit,
    denote_side_push_sequence by exact Hrevvalid.
  rewrite ds_list_rev,denote_side_push_lit.
  unfold denote_side,P.sep. cbn [List.map sym_of_bool].
  repeat rewrite Str_app_assoc.
  pose proof (BL_groups_all_N (rev (P.ds_list ns))
    (side_bits ltail *> z) (side_bits rtail *> 0inf) Hnonempty) as Hrule.
  rewrite rev_involutive in Hrule. repeat rewrite Str_app_assoc in Hrule.
  exact Hrule.
Qed.

Lemma BL_chain_sides_on left right ns ltail rtail z :
  valid_dseq ns -> P.ds_at_least_two ns = true ->
  side_bits left = count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail ->
  denote_side right = [1] *> denote_side rtail ->
  denote_side_on left z <{{B}} denote_side right -[tm]->*
  denote_side_on ltail z <{{B}}
    denote_side (P.push_lit [true]
      (P.push_sequence P.W001111 (P.ds_rev ns) rtail)).
Proof.
  intros Hds Htwo Hleft Hright.
  assert (Hrevvalid : valid_dseq (P.ds_rev ns)) by
    (apply ds_rev_valid; exact Hds).
  assert (Hnonempty : rev (P.ds_list ns) <> []).
  { intro E. apply (f_equal (@length N)) in E. rewrite length_rev in E.
    apply ds_at_least_two_spec in Htwo.
    pose proof (valid_dseq_len ns Hds) as Hlength.
    rewrite E in Hlength. cbn in Hlength. lia. }
  assert (Hleftden : denote_side_on left z =
      (count_bits P.W110110 (P.ds_list ns) ++ side_bits ltail) *> z).
  { unfold denote_side_on. rewrite Hleft. reflexivity. }
  rewrite Hleftden,Hright.
  rewrite denote_side_push_lit,
    denote_side_push_sequence by exact Hrevvalid.
  rewrite ds_list_rev.
  unfold denote_side. cbn [List.map sym_of_bool].
  repeat rewrite Str_app_assoc.
  pose proof (BL_chain_all_N (rev (P.ds_list ns))
    (side_bits ltail *> z) (side_bits rtail *> 0inf) Hnonempty) as Hrule.
  rewrite rev_involutive in Hrule. repeat rewrite Str_app_assoc in Hrule.
  exact Hrule.
Qed.

Lemma apply_chain_left_on_sound m m' z :
  valid_machine m -> P.m_state m = P.B -> P.m_dir m = P.L ->
  P.apply_chain_left m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine P.m_state P.m_dir] in *.
  intros [Hl Hr] Hq Hd E. subst q d.
  unfold P.apply_chain_left in E; cbn [P.m_right P.m_left] in E.
  destruct (P.strip_bits [true] r) as [r0|] eqn:Estrip; [|discriminate].
  pose proof (strip_bits_denote [true] r r0 Hr Estrip) as [Hr0 Hright].
  destruct l as [|block after]; [cbn [P.collect_chain P.collect_runs] in E;
    discriminate|].
  inversion Hl as [|? ? Hblock Hafter]; subst.
  destruct block as [bits|w n|w ds0].
  - destruct (P.bits_eqb bits P.sep) eqn:Esep.
    + apply bits_eqb_eq in Esep. subst bits.
      destruct (P.collect_chain P.W110110 after)
        as [[ns lout]|] eqn:Ecollect.
      * inversion E; subst; clear E.
        pose proof (collect_chain_spec P.W110110 after ns lout Hafter Ecollect)
          as [Hds [Hpos [Hlen [Hlout Hsame]]]].
        assert (Hleft : side_bits (P.Lit P.sep :: after) =
          [1;1;1;1] ++ count_bits P.W110110 (P.ds_list ns) ++
            side_bits lout).
        { cbn [side_bits block_bits P.sep List.map sym_of_bool].
          rewrite Hsame. reflexivity. }
        change (denote_side_on (P.Lit P.sep::after) z <{{B}} denote_side r
          -[tm]->* denote_side_on lout z <{{B}}
          denote_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns)
              (P.push_lit P.sep r0)))).
        eapply BL_groups_sides_on; eassumption.
      * destruct (P.collect_chain P.W110110 (P.Lit P.sep::after))
          as [[ns lout]|] eqn:Ecollect0; [|discriminate].
        destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
        inversion E; subst; clear E.
        pose proof (collect_chain_spec P.W110110 (P.Lit P.sep::after)
          ns lout Hl Ecollect0) as [Hds [Hpos [Hlen [Hlout Hleft]]]].
        change (denote_side_on (P.Lit P.sep::after) z <{{B}} denote_side r
          -[tm]->* denote_side_on lout z <{{B}}
          denote_side (P.push_lit [true]
            (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
        eapply BL_chain_sides_on; eassumption.
    + destruct (P.collect_chain P.W110110 (P.Lit bits::after))
        as [[ns lout]|] eqn:Ecollect; [|discriminate].
      destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
      inversion E; subst; clear E.
      pose proof (collect_chain_spec P.W110110 (P.Lit bits::after)
        ns lout Hl Ecollect) as [Hds [Hpos [Hlen [Hlout Hleft]]]].
      change (denote_side_on (P.Lit bits::after) z <{{B}} denote_side r
        -[tm]->* denote_side_on lout z <{{B}}
        denote_side (P.push_lit [true]
          (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
      eapply BL_chain_sides_on; eassumption.
  - destruct (P.collect_chain P.W110110 (P.Run w n::after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    pose proof (collect_chain_spec P.W110110 (P.Run w n::after)
      ns lout Hl Ecollect) as [Hds [Hpos [Hlen [Hlout Hleft]]]].
    change (denote_side_on (P.Run w n::after) z <{{B}} denote_side r
      -[tm]->* denote_side_on lout z <{{B}}
      denote_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    eapply BL_chain_sides_on; eassumption.
  - destruct (P.collect_chain P.W110110 (P.Chain w ds0::after))
      as [[ns lout]|] eqn:Ecollect; [|discriminate].
    destruct (P.ds_at_least_two ns) eqn:Htwo; [|discriminate].
    inversion E; subst; clear E.
    pose proof (collect_chain_spec P.W110110 (P.Chain w ds0::after)
      ns lout Hl Ecollect) as [Hds [Hpos [Hlen [Hlout Hleft]]]].
    change (denote_side_on (P.Chain w ds0::after) z <{{B}} denote_side r
      -[tm]->* denote_side_on lout z <{{B}}
      denote_side (P.push_lit [true]
        (P.push_sequence P.W001111 (P.ds_rev ns) r0))).
    eapply BL_chain_sides_on; eassumption.
Qed.

Lemma apply_chain_on_sound m m' z :
  valid_machine m -> P.apply_chain m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  intros Hvalid E.
  destruct (P.m_state m) eqn:Hq,(P.m_dir m) eqn:Hd;
    unfold P.apply_chain in E; rewrite ?Hq,?Hd in E; try discriminate.
  - eapply apply_chain_left_on_sound; eauto.
  - eapply apply_chain_right_on_sound; eauto.
Qed.

Lemma h_local_step_sound m m' z :
  valid_machine m -> P.crossed_left_boundary m = false ->
  P.h_local_step m = Some m' ->
  denote_machine_on m z -[tm]->* denote_machine_on m' z.
Proof.
  intros Hvalid Hinside E. unfold P.h_local_step in E.
  destruct (P.apply_chain m) as [m1|] eqn:Echain.
  - inversion E; subst. eapply apply_chain_on_sound; eassumption.
  - destruct (P.apply_shift m) as [m2|] eqn:Eshift.
    + inversion E; subst. eapply apply_shift_on_sound; eassumption.
    + eapply raw_step_on_sound; eassumption.
Qed.

Lemma h_local_step_valid m m' :
  valid_machine m -> P.h_local_step m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E. unfold P.h_local_step in E.
  destruct (P.apply_chain m) as [m1|] eqn:Echain.
  - inversion E; subst. eapply apply_chain_valid; eassumption.
  - destruct (P.apply_shift m) as [m2|] eqn:Eshift.
    + inversion E; subst. eapply apply_shift_valid; eassumption.
    + eapply raw_step_valid; eassumption.
Qed.

Lemma h_returned_spec m r' :
  valid_machine m -> P.h_returned m = Some r' ->
  valid_side r' /\
  forall z, denote_machine_on m z = z <{{B}} [1] *> denote_side r'.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. destruct q,d,l; cbn [P.h_returned] in E;
    try discriminate.
  pose proof (strip_bits_denote [true] r r' Hr E) as [Hr' Hden].
  split; [exact Hr'|]. intro z.
  unfold denote_machine_on; cbn [P.m_dir P.m_left P.m_right P.m_state
    denote_q denote_side_on side_bits]. rewrite Hden. reflexivity.
Qed.

Lemma run_h_fuel_spec fuel m r' :
  valid_machine m -> P.run_h_fuel fuel m = Some r' ->
  valid_side r' /\
  forall z, denote_machine_on m z -[tm]->*
    z <{{B}} [1] *> denote_side r'.
Proof.
  revert m r'. induction fuel as [|fuel IH]; intros m r' Hvalid E;
    cbn [P.run_h_fuel] in E.
  - destruct (P.crossed_left_boundary m) eqn:Ecross.
    + pose proof (h_returned_spec m r' Hvalid E) as [Hr Hden].
      split; [exact Hr|]. intro z. rewrite Hden. finish.
    + discriminate.
  - destruct (P.crossed_left_boundary m) eqn:Ecross.
    + pose proof (h_returned_spec m r' Hvalid E) as [Hr Hden].
      split; [exact Hr|]. intro z. rewrite Hden. finish.
    + destruct (P.h_local_step m) as [m'|] eqn:Estep; [|discriminate].
      pose proof (h_local_step_valid m m' Hvalid Estep) as Hvalid'.
      pose proof (IH m' r' Hvalid' E) as [Hr Htail].
      split; [exact Hr|]. intro z. eapply evstep_trans.
      * eapply h_local_step_sound; eassumption.
      * apply Htail.
Qed.

Lemma step_star_progress tm c c' c'' :
  c -[tm]-> c' -> c' -[tm]->* c'' -> c -[tm]->+ c''.
Proof.
  intros Hstep Hstar. revert c Hstep.
  induction Hstar; intros c0 H0.
  - apply progress_base. exact H0.
  - eapply progress_step; [exact H0|].
    apply IHHstar. assumption.
Qed.

Lemma evstep_neq_progress tm c c' :
  c -[tm]->* c' -> c <> c' -> c -[tm]->+ c'.
Proof.
  intros H Hneq. inversion H; subst; [contradiction|].
  eapply step_star_progress; eassumption.
Qed.

Lemma run_h_sound r r' :
  valid_side r -> P.run_h r = Some r' ->
  valid_side r' /\ sideRL tm T.hF T.hB (denote_side r) (denote_side r').
Proof.
  intros Hr E.
  assert (Hm : valid_machine (P.machine P.F P.R [] r 0%N)).
  { unfold valid_machine; cbn [P.machine]. split; [constructor|exact Hr]. }
  pose proof (run_h_fuel_spec 4096 (P.machine P.F P.R [] r 0%N) r' Hm E)
    as [Hr' Hrun]. split; [exact Hr'|].
  unfold sideRL. intro z.
  specialize (Hrun z). cbn [denote_machine_on P.machine denote_q
    denote_side_on side_bits] in Hrun.
  apply evstep_neq_progress with
    (c:=z {{F}}> denote_side r) (c':=z <{{B}} [1] *> denote_side r');
    [exact Hrun|discriminate].
Qed.

Lemma run_hs_sound calls r r' :
  valid_side r -> P.run_hs calls r = Some r' ->
  valid_side r' /\ sideRLs tm (T.h^^calls) (denote_side r) (denote_side r').
Proof.
  revert r r'. induction calls as [|calls IH]; intros r r' Hr E.
  - change (Some r = Some r') in E.
    inversion E; subst. split; [exact Hr|constructor].
  - change ((match P.run_h r with
      | Some r1 => P.run_hs calls r1
      | None => None
      end) = Some r') in E.
    destruct (P.run_h r) as [r1|] eqn:E1; [|discriminate].
    pose proof (run_h_sound r r1 Hr E1) as [Hr1 H1].
    pose proof (IH r1 r' Hr1 E) as [Hr' Htail].
    split; [exact Hr'|]. cbn [lpow]. econstructor; eassumption.
Qed.

Definition chunks_list (chunks : list P.DSeq) : list N :=
  List.concat (List.map P.ds_list chunks).

Definition valid_chunk (ns : P.DSeq) : Prop :=
  valid_dseq ns /\ List.Forall positive_count (P.ds_list ns) /\
  P.ds_list ns <> [].

Definition valid_chunks (chunks : list P.DSeq) : Prop :=
  List.Forall valid_chunk chunks.

Lemma chunks_list_cons ns chunks :
  chunks_list (ns::chunks) = P.ds_list ns ++ chunks_list chunks.
Proof. reflexivity. Qed.

Lemma chunks_list_nil : chunks_list [] = [].
Proof. reflexivity. Qed.


Lemma count_bits_app_nonempty w xs ys : xs <> [] -> ys <> [] ->
  count_bits w (xs ++ ys) =
    count_bits w xs ++ [1;1;1;1] ++ count_bits w ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Hx Hy; [contradiction|].
  destruct xs as [|y xs].
  - destruct ys as [|z ys]; [contradiction|]. reflexivity.
  - change (copies (word_bits w) x ++ [1;1;1;1] ++
      count_bits w ((y::xs)++ys) =
      (copies (word_bits w) x ++ [1;1;1;1] ++ count_bits w (y::xs)) ++
        [1;1;1;1] ++ count_bits w ys).
    rewrite IH by discriminate || assumption.
    repeat rewrite app_assoc. reflexivity.
Qed.

Lemma chunks_list_nonempty chunks :
  valid_chunks chunks -> chunks <> [] -> chunks_list chunks <> [].
Proof.
  intros Hv Hne. destruct chunks as [|ns chunks]; [contradiction|].
  inversion Hv as [|? ? Hns]; subst. rewrite chunks_list_cons.
  destruct Hns as [_ [_ Hns]]. intro E. apply app_eq_nil in E. tauto.
Qed.

Lemma count_bits_chunks_cons w ns chunks :
  valid_chunk ns -> valid_chunks chunks -> chunks <> [] ->
  count_bits w (chunks_list (ns::chunks)) =
    count_bits w (P.ds_list ns) ++ [1;1;1;1] ++
      count_bits w (chunks_list chunks).
Proof.
  intros Hns Hchunks Hne. rewrite chunks_list_cons.
  apply count_bits_app_nonempty.
  - exact (proj2 (proj2 Hns)).
  - apply chunks_list_nonempty; assumption.
Qed.

Lemma side_bits_push_chunks w chunks tail :
  valid_chunks chunks ->
  side_bits (P.push_chunks w chunks tail) =
    count_bits w (chunks_list chunks) ++ side_bits tail.
Proof.
  induction chunks as [|ns chunks IH]; intro Hv.
  - reflexivity.
  - inversion Hv as [|? ? Hns Hchunks]; subst.
    destruct chunks as [|ns' chunks'].
    + cbn [P.push_chunks]. unfold chunks_list. cbn.
      rewrite side_bits_push_sequence by exact (proj1 Hns).
      rewrite app_nil_r. reflexivity.
    + change (side_bits (P.push_sequence w ns
          (P.Lit P.sep :: P.push_chunks w (ns'::chunks') tail)) =
        count_bits w (chunks_list (ns::ns'::chunks')) ++ side_bits tail).
      rewrite side_bits_push_sequence by exact (proj1 Hns).
      change (count_bits w (P.ds_list ns) ++ [1;1;1;1] ++
        side_bits (P.push_chunks w (ns'::chunks') tail) =
        count_bits w (chunks_list (ns::ns'::chunks')) ++ side_bits tail).
      rewrite IH by exact Hchunks.
      rewrite (count_bits_chunks_cons w ns (ns'::chunks')
        Hns Hchunks (ltac:(discriminate))).
      repeat rewrite app_assoc. reflexivity.
Qed.

Lemma denote_side_push_chunks w chunks tail :
  valid_chunks chunks ->
  denote_side (P.push_chunks w chunks tail) =
    count_bits w (chunks_list chunks) *> denote_side tail.
Proof.
  intro H. unfold denote_side. rewrite side_bits_push_chunks by exact H.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma singleton_chunk_spec w ns rest :
  valid_chunk ns -> valid_side rest ->
  valid_chunks [ns] /\ [ns] <> [] /\ valid_side rest /\
  count_bits w (P.ds_list ns) ++ side_bits rest =
    count_bits w (chunks_list [ns]) ++ side_bits rest.
Proof.
  intros Hns Hrest. split; [constructor; [exact Hns|constructor]|].
  split; [discriminate|]. split; [exact Hrest|].
  unfold chunks_list. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma collect_chain_chunks_spec fuel w s chunks tail :
  valid_side s ->
  P.collect_chain_chunks fuel w s = Some (chunks,tail) ->
  valid_chunks chunks /\ chunks <> [] /\ valid_side tail /\
  side_bits s = count_bits w (chunks_list chunks) ++ side_bits tail.
Proof.
  revert s chunks tail. induction fuel as [|fuel IH];
    intros s chunks tail Hvalid E; [discriminate|].
  assert (Hcontinue : forall ns rest chunks0 tail0,
    valid_chunk ns -> valid_side rest ->
    (match rest with
     | P.Lit bits :: after_sep =>
         if P.bits_eqb bits P.sep then
           match P.collect_chain_chunks fuel w after_sep with
           | Some (more,out) => Some (ns::more,out)
           | None => Some ([ns],rest)
           end
         else Some ([ns],rest)
     | _ => Some ([ns],rest)
    end) = Some (chunks0,tail0) ->
    valid_chunks chunks0 /\ chunks0 <> [] /\ valid_side tail0 /\
    count_bits w (P.ds_list ns) ++ side_bits rest =
      count_bits w (chunks_list chunks0) ++ side_bits tail0).
  { intros ns rest chunks0 tail0 Hns Hrest Ec.
    destruct rest as [|block after].
    - inversion Ec; subst. apply singleton_chunk_spec; assumption.
    - destruct block as [bits|wr nr|wc nsc].
      + destruct (P.bits_eqb bits P.sep) eqn:Esep.
        * apply bits_eqb_eq in Esep. subst bits.
          inversion Hrest as [|? ? Hlit Hafter]; subst.
          destruct (P.collect_chain_chunks fuel w after)
            as [[more out]|] eqn:Erec.
          -- inversion Ec; subst chunks0 tail0; clear Ec.
             pose proof (IH after more out Hafter Erec)
               as [Hmore [Hmore_ne [Hout Hbits]]].
             repeat split; try constructor; try assumption; try discriminate.
             rewrite chunks_list_cons.
             rewrite count_bits_app_nonempty;
               [|exact (proj2 (proj2 Hns))
                |apply chunks_list_nonempty; assumption].
             cbn [side_bits block_bits P.sep List.map sym_of_bool].
             rewrite Hbits. repeat rewrite app_assoc. reflexivity.
          -- inversion Ec; subst chunks0 tail0; clear Ec.
             apply singleton_chunk_spec; assumption.
        * inversion Ec; subst chunks0 tail0; clear Ec.
          apply singleton_chunk_spec; assumption.
      + inversion Ec; subst chunks0 tail0; clear Ec.
        apply singleton_chunk_spec; assumption.
      + inversion Ec; subst chunks0 tail0; clear Ec.
        apply singleton_chunk_spec; assumption. }
  destruct s as [|block rest]; [discriminate|].
  inversion Hvalid as [|? ? Hblock Hrest]; subst.
  destruct block as [bits|w' n|w' ns]; [discriminate| |].
  - cbn [P.collect_chain_chunks] in E.
    destruct (P.word_eqb w w' && negb (NCount.is_zero n))%bool
      eqn:Eguard; [|discriminate].
    apply and_true_iff in Eguard. destruct Eguard as [Ew En].
    apply word_eqb_eq in Ew. subst w'.
    apply Bool.negb_true_iff,N.eqb_neq in En.
    pose proof (Hcontinue (P.ds_of_list [n]) rest chunks tail) as Hc.
    apply Hc; try assumption.
    + split; [exact I|]. split.
      * rewrite ds_list_of_list. constructor; [unfold positive_count; lia|constructor].
      * rewrite ds_list_of_list. discriminate.
  - cbn [P.collect_chain_chunks] in E.
    destruct (P.word_eqb w w' && P.ds_nonempty ns)%bool
      eqn:Eguard; [|discriminate].
    apply and_true_iff in Eguard. destruct Eguard as [Ew En].
    apply word_eqb_eq in Ew. subst w'.
    destruct Hblock as [Hds [Hpos Hlen]].
    pose proof (Hcontinue ns rest chunks tail) as Hc.
    apply Hc; try assumption.
    + split; [exact Hds|]. split; [exact Hpos|].
      intro Hnil. pose proof (valid_dseq_len ns Hds) as Hlength.
      rewrite Hnil in Hlength. cbn in Hlength. lia.
Qed.

Lemma parse_boundary_chunks_spec m p :
  valid_machine m -> P.parse_boundary_chunks m = Some p ->
  P.m_state m = P.C /\ P.m_dir m = P.L /\ P.m_left m = [] /\
  valid_side (P.bc_header p) /\ valid_chunks (P.bc_xs p) /\
  P.bc_xs p <> [] /\ valid_side (P.bc_tail p) /\
  transparent_header (P.bc_header p) /\
  denote_side (P.m_right m) = [1;1] *>
    copies (word_bits P.W0011) (P.bc_a p) *>
    side_bits (P.bc_header p) *>
    count_bits P.W001111 (chunks_list (P.bc_xs p)) *>
    denote_side (P.bc_tail p).
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. unfold P.parse_boundary_chunks in E.
  destruct q,d,l;
    cbv beta delta [P.m_state P.m_dir P.m_left P.m_right] iota zeta in E;
    try discriminate.
  destruct (P.strip_bits [true;true] r) as [r0|] eqn:Estrip;
    [|discriminate].
  destruct (P.consume_word P.W0011 r0) as [a r1] eqn:Econsume.
  destruct (P.parse_boundary_header r1) as [header r2] eqn:Eheader.
  destruct (P.collect_chain_chunks (S (length r2)) P.W001111 r2)
    as [[chunks tail]|] eqn:Ecollect; [|discriminate].
  inversion E; subst p; clear E.
  pose proof (strip_bits_denote [true;true] r r0 Hr Estrip)
    as [Hr0 Hstrip].
  pose proof (consume_word_denote P.W0011 r0 a r1 Hr0 Econsume)
    as [Hr1 Hconsume].
  pose proof (parse_boundary_header_spec r1 header r2 Hr1 Eheader)
    as [Hheader [Hr2 [Hheadersame Htransparent]]].
  pose proof (collect_chain_chunks_spec (S (length r2)) P.W001111 r2
    chunks tail Hr2 Ecollect) as [Hchunks [Hchunks_ne [Htail Hcollect]]].
  assert (Hheaderden : denote_side r1 = side_bits header *> denote_side r2).
  { unfold denote_side. rewrite Hheadersame,Str_app_assoc. reflexivity. }
  assert (Hcollectden : denote_side r2 =
      count_bits P.W001111 (chunks_list chunks) *> denote_side tail).
  { unfold denote_side. rewrite Hcollect,Str_app_assoc. reflexivity. }
  repeat split; try assumption; try reflexivity.
  change (denote_side r = [1;1] *> copies (word_bits P.W0011) a *>
    side_bits header *> count_bits P.W001111 (chunks_list chunks) *>
    denote_side tail).
  rewrite Hstrip,Hconsume,Hheaderden,Hcollectden.
  cbn [List.map sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_side_make_boundary_chunks a header chunks tail :
  valid_chunks chunks ->
  denote_side (P.make_boundary_chunks_right a header chunks tail) =
  [1;1] *> copies (word_bits P.W0011) a *> side_bits header *>
    count_bits P.W001111 (chunks_list chunks) *> denote_side tail.
Proof.
  intro Hchunks. unfold P.make_boundary_chunks_right.
  rewrite denote_side_push_lit,denote_side_push_run.
  unfold denote_side at 1. rewrite side_bits_app,side_bits_push_chunks
    by exact Hchunks.
  cbn [List.map sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.


Lemma chunks_cons_list x chunks :
  chunks_list (P.chunks_cons x chunks) = x :: chunks_list chunks.
Proof.
  destruct chunks as [|ns chunks].
  - change (P.ds_list (P.ds_of_list [x]) = [x]). apply ds_list_of_list.
  - change (P.ds_list (P.ds_cons x ns) ++ chunks_list chunks =
      x :: (P.ds_list ns ++ chunks_list chunks)).
    rewrite ds_list_cons. reflexivity.
Qed.

Lemma chunks_cons_valid x chunks :
  positive_count x -> valid_chunks chunks ->
  valid_chunks (P.chunks_cons x chunks).
Proof.
  intros Hx Hchunks. destruct chunks as [|ns chunks].
  - cbn [P.chunks_cons]. constructor; [|constructor].
    split; [exact I|]. split.
    + rewrite ds_list_of_list. constructor; [exact Hx|constructor].
    + rewrite ds_list_of_list. discriminate.
  - inversion Hchunks as [|? ? Hns Htail]; subst.
    cbn [P.chunks_cons]. constructor; [|exact Htail].
    destruct Hns as [Hds [Hpos Hne]]. split; [exact I|]. split.
    + rewrite ds_list_cons. constructor; assumption.
    + rewrite ds_list_cons. discriminate.
Qed.

Lemma chunks_uncons_ok chunks :
  match P.chunks_uncons chunks with
  | None => chunks_list chunks = []
  | Some (x,rest) => chunks_list chunks = x :: chunks_list rest
  end.
Proof.
  induction chunks as [|ns chunks IH]; [reflexivity|].
  cbn [P.chunks_uncons chunks_list].
  destruct (P.ds_uncons ns) as [[x ns']|] eqn:Eun.
  - pose proof (ds_uncons_ok ns) as Hds. rewrite Eun in Hds.
    destruct (negb (P.ds_nonempty ns')) eqn:Eempty.
    + apply Bool.negb_true_iff in Eempty.
      rewrite (ds_nonempty_false ns' Eempty) in Hds. cbn in Hds.
      change (P.ds_list ns ++ chunks_list chunks = x :: chunks_list chunks).
      rewrite Hds. reflexivity.
    + apply Bool.negb_false_iff in Eempty.
      change (P.ds_list ns ++ chunks_list chunks =
        x :: (P.ds_list ns' ++ chunks_list chunks)).
      rewrite Hds. reflexivity.
  - pose proof (ds_uncons_ok ns) as Hds. rewrite Eun in Hds.
    destruct (P.chunks_uncons chunks) as [[x rest]|] eqn:Erec.
    + specialize IH.
      change (P.ds_list ns ++ chunks_list chunks =
        x :: chunks_list rest). rewrite Hds. exact IH.
    + specialize IH.
      change (P.ds_list ns ++ chunks_list chunks = []).
      rewrite Hds. exact IH.
Qed.

Lemma chunks_unsnoc_ok chunks :
  match P.chunks_unsnoc chunks with
  | None => chunks_list chunks = []
  | Some (prefix,x) => chunks_list chunks = chunks_list prefix ++ [x]
  end.
Proof.
  induction chunks as [|ns chunks IH]; [reflexivity|].
  destruct chunks as [|ns' chunks'].
  - cbn [P.chunks_unsnoc chunks_list].
    destruct (P.ds_unsnoc ns) as [[ns0 x]|] eqn:Eun.
    + pose proof (ds_unsnoc_ok ns) as Hds. rewrite Eun in Hds.
      destruct (negb (P.ds_nonempty ns0)) eqn:Eempty.
      * apply Bool.negb_true_iff in Eempty.
        rewrite (ds_nonempty_false ns0 Eempty) in Hds. cbn in Hds.
        rewrite chunks_list_cons,chunks_list_nil,!app_nil_r. exact Hds.
      * apply Bool.negb_false_iff in Eempty.
        rewrite !chunks_list_cons,chunks_list_nil,!app_nil_r. exact Hds.
    + pose proof (ds_unsnoc_ok ns) as Hds. rewrite Eun in Hds.
      rewrite chunks_list_cons,chunks_list_nil,!app_nil_r. exact Hds.
  - change
      (match
         (match P.chunks_unsnoc (ns'::chunks') with
          | Some (prefix,x) => Some (ns::prefix,x)
          | None =>
              match P.ds_unsnoc ns with
              | Some (ns0,x) =>
                  if negb (P.ds_nonempty ns0)
                  then Some ([],x) else Some ([ns0],x)
              | None => None
              end
          end)
       with
       | Some (prefix,x) =>
           chunks_list (ns::ns'::chunks') = chunks_list prefix ++ [x]
       | None => chunks_list (ns::ns'::chunks') = []
       end).
    destruct (P.chunks_unsnoc (ns'::chunks'))
      as [[prefix x]|] eqn:Erec.
    + specialize (IH).
      rewrite (chunks_list_cons ns (ns'::chunks')).
      rewrite (chunks_list_cons ns prefix).
      rewrite IH,app_assoc. reflexivity.
    + specialize (IH).
      destruct (P.ds_unsnoc ns) as [[ns0 x]|] eqn:Eun.
      * pose proof (ds_unsnoc_ok ns) as Hds. rewrite Eun in Hds.
        destruct (negb (P.ds_nonempty ns0)) eqn:Eempty.
        -- apply Bool.negb_true_iff in Eempty.
           rewrite (ds_nonempty_false ns0 Eempty) in Hds.
           rewrite chunks_list_cons,IH,chunks_list_nil,Hds.
           cbn. reflexivity.
        -- apply Bool.negb_false_iff in Eempty.
           rewrite (chunks_list_cons ns (ns'::chunks')).
           rewrite (chunks_list_cons ns0 []).
           rewrite IH,Hds,chunks_list_nil,!app_nil_r. reflexivity.
      * pose proof (ds_unsnoc_ok ns) as Hds. rewrite Eun in Hds.
        rewrite chunks_list_cons,IH,Hds. reflexivity.
Qed.

Lemma chunks_uncons_valid chunks x rest :
  valid_chunks chunks -> P.chunks_uncons chunks = Some (x,rest) ->
  positive_count x /\ valid_chunks rest.
Proof.
  induction chunks as [|ns chunks IH]; intros Hv E; [discriminate|].
  inversion Hv as [|? ? Hns Hchunks]; subst.
  destruct Hns as [Hds [Hpos Hne]].
  cbn [P.chunks_uncons] in E.
  destruct (P.ds_uncons ns) as [[x0 ns']|] eqn:Eun.
  - pose proof (ds_uncons_forall ns x0 ns' Hpos Eun) as [Hx Hpos'].
    pose proof (ds_uncons_valid ns x0 ns' Hds Eun) as Hds'.
    destruct (negb (P.ds_nonempty ns')) eqn:Eempty;
      inversion E; subst x0 rest; clear E.
    + split; [exact Hx|exact Hchunks].
    + apply Bool.negb_false_iff in Eempty. split; [exact Hx|].
      constructor; [|exact Hchunks]. split; [exact Hds'|]. split;
        [exact Hpos'|].
      intro Hnil. pose proof (valid_dseq_len ns' Hds') as Hlength.
      pose proof (ds_nonempty_len ns' Eempty) as Hpositive.
      rewrite Hnil in Hlength. cbn in Hlength. lia.
  - pose proof (ds_uncons_ok ns) as Hnil. rewrite Eun in Hnil.
    contradiction.
Qed.

Lemma chunks_unsnoc_valid chunks prefix x :
  valid_chunks chunks -> P.chunks_unsnoc chunks = Some (prefix,x) ->
  valid_chunks prefix /\ positive_count x.
Proof.
  revert prefix x. induction chunks as [|ns chunks IH];
    intros prefix x Hv E; [discriminate|].
  inversion Hv as [|? ? Hns Hchunks]; subst.
  destruct chunks as [|ns' chunks'].
  - cbn [P.chunks_unsnoc] in E.
    destruct (P.ds_unsnoc ns) as [[ns0 x0]|] eqn:Eun; [|discriminate].
    destruct Hns as [Hds [Hpos Hne]].
    pose proof (ds_unsnoc_forall ns ns0 x0 Hpos Eun) as [Hpos' Hx].
    pose proof (ds_unsnoc_valid ns ns0 x0 Hds Eun) as Hds'.
    destruct (negb (P.ds_nonempty ns0)) eqn:Eempty;
      inversion E; subst prefix x0; clear E.
    + split; [constructor|exact Hx].
    + apply Bool.negb_false_iff in Eempty. split; [|exact Hx].
      constructor; [|constructor]. split; [exact Hds'|]. split;
        [exact Hpos'|].
      intro Hnil. pose proof (valid_dseq_len ns0 Hds') as Hlength.
      pose proof (ds_nonempty_len ns0 Eempty) as Hpositive.
      rewrite Hnil in Hlength. cbn in Hlength. lia.
  - change
      (match P.chunks_unsnoc (ns'::chunks') with
       | Some (pre,y) => Some (ns::pre,y)
       | None =>
           match P.ds_unsnoc ns with
           | Some (ns0,y) =>
               if negb (P.ds_nonempty ns0)
               then Some ([],y) else Some ([ns0],y)
           | None => None
           end
       end = Some (prefix,x)) in E.
    destruct (P.chunks_unsnoc (ns'::chunks'))
      as [[pre y]|] eqn:Erec.
    + inversion E; subst prefix y; clear E.
      pose proof (IH pre x Hchunks eq_refl) as [Hpre Hx].
      split; [constructor; [exact Hns|exact Hpre]|exact Hx].
    + pose proof (chunks_unsnoc_ok (ns'::chunks')) as Hnil.
      rewrite Erec in Hnil.
      assert (Htailne : chunks_list (ns'::chunks') <> []).
      { apply chunks_list_nonempty; [exact Hchunks|discriminate]. }
      contradiction.
Qed.

Lemma chunks_at_least_two_spec chunks :
  valid_chunks chunks -> P.chunks_at_least_two chunks = true ->
  2 <= length (chunks_list chunks).
Proof.
  induction chunks as [|ns chunks IH]; intros Hv Htwo; [discriminate|].
  inversion Hv as [|? ? Hns Hchunks]; subst.
  cbn [P.chunks_at_least_two] in Htwo.
  destruct (P.ds_at_least_two ns) eqn:E2.
  - apply ds_at_least_two_spec in E2. rewrite chunks_list_cons,length_app.
    rewrite (valid_dseq_len ns (proj1 Hns)) in E2. lia.
  - destruct (P.ds_nonempty ns) eqn:Ene.
    + destruct chunks as [|ns' chunks']; [discriminate|].
      rewrite chunks_list_cons,length_app.
      pose proof (ds_nonempty_len ns Ene) as Hn.
      assert (Ht : 1 <= length (chunks_list (ns'::chunks'))).
      { destruct (chunks_list (ns'::chunks')) eqn:El; [|cbn; lia].
        exfalso. apply (chunks_list_nonempty (ns'::chunks') Hchunks
          (ltac:(discriminate))). exact El. }
      rewrite <- (valid_dseq_len ns (proj1 Hns)).
      change (1 + 1 <= P.ds_len ns + length (chunks_list (ns'::chunks'))).
      apply Nat.add_le_mono; assumption.
    + exfalso. apply (proj2 (proj2 Hns)),ds_nonempty_false,Ene.
Qed.

Lemma take_last_chunks_spec count chunks acc main out :
  valid_chunks chunks -> List.Forall positive_count acc ->
  P.take_last_chunks count chunks acc = Some (main,out) ->
  valid_chunks main /\ List.Forall positive_count out /\
  chunks_list chunks ++ acc = chunks_list main ++ out.
Proof.
  revert chunks acc main out. induction count as [|count IH];
    intros chunks acc main out Hchunks Hacc E.
  - inversion E; subst. repeat split; assumption || reflexivity.
  - cbn [P.take_last_chunks] in E.
    destruct (P.chunks_unsnoc chunks) as [[prefix x]|] eqn:Eun;
      [|discriminate].
    pose proof (chunks_unsnoc_valid chunks prefix x Hchunks Eun)
      as [Hprefix Hx].
    pose proof (IH prefix (x::acc) main out Hprefix
      (ltac:(constructor; assumption)) E) as [Hmain [Hout Heq]].
    split; [exact Hmain|]. split; [exact Hout|].
    pose proof (chunks_unsnoc_ok chunks) as Hlist. rewrite Eun in Hlist.
    rewrite Hlist,<-app_assoc. cbn. exact Heq.
Qed.

Lemma take_last_chunks_length count chunks acc main out :
  P.take_last_chunks count chunks acc = Some (main,out) ->
  length out = count + length acc.
Proof.
  revert chunks acc main out. induction count as [|count IH];
    intros chunks acc main out E.
  - inversion E. reflexivity.
  - cbn [P.take_last_chunks] in E.
    destruct (P.chunks_unsnoc chunks) as [[prefix x]|]; [|discriminate].
    specialize (IH prefix (x::acc) main out E). cbn in IH. lia.
Qed.

Lemma sideRL_header hx hy r1 r2 :
  header_pass hx hy -> sideRL tm (F,[]) (B,[1]) r1 r2 ->
  sideRL tm (F,[]) (B,[1]) (hx *> r1) (hx *> r2).
Proof.
  intros [HF HB] H l. unfold sideRL in H.
  eapply evstep_progress_trans.
  - apply HF.
  - eapply progress_evstep_trans.
    + apply H.
    + apply HB.
Qed.

Lemma sideRLs_header hx hy k r1 r2 :
  header_pass hx hy -> sideRLs tm (T.h^^k) r1 r2 ->
  sideRLs tm (T.h^^k) (hx *> r1) (hx *> r2).
Proof.
  intros Hheader. revert r1 r2. induction k as [|k IH];
    intros r1 r2 H; cbn [lpow] in *.
  - inversion H. constructor.
  - inversion H; subst. econstructor.
    + eapply sideRL_header; eassumption.
    + eapply IH; eassumption.
Qed.

Lemma WGroups_count_bits ns :
  T.WGroups (List.map N.to_nat ns) = rgroup_bits P.W001111 ns.
Proof.
  induction ns as [|n ns IH]; [reflexivity|].
  cbn [List.map T.WGroups rgroup_bits]. rewrite IH.
  unfold copies,word_bits,T.X,T.Sep.
  cbn [P.spelling sym_of_bool]. reflexivity.
Qed.

Lemma rgroup_bits_app w xs ys :
  rgroup_bits w (xs++ys) = rgroup_bits w xs ++ rgroup_bits w ys.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (copies (word_bits w) x ++ [1;1;1;1] ++
    rgroup_bits w (xs++ys) =
    (copies (word_bits w) x ++ [1;1;1;1] ++ rgroup_bits w xs) ++
      rgroup_bits w ys).
  rewrite IH. repeat rewrite app_assoc. reflexivity.
Qed.

Lemma count_bits_app_rgroup w xs ys : xs <> [] -> ys <> [] ->
  count_bits w (xs++ys) = rgroup_bits w xs ++ count_bits w ys.
Proof.
  intros Hx Hy. rewrite count_bits_app_nonempty by assumption.
  rewrite rgroup_bits_count by assumption.
  repeat rewrite app_assoc. reflexivity.
Qed.

Lemma count_bits_sep_side w xs z : xs <> [] ->
  count_bits w xs *> [1;1;1;1] *> z = rgroup_bits w xs *> z.
Proof.
  intro Hx. rewrite rgroup_bits_count by assumption.
  rewrite Str_app_assoc. reflexivity.
Qed.

Lemma core_input_den ls y x r0 rs tail_counts z :
  tail_counts <> [] ->
  count_bits P.W001111 ((ls ++ [y]) ++ [x]) *>
    [1;1;0;1;1;1;1;1;1;1] *>
    count_bits P.W001111 ((r0::rs) ++ tail_counts) *> z =
  T.Core (List.map N.to_nat ls ++ [N.to_nat y]) (N.to_nat x)
    (N.to_nat r0 :: List.map N.to_nat rs) *>
    count_bits P.W001111 tail_counts *> z.
Proof.
  intro Htail. unfold T.Core.
  rewrite T.WGroups_app,!WGroups_count_bits.
  rewrite count_bits_last,count_bits_app_rgroup by discriminate || assumption.
  rewrite rgroup_bits_app.
  cbn [T.WGroups rgroup_bits]. rewrite WGroups_count_bits.
  unfold copies,word_bits,T.X.
  cbn [P.spelling sym_of_bool List.map].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma core_output_den ls y x r0 rs z :
  count_bits P.W001111 (ls ++ [y]) *>
    [1;1;0;1;1;1;1;1;1;1] *>
    count_bits P.W001111 (x::r0::rs) *> [1;1;1;1] *> z =
  T.Core (List.map N.to_nat ls) (N.to_nat y)
    (N.to_nat x :: N.to_nat r0 :: List.map N.to_nat rs) *> z.
Proof.
  unfold T.Core. rewrite !WGroups_count_bits.
  rewrite count_bits_last.
  rewrite count_bits_sep_side by discriminate.
  cbn [T.WGroups rgroup_bits]. rewrite WGroups_count_bits.
  unfold copies,word_bits,T.X.
  cbn [P.spelling sym_of_bool List.map lpow].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma Bnd_core28_header hx hy a ls y x r0 rs u v :
  header_pass hx hy ->
  sideRLs tm (T.h^^4) u v ->
  T.Bnd a (hx *> T.Core (ls++[y]) (S (S x))
      (S (S (S (S r0)))::rs) *> u) -[tm]->*
  T.Bnd (28+a) (hx *> T.Core ls y (S x::S r0::rs) *> v).
Proof.
  intros Hheader Htail. apply T.Bnd_sideRLs.
  eapply sideRLs_header; [exact Hheader|].
  eapply segRLs_sideRLs_concat; [apply T.seg_core28|exact Htail].
Qed.

Lemma denote_parsed_boundary_chunks m p :
  valid_machine m -> P.parse_boundary_chunks m = Some p ->
  denote_machine m = T.Bnd (N.to_nat (P.bc_a p))
    (side_bits (P.bc_header p) *>
      count_bits P.W001111 (chunks_list (P.bc_xs p)) *>
      denote_side (P.bc_tail p)).
Proof.
  intros Hvalid E.
  pose proof (parse_boundary_chunks_spec m p Hvalid E) as H.
  destruct H as [Hq [Hd [Hl [_ [_ [_ [_ [_ Hbits]]]]]]]].
  unfold denote_machine. rewrite Hq,Hd,Hl. cbn [denote_q denote_side].
  unfold T.Bnd. rewrite Hbits. unfold copies,word_bits.
  cbn [P.spelling sym_of_bool]. repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma denote_make_boundary_chunks a header chunks tail inc :
  valid_chunks chunks ->
  denote_machine (P.machine P.C P.L []
    (P.make_boundary_chunks_right a header chunks tail) inc) =
  T.Bnd (N.to_nat a)
    (side_bits header *> count_bits P.W001111 (chunks_list chunks) *>
      denote_side tail).
Proof.
  intro Hchunks.
  change (denote_side [] <{{C}}
    denote_side (P.make_boundary_chunks_right a header chunks tail) =
    T.Bnd (N.to_nat a)
      (side_bits header *> count_bits P.W001111 (chunks_list chunks) *>
        denote_side tail)).
  rewrite denote_side_make_boundary_chunks by exact Hchunks.
  unfold T.Bnd,copies,word_bits,denote_side. cbn [P.spelling sym_of_bool side_bits].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Lemma valid_push_chunks w chunks tail :
  valid_chunks chunks -> valid_side tail ->
  valid_side (P.push_chunks w chunks tail).
Proof.
  induction chunks as [|ns chunks IH]; intros Hchunks Htail.
  - exact Htail.
  - inversion Hchunks as [|? ? Hns Hchunks']; subst.
    destruct chunks as [|ns' chunks'].
    + cbn [P.push_chunks]. eapply valid_push_sequence;
        [exact (proj1 Hns)|exact (proj1 (proj2 Hns))|exact Htail].
    + cbn [P.push_chunks]. eapply valid_push_sequence.
      * exact (proj1 Hns).
      * exact (proj1 (proj2 Hns)).
      * constructor; [discriminate|]. eapply IH; eassumption.
Qed.

Lemma make_boundary_chunks_valid a header chunks tail inc :
  valid_side header -> valid_chunks chunks -> valid_side tail ->
  valid_machine (P.machine P.C P.L []
    (P.make_boundary_chunks_right a header chunks tail) inc).
Proof.
  intros Hheader Hchunks Htail. split; [constructor|].
  unfold P.make_boundary_chunks_right. apply valid_push_lit,valid_push_run.
  unfold valid_side in *. rewrite Forall_app. split; [exact Hheader|].
  eapply valid_push_chunks; eassumption.
Qed.

Lemma apply_boundary_core_split_chunks_spec p k marker rhs after_rhs m' :
  valid_side (P.bc_header p) ->
  valid_chunks (P.bc_xs p) ->
  2 <= length (chunks_list (P.bc_xs p)) ->
  valid_chunks rhs -> valid_side after_rhs ->
  transparent_header (P.bc_header p) ->
  marker = [true;true;false;true;true;true;true;true;true;true] ->
  1 <= k ->
  P.apply_boundary_core_split_chunks k p marker rhs after_rhs = Some m' ->
  valid_machine m' /\
  T.Bnd (N.to_nat (P.bc_a p))
    (side_bits (P.bc_header p) *>
      count_bits P.W001111 (chunks_list (P.bc_xs p)) *>
      List.map sym_of_bool marker *>
      count_bits P.W001111 (chunks_list rhs) *> denote_side after_rhs)
    -[tm]->* denote_machine m'.
Proof.
  destruct p as [a header bc_xs boundary_tail].
  intros Hheader Hbc Hbc2 Hrhs Hafter Htransparent Hmarker Hk E.
  cbv beta iota zeta delta [P.bc_header P.bc_xs P.bc_a] in
    Hheader,Hbc,Hbc2,Htransparent,E |- *.
  unfold P.apply_boundary_core_split_chunks in E.
  cbv beta iota zeta delta [P.bc_xs P.bc_a P.bc_header P.bc_tail] in E.
  destruct (P.chunks_unsnoc bc_xs) as [[lhs x]|] eqn:Eleft;
  destruct (P.take_last_chunks k rhs []) as [[main tail_counts]|]
    eqn:Etake; try discriminate.
  destruct (P.chunks_uncons main) as [[r0 middle]|] eqn:Eright;
    cbn beta iota zeta in E; try discriminate.
  change ((if (N.leb 2 x && N.leb 4 r0)%bool then
    match P.run_hs 4
      (P.push_sequence P.W001111 (P.ds_of_list tail_counts) after_rhs) with
    | Some tail_output =>
        Some (P.machine P.C P.L []
          (P.make_boundary_chunks_right (a+28)%N header lhs
            (P.Lit marker :: P.push_chunks P.W001111
              (P.chunks_cons (N.pred x)
                (P.chunks_cons (N.sub r0 3) middle))
              (P.Lit P.sep :: tail_output))) 0%N)
    | None => None
    end else None) = Some m') in E.
  destruct (N.leb 2 x && N.leb 4 r0)%bool eqn:Eguard;
    cbn beta iota zeta in E; try discriminate.
  destruct (P.run_hs 4
    (P.push_sequence P.W001111 (P.ds_of_list tail_counts) after_rhs))
    as [tail_output|] eqn:Erun; cbn beta iota zeta in E; try discriminate.
  inversion E; subst m'; clear E.
  apply and_true_iff in Eguard.
  destruct Eguard as [Hx Hr0]. apply N.leb_le in Hx. apply N.leb_le in Hr0.

  pose proof (chunks_unsnoc_valid bc_xs lhs x Hbc Eleft)
    as [Hlhs Hxpos].
  pose proof (chunks_unsnoc_ok bc_xs) as Hbclist. rewrite Eleft in Hbclist.
  assert (Hlhsne : chunks_list lhs <> []).
  { intro Hnil. rewrite Hbclist,Hnil in Hbc2. cbn in Hbc2. lia. }
  destruct (exists_last Hlhsne) as [ls [y Hlhslist]].

  pose proof (take_last_chunks_spec k rhs [] main tail_counts Hrhs
    (ltac:(constructor)) Etake) as [Hmain [Htailpos Hrhslist]].
  rewrite app_nil_r in Hrhslist.
  pose proof (take_last_chunks_length k rhs [] main tail_counts Etake)
    as Htaillen. cbn in Htaillen.
  assert (Htailne : tail_counts <> []).
  { intro Hnil. rewrite Hnil in Htaillen. cbn in Htaillen. lia. }
  pose proof (chunks_uncons_valid main r0 middle Hmain Eright)
    as [Hr0pos Hmiddle].
  pose proof (chunks_uncons_ok main) as Hmainlist. rewrite Eright in Hmainlist.
  rewrite Hmainlist in Hrhslist.

  assert (Htailinput : valid_side
    (P.push_sequence P.W001111 (P.ds_of_list tail_counts) after_rhs)).
  { eapply valid_push_sequence; [exact I| |exact Hafter].
    rewrite ds_list_of_list. exact Htailpos. }
  pose proof (run_hs_sound 4
    (P.push_sequence P.W001111 (P.ds_of_list tail_counts) after_rhs)
    tail_output Htailinput Erun) as [Htailout Hcalls].
  assert (Htailden :
    denote_side (P.push_sequence P.W001111
      (P.ds_of_list tail_counts) after_rhs) =
    count_bits P.W001111 tail_counts *> denote_side after_rhs).
  { rewrite denote_side_push_sequence by exact I.
    rewrite ds_list_of_list. reflexivity. }
  rewrite Htailden in Hcalls.

  pose proof (N_to_nat_le 2 x Hx) as Hxnat.
  pose proof (N_to_nat_le 4 r0 Hr0) as Hr0nat.
  set (xb := N.to_nat x - 2).
  set (rb := N.to_nat r0 - 4).
  assert (Hx0 : N.to_nat x = S (S xb)) by (unfold xb; cbn in Hxnat; lia).
  assert (Hx1 : N.to_nat (N.pred x) = S xb).
  { rewrite N2Nat.inj_pred,Hx0. reflexivity. }
  assert (Hr00 : N.to_nat r0 = S (S (S (S rb)))) by
    (unfold rb; cbn in Hr0nat; lia).
  assert (Hr01 : N.to_nat (N.sub r0 3) = S rb).
  { rewrite N2Nat.inj_sub,Hr00. reflexivity. }

  set (rhs' := P.chunks_cons (N.pred x)
    (P.chunks_cons (N.sub r0 3) middle)).
  assert (Hrhs' : valid_chunks rhs').
  { unfold rhs'. apply chunks_cons_valid; [apply N_pred_pos2; exact Hx|].
    apply chunks_cons_valid; [apply N_sub3_pos4; exact Hr0|exact Hmiddle]. }
  assert (Hrhs'list : chunks_list rhs' =
    N.pred x :: N.sub r0 3 :: chunks_list middle).
  { unfold rhs'. rewrite !chunks_cons_list. reflexivity. }
  assert (Houtvalid : valid_machine
    (P.machine P.C P.L []
      (P.make_boundary_chunks_right (a+28)%N header lhs
        (P.Lit marker :: P.push_chunks P.W001111 rhs'
          (P.Lit P.sep :: tail_output))) 0%N)).
  { apply make_boundary_chunks_valid; try assumption.
    constructor; [subst marker; discriminate|].
    eapply valid_push_chunks; [exact Hrhs'|].
    constructor; [discriminate|exact Htailout]. }
  split; [exact Houtvalid|].

  subst marker.
  change (List.map sym_of_bool
    [true;true;false;true;true;true;true;true;true;true])
    with ([1;1;0;1;1;1;1;1;1;1] : list Sym).
  destruct Htransparent as [hy Hpass].
  rewrite Hbclist,Hlhslist,Hrhslist.
  change (evstep tm
    (T.Bnd (N.to_nat a) (Str_app (side_bits header)
      (Str_app (count_bits P.W001111 ((ls++[y])++[x]))
        (Str_app [1;1;0;1;1;1;1;1;1;1]
          (Str_app (count_bits P.W001111
            ((r0::chunks_list middle)++tail_counts))
            (denote_side after_rhs))))))
    (denote_machine (P.machine P.C P.L []
      (P.make_boundary_chunks_right (a+28)%N header lhs
        (P.Lit [true;true;false;true;true;true;true;true;true;true] ::
          P.push_chunks P.W001111 rhs' (P.Lit P.sep :: tail_output))) 0%N))).
  pose proof (core_input_den ls y x r0 (chunks_list middle) tail_counts
    (denote_side after_rhs) Htailne) as Hcorein.
  replace (Str_app (side_bits header)
    (Str_app (count_bits P.W001111 ((ls++[y])++[x]))
      (Str_app [1;1;0;1;1;1;1;1;1;1]
        (Str_app (count_bits P.W001111
          ((r0::chunks_list middle)++tail_counts))
          (denote_side after_rhs))))) with
    (Str_app (side_bits header)
      (Str_app (T.Core (List.map N.to_nat ls ++ [N.to_nat y])
        (N.to_nat x) (N.to_nat r0 :: List.map N.to_nat (chunks_list middle)))
        (Str_app (count_bits P.W001111 tail_counts)
          (denote_side after_rhs)))) by (f_equal; symmetry; exact Hcorein).
  rewrite Hx0,Hr00.
  eapply evstep_trans.
  - apply (Bnd_core28_header (side_bits header) hy (N.to_nat a)
      (List.map N.to_nat ls) (N.to_nat y) xb rb
      (List.map N.to_nat (chunks_list middle))
      (count_bits P.W001111 tail_counts *> denote_side after_rhs)
      (denote_side tail_output) Hpass Hcalls).
  - rewrite denote_make_boundary_chunks by exact Hlhs.
    rewrite Hlhslist,denote_lit_cons,
      denote_side_push_chunks by exact Hrhs'.
    rewrite Hrhs'list,denote_lit_cons.
    change (List.map sym_of_bool
      [true;true;false;true;true;true;true;true;true;true])
      with ([1;1;0;1;1;1;1;1;1;1] : list Sym).
    change (List.map sym_of_bool P.sep) with ([1;1;1;1] : list Sym).
    pose proof (core_output_den ls y (N.pred x) (N.sub r0 3)
      (chunks_list middle) (denote_side tail_output)) as Hcoreout.
    change (evstep tm
      (T.Bnd (28 + N.to_nat a)
        (Str_app (side_bits header)
          (Str_app (T.Core (List.map N.to_nat ls) (N.to_nat y)
            (S xb :: S rb :: List.map N.to_nat (chunks_list middle)))
            (denote_side tail_output))))
      (T.Bnd (N.to_nat (a+28)%N)
        (Str_app (side_bits header)
          (Str_app (count_bits P.W001111 (ls++[y]))
            (Str_app [1;1;0;1;1;1;1;1;1;1]
              (Str_app (count_bits P.W001111
                (N.pred x::N.sub r0 3::chunks_list middle))
                (Str_app [1;1;1;1] (denote_side tail_output)))))))).
    rewrite Hcoreout.
    rewrite Hx1,Hr01.
    replace (N.to_nat (a+28)%N) with (28 + N.to_nat a) by
      (rewrite N2Nat.inj_add; cbn; lia).
    finish.
Qed.

Lemma apply_boundary_core_chunks_spec m m' :
  valid_machine m -> P.apply_boundary_core_chunks m = Some m' ->
  valid_machine m' /\ denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_boundary_core_chunks in E.
  destruct (P.parse_boundary_chunks m) as [p|] eqn:Eparse;
    [|discriminate].
  pose proof (parse_boundary_chunks_spec m p Hvalid Eparse) as Hparse.
  destruct Hparse as [_ [_ [_ [Hheader [Hbc [Hbcne [Hbtail
    [Htransparent Hparsed]]]]]]]].
  destruct p as [a header bc_xs boundary_tail].
  cbv beta iota zeta delta [P.bc_header P.bc_xs P.bc_a P.bc_tail] in
    Hheader,Hbc,Hbcne,Hbtail,Htransparent,Hparsed,E |- *.
  destruct boundary_tail as [|block rest]; [discriminate|].
  destruct block as [marker|w n|w ns]; try discriminate.
  destruct (P.bits_eqb marker
    [true;true;false;true;true;true;true;true;true;true] &&
    P.chunks_at_least_two bc_xs)%bool eqn:Eguard; [|discriminate].
  apply and_true_iff in Eguard. destruct Eguard as [Hmarker Htwo].
  apply bits_eqb_eq in Hmarker.
  pose proof (chunks_at_least_two_spec bc_xs Hbc Htwo) as Hbc2.
  destruct (P.collect_chain_chunks (S (length rest)) P.W001111 rest)
    as [[rhs after_rhs]|] eqn:Ecollect; [|discriminate].
  inversion Hbtail as [|? ? Hlit Hrest].
  pose proof (collect_chain_chunks_spec (S (length rest)) P.W001111
    rest rhs after_rhs Hrest Ecollect)
    as [Hrhs [Hrhsne [Hafter Hcollect]]].
  assert (Hrestden : denote_side rest =
    count_bits P.W001111 (chunks_list rhs) *> denote_side after_rhs).
  { unfold denote_side. rewrite Hcollect,Str_app_assoc. reflexivity. }

  destruct (P.apply_boundary_core_split_chunks 1
    {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
       P.bc_tail:=P.Lit marker::rest |} marker rhs after_rhs)
    as [m1|] eqn:Eone.
  - inversion E; subst m'; clear E.
    pose proof (apply_boundary_core_split_chunks_spec
      {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
         P.bc_tail:=P.Lit marker::rest |}
      1 marker rhs after_rhs m1 Hheader Hbc Hbc2 Hrhs Hafter
      Htransparent Hmarker (ltac:(lia)) Eone) as [Hm1 Hstep].
    split.
    + exact Hm1.
    + rewrite (denote_parsed_boundary_chunks m
        {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
           P.bc_tail:=P.Lit marker::rest |} Hvalid Eparse).
      match goal with
      | |- evstep _ _ ?target =>
          change (evstep tm
            (T.Bnd (N.to_nat a) (Str_app (side_bits header)
              (Str_app (count_bits P.W001111 (chunks_list bc_xs))
                (denote_side (P.Lit marker::rest))))) target)
      end.
      rewrite denote_lit_cons,Hrestden.
      exact Hstep.
  - destruct (P.apply_boundary_core_split_chunks 2
      {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
         P.bc_tail:=P.Lit marker::rest |} marker rhs after_rhs)
      as [m2|] eqn:Etwo; [|discriminate].
    inversion E; subst m'; clear E.
    pose proof (apply_boundary_core_split_chunks_spec
      {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
         P.bc_tail:=P.Lit marker::rest |}
      2 marker rhs after_rhs m2 Hheader Hbc Hbc2 Hrhs Hafter
      Htransparent Hmarker (ltac:(lia)) Etwo) as [Hm2 Hstep].
    split.
    + exact Hm2.
    + rewrite (denote_parsed_boundary_chunks m
        {| P.bc_a:=a; P.bc_header:=header; P.bc_xs:=bc_xs;
           P.bc_tail:=P.Lit marker::rest |} Hvalid Eparse).
      match goal with
      | |- evstep _ _ ?target =>
          change (evstep tm
            (T.Bnd (N.to_nat a) (Str_app (side_bits header)
              (Str_app (count_bits P.W001111 (chunks_list bc_xs))
                (denote_side (P.Lit marker::rest))))) target)
      end.
      rewrite denote_lit_cons,Hrestden.
      exact Hstep.
Qed.

Lemma copies_succ_pred_right w n : (0 < n)%N ->
  copies w n = copies w (N.pred n) ++ w.
Proof.
  intro Hn. rewrite <- (N.succ_pred n) at 1 by lia.
  rewrite <- N.add_1_r,copies_add.
  replace (copies w 1%N) with w; [reflexivity|].
  unfold copies. change (w = w ++ []). symmetry; apply app_nil_r.
Qed.

Lemma match_inc1_spec k s im :
  valid_side s -> P.match_inc1 k s = Some im ->
  P.im_kind im = P.Inc1 /\ valid_side (P.im_rest im) /\
  copies (word_bits P.W0011) k *> denote_side s =
    [0;0;1;1]^^(N.to_nat (P.im_a im)) *>
    [0;0;1;1;1;1;1] *>
    [0;0;1;1;1]^^(N.to_nat (P.im_b im)) *>
    [0;1;1;1]^^(N.to_nat (P.im_c im)) *>
    denote_side (P.im_rest im).
Proof.
  intros Hs E. unfold P.match_inc1 in E.
  cbv delta [NCount.is_zero] in E.
  destruct (N.eqb k 0) eqn:Ek; [discriminate|].
  apply N.eqb_neq in Ek.
  destruct (P.strip_bits [true;true;true] s) as [s1|] eqn:Estrip;
    [|discriminate].
  destruct (P.consume_word P.W00111 s1) as [b s2] eqn:Eb.
  destruct (P.consume_word P.W0111 s2) as [c s3] eqn:Ec.
  destruct (P.ge2 c) eqn:Ege; [|discriminate].
  inversion E; subst im; clear E. cbn [P.im_kind P.im_rest P.im_a P.im_b P.im_c].
  pose proof (strip_bits_denote [true;true;true] s s1 Hs Estrip)
    as [Hs1 Hstrip].
  pose proof (consume_word_denote P.W00111 s1 b s2 Hs1 Eb)
    as [Hs2 Hb].
  pose proof (consume_word_denote P.W0111 s2 c s3 Hs2 Ec)
    as [Hs3 Hc].
  split; [reflexivity|]. split; [exact Hs3|].
  rewrite Hstrip,Hb,Hc,copies_succ_pred_right by lia.
  unfold copies,word_bits.
  cbn [P.spelling sym_of_bool List.map].
  repeat rewrite Str_app_assoc. reflexivity.
Qed.

Definition inc2_default (a b : N) (s : P.Side) : option P.IncMatch :=
  let '(c,s2) := P.consume_word P.W01111 s in
  if P.ge2 c then
    Some {| P.im_kind:=P.Inc2; P.im_a:=a; P.im_b:=b;
            P.im_c:=c; P.im_rest:=s2 |}
  else None.

Definition inc2_tail (a b : N) (s : P.Side) : option P.IncMatch :=
  match s with
  | P.Lit [false] :: rest =>
      let '(c,s2) := P.consume_word P.W01111 rest in
      if P.ge3 c then
        Some {| P.im_kind:=P.Inc2; P.im_a:=a; P.im_b:=N.succ b;
                P.im_c:=N.pred c; P.im_rest:=s2 |}
      else None
  | _ => inc2_default a b s
  end.

Lemma inc2_default_spec a b s im :
  valid_side s -> inc2_default a b s = Some im ->
  P.im_kind im = P.Inc2 /\ P.im_a im = a /\
  valid_side (P.im_rest im) /\
  copies (word_bits P.W001111) b *> denote_side s =
    [0;0;1;1;1;1]^^(N.to_nat (P.im_b im)) *>
    [0;1;1;1;1]^^(N.to_nat (P.im_c im)) *>
    denote_side (P.im_rest im).
Proof.
  intros Hs E. unfold inc2_default in E.
  destruct (P.consume_word P.W01111 s) as [c s2] eqn:Ec.
  destruct (P.ge2 c); [|discriminate].
  inversion E; subst im; clear E. cbn.
  pose proof (consume_word_denote P.W01111 s c s2 Hs Ec) as [Hs2 Hden].
  repeat split; try reflexivity; try exact Hs2.
  rewrite Hden. unfold copies,word_bits.
  cbn [P.spelling sym_of_bool List.map]. reflexivity.
Qed.

Lemma inc2_tail_spec a b s im :
  valid_side s -> inc2_tail a b s = Some im ->
  P.im_kind im = P.Inc2 /\ P.im_a im = a /\
  valid_side (P.im_rest im) /\
  copies (word_bits P.W001111) b *> denote_side s =
    [0;0;1;1;1;1]^^(N.to_nat (P.im_b im)) *>
    [0;1;1;1;1]^^(N.to_nat (P.im_c im)) *>
    denote_side (P.im_rest im).
Proof.
  intros Hs E. destruct s as [|block rest].
  - eapply inc2_default_spec; [exact Hs|exact E].
  - destruct block as [bits|w n|w ns];
      try (eapply inc2_default_spec; [exact Hs|exact E]).
    destruct bits as [|bit bits].
    { eapply inc2_default_spec; [exact Hs|exact E]. }
    destruct bit.
    { eapply inc2_default_spec; [exact Hs|exact E]. }
    destruct bits as [|bit bits].
    2: { eapply inc2_default_spec; [exact Hs|exact E]. }
    cbn [inc2_tail] in E.
    inversion Hs as [|? ? Hlit Hrest]; subst.
    destruct (P.consume_word P.W01111 rest) as [c s2] eqn:Ec.
    destruct (P.ge3 c) eqn:Ege; [|discriminate].
    inversion E; subst im; clear E. cbn.
    unfold P.ge3 in Ege. apply N.leb_le in Ege.
    change (3 <= c)%N in Ege.
    pose proof (consume_word_denote P.W01111 rest c s2 Hrest Ec)
      as [Hs2 Hden].
    repeat split; try reflexivity; try exact Hs2.
    change (Str_app (copies (word_bits P.W001111) b)
      (denote_side (P.Lit [false]::rest)) =
      Str_app ([0;0;1;1;1;1]^^(N.to_nat (N.succ b)))
        (Str_app ([0;1;1;1;1]^^(N.to_nat (N.pred c)))
          (denote_side s2))).
    assert (Hcpos : (0 < c)%N).
    { lia. }
    rewrite denote_lit_cons,Hden,
      (copies_succ_pred (word_bits P.W01111) c Hcpos).
    unfold copies,word_bits. cbn [P.spelling sym_of_bool List.map].
    change (Str_app ([0;0;1;1;1;1]^^(N.to_nat b))
      (Str_app [0;0;1;1;1;1]
        (Str_app ([0;1;1;1;1]^^(N.to_nat (N.pred c)))
          (denote_side s2))) =
      Str_app ([0;0;1;1;1;1]^^(N.to_nat (N.succ b)))
        (Str_app ([0;1;1;1;1]^^(N.to_nat (N.pred c)))
          (denote_side s2))).
    rewrite N2Nat.inj_succ. cbn [lpow].
    rewrite <- Str_app_assoc. f_equal. apply lpow_shift.
Qed.

Lemma match_inc2_spec k s im :
  valid_side s -> P.match_inc2 k s = Some im ->
  P.im_kind im = P.Inc2 /\ valid_side (P.im_rest im) /\
  copies (word_bits P.W0011) k *> denote_side s =
    [0;0;1;1]^^(N.to_nat (P.im_a im)) *>
    [0;0;1;1;1;1]^^(N.to_nat (P.im_b im)) *>
    [0;1;1;1;1]^^(N.to_nat (P.im_c im)) *>
    denote_side (P.im_rest im).
Proof.
  intros Hs E. unfold P.match_inc2 in E.
  destruct (P.strip_bits [true;true] s) as [s'|] eqn:Estrip.
  - destruct (NCount.is_zero k) eqn:Ek.
    + change (inc2_tail k 0 s = Some im) in E.
      pose proof (inc2_tail_spec k 0 s im Hs E)
        as [Hkind [Ha [Hrest Htail]]].
      split; [exact Hkind|]. split; [exact Hrest|].
      unfold NCount.is_zero in Ek. apply N.eqb_eq in Ek. subst k.
      rewrite Ha. cbn [copies lpow] in Htail |- *. exact Htail.
    + destruct (P.consume_word P.W001111 s') as [n s''] eqn:En.
      change (inc2_tail (N.pred k) (N.succ n) s'' = Some im) in E.
      unfold NCount.is_zero in Ek. apply N.eqb_neq in Ek.
      pose proof (strip_bits_denote [true;true] s s' Hs Estrip)
        as [Hs' Hstrip].
      pose proof (consume_word_denote P.W001111 s' n s'' Hs' En)
        as [Hs'' Hn].
      pose proof (inc2_tail_spec (N.pred k) (N.succ n) s'' im Hs'' E)
        as [Hkind [Ha [Hrest Htail]]].
      split; [exact Hkind|]. split; [exact Hrest|].
      rewrite Hstrip,Hn,copies_succ_pred_right by lia.
      rewrite Ha. rewrite <- Htail.
      unfold copies,word_bits. cbn [P.spelling sym_of_bool List.map].
      rewrite Str_app_assoc.
      change
        (Str_app ([0;0;1;1]^^N.to_nat (N.pred k))
          (Str_app [0;0;1;1;1;1]
            (Str_app ([0;0;1;1;1;1]^^N.to_nat n)
              (denote_side s''))) =
         Str_app ([0;0;1;1]^^N.to_nat (N.pred k))
          (Str_app ([0;0;1;1;1;1]^^N.to_nat (N.succ n))
            (denote_side s''))).
      f_equal. rewrite N2Nat.inj_succ. cbn [lpow].
      rewrite <- Str_app_assoc. reflexivity.
  - destruct (P.consume_word P.W001111 s) as [n s'] eqn:En.
    change (inc2_tail k n s' = Some im) in E.
    pose proof (consume_word_denote P.W001111 s n s' Hs En)
      as [Hs' Hn].
    pose proof (inc2_tail_spec k n s' im Hs' E)
      as [Hkind [Ha [Hrest Htail]]].
    split; [exact Hkind|]. split; [exact Hrest|].
    rewrite Ha,Hn,Htail. reflexivity.
Qed.

Definition inc_source (im : P.IncMatch) : state * tape :=
  match P.im_kind im with
  | P.Inc1 => T.S1 (N.to_nat (P.im_a im)) (N.to_nat (P.im_b im))
                  (N.to_nat (P.im_c im)) (denote_side (P.im_rest im))
  | P.Inc2 => T.S2 (N.to_nat (P.im_a im)) (N.to_nat (P.im_b im))
                  (N.to_nat (P.im_c im)) (denote_side (P.im_rest im))
  end.

Lemma match_inc_spec m im :
  valid_machine m -> P.match_inc m = Some im ->
  valid_side (P.im_rest im) /\ denote_machine m = inc_source im.
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. unfold P.match_inc in E.
  destruct q,d,l;
    cbv beta delta [P.m_state P.m_dir P.m_left P.m_right] iota zeta in E;
    try discriminate.
  destruct (P.strip_bits [true;true] r) as [s|] eqn:Estrip;
    [|discriminate].
  destruct (P.consume_word P.W0011 s) as [k s'] eqn:Econsume.
  pose proof (strip_bits_denote [true;true] r s Hr Estrip)
    as [Hs Hstrip].
  pose proof (consume_word_denote P.W0011 s k s' Hs Econsume)
    as [Hs' Hconsume].
  destruct (P.match_inc1 k s') as [im'|] eqn:Einc1.
  - inversion E; subst im'; clear E.
    pose proof (match_inc1_spec k s' im Hs' Einc1)
      as [Hkind [Hrest Htail]].
    split; [exact Hrest|].
    unfold inc_source. rewrite Hkind.
    unfold denote_machine,T.S1. cbn [P.m_dir P.m_left P.m_right
      P.m_state denote_q denote_side side_bits].
    rewrite Hstrip,Hconsume,Htail. cbn [List.map sym_of_bool]. reflexivity.
  - pose proof (match_inc2_spec k s' im Hs' E)
      as [Hkind [Hrest Htail]].
    split; [exact Hrest|].
    unfold inc_source. rewrite Hkind.
    unfold denote_machine,T.S2. cbn [P.m_dir P.m_left P.m_right
      P.m_state denote_q denote_side side_bits].
    rewrite Hstrip,Hconsume,Htail. cbn [List.map sym_of_bool]. reflexivity.
Qed.

Lemma parity_decomp n :
  N.to_nat n = 2 * N.to_nat (N.div2 n) + N.to_nat (P.parity n).
Proof.
  pose proof (N.div2_odd n) as H.
  assert (Hp : P.parity n = N.b2n (N.odd n)).
  { unfold P.parity,NCount.odd,NCount.one,NCount.zero.
    destruct (N.odd n); reflexivity. }
  rewrite <- Hp in H. apply (f_equal N.to_nat) in H.
  rewrite N2Nat.inj_add,N2Nat.inj_mul in H. exact H.
Qed.

Lemma apply_inc_valid m m' :
  valid_machine m -> P.apply_inc m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_inc in E.
  destruct (P.match_inc m) as [im|] eqn:Ematch; [|discriminate].
  pose proof (match_inc_spec m im Hvalid Ematch) as [Hrest _].
  destruct im as [kind a b c rest]. destruct kind.
  - cbn [P.im_kind P.im_a P.im_b P.im_c P.im_rest] in E;
      inversion E; subst m'; clear E.
    cbn [P.im_rest] in Hrest.
    unfold valid_machine; cbn [P.machine P.m_left P.m_right]. split.
    + constructor.
    + change (valid_side
        (P.push_lit [true;true]
          (P.push_run P.W0011 (N.add a (N.mul 3 (N.div2 c)))
            (P.push_lit [false;false;true;true;true;true;true]
              (P.push_run P.W00111 (N.add b (N.div2 c))
                (P.push_run P.W0111 (P.parity c) rest)))))).
      apply valid_push_lit,valid_push_run,valid_push_lit,
        valid_push_run,valid_push_run. exact Hrest.
  - cbn [P.im_kind P.im_a P.im_b P.im_c P.im_rest] in E;
      inversion E; subst m'; clear E.
    cbn [P.im_rest] in Hrest.
    unfold valid_machine; cbn [P.machine P.m_left P.m_right]. split.
    + constructor.
    + change (valid_side
        (P.push_lit [true;true]
          (P.push_run P.W0011 (N.add a (N.mul 4 (N.div2 c)))
            (P.push_run P.W001111 (N.add b (N.div2 c))
              (P.push_run P.W01111 (P.parity c) rest))))).
      apply valid_push_lit,valid_push_run,valid_push_run,valid_push_run.
      exact Hrest.
Qed.

Lemma denote_inc1_output a b c rest inc :
  denote_machine
    (P.machine P.C P.L []
      (P.push_lit [true;true]
        (P.push_run P.W0011 (N.add a (N.mul 3 (N.div2 c)))
          (P.push_lit [false;false;true;true;true;true;true]
            (P.push_run P.W00111 (N.add b (N.div2 c))
              (P.push_run P.W0111 (P.parity c) rest))))) inc) =
  T.S1 (N.to_nat (N.add a (N.mul 3 (N.div2 c))))
       (N.to_nat (N.add b (N.div2 c))) (N.to_nat (P.parity c))
       (denote_side rest).
Proof.
  unfold denote_machine,T.S1. cbn [P.machine P.m_dir P.m_left
    P.m_right P.m_state denote_q].
  repeat first [rewrite denote_side_push_lit | rewrite denote_side_push_run].
  cbn [denote_side side_bits].
  unfold copies,word_bits. cbn [P.spelling sym_of_bool List.map]. reflexivity.
Qed.

Lemma denote_inc2_output a b c rest inc :
  denote_machine
    (P.machine P.C P.L []
      (P.push_lit [true;true]
        (P.push_run P.W0011 (N.add a (N.mul 4 (N.div2 c)))
          (P.push_run P.W001111 (N.add b (N.div2 c))
            (P.push_run P.W01111 (P.parity c) rest)))) inc) =
  T.S2 (N.to_nat (N.add a (N.mul 4 (N.div2 c))))
       (N.to_nat (N.add b (N.div2 c))) (N.to_nat (P.parity c))
       (denote_side rest).
Proof.
  unfold denote_machine,T.S2. cbn [P.machine P.m_dir P.m_left
    P.m_right P.m_state denote_q].
  repeat first [rewrite denote_side_push_lit | rewrite denote_side_push_run].
  cbn [denote_side side_bits].
  unfold copies,word_bits. cbn [P.spelling sym_of_bool List.map]. reflexivity.
Qed.

Lemma apply_inc_sound m m' :
  valid_machine m -> P.apply_inc m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_inc in E.
  destruct (P.match_inc m) as [im|] eqn:Ematch; [|discriminate].
  pose proof (match_inc_spec m im Hvalid Ematch) as [Hrest Hsource].
  destruct im as [kind a b c rest]. destruct kind.
  - cbn [P.im_kind P.im_a P.im_b P.im_c P.im_rest] in E,Hsource;
      inversion E; subst m'; clear E.
    rewrite Hsource.
    change
      (T.S1 (N.to_nat a) (N.to_nat b) (N.to_nat c) (denote_side rest)
        -[tm]->*
       denote_machine
        (P.machine P.C P.L []
          (P.push_lit [true;true]
            (P.push_run P.W0011 (N.add a (N.mul 3 (N.div2 c)))
              (P.push_lit [false;false;true;true;true;true;true]
                (P.push_run P.W00111 (N.add b (N.div2 c))
                  (P.push_run P.W0111 (P.parity c) rest)))))
          (N.succ (P.m_incs m)))).
    rewrite denote_inc1_output,(parity_decomp c).
    replace (N.to_nat (N.add a (N.mul 3 (N.div2 c))))
      with (3 * N.to_nat (N.div2 c) + N.to_nat a)
      by (rewrite N2Nat.inj_add,N2Nat.inj_mul; lia).
    replace (N.to_nat (N.add b (N.div2 c)))
      with (N.to_nat (N.div2 c) + N.to_nat b)
      by (rewrite N2Nat.inj_add; lia).
    apply T.Inc1s.
  - cbn [P.im_kind P.im_a P.im_b P.im_c P.im_rest] in E,Hsource;
      inversion E; subst m'; clear E.
    rewrite Hsource.
    change
      (T.S2 (N.to_nat a) (N.to_nat b) (N.to_nat c) (denote_side rest)
        -[tm]->*
       denote_machine
        (P.machine P.C P.L []
          (P.push_lit [true;true]
            (P.push_run P.W0011 (N.add a (N.mul 4 (N.div2 c)))
              (P.push_run P.W001111 (N.add b (N.div2 c))
                (P.push_run P.W01111 (P.parity c) rest))))
          (N.succ (P.m_incs m)))).
    rewrite denote_inc2_output,(parity_decomp c).
    replace (N.to_nat (N.add a (N.mul 4 (N.div2 c))))
      with (4 * N.to_nat (N.div2 c) + N.to_nat a)
      by (rewrite N2Nat.inj_add,N2Nat.inj_mul; lia).
    replace (N.to_nat (N.add b (N.div2 c)))
      with (N.to_nat (N.div2 c) + N.to_nat b)
      by (rewrite N2Nat.inj_add; lia).
    apply T.Inc2s.
Qed.

Lemma apply_boundary_sound m m' :
  valid_machine m -> P.apply_boundary m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_boundary in E.
  destruct (P.apply_boundary_core m) as [m1|] eqn:Ecore.
  - unfold P.apply_boundary_core in Ecore.
    pose proof (proj2 (apply_boundary_core_chunks_spec m m1 Hvalid Ecore))
      as Hstep.
    inversion E; subst; exact Hstep.
  - eapply apply_boundary_plain_sound; eassumption.
Qed.

Lemma apply_boundary_valid m m' :
  valid_machine m -> P.apply_boundary m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E. unfold P.apply_boundary in E.
  destruct (P.apply_boundary_core m) as [m1|] eqn:Ecore.
  - unfold P.apply_boundary_core in Ecore.
    pose proof (proj1 (apply_boundary_core_chunks_spec m m1 Hvalid Ecore))
      as Hvalid1.
    inversion E; subst; exact Hvalid1.
  - eapply apply_boundary_plain_valid; eassumption.
Qed.

Lemma astep_sound m m' :
  valid_machine m -> P.astep m = Some m' ->
  denote_machine m -[tm]->* denote_machine m'.
Proof.
  intros Hvalid E. unfold P.astep in E.
  destruct (P.apply_inc m) as [mi|] eqn:Ei.
  - inversion E; subst. eapply apply_inc_sound; eassumption.
  - destruct (P.apply_boundary m) as [mb|] eqn:Eb.
    + inversion E; subst. eapply apply_boundary_sound; eassumption.
    + destruct (P.apply_chain m) as [mc|] eqn:Ec.
      * inversion E; subst. eapply apply_chain_sound; eassumption.
      * destruct (P.apply_shift m) as [ms|] eqn:Es.
        -- inversion E; subst. eapply apply_shift_sound; eassumption.
        -- eapply raw_burst_sound; eassumption.
Qed.

Lemma astep_valid m m' :
  valid_machine m -> P.astep m = Some m' -> valid_machine m'.
Proof.
  intros Hvalid E. unfold P.astep in E.
  destruct (P.apply_inc m) as [mi|] eqn:Ei.
  - inversion E; subst. eapply apply_inc_valid; eassumption.
  - destruct (P.apply_boundary m) as [mb|] eqn:Eb.
    + inversion E; subst. eapply apply_boundary_valid; eassumption.
    + destruct (P.apply_chain m) as [mc|] eqn:Ec.
      * inversion E; subst. eapply apply_chain_valid; eassumption.
      * destruct (P.apply_shift m) as [ms|] eqn:Es.
        -- inversion E; subst. eapply apply_shift_valid; eassumption.
        -- eapply raw_burst_valid; eassumption.
Qed.

Lemma raw_step_none_halted m :
  valid_machine m -> P.raw_step m = None -> halted tm (denote_machine m).
Proof.
  destruct m as [q d l r inc]. cbn [valid_machine] in *.
  intros [Hl Hr] E. destruct d.
  - destruct (P.pop_bit l) as [bit l'] eqn:Epop.
    pose proof (pop_bit_same l Hl) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.L; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,l')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in E. rewrite Epop0 in E. cbn [P.active] in E.
    destruct q,bit; cbn [P.trans] in E; try discriminate;
      unfold halted,denote_machine;
      cbv delta [P.m_dir P.m_left P.m_right P.m_state] iota zeta;
      cbn [denote_q]; unfold denote_side in Hpop |- *; rewrite Hpop;
      reflexivity.
  - destruct (P.pop_bit r) as [bit r'] eqn:Epop.
    pose proof (pop_bit_same r Hr) as Hpop. rewrite Epop in Hpop.
    assert (Epop0 :
      P.pop_bit (P.active
        {| P.m_state:=q; P.m_dir:=P.R; P.m_left:=l;
           P.m_right:=r; P.m_incs:=inc |}) = (bit,r')).
    { cbn [P.active P.machine]. exact Epop. }
    unfold P.raw_step in E. rewrite Epop0 in E. cbn [P.active] in E.
    destruct q,bit; cbn [P.trans] in E; try discriminate;
      unfold halted,denote_machine;
      cbv delta [P.m_dir P.m_left P.m_right P.m_state] iota zeta;
      cbn [denote_q]; unfold denote_side in Hpop |- *; rewrite Hpop;
      reflexivity.
Qed.

Lemma astep_none_halted m :
  valid_machine m -> P.astep m = None -> halted tm (denote_machine m).
Proof.
  intros Hvalid E. unfold P.astep in E.
  destruct (P.apply_inc m); [discriminate|].
  destruct (P.apply_boundary m); [discriminate|].
  destruct (P.apply_chain m); [discriminate|].
  destruct (P.apply_shift m); [discriminate|].
  unfold P.raw_burst in E.
  destruct (P.raw_step m) eqn:Eraw; [discriminate|].
  eapply raw_step_none_halted; eassumption.
Qed.

Definition run_inv (m : P.Machine) : Prop :=
  valid_machine m /\ c0 -[tm]->* denote_machine m.


Definition exec_property (s : P.Machine + P.Machine) : Prop :=
  match s with
  | inl m => run_inv m
  | inr _ => halts tm c0
  end.

Lemma exec_until_step_property m :
  run_inv m -> exec_property (P.exec_until_step m).
Proof.
  intros [Hvalid Hreach]. unfold P.exec_until_step,exec_property.
  destruct (P.astep m) as [m'|] eqn:E.
  - split.
    + eapply astep_valid; eassumption.
    + eapply evstep_trans; [exact Hreach|].
      eapply astep_sound; eassumption.
  - eapply halts_evstep; [|exact Hreach].
    exists O, (denote_machine m). split; [constructor|].
    eapply astep_none_halted; eassumption.
Qed.

Lemma exec_until_chunks_spec chunk_size chunks s :
  exec_property s ->
  exec_property (P.exec_until_chunks chunk_size chunks s).
Proof.
  revert s. induction chunks as [|chunks IH]; intros [m|m] H.
  - exact H.
  - exact H.
  - change (exec_property
      (P.exec_until_chunks chunk_size chunks
        (N_iter_until P.exec_until_step (inl m) chunk_size))).
    apply IH.
    eapply N_iter_until_spec; [|exact H].
    intros m' Hm'. exact (exec_until_step_property m' Hm').
  - exact H.
Qed.

Lemma run_exec_until_chunks_spec chunks :
  exec_property (P.run_exec_until_chunks chunks).
Proof.
  unfold P.run_exec_until_chunks. apply exec_until_chunks_spec.
  split; [apply valid_init|]. rewrite denote_init. finish.
Qed.

Definition stoppedb (s : P.Machine + P.Machine) : bool :=
  match s with
  | inl _ => false
  | inr _ => true
  end.

Lemma stoppedb_sound s :
  exec_property s -> stoppedb s = true -> halts tm c0.
Proof.
  destruct s; cbn [exec_property stoppedb].
  - discriminate.
  - intros H _. exact H.
Qed.

Lemma run_stoppedb_sound chunks :
  stoppedb (P.run_exec_until_chunks chunks) = true -> halts tm c0.
Proof.
  intro Hcheck.
  eapply stoppedb_sound with (s := P.run_exec_until_chunks chunks).
  - apply run_exec_until_chunks_spec.
  - exact Hcheck.
Qed.

(* This is the only long computation in the file.  It evaluates a Boolean;
   [stoppedb_sound] separately turns the result into the semantic theorem. *)
Lemma halt : halts tm c0.
Proof.
  apply (run_stoppedb_sound 25).
  native_check_eq.
Time Qed.

Print Assumptions halt.

