(** October 30 BB(6) line 608, bbchallenge ID 181655.

    Fractal Geometry Explorer proved this machine halts from blank. The
    theorem below imports the author's published proof and checks the
    transition table against BusyCoq's literal representation. The proof
    adapts the fast engine of BusyCoq PR 93 and proves a detour lemma.

    From verify/ with Individual62.vo built, fetch and check the pinned source:

    curl -fL -o H181655.v https://raw.githubusercontent.com/fractal-geometry-explorer/busy-beaver-explorer/c409c4b292369cb404e939753004bd1216fa3333/holdouts/1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE/coq/H181655.v
    echo '81de298d6244da5ebc83fb7da43a63adcbb01699b73dcdfa0e3f6485de6a8ede  H181655.v' | sha256sum -c -
    coqc -Q . BusyCoq H181655.v
    coqc -Q . BusyCoq M_1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RAHHH_0LB0LE.v

    The author's build log is next to H181655.v in the pinned source. *)
From BusyCoq Require Import Individual62.
From BusyCoq Require H181655.
From Coq Require Import String.

Definition tm : TM :=
  TM_from_str "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE"%string.

Definition halt : halts tm c0 := H181655.halt.
Print Assumptions halt.
