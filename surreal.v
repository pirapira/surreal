Inductive game :=
| nilnil: game
| lcons: game -> game -> game
| rcons: game -> game -> game
.

(* list game -> list game -> game は破滅 *)

Require Import List.

Fixpoint display (g: game): (list game * list game) :=
  match g with
    | nilnil => (nil, nil)
    | lcons e _g =>
      match display _g with
        (l_g, r_g) => (e :: l_g, r_g)
      end
    | rcons e _g =>
      match display _g with
        (l_g, r_g) => (l_g, e :: r_g)
      end
  end.

(* it would be interesting to compare this to
   sb's phd thesis *)



Require Import Arith.Wf_nat.

Fixpoint size (g: game) :=
  match g with
    | nilnil => O
    | lcons e h => size e + size h + 1
    | rcons e h => size e + size h + 1
  end.

Definition sumsize yx := match yx with (y,x) => size y + size x end.

Require Import Program.Wf.
Require Import Omega.
(* no xR <= y *) (* no x <= yL *)

Inductive gle := 

Definition zero := nilnil.
Definition one  := lcons zero zero.

Eval compute in (gle (one,one)).



(* gle x x for all games *)
(* trans for all games, induction on (x, z) *)

(* left <== self *)



