Inductive game: Set :=
  | _game : list game -> list game -> game
.

Ltac inv H := inversion H; subst; clear H.
Ltac gen H a :=
    generalize (H a); clear H; intro H.

Require Import List.

Inductive gle: game -> game -> bool -> Prop :=
| gle_t: forall XL XR YL YR,
    (forall xL, In xL XL -> gle (_game YL YR) xL false) ->
    (forall yR, In yR YR -> gle yR (_game XL XR) false) ->
    gle (_game XL XR) (_game YL YR) true
| gle_fxL: forall XL XR YL YR,
     (exists xL, In xL XL /\ gle (_game YL YR) xL true) ->
     gle (_game XL XR) (_game YL YR) false
| gle_fyR: forall XL XR YL YR,
     (exists yR, In yR YR /\ gle yR (_game XL XR) true) ->
     gle (_game XL XR) (_game YL YR) false
.
    

Definition zero := _game nil nil.
Definition one  := _game (zero :: nil) nil.

Lemma nn: gle zero zero true.
  apply gle_t.
  intros.
  inv H.

  intros.
  inv H.
Qed.

Lemma refl: forall g, gle g g true.
  induction g.
Abort.

Inductive part: game -> game -> Prop :=
  | part_l: forall l L R,
      In l L -> part l (_game L R)
  | part_r: forall r L R,
      In r R -> part r (_game L R)
.

Inductive size: game -> nat -> Prop :=
| size_nil: size (_game nil nil) O
| size_lcons: forall L R l sg sl,
  size (_game L R) sg ->
  size l sl ->
  size (_game (l :: L) R) (sg + sl + 1)
| size_rcons: forall L R r sg sr,
  size (_game L R) sg ->
  size r sr ->
  size (_game L (r :: R)) (sg + sr + 1)
.

Theorem gind:
  forall (P: game -> Prop),
    (forall L R,
      (forall l, In l L -> P l) ->
      (forall r, In r R -> P r) ->
      P (_game L R)) ->
    forall g, P g.
  generalize Fix_F.
  intro FF.
  gen FF game.
  gen FF part.
  intro P.
  gen FF P.
  intro IH.

  assert (forall x : game, (forall y : game, part y x -> P y) -> P x).
  clear FF.
  intro x.

  destruct x as [L R].

  gen IH L.
  gen IH R.

  intro y.
  apply IH.
  intros.
  apply y.
  apply part_l.
  assumption.

  intro r.
  intro inR.
  apply y.
  apply part_r.
  assumption.

  gen FF H.
  clear H.
  clear IH.
  intro g.
  gen FF g.
  apply FF.
  clear FF.

  Require Import Wf_nat.
  apply acc_lt_rel with size.
  intros.
  inv H.
  unfold inv_lt_rel.


  
  
(* well, we need an induction principle *)




(* gle x x for all games *)
(* trans for all games, induction on (x, z) *)

(* left <== self *)



