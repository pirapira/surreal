Inductive step (orig: Type): Type :=
  | compose: (orig -> Prop) -> (orig -> Prop) -> step orig
.

Inductive empty: Type := .

Fixpoint game (m: nat): Type :=
  match m with
   | O => empty
   | S m' => step (game m')
  end.



Definition sg: forall m, (step (game m)) -> game (S m) := (fun _ x => x).
    
Ltac inv H := inversion H; subst; clear H.
Ltac gen H a :=
    generalize (H a); clear H; intro H.

(* are they needed ?

Axiom ex_bool: forall {A} (f g: A -> bool),
  (forall (a: A), f a = g a) -> f = g.

Lemma empty_uniq: forall
  (x y: empty -> bool),
  x = y.
  intros.
  apply ex_bool.
  intros.
  inv a.
Qed.

*)

(*
Fixpoint gle m n (x: game m) (y: game n): bool :=
  match (x, y) with
    | (inherit _ x', y) => gle _ _ x' y
    | (_, inherit _ h') => gle _ _ x y'
    | (compose _
termination is nasty
*)

Inductive gle: forall m n, game m -> game n -> bool -> Prop :=
| gle_St: forall m n (xL: game m -> Prop) xR yL (yR: game n -> Prop),
  (forall xl, xL xl -> gle (S n) _ (compose (game n) yL yR) xl false) ->
  (forall yr, yR yr -> gle _ (S m) yr (compose (game m) xL xR) false) ->
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) true
| gle_Sfl: forall m n (xL: game m -> Prop) xR y,
  (exists xl, xL xl /\ gle n _ y xl true) ->
  gle (S m) n (compose (game m) xL xR) y false
| gle_Sfr: forall m n x yL (yR: game n -> Prop),
  (exists yr, yR yr /\ gle _ m yr x true) ->
  gle m (S n) x (compose (game n) yL yR) false
.


Lemma refl: forall m (g: game m), gle _ _ g g true.
induction m.
intro g.
destruct g.

intro g.
destruct g; fold game in *.

rename P into L.
rename P0 into R.
apply gle_St.

intros.
apply gle_Sfl.
exists xl.
intuition.

intros.
apply gle_Sfr.
exists yr.
intuition.
Qed.


Definition charm: game 0 -> Prop.
intro.
destruct X.
Defined.



Definition zero: game 1 := compose _ charm charm.
Definition one : game 2 := compose _ (fun _ => True) (fun _ => False).
Definition half: game 3 := compose _ (fun x => x = zero) (fun y => y = one).

Lemma zero_one: gle _ _ zero one.
  compute.
  intuition.
Qed.

Lemma one_zero: gle _ _ one zero -> False.
  compute.
  intuition.
  clear H1.
  gen H0 zero.
  apply H0.
  auto.
  compute.
  intuition.
Qed.

Lemma zero_zero: gle _ _ zero zero.
  compute.
  intuition.
Qed.

Lemma one_one: gle _ _ one one.
  compute.
  intuition.
  destruct xl.
  inv e.
  intuition.
  clear H2.
  apply H1 with zero.
  auto.
  compute.
  intuition.
Qed.

Lemma zero_half: gle _ _ zero half.
  compute.
  intuition.
  subst.
  intuition.
  clear H1.
  gen H zero.
  intuition.
  apply H0.
  compute.
  intuition.
Qed.
  
(* next, reflexivity of gle *)
Lemma refl: forall m g, gle m m g g.
  induction m.
  intros.
  inv g.

  intros.
  destruct g; fold game in *.

  unfold gle.
  simpl.


