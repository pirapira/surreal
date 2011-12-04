(* hard ****)

Inductive step (orig: Set): Set :=
  | inherit: orig -> step orig
  | compose: list orig -> list orig -> step orig
.


Fixpoint game (m: nat): Set :=
  match m with
   | O => unit
   | S m' => step (game m')
  end.
    
Ltac inv H := inversion H; subst; clear H.
Ltac gen H a :=
    generalize (H a); clear H; intro H.

Require Import List.

Definition ok_yRx (_x _yR:Set) (x: _x) (yR: list _yR) (le: _yR -> _x -> bool): bool :=
 negb (existsb (fun yr => le yr x) yR).

Definition ok_yxL (_xL _y:Set) (xL: list _xL) (y: _y) (le: _y -> _xL -> bool): bool :=
 negb (existsb (fun xl => le y xl) xL).

Definition _gle: forall s, forall m n, m + n <= s -> game m -> game n -> bool.
induction s.
intros.
exact (true).

intros m n H x y.
destruct m; destruct n.
exact (true).

case_eq y.
fold game.
intro y_content.
intro y_eq.
refine (IHs 0 n _ x y_content).
Require Omega.
omega.

fold game.
intros L R.
intro y_eq.
clear y_eq.
clear L.
rename R into yR.
gen IHs n.
gen IHs O.
assert (n + 0 <= s).
omega.
gen IHs H0.
clear H0.
generalize ok_yRx.
intro ok.
gen ok (game O).
gen ok (game n).
exact (ok x yR IHs).

case_eq x.
fold game.
intro x_content.
intro x_eq.
gen IHs m.
gen IHs O.
apply IHs.
omega.
exact x_content.
exact y.
fold game.
intros xL xR.
intro x_eq.
generalize ok_yxL.
intro ok.
gen ok (game m).
gen ok (game O).
refine (ok xL y _ ).
gen IHs O.
gen IHs m.
apply IHs.
omega.

case_eq x; fold game; case_eq y; fold game.
intro y_content.
intro y_eq.
clear y y_eq.
intro x_content.
intro x_eq.
clear x_eq x.
gen IHs m.
gen IHs n.
apply IHs.
omega.
exact x_content.
exact y_content.


intros yL yR.
intro y_eq.
clear yL yR y_eq.
intro x_content.
intro x_eq.
clear x x_eq.
gen IHs m.
gen IHs (S n).
apply IHs.
omega.
exact x_content.
exact y.

intro y_content.
intro y_eq.
clear y_eq y.
intros _ _ _.
gen IHs (S m).
gen IHs n.
apply IHs.
omega.
exact x.
exact y_content.

intros yL yR.
intro y_eq.
intros xL xR.
intro x_eq.

refine (andb _ _); [ generalize ok_yxL | generalize ok_yRx ].
intro ok.
clear x_eq y_eq xR x yL yR.
gen ok (game m).
gen ok (game (S n)).
apply ok.
apply xL.
apply y.
apply IHs.
omega.

clear x_eq xL xR.
clear y_eq y yL.
intro ok.
gen ok (game (S m)).
gen ok (game n).
apply ok.
apply x.
apply yR.
apply IHs.
omega.
Defined.

Definition gle { m n }: game m -> game n -> bool.
generalize _gle.
intro _gle.
gen _gle (m + n).
apply _gle.
omega.
Defined.  


Definition zero : game O := tt.

Definition one : game (S O) := compose unit (zero :: nil) nil.
Definition neg_one : game (S O) := compose unit nil (zero :: nil).

Eval compute in (gle one zero). (* false *)
Eval compute in (gle zero zero). (* true *)
Eval compute in (gle neg_one zero). (* true *)
Eval compute in (gle one zero). (* false *)

Lemma inhL: forall m n (Sg: game (S n)) g g',
  Sg = (inherit (game m) g) ->
  gle Sg g' = gle g g'.

Lemma refl: forall m (g: game m), gle g g = true.
induction m.

(* base case *)
intro g.
destruct g.
reflexivity.

(* S *)
intro g.
destruct g.
fold game in *.
unfold gle.