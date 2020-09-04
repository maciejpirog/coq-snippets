(* 2019 Maciej Piróg

A simplified version of a proof by Andrej Bauer and Peter LeFanu Lumsdaine
<https://ncatlab.org/nlab/files/BauerLumsdaineUnivalence.pdf>
that univalence implies extensional equality. This version highlights the
central lemma (eqv_mono), which states that equivalences are monomorphisms (in the
categorical sense).
*)

Definition id {A : Type} (x : A) : A := x.

Definition comp {A B X : Type} (e : A -> B) (f : X -> A) (x : X) : B :=
  e (f x).

Notation " g · f " := (comp g f) (at level 40, left associativity).

Definition homo {A B : Type} (f g : A -> B) := forall x, f x = g x.

Notation " f ~~ g " := (homo f g) (at level 41, no associativity).

Hint Unfold homo.

Inductive is_eqv {A B : Type} (e : A -> B) : Type :=
  is_eqvC (g : B -> A) (leftInverse  : g · e ~~ id)
          (h : B -> A) (rightInverse : e · h ~~ id).

Inductive Equivalence (A B : Type) : Type :=
  EquivalenceC (e : A -> B) (EQV : is_eqv e).

Notation " A ≅ B " := (Equivalence A B) (at level 40, no associativity).

Definition underlying {A B : Type} (e : A ≅ B) : A -> B :=
match e with
| EquivalenceC _ _ f _ => f
end.

Ltac refine_eqv e g h :=
  refine (EquivalenceC _ _ e (is_eqvC e g _ h _)).

Definition eq_to_eqv {A B : Type} (p : A = B) : A ≅ B.
Proof.
destruct p.
refine_eqv (id(A:=A)) (id(A:=A)) (id(A:=A)); auto.
Defined.

Axiom univalence : forall {A B : Type}, is_eqv (eq_to_eqv(A:=A)(B:=B)).

Lemma eqv_to_eq {A B : Type} (e : A ≅ B) :
  {p : A = B | e = eq_to_eqv p}.
Proof.
destruct (univalence(A:=A)(B:=B)).
exists (h e).
symmetry.
apply rightInverse.
Qed.

Definition mono {A B : Type} (f : A -> B) :=
  forall (X : Type) (g h : X -> A), f · g = f · h -> g = h.

Lemma id_comp : forall {A B : Type} (f : A -> B), id · f = f.
Proof.
intros.
unfold id.
unfold comp.
change (fun x => f x) with f. (* eta *)
reflexivity.
Qed.

Lemma eqv_mono : forall {A B : Type} (e : A ≅ B), mono (underlying e).
Proof.
repeat intro.
destruct (eqv_to_eq e) as [p EQV].
destruct p.
rewrite EQV in H.
simpl in H.
repeat rewrite id_comp in H.
assumption.
Qed.

Section Paths.

Variable A : Type.

Inductive Path := PathC (e1 e2 : A) (p : e1 = e2).

Definition refl_path (a : A) : Path := PathC a a eq_refl.

Definition Path_proj1 (p : Path) : A :=
match p with
| PathC e _ _ => e
end.

Definition Path_proj2 (p : Path) : A :=
match p with
| PathC _ e _ => e
end.

Definition Path_proj1_eqv : Path ≅ A.
Proof.
refine_eqv Path_proj1 refl_path refl_path; intro.
- destruct x.
  destruct p.
  reflexivity.
- reflexivity.
Defined.

End Paths.

Section FunExt.

Variable A B : Type.
Variable f g : A -> B.
Variable h   : f ~~ g.

Definition diagonal : A -> Path B :=
  fun x : A => PathC _ (f x) (f x) eq_refl.

Definition quasi_diagonal : A -> Path B:=
  fun x : A => PathC _ (f x) (g x) (h x).

Lemma quasi_eq : diagonal = quasi_diagonal.
Proof.
apply (eqv_mono (Path_proj1_eqv B)).
reflexivity.
Qed.

Theorem fun_ext : f = g.
Proof.
replace f with (Path_proj2 B · diagonal) by reflexivity.
replace g with (Path_proj2 B · quasi_diagonal) by reflexivity.
rewrite quasi_eq.
reflexivity.
Qed.

End FunExt.
