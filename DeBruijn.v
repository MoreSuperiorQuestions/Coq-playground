From Coq Require Import Arith Lia.

(** A small, TAPL-style development of nameless lambda terms.

    A variable [var x n] stores:
    - [x]: its de Bruijn index;
    - [n]: the length of the surrounding context.

    The second number is redundant mathematically, but useful operationally:
    after every correct shift it must change with the context. *)

Inductive tm : Type :=
| var : nat -> nat -> tm
| abs : tm -> tm
| app : tm -> tm -> tm.

(** [shift d c t] adds [d] to every index in [t] that is at least
    the cutoff [c].  Every stored context length grows by [d]. *)
Fixpoint shift (d c : nat) (t : tm) : tm :=
  match t with
  | var x n =>
      var (if c <=? x then x + d else x) (n + d)
  | abs t1 => abs (shift d (S c) t1)
  | app t1 t2 => app (shift d c t1) (shift d c t2)
  end.

(** TAPL's substitution [j |-> s]t.  Going below a binder increments
    [j].  At a matching variable, [s] is shifted by [j] because it is
    being inserted below [j] surrounding binders. *)
Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | var x n => if x =? j then shift j 0 s else var x n
  | abs t1 => abs (subst (S j) s t1)
  | app t1 t2 => app (subst j s t1) (subst j s t2)
  end.

(** Downward shift by one.  [Nat.pred] is safe on terms satisfying the
    expected scoping invariant at the point where this operation is used.
    Keeping it separate makes the potentially partial step visible. *)
Fixpoint shift_down (c : nat) (t : tm) : tm :=
  match t with
  | var x n =>
      var (if c <=? x then Nat.pred x else x) (Nat.pred n)
  | abs t1 => abs (shift_down (S c) t1)
  | app t1 t2 => app (shift_down c t1) (shift_down c t2)
  end.

(** Substitute a term for the outermost variable and remove its binder:
    shift up, substitute, then shift down. *)
Definition subst_top (s t : tm) : tm :=
  shift_down 0 (subst 0 (shift 1 0 s) t).

(** [well_scoped n t] states both parts of TAPL's representation
    invariant: every variable records context length [n], and its index
    is strictly smaller than [n]. *)
Fixpoint well_scoped (n : nat) (t : tm) : Prop :=
  match t with
  | var x stored_n => stored_n = n /\ x < n
  | abs t1 => well_scoped (S n) t1
  | app t1 t2 => well_scoped n t1 /\ well_scoped n t2
  end.

Definition closed (t : tm) : Prop := well_scoped 0 t.

(** Familiar closed terms. *)
Definition id : tm := abs (var 0 1).
Definition const : tm := abs (abs (var 1 2)).

Example id_is_closed : closed id.
Proof. unfold closed, id; simpl; lia. Qed.

Example const_is_closed : closed const.
Proof. unfold closed, const; simpl; lia. Qed.

(** ---------- Foundational properties of shifting ---------- *)

Lemma shift_zero : forall c t, shift 0 c t = t.
Proof.
  induction t as [x n | t IH | t1 IH1 t2 IH2]; intros c; simpl.
  - destruct (c <=? x); reflexivity.
  - now rewrite IH.
  - now rewrite IH1, IH2.
Qed.

Lemma shift_add : forall d e c t,
  shift d c (shift e c t) = shift (e + d) c t.
Proof.
  induction t as [x n | t IH | t1 IH1 t2 IH2];
    intros d e c; simpl.
  - destruct (c <=? x) eqn:Hcx.
    + apply Nat.leb_le in Hcx.
      assert (Hcxe : (c <=? x + e) = true)
        by (apply Nat.leb_le; lia).
      rewrite Hcxe. f_equal; lia.
    + rewrite Hcx. f_equal; lia.
  - now rewrite IH.
  - now rewrite IH1, IH2.
Qed.

Lemma shift_preserves_scoping : forall t n c d,
  well_scoped n t ->
  c <= n ->
  well_scoped (n + d) (shift d c t).
Proof.
  induction t as [x stored_n | t IH | t1 IH1 t2 IH2];
    intros n c d Hscope Hcut; simpl in *.
  - destruct Hscope as [Hstored Hx]. subst stored_n.
    split; [reflexivity |].
    destruct (c <=? x) eqn:Hcx.
    + apply Nat.leb_le in Hcx. lia.
    + apply Nat.leb_gt in Hcx. lia.
  - replace (S n + d) with (S (n + d)) by lia.
    apply IH with (c := S c); lia.
  - destruct Hscope as [H1 H2]. split.
    + now apply IH1 with (n := n) (c := c).
    + now apply IH2 with (n := n) (c := c).
Qed.

Corollary shift_closed_into_context : forall t d,
  closed t -> well_scoped d (shift d 0 t).
Proof.
  intros t d Hclosed.
  replace d with (0 + d) by lia.
  now apply shift_preserves_scoping.
Qed.

(** ---------- Small substitution calculations ---------- *)

Lemma subst_var_hit : forall j s n,
  subst j s (var j n) = shift j 0 s.
Proof.
  intros j s n; simpl. now rewrite Nat.eqb_refl.
Qed.

Lemma subst_var_miss : forall j x n s,
  x <> j -> subst j s (var x n) = var x n.
Proof.
  intros j x n s Hneq; simpl.
  apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

(** beta-reducing [(fun. 0) id] yields [id]. *)
Example subst_top_identity :
  subst_top id (var 0 1) = id.
Proof. reflexivity. Qed.

(** In [fun. 1], index [1] refers outside the inner abstraction.
    Substituting [id] for that outer variable yields [fun. id], with
    the stored context lengths updated consistently. *)
Example subst_under_binder :
  subst_top id (abs (var 1 2)) = abs (abs (var 0 2)).
Proof. reflexivity. Qed.

(** A closed term cannot itself be a variable. *)
Lemma closed_not_var : forall x n, ~ closed (var x n).
Proof.
  intros x n H; unfold closed in H; simpl in H; lia.
Qed.
