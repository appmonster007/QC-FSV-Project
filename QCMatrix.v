From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Definition gint : Type := Z * Z.

Example gint_ex : gint := (3%Z, 4%Z).

Definition mkG (re im : Z) : gint := (re, im).

Example mkG_ex : mkG 3 4 = (3%Z, 4%Z).
Proof. reflexivity. Qed.

(* << re , im >> for re + im*i *)
Notation "<< re , im >>" := (mkG re im) (at level 0).

Example gint_notation_ex : << 3 , 4 >> = mkG 3 4.
Proof. reflexivity. Qed.

Definition gadd (x y : gint) : gint :=
match x, y with
| (xr, xi), (yr, yi) => (Z.add xr yr, Z.add xi yi)
end.

Example gadd_ex : gadd << 1 , 2 >> << 3 , 4 >> = << 4 , 6 >>.
Proof. reflexivity. Qed.

Definition gopp (x : gint) : gint :=
match x with
| (xr, xi) => (Z.opp xr, Z.opp xi)
end.

Example gopp_ex : gopp << 1 , 2 >> = << -1 , -2 >>.
Proof. reflexivity. Qed.

Definition gconj (x : gint) : gint :=
match x with
| (xr, xi) => (xr, Z.opp xi)
end.

Example gconj_ex : gconj << 1 , 2 >> = << 1 , -2 >>.
Proof. reflexivity. Qed.

Definition gmul (x y : gint) : gint :=
match x, y with
| (xr, xi), (yr, yi) =>
    (Z.sub (Z.mul xr yr) (Z.mul xi yi), Z.add (Z.mul xr yi) (Z.mul xi yr))
end.

Example gmul_ex : gmul << 1 , 2 >> << 3 , 4 >> = << -5 , 10 >>.
Proof. reflexivity. Qed.

Definition g0  : gint := << 0 , 0 >>.
Definition g1  : gint := << 1 , 0 >>.
Definition gn1 : gint := << -1 , 0 >>.
Definition gi  : gint := << 0 , 1 >>.

Example g0_ex  : g0  = mkG 0 0.    Proof. reflexivity. Qed.
Example g1_ex  : g1  = mkG 1 0.    Proof. reflexivity. Qed.
Example gn1_ex : gn1 = mkG (-1) 0. Proof. reflexivity. Qed.
Example gi_ex  : gi  = mkG 0 1.    Proof. reflexivity. Qed.

Definition qmat : Type := nat * list (list gint).

Example qmat_ex : qmat := (0, [ [g0; g0]; [g0; g0] ]).

Definition mkRows (k : nat) (rows : list (list gint)) : qmat := (k, rows).

Example mkRows_ex : mkRows 1 [ [g1; g0]; [g0; gn1] ] = (1, [ [g1; g0]; [g0; gn1] ]).
Proof. reflexivity. Qed.

(* a row, comma-separated so it reads like a row of a matrix; same
   recursive trick ListNotations uses for '[ x ; y ; .. ; z ]'. *)
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)) (at level 0).

Example row_notation_ex : [g1, g0, gn1] = [g1; g0; gn1].
Proof. reflexivity. Qed.

(* [ row ; .. ; row ] / rt2 ^ ( k ) for (1/sqrt 2)^k times that list of
   rows, any n x m shape. *)
Notation "rows / 'rt2' ^ ( k )" := (mkRows k rows) (at level 0).

Example qmat_notation_ex :
    [ [g1, g0]; [g0, gn1] ] / rt2^(1) = mkRows 1 [ [g1; g0]; [g0; gn1] ].
Proof. reflexivity. Qed.

Definition dot (r1 r2 : list gint) : gint :=
    fold_left gadd (map (fun p => gmul (fst p) (snd p)) (combine r1 r2)) g0.

Example dot_ex : dot [g1; g0] [g0; g1] = g0.
Proof. reflexivity. Qed.

Definition transpose (rows : list (list gint)) : list (list gint) :=
match rows with
| [] => []
| r :: _ => map (fun i => map (fun row => nth i row g0) rows) (seq 0 (length r))
end.

Example transpose_ex : transpose [ [g1; g0]; [gn1; g1] ] = [ [g1; gn1]; [g0; g1] ].
Proof. reflexivity. Qed.

Definition conjugate (rows : list (list gint)) : list (list gint) :=
    map (map gconj) rows.

Example conjugate_ex : conjugate [ [gi; g0]; [g0; gi] ] = [ [<< 0 , -1 >>; g0]; [g0; << 0 , -1 >>] ].
Proof. reflexivity. Qed.

Definition conjugate_transpose (rows : list (list gint)) : list (list gint) :=
    conjugate (transpose rows).

Example conjugate_transpose_ex :
    conjugate_transpose [ [g1; gi]; [g0; g1] ] = [ [g1; g0]; [<< 0 , -1 >>; g1] ].
Proof. reflexivity. Qed.

Definition mmul (a b : qmat) : qmat :=
match a, b with
| (ka, ra), (kb, rb) =>
    let bt := transpose rb in
    (Nat.add ka kb, map (fun row => map (fun col => dot row col) bt) ra)
end.

Example mmul_ex :
    mmul ([ [g1, g0]; [g0, g1] ] / rt2^(0)) ([ [g0, g1]; [g1, g0] ] / rt2^(0))
    = [ [g0, g1]; [g1, g0] ] / rt2^(0).
Proof. reflexivity. Qed.

Definition scale_row (s : gint) (r : list gint) : list gint := map (gmul s) r.

Example scale_row_ex : scale_row gn1 [g1; g0] = [gn1; g0].
Proof. reflexivity. Qed.

(* scalar * matrix, same scalar on every entry; reused below to build
   the Kronecker product one row at a time *)
Definition smul (s : gint) (a : qmat) : qmat :=
match a with
| (k, rows) => (k, map (scale_row s) rows)
end.

Example smul_ex : smul gn1 ([ [g1, g0]; [g0, g1] ] / rt2^(0)) = [ [gn1, g0]; [g0, gn1] ] / rt2^(0).
Proof. reflexivity. Qed.

(* (1/sqrt 2)^2 = 1/2: halve every entry and drop 2 from k while every
   entry is even and k >= 2, e.g. reducing H*H's raw k=2 result to the
   identity at k=0. *)

Definition gdiv2 (x : gint) : gint :=
match x with
| (xr, xi) => (Z.div xr 2, Z.div xi 2)
end.

Example gdiv2_ex : gdiv2 << 4 , 6 >> = << 2 , 3 >>.
Proof. reflexivity. Qed.

Definition geven (x : gint) : bool :=
match x with
| (xr, xi) => andb (Z.eqb (Z.modulo xr 2) 0) (Z.eqb (Z.modulo xi 2) 0)
end.

Example geven_ex : geven << 4 , 6 >> = true.
Proof. reflexivity. Qed.

Definition rows_even (rows : list (list gint)) : bool :=
    forallb (forallb geven) rows.

Example rows_even_ex : rows_even [ [<< 4 , 6 >>; g0]; [g0; << 2 , 0 >>] ] = true.
Proof. reflexivity. Qed.

Definition rows_div2 (rows : list (list gint)) : list (list gint) :=
    map (map gdiv2) rows.

Example rows_div2_ex : rows_div2 [ [<< 4 , 6 >>; g0] ] = [ [<< 2 , 3 >>; g0] ].
Proof. reflexivity. Qed.

Fixpoint normalize (fuel : nat) (a : qmat) : qmat :=
match fuel with
| 0 => a
| S fuel' =>
    match a with
    | (k, rows) =>
        if andb (Nat.leb 2 k) (rows_even rows)
        then normalize fuel' (Nat.sub k 2, rows_div2 rows)
        else a
    end
end.

(* H*H's raw k=2 result normalizes down to the identity. *)
Example normalize_ex :
    normalize 2 ([ [<< 2 , 0 >>, g0]; [g0, << 2 , 0 >>] ] / rt2^(2))
    = [ [g1, g0]; [g0, g1] ] / rt2^(0).
Proof. reflexivity. Qed.

Definition qnorm (a : qmat) : qmat :=
match a with
| (k, _) => normalize k a
end.

Example qnorm_ex :
    qnorm (mmul ([ [g1, g1]; [g1, gn1] ] / rt2^(1)) ([ [g1, g1]; [g1, gn1] ] / rt2^(1)))
    = [ [g1, g0]; [g0, g1] ] / rt2^(0).
Proof. reflexivity. Qed.

Definition unit_row (n i : nat) : list gint :=
    map (fun j => if Nat.eqb j i then g1 else g0) (seq 0 n).

Example unit_row_ex : unit_row 3 1 = [g0; g1; g0].
Proof. reflexivity. Qed.

Definition midentity (n : nat) : qmat := mkRows 0 (map (unit_row n) (seq 0 n)).

Example midentity_ex : midentity 2 = [ [g1, g0]; [g0, g1] ] / rt2^(0).
Proof. reflexivity. Qed.

(* one block-row of a Kronecker product: arow's entries, each scaling
   a copy of brow via scale_row (the same op smul uses), laid side by
   side *)
Fixpoint kron_row (arow brow : list gint) : list gint :=
match arow with
| [] => []
| a :: arow' => scale_row a brow ++ kron_row arow' brow
end.

Example kron_row_ex : kron_row [g1; g0] [g0; g1] = [g0; g1; g0; g0].
Proof. reflexivity. Qed.

Definition kron (a b : qmat) : qmat :=
match a, b with
| (ka, ra), (kb, rb) =>
    (Nat.add ka kb, flat_map (fun arow => map (kron_row arow) rb) ra)
end.

Example kron_ex :
    kron ([ [g1, g0]; [g0, gn1] ] / rt2^(0)) (midentity 1)
    = [ [g1, g0]; [g0, gn1] ] / rt2^(0).
Proof. reflexivity. Qed.

Definition Imat : qmat := [ [g1, g0]; [g0, g1] ] / rt2^(0).
Definition Xmat : qmat := [ [g0, g1]; [g1, g0] ] / rt2^(0).
Definition Ymat : qmat := [ [g0, << 0 , -1 >>]; [gi, g0] ] / rt2^(0).
Definition Zmat : qmat := [ [g1, g0]; [g0, gn1] ] / rt2^(0).
Definition Hmat : qmat := [ [g1, g1]; [g1, gn1] ] / rt2^(1).
Definition Smat : qmat := [ [g1, g0]; [g0, gi] ] / rt2^(0).

Example Imat_normalized : qnorm Imat = Imat. Proof. reflexivity. Qed.
Example Xmat_normalized : qnorm Xmat = Xmat. Proof. reflexivity. Qed.
Example Ymat_normalized : qnorm Ymat = Ymat. Proof. reflexivity. Qed.
Example Zmat_normalized : qnorm Zmat = Zmat. Proof. reflexivity. Qed.
Example Hmat_normalized : qnorm Hmat = Hmat. Proof. reflexivity. Qed.
Example Smat_normalized : qnorm Smat = Smat. Proof. reflexivity. Qed.

Inductive gate1 : Type := Hg | Sg | Xg | Yg | Zg | Ig.

Example gate1_ex : gate1 := Hg.

Definition gmat (g : gate1) : qmat :=
match g with
| Hg => Hmat
| Sg => Smat
| Xg => Xmat
| Yg => Ymat
| Zg => Zmat
| Ig => Imat
end.

Example gmat_ex : gmat Sg = Smat.
Proof. reflexivity. Qed.

(* the gate applied first is the leftmost in the list, and ends up
   closest to the state vector, i.e. run [g1;g2] = g2 * g1 *)
Fixpoint run (gs : list gate1) : qmat :=
match gs with
| [] => Imat
| g :: gs' => mmul (run gs') (gmat g)
end.

Example run_ex : run [Hg] = Hmat.
Proof. reflexivity. Qed.

Definition gequiv (xs ys : list gate1) : Prop := qnorm (run xs) = qnorm (run ys).

(* ===== proof for identities ===== *)

Example HH_eq_I : gequiv [Hg; Hg] [].
Proof. unfold gequiv. reflexivity. Qed.

Example XX_eq_I : gequiv [Xg; Xg] [].
Proof. unfold gequiv. reflexivity. Qed.

Example YY_eq_I : gequiv [Yg; Yg] [].
Proof. unfold gequiv. reflexivity. Qed.

Example ZZ_eq_I : gequiv [Zg; Zg] [].
Proof. unfold gequiv. reflexivity. Qed.

Example SS_eq_Z : gequiv [Sg; Sg] [Zg].
Proof. unfold gequiv. reflexivity. Qed.

Example SSSS_eq_I : gequiv [Sg; Sg; Sg; Sg] [].
Proof. unfold gequiv. reflexivity. Qed.

Example HXH_eq_Z : gequiv [Hg; Xg; Hg] [Zg].
Proof. unfold gequiv. reflexivity. Qed.

Example HZH_eq_X : gequiv [Hg; Zg; Hg] [Xg].
Proof. unfold gequiv. reflexivity. Qed.

(* ===== peephole optimizer: rewrite left to right ===== *)

Fixpoint peephole_step (gs : list gate1) : list gate1 :=
match gs with
| Hg :: Hg :: rest => peephole_step rest
| Xg :: Xg :: rest => peephole_step rest
| Yg :: Yg :: rest => peephole_step rest
| Zg :: Zg :: rest => peephole_step rest
| Sg :: Sg :: Sg :: Sg :: rest => peephole_step rest
| Sg :: Sg :: rest => Zg :: peephole_step rest
| Hg :: Xg :: Hg :: rest => Zg :: peephole_step rest
| Hg :: Zg :: Hg :: rest => Xg :: peephole_step rest
| Ig :: rest => peephole_step rest
| g :: rest => g :: peephole_step rest
| [] => []
end.

Example peephole_step_ex : peephole_step [Hg; Hg; Sg] = [Sg].
Proof. reflexivity. Qed.

Fixpoint peephole (fuel : nat) (gs : list gate1) : list gate1 :=
match fuel with
| 0 => gs
| S fuel' =>
    let gs' := peephole_step gs in
    if Nat.ltb (length gs') (length gs) then peephole fuel' gs' else gs'
end.

Example peephole_ex : peephole 4 [Sg; Sg; Zg; Zg] = [Zg].
Proof. reflexivity. Qed.

Definition optimize (gs : list gate1) : list gate1 := peephole (length gs) gs.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : list gate1 -> list gate1 -> Prop :=
| step_HH   : forall rest, (Hg :: Hg :: rest) --> rest
| step_XX   : forall rest, (Xg :: Xg :: rest) --> rest
| step_YY   : forall rest, (Yg :: Yg :: rest) --> rest
| step_ZZ   : forall rest, (Zg :: Zg :: rest) --> rest
| step_SSSS : forall rest, (Sg :: Sg :: Sg :: Sg :: rest) --> rest
| step_SS   : forall rest, (Sg :: Sg :: rest) --> (Zg :: rest)
| step_HXH  : forall rest, (Hg :: Xg :: Hg :: rest) --> (Zg :: rest)
| step_HZH  : forall rest, (Hg :: Zg :: Hg :: rest) --> (Xg :: rest)
| step_I    : forall rest, (Ig :: rest) --> rest
| step_ctx  : forall g gs gs', gs --> gs' -> (g :: gs) --> (g :: gs')
where "t1 '-->' t2" := (step t1 t2).

Example step_ex : [Sg; Sg; Zg] --> [Zg; Zg].
Proof. apply step_SS. Qed.

Reserved Notation "t1 '-->*' t2" (at level 40).

Inductive multistep : list gate1 -> list gate1 -> Prop :=
| multi_refl : forall gs, gs -->* gs
| multi_step : forall gs gs' gs'', gs --> gs' -> gs' -->* gs'' -> gs -->* gs''
where "t1 '-->*' t2" := (multistep t1 t2).

Lemma multistep_ctx : forall g xs ys, xs -->* ys -> (g :: xs) -->* (g :: ys).
Proof.
  intros g xs ys H.
  induction H as [gs | gs gs' gs'' Hstep Hrest IH].
  - apply multi_refl.
  - eapply multi_step. { apply step_ctx. apply Hstep. } apply IH.
Qed.

Lemma multistep_trans : forall xs ys zs, xs -->* ys -> ys -->* zs -> xs -->* zs.
Proof.
  intros xs ys zs H1 H2.
  induction H1 as [gs | gs gs' gs'' Hstep Hrest IH].
  - apply H2.
  - eapply multi_step. { apply Hstep. } apply IH. apply H2.
Qed.

Ltac solve_leaf IH :=
  simpl in *;
  try apply multi_refl;
  match goal with
  | |- (Hg :: Hg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_HH |apply (IH rest); simpl; lia]
  | |- (Xg :: Xg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_XX |apply (IH rest); simpl; lia]
  | |- (Yg :: Yg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_YY |apply (IH rest); simpl; lia]
  | |- (Zg :: Zg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_ZZ |apply (IH rest); simpl; lia]
  | |- (Sg :: Sg :: Sg :: Sg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_SSSS |apply (IH rest); simpl; lia]
  | |- (Sg :: Sg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_SS |apply (multistep_ctx Zg rest); apply (IH rest); simpl; lia]
  | |- (Hg :: Xg :: Hg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_HXH |apply (multistep_ctx Zg rest); apply (IH rest); simpl; lia]
  | |- (Hg :: Zg :: Hg :: ?rest) -->* _ =>
      eapply multi_step; [apply step_HZH |apply (multistep_ctx Xg rest); apply (IH rest); simpl; lia]
  | |- (Ig :: ?rest) -->* _ =>
      eapply multi_step; [apply step_I |apply (IH rest); simpl; lia]
  | |- (?g :: ?rest) -->* _ =>
      apply (multistep_ctx g rest); apply (IH rest); simpl; lia
  end.

Lemma peephole_step_sound_fuel :
    forall fuel gs, length gs <= fuel -> gs -->* (peephole_step gs).
Proof.
  induction fuel as [| fuel' IH]; intros gs Hle.
  - destruct gs as [| g gs'].
    + apply multi_refl.
    + simpl in Hle. lia.
  - destruct gs as [| g1 gs1]; [apply multi_refl |].
    destruct gs1 as [| g2 gs2].
    + destruct g1; solve_leaf IH.
    + destruct gs2 as [| g3 gs3].
      * destruct g1, g2; solve_leaf IH.
      * destruct gs3 as [| g4 gs4].
        -- destruct g1, g2, g3; solve_leaf IH.
        -- destruct g1, g2, g3, g4; solve_leaf IH.
Qed.

Lemma peephole_step_sound : forall gs, gs -->* (peephole_step gs).
Proof. intros gs. apply (peephole_step_sound_fuel (length gs) gs). lia. Qed.

Lemma peephole_sound : forall fuel gs, gs -->* (peephole fuel gs).
Proof.
  induction fuel as [| fuel' IH]; intros gs.
  - simpl. apply multi_refl.
  - simpl.
    destruct (Nat.ltb (length (peephole_step gs)) (length gs)).
    + eapply multistep_trans. { apply peephole_step_sound. } apply IH.
    + apply peephole_step_sound.
Qed.

(* the equivalence theorem: whatever optimize computes, multistep can
   also derive from the same starting list *)
Theorem optimize_sound : forall gs, gs -->* (optimize gs).
Proof. intros gs. unfold optimize. apply peephole_sound. Qed.

(* ===== examples ===== *)

Example optimize_ex_1 : optimize [Hg; Hg] = [].
Proof. reflexivity. Qed.

Example optimize_ex_2 : optimize [Sg; Sg; Sg; Sg] = [].
Proof. reflexivity. Qed.

Example optimize_ex_3 : optimize [Hg; Xg; Hg] = [Zg].
Proof. reflexivity. Qed.

Example optimize_ex_4 : optimize [Sg; Sg; Zg; Zg] = [Zg].
Proof. reflexivity. Qed.

Example optimize_ex_5 : optimize [Xg; Hg; Hg; Yg] = [Xg; Yg].
Proof. reflexivity. Qed.

Example optimize_ex_6 : optimize [Hg; Xg; Hg; Zg; Zg] = [Zg].
Proof. reflexivity. Qed.

Example optimize_ex_7 : optimize [Ig; Hg; Ig; Sg] = [Hg; Sg].
Proof. reflexivity. Qed.

(* S S Z = Z Z = I: the Z from "S S" only cancels with the existing Z
   on the second peephole_step pass, after "S S" becomes "Z" *)
Example optimize_ex_8 : optimize [Sg; Sg; Zg] = [].
Proof. reflexivity. Qed.

(* the same eight examples, proved directly from the inductive
   definition as an explicit chain of step's ending in multi_refl *)

Example multistep_ex_1 : [Hg; Hg] -->* [].
Proof.
  eapply multi_step. { apply step_HH. }
  apply multi_refl.
Qed.

Example multistep_ex_2 : [Sg; Sg; Sg; Sg] -->* [].
Proof.
  eapply multi_step. { apply step_SSSS. }
  apply multi_refl.
Qed.

Example multistep_ex_3 : [Hg; Xg; Hg] -->* [Zg].
Proof.
  eapply multi_step. { apply step_HXH. }
  apply multi_refl.
Qed.

Example multistep_ex_4 : [Sg; Sg; Zg; Zg] -->* [Zg].
Proof.
  eapply multi_step. { apply step_SS. }   (* [S;S;Z;Z] -> [Z;Z;Z] *)
  eapply multi_step. { apply step_ZZ. }   (* [Z;Z;Z]   -> [Z]     *)
  apply multi_refl.
Qed.

Example multistep_ex_5 : [Xg; Hg; Hg; Yg] -->* [Xg; Yg].
Proof.
  eapply multi_step. { apply step_ctx. apply step_HH. } (* [X;H;H;Y] -> [X;Y] *)
  apply multi_refl.
Qed.

Example multistep_ex_6 : [Hg; Xg; Hg; Zg; Zg] -->* [Zg].
Proof.
  eapply multi_step. { apply step_HXH. }  (* [H;X;H;Z;Z] -> [Z;Z;Z] *)
  eapply multi_step. { apply step_ZZ. }   (* [Z;Z;Z]     -> [Z]     *)
  apply multi_refl.
Qed.

Example multistep_ex_7 : [Ig; Hg; Ig; Sg] -->* [Hg; Sg].
Proof.
  eapply multi_step. { apply step_I. }                    (* [I;H;I;S] -> [H;I;S] *)
  eapply multi_step. { apply step_ctx. apply step_I. }    (* [H;I;S]   -> [H;S]   *)
  apply multi_refl.
Qed.

Example multistep_ex_8 : [Sg; Sg; Zg] -->* [].
Proof.
  eapply multi_step. { apply step_SS. }   (* [S;S;Z] -> [Z;Z] *)
  eapply multi_step. { apply step_ZZ. }   (* [Z;Z]   -> []    *)
  apply multi_refl.
Qed.

(* ===== CNOT, as a real 4x4 matrix on two qubits ===== *)

(* CNOT, control = qubit 0, target = qubit 1: the 4x4 permutation
   matrix on |00>,|01>,|10>,|11> that swaps |10> and |11> (flips the
   target exactly when the control is 1) and fixes the rest. *)
Definition CNOT_mat : qmat :=
    [ [g1, g0, g0, g0]; [g0, g1, g0, g0];
      [g0, g0, g0, g1]; [g0, g0, g1, g0] ] / rt2^(0).

Example CNOT_mat_ex :
    CNOT_mat = mkRows 0 [ [g1; g0; g0; g0]; [g0; g1; g0; g0];
                          [g0; g0; g0; g1]; [g0; g0; g1; g0] ].
Proof. reflexivity. Qed.

Example CNOT_mat_involutive : mmul CNOT_mat CNOT_mat = midentity 4.
Proof. reflexivity. Qed.

Example CNOT_propagates_X_control_to_target :
    mmul (mmul CNOT_mat (kron Xmat (midentity 2))) CNOT_mat
    = kron Xmat Xmat.
Proof. reflexivity. Qed.

Example CNOT_propagates_Z_target_to_control :
    mmul (mmul CNOT_mat (kron (midentity 2) Zmat)) CNOT_mat
    = kron Zmat Zmat.
Proof. reflexivity. Qed.

(* and what does NOT propagate: X on the target, Z on the control *)
Example CNOT_X_target_unchanged :
    mmul (mmul CNOT_mat (kron (midentity 2) Xmat)) CNOT_mat
    = kron (midentity 2) Xmat.
Proof. reflexivity. Qed.

Example CNOT_Z_control_unchanged :
    mmul (mmul CNOT_mat (kron Zmat (midentity 2))) CNOT_mat
    = kron Zmat (midentity 2).
Proof. reflexivity. Qed.
