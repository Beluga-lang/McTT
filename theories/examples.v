From Stdlib Require Import List.
From Stdlib Require Init.
Require Import MetaRocq.Template.All.
From MetaRocq.Utils Require Import utils.
Import MRMonadNotation.
Require Import MetaRocq.Common.BasicAst.
From Translation Require Import trans printing.

MetaRocq Run (
    qt <- tmQuote (fun x : nat => x);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (fun x y : nat => x);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote ((fun x y : nat => x) 3);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (forall x : nat, nat);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote ((fun x : nat -> nat => x 3) (fun y : nat => y));;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (fun x y z : nat -> nat => x);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote ((fun x y z : nat => x) 1 2 3);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote ({x : nat & nat});;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (forall p : nat, nat);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (forall p : {x : nat & nat}, nat);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote ((3, 5));;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Run (
    qt <- tmQuote (snd (3, 5));;
    tmEval all (translate_term qt) >>= tmPrint
  ).

MetaRocq Test Quote (forall p : {x : nat & nat},nat).

MetaRocq Run (
    qt <- tmQuote (S 3);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

(* Natural number recursor *)

MetaRocq Run (
    qt <- tmQuote (fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a);;
    tmPrint qt
  ).

MetaRocq Run (
    qt <- tmQuote (fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a);;
    tmEval all (translate_term qt) >>= tmPrint
  ).

(* natrec.mctt *)

MetaRocq Run (
    qt <- tmQuote (fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a);;
    qty <- tmQuote (nat -> nat -> nat);;
    let result := translate_term qt in
    let result_ty := translate_term qty in
    match result, result_ty with
    | Some e, Some ty =>
        s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
        tmPrint s
    | _, _ => tmFail "translation failed"
    end
  ).

(* eq.mctt *)

 MetaRocq Run (
    qt <- tmQuote (1 = 2);;
    qty <- tmQuote (Type);;
    let result := translate_term qt in
    let result_ty := translate_term qty in
    match result, result_ty with
    | Some e, Some ty =>
        s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
        tmPrint s
    | _, _ => tmFail "translation failed"
    end
  ).

 (* refl.mctt *)

MetaRocq Run (
    qt <- tmQuote (@eq_refl nat 1);;
    qty <- tmQuote (1 = 1);;
    let result := translate_term qt in
    let result_ty := translate_term qty in
    match result, result_ty with
    | Some e, Some ty =>
        s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
        tmPrint s
    | _, _ => tmFail "translation failed"
    end
  ).

(* refl_addition.mctt *)

MetaRocq Run (
    qt <- tmQuote (@eq_refl nat 2);;
    qty <- tmQuote (
      (fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a) 1 1 = 2 (* comutation not inductive proof *)
    );;
    let result := translate_term qt in
    let result_ty := translate_term qty in
    match result, result_ty with
    | Some e, Some ty =>
        s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
        tmPrint s
    | _, _ => tmFail "translation failed"
    end
  ).

(* minimal example eqrec-minimal.mctt *)

MetaRocq Run (
  qt <- tmQuote (fun (A : Type) (x y : A) (p : x = y) =>
  eq_rect x (fun z => A) x y p);;
  qty <- tmQuote (
    forall (A : Type) (x y : A) (p : x = y), A
  );;
  let result := translate_term qt in
  let result_ty := translate_term qty in
  match result, result_ty with
  | Some e, Some ty =>
      s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
      tmPrint s
  | _, _ => tmFail "translation failed"
  end
).

(* scary example broken *)

MetaRocq Run (
  qt <- tmQuote (
    fun (A : Type) (x y : A) (p : x = y) =>
      eq_rect x (fun z => z = z) eq_refl y p
  );;
  qty <- tmQuote (
    forall (A : Type) (x y : A) (p : x = y), y = y
  );;
  let result := translate_term qt in
  let result_ty := translate_term qty in
  match result, result_ty with
  | Some e, Some ty =>
      s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
      tmPrint s
  | _, _ => tmFail "translation failed"
  end
).

(* simple_nested_add.mctt*)

MetaRocq Run (
    qt <- tmQuote (
      (fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a)
      ((fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a) 1 1)
      ((fun (a b : nat) => nat_rect (fun _ => nat) b (fun _ r => S r) a) 1 1)
    );;
    let result := translate_term qt in
    match result with
    | Some e =>
        s <- tmEval all (print_exp [] e ^ " : Nat");;
        tmPrint s
    | None => tmFail "translation failed"
    end
  ).

(* gen_nested_add.mctt *)

MetaRocq Run (
    
  add <- tmQuote (fun a b =>
    nat_rect (fun _ => nat) b (fun _ r => S r) a) ;;

  let fix build n :=
    match n with
    | 0 => tmQuote (S O)
    | S n' =>
        t <- build n' ;;
        ret (Ast.tApp add [t; t])
    end
  in

  t <- build 10 ;;

  let result := translate_term t in

  qty <- tmQuote nat ;;
  let result_ty := translate_term qty in

  match result, result_ty with
  | Some e, Some ty =>
      s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
      tmPrint s
  | _, _ => tmFail "translation failed"
  end
).

(* gen_nested_mult.mctt *)

MetaRocq Run (
  mul <- tmQuote (
    fun a b =>
      nat_rect (fun _ => nat) 0
        (fun _ r =>
           nat_rect (fun _ => nat) r (fun _ r' => S r') b)
        a
  ) ;;

  let fix build n :=
    match n with
    | 0 => tmQuote (S (S O))   (* 2 *)
    | S n' =>
        t <- build n' ;;
        ret (Ast.tApp mul [t; t])
    end
  in

  t <- build 3 ;;

  let result := translate_term t in
  qty <- tmQuote nat ;;
  let result_ty := translate_term qty in

  match result, result_ty with
  | Some e, Some ty =>
      s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
      tmPrint s
  | _, _ => tmFail "translation failed"
  end
  ).

(* Inductive scratch space *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

MetaRocq Run (printConstant "plus" true).

MetaRocq Run (
    kn <- tmLocate1 "day";;
    match kn with
    | IndRef ind => tmQuoteInductive (inductive_mind ind) >>= tmPrint
    | _ => tmFail "not an inductive"
    end
  ).

MetaRocq Run (
    kn <- tmLocate1 "plus";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body => tmPrint body
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

MetaRocq Run (
    kn <- tmLocate1 "plus";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            tmEval all (translate_term body) >>= tmPrint
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

(* quoted_plus.mctt *)

MetaRocq Run (
    kn <- tmLocate1 "plus";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            let result := translate_term body in
            match result with
            | Some e =>
                s <- tmEval all (print_exp [] e ^ " : forall (x0 : Nat) -> forall (x1 : Nat) -> Nat");;
                tmPrint s
            | None => tmFail "translation failed"
            end
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

Theorem plus_assoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

MetaRocq Run (
    kn <- tmLocate1 "plus_assoc";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body => tmPrint body
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

MetaRocq Run (
    kn <- tmLocate1 "plus_assoc";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            unfolded <- tmEval all body;;
            tmPrint unfolded
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

MetaRocq Run (printConstant "eq_ind_r" true).

MetaRocq Run (
    kn <- tmLocate1 "plus_assoc";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            let result := translate_term body in
            match result with
            | Some e =>
                s <- tmEval all (print_exp [] e);;
                tmPrint s
            | None => tmFail "translation failed"
            end
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

MetaRocq Run (
    qty <- tmQuote (forall n m p : nat, plus n (plus m p) = plus (plus n m) p);;
    let result_ty := translate_term qty in
    match result_ty with
    | Some ty =>
        s <- tmEval all (print_exp [] ty);;
        tmPrint s
    | None => tmFail "translation failed"
    end
  ).

MetaRocq Run (
    kn <- tmLocate1 "plus_assoc";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            qty <- tmQuote (forall n m p : nat, plus n (plus m p) = plus (plus n m) p);;
            let result := translate_term body in
            let result_ty := translate_term qty in
            match result, result_ty with
            | Some e, Some ty =>
                s <- tmEval all (print_exp [] e ^ " : " ^ print_exp [] ty);;
                tmPrint s
            | _, _ => tmFail "translation failed"
            end
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).

MetaRocq Run (
    kn <- tmLocate1 "plus_assoc";;
    match kn with
    | ConstRef kn =>
        cb <- tmQuoteConstant kn true;;
        match cb.(cst_body) with
        | Some body =>
            tmEval all (translate_term body) >>= tmPrint
        | None => tmFail "no body"
        end
    | _ => tmFail "not a constant"
    end
  ).
