From Stdlib Require Import List.
From Stdlib Require Init.
Require Import MetaRocq.Template.All.
From MetaRocq.Utils Require Import utils.
Import MRMonadNotation.
Require Import MetaRocq.Common.BasicAst.

Definition printConstant (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => (tmQuoteConstant kn b) >>= tmPrint
  | _ => tmFail ("[" ^ q ^ "] is not a constant")
  end.

Definition name_of_binder (na : binder_annot name) : string :=
  match binder_name na with
  | nAnon => "_"
  | nNamed id => id
  end.

Fixpoint monadic_map {A B} (f : A -> option B) (xs : list A)
  : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs' =>
      match f x, monadic_map f xs' with
      | Some y, Some ys => Some (y :: ys)
      | _, _ => None
      end
  end.

Inductive tterm : Type :=
| tRel (n : nat)
| tSort (n : nat)
| tNat
| tZero
| tSucc (t : tterm)
| tProd (n : string) (t1 : tterm) (t2 : tterm)
| tLambda (n : string) (t1 : tterm) (t2 : tterm)
| tApp (t : tterm) (l : list tterm)
| tSigma (A : tterm) (B : tterm)
| tPair  (a : tterm) (A : tterm) (b : tterm) (B : tterm)
| tFst   (t : tterm)
| tSnd   (t : tterm)
| tNatRec (motive : tterm) (base : tterm) (step : tterm) (n : tterm)
| tEq (A : tterm) (x : tterm) (y : tterm)
| tRefl (A : tterm) (x : tterm)
| tEqRec (A : tterm) (motive : tterm) (proof : tterm) (x : tterm) (y : tterm) (p : tterm).

Inductive exp : Type :=
| a_var (n : nat)
| a_typ (n : nat)
| a_nat
| a_zero
| a_succ (t : exp)
| a_pi (e1 : exp) (e2 : exp)
| a_fn (e1 : exp) (e2 : exp)
| a_app (e1 : exp) (e2 : exp)
| a_sigma (e1 : exp) (e2 : exp)
| a_pair (e1 : exp) (t1 : exp) (e2 : exp) (t2 : exp)
| a_fst (e : exp)
| a_snd (e : exp)
| a_natrec (e1 : exp) (t1 : exp) (e2 : exp) (e3 : exp)
| a_eq (t1 : exp) (e1 : exp) (e2 : exp)
| a_refl (t1 : exp) (e1 : exp)
| a_eqrec (e1 : exp) (t1 : exp) (e2 : exp) (e3 : exp) (t2 : exp) (e4 : exp).

Fixpoint trans (t : tterm) : exp :=
  match t with
  | tRel n => a_var n
  | tSort n => a_typ n
  | tNat => a_nat
  | tZero => a_zero
  | tSucc t => a_succ (trans t)
  | tProd _ t1 t2 => a_pi (trans t1) (trans t2)
  | tLambda _ t1 t2 => a_fn (trans t1) (trans t2)
  | tApp t l => List.fold_left (fun a x => a_app a (trans x)) l (trans t)                
  | tSigma A B => a_sigma (trans A) (trans B)
  | tPair a A b B =>
      a_pair (trans a) (trans A) (trans b) (trans B)
  | tFst t => a_fst (trans t)
  | tSnd t => a_snd (trans t)
  | tNatRec motive base step n =>
      a_natrec (trans n) (trans motive) (trans base) (trans step)
  | tEq A x y => a_eq (trans A) (trans x) (trans y)
  | tRefl A x => a_refl (trans A) (trans x)
  | tEqRec A motive proof x y p =>
      a_eqrec (trans A)
        (trans motive)
        (trans proof)
        (trans x)
        (trans y)
        (trans p)
  end.

Fixpoint lift_tterm (n k : nat) (t : tterm) : tterm :=
  match t with
  | tRel i => if Nat.leb k i then tRel (n + i) else tRel i
  | tNat => tNat
  | tZero => tZero
  | tSucc t => tSucc (lift_tterm n k t)
  | tSort i => tSort i
  | tProd s t1 t2 => tProd s (lift_tterm n k t1) (lift_tterm n (S k) t2)
  | tLambda s t1 t2 => tLambda s (lift_tterm n k t1) (lift_tterm n (S k) t2)
  | tApp t l => tApp (lift_tterm n k t) (List.map (lift_tterm n k) l)
  | tNatRec m b s x => tNatRec (lift_tterm n k m) (lift_tterm n k b) (lift_tterm n k s) (lift_tterm n k x)
  | tSigma t1 t2 => tSigma (lift_tterm n k t1) (lift_tterm n (S k) t2)
  | tPair a A b B => tPair (lift_tterm n k a) (lift_tterm n k A) (lift_tterm n k b) (lift_tterm n k B)
  | tFst t => tFst (lift_tterm n k t)
  | tSnd t => tSnd (lift_tterm n k t)
  | tEq A x y => tEq (lift_tterm n k A) (lift_tterm n k x) (lift_tterm n k y)
  | tRefl A x => tRefl (lift_tterm n k A) (lift_tterm n k x)
  | tEqRec A m prf x y p => tEqRec (lift_tterm n k A) (lift_tterm n k m) (lift_tterm n k prf) (lift_tterm n k x) (lift_tterm n k y) (lift_tterm n k p)
  end.

Fixpoint subst_tterm (s : tterm) (k : nat) (t : tterm) : tterm :=
  match t with
  | tRel i =>
      if Nat.eqb i k then s
      else if Nat.leb k i then tRel (i - 1)
           else tRel i
  | tNat => tNat
  | tZero => tZero
  | tSucc t => tSucc (subst_tterm s k t)
  | tSort i => tSort i
  | tProd nm t1 t2 => tProd nm (subst_tterm s k t1) (subst_tterm s (S k) t2)
  | tLambda nm t1 t2 => tLambda nm (subst_tterm s k t1) (subst_tterm s (S k) t2)
  | tNatRec m b st n => tNatRec (subst_tterm s k m) (subst_tterm s k b) (subst_tterm s k st) (subst_tterm s k n)
  | tEq A x y => tEq (subst_tterm s k A) (subst_tterm s k x) (subst_tterm s k y)
  | tRefl A x => tRefl (subst_tterm s k A) (subst_tterm s k x)
  | tEqRec A m prf x y p => tEqRec (subst_tterm s k A) (subst_tterm s k m) (subst_tterm s k prf) (subst_tterm s k x) (subst_tterm s k y) (subst_tterm s k p)
  | tSigma t1 t2 => tSigma (subst_tterm s k t1) (subst_tterm s (S k) t2)
  | tPair a A b B => tPair (subst_tterm s k a) (subst_tterm s k A) (subst_tterm s k b) (subst_tterm s k B)
  | tFst t => tFst (subst_tterm s k t)
  | tSnd t => tSnd (subst_tterm s k t)
  | tApp t l =>
    match t with
    | tRel i => if Nat.eqb i k then s
                else tApp (subst_tterm s k t) (List.map (subst_tterm s k) l)
    | _ => tApp (subst_tterm s k t) (List.map (subst_tterm s k) l)
    end
  end.

Fixpoint tterm_of_term (t : Ast.term) : option tterm :=
  match t with
  | Ast.tRel n => Some (tRel (n))

  | Ast.tCast t _ _ =>
      tterm_of_term t

  | Ast.tSort s => Some (tSort 0) (* temporary: collapse Set, Prop, and Type to 0 *)
                       
  | Ast.tInd ind u =>
      let '(mkInd kn _) := ind in
      if String.eqb (snd kn) "nat"
      then Some tNat
      else None

  (* u is the universe we ignore for now *)
  (* idx refers to which branch of the type constructor we are looking it (Z or S) *)
  | Ast.tConstruct ind idx u =>
      let '(mkInd kn _) := ind in
      if String.eqb (snd kn) "nat" then
        match idx with
        | 0 => Some tZero
        | 1 => None
        | _ => None
        end
      else None

  | Ast.tProd name t1 t2 =>
      match tterm_of_term t1, tterm_of_term t2 with
      | Some t1', Some t2' => Some (tProd (name_of_binder name) t1' t2')
      | _, _ => None
      end

  | Ast.tLambda name t1 t2 =>
      match tterm_of_term t1, tterm_of_term t2 with
      | Some t1', Some t2' => Some (tLambda (name_of_binder name) t1' t2')
      | _, _ => None
      end

  | Ast.tProj p t =>
      match tterm_of_term t with
      | Some t' =>
          if Nat.eqb (proj_arg p) 1 then Some (tFst t')
          else if Nat.eqb (proj_arg p) 2 then Some (tSnd t')
               else None
      | None => None
      end
        
  | Ast.tApp (Ast.tInd ind _) [A; x; y] =>
      if String.eqb (snd (inductive_mind ind)) "eq" then
        match tterm_of_term A, tterm_of_term x, tterm_of_term y with
        | Some A', Some x', Some y' => Some (tEq A' x' y')
        | _,_,_ => None
        end
      else None

  | Ast.tApp (Ast.tInd ind u) [A; B] =>
      let '(mkInd kn _) := ind in
      if String.eqb (snd kn) "sigT" then
        match tterm_of_term A, tterm_of_term B with
        | Some A', Some B' => Some (tSigma A' B')
        | _,_ => None
        end
      else if String.eqb (snd kn) "prod" then
             match tterm_of_term A, tterm_of_term B with
             | Some A', Some B' => Some (tSigma A' B')
             | _, _ => None
             end
           else None
                  
  | Ast.tApp (Ast.tConstruct ind 0 _) [A; x] =>
      if String.eqb (snd (inductive_mind ind)) "eq" then
        match tterm_of_term A, tterm_of_term x with
        | Some A', Some x' => Some (tRefl A' x')
        | _,_ => None
        end
      else None

  | Ast.tApp (Ast.tConstruct ind 0 _) [A; B; a; b] =>
      let '(mkInd kn _) := ind in
      if String.eqb (snd kn) "prod" then
        match tterm_of_term A,
          tterm_of_term B,
          tterm_of_term a,
          tterm_of_term b
        with
        | Some A', Some B', Some a', Some b' =>
            Some (tPair a' A' b' B')
        | _,_,_,_ => None
        end
      else None

| Ast.tApp (Ast.tConstruct ind 1 _) [n] =>
    let '(mkInd kn _) := ind in
    if String.eqb (snd kn) "nat" then
      match tterm_of_term n with
      | Some n' => Some (tSucc n')
      | None => None
      end
    else None

| Ast.tApp (Ast.tConst kn _) [motive; base; step; n] =>
    match snd kn with
    | "nat_rect" | "nat_ind" =>
        match tterm_of_term motive with
        | Some (tLambda _ _ motive_body) =>
            match tterm_of_term base,
                  tterm_of_term step,
                  tterm_of_term n with
            | Some base', Some (tLambda _ _ (tLambda _ _ step_body)), Some n' =>
                Some (tNatRec motive_body base' step_body n')
            | _,_,_ => None
            end
        | _ => None
        end
    | _ => None
    end

  | Ast.tApp (Ast.tConst kn _) [A; x; motive; proof; y; p] =>
      match snd kn with
      | "eq_rect" =>
          match motive with
          | Ast.tLambda _ _ motive_body =>
              match tterm_of_term motive_body with
              | Some m' =>
                  let shifted_m := lift_tterm 2 1 m' in
                  match tterm_of_term A,
                    tterm_of_term x,
                    tterm_of_term proof,
                    tterm_of_term y,
                    tterm_of_term p with
                  | Some A', Some x', Some prf', Some y', Some p' =>
                      Some (tEqRec A' x' shifted_m prf' y' p')
                  | _,_,_,_,_ => None
                  end
              | None => None
              end
          | _ => None
          end
      | "eq_ind_r" =>
          match motive with
          | Ast.tLambda _ _ motive_body =>
              match tterm_of_term motive_body with
              | Some m' =>
                  let shifted_m := lift_tterm 1 1 m' in
                  match tterm_of_term A,
                    tterm_of_term x,
                    tterm_of_term proof,
                    tterm_of_term y,
                    tterm_of_term p with
                  | Some A', Some x', Some prf', Some y', Some p' =>
                      Some (tEqRec A' y' shifted_m prf' x' p')
                  | _,_,_,_,_ => None
                  end
              | None => None
              end
          | _ => None
          end
      | _ => None
      end  
        
  | Ast.tApp (Ast.tConst kn _) [A; B; p] =>
      match snd kn with
      | "fst" => 
          match tterm_of_term p with
          | Some p' => Some (tFst p')
          | None    => None
          end
      | "snd" =>
          match tterm_of_term p with
          | Some p' => Some (tSnd p')
          | None    => None
          end
      | _ => None
      end

  (* Hard coded plus *)
  | Ast.tApp (Ast.tConst kn _) [a; b] =>
      match snd kn with
      | "plus" =>
          match tterm_of_term a, tterm_of_term b with
          | Some a', Some b' =>
              Some (tApp (tLambda "n" tNat (tLambda "m" tNat
                                              (tNatRec tNat (tRel 0) (tSucc (tRel 0)) (tRel 1)))) [a'; b'])
          | _,_ => None
          end
      | _ => None
      end
        
  | Ast.tApp t l =>
      match tterm_of_term t, monadic_map tterm_of_term l with
      | Some t', Some l' => Some (tApp t' l')
      | _, _ => None
      end

  | Ast.tFix [mfix] 0 =>
      if Nat.eqb mfix.(rarg) 0 then
        match mfix.(dbody) with
        | Ast.tLambda _ _ (Ast.tLambda _ _ (Ast.tCase ci _ discr branches)) =>
            let kn := ci.(ci_ind) in
            if String.eqb (snd (inductive_mind kn)) "nat" then
              match branches with
              | [ {| bcontext := []; bbody := o_branch |} ;
                  {| bcontext := [_]; bbody := s_branch |} ] =>
                  match tterm_of_term discr,
                    tterm_of_term o_branch,
                    tterm_of_term s_branch with
                  | Some discr', Some o', Some s' =>
                      let s_fixed := subst_tterm (tRel 0) 3 s' in
                      Some (tLambda "n" tNat (tLambda "m" tNat (tNatRec tNat o' s_fixed discr')))
                  | _,_,_ => None
                  end
              | _ => None
              end
            else None
        | _ => None
        end
      else None
        
  | _ => None
end.

Definition translate_term (qt : Ast.term) : option exp :=
  match tterm_of_term qt with
  | Some x => Some (trans x)
  | _ => None
  end.
