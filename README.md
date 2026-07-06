# Translation for benchmarking

This project translates a subset of Rocq programs into McTT programs with the help of MetaRocq’s quotation feature.
 
There are two goals in mind with this translation. First, it is a step towards checking Rocq developments with McTT. Second, translating terms gives an opportunity to consider how performant the McTT typechecker is.

## Requirements
- [Rocq 9.1.0](https://rocq-prover.org/)
- [MetaRocq 1.4.1+9.1](https://metarocq.github.io/)

```bash
# setup OPAM switch
opam update
opam switch create coq-9.1.0 5.3.0
opam switch coq-9.1.0
eval $(opam env)

# install Rocq
opam pin -y add coq 9.1.0
opam repo add coq-released https://coq.inria.fr/opam/released

# install dependencies
opam install rocq-metarocq-utils.1.4.1+9.1
opam install rocq-metarocq-quotation.1.4.1+9.1

```

## Building from source

```bash
./configure
make
```

## Example translation

Under `examples.v`, there are many examples to step through, such as this:

```
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
```

The translator gives this McTT program. Paste this into `natrec.mctt` and run `dune exec mctt natrec.mctt` to see the typechecking result.

```
fun (x0 : Nat) -> fun (x1 : Nat) -> rec x0 return x2 . Nat | zero => x1 | succ x3, x4 => succ x4 end : forall (x0 : Nat) -> forall (x1 : Nat) -> Nat

```

## Adding timers to McTT

In the extracted OCaml program add these methods to `driver/extracted/Entrypoint.ml`:

```ocaml
let time_type f x y =
    let t = Sys.time() in
    let fx = f x y in
    Printf.printf "Typechecking time: %fs\n" (Sys.time() -. t);
    fx

let time_nbe f x y z=
    let t = Sys.time() in
    let fx = f x y z in
    Printf.printf "NbE time: %fs\n" (Sys.time() -. t);
    fx
```

Then modify `main` to use `time_type` before `type_check_closed` and `time_nbe` before `nbe_impl`:

```ocaml
let main log_fuel buf =
  match prog log_fuel buf with
  | MenhirLibParser.Inter.Fail_pr_full (s, t) -> ParserFailure (s, t)
  | MenhirLibParser.Inter.Timeout_pr -> ParserTimeout log_fuel
  | MenhirLibParser.Inter.Parsed_pr (p, _) ->
    let (o, o0) = p in
    (match elaborate o0 [] with
     | Some e ->
       (match elaborate o [] with
        | Some e0 ->
          if time_type type_check_closed e e0 
          then AllGood (o0, o, e, e0, (time_nbe nbe_impl [] e0 e))
          else TypeCheckingFailure (e, e0)
        | None -> ElaborationFailure o)
     | None -> ElaborationFailure o0)
```
