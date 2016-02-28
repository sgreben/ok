(* a tiny Parsec-style parser combinator library *)
open Lexer
exception Failed
type state = {tokens:token array; pos:int}
(* primitives *)
[@@inline always] let fail () = raise Failed
[@@inline always] let next s = {s with pos = s.pos + 1}
[@@inline always] let current {tokens;pos} = try tokens.(pos) with _ -> fail()
[@@inline always] let return x s = x,s
[@@inline always] let option x s = try let x,s=x s in Some x,s with Failed -> None,s
[@@inline always] let (^|^) x y s = try x s with Failed -> y s
[@@inline always] let (|^>^) x y s = let x,s = x s in let y,s = y s in (x,y),s
[@@inline always] let (|>^) x y s = let _,s = x s in let y,s = y s in y,s
[@@inline always] let (|^>) x y s = let x,s = x s in let _,s = y s in x,s
[@@inline always] let (|>>) x f s = let x,s = x s in f x,s
[@@inline always] let (>>=) x f s = let x,s = x s in f x s
[@@inline always] let pipe2 x y f s = let x,s = x s in let y,s = y s in f x y,s
[@@inline always] let pipe3 x y z f s = let x,s = x s in let y,s = y s in let z,s = z s in f x y z,s
[@@inline always] let pipe4 x y z u f s = let x,s = x s in let y,s = y s in let z,s = z s in let u,s = u s in f x y z u,s
(* composite combinators *)
let choice xs s = let rec loop xs = match xs with [] -> fail() | x::xs -> try x s with Failed -> loop xs in loop xs
let skip x s = try let _,s = x s in (),s with Failed -> (),s
let skip_many x s = let s = ref s in try while true do s:=snd(x !s); done; (),!s with Failed -> (),!s
let token t s = if current s = t then (),next s else fail()
let token_map f s = f (current s),next s
let sep sep x =
  let return acc s = List.rev acc,s in
  let rec loop acc s =
    try let x,s=x s in let acc = x::acc in
        (try let _,s = sep s in loop acc s
         with Failed -> return acc s)
    with Failed -> return acc s
  in loop []
let sep_empty sep x empty =
    let return acc s = List.rev acc,s in
    let rec empties acc s =
      try let _,s = sep s in empties (empty::acc) s
      with Failed -> loop acc s
    and loop acc s =
      try let x,s = x s in let acc = x::acc in
          (try let _,s = sep s in empties acc s
           with Failed -> return acc s)
      with Failed -> (let acc = empty::acc in
                     try let _,s=sep s in empties acc s
                     with Failed -> return acc s)
    in loop []
let sep_token t x =
  let return acc s = List.rev acc,s in
  let rec loop acc s =
    try let x,s=x s in let acc = x::acc in
        (try if current s = t then loop acc (next s) else return acc s
         with Failed -> return acc s)
    with Failed -> return acc s
  in loop []
let sep_token1 t x s = match sep_token t x s with [],_ ->fail() | ok -> ok
let seq x =
  let rec loop acc s = try let x,s=x s in loop (x::acc) s with Failed -> List.rev acc,s
  in loop []
let seq1 x s = match seq x s with [],_ -> fail() | ok -> ok
let seq_fold x ~f ~init =
  let rec loop acc s = try let x,s=x s in loop (f acc x) s with Failed -> acc,s
  in loop init
let seq_fold_token ~f ~init =
  let rec loop acc s = try loop (f acc (current s)) (next s) with Failed -> acc,s
  in loop init