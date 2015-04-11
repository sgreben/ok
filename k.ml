open Core.Std
(* page 108
FIXME: the parser cases for verb/adverb/function applications are messy, require cleanup for clarity
TODO: arbitrary function arity & (partial) application f[x;;z]
TODO: parse (and represent) partial verb application (e.g. (3 +) )
TODO: parse
TODO: proper equality tests for floats (tolerance), remove all polymorphic eq tests
TODO: attributes
TODO: built-in operators (_in _draw etc.)
TODO: special REPL commands (\p,..)
TODO: missing operations: grep Not_implemented k.ml
X TODO: ktree
X TODO: functions (e.g. {x@y-1})
X TODO: definitions (e.g. elementat:123)
X TODO: handles (as in .`p.q.r)
X TODO: parse (and represent) variable names (alpha without bquote)
X TODO: finish verbs (verb compositions (e.g. (%-)[a;b]))
X TODO: finish basic adverbs (distinguish dyadic/monadic application of the verb, do adverb compositions)
X TODO: parse lists (e.g. (a;b;c))
OPT: type tracking for list optimizations, e.g. (KList (TInteger,(KInteger x,KInteger y,KInteger z)) ~> KIntegerArray [|x,y,z|]
OPT: constant folding for expressions e.g. (1,2,3,4) : EAppD(EInteger 1,VComma,EAppD(EInteger 2,VComma,....(,EInteger 4))) -> EIntegerArray [|1;2;3;4|]
OPT: type (and shape) inference. likely necessary for simple JIT code as well as for performance
     edit: looks like someone already figured out most of the necessary framework http://dx.doi.org/10.1007/978-3-642-54833-8_3 :)
OPT: optimize for ocamlc inlining (http://www.ocamlpro.com/blog/2013/05/24/optimisations-you-shouldn-t-do.html:
  "functions containing structured constants or local functions are not allowed to be duplicated, preventing them from being inlined.")
OPT: special-case some verb/adverb compositions to avoid a lot of array appends. for example ,//
OPT: optimize constant enumerations, e.g. (100!) @ 10! is just 10!; (some-vector)@5! is just 5#(some-vector)
OPT: add matrix types (KIntegerArray2, KFloatArray2)
OPT: switch to Bigarrays
OPT: use LLVM to compile expressions just-in-time (probably Bigarray or Obj.magic hacks will be necessary to deal with [type k])
OPT: get rid of Core to reduce executable size (currently a whopping 11M, which is ~96% Core code we don't use. compare with 520K for all of q)
     of course, this only makes sense once we know which functions to replace and no longer need Core's boilerplate code generation.
PRETTY: refactor verbs into modules (but maybe this sucks for inlining):
type m = k -> k
type d = k -> k -> k
module type Verb = sig
  val m : m;
  val d : d;
  val av_dm : av -> d;
  val av_dd : av -> d;
  val av_mm : av -> m;
  val av_md : av -> m;
end
*)
exception Not_implemented
module Symbol = struct
  module T = struct type t = S of int with sexp,compare let hash (S k) = k end
  include T
  include Comparable.Make(T) include Hashable.Make(T)
  let (_s: t String.Table.t) = String.Table.create ()
  let (_sr:string Table.t) = Table.create ()
  let (_sc:int ref) = ref 0
  let sexp_of_t (s:t) = Sexp.Atom (Table.find_exn _sr s)
  let to_string (s:t) : string = Table.find_exn _sr s
  let make (s:string) : t = match String.Table.find _s s with
    | Some s -> s
    | None -> let i = !_sc in Hashtbl.add_exn _sr ~key:(S i) ~data:s; Hashtbl.add_exn _s ~key:s ~data:(S i); Int.incr _sc; S i
end

type s = Symbol.t with sexp,compare
type id = IdRelative of s list
       | IdAbsolute of s list with sexp,compare
type v = VPlus
       | VMinus
       | VStar
       | VExclaim
       | VPercent
       | VPipe
       | VAmpersand
       | VCircumflex
       | VLangle
       | VRangle
       | VEquals
       | VPound
       | VLodash
       | VTilde
       | VDollar
       | VQuestion
       | VAt
       | VDot
       | VComma with sexp
type av =AVForwardslash
       | AVForwardslashColon
       | AVBackslash
       | AVBackslashColon
       | AVColon
       | AVQuote
       | AVQuoteColon with sexp
type f = F of e | F1 of e | F2 of e
and  e = EAppD of e*e*e
       | EAppM of e*e
       | ESymbol of s
       | EList of e array
       | EInteger of int
       | EFloat of float
       | EChar of char
       | EIntegerArray of int array
       | EFloatArray of float array
       | ESymbolArray of s array
       | ECharArray of char array
       | EFunction of f
       | EVerb of v
       | EAdverb of av*e
       | EId of id
       | EAssign of id*e
       | EReturn of e
       | ENull
       with sexp
type t = TList
       | TInteger
       | TIntegerArray
       | TFloat
       | TFloatArray
       | TChar
       | TCharArray
       | TSymbol
       | TSymbolArray
       | TDictionary
       | TFunction
       | TNull
and  d = k Symbol.Table.t
and  k = KList of k array
       | KInteger of int
       | KIntegerArray of int array
       | KFloat of float
       | KFloatArray of float array
       | KChar of char
       | KCharArray of char array
       | KSymbol of s
       | KSymbolArray of s array
       | KDictionary of d
       | KFunction of f
       | KNull
     with sexp

let dict () = Symbol.Table.create ()
let tree : d = dict ()
let handle : id Symbol.Table.t = dict ()
let h s h = Symbol.Table.replace handle ~key:s ~data:h
let root = let s = Symbol.make "" in h s (IdRelative []); s
let arg_x, arg_x_sym = let s = Symbol.make "x" in let id = IdRelative [s] in h s id; id, s
let arg_y, arg_y_sym = let s = Symbol.make "y" in let id = IdRelative [s] in h s id; id, s
let _ = assert (Symbol.S 0 = root)
let _ = assert (Symbol.S 1 = arg_x_sym)
let _ = assert (Symbol.S 2 = arg_y_sym)
let pwd : d ref = ref tree
let lookup id = let d,s = match id with
  | IdRelative s -> !pwd,s
  | IdAbsolute s -> tree,s
  in try List.fold_left s ~init:(KDictionary d) ~f:(fun (KDictionary d) s -> Hashtbl.find_exn d s)
     with _ -> KNull
let lookup_symbol s = let id = Symbol.Table.find_exn handle s in id
let never () = assert false
type tc = {tlist:int;tinteger:int;tintegerarray:int;tfloat:int;tfloatarray:int;tchar:int;tchararray:int;tsymbol:int;tsymbolarray:int;tdictionary:int;tfunction:int;tnull:int;}
let ts = Array.fold ~init:{tlist=0;tinteger=0;tintegerarray=0;tfloat=0;tfloatarray=0;tchar=0;tchararray=0;tsymbol=0;tsymbolarray=0;tdictionary=0;tfunction=0;tnull=0;}
  ~f:(fun ts -> function
      | KList _ -> {ts with tlist=1+ts.tlist}
      | KInteger _ -> {ts with tinteger=1+ts.tinteger}
      | KIntegerArray _ -> {ts with tintegerarray=1+ts.tintegerarray}
      | KFloat _ -> {ts with tfloat=1+ts.tfloat}
      | KFloatArray _ -> {ts with tfloatarray=1+ts.tfloatarray}
      | KChar _ -> {ts with tchar=1+ts.tchar}
      | KCharArray _ -> {ts with tchararray=1+ts.tchararray}
      | KSymbol _ -> {ts with tsymbol=1+ts.tsymbol}
      | KSymbolArray _ -> {ts with tsymbolarray=1+ts.tsymbolarray}
      | KDictionary _ -> {ts with tdictionary=1+ts.tdictionary}
      | KFunction _ -> {ts with tfunction=1+ts.tfunction}
      | KNull -> {ts with tnull=1+ts.tnull} )
let is_vector ts =
  let c,t = 0, TNull in
  let c,t = if ts.tlist > 0 then c+1,TList else c,t in
  let c,t = if ts.tinteger > 0 then c+1,TInteger else c,t in
  let c,t = if ts.tintegerarray > 0 then c+1,TIntegerArray else c,t in
  let c,t = if ts.tfloat > 0 then c+1,TFloat else c,t in
  let c,t = if ts.tfloatarray > 0 then c+1,TFloatArray else c,t in
  let c,t = if ts.tchar > 0 then c+1,TChar else c,t in
  let c,t = if ts.tchararray > 0 then c+1,TCharArray else c,t in
  let c,t = if ts.tsymbol > 0 then c+1,TSymbol else c,t in
  let c,t = if ts.tsymbolarray > 0 then c+1,TSymbolArray else c,t in
  let c,t = if ts.tdictionary > 0 then c+1,TDictionary else c,t in
  let c,t = if ts.tfunction > 0 then c+1,TFunction else c,t in
  let c,t = if ts.tnull > 0 then c+1,TNull else c,t in
  if Int.equal c 1 then Some t else None
let n = function
    | KList x -> Array.length x
    | KInteger _ -> 1
    | KIntegerArray x -> Array.length x
    | KFloat _ -> 1
    | KFloatArray x -> Array.length x
    | KChar _ -> 1
    | KCharArray x -> Array.length x
    | KSymbol _ -> 1
    | KSymbolArray x -> Array.length x
    | KDictionary x -> Symbol.Table.length x
    | KFunction _ -> 1
    | KNull -> 1

exception KError_domain of k list with sexp
exception KError_type of k list with sexp
exception KError_length of k list with sexp
exception KError_rank of k list with sexp
exception KError_index of k list with sexp
exception KError_syntax with sexp


let match_compare x y = x=y
let match_compare_int x y = if match_compare x y then 1 else 0
let sub a pos len = Array.sub a ~pos ~len
let mod_pos x y = if x < 0 then y+(x mod y) else x mod y
let zip x y f = if Array.length x = Array.length y then Array.map2_exn x y ~f else raise (KError_length [])
let map x f = Array.map x ~f
let append x y = Array.append x y
let take x y = let n = Array.length y in (Array.init (Int.abs x) ~f:(fun i -> y.(mod_pos i n)))
let drop x y = let n = Array.length y in let p,l = if x >= 0 then x,n-x else 0,n+x in sub y p l
let vec x = match is_vector (ts x) with (* vectorize a homogeneous list *)
  | Some TInteger -> KIntegerArray (map x (function (KInteger x) -> x | _ -> never()))
  | Some TFloat -> KFloatArray (map x (function (KFloat x) -> x | _ -> never()))
  | Some TChar -> KCharArray (map x (function (KChar x) -> x | _ -> never()))
  | Some TSymbol -> KSymbolArray (map x (function (KSymbol x) -> x | _ -> never()))
  | _ -> KList x
let as_list = function
  | KIntegerArray x -> map x (fun x -> KInteger x)
  | KFloatArray x -> map x (fun x -> KFloat x)
  | KCharArray x -> map x (fun x -> KChar x)
  | KSymbolArray x -> map x (fun x -> KSymbol x)
  | KList x -> x
  | x -> [|x|]
let cut x y f = let n = Array.length y in
                let p, a = Array.fold x ~init:(0,[]) ~f:(fun (p,xs) x -> (x,f (sub y p (x-p))::xs)) in
                if p < n then Array.of_list_rev ((f (sub y p (n-p))) :: a) else Array.of_list_rev a
let rec split_map f d m a i = if i+d > m then [] else f (sub a i d) :: split_map f d m a (i+d)
let reshape_k x nx y ny =
    let px = Array.fold x ~init:1 ~f:( * ) in
    let rec loop i m a = if i >= nx then a.(0) else let m' = m/x.(i) in KList (Array.of_list (split_map (loop (i+1) m') m' m a 0)) in
    if px > ny then raise (KError_length []) else loop 0 px y
let reshape_v x y f =
    let nx,ny = Array.length x, Array.length y in let xnx1 = x.(nx-1) in
    let ya = Array.of_list (split_map f xnx1 ny y 0) in
    reshape_k (sub x 0 (nx-1)) (nx-1) ya (ny/xnx1)
let rot (x:int) (y:'a array) : 'a array =
      let len = Array.length y in
      let a = Array.copy y in
      let x = x mod len in
      let x = if x < 0 then len+x else x in
      let k = len - x in
      Array.blit ~src:y ~src_pos:x ~dst:a ~dst_pos:0 ~len:k; (*SLOW*)
      Array.blit ~src:y ~src_pos:0 ~dst:a ~dst_pos:k ~len:x; (*SLOW*)
      a

let rec av_dd av f x y : k = match av,x,y with (* f:dyad, derived verb:dyad *)
  (* each *)
  | AVQuote,             KList x,         KList y          -> KList (zip x y f)
  | AVQuote,             KList x,         KIntegerArray y  -> KList (zip x y (fun x y -> f x (KInteger y)))
  | AVQuote,             KList x,         KFloatArray y    -> KList (zip x y (fun x y -> f x (KFloat y)))
  | AVQuote,             KList x,         KCharArray y     -> KList (zip x y (fun x y -> f x (KChar y)))
  | AVQuote,             KList x,         KSymbolArray y   -> KList (zip x y (fun x y -> f x (KSymbol y)))
  | AVQuote,             KIntegerArray x, KList y          -> KList (zip x y (fun x y -> f (KInteger x) y))
  | AVQuote,             KIntegerArray x, KIntegerArray y  -> KList (zip x y (fun x y -> f (KInteger x) (KInteger y)))
  | AVQuote,             KIntegerArray x, KFloatArray y    -> KList (zip x y (fun x y -> f (KInteger x) (KFloat y)))
  | AVQuote,             KIntegerArray x, KCharArray y     -> KList (zip x y (fun x y -> f (KInteger x) (KChar y)))
  | AVQuote,             KIntegerArray x, KSymbolArray y   -> KList (zip x y (fun x y -> f (KInteger x) (KSymbol y)))
  | AVQuote,             KFloatArray x,   KList y          -> KList (zip x y (fun x y -> f (KFloat x) y))
  | AVQuote,             KFloatArray x,   KIntegerArray y  -> KList (zip x y (fun x y -> f (KFloat x) (KInteger y)))
  | AVQuote,             KFloatArray x,   KFloatArray y    -> KList (zip x y (fun x y -> f (KFloat x) (KFloat y)))
  | AVQuote,             KFloatArray x,   KCharArray y     -> KList (zip x y (fun x y -> f (KFloat x) (KChar y)))
  | AVQuote,             KFloatArray x,   KSymbolArray y   -> KList (zip x y (fun x y -> f (KFloat x) (KSymbol y)))
  | AVQuote,             KCharArray x,    KList y          -> KList (zip x y (fun x y -> f (KChar x) y))
  | AVQuote,             KCharArray x,    KIntegerArray y  -> KList (zip x y (fun x y -> f (KChar x) (KInteger y)))
  | AVQuote,             KCharArray x,    KFloatArray y    -> KList (zip x y (fun x y -> f (KChar x) (KFloat y)))
  | AVQuote,             KCharArray x,    KCharArray y     -> KList (zip x y (fun x y -> f (KChar x) (KChar y)))
  | AVQuote,             KCharArray x,    KSymbolArray y   -> KList (zip x y (fun x y -> f (KChar x) (KSymbol y)))
  | AVQuote,             KSymbolArray x,  KList y          -> KList (zip x y (fun x y -> f (KSymbol x) y))
  | AVQuote,             KSymbolArray x,  KIntegerArray y  -> KList (zip x y (fun x y -> f (KSymbol x) (KInteger y)))
  | AVQuote,             KSymbolArray x,  KFloatArray y    -> KList (zip x y (fun x y -> f (KSymbol x) (KFloat y)))
  | AVQuote,             KSymbolArray x,  KCharArray y     -> KList (zip x y (fun x y -> f (KSymbol x) (KChar y)))
  | AVQuote,             KSymbolArray x,  KSymbolArray y   -> KList (zip x y (fun x y -> f (KSymbol x) (KSymbol y)))
  | AVQuote,             KSymbolArray x,  y                -> KList (map x (fun x -> f (KSymbol x) y))
  | AVQuote,             KIntegerArray x, y                -> KList (map x (fun x -> f (KInteger x) y))
  | AVQuote,             KFloatArray x,   y                -> KList (map x (fun x -> f (KFloat x) y))
  | AVQuote,             KCharArray x,    y                -> KList (map x (fun x -> f (KChar x) y))
  | AVQuote,             y,               KSymbolArray x   -> KList (map x (fun x -> f y (KSymbol x)))
  | AVQuote,             y,               KIntegerArray x  -> KList (map x (fun x -> f y (KInteger x)))
  | AVQuote,             y,               KFloatArray x    -> KList (map x (fun x -> f y (KFloat x)))
  | AVQuote,             y,               KCharArray x     -> KList (map x (fun x -> f y (KChar x)))
  (* each-left *)
  | AVBackslashColon,    KList x,         y                -> KList (map x (fun x -> f x y))
  | AVBackslashColon,    KSymbolArray x,  y                -> KList (map x (fun x -> f (KSymbol x) y))
  | AVBackslashColon,    KIntegerArray x, y                -> KList (map x (fun x -> f (KInteger x) y))
  | AVBackslashColon,    KFloatArray x,   y                -> KList (map x (fun x -> f (KFloat x) y))
  | AVBackslashColon,    KCharArray x,    y                -> KList (map x (fun x -> f (KChar x) y))
  | AVBackslashColon,    x,               y                -> f x y
  (* each-right *)
  | AVForwardslashColon, x,               KList y          -> KList (map y (f x))
  | AVForwardslashColon, x,               KSymbolArray y   -> KList (map y (fun y -> f x (KSymbol y)))
  | AVForwardslashColon, x,               KIntegerArray y  -> KList (map y (fun y -> f x (KInteger y)))
  | AVForwardslashColon, x,               KFloatArray y    -> KList (map y (fun y -> f x (KFloat y)))
  | AVForwardslashColon, x,               KCharArray y     -> KList (map y (fun y -> f x (KChar y)))
  (* 1/2 over-dyad (fold) (x f/ y) *)
  | AVForwardslash,      _,               KList y          -> Array.fold_right ~init:x ~f y
  | AVForwardslash,      _,               KSymbolArray y   -> Array.fold_right ~init:x ~f:(fun y x -> f x (KSymbol y)) y
  | AVForwardslash,      _,               KIntegerArray y  -> Array.fold_right ~init:x ~f:(fun y x -> f x (KInteger y)) y
  | AVForwardslash,      _,               KFloatArray y    -> Array.fold_right ~init:x ~f:(fun y x -> f x (KFloat y)) y
  | AVForwardslash,      _,               KCharArray y     -> Array.fold_right ~init:x ~f:(fun y x -> f x (KChar y)) y
  | AVForwardslash,      _,               _                -> f x y
  | _ -> raise Not_implemented
let av_mm av f x = match av,x with (* f:monad, derived verb:monad *)
    (* (1/3) over-monad (f/ x) *)
    | AVForwardslash,_ -> let ix = x in let rec loop x = let fx = f x in if match_compare x fx || match_compare ix fx then fx else loop fx in loop ix
    (* (1/3) scan-monad (f\ x) *)
    | AVBackslash,_ -> let ix = x in let rec loop acc x = let fx = f x in let acc = fx::acc in if match_compare x fx || match_compare ix fx then acc else loop acc fx in vec (Array.of_list_rev (loop [] ix))
    (* each-monad *)
    | AVQuote, KList x -> KList (map x f)
    | AVQuote, KSymbolArray x -> vec (map x (fun x -> f (KSymbol x)))
    | AVQuote, KIntegerArray x -> vec (map x (fun x -> f (KInteger x)))
    | AVQuote, KFloatArray x -> vec (map x (fun x -> f (KFloat x)))
    | AVQuote, KCharArray x -> vec (map x (fun x -> f (KChar x)))
    | AVQuote, x -> f x
    | _ -> raise Not_implemented
let av_dm av f x y = match av, x, y with (* f:monad, derived verb:dyad *)
    (* (2/3) over-monad (n f/ x) *)
    | AVForwardslash, KInteger n, x when n >= 0 -> let rec loop x = function |0->x|n -> loop (f x) (n-1) in loop x n
    (* (3/3) over-monad (b f/ y) -- Need proper KFunction *)
    | AVForwardslash, _, _ -> raise Not_implemented
    (* (2/3) scan-monad (n f/ x) *)
    | AVBackslash, KInteger n, x when n >= 0 -> let rec loop acc x = function |0->acc|n -> let fx = f x in loop (fx :: acc) fx (n-1) in vec (Array.of_list_rev (loop [] x n))
    (* (3/3) scan-monad (b f/ y) -- Need proper KFunction *)
    | AVBackslash, _, _ -> raise Not_implemented
    | _ -> raise Not_implemented
let av_md av f x = (* f:dyad, derived verb:monad *)
    let app_pairs f g xs = let fs,_ = Array.fold (sub xs 1 ((Array.length xs)-1)) ~init:([],g xs.(0)) ~f:(fun (acc,x) y -> let y = g y in ((f y x)::acc,y))
                           in Array.of_list_rev fs
    in
    match av, x with
    (* each-pair *)
    | AVQuoteColon, KSymbol _ | AVQuote, KInteger _ | AVQuote, KFloat _ | AVQuote, KChar _ -> f x x
    | AVQuoteColon, KList [||]         -> raise (KError_length [x])
    | AVQuoteColon, KSymbolArray [||]  -> raise (KError_length [x])
    | AVQuoteColon, KIntegerArray [||] -> raise (KError_length [x])
    | AVQuoteColon, KFloatArray [||]   -> raise (KError_length [x])
    | AVQuoteColon, KCharArray [||]    -> raise (KError_length [x])
    | AVQuoteColon, KList x            -> vec (app_pairs f Fn.id x)
    | AVQuoteColon, KSymbolArray x     ->  vec (app_pairs f (fun x -> KSymbol x) x)
    | AVQuoteColon, KIntegerArray x    ->  vec (app_pairs f (fun x -> KInteger x) x)
    | AVQuoteColon, KFloatArray x      ->  vec (app_pairs f (fun x -> KFloat x) x)
    | AVQuoteColon, KCharArray x       ->  vec (app_pairs f (fun x -> KChar x) x)
    | AVQuoteColon, _                  -> raise (KError_type [x])
    (* 2/2 over-dyad (fold) (x f/ y) *)
    | AVForwardslash, KList y          -> Array.reduce_exn ~f y
    | AVForwardslash, KIntegerArray y  -> Array.reduce_exn ~f:(fun x y -> f x y) (map y (fun x -> KInteger x))
    | AVForwardslash, KFloatArray y    -> Array.reduce_exn ~f:(fun x y -> f x y) (map y (fun x -> KFloat x))
    | AVForwardslash, KSymbolArray y   -> Array.reduce_exn ~f:(fun x y -> f x y) (map y (fun x -> KSymbol x))
    | AVForwardslash, KCharArray y     -> Array.reduce_exn ~f:(fun x y -> f x y) (map y (fun x -> KChar x))
    | AVForwardslash, _                -> raise (KError_type [x])

let rec vplus x y = match x,y with
    | KInteger x,      KInteger y              -> KInteger (x+y)
    | KIntegerArray x,KInteger y               -> KIntegerArray (map x (fun x->y+x))
    | KInteger x,      KIntegerArray y         -> KIntegerArray (map y (fun y->y+x))
    | KInteger x,      KFloatArray y           -> let x = Float.of_int x in KFloatArray (map y (fun y->y+.x))
    | KFloat x,        KFloat y                -> KFloat (x+.y)
    | KFloatArray x,   KFloat y                -> KFloatArray (map x (fun x->y+.x))
    | KFloat x,        KFloatArray y           -> KFloatArray (map y (fun y->y+.x))
    | KFloat x,        KIntegerArray y         -> KFloatArray (map y (fun y->(Float.of_int y)+.x))
    | KIntegerArray x, KIntegerArray y         -> KIntegerArray (zip x y (+))
    | KFloatArray x,   KFloatArray y           -> KFloatArray (zip x y (+.))
    | KList x,         KList y                 -> KList (zip x y vplus)
    | KInteger _,      KList y
    | KFloat _,        KList y                 -> KList (map y (vplus x))
    | KList x,         KInteger _              -> KList (map x (fun x -> vplus x y))
    | _ -> raise (KError_type [x;y])
let vplus_m =
    let vph p q x f g = KList (Array.init q ~f:(fun i -> f (Array.init p ~f:(fun j ->(g x.(j)).(i))))) in function
    | KList [||] -> KList [||]
    | KList x ->
        let p,q = Array.length x,Option.value_exn (Array.max_elt ~cmp:Int.compare (map x n)) in
        let ts = ts x in
        (match is_vector ts with
        | Some TIntegerArray -> vph p q x (fun x -> KIntegerArray x) (function (KIntegerArray x) -> x | _ -> never())
        | Some TFloatArray -> vph p q x (fun x -> KFloatArray x) (function (KFloatArray x) -> x | _ -> never())
        | Some TSymbolArray -> vph p q x (fun x -> KSymbolArray x) (function (KSymbolArray x) -> x | _ -> never())
        | Some TCharArray -> vph p q x (fun x -> KCharArray x) (function (KCharArray x) -> x | _ -> never())
        | Some _ | None ->
          KList (Array.init q ~f:(fun i -> (vec (Array.init p ~f:(fun j ->
            match x.(j) with
            | KIntegerArray y -> KInteger y.(i)
            | KFloatArray y -> KFloat y.(i)
            | KCharArray y -> KChar y.(i)
            | KSymbolArray y -> KSymbol y.(i)
            | KList y -> y.(i)
            | y -> y))))))
    | x -> x
let vplus_av_mm av x = av_mm av vplus_m x
let vplus_av_md av x = av_md av vplus x
let vplus_av_dm av x y = av_dm av vplus_m x y
let vplus_av_dd av x y = match av,x,y with
  | AVForwardslash, KInteger x, KIntegerArray y -> KInteger (Array.fold y ~init:x ~f:(+))
  | AVForwardslash, KInteger x, KFloatArray y   -> KFloat (Array.fold y ~init:(Float.of_int x) ~f:(+.))
  | AVForwardslash, KFloat x,   KFloatArray y   -> KFloat (Array.fold y ~init:x ~f:(+.))
  | AVForwardslash, KFloat x,   KIntegerArray y -> KFloat (Array.fold (map y Float.of_int) ~init:x ~f:(+.))
  | _ -> av_dd av vplus x y
let rec vminus x y = match x,y with
    | KInteger x,      KInteger y      -> KInteger (x-y)
    | KInteger x,      KIntegerArray y -> KIntegerArray (map y (fun y->y-x))
    | KInteger x,      KFloatArray y   -> let x = Float.of_int x in KFloatArray (map y (fun y->y-.x))
    | KFloat x,        KFloat y        -> KFloat (x-.y)
    | KFloat x,        KFloatArray y   -> KFloatArray (map y (fun y->y-.x))
    | KFloat x,        KIntegerArray y -> KFloatArray (map y (fun y->(Float.of_int y)-.x))
    | KIntegerArray x, KIntegerArray y -> KIntegerArray (zip x y (-))
    | KFloatArray x,   KFloatArray y   -> KFloatArray (zip x y (-.))
    | KList x,         KList y         -> KList (zip x y vminus)
    | _ -> raise (KError_type [x;y])
let rec vminus_m x = match x with
  | KInteger x      -> KInteger (-x)
  | KFloat x        -> KFloat (0.0-.x)
  | KIntegerArray x -> KIntegerArray (map x (fun x -> -x))
  | KFloatArray x   -> KFloatArray (map x (fun x -> 0.0-.x))
  | KList x         -> KList (map x vminus_m)
  | _ -> raise (KError_type [x])
let vminus_av_mm av x = av_mm av vminus_m x
let vminus_av_md av x = av_md av vminus x
let vminus_av_dm av x y = av_dm av vminus_m x y
let vminus_av_dd av x y = match av,x,y with
  | AVForwardslash, KInteger x, KIntegerArray y -> KInteger (Array.fold y ~init:x ~f:(-))
  | AVForwardslash, KInteger x, KFloatArray y   -> KFloat (Array.fold y ~init:(Float.of_int x) ~f:(-.))
  | AVForwardslash, KFloat x,   KFloatArray y   -> KFloat (Array.fold y ~init:x ~f:(-.))
  | AVForwardslash, KFloat x,   KIntegerArray y -> KFloat (Array.fold (map y Float.of_int) ~init:x ~f:(-.))
  | _ -> av_dd av vminus x y
let rec vstar x y = match x,y with
    | KInteger _,      KList y         -> KList (map y (vstar x))
    | KList x,         KInteger _      -> KList (map x (fun x -> vstar x y))
    | KInteger x,      KInteger y      -> KInteger (x*y)
    | KFloat x,        KFloat y        -> KFloat (x*.y)
    | KIntegerArray x, KIntegerArray y -> KIntegerArray (zip x y ( * ))
    | KFloatArray x,   KFloatArray y   -> KFloatArray (zip x y ( *. ))
    | KList x,         KList y         -> KList (zip x y vstar)
    | KIntegerArray x, KList y         -> KList (zip x y (fun x y -> vstar (KInteger x) y))
    | KInteger x,      KIntegerArray y -> KIntegerArray (map y (fun y -> x * y))
    | KIntegerArray x, KInteger y      -> KIntegerArray (map x (fun x -> x * y))
    | KInteger x,      KFloatArray y   -> let x = Float.of_int x in KFloatArray (map y (fun y -> x *. y))
    | _ -> raise (KError_type [x;y]) (* TODO: Missing cases: float*list, list*integer etc. *)
let vstar_m x = match x with
    | KList [||]         -> KNull
    | KList x            -> x.(0)
    | KIntegerArray [||] -> KInteger 0
    | KIntegerArray x    -> KInteger x.(0)
    | KFloatArray [||]   -> KFloat 0.0
    | KFloatArray x      -> KFloat x.(0)
    | KSymbolArray [||]  -> KNull
    | KSymbolArray x     -> KSymbol x.(0)
    | KCharArray [||]    -> KChar ' '
    | KCharArray x       -> KChar x.(0)
    | x -> x
let vstar_av_mm av x = av_mm av vstar_m x
let vstar_av_md av x = av_md av vstar x
let vstar_av_dm av x y = av_dm av vstar_m x y
let vstar_av_dd av x y = av_dd av vstar x y
let vexclaim x y = match x,y with
  | KIntegerArray x, KIntegerArray y -> KList (map x (fun i -> KIntegerArray (rot i y)))
  | KIntegerArray x, KFloatArray y   -> KList (map x (fun i -> KFloatArray (rot i y)))
  | KInteger x,      KInteger y      -> KInteger (x mod y)
  | KInteger x,      KFloat y        -> KFloat (Float.mod_float y (Float.of_int x))
  | KInteger x,      KIntegerArray y -> KIntegerArray (rot x y)
  | KInteger x,      KFloatArray y   -> KFloatArray (rot x y)
  | KInteger x,      KSymbolArray y  -> KSymbolArray (rot x y)
  | KInteger x,      KCharArray y    -> KCharArray (rot x y)
  | KInteger x,      KList y         -> KList (rot x y)
  | _ -> raise (KError_type [x;y])
let vexclaim_m = function
    | KInteger 0                     -> KIntegerArray [||]
    | KInteger x when x > 0          -> KIntegerArray (Array.init x ~f:Fn.id)
    | KDictionary d                  -> KSymbolArray (Array.of_list (Hashtbl.keys d))
    | x -> raise (KError_type [x])
let vexclaim_av_dm av x y = av_dm av vexclaim_m x y
let vexclaim_av_md av x = av_md av vexclaim x
let vexclaim_av_mm av x = match av,x with
    | AVQuote, KIntegerArray x    ->  KList (map x (fun n -> KIntegerArray (Array.init n ~f:Fn.id)))
    | _,x -> raise (KError_type [x])
let vexclaim_av_dd av x y = av_dd av vexclaim x y
let vpercent x y = match x,y with (* fsa, non-standard. (transitions: state x symbol -> state) % (input tape) ~> (state sequence) *)
  | KList x, KIntegerArray y ->
    let t = map x (function (KIntegerArray x) -> x |_ -> never()) in
    let _,s =  Array.fold y ~init:(0,[]) ~f:(fun (i,s) j -> let xij = t.(i).(j) in xij,(xij::s)) in
    KIntegerArray (Array.of_list_rev s)
  | _ -> raise Not_implemented
let rec vpercent_m x = match x with
  | KInteger x -> KFloat (1.0/.(Float.of_int x))
  | KFloat x -> KFloat (1.0/.x)
  | KIntegerArray x -> KFloatArray (map x (fun x -> (1.0/.(Float.of_int x))))
  | KFloatArray x -> KFloatArray (map x (fun x -> 1.0/.x))
  | KList x -> KList (map x vpercent_m)
  | _ -> raise (KError_type [x])

let vpercent_av_mm av x = av_mm av vpercent_m x
let vpercent_av_md av x = av_md av vpercent x
let vpercent_av_dm av x y = av_dm av vpercent_m x y
let vpercent_av_dd av x y = av_dd av vpercent x y
let rec vpipe x y = match x,y with
  | KInteger x,     KInteger y when x >= y -> KInteger x
  | KInteger _,     KInteger y             -> KInteger y
  | KFloat x,       KFloat y when x >= y   -> KFloat x
  | KFloat _,       KFloat y               -> KFloat y
  | KChar x,        KChar y when x >= y    -> KChar x
  | KChar _,        KChar y                -> KChar y
  | KIntegerArray x,KIntegerArray y        -> KIntegerArray (zip x y Int.max)
  | KFloatArray x,  KFloatArray y          -> KFloatArray (zip x y Float.max)
  | KCharArray x,   KCharArray y           -> KCharArray (zip x y Char.max)
  | KList x,        KList y                -> KList (zip x y vpipe)
  | KInteger x,     KSymbol y              -> KSymbol y
  | KSymbol x,      KInteger y             -> KSymbol x
  | KSymbol x,      KChar y                -> KSymbol x
  | KSymbol x,      KSymbol y              -> KSymbol (if x >= y then x else y) (* FIXME: lexicographic comparison of symbols *)
  | _ -> raise (KError_type [x;y])
let vpipe_m x = match x with
   | KIntegerArray xs -> let a = Array.copy xs in Array.rev_inplace a; KIntegerArray a
   | KFloatArray xs   -> let a = Array.copy xs in Array.rev_inplace a; KFloatArray a
   | KSymbolArray xs  -> let a = Array.copy xs in Array.rev_inplace a; KSymbolArray a
   | KCharArray xs    -> let a = Array.copy xs in Array.rev_inplace a; KCharArray a
   | KList xs         -> let a = Array.copy xs in Array.rev_inplace a; KList a
   | x                -> x
let vpipe_av_mm av x = av_mm av vpipe_m x
let vpipe_av_md av x = av_md av vpipe x
let vpipe_av_dm av x y = av_dm av vpipe_m x y
let vpipe_av_dd av x y = av_dd av vpipe x y
let rec vampersand x y = match x,y with
  | KInteger x,     KInteger y when x <= y -> KInteger x
  | KInteger _,     KInteger y             -> KInteger y
  | KFloat x,       KFloat y when x <= y   -> KFloat x
  | KFloat _,       KFloat y               -> KFloat y
  | KChar x,        KChar y when x <= y    -> KChar x
  | KChar _,        KChar y                -> KChar y
  | KIntegerArray x,KIntegerArray y        -> KIntegerArray (zip x y Int.min)
  | KFloatArray x,  KFloatArray y          -> KFloatArray (zip x y Float.min)
  | KCharArray x,   KCharArray y           -> KCharArray (zip x y Char.min)
  | KList x,        KList y                -> KList (zip x y vampersand)
  | _ -> raise (KError_type [x;y])
let vampersand_m x = match x with
  | KInteger x when x >= 0 -> KIntegerArray (Array.create ~len:x 0)
  | KInteger _ -> raise (KError_domain [x])
  | KIntegerArray x -> let a = Array.create ~len:(Array.fold ~init:0 ~f:(+) x) 0 in
                       Array.iter x ~f:(fun y -> if y < 0 then raise (KError_domain [KIntegerArray x]));
                       ignore (Array.fold x ~init:(0,0) ~f:(fun (i,p) x -> Array.fill a ~pos:p ~len:x i; (i+1,p+x)));
                       KIntegerArray a
  | _ -> raise (KError_type [x])

let vampersand_av_mm av x = av_mm av vampersand_m x
let vampersand_av_md av x = av_md av vampersand x
let vampersand_av_dm av x y = av_dm av vampersand_m x y
let vampersand_av_dd av x y = av_dd av vampersand x y
let vcomma x y = match x,y with (* join *)
    | KList x,         KList y         -> KList (append x y)
    | KInteger x,      KInteger y      -> KIntegerArray [|x;y|]
    | KIntegerArray x, KIntegerArray y -> KIntegerArray (append x y)
    | KFloat x,        KFloat y        -> KFloatArray [|x;y|]
    | KFloatArray x,   KFloatArray y   -> KFloatArray (append x y)
    | KChar x,         KChar y         -> KCharArray [|x;y|]
    | KCharArray x,    KCharArray y    -> KCharArray (append x y)
    | KSymbol x,       KSymbol y       -> KSymbolArray [|x;y|]
    | KSymbolArray x,  KSymbolArray y  -> KSymbolArray (append x y)
    | KInteger x,      KIntegerArray y -> KIntegerArray (append [|x|] y)
    | KIntegerArray x, KInteger y      -> KIntegerArray (append x [|y|])
    | KFloat x,        KFloatArray y   -> KFloatArray (append [|x|] y)
    | KFloatArray x,   KFloat y        -> KFloatArray (append x [|y|])
    | KChar x,         KCharArray y    -> KCharArray (append [|x|] y)
    | KCharArray x,    KChar y         -> KCharArray (append x [|y|])
    | KSymbol x,       KSymbolArray y  -> KSymbolArray (append [|x|] y)
    | KSymbolArray x,  KSymbol y       -> KSymbolArray (append x [|y|])
    | KFloat x,        KInteger y      -> KFloatArray [|x;Float.of_int y|]
    | KInteger x,      KFloat y        -> KFloatArray [|Float.of_int x;y|]
    | KFloat x,        KIntegerArray y -> KFloatArray (append [|x|] (map y Float.of_int))
    | KIntegerArray x, KFloat y        -> KFloatArray (append (map x Float.of_int) [|y|])
    | KFloatArray x,   KInteger y      -> KFloatArray (append x [|Float.of_int y|])
    | KInteger x,      KFloatArray y   -> KFloatArray (append [|Float.of_int x|] y)
    | KFloatArray x,   KIntegerArray y -> KFloatArray (append x (map y Float.of_int))
    | KIntegerArray x, KFloatArray y   -> KFloatArray (append (map x Float.of_int) y)
    | KDictionary _,KDictionary _|KFunction _,KFunction _|KNull,KNull|KChar _,KFloat _|KFloat _,KChar _|KChar _,KInteger _|KInteger _,KChar _|KInteger _,KSymbol _|KSymbol _,KInteger _|KInteger _,KNull|KNull,KInteger _|KFloat _,KSymbol _|KSymbol _,KFloat _|KFloat _,KFunction _|KFunction _,KFloat _|KFloat _,KNull|KNull,KFloat _|KFunction _,KSymbol _|KSymbol _,KFunction _|KDictionary _,KInteger _|KInteger _,KDictionary _|KDictionary _,KFloat _|KFloat _,KDictionary _|KDictionary _,KSymbol _|KSymbol _,KDictionary _|KDictionary _,KFunction _|KFunction _,KDictionary _|KDictionary _,KNull|KNull,KDictionary _|KFunction _,KInteger _|KInteger _,KFunction _|KFunction _,KNull|KNull,KFunction _|KNull,KSymbol _|KSymbol _,KNull|KChar _,KSymbol _|KSymbol _,KChar _|KChar _,KDictionary _|KDictionary _,KChar _|KChar _,KFunction _|KFunction _,KChar _|KChar _,KNull|KNull,KChar _ ->
      KList [|x;y|]
    | KSymbol _,KList y|KNull,KList y|KInteger _,KList y|KFloat _,KList y|KChar _,KList y|KDictionary _,KList y|KFunction _,KList y ->
      KList (append [|x|] y)
    | KList x,KSymbol _| KList x,KNull| KList x,KInteger _| KList x,KFloat _| KList x,KChar _| KList x,KDictionary _ | KList x,KFunction _ ->
      KList (append x [|y|])
    | KList x,KSymbolArray _|KList x,KIntegerArray _|KList x,KFloatArray _ |KList x,KCharArray _ ->
      KList (append x (as_list y))
    | KSymbolArray _,KList y|KIntegerArray _,KList y|KFloatArray _,KList y|KCharArray _,KList y ->
      KList (append (as_list x) y)
    | KChar _,KFloatArray _|KChar _,KIntegerArray _|KChar _,KSymbolArray _|KDictionary _,KCharArray _|KDictionary _,KFloatArray _|KDictionary _,KIntegerArray _|KDictionary _,KSymbolArray _|KFloat _,KCharArray _|KFloat _,KSymbolArray _|KFunction _,KCharArray _|KFunction _,KFloatArray _|KFunction _,KIntegerArray _|KFunction _,KSymbolArray _|KInteger _,KCharArray _|KInteger _,KSymbolArray _|KIntegerArray _,KChar _|KNull,KCharArray _|KNull,KFloatArray _|KNull,KIntegerArray _|KNull,KSymbolArray _|KSymbol _,KCharArray _|KSymbol _,KIntegerArray _|KSymbol _,KFloatArray _ ->
      KList (append [|x|] (as_list y))
    | KCharArray _,KDictionary _|KCharArray _,KFloat _|KCharArray _,KFunction _|KCharArray _,KInteger _|KCharArray _,KNull|KCharArray _,KSymbol _|KFloatArray _,KChar _|KFloatArray _,KDictionary _|KFloatArray _,KFunction _|KFloatArray _,KNull|KFloatArray _,KSymbol _|KIntegerArray _,KDictionary _|KIntegerArray _,KFunction _|KIntegerArray _,KNull|KIntegerArray _,KSymbol _|KSymbolArray _,KChar _|KSymbolArray _,KDictionary _|KSymbolArray _,KFloat _|KSymbolArray _,KFunction _|KSymbolArray _,KInteger _|KSymbolArray _, KNull ->
      KList (append (as_list x) [|y|])
    | KCharArray _,KFloatArray _|KCharArray _,KIntegerArray _| KCharArray _,KSymbolArray _|KFloatArray _,KCharArray _|KFloatArray _,KSymbolArray _|KIntegerArray _,KCharArray _|KIntegerArray _,KSymbolArray _|KSymbolArray _,KCharArray _|KSymbolArray _,KFloatArray _|KSymbolArray _,KIntegerArray _ ->
      KList (append (as_list x) (as_list y))
let vcomma_m x = match x with (* enlist *)
    | KChar x    -> KCharArray [|x|]
    | KFloat x   -> KFloatArray [|x|]
    | KInteger x -> KIntegerArray [|x|]
    | KSymbol x  -> KSymbolArray [|x|]
    | x -> KList [|x|]
let vcomma_av_mm av x = av_mm av vcomma_m x
let vcomma_av_md av x = av_md av vcomma x
let vcomma_av_dm av x y = av_dm av vcomma_m x y
let vcomma_av_dd av x y = match av,x,y with
    | AVForwardslash, KCharArray x,   KCharArray y    -> let a = Array.append x y in Array.rev_inplace a; KCharArray a
    | AVForwardslash, KFloatArray x,  KFloatArray y   -> let a = Array.append x y in Array.rev_inplace a; KFloatArray a
    | AVForwardslash, KIntegerArray x,KIntegerArray y -> let a = Array.append x y in Array.rev_inplace a; KIntegerArray a
    | AVForwardslash, KSymbolArray x, KSymbolArray y  -> let a = Array.append x y in Array.rev_inplace a; KSymbolArray a
    | AVForwardslash, KList [||],     KCharArray y    -> KCharArray y
    | AVForwardslash, KList [||],     KFloatArray y   -> KFloatArray y
    | AVForwardslash, KList [||],     KIntegerArray y -> KIntegerArray y
    | AVForwardslash, KList [||],     KSymbolArray y  -> KSymbolArray y
    | AVForwardslash, KList [||],     KList y         -> KList y
    | AVForwardslash, KList x,        KList y         -> let a = Array.append x y in Array.rev_inplace a; KList a
    | _ -> av_dd av vcomma x y
let vcircumflex x y = match x,y with
    | KInteger x,KInteger y when y >= 0 -> KInteger (Int.pow x y)
    | KInteger x,KInteger y             -> KFloat ((Float.of_int x) ** (Float.of_int y))
    | _                                 -> raise (KError_type [x;y])
let rec vcircumflex_m x = match x with
    | KInteger _ | KChar _ | KFloat _ | KSymbol _ -> KIntegerArray [||]
    | KList x -> vcomma (KIntegerArray [|Array.length x|]) (vcircumflex_m x.(0))
    | KDictionary _ -> raise Not_implemented
    | y -> KIntegerArray [|n y|]
let vcircumflex_av_mm av x = av_mm av vcircumflex_m x
let vcircumflex_av_md av x = av_md av vcircumflex x
let vcircumflex_av_dm av x y = av_dm av vcircumflex_m x y
let vcircumflex_av_dd av x y = av_dd av vcircumflex x y
let rec vlangle x y = let lt f x y = if f x y < 0 then 1 else 0 in match x,y with
    | KChar x,         KChar y          -> KInteger (lt Char.compare x y)
    | KCharArray x,    KCharArray y     -> KIntegerArray (zip x y (lt Char.compare))
    | KInteger x,      KInteger y       -> KInteger (lt Int.compare x y)
    | KInteger x,      KIntegerArray y  -> KIntegerArray (map y (lt Int.compare x))
    | KInteger x,      KFloatArray y    -> let x = Float.of_int x in KIntegerArray (map y (lt Float.compare x))
    | KIntegerArray x, KIntegerArray y  -> KIntegerArray (zip x y (lt Int.compare))
    | KSymbol x,       KSymbol y        -> KInteger (lt Symbol.compare x y)
    | KSymbolArray x,  KSymbolArray y   -> KIntegerArray (zip x y (lt Symbol.compare))
    | KList x,         KList y          -> KList (zip x y vlangle)
    | _ -> raise (KError_type [x;y]) (* Not_implemented, actually *)
let vlangle_m _ = raise Not_implemented (* < grade up *)
let vlangle_av_mm av x = av_mm av vlangle_m x
let vlangle_av_md av x = av_md av vlangle x
let vlangle_av_dm av x y = av_dm av vlangle_m x y
let vlangle_av_dd av x y = av_dd av vlangle x y
let vrangle x y = vlangle y x
let vrangle_m _ = raise Not_implemented (* > grade down *)
let vrangle_av_mm av x = av_mm av vrangle_m x
let vrangle_av_md av x = av_md av vrangle x
let vrangle_av_dm av x y = av_dm av vrangle_m x y
let vrangle_av_dd av x y = av_dd av vrangle x y
let rec vequals x y = let eq f x y = if f x y then 1 else 0 in match x,y with
    | KChar x,         KChar y         -> KInteger (eq Char.equal x y)
    | KCharArray x,    KChar y         -> KIntegerArray (map x (eq Char.equal y))
    | KCharArray x,    KCharArray y    -> KIntegerArray (zip x y (eq Char.equal))
    | KInteger x,      KInteger y      -> KInteger (eq Int.equal x y)
    | KIntegerArray x, KIntegerArray y -> KIntegerArray (zip x y (eq Int.equal))
    | KList x,         KList y         -> KList (zip x y vequals)
    | KSymbol x,       KSymbol y       -> KInteger (eq Symbol.equal x y)
    | KSymbolArray x,  KSymbolArray y  -> KIntegerArray (zip x y (eq Symbol.equal))
    | _ -> raise (KError_type [x;y])
let vequals_m _ = raise Not_implemented (* = group *)
let vequals_av_mm av x = av_mm av vequals_m x
let vequals_av_md av x = av_md av vequals x
let vequals_av_dm av x y = av_dm av vequals_m x y
let vequals_av_dd av x y = av_dd av vequals x y
let vpound x y = match x,y with (* # take / reshape *)
  | KInteger 0,      KFloat 0.0      -> KFloatArray [||]
  | KInteger 0,      KFloat 0.0      -> KFloatArray [||]
  | KInteger 0,      KList _         -> KList [||]
  | KInteger 0,      KCharArray _    -> KCharArray [||]
  | KInteger 0,      KIntegerArray _ -> KIntegerArray [||]
  | KInteger 0,      KSymbolArray _  -> KSymbolArray [||]
  | KInteger 0,      KFloatArray _   -> KFloatArray [||]
  | KInteger x,      KList y         -> KList (take x y)
  | KInteger x,      KCharArray y    -> KCharArray (take x y)
  | KInteger x,      KIntegerArray y -> KIntegerArray (take x y)
  | KInteger x,      KSymbolArray y  -> KSymbolArray (take x y)
  | KInteger x,      KFloatArray y   -> KFloatArray (take x y)
  | KIntegerArray x, KList y         -> let nx = Array.length x in let ny = Array.length y in reshape_k x nx y ny
  | KIntegerArray x, KCharArray y    -> reshape_v x y (fun a -> KCharArray a)
  | KIntegerArray x, KIntegerArray y -> reshape_v x y (fun a -> KIntegerArray a)
  | KIntegerArray x, KSymbolArray y  -> reshape_v x y (fun a -> KSymbolArray a)
  | KIntegerArray x, KFloatArray y   -> reshape_v x y (fun a -> KFloatArray a)
  | _ -> raise Not_implemented
let vpound_m x = KInteger (n x)
let vpound_av_mm av x = av_mm av vpound_m x
let vpound_av_md av x = av_md av vpound x
let vpound_av_dm av x y = av_dm av vpound_m x y
let vpound_av_dd av x y = av_dd av vpound x y
let vlodash x y = match x,y with
  | KInteger _,      KList [||]         -> y
  | KInteger _,      KCharArray [||]    -> y
  | KInteger _,      KIntegerArray [||] -> y
  | KInteger _,      KSymbolArray [||]  -> y
  | KInteger _,      KFloatArray [||]   -> y
  | KInteger x,      KList y            -> KList (drop x y)
  | KInteger x,      KCharArray y       -> KCharArray (drop x y)
  | KInteger x,      KIntegerArray y    -> KIntegerArray (drop x y)
  | KInteger x,      KSymbolArray y     -> KSymbolArray (drop x y)
  | KInteger x,      KFloatArray y      -> KFloatArray (drop x y)
  | KIntegerArray x, KList y            -> KList (cut x y (fun a -> KList a))
  | KIntegerArray x, KCharArray y       -> KList (cut x y (fun a -> KCharArray a))
  | KIntegerArray x, KIntegerArray y    -> KList (cut x y (fun a -> KIntegerArray a))
  | KIntegerArray x, KSymbolArray y     -> KList (cut x y (fun a -> KSymbolArray a))
  | KIntegerArray x, KFloatArray y      -> KList (cut x y (fun a -> KFloatArray a))
  | _ -> raise Not_implemented
let rec vlodash_m = function
  | KInteger x      -> KInteger x
  | KFloat x        -> KInteger (Int.of_float (Float.round_down x))
  | KIntegerArray x -> KIntegerArray x
  | KFloatArray x   -> KIntegerArray (map x (Fn.compose Int.of_float Float.round_down))
  | KList x         -> KList (map x vlodash_m)
  | x               -> raise (KError_type [x])
let vlodash_av_mm av x = av_mm av vlodash_m x
let vlodash_av_md av x = av_md av vlodash x
let vlodash_av_dm av x y = av_dm av vlodash_m x y
let vlodash_av_dd av x y = av_dd av vlodash x y
let vtilde x y = KInteger (match_compare_int x y)
let rec vtilde_m x = match x with
  | KInteger _      -> vtilde x (KInteger 0)
  | KFloat _        -> vtilde x (KFloat 0.0)
  | KIntegerArray x -> KIntegerArray (map x (match_compare_int 0))
  | KFloatArray x   -> KIntegerArray (map x (match_compare_int 0.0))
  | KList x         -> KList (map x vtilde_m)
  | _               -> raise (KError_type [x])
let vtilde_av_mm av x = av_mm av vtilde_m x
let vtilde_av_md av x = av_md av vtilde x
let vtilde_av_dm av x y = av_dm av vtilde_m x y
let vtilde_av_dd av x y = av_dd av vtilde x y
let vdollar _ _ = raise Not_implemented (* $ format *)
let vdollar_m _ = raise Not_implemented (* $ format *)
let vdollar_av_mm av x = av_mm av vdollar_m x
let vdollar_av_md av x = av_md av vdollar x
let vdollar_av_dm av x y = av_dm av vdollar_m x y
let vdollar_av_dd av x y = av_dd av vdollar x y
let vquestion x y =
    let find x y = KInteger (match (Array.findi x ~f:(fun _ -> match_compare y)) with
    | Some (i,_) -> i
    | None -> Array.length x) in
    match x,y with
    | KNull,           _          -> KInteger 1
    | KIntegerArray x, KInteger y -> find x y
    | KList x,         y          -> find x y
    | KCharArray x,    KChar y    -> find x y
    | KSymbolArray x,  KSymbol y  -> find x y
    | KFloatArray x,   KFloat y   -> find x y
    | _                           -> raise (KError_type [x;y])
let vquestion_m x = match x with
  | KList x        -> KList (Array.of_list (List.dedup (Array.to_list x))) (* SLOW *)
  | KSymbolArray x -> KSymbolArray (Array.of_list (List.dedup (Array.to_list x))) (* SLOW *)
  | KCharArray x   -> KCharArray (Array.of_list (List.dedup (Array.to_list x))) (* SLOW *)
  | _ ->  raise (KError_rank [x])
let vquestion_av_mm av x = av_mm av vquestion_m x
let vquestion_av_md av x = av_md av vquestion x
let vquestion_av_dm av x y = av_dm av vquestion_m x y
let vquestion_av_dd av x y = av_dd av vquestion x y
(* let vat_op a i = if 0 < i && i < Array.length a then a.(i) else raise (KError_index [KInteger i]) *)
let rec vat x y = match x,y with
  | KList x,         KInteger y      -> x.(y)
  | KIntegerArray x, KInteger y      -> KInteger x.(y)
  | KFloatArray x,   KInteger y      -> KFloat x.(y)
  | KCharArray x,    KInteger y      -> KChar x.(y)
  | KSymbolArray x,  KInteger y      -> KSymbol x.(y)
  | KList x,         KIntegerArray y -> KList (map y (fun y -> x.(y)))
  | KIntegerArray x, KIntegerArray y -> KIntegerArray (map y (fun y -> x.(y)))
  | KFloatArray x,   KIntegerArray y -> KFloatArray (map y (fun y -> x.(y)))
  | KCharArray x,    KIntegerArray y -> KCharArray (map y (fun y -> x.(y)))
  | KSymbolArray x,  KIntegerArray y -> KSymbolArray (map y (fun y -> x.(y)))
  | KIntegerArray _, KList y         -> KList (map y (vat x))
  | KFloatArray _,   KList y         -> KList (map y (vat x))
  | KCharArray _,    KList y         -> KList (map y (vat x))
  | KSymbolArray _,  KList y         -> KList (map y (vat x))
  | KDictionary x,   KSymbol y       -> Symbol.Table.find_exn x y
  | KDictionary x,   KSymbolArray y  -> KList (map y (Symbol.Table.find_exn x))
  | KDictionary _,   KList y         -> KList (map y (vat x))
  | _                                -> raise (KError_type [x;y])
let vat_m _ = raise Not_implemented
let vat_av_mm av x = av_mm av vat_m x
let vat_av_md av x = av_md av vat x
let vat_av_dm av x y = av_dm av vat_m x y
let vat_av_dd av x y = av_dd av vat x y
let rec vdot x y = match x,y with
  | KList _, KIntegerArray y     -> Array.fold y ~init:x ~f:(fun x i -> vdot x (KInteger i))
  | _,       KList [|_|]         -> vat x y
  | _,       KIntegerArray [|_|] -> vat x y
  | _,       KInteger y          -> vat x (KInteger y)
  | _                            -> raise Not_implemented
let vdot_m x = match x with
  | KSymbol s -> lookup (lookup_symbol s)
  | KList x -> let d = dict () in
    for i=0 to Array.length x-1 do
      match x.(i) with
      | KList x ->(match x.(0) with
                  | KSymbol key -> Hashtbl.replace d ~key ~data:x.(1)
                  | _ -> raise (KError_rank [KList x]))
      | _ -> raise (KError_rank [KList x])
    done; KDictionary d
  | KDictionary x ->
      KList (Symbol.Table.to_alist x
      |> List.map ~f:(fun (s,k) -> KList [|KSymbol s;k|])
      |> Array.of_list)
  | _ -> raise (KError_type [x])
let vdot_av_mm av x = av_mm av vdot_m x
let vdot_av_md av x = av_md av vdot x
let vdot_av_dm av x y = av_dm av vdot_m x y
let vdot_av_dd av x y = av_dd av vdot x y
let eid = lookup
let eassign v x =
  let d, s = match v with
  | IdRelative s -> !pwd,s
  | IdAbsolute s -> tree,s
  in let rec loop d s =
    match s with
    | [] -> ()
    | [v] -> Hashtbl.replace d ~key:v ~data:x
    | v::s -> (match Hashtbl.find d v with
          | None -> let d' = dict () in Hashtbl.replace d ~key:v ~data:(KDictionary d'); loop d' s
          | Some (KDictionary d) -> loop d s)
  in loop d s; x
let rec ed f : k -> k -> k =
    let f = match e f with KFunction f -> f | f -> raise (KError_type [f]) in
    match f with
    | F2 e -> exy e
    | F _e -> (match _e with
    | EVerb VPlus -> vplus
    | EAdverb (av,EVerb VPlus) -> vplus_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VPlus)) -> vplus_av_dm av
    | EVerb VMinus -> vminus
    | EAdverb (av,EVerb VMinus) -> vminus_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VMinus)) -> vminus_av_dm av
    | EVerb VStar -> vstar
    | EAdverb (av,EVerb VStar) -> vstar_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VStar)) -> vstar_av_dm av
    | EVerb VExclaim -> vexclaim
    | EAdverb (av,EVerb VExclaim) -> vexclaim_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VExclaim)) -> vexclaim_av_dm av
    | EVerb VPercent -> vpercent
    | EAdverb (av,EVerb VPercent) -> vpercent_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VPercent)) -> vpercent_av_dm av
    | EVerb VPipe -> vpipe
    | EAdverb (av,EVerb VPipe) -> vpipe_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VPipe)) -> vpipe_av_dm av
    | EVerb VAmpersand -> vampersand
    | EAdverb (av,EVerb VAmpersand) -> vampersand_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VAmpersand)) -> vampersand_av_dm av
    | EVerb VCircumflex -> vcircumflex
    | EAdverb (av,EVerb VCircumflex) -> vcircumflex_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VCircumflex)) -> vcircumflex_av_dm av
    | EVerb VLangle -> vlangle
    | EAdverb (av,EVerb VLangle) -> vlangle_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VLangle)) -> vlangle_av_dm av
    | EVerb VRangle -> vrangle
    | EAdverb (av,EVerb VRangle) -> vrangle_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VRangle)) -> vrangle_av_dm av
    | EVerb VEquals -> vequals
    | EAdverb (av,EVerb VEquals) -> vequals_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VEquals)) -> vequals_av_dm av
    | EVerb VPound -> vpound
    | EAdverb (av,EVerb VPound) -> vpound_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VPound)) -> vpound_av_dm av
    | EVerb VLodash -> vlodash
    | EAdverb (av,EVerb VLodash) -> vlodash_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VLodash)) -> vlodash_av_dm av
    | EVerb VTilde -> vtilde
    | EAdverb (av,EVerb VTilde) -> vtilde_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VTilde)) -> vtilde_av_dm av
    | EVerb VDollar -> vdollar
    | EAdverb (av,EVerb VDollar) -> vdollar_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VDollar)) -> vdollar_av_dm av
    | EVerb VQuestion -> vquestion
    | EAdverb (av,EVerb VQuestion) -> vquestion_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VQuestion)) -> vquestion_av_dm av
    | EVerb VAt -> vat
    | EAdverb (av,EVerb VAt) -> vat_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VAt)) -> vat_av_dm av
    | EVerb VDot -> vdot
    | EAdverb (av,EVerb VDot) -> vdot_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VDot)) -> vdot_av_dm av
    | EVerb VComma -> vcomma
    | EAdverb (av,EVerb VComma) -> vcomma_av_dd av
    | EAdverb (av,EAdverb(AVColon,EVerb VComma)) -> vcomma_av_dm av
    | EAdverb (av,EId id) -> let KFunction f = e (EId id) in ed (EAdverb(av,EFunction f)) (* FIXME *)
    | EAdverb (av,EFunction (F1 f)) -> av_dm av (em f)
    | EAdverb (av,EFunction (F2 f)) -> av_dd av (ed f)
    | EAdverb (av,e) -> av_dd av (ed e)
    | _ -> raise Not_implemented)
   | _ -> raise Not_implemented
and em f : k -> k =
    let f = match e f with KFunction f -> f | f -> raise (KError_type [f]) in
    match f with
    | F1 e -> ex e
    | F _e -> (match _e with
    | EVerb VPlus -> vplus_m
    | EAdverb (av,EVerb VPlus) -> vplus_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VPlus)) -> vplus_av_mm av
    | EVerb VMinus -> vminus_m
    | EAdverb (av,EVerb VMinus) -> vminus_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VMinus)) -> vminus_av_mm av
    | EVerb VStar -> vstar_m
    | EAdverb (av,EVerb VStar) -> vstar_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VStar)) -> vstar_av_mm av
    | EVerb VExclaim -> vexclaim_m
    | EAdverb (av,EVerb VExclaim) -> vexclaim_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VExclaim)) -> vexclaim_av_mm av
    | EVerb VPercent -> vpercent_m
    | EAdverb (av,EVerb VPercent) -> vpercent_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VPercent)) -> vpercent_av_mm av
    | EVerb VPipe -> vpipe_m
    | EAdverb (av,EVerb VPipe) -> vpipe_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VPipe)) -> vpipe_av_mm av
    | EVerb VAmpersand -> vampersand_m
    | EAdverb (av,EVerb VAmpersand) -> vampersand_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VAmpersand)) -> vampersand_av_mm av
    | EVerb VCircumflex -> vcircumflex_m
    | EAdverb (av,EVerb VCircumflex) -> vcircumflex_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VCircumflex)) -> vcircumflex_av_mm av
    | EVerb VLangle -> vlangle_m
    | EAdverb (av,EVerb VLangle) -> vlangle_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VLangle)) -> vlangle_av_mm av
    | EVerb VRangle -> vrangle_m
    | EAdverb (av,EVerb VRangle) -> vrangle_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VRangle)) -> vrangle_av_mm av
    | EVerb VEquals -> vequals_m
    | EAdverb (av,EVerb VEquals) -> vequals_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VEquals)) -> vequals_av_mm av
    | EVerb VPound -> vpound_m
    | EAdverb (av,EVerb VPound) -> vpound_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VPound)) -> vpound_av_mm av
    | EVerb VLodash -> vlodash_m
    | EAdverb (av,EVerb VLodash) -> vlodash_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VLodash)) -> vlodash_av_mm av
    | EVerb VTilde -> vtilde_m
    | EAdverb (av,EVerb VTilde) -> vtilde_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VTilde)) -> vtilde_av_mm av
    | EVerb VDollar -> vdollar_m
    | EAdverb (av,EVerb VDollar) -> vdollar_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VDollar)) -> vdollar_av_mm av
    | EVerb VQuestion -> vquestion_m
    | EAdverb (av,EVerb VQuestion) -> vquestion_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VQuestion)) -> vquestion_av_mm av
    | EVerb VAt -> vat_m
    | EAdverb (av,EVerb VAt) -> vat_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VAt)) -> vat_av_mm av
    | EVerb VDot -> vdot_m
    | EAdverb (av,EVerb VDot) -> vdot_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VDot)) -> vdot_av_mm av
    | EVerb VComma -> vcomma_m
    | EAdverb (av,EVerb VComma) -> vcomma_av_md av
    | EAdverb (av,EAdverb(AVColon,EVerb VComma)) -> vcomma_av_mm av
    | EAdverb (av,EId id) -> let KFunction f = e (EId id) in em (EAdverb(av,EFunction f)) (* FIXME *)
    | EAdverb (av,EFunction (F1 f)) -> av_mm av (em (EFunction (F1 f))) (* FIXME *)
    | EAdverb (av,EFunction (F2 f)) -> av_md av (ed (EFunction (F2 f))) (* FIXME *)
    | EAdverb (av,e) -> av_mm av (em e)
    | _ -> raise Not_implemented)
   | _ -> raise Not_implemented
and e _e = match _e with
    | EAppD (x,f,y) -> let x = e x in let y = e y in ed f x y
    | EAppM (f,x) -> let x = e x in em f x
    | EId id -> eid id
    | EAssign (v,x) -> let x = e x in eassign v x
    | ESymbol s -> KSymbol s
    | EList es -> KList (Array.map es ~f:e)
    | EIntegerArray a -> KIntegerArray a
    | EFloatArray a -> KFloatArray a
    | ESymbolArray a -> KSymbolArray a
    | ECharArray a -> KCharArray a
    | EInteger a -> KInteger a
    | EFloat a -> KFloat a
    | EChar a -> KChar a
    | EVerb _ | EAdverb _ -> KFunction (F _e)
    | EFunction f -> KFunction f
    | ENull -> KNull
and ex _e x' = match _e with
    | EId id when id = IdRelative[Symbol.S 1] (*arg_x*) -> x'
    | EAppD (x,f,y) -> let x = ex x x' in let y = ex y x' in ed f x y
    | EAppM (f,x) -> let x = ex x x' in em f x
    | EAssign (v,x) -> let x = ex x x' in eassign v x
    | EList es -> KList (Array.map es ~f:(fun x -> ex x x'))
    | _ -> e _e
and exy _e x' y' = match _e with
    | EId id when id = IdRelative[Symbol.S 1] (*arg_x*) -> x'
    | EId id when id = IdRelative[Symbol.S 2] (*arg_y*) -> y'
    | EAppD (x,f,y) -> let x = exy x x' y' in let y = exy y x' y' in ed f x y
    | EAppM (f,x) -> let x = exy x x' y' in em f x
    | EAssign (v,x) -> let x = exy x x' y' in eassign v x
    | EList es -> KList (Array.map es ~f:(fun x -> exy x x' y'))
    | _ -> e _e

(* parsing k. still very sketchy.
  > step 1: make it work.
    step 2: make it short.
    step 3: make it fast. *)
type tk = TkNum | TkAlpha | TkVerb | TkSpace | TkBracketO | TkBracketC | TkBraceO | TkBraceC | TkParenO | TkParenC | TkColon | TkLodash | TkForwardslash | TkBackslash | TkSquote | TkDquote | TkBquote | TkOther | TkDot | TkSemicolon with sexp
type tks = (tk * char list) array with sexp
let tk = function
  |'a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
  |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'->TkAlpha
  |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'->TkNum
  |','|'+'|'-'|'*'|'%'|'|'|'&'|'^'|'<'|'>'|'='|'!'|'#'|'~'|'$'|'?'|'@'->TkVerb
  |':'->TkColon          |';'->TkSemicolon    |'.'->TkDot     |'_'->TkLodash  |'/'->TkForwardslash| '\\'->TkBackslash
  |'''->TkSquote         |'"'->TkDquote       |'`'->TkBquote
  |'[' ->TkBracketO      |']'->TkBracketC     |'{'->TkBraceO  |'}'->TkBraceC  |'(' ->TkParenO |')'->TkParenC
  |' '|'\n'|'\t'->TkSpace| _->TkOther
let tokenize s = String.fold s ~init:(TkSpace,[],[]) ~f:(fun (s,xs,x) c -> let t = tk c in match s,t,x with
  | TkSpace, TkSpace , _     -> (s,xs,c::x)
  | TkSpace, _       , _     -> (t,(TkSpace,x)::xs,[c])
  | TkAlpha, TkAlpha , _
  | TkAlpha, TkNum   , _     -> (s,xs,c::x)
  | TkAlpha, TkDot   , _     -> (s,xs,c::x)
  | TkAlpha, TkLodash, _     -> (s,xs,c::x)
  | TkAlpha, _       , _     -> (t,(TkAlpha,x)::xs,[c])
  | TkNum,  TkDot    , _
  | TkNum,  TkNum    , _     -> (s,xs,c::x)
  | TkVerb, TkNum    , ['-'] -> (TkNum,xs,[c;'-'])
  | _                        -> (t,(s,x)::xs,[c]))
  |> fun (s,xs,x) -> (s,x)::xs
  |> Array.of_list_rev_map ~f:(fun (s,x) -> (s,List.rev x))

let rec nvars e = match e with
  | EId v when v = arg_x -> 1
  | EId v when v = arg_y -> 2
  | EId _ -> 0
  | EAdverb (_,x) -> nvars x
  | EReturn x -> nvars x
  | EAppD(x,f,y) -> Int.max (nvars x) (Int.max (nvars f) (nvars y))
  | EAppM(f,x) -> Int.max (nvars f) (nvars x)
  | EAssign(v,x) -> Int.max (nvars (EId v)) (nvars x)
  | EList x -> map x nvars |> Array.max_elt ~cmp:Int.compare |> Option.value ~default:0
  | ESymbol _ -> 0|EIntegerArray _->0|EFloatArray _->0|ESymbolArray _->0|ECharArray _->0|EInteger _->0|EFloat _->0|EChar _->0|EVerb _->0|ENull->0
let lookahead a i = try Some(a.(i)) with _ -> None
let parse_verb = function |'+'->VPlus|'-'->VMinus|'*'->VStar|'!'->VExclaim|'%'->VPercent|'|'->VPipe|'&'->VAmpersand|'^'->VCircumflex|'<'->VLangle|'>'->VRangle|'='->VEquals|'#'->VPound|'_'->VLodash|'~'->VTilde|'$'->VDollar|'?'->VQuestion|'@'->VAt|'.'->VDot|','->VComma|_-> raise (Invalid_argument "verb")
let parse_id_body s = String.of_char_list s |> String.split ~on:'.' |> List.map ~f:(fun s -> let s = Symbol.make s in h s (IdRelative [s]); s)
let parse_id s = match s with
  | '.'::s -> IdAbsolute (parse_id_body s)
  | _ -> IdRelative (parse_id_body s)
let parse_symbol ss = let s = Symbol.make (String.of_char_list ss) in let id = parse_id ss in h s id; s
let append_earray xs x  = match xs,x with
  | EIntegerArray k, EInteger l -> EIntegerArray (Array.append k [|l|])
  | EIntegerArray k, EFloat l   -> EFloatArray (Array.append (map k Float.of_int) [|l|])
  | EFloatArray k,   EInteger l -> EFloatArray (Array.append k [|Float.of_int l|])
  | EFloatArray k,   EFloat l   -> EFloatArray (Array.append k [|l|])
let rec parse_adverb_composition e t i = match lookahead t i, lookahead t (i+1) with
  | Some (TkBackslash,_),    Some(TkColon,_) -> parse_adverb_composition (EAdverb(AVBackslashColon,e)) t (i+2)
  | Some (TkBackslash,_),    _               -> parse_adverb_composition (EAdverb(AVBackslash,e)) t (i+1)
  | Some (TkForwardslash,_), Some(TkColon,_) -> parse_adverb_composition (EAdverb(AVForwardslashColon,e)) t (i+2)
  | Some (TkForwardslash,_), _               -> parse_adverb_composition (EAdverb(AVForwardslash,e)) t (i+1)
  | Some (TkSquote,_),       Some(TkColon,_) -> parse_adverb_composition (EAdverb(AVQuoteColon,e)) t (i+2)
  | Some (TkSquote,_),       _               -> parse_adverb_composition (EAdverb(AVQuote,e)) t (i+1)
  | Some (TkColon,_),        _               -> parse_adverb_composition (EAdverb(AVColon,e)) t (i+1)
  | Some _,                  _               -> i,e
  | None,                    _               -> i,e
exception Parse_exn of (e option * ((tk * char list) option) * ((tk * char list) option)) with sexp
let rec parse_string t i = let rec loop j acc =
    match lookahead t j,acc with
    | Some (TkDquote,_), [c] -> j+1,EChar c
    | Some (TkDquote,_), cs  -> j+1,ECharArray (Array.of_list_rev cs)
    | Some (_,cs),       _   -> loop (j+1) ((List.rev cs)@acc)
    | None,              _   -> raise KError_syntax
  in loop i []
and parse_nested o c t i =
  let rec loop j p =
    if p = 0 then j,(sub t i (j-i-1))
    else match lookahead t j with
    | Some (c',_) when c=c' -> loop (j+1) (p-1)
    | Some (o',_) when o=o' -> loop (j+1) (p+1)
    | Some _                -> loop (j+1) p
    | None                  -> raise KError_syntax
  in loop i 1
and parse_list t i =
  let rec loop acc last j p =
    match p,lookahead t j,last with
    | _,Some (TkParenO,_)   , _      -> loop acc last (j+1) (p+1)
    | _,Some (TkParenC,_)   , _      -> loop acc last (j+1) (p-1)
    | 0,None,                 None   -> parse_exp None (sub t i (j-i)) 0
    | 0,None,                 Some k -> let acc = (parse_exp None (sub t (k+1) (j-k-1)) 0)::acc in EList (Array.of_list_rev acc)
    | 0,Some (TkSemicolon,_), None   -> loop ((parse_exp None (sub t 0 j) 0)::acc) (Some j) (j+1) p
    | 0,Some (TkSemicolon,_), Some k -> loop ((parse_exp None (sub t (k+1) (j-k-1)) 0)::acc) (Some j) (j+1) p
    | _,Some _, _                    -> loop acc last (j+1) p
  in loop [] None i 0
and parse_args t i =
  let j,t = parse_nested TkBracketO TkBracketC t i in
  let rec loop acc last j p =
    match p,lookahead t j,last with
    | _,Some (TkBracketO,_)   , _    -> loop acc last (j+1) (p+1)
    | _,Some (TkBracketC,_)   , _    -> loop acc last (j+1) (p-1)
    | 0,None,                 None   -> [parse_exp None (sub t 0 (j)) 0]
    | 0,None,                 Some k -> let acc = (parse_exp None (sub t (k+1) (j-k-1)) 0)::acc in List.rev acc
    | 0,Some (TkSemicolon,_), None   -> loop ((parse_exp None (sub t 0 j) 0)::acc) (Some j) (j+1) p
    | 0,Some (TkSemicolon,_), Some k -> loop ((parse_exp None (sub t (k+1) (j-k-1)) 0)::acc) (Some j) (j+1) p
    | _,Some _, _                    -> loop acc last (j+1) p
  in j,loop [] None 0 0
and parse_paren t i = let j,a = parse_nested TkParenO TkParenC t i in j,parse_list a 0
and parse_num t = let s = String.of_char_list t in try EInteger (Int.of_string s) with _ -> EFloat (Float.of_string s)
and parse_fun t i = let j,t = parse_nested TkBraceO TkBraceC t i in let e = parse_exp None t 0 in match nvars e with
  | 1 -> j, F1 e | 2 -> j, F2 e | _ -> raise Not_implemented
and parse_exp e t i : e =
  match e,lookahead t i,lookahead t (i+1) with
  | None,                 Some(TkSpace,_),       Some (TkForwardslash,_)
  | None,                 None,                  None                    -> ENull
  | Some e,               Some(TkSpace,_),       Some (TkForwardslash,_)
  | Some e,               None,                  None                    -> e
  | None,                 Some(TkBraceO,_),      _                       -> let i,f = parse_fun t (i+1) in parse_exp (Some (EFunction f)) t i
  | Some e,               Some(TkBracketO,_),    _                       -> let j, a = parse_args t (i+1) in
                                                                            parse_exp (Some (match a with [x] -> EAppM(e,x) | [x;y] -> EAppD(x,e,y))) t (j+1)
  | Some (EId v),         Some(TkColon,_),       Some (_)                -> let e = parse_exp None t (i+1) in EAssign(v, e)
  | None,                 Some(TkAlpha,s),       _                       -> parse_exp (Some (EId (parse_id s))) t (i+1)
  | None,                 Some(TkBquote,_),      Some (TkAlpha,s)        -> parse_exp (Some (ESymbol (parse_symbol s))) t (i+2)
  | None,                 Some(TkBquote,_),      Some (TkDquote,_)       -> raise Not_implemented
  | None,                 Some(TkBquote,_),      Some (TkSpace,_)
  | None,                 Some(TkBquote,_),      None                    -> parse_exp (Some (ESymbol root)) t (i+1)
  | None,                 Some(TkParenO,_),      Some (TkParenC,_)       -> parse_exp (Some (EList [||])) t (i+2)
  | None,                 Some(TkParenO,_),      _                       -> let i,e = parse_paren t (i+1) in parse_exp (Some e) t i
  | None,                 Some(TkDquote,_),      _                       -> let i,e = parse_string t (i+1) in parse_exp (Some e) t i
  | Some e,               Some(TkAlpha,s),       _                       -> let i,f = parse_adverb_composition (EId (parse_id s)) t (i+1) in
                                                                            EAppD(e,f,parse_exp None t i)
  | Some e,               Some(TkVerb,[c]),      _                       -> let i,f = parse_adverb_composition (EVerb (parse_verb c)) t (i+1) in
                                                                            EAppD(e,f,parse_exp None t i)
  | Some e,               Some(TkVerb,[c]),      _                       -> EAppD(e,EVerb (parse_verb c),parse_exp None t (i+1))
  | Some e,               Some(TkDot,_) ,        _                       -> EAppD(e,EVerb VDot,parse_exp None t (i+1))
  | Some e,               Some(TkLodash,_) ,     _                       -> let i,f = parse_adverb_composition (EVerb VLodash) t (i+1) in
                                                                            EAppD(e,f,parse_exp None t i)
  | None,                 Some(TkVerb,[c]),      _                       -> let i,f = parse_adverb_composition (EVerb (parse_verb c)) t (i+1) in
                                                                            (match lookahead t i with None -> f | _ -> EAppM(f,parse_exp None t i))
  | None,                 Some(TkDot,_),         _                       -> let i,f = parse_adverb_composition (EVerb VDot) t (i+1) in
                                                                            (match lookahead t i with None -> f | _ -> EAppM(f,parse_exp None t i))
  | None,                 Some(TkLodash,_),      _                       -> let i,f = parse_adverb_composition (EVerb VLodash) t (i+1) in
                                                                            (match lookahead t i with None -> f | _ -> EAppM(f,parse_exp None t i))
  | Some (EId v),         Some(TkSpace,_),       _                       -> let i,f = parse_adverb_composition (EId v) t (i+1) in
                                                                            (match lookahead t i with None -> f | _ -> EAppM(f,parse_exp None t i))
  | Some e,               Some(TkBackslash,_),   None
  | Some e,               Some(TkForwardslash,_),None
  | Some e,               Some(TkSquote,_),      None
  | Some e,               Some(TkColon,_),       None                    -> let i,f = parse_adverb_composition e t i in parse_exp (Some f) t i
  | Some e,               Some(TkBackslash,_),   _
  | Some e,               Some(TkForwardslash,_),_
  | Some e,               Some(TkSquote,_),      _
  | Some e,               Some(TkColon,_),       _                       -> let i,f = parse_adverb_composition e t i in
                                                                            (match lookahead t i with None -> f | _ -> EAppM(f,parse_exp None t i))
  | None,                 Some(TkNum,num),       _                       -> parse_exp (Some (parse_num num)) t (i+1)
  | Some(ESymbol k),      Some(TkBquote,_),      Some(TkAlpha, s)        -> parse_exp (Some (ESymbolArray [|k;parse_symbol s|])) t (i+2)
  | Some(ESymbol k),      Some(TkSpace,_),       Some(TkBquote,_)        -> parse_exp (Some (ESymbolArray [|k|])) t (i+1)
  | Some(ESymbolArray k), Some(TkBquote,_),      Some(TkAlpha, s)        -> parse_exp (Some (ESymbolArray (Array.append k [|parse_symbol s|]))) t (i+2)
  | Some(EInteger k),     Some(TkSpace,_),       Some(TkNum,num)         -> parse_exp (Some (append_earray (EIntegerArray [|k|]) (parse_num num))) t (i+2)
  | Some(EFloat k),       Some(TkSpace,_),       Some(TkNum,num)         -> parse_exp (Some (append_earray (EFloatArray [|k|]) (parse_num num))) t (i+2)
  | Some(EIntegerArray k),Some(TkSpace,_),       Some(TkNum,num)         -> parse_exp (Some (append_earray (EIntegerArray k) (parse_num num))) t (i+2)
  | Some(EFloatArray k),  Some(TkSpace,_),       Some(TkNum,num)         -> parse_exp (Some (append_earray (EFloatArray k) (parse_num num))) t (i+2)
  | e,                    Some(TkSpace,_),       _                       -> parse_exp e t (i+1)
  | a,                    b,                     c                       -> raise (Parse_exn (a,b,c))


let i1 x = (printf "EVAL %s\n" (Sexp.to_string_hum (sexp_of_e x)); printf "%s\n\n" (Sexp.to_string_hum (sexp_of_k (e x))); flush_all())
let i () =
    let print_expr e = printf "%s\n" (Sexp.to_string_hum (sexp_of_e e)) in
    let print_tks tks =  () in (* printf "%s\n" (Sexp.to_string_hum @@ sexp_of_tks tks) in *)
    let rec loop () = printf "k) ";flush_all ();match In_channel.input_line ~fix_win_eol:true stdin with
    | Some s -> (
                  (* try  *)
                    let tks = tokenize s in print_tks tks; let e = parse_exp None tks 0 in i1 e
                 (* with e -> printf "'error \"%s\"\n" (Sexp.to_string_hum (sexp_of_exn e)) *)
                 );
                loop ();
    | None -> ()
  in loop ()

;; i () ;;