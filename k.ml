(* preliminaries & ast ===================================================== *)
type s = int (* symbols *)

type h =  (* handles *)
  | HRel of s list (* x.y.z *)
  | HAbs of s list (* .x.y.z *)

module H = Hashtbl.Make(struct type t = s let equal x y = x=y and hash x = x end) (* symbol-keyed hash table *)

type v =  (* verbs. (TODO?:semantic names) *)
  | VPlus       (*   +   *)
  | VMinus      (*   -   *)
  | VStar       (*   *   *)
  | VExclaim    (*   !   *)
  | VPercent    (*   %   *)
  | VPipe       (*   |   *)
  | VAmpersand  (*   &   *)
  | VCircumflex (*   ^   *)
  | VLangle     (*   <   *)
  | VRangle     (*   >   *)
  | VEquals     (*   =   *)
  | VPound      (*   #   *)
  | VLodash     (*   _   *)
  | VTilde      (*   ~   *)
  | VDollar     (*   $   *)
  | VQuestion   (*   ?   *)
  | VAt         (*   @   *)
  | VDot        (*   .   *)
  | VComma      (*   ,   *)
  | VZeroColon  (*   0:  *)
  | VOneColon   (*   1:  *)
  | VTwoColon   (*   2:  *)
  | VThreeColon (*   3:  *)
  | VFourColon  (*   4:  *)
  | VFiveColon  (*   5:  *)

type av = (* adverbs *)
  | AVForwardslash | AVForwardslashColon
  | AVBackslash    | AVBackslashColon
  | AVQuote        | AVQuoteColon

type f = (* function values (PERF?: optimized form for partially-applied functions, eg FNaryp(n,is,a,f)) *)
  | FNilad of (unit -> k)
  | FMonad of (k -> k)
  | FMonadDyad of (k -> k)*(k -> k -> k)
  | FMonadDyadTriad of (k -> k)*(k -> k -> k)*(k -> k -> k -> k)
  | FMonadDyadTriadTetrad of (k -> k)*(k -> k -> k)*(k -> k -> k -> k)*(k -> k -> k -> k -> k)
  | FDyad of (k -> k -> k)
  | FTriad of (k -> k -> k -> k)
  | FNary of int * (k array -> k) (* n>=4 *)

and ea = (* arguments (ast) (NOTE/PERF: is it worth it to treat n<=3 separately?) *)
  | Ea0
  | Ea1 of e
  | Ea2 of e * e
  | Ea3 of e * e * e
  | Ea of e array (* inv:n>=4 *)

and ka = (* arguments (values) *)
  | Ka0
  | Ka1 of k
  | Ka2 of k * k
  | Ka3 of k * k * k
  | Ka of k array (* inv:n>=4 *)
  | Kap of int*k array*int array*int array (* inv. Kap(n,ks,is,js) => |ks|=|is| /\ |is|+|js| = n /\ disjoint(set(is),set(js)) /\ sorted(is) /\ sorted(js) *)

and e = (* expressions *)
  | ENil (* empty expression, as in (;). distinct from _n, e.g. ,[_n;2] is application, ,[;2] is partial application *)
  | EColon (* assignment in verb form *)
  | ELambda of s array * e (* {[x1;x2;...;xN] e} *)
  | EApp of e*ea
  | EList of e list
  | EAdverb of av*e
  | EReturn of e (* :e *)
  | ESeq of e*e (* e;e' *)
  | EIfSimple of e*e*e (* :[i;t;e] *)
  | EIfMulti of e array * e array * e (* :[i1;t1;i2;t2;...;iN;tN;e] *)
  | EAssign of h*e (* x : e *)
  | EAssignMonad of h*e (* x f: *)
  | EAssignDyad of h*e*e (* x f: y*)
  | EAssignGlobal of h*e (* x :: e  *)
  | EAssignIndex of h*e array*e (* x[i1;...;iN] : e *)
  | EAssignIndexMonad of h*e array*e (* x[i1;...;iN] f: *)
  | EAssignIndexDyad of h*e array*e*e (* x[i1;...;iN] f: y *)
  | EName of h
  | ENameSys of s (* _in, _draw,... *)
  | EVerb of v
  | EVerbMonadic of v (* v: *)
  | EComp of e*e (* e e' (composition) *)
  | ELiteral of k

and k = (* values *)
  | KNil
  | KList of k array
  | KDictionary of d
  | KFunction of f (* PERF?: fold [type f] into [type k], saves one unboxing step *)
  | KInteger of int   | KIntegerArray of int array
  | KFloat of float   | KFloatArray of float array
  | KChar of char     | KCharArray of char array (* PERF *)
  | KSymbol of s      | KSymbolArray of s array
  | KSSymbol of string| KSSymbolArray of string array | KSDictionary of (string*k*k) array (* serialization-proof forms *)

and d = (* dictionaries *)
  de H.t
and de = (* dictionary entries *)
  { value:k; attr:attr }
and attr = (* dictionary entry attributes *)
  | ANil
  | ADict of d

type c = (* command *)
  | CEval of e               (* (expr) *)
  | CExit                    (* \\ *)
  | CLoad of string          (* \l *)
  | CCd of h                 (* \d x *)
  | CPwd                     (* \d *)
  | CWsSave of string option (* \save *)
  | CWsLoad of string option (* \load *)
  | CWsSize                  (* \w *)

module Hk = Hashtbl.Make(struct type t = k let equal x y = x=y and hash = Hashtbl.hash end)
module Hf = Hashtbl.Make(struct type t = float let equal x y = x=y and hash = Hashtbl.hash end)

let is_atom = function | KInteger _ | KFloat _ | KSymbol _ | KChar _ | KNil | KFunction _ -> true | _ -> false
[@@inline always] let kinteger x = KInteger x
[@@inline always] let kfloat x = KFloat x
[@@inline always] let kchar x = KChar x
[@@inline always] let ksymbol x = KSymbol x
[@@inline always] let kintegerarray x = KIntegerArray x
[@@inline always] let kfloatarray x = KFloatArray x
[@@inline always] let kchararray x = KCharArray x
[@@inline always] let ksymbolarray x = KSymbolArray x
[@@inline always] let klist x = KList x
[@@inline always] let kdictionary x = KDictionary x
[@@inline always] let elambda x y = ELambda(x,y)
[@@inline always] let eapp x y = EApp(x,y)
[@@inline always] let eadverb x y = EAdverb(x,y)
[@@inline always] let eseq x y = ESeq(x,y)
[@@inline always] let eassign x y = EAssign(x,y)
[@@inline always] let eassignglobal x y = EAssignGlobal(x,y)
[@@inline always] let eassignmonad x y = EAssignMonad(x,y)
[@@inline always] let eassigndyad x y z = EAssignDyad(x,y,z)
[@@inline always] let eassignindex x y z = EAssignIndex(x,y,z)
[@@inline always] let eassignindexmonad x y z = EAssignIndexMonad(x,y,z)
[@@inline always] let eassignindexdyad x y z u = EAssignIndexDyad(x,y,z,u)
[@@inline always] let eifsimple x y z = EIfSimple(x,y,z)
[@@inline always] let eifmulti x y z = EIfMulti(x,y,z)
[@@inline always] let elist x = EList x
[@@inline always] let ereturn x = EReturn x
[@@inline always] let ename x = EName x
[@@inline always] let enamesys x = ENameSys x
[@@inline always] let everb x = EVerb x
[@@inline always] let ecomp x y = EComp(x,y)
[@@inline always] let everbmonadic x = EVerbMonadic x
[@@inline always] let eliteral x = ELiteral x
[@@inline always] let ea1 x = Ea1 x
[@@inline always] let ea2 x y = Ea2 (x,y)
[@@inline always] let ea3 x y z = Ea3 (x,y,z)
[@@inline always] let ea x = Ea x
let ceval x = CEval x
let cload x = CLoad x
let cwssave x = CWsSave x
let cwsload x = CWsLoad x
let ccd x = CCd x

let ensure_suffix s f = if Filename.check_suffix f s then f else f^s

exception Not_implemented_attribute
exception Not_implemented_format
exception Not_implemented_builtins
exception Not_implemented_io
exception Not_implemented_dynlink
exception Not_implemented_apply

exception Return of k
exception KReturn of k
exception KExit

exception KError_length
exception KError_index
exception KError_valence
exception KError_type
exception KError_domain
exception KError_rank
exception KError_limit
exception KError_nonce
exception KError_unmatched
let kinteger_prj = function KInteger x->x|_->raise KError_type
let kfloat_prj = function KFloat x->x|_->raise KError_type
and kchar_prj = function KChar x->x|_->raise KError_type
and ksymbol_prj = function KSymbol x->x|_->raise KError_type
and kdictionary_prj = function KDictionary x->x|_->raise KError_type

[@@inline always] let len = Array.length
[@@inline always] let id x = x
[@@inline always] let const x _ = x

let partial_app_dyad f ks is = KFunction (if len is = 0 then FDyad f else let x = ks.(0) in FMonad (if is.(0) = 0 then f x else (fun y -> f y x)))
let partial_app_triad f ks is = KFunction (match is with
  | [|0;1|] -> let x=ks.(0) and y=ks.(1) in FMonad (f x y)
  | [|0;2|] -> let x=ks.(0) and z=ks.(1) in FMonad (fun y -> f x y z)
  | [|1;2|] -> let y=ks.(0) and z=ks.(1) in FMonad (fun x -> f x y z)
  | [|0|]   -> let x=ks.(0) in FDyad (fun y z -> f x y z)
  | [|1|]   -> let y=ks.(0) in FDyad (fun x z -> f x y z)
  | [|2|]   -> let z=ks.(0) in FDyad (fun x y -> f x y z)
  | [||]    -> FTriad f
  | _       -> assert false)
let partial_app_tetrad f ks is = KFunction (match is with
  | [|0;1;2|] -> let x=ks.(0) and y=ks.(1) and z=ks.(2) in FMonad (f x y z)
  | [|0;1;3|] -> let x=ks.(0) and y=ks.(1) and u=ks.(2) in FMonad (fun z -> f x y z u)
  | [|0;2;3|] -> let x=ks.(0) and z=ks.(1) and u=ks.(2) in FMonad (fun y -> f x y z u)
  | [|1;2;3|] -> let y=ks.(0) and z=ks.(1) and u=ks.(2) in FMonad (fun x -> f x y z u)
  | [|0;1|]   -> let x=ks.(0) and y=ks.(1) in FDyad (fun z u -> f x y z u)
  | [|0;2|]   -> let x=ks.(0) and z=ks.(1) in FDyad (fun y u -> f x y z u)
  | [|0;3|]   -> let x=ks.(0) and u=ks.(1) in FDyad (fun y z -> f x y z u)
  | [|1;2|]   -> let y=ks.(0) and z=ks.(1) in FDyad (fun x u -> f x y z u)
  | [|1;3|]   -> let y=ks.(0) and u=ks.(1) in FDyad (fun x z -> f x y z u)
  | [|2;3|]   -> let z=ks.(0) and u=ks.(1) in FDyad (fun x y -> f x y z u)
  | [|0|]     -> let x=ks.(0) in FTriad (fun y z u -> f x y z u)
  | [|1|]     -> let y=ks.(0) in FTriad (fun x z u -> f x y z u)
  | [|2|]     -> let z=ks.(0) in FTriad (fun x y u -> f x y z u)
  | [|3|]     -> let u=ks.(0) in FTriad (fun x y z -> f x y z u)
  | [||]      -> FNary(4,function [|x;y;z;u|] -> f x y z u|_->assert false)
  | _         -> assert false)
let partial_app_nary f n ks is js = KFunction (
  let m = len is and a = Array.make n KNil in for i = 0 to m-1 do a.(is.(i)) <- ks.(i); done;
  if m=0 then FNary(n,f) else match n-m with
  | 1 -> FMonad (fun x -> a.(js.(0)) <- x; f a)
  | 2 -> FDyad (fun x y -> a.(js.(0)) <- x; a.(js.(1)) <- y; f a)
  | 3 -> FTriad (fun x y z -> a.(js.(0)) <- x; a.(js.(1)) <- y; a.(js.(2)) <- z; f a)
  | p -> FNary(p,fun a' -> for i = 0 to p-1 do a.(js.(i)) <- a'.(i); done; f a))
let partial_app_nary_prefix f n m xs = KFunction (
  let a = Array.make n KNil in for i=0 to m-1 do a.(i) <- xs.(i); done;
  if m=0 then FNary(n,f) else match n-m with
  | 1 -> FMonad(fun x -> a.(n-1)<-x;f a)
  | 2 -> FDyad(fun x y -> a.(n-2)<-x;a.(n-1)<-y;f a)
  | 3 -> FTriad(fun x y z -> a.(n-3)<-x;a.(n-2)<-y;a.(n-1)<-z;f a)
  | p -> FNary(p,fun a' -> for i=0 to p-1; do a.(m+i) <- a'.(i); done;f a))

(* config ================================================================== *)
type config = {
  mutable compare_tolerance : float; (* runtime (mutable) *)
  mutable approx_tolerance : float;
  mutable hash_size : int;
  mutable workspace_name : string;
  local_env_hash_size : int;         (* static            *)
  approx_iter : int;
}
let config = {
  compare_tolerance = epsilon_float;
  approx_tolerance = 1e-6;
  hash_size = 128;
  workspace_name = "ok_workspace";
  local_env_hash_size = 5;
  approx_iter = 20;
}

(* symbol table ============================================================ *)
module St = Hashtbl.Make(struct type t = string let equal x y = x=y and hash x = Hashtbl.hash x end)
let _S : s St.t = St.create config.hash_size (* string -> symbol *)
let _Srev : string H.t = H.create config.hash_size (* symbol -> string *)
let _Sh : h H.t = H.create config.hash_size (* symbol -> handle *)
let _Smax = ref (-1)
let s x h = if St.mem _S x then St.find _S x else (
  incr _Smax; let s = !_Smax in St.add _S x s; H.replace _Srev s x;
  (match h with None -> H.replace _Sh s (HRel [s]) | Some h -> H.replace _Sh s h);s)
let sname = H.find _Srev
let handle = H.find _Sh
let handle_abs s = match handle s with HAbs h -> h | _ -> raise Not_found
(* built-ins *)
let s0 = s "" (Some (HAbs [])) and s0r = s "" (Some (HRel [])) and sx = s "x" None and sy = s "y" None and sz = s "z" None
and s_in = s "_in" None and s_lin = s "_lin" None and s_n = s "_n" None and s_d = s "_d" None and s_log = s "_log" None
and s_exp = s "_exp" None and s_sin = s "_sin" None and s_sinh = s "_sinh" None and s_cos = s "_cos" None and s_cosh = s "_cosh" None
and s_tan = s "_tan" None and s_tanh = s "_tanh" None and s_sqrt = s "_sqrt" None and s_sqr = s "_sqr" None and s_ic = s "_ic" None
and s_ci = s "_ci" None and s_mul = s "_mul" None and s_dot = s "_dot" None and s_pretty = s "_pretty" None

(* dict utils ============================================================== *)
let dmake n = H.create n
let dget_exn d s = H.find d s
let dgetv_or_nil d s = try (dget_exn d s).value with Not_found -> KNil
let dget d s = if H.mem d s then Some (dget_exn d s) else None
let dset d s v = H.replace d s v
let dsetv d s value = let attr = if H.mem d s then (H.find d s).attr else ANil in dset d s {value;attr}
let dmapv_inplace d f = H.iter (fun k {value;attr} -> dset d k {value=f value;attr}) d
let dcopy = H.copy
let rec dsetl d ss v = match ss with
  | [] -> raise KError_domain
  | [s] -> dset d s v
  | s::ss -> (match dget d s with
    | Some {value=KDictionary d;_} -> dsetl d ss v
    | None ->
      let d' = dmake config.hash_size in
      dset d s {value=KDictionary d';attr=ANil};
      dsetl d' ss v
    | _ -> raise KError_type)
let rec dgetl_exn d ss = match ss with
  | [] -> KDictionary d
  | [s] -> (dget_exn d s).value
  | s::ss -> (match dget_exn d s with {value=KDictionary d;_} -> dgetl_exn d ss |_ -> raise KError_type)
let dmakel xs =
  let n = len xs in let d = dmake n in
  Array.iter (function
    | KList [|KSymbol s;value;KNil|]
    | KList [|KSymbol s;value|] -> dset d s {value;attr=ANil}
    | KList [|KSymbol s;value;KDictionary attr|] -> dset d s {value;attr=ADict attr}
    | KList _ -> raise KError_type
    | _ -> raise KError_rank) xs;
  d
let dkeys d =
  let n = H.length d in
  let a = Array.make n s0 in
  let i = ref 0 in H.iter (fun k _ -> a.(!i)<-k;incr i) d;
  a
let dvalues d =
  let n = H.length d in
  let a = Array.make n KNil in
  let i = ref 0 in H.iter (fun k v -> a.(!i) <- KList [|KSymbol k;v.value;match v.attr with ANil->KNil|ADict d->KDictionary d|];incr i) d;
  a

(* k-tree ================================================================== *)
let ktree : d ref = ref(dmake config.hash_size)
let ktree_pwd : d ref = ref (dmake config.hash_size)
let s_k = s "k" None let _ = dsetv (!ktree) s_k (KDictionary(!ktree_pwd))
let ktree_env : d list ref = ref [!ktree_pwd]
let ktree_pwdh : s list ref = ref [s_k]
let ktree_set_pwdh h = ktree_pwdh:=(match h with HRel h -> !ktree_pwdh@h | HAbs h -> h)
[@@inline always] let ktree_cd d = ktree_env:=(match !ktree_env with h::t -> d::t|[]->[d])
[@@inline always] let ktree_in d f = let p= !ktree_env in ktree_env:=d; let k = try f() with e -> (ktree_env:=p; raise e) in ktree_env:=p;k
let kgetl_abs_exn h = dgetl_exn !ktree h
let kgetl_rel_exn h =
  let rec loop = function
    [] -> kgetl_abs_exn h | d::ds -> (try dgetl_exn d h with Not_found -> loop ds)
  in loop !ktree_env
let kgeth_exn = function HAbs h -> kgetl_abs_exn h | HRel h -> kgetl_rel_exn h
let kgeth_or_nil h = try kgeth_exn h with Not_found -> KNil
let kgets_exn s = match handle s with HAbs h -> kgetl_abs_exn h | HRel h -> dgetl_exn !ktree_pwd h
let ksetl_abs h = dsetl !ktree h
let ksetl_rel h v = dsetl (List.hd !ktree_env) h v
let kseth h v = match h with HAbs h -> ksetl_abs h v | HRel h -> ksetl_rel h v
let ksethv h value = kseth h {value;attr=ANil}
let ksethv_ret h v = ksethv h v; v
let ksets s v = match handle s with HAbs h -> ksetl_abs h v | HRel h -> dsetl !ktree_pwd h v
let ksetsv s value = ksets s {value;attr=ANil}
let ksetsv_ret s v = ksetsv s v; v

(* pretty-printing (ugly code) ============================================= *)
let fpf = Format.fprintf
let fps : (Format.formatter -> unit) -> bytes  =
  let buffer = Buffer.create 80 in
  let formatter = Format.formatter_of_buffer buffer in
  (fun f ->
    f formatter; Format.pp_print_flush formatter ();
    let bytes = Buffer.to_bytes buffer in Buffer.clear buffer;
    bytes)
let pp_sep f ~sep g a =
  let n = len a in if n > 0 then for i = 0 to n-1 do
    g f a.(i); if i < n-1 then fpf f sep;
  done
let aall p xs =
  let n = len xs in
  try for i = 0 to n-1 do if not (p xs.(i)) then raise (Return KNil) done; true
  with Return _ -> false
let is_lowercase t = 'a'<=t&&t<='z' and is_uppercase t = 'A'<=t&&t<='Z' and is_digit t = '0'<=t&&t<='9'
let is_alpha t = is_lowercase t || is_uppercase t let is_alphanum t = is_alpha t || is_digit t
let sn_escape s = let n = String.length s in try (for i=0 to n-1 do if not (is_alphanum s.[i]||s.[i]='_'||s.[i]='.') then raise Exit;done;s) with Exit -> "\""^s^"\""
let pp_s f s = fpf f "@[`%s@]" (sn_escape (sname s))
let pp_sn f s = fpf f "@[%s@]" (sn_escape (sname s))
let pp_a f g a = fpf f "@[%a@]" (fun f -> pp_sep f ~sep:" " g) a
let pp_ca f a = fpf f "@[\""; Array.iter (fun c -> fpf f "%s" (Char.escaped c)) a; fpf f "\"@]"
let rec pp_k f = function
  | KNil -> ()
  | KList [|k|] -> fpf f "@[,%a@]" pp_k k
  | KList ks -> if aall is_atom ks then fpf f "@[(%a)@]" (fun f -> pp_sep f ~sep:";" pp_k) ks
                else fpf f "@[(%a)@]" (fun f -> pp_sep f ~sep:"@\n " pp_k) ks
  | KDictionary d -> fpf f "@[.%a@]" pp_k (KList(dvalues d))
  | KFunction (FNilad _) -> fpf f "(fun/0)"
  | KFunction (FMonad _) -> fpf f "(fun/1)"
  | KFunction (FMonadDyad _) -> fpf f "(fun/1,2)"
  | KFunction (FMonadDyadTriad _) -> fpf f "(fun/1,2,3)"
  | KFunction (FMonadDyadTriadTetrad _) -> fpf f "(fun/1,2,3,4)"
  | KFunction (FDyad _) -> fpf f "(fun/2)"
  | KFunction (FTriad _) -> fpf f "(fun/3)"
  | KFunction (FNary (n,_)) -> fpf f "(fun/%d)" n
  | KInteger i -> fpf f "%d" i
  | KIntegerArray [||] -> fpf f "!0"
  | KIntegerArray [|i|] -> fpf f ",%d" i
  | KIntegerArray a -> pp_a f (fun f -> fpf f "%d") a
  | KFloat x -> Format.pp_print_float f x
  | KFloatArray [|x|] -> fpf f ",%a" Format.pp_print_float x
  | KFloatArray a -> pp_a f Format.pp_print_float a
  | KChar c -> fpf f "\"%s\"" (Char.escaped c)
  | KCharArray a -> pp_ca f a
  | KSymbol s -> pp_s f s
  | KSymbolArray [||] -> fpf f "0#`"
  | KSymbolArray [|s|] -> fpf f ","; pp_s f s
  | KSymbolArray a -> pp_a f pp_s a
and pp_de f = function
  | KList [|k;v|] -> fpf f "@[(%a;%a)@]" pp_k k pp_k v
  | KList [|k;v;a|] -> fpf f "@[(%a;%a;%a)@]" pp_k k pp_k v pp_k a
  | _ -> assert false
let rec pp_h f = function
| HRel ss -> pp_sep f ~sep:"." pp_sn (Array.of_list ss)
| HAbs ss -> fpf f "."; pp_sep f ~sep:"." pp_sn (Array.of_list ss)
let rec pp_e f = function
| ELambda (args, e) -> fpf f "@[{[%a] %a}@]" (fun f -> pp_sep f ~sep:";" pp_sn) args pp_e e
| EApp (e,ea) ->
  let args = match ea with
    | Ea0 -> [||] | Ea1 x -> [|x|] | Ea2 (x,y) -> [|x;y|] | Ea3 (x,y,z) -> [|x;y;z|] | Ea args -> args in
  fpf f "@["; pp_e f e; fpf f "["; pp_sep f ~sep:";" pp_e args; fpf f "]@]"
| EList es -> fpf f "@[(%a)@]" (fun f -> pp_sep f ~sep:";" pp_e) (Array.of_list es)
| EAdverb (av,e) ->
    let av = match av with AVForwardslash -> "/" | AVForwardslashColon -> "/:" | AVBackslash -> "\\" | AVBackslashColon -> "\\:" | AVQuote -> "\'" | AVQuoteColon -> "\':"
    in fpf f "@["; pp_e f e; fpf f "%s@]" av
| EReturn e -> fpf f "@[:%a@]" pp_e e
| ESeq (e,e') -> fpf f "@[%a;%a@]" pp_e e pp_e e'
| EIfSimple (i,t,e) -> fpf f "@[:[%a;%a;%a]@]" pp_e i pp_e t pp_e e
| EIfMulti (i,t,e) -> fpf f "@[if_multi@]"
| EAssign (h,e) -> fpf f "@[%a: %a@]" pp_h h pp_e e
| EAssignMonad (h,e) -> fpf f "@[%a %a:@]" pp_h h pp_e e
| EAssignDyad (h,e,e') -> fpf f "@[%a %a: %a@]" pp_h h pp_e e pp_e e'
| EAssignIndex (h,es,e) -> fpf f "@[%a[%a]: %a@]" pp_h h (fun f -> pp_sep f ~sep:";" pp_e) es pp_e e
| EAssignIndexMonad (h,es,e) -> fpf f "@[%a[%a] %a:@]" pp_h h (fun f -> pp_sep f ~sep:";" pp_e) es pp_e e
| EAssignIndexDyad (h,es,e,e') -> fpf f "@[%a[%a] %a: %a@]" pp_h h (fun f -> pp_sep f ~sep:";" pp_e) es pp_e e pp_e e'
| EAssignGlobal (h,e) -> fpf f "@[%a:: %a@]" pp_h h pp_e e
| EComp(e,e') -> fpf f "@[%a %a@]" pp_e e pp_e e'
| EName (HAbs []) -> fpf f "@[.`@]"
| EName h -> fpf f "@["; pp_h f h; fpf f "@]";
| ENameSys s -> fpf f "@[%s@]" (sname s);
| EVerbMonadic v -> fpf f "@["; pp_e f (EVerb v); fpf f ":"; fpf f "@]"
| EVerb v ->
  let v = match v with
  |VPlus->"+"|VMinus->"-"|VStar->"*"|VExclaim->"!"|VPercent->"%"|VPipe->"|"|VAmpersand->"&"
  |VCircumflex->"^"|VLangle->"<"|VRangle->">"|VEquals->"="|VPound->"#"|VLodash->"_"|VTilde->"~"
  |VDollar->"$"|VQuestion->"?"|VAt->"@"|VDot->"."|VComma->","|VZeroColon->"0:"|VOneColon->"1:"|VTwoColon->"2:"|VThreeColon->"3:"|VFourColon->"4:"|VFiveColon->"5:"
  in fpf f "@[%s@]" v
| ELiteral k -> pp_k f k
| EColon -> fpf f "@[:@]"
| ENil -> ()
let pp_c f = function
  | CEval e -> pp_e f e
  | CExit -> fpf f "@[\\\\@]"
  | CCd h -> fpf f "@[\\d %a@]" pp_h h
  | CPwd ->  fpf f "@[\\d@]"
  | CLoad fn -> fpf f "@[\\l \"%s\"@]" (String.escaped fn)
  | CWsLoad (Some fn) -> fpf f "@[\\load \"%s\"@]" (String.escaped fn)
  | CWsLoad None -> fpf f "@[\\load@]"
  | CWsSave (Some fn) -> fpf f "@[\\save \"%s\"@]" (String.escaped fn)
  | CWsSave None -> fpf f "@[\\save@]"
  | CWsSize -> fpf f "@[\\w@]"
let pp_cs f cs = List.iter (pp_c f) cs
(* stdlib / utilities ====================================================== *)
[@@inline always] let some x = Some x
let int_of_string s = try int_of_string s with Failure _ -> raise KError_domain
let float_of_string s = try float_of_string s with Failure _ -> raise KError_domain
let is_empty = function [] -> true | _ -> false
let swap t i j =
    let tmp = t.(i) in
    t.(i) <- t.(j);
    t.(j) <- tmp
let arev_inplace t =
  let i = ref 0 in
  let j = ref (len t - 1) in
  while !i < !j; do
    swap t !i !j; incr i; decr j;
  done
let array_of_list_rev xs = let a = Array.of_list xs in arev_inplace a; a

(* R. Sedgewick, "Analysis of shellsort and related algorithms", http://www.cs.princeton.edu/~rs/talks/shellsort.pdf *)
let shell_grade_inc = [|1073790977;268460033;67121153;16783361;4197377;1050113;262913;65921;16577;4193;1073;281;77;23;8;1;0|]
let shell_grade_inc_n = len shell_grade_inc
let shell_grade less x = (* PERF:avoid indexing through p (sort x itself simultaneously) *)
  let n = len x in let p = Array.init n (fun i -> i) in
  let i = ref 0 and j = ref 0 and h = ref 0 and t = ref 0 in
  while shell_grade_inc.(!t) > n do incr t; done;
  while !t < shell_grade_inc_n do
    h := shell_grade_inc.(!t); i := !h;
    while !i < n do
      let vp = p.(!i) in j := !i;
      while !j >= !h && less x.(vp) x.(p.(!j - !h)) do
        p.(!j) <- p.(!j - !h); j := !j - !h;
      done;
      p.(!j) <- vp; incr i;
    done; incr t;
  done; p

let radix_grade_int_asc x = (* PERF:avoid indexing through p (sort x itself simultaneously) *)
  let n = len x in
  let c = Array.make 0x100 0 and b = Array.make 0x100 0
  and p = Array.init n (fun i -> i) and aux = Array.make n 0
  and j = ref 0 in
  let pass p aux shift =
    for i = 0 to n-1 do
      let h = (x.(p.(i)) lsr shift) land 0xFF
      in c.(h) <- 1+c.(h);
    done;
    j := 0; for i = 0 to 0xFF do
      b.(i) <- !j; j := !j + c.(i); c.(i) <- 0;
    done;
    for i = 0 to n-1 do
      let pi = p.(i) in let h = (x.(pi) lsr shift) land 0xFF in
      let bh = b.(h) in aux.(bh) <- pi; b.(h) <- b.(h)+1;
    done in
  let sign p aux =
    let nn = ref 0 in for i = 0 to n-1 do if x.(p.(i)) < 0 then incr nn; done;
    j := 0; for i = 0 to n-1 do
      let pi = p.(i) in
      if x.(pi) >= 0 then (aux.(!nn) <- pi; incr nn) else (aux.(!j) <- pi; incr j)
    done in
  pass p aux 0; pass aux p 8; pass p aux 16;
  sign aux p; p
let radix_grade_int_desc x = let x = radix_grade_int_asc x in arev_inplace x; x (* PERF/MEM *)

[@@inline always] let some x = Some x
[@@inline always] let flip f x y = f y x
[@@inline always] let comp f g x = f (g x)
[@@inline always] let comp3 f g h x = f (g (h x))
[@@inline always] let comp4 f g h i x = f (g (h (i x)))
[@@inline always] let comp_r f g x y = f x (g y)
[@@inline always] let comp_l f g x y = f (g x) y
[@@inline always] let comp_lr f g h x y = f (g x) (h y)
[@@inline always] let append x y = Array.append x y
[@@inline always] let aiter x f = let n = len x in for i = 0 to n-1 do f x.(i); done
[@@inline always] let aiteri x f = let n = len x in for i = 0 to n-1 do f x.(i) i; done
[@@inline always] let amap x f = Array.map f x
[@@inline always] let aget a i = try a.(i) with _ -> raise KError_index
let afindi xs x = let n = len xs in
  let rec loop i = if i >= n then n else
    if xs.(i) = x then i else loop (i+1)
  in loop 0
let mod_pos x y = if x < 0 then y+(x mod y) else x mod y
let atake x y = let n = len y in (Array.init (abs x) (if x > 0 then fun i -> y.(mod_pos i n) else fun i -> y.(mod_pos (n+x+i) n)))
[@@inline always] let afoldl x ~f ~init = Array.fold_left f init x
let ascanl_map x ~f ~g ~init = let n = len x in
  if n = 0 then []
  else (let r = ref init in let a = ref [!r] in for i = 0 to n - 1 do r := f !r (g x.(i));a:=!r::!a; done; !a)
let ascanl1_map x ~f ~g = let n = len x in
  if n = 0 then []
  else (let r = ref (g x.(0)) in let a = ref [!r] in for i = 1 to n - 1 do r := f !r (g x.(i));a:=!r::!a; done; !a)
let areduce t ~f = let n = len t in
  if n = 0 then raise KError_length
  else (let r = ref t.(0) in for i = 1 to n - 1 do r := f !r t.(i) done; !r)
let areduce_map t ~f ~g = let n = len t in
  if n = 0 then raise KError_length
  else (let r = ref (g t.(0)) in for i = 1 to n - 1 do r := f !r (g t.(i)) done;!r)
[@@inline always] let azip_map f (x:'a array) (y:'b array) =
  let n = len x in if n <> len y then raise KError_length
  else Array.init n (fun i -> f x.(i) y.(i))
let azip_map_r g f = azip_map (comp_r f g)
let azip_map_l g f = azip_map (comp_l f g)
let azip_map_lr g h f = azip_map (comp_lr f g h)
[@@inline always] let aiter2 f (x:'a array) (y:'b array) =
  let n = len x in if n <> len y then raise KError_length
  else for i = 0 to n-1 do f x.(i) y.(i); done
[@@inline always] let aiteri2 f (x:'a array) (y:'b array) =
  let n = len x in if n <> len y then raise KError_length
  else for i = 0 to n-1 do f x.(i) y.(i) i; done
[@@inline always] let aiter2_ x y n f = for i = 0 to n-1 do f x.(i) y.(i); done
let aiter2_map_r g f = aiter2 (comp_r f g)
let aiter2_map_l g f = aiter2 (comp_l f g)
let aiter2_map_lr g h f = aiter2 (comp_lr f g h)
let amap_pairs f a = Array.init (len a-1) (fun i -> f a.(i) a.(i+1))

[@@inline always] let group xs ~hmake ~hmem ~hadd ~hiter ~hall =
  let n = len xs in let h = hmake n and h1 = hmake n and j = ref 0 in
  for i = 0 to n-1 do
    let xsi = xs.(i) in
    if not (hmem h xsi) then (hadd h xsi !j; incr j);
    hadd h1 xsi i;
  done;
  let r = Array.make !j KNil in
  hiter (fun x j -> r.(j) <- KIntegerArray (array_of_list_rev (hall h1 x))) h;
  r
let group_k = group ~hmake:(fun _ -> Hk.create config.hash_size) ~hmem:Hk.mem ~hadd:Hk.add ~hiter:Hk.iter ~hall:Hk.find_all
let group_int = group ~hmake:(fun _ -> H.create config.hash_size) ~hmem:H.mem ~hadd:H.add ~hiter:H.iter ~hall:H.find_all
let group_float = group ~hmake:(fun _ -> Hf.create config.hash_size) ~hmem:Hf.mem ~hadd:Hf.add ~hiter:Hf.iter ~hall:Hf.find_all
let group_sym = group_int
let group_char x = group
  ~hmake:(fun _ -> Array.make 255 [])
  ~hmem:(fun h x -> not (is_empty h.(x)))
  ~hadd:(fun h x j -> h.(x) <- j :: h.(x))
  ~hall:(Array.get)
  ~hiter:(fun f h -> for i = 0 to 254 do if not (is_empty h.(i)) then f i (List.hd h.(i)); done) (Array.map Char.code x)

[@@inline always] let range ~hmake ~hmem ~hadd ~hiter ~nil xs =
  let n = len xs in let h = hmake () and j = ref 0 in
  for i = 0 to n-1 do
    let xsi = xs.(i) in if not (hmem h xsi) then (hadd h xsi !j; incr j);
  done;
  let r = Array.make !j nil in
  hiter (fun x j -> r.(j) <- x) h; r
let range_k = range ~hmake:(fun _ -> Hk.create 255) ~hmem:Hk.mem ~hadd:Hk.add ~hiter:Hk.iter ~nil:KNil
let range_int = range ~hmake:(fun _ -> H.create 255) ~hmem:H.mem ~hadd:H.replace ~hiter:H.iter ~nil:0
let range_float = range ~hmake:(fun _ -> Hf.create 255) ~hmem:Hf.mem ~hadd:Hf.add ~hiter:Hf.iter ~nil:0.0
let range_sym = range_int
let range_char x = range
  ~hmake:(fun _ -> Array.make 256 (-1))
  ~hmem:(fun h x -> h.(x) >= 0)
  ~hadd:(fun h x j -> h.(x) <- j)
  ~hiter:(fun f h -> for i = 0 to 255 do if h.(i) >= 0 then f (Char.chr i) h.(i); done)
  ~nil:' ' (Array.map Char.code x)

let klen = function
  | KIntegerArray y -> len y | KFloatArray y -> len y | KCharArray y -> len y | KSymbolArray y -> len y | KList y -> len y
  | _ -> 1
let kmap1 f = function
  | KIntegerArray x -> amap x (comp f kinteger)
  | KFloatArray x -> amap x (comp f kfloat)
  | KCharArray x -> amap x (comp f kchar)
  | KSymbolArray x -> amap x (comp f ksymbol)
  | KList x -> amap x f
  | _ -> raise KError_type
let rec kcopy_deep_box d = match d with (* PERF *)
  | KDictionary d -> KDictionary (dcopy_deep_box d)
  | KIntegerArray x -> KList (amap x kinteger)
  | KFloatArray x -> KList (amap x kfloat)
  | KCharArray x -> KList (amap x kchar)
  | KSymbolArray x -> KList (amap x ksymbol)
  | KList x -> KList (amap x kcopy_deep_box)
  | KNil | KFunction _  | KInteger _ | KFloat _ | KChar _ | KSymbol _ -> d
and dcopy_deep_box d = let d = dcopy d in
    H.iter (fun k {value;attr} -> dset d k {
      value = kcopy_deep_box value;
      attr  = match attr with ANil -> attr | ADict d ->  ADict (dcopy_deep_box d)}) d;
    d
let blit ~src ~src_pos ~dst ~dst_pos ~len = Array.blit src src_pos dst dst_pos len
let arot (x:int) (y:'a array) : 'a array = (* PERF:blit *)
  let len = len y in
  let a = Array.copy y in
  let x = x mod len in
  let x = if x < 0 then len+x else x in
  let k = len - x in
  blit ~src:y ~src_pos:x ~dst:a ~dst_pos:0 ~len:k; (*SLOW*)
  blit ~src:y ~src_pos:0 ~dst:a ~dst_pos:k ~len:x; (*SLOW*)
  a
let krot x = function
  | KIntegerArray y -> KIntegerArray (arot x y)
  | KFloatArray y -> KFloatArray (arot x y)
  | KCharArray y -> KCharArray (arot x y)
  | KSymbolArray y -> KSymbolArray (arot x y)
  | KList y -> KList (arot x y)
  | _ -> raise KError_type
let as_list = function
  | KIntegerArray x -> amap x kinteger
  | KFloatArray x -> amap x kfloat
  | KCharArray x -> amap x kchar
  | KSymbolArray x -> amap x ksymbol
  | KList x -> x
  | x -> [|x|]
let sub a pos len = Array.sub a pos len
let explode s = Array.init (Bytes.length s) (fun i -> s.[i])
let adrop x y = let n = len y in let p,l = if x >= 0 then x,n-x else 0,n+x in sub y p l
let acut x y f = let n = len y in
  let p, a = afoldl x ~init:(0,[]) ~f:(fun (p,xs) x ->  if x-p>0 then (x,f (sub y p (x-p))::xs) else (x,xs)) in
  if p < n then array_of_list_rev ((f (sub y p (n-p))) :: a) else array_of_list_rev a
let rec shape x = match x with
  | KFunction _ | KDictionary _ | KInteger _ | KChar _ | KFloat _ | KSymbol _ | KNil -> [||]
  | KCharArray _| KFloatArray _| KIntegerArray _| KSymbolArray _ -> [|klen x|]
  | KList [||] -> [|0|]
  | KList x ->
      let n = len x in
      let s = Array.init n (fun i -> shape x.(i)) in
      let m = areduce_map ~f:min ~g:len s in
      let acc = ref [] in
      (try for j = 0 to m-1 do
          let current = s.(0).(j) in
          for i = 1 to n-1 do if s.(i).(j) <> current then raise Exit; done;
          acc := current::!acc
        done with Exit -> ());
      Array.of_list (n::List.rev !acc)
let kvec xs =
  let int = ref 0 and char = ref 0 and float = ref 0 and symbol = ref 0 in
  try let n = len xs in if n = 0 then raise Exit else for i = 0 to n-1 do
      (match xs.(i) with KInteger _ -> int:=1 | KFloat _ -> float:=1 | KChar _ -> char:=1 | KSymbol _ -> symbol:=1 |_-> raise Exit);
      if !int+ !float+ !char+ !symbol > 1 then raise Exit;
    done;
    if !int>0 then KIntegerArray (amap xs kinteger_prj)
    else if !char>0 then KCharArray (amap xs kchar_prj)
    else if !float>0 then KFloatArray (amap xs kfloat_prj)
    else if !symbol>0 then KSymbolArray (amap xs ksymbol_prj)
    else assert false
  with Exit -> KList xs
let rec kvec_deep = function KList d -> (match kvec d with KList d -> KList (amap d kvec_deep) |d -> d) | KDictionary d -> KDictionary(dmapv_inplace d kvec_deep;d) | d -> d
let kzip_with f x y = match x,y with
  | KList x,KIntegerArray y ->  azip_map_r kinteger f x y
  | KList x,KFloatArray y ->  azip_map_r kfloat f x y
  | KList x,KCharArray y ->  azip_map_r kchar f x y
  | KList x,KSymbolArray y ->  azip_map_r ksymbol f x y
  | KList x,KList y ->  azip_map f x y
  | KList x,atom    -> amap x (flip f atom)
  | KIntegerArray x,KIntegerArray y -> azip_map_lr kinteger kinteger f x y
  | KIntegerArray x,KFloatArray y -> azip_map_lr kinteger kfloat f x y
  | KIntegerArray x,KCharArray y -> azip_map_lr kinteger kchar f x y
  | KIntegerArray x,KSymbolArray y -> azip_map_lr kinteger ksymbol f x y
  | KIntegerArray x,KList y -> azip_map_l kinteger f x y
  | KIntegerArray x,atom    -> amap x (comp (flip f atom) kinteger)
  | KFloatArray x,KIntegerArray y -> azip_map_lr kfloat kinteger f x y
  | KFloatArray x,KFloatArray y -> azip_map_lr kfloat kfloat f x y
  | KFloatArray x,KCharArray y -> azip_map_lr kfloat kchar f x y
  | KFloatArray x,KSymbolArray y -> azip_map_lr kfloat ksymbol f x y
  | KFloatArray x,KList y -> azip_map_l kfloat f x y
  | KFloatArray x,atom    -> amap x (comp (flip f atom) kfloat)
  | KCharArray x,KIntegerArray y -> azip_map_lr kchar kinteger f x y
  | KCharArray x,KFloatArray y -> azip_map_lr kchar kfloat f x y
  | KCharArray x,KCharArray y -> azip_map_lr kchar kchar f x y
  | KCharArray x,KSymbolArray y -> azip_map_lr kchar ksymbol f x y
  | KCharArray x,KList y -> azip_map_l kchar f x y
  | KCharArray x,atom    -> amap x (comp (flip f atom) kchar)
  | KSymbolArray x,KIntegerArray y -> azip_map_lr ksymbol kinteger f x y
  | KSymbolArray x,KFloatArray y -> azip_map_lr ksymbol kfloat f x y
  | KSymbolArray x,KCharArray y -> azip_map_lr ksymbol kchar f x y
  | KSymbolArray x,KSymbolArray y -> azip_map_lr ksymbol ksymbol f x y
  | KSymbolArray x,KList y -> azip_map_l ksymbol f x y
  | KSymbolArray x,atom    -> amap x (comp (flip f atom) ksymbol)
  | atom,KList x -> amap x (f atom)
  | atom,KSymbolArray x -> amap x (comp (f atom) ksymbol)
  | atom,KCharArray x -> amap x (comp (f atom) kchar)
  | atom,KFloatArray x -> amap x (comp (f atom) kfloat)
  | atom,KIntegerArray x -> amap x (comp (f atom) kinteger)
  | _ -> raise KError_type
let kiter2_with f x y = match x,y with
  | KList x,KIntegerArray y ->  aiter2_map_r kinteger f x y
  | KList x,KFloatArray y ->  aiter2_map_r kfloat f x y
  | KList x,KCharArray y ->  aiter2_map_r kchar f x y
  | KList x,KSymbolArray y ->  aiter2_map_r ksymbol f x y
  | KList x,KList y ->  aiter2 f x y
  | KList x,atom    -> aiter x (flip f atom)
  | KIntegerArray x,KIntegerArray y -> aiter2_map_lr kinteger kinteger f x y
  | KIntegerArray x,KFloatArray y -> aiter2_map_lr kinteger kfloat f x y
  | KIntegerArray x,KCharArray y -> aiter2_map_lr kinteger kchar f x y
  | KIntegerArray x,KSymbolArray y -> aiter2_map_lr kinteger ksymbol f x y
  | KIntegerArray x,KList y -> aiter2_map_l kinteger f x y
  | KIntegerArray x,atom    -> aiter x (comp (flip f atom) kinteger)
  | KFloatArray x,KIntegerArray y -> aiter2_map_lr kfloat kinteger f x y
  | KFloatArray x,KFloatArray y -> aiter2_map_lr kfloat kfloat f x y
  | KFloatArray x,KCharArray y -> aiter2_map_lr kfloat kchar f x y
  | KFloatArray x,KSymbolArray y -> aiter2_map_lr kfloat ksymbol f x y
  | KFloatArray x,KList y -> aiter2_map_l kfloat f x y
  | KFloatArray x,atom    -> aiter x (comp (flip f atom) kfloat)
  | KCharArray x,KIntegerArray y -> aiter2_map_lr kchar kinteger f x y
  | KCharArray x,KFloatArray y -> aiter2_map_lr kchar kfloat f x y
  | KCharArray x,KCharArray y -> aiter2_map_lr kchar kchar f x y
  | KCharArray x,KSymbolArray y -> aiter2_map_lr kchar ksymbol f x y
  | KCharArray x,KList y -> aiter2_map_l kchar f x y
  | KCharArray x,atom    -> aiter x (comp (flip f atom) kchar)
  | KSymbolArray x,KIntegerArray y -> aiter2_map_lr ksymbol kinteger f x y
  | KSymbolArray x,KFloatArray y -> aiter2_map_lr ksymbol kfloat f x y
  | KSymbolArray x,KCharArray y -> aiter2_map_lr ksymbol kchar f x y
  | KSymbolArray x,KSymbolArray y -> aiter2_map_lr ksymbol ksymbol f x y
  | KSymbolArray x,KList y -> aiter2_map_l ksymbol f x y
  | KSymbolArray x,atom    -> aiter x (comp (flip f atom) ksymbol)
  | atom,KList x -> aiter x (f atom)
  | atom,KSymbolArray x -> aiter x (comp (f atom) ksymbol)
  | atom,KCharArray x -> aiter x (comp (f atom) kchar)
  | atom,KFloatArray x -> aiter x (comp (f atom) kfloat)
  | atom,KIntegerArray x -> aiter x (comp (f atom) kinteger)
  | atom,atom' -> f atom atom'
let kiter_with f x = match x with
  | KList x ->  aiter x f
  | KIntegerArray x -> aiter x (comp f kinteger)
  | KFloatArray x -> aiter x (comp f kfloat)
  | KCharArray x -> aiter x (comp f kchar)
  | KSymbolArray x -> aiter x (comp f ksymbol)
  | atom -> f atom
let kaiter_with f x a = match x with
  | KList x ->  aiter2 f x a
  | KIntegerArray x -> aiter2 (comp f kinteger) x a
  | KFloatArray x -> aiter2 (comp f kfloat) x a
  | KCharArray x -> aiter2 (comp f kchar) x a
  | KSymbolArray x -> aiter2 (comp f ksymbol) x a
  | atom -> aiter a (fun a -> f atom a)
let kaiteri_with f x a = match x with
  | KList x ->  aiteri2 f x a
  | KIntegerArray x -> aiteri2 (comp f kinteger) x a
  | KFloatArray x -> aiteri2 (comp f kfloat) x a
  | KCharArray x -> aiteri2 (comp f kchar) x a
  | KSymbolArray x -> aiteri2 (comp f ksymbol) x a
  | atom -> aiteri a (fun a i -> f atom a i)
let rec kmap_rec f = function KList x -> f (KList (amap x (kmap_rec f))) | x -> f x

let list_of_kap n ks is = let x = Array.make n KNil in aiter2 (fun k i -> x.(i) <- k) ks is; x
let k_of_kargs = function
  | Ka0 -> KNil | Ka1 x -> x
  | Ka2 (x,y) -> kvec [|x;y|] | Ka3 (x,y,z) -> kvec [|x;y;z|] | Ka xs -> kvec xs
  | Kap (n,ks,is,js) -> KList (list_of_kap n ks is)
let klist_of_kargs = function
  | Ka0 -> KNil | Ka1 x -> KList [|x|] | Ka2 (x,y) -> KList [|x;y|] | Ka3 (x,y,z) -> KList [|x;y;z|] | Ka x -> KList x
  | Kap (n,ks,is,_) ->  KList (list_of_kap n ks is)

let fmonad_prj = function (FMonadDyadTriadTetrad (f,_,_,_)|FMonadDyadTriad (f,_,_)|FMonadDyad (f,_)|FMonad f) -> f
  | FNilad _ -> raise KError_valence
  | FDyad f -> (fun x -> KFunction (FMonad (f x)))
  | FTriad f -> (fun x -> KFunction (FDyad (f x)))
  | FNary (n,f) -> (fun x -> partial_app_nary_prefix f n 1 [|x|])
let kfmonad_prj = function KFunction f -> fmonad_prj f | KNil -> id |_ -> raise KError_type
let fdyad_prj = function (FMonadDyadTriadTetrad (_,f,_,_)|FMonadDyadTriad (_,f,_)|FMonadDyad (_,f)|FDyad f) -> f
  | FNilad _|FMonad _ -> raise KError_valence
  | FTriad f -> (fun x y -> KFunction (FMonad (f x y)))
  | FNary (n,f) -> (fun x y -> partial_app_nary_prefix f n 2 [|x;y|])
let kfdyad_prj = function KFunction f -> fdyad_prj f |KNil -> (fun x y -> kvec [|x;y|]) |_ -> raise KError_type
let ftriad_prj = function (FMonadDyadTriadTetrad (_,_,f,_)|FMonadDyadTriad (_,_,f)|FTriad f) -> f
  | FNilad _|FMonad _|FDyad _|FMonadDyad _ -> raise KError_valence
  | FNary (n,f) -> (fun x y z -> partial_app_nary_prefix f n 3 [|x;y;z|])
let kftriad_prj = function KFunction f -> ftriad_prj f |KNil -> (fun x y z -> kvec [|x;y;z|]) |_ -> raise KError_type
let ftetrad_prj = function FMonadDyadTriadTetrad (_,_,_,f) -> f
  | FNary(n,f) when n>=4 -> (fun x y z u -> partial_app_nary_prefix f n 4 [|x;y;z;u|])
  | _ -> raise KError_valence
let kftetrad_prj = function KFunction f -> ftetrad_prj f | KNil -> (fun x y z u -> kvec [|x;y;z;u|]) | _ -> raise KError_type

let secant_root ~f ~x0 ~x1 ~max_iter ~tolerance =
    let rec loop xn1 fxn1 xn2 fxn2 i =
      if i = max_iter then raise KError_limit;
      let xn = xn1 -. (fxn1 *. ((xn1 -. xn2) /. (fxn1 -. fxn2))) in
      let fxn = f xn in
      if abs_float fxn < tolerance then xn
      else loop xn fxn xn1 fxn1 (i+1)
    in loop x1 (f x1) x0 (f x0) 0

(* symbol parser (already req'd for marshalling) =========================== *)
module Symbol_parser = struct open Tinyparse open Lexer
let t = token let tm = token_map let ws = t WS let tws tk = t tk |^> skip ws
let tname = tm (function NAME i -> i |_->fail())
let pnames = sep_token1 DOT tname |>> fun l -> (String.concat "." l, List.map (flip s None) l)
let phandle = choice [t DOT |>^ pnames |>> (fun (x,h) -> "."^x,HAbs h);pnames |>> (fun (x,h) -> x,HRel h)]
let parse_symbol s =
    let rec tokenize b ts = match Lexer.read b with EOF-> array_of_list_rev (EOF::ts) |t->tokenize b (t::ts) in
    let tokens = tokenize (Lexing.from_string s) [] in fst (phandle {tokens;pos=0})
end include Symbol_parser

(* adverbs ================================================================= *)
(* <adverb>_<arg-valence><result-valence> *)
let each_dd f x y = kvec (kzip_with f x y)
let each_left_dd f x y = match x,y with
  | KList x, y -> kvec (amap x (fun x -> f x y))
  | KSymbolArray x, y -> kvec (amap x (flip (comp_l f ksymbol) y))
  | KIntegerArray x, y -> kvec (amap x (flip (comp_l f kinteger) y))
  | KFloatArray x, y -> kvec (amap x (flip (comp_l f kfloat) y))
  | KCharArray x, y -> kvec (amap x (flip (comp_l f kchar) y))
  | x, y -> f x y
let each_right_dd f x y = match x,y with
  | x, KList y -> kvec (amap y (f x))
  | x, KSymbolArray y -> kvec (amap y (comp_r f ksymbol x))
  | x, KIntegerArray y -> kvec (amap y (comp_r f kinteger x))
  | x, KFloatArray y -> kvec (amap y (comp_r f kfloat x))
  | x, KCharArray y -> kvec (amap y (comp_r f kchar x))
  | _ -> raise KError_type
let over_dd f x y = match y with
  | KList y -> afoldl ~init:x ~f y
  | KSymbolArray y -> afoldl ~init:x ~f:(comp_r f ksymbol) y
  | KIntegerArray y -> afoldl ~init:x ~f:(comp_r f kinteger) y
  | KFloatArray y -> afoldl ~init:x ~f:(comp_r f kfloat) y
  | KCharArray y -> afoldl ~init:x ~f:(comp_r f kchar) y
  | _ -> f x y
let over_mm f x =
  let ix = x in
  let rec loop x =
    let fx = f x in
    if x = fx || ix = fx then fx else loop fx
  in loop ix
let scan_mm (f:k -> k) x =
  let ix = x in
  let rec loop acc x =
    let fx = f x in
    let acc = fx::acc in
    if x = fx || ix = fx then acc
    else loop acc fx
  in kvec (array_of_list_rev (loop [] ix))
let each_mm f x = match x with
  | KList x -> kvec (amap x f)
  | KSymbolArray x -> kvec (amap x (comp f ksymbol))
  | KIntegerArray x -> kvec (amap x (comp f kinteger))
  | KFloatArray x -> kvec (amap x (comp f kfloat))
  | KCharArray x -> kvec (amap x (comp f kchar))
  | x -> f x
let over_md f x y = match x,y with
  | KInteger n, x when n >= 0 ->
    let rec loop x = function 0 -> x | n -> loop (f x) (n-1)
    in loop x n
  | KInteger _, _ -> raise KError_domain
  | KFunction (FMonad b | FMonadDyad (b,_) | FMonadDyadTriad (b,_,_) | FMonadDyadTriadTetrad (b,_,_,_)), x (* b f\ x *) ->
    let b x = b x = KInteger 0 in
    let rec loop x = if b x then x else loop (f x)
    in loop x
  | KFunction _, _ -> raise KError_valence
  | _ -> raise KError_type
let scan_md f x y = match x,y with
  | KInteger n, x when n >= 0 ->
    let rec loop acc x = function 0 -> acc | n -> let fx = f x in loop (fx::acc) fx (n-1)
    in kvec (array_of_list_rev (loop [] x n))
  | KInteger _, _ -> raise KError_domain
  | KFunction (FMonad b | FMonadDyad (b,_) | FMonadDyadTriad (b,_,_) | FMonadDyadTriadTetrad (b,_,_,_)), x (* b f/ x *) ->
    let b x = b x = KInteger 0 in
    let rec loop acc x = if b x then acc else let fx = f x in loop (fx::acc) fx
    in kvec (array_of_list_rev (loop [] x))
  | KFunction _, _ -> raise KError_valence
  | _ -> raise KError_type
let each_pair_dm f x = match x with
  | KSymbol _ | KInteger _ | KFloat _ | KChar _ ->
    f x x
  | KList [||] | KSymbolArray [||] | KIntegerArray [||] | KFloatArray [||] | KCharArray [||] ->
    raise KError_length
  | KList x -> kvec (amap_pairs f x)
  | KSymbolArray x -> kvec (amap_pairs (comp_lr f ksymbol ksymbol) x)
  | KIntegerArray x -> kvec (amap_pairs (comp_lr f kinteger kinteger) x)
  | KFloatArray x -> kvec (amap_pairs (comp_lr f kfloat kfloat) x)
  | KCharArray x -> kvec (amap_pairs (comp_lr f kchar kchar) x)
  | _ -> raise KError_type
let over_dm f x = match x with
  | KList x -> areduce ~f x
  | KIntegerArray x -> areduce_map ~f ~g:kinteger x
  | KFloatArray x -> areduce_map ~f ~g:kfloat x
  | KSymbolArray x -> areduce_map ~f ~g:ksymbol x
  | KCharArray x -> areduce_map ~f ~g:kchar x
  | _ -> raise KError_type
let scan_dm f x = match x with
  | KList x -> kvec (array_of_list_rev (ascanl1_map ~f ~g:(fun x ->x) x))
  | KIntegerArray x -> kvec (array_of_list_rev (ascanl1_map ~f ~g:kinteger x))
  | KFloatArray x -> kvec (array_of_list_rev (ascanl1_map ~f ~g:kfloat x))
  | KSymbolArray x -> kvec (array_of_list_rev (ascanl1_map ~f ~g:ksymbol x))
  | KCharArray x -> kvec (array_of_list_rev (ascanl1_map ~f ~g:kchar x))
  | _ -> raise KError_type
let scan_dd f x y = match y with
  | KList y -> kvec (array_of_list_rev (ascanl_map ~f ~g:(fun y ->y) ~init:x y))
  | KIntegerArray y -> kvec (array_of_list_rev (ascanl_map ~f ~g:kinteger ~init:x y))
  | KFloatArray y -> kvec (array_of_list_rev (ascanl_map ~f ~g:kfloat ~init:x y))
  | KSymbolArray y -> kvec (array_of_list_rev (ascanl_map ~f ~g:ksymbol ~init:x y))
  | KCharArray y -> kvec (array_of_list_rev (ascanl_map ~f ~g:kchar ~init:x y))
  | _ -> raise KError_type

(* verb utils ============================================================== *)
let rec atomic_m (f:k -> k) (x:k) = if is_atom x then f x else kvec (kmap1 (atomic_m f) x)
let rec atomic_d f x y = match is_atom x,is_atom y with
  | true,true -> f x y
  | true,false -> kvec (kmap1 (fun y -> (atomic_d f) x y) y)
  | false,true -> kvec (kmap1 (fun x -> (atomic_d f) x y) x)
  | false,false -> kvec (kzip_with (atomic_d f) x y)
[@@inline always] let num_atomic_m ~f_int ~f_float = atomic_m (fun x ->
  match x with
  | KInteger x -> f_int x
  | KFloat x -> f_float x
  | _ -> raise KError_type)
[@@inline always] let num_atomic_d ~f_int ~f_float = atomic_d (fun x y -> match x,y with
  | KInteger n, KInteger m -> KInteger (f_int n m)
  | KFloat n, KFloat m -> KFloat (f_float n m)
  | KInteger n, KFloat m -> KFloat (f_float (float_of_int n) m)
  | KFloat n, KInteger m -> KFloat (f_float n (float_of_int m))
  | x,y -> raise KError_type)
[@@inline always] let not_atomic_m ~f_int ~f_float ~f_sym ~f_char ~f_k = function
  | KIntegerArray xs -> f_int xs
  | KFloatArray xs -> f_float xs
  | KSymbolArray xs -> f_sym xs
  | KCharArray xs -> f_char xs
  | KList xs -> f_k xs
  | _ -> raise KError_rank
[@@inline always] let float_atomic_d f = atomic_d (fun x y -> match x,y with
  | KInteger n, KInteger m -> KFloat (f (float_of_int n) (float_of_int m))
  | KFloat n, KFloat m -> KFloat (f n m)
  | KInteger n, KFloat m -> KFloat (f (float_of_int n) m)
  | KFloat n, KInteger m -> KFloat (f n (float_of_int m))
  | _ -> raise KError_type)
[@@inline always] let float_atomic_m f = num_atomic_m ~f_float:f ~f_int:(comp f float_of_int)
[@@inline always] let float_atomic_d2 f = atomic_d (fun x y -> match x,y with (* FIXME *)
  | KInteger n, KInteger m -> f (float_of_int n) (float_of_int m)
  | KFloat n, KFloat m -> f n m
  | KInteger n, KFloat m -> f (float_of_int n) m
  | KFloat n, KInteger m -> f n (float_of_int m)
  | _ -> raise KError_type)

(* verbs =================================================================== *)
let vplus = num_atomic_d ~f_int:(+) ~f_float:(+.)
let vplus_m x = match x with  (* flip PERF:track types *)
  | KList [||] -> x
  | KList [|_|] -> x
  | KList xs ->
      let m = len xs in
      let n = afoldl ~init:(-1) ~f:(fun acc x ->
        if acc = -1 then klen x else
        if is_atom x then acc else
        if acc <> klen x then raise KError_length else acc) xs in
      let at = amap xs @@ fun x ->
        if is_atom x then const x
        else match x with
        | KIntegerArray xs -> fun j -> KInteger xs.(j)
        | KFloatArray xs -> fun j -> KFloat xs.(j)
        | KSymbolArray xs -> fun j -> KSymbol xs.(j)
        | KCharArray xs -> fun j -> KChar xs.(j)
        | KList xs -> fun j -> xs.(j)
        | _ -> raise KError_rank
      in let a = Array.make_matrix n m KNil in
      for i = 0 to m-1 do
        let at = at.(i) in for j = 0 to n-1 do a.(j).(i) <- at j done
      done; kvec (Array.map klist a)
  | _ -> x
let vminus = num_atomic_d ~f_int:(-) ~f_float:(-.)
let vminus_m = num_atomic_m ~f_int:(fun x -> KInteger (0-x)) ~f_float:(fun x -> KFloat (0.0-.x))
let vstar = num_atomic_d ~f_int:( * ) ~f_float:( *. )
let vstar_m x =
  if is_atom x then x else match x with
  | KIntegerArray [||] -> KInteger 0
  | KIntegerArray xs -> KInteger xs.(0)
  | KFloatArray [||] -> KFloat 0.0
  | KFloatArray xs -> KFloat xs.(0)
  | KSymbolArray [||] -> KSymbol s0
  | KSymbolArray xs -> KSymbol xs.(0)
  | KCharArray [||] -> KChar ' '
  | KCharArray xs -> KChar xs.(0)
  | KList [||] ->  KNil
  | KList xs -> xs.(0)
  | _ -> assert false
let vexclaim x y = match x,y with
  | _, KInteger y -> let yf = float_of_int y in num_atomic_m ~f_int:(fun x -> KInteger(x mod y)) ~f_float:(fun x -> KFloat(mod_float x yf)) x
  | KIntegerArray x, y -> kvec (amap x (fun i -> krot i y))
  | KInteger x, y -> krot x y
  | _ -> raise KError_type
let vexclaim_m = function
  | KNil -> KSymbolArray [||]
  | KInteger 0 -> KIntegerArray [||]
  | KInteger n when n > 0 -> KIntegerArray (Array.init n (fun i -> i))
  | KIntegerArray x -> let n = len x in (* odometer *)
    let rec step i y =
      let j = n-1-i in if i = n then raise Exit
      else if y.(j)<x.(j)-1 then (y.(j) <- y.(j)+1;for k=j+1 to n-1 do y.(k)<-0;done;KIntegerArray y)
      else step (i+1) y in
    let rec loop acc y =
      let y = Array.copy y in try loop (step 0 y::acc) y with Exit -> KList (array_of_list_rev acc)
    in let y = Array.make n 0 in loop [KIntegerArray y] y
  | KInteger _ -> raise KError_domain
  | KList _ -> raise KError_domain
  | KDictionary d -> KSymbolArray (dkeys d)
  | KSymbol s -> try (match kgets_exn s with KDictionary d -> KSymbolArray (dkeys d) |_->KNil) with Not_found -> KNil
  | _ -> raise KError_type
let vpercent = float_atomic_d (/.)
let vpercent_m = num_atomic_m ~f_int:(fun x -> kfloat @@ 1.0/.(float_of_int x))
                              ~f_float:(fun x -> kfloat @@ 1.0/.x)
let vpipe = num_atomic_d ~f_int:max ~f_float:max
let vpipe_m = function
  | KIntegerArray xs -> let a = Array.copy xs in arev_inplace a; KIntegerArray a
  | KFloatArray xs -> let a = Array.copy xs in arev_inplace a; KFloatArray a
  | KSymbolArray xs -> let a = Array.copy xs in arev_inplace a; KSymbolArray a
  | KCharArray xs -> let a = Array.copy xs in arev_inplace a; KCharArray a
  | KList xs -> let a = Array.copy xs in arev_inplace a; KList a
  | x -> x
let vampersand = num_atomic_d ~f_int:min ~f_float:min
let rec vampersand_m x = match x with
  | KInteger x when x >= 0 -> KIntegerArray (Array.make x 0)
  | KInteger _ -> raise KError_domain
  | KIntegerArray x ->
    let a = Array.make (afoldl ~init:0 ~f:(+) x) 0 in
    Array.iter (fun y -> if y < 0 then raise KError_domain) x;
    ignore(afoldl x ~init:(0,0) ~f:(fun (i,p) x -> Array.fill a p x i; (i+1,p+x)));
    KIntegerArray a
  | KList x -> (match kvec x with KIntegerArray x -> vampersand_m (KIntegerArray x) | _ -> raise KError_type)
  | _ -> raise KError_type
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
  | KFloat x,        KInteger y      -> KFloatArray [|x;float_of_int y|]
  | KInteger x,      KFloat y        -> KFloatArray [|float_of_int x;y|]
  | KFloat x,        KIntegerArray y -> KFloatArray (append [|x|] (amap y float_of_int))
  | KIntegerArray x, KFloat y        -> KFloatArray (append (amap x float_of_int) [|y|])
  | KFloatArray x,   KInteger y      -> KFloatArray (append x [|float_of_int y|])
  | KInteger x,      KFloatArray y   -> KFloatArray (append [|float_of_int x|] y)
  | KFloatArray x,   KIntegerArray y -> KFloatArray (append x (amap y float_of_int))
  | KIntegerArray x, KFloatArray y   -> KFloatArray (append (amap x float_of_int) y)
  (* not list,list *)
  | KSymbol _,KList y|KNil,KList y|KInteger _,KList y|KFloat _,KList y|KChar _,KList y|KDictionary _,KList y|KFunction _,KList y ->
    KList (append [|x|] y)
  (* list,not list *)
  | KList x,KSymbol _| KList x,KNil| KList x,KInteger _| KList x,KFloat _| KList x,KChar _| KList x,KDictionary _ | KList x,KFunction _ ->
    KList (append x [|y|])
  (* list,vector *)
  | KList x,KSymbolArray _|KList x,KIntegerArray _|KList x,KFloatArray _ |KList x,KCharArray _ ->
    KList (append x (as_list y))
  (* vector,list *)
  | KSymbolArray _,KList y|KIntegerArray _,KList y|KFloatArray _,KList y|KCharArray _,KList y ->
    KList (append (as_list x) y)
  (* t1-vector,t2-atom (t1!=t2) *)
  |KChar _,KIntegerArray _|KChar _,KSymbolArray _|KDictionary _,KCharArray _|KDictionary _,KFloatArray _|KDictionary _,KIntegerArray _|KDictionary _,KSymbolArray _|KFloat _,KCharArray _|KFloat _,KSymbolArray _|KFunction _,KCharArray _|KFunction _,KFloatArray _|KFunction _,KIntegerArray _|KFunction _,KSymbolArray _|KInteger _,KCharArray _|KInteger _,KSymbolArray _|KIntegerArray _,KChar _|KNil,KCharArray _|KNil,KFloatArray _|KNil,KIntegerArray _|KNil,KSymbolArray _|KSymbol _,KCharArray _|KSymbol _,KIntegerArray _|KSymbol _,KFloatArray _ ->
    KList (append [|x|] (as_list y))
  (* t1-atom,t2-vector (t1!=t2) *)
  |KCharArray _,KDictionary _|KCharArray _,KFloat _|KCharArray _,KFunction _|KCharArray _,KInteger _|KCharArray _,KNil|KCharArray _,KSymbol _|KFloatArray _,KChar _|KFloatArray _,KDictionary _|KFloatArray _,KFunction _|KFloatArray _,KNil|KFloatArray _,KSymbol _|KIntegerArray _,KDictionary _|KIntegerArray _,KFunction _|KIntegerArray _,KNil|KIntegerArray _,KSymbol _|KSymbolArray _,KChar _|KSymbolArray _,KDictionary _|KSymbolArray _,KFloat _|KSymbolArray _,KFunction _|KSymbolArray _,KInteger _|KSymbolArray _, KNil ->
    KList (append (as_list x) [|y|])
  (* t1-vector,t2-vector (t1!=t2) *)
  | KCharArray _,KFloatArray _|KCharArray _,KIntegerArray _| KCharArray _,KSymbolArray _|KFloatArray _,KCharArray _|KFloatArray _,KSymbolArray _|KIntegerArray _,KCharArray _|KIntegerArray _,KSymbolArray _|KSymbolArray _,KCharArray _|KSymbolArray _,KFloatArray _|KSymbolArray _,KIntegerArray _ ->
    KList (append (as_list x) (as_list y))
  (* non-list atoms. (t1,t1) where t1 has no vector representation; (t1,t2) where t1!=t2 *)
  | x,y -> KList [|x;y|]
let vcomma_m x = match x with (* enlist *)
  | KChar x    -> KCharArray [|x|]
  | KFloat x   -> KFloatArray [|x|]
  | KInteger x -> KIntegerArray [|x|]
  | KSymbol x  -> KSymbolArray [|x|]
  | x          -> KList [|x|]
let rec int_pow a = function
  | 0 -> 1 | 1 -> a | n -> let b = int_pow a (n / 2) in b * b * (if n mod 2 = 0 then 1 else a)
let vcircumflex = num_atomic_d ~f_int:int_pow ~f_float:( ** )
let rec vcircumflex_m x = KIntegerArray (shape x)
let vlangle = atomic_d (fun x y -> match x,y with
  | KInteger n, KInteger m -> KInteger (if n<m then 1 else 0)
  | KInteger n, KFloat m -> KInteger (if (float_of_int n)<m then 1 else 0)
  | KFloat n, KInteger m -> KInteger (if n<(float_of_int m) then 1 else 0)
  | KChar n, KChar m -> KInteger (if n<m then 1 else 0)
  | KFloat n, KFloat m -> KInteger (if n<m then 1 else 0)
  | KSymbol n, KSymbol m -> KInteger (if n<m then 1 else 0)
  | _ -> raise KError_type)
let vlangle_m = not_atomic_m (* grade up *)
  ~f_k:(fun xs -> KIntegerArray (shell_grade (<) xs))
  ~f_char:(fun xs -> KIntegerArray (shell_grade (<) xs))
  ~f_int:(fun xs -> KIntegerArray (radix_grade_int_asc xs))
  ~f_sym:(fun xs -> KIntegerArray (radix_grade_int_asc xs))
  ~f_float:(fun xs -> KIntegerArray (shell_grade (<) xs))
let vrangle = flip vlangle
let vrangle_m = not_atomic_m  (* grade down *)
  ~f_k:(fun xs -> KIntegerArray (shell_grade (>) xs))
  ~f_char:(fun xs -> KIntegerArray (shell_grade (>) xs))
  ~f_int:(fun xs -> KIntegerArray (radix_grade_int_desc xs))
  ~f_sym:(fun xs -> KIntegerArray (radix_grade_int_desc xs))
  ~f_float:(fun xs -> KIntegerArray (shell_grade (>) xs))
let vequals = atomic_d (fun x y -> KInteger (if x=y then 1 else 0))
let vequals_m = not_atomic_m (* group *)
  ~f_k:(fun xs -> KList (group_k xs))
  ~f_char:(fun xs -> KList (group_char xs))
  ~f_int:(fun xs -> KList (group_int xs))
  ~f_sym:(fun xs -> KList (group_sym xs))
  ~f_float:(fun xs -> KList (group_float xs))
let rec split_map f d m a i = if i+d > m then [] else f (sub a i d) :: split_map f d m a (i+d)
let reshape_k x nx y ny = (* FIXME/TODO:filling behavior *)
  let px = afoldl x ~init:1 ~f:( * ) in
  let rec loop i m a =
    if i >= nx then a.(0)
    else let m' = m/x.(i)
         in KList (Array.of_list (split_map (loop (i+1) m') m' m a 0)) in
  if px > ny then raise KError_length else loop 0 px y
let reshape_v x y f =  (* FIXME/TODO:filling behavior *)
  let nx,ny = len x, len y in let xnx1 = x.(nx-1) in
  let ya = Array.of_list (split_map f xnx1 ny y 0) in
  reshape_k (sub x 0 (nx-1)) (nx-1) ya (ny/xnx1)
let rec vpound x y = match x,y with (* take/reshape *)
  | KInteger x, KList y -> KList (atake x y)
  | KInteger x, KCharArray y -> KCharArray (atake x y)
  | KInteger x, KIntegerArray y -> KIntegerArray (atake x y)
  | KInteger x, KSymbolArray y -> KSymbolArray (atake x y)
  | KInteger x, KFloatArray y -> KFloatArray (atake x y)
  | KInteger x, KChar y -> KCharArray(Array.make (abs x) y)
  | KInteger x, KInteger y -> KIntegerArray(Array.make (abs x) y)
  | KInteger x, KSymbol y -> KSymbolArray(Array.make (abs x) y)
  | KInteger x, KFloat y -> KFloatArray(Array.make (abs x) y)
  | KIntegerArray x, KList y -> let nx = len x and  ny = len y in reshape_k x nx y ny
  | KIntegerArray x, KCharArray y -> reshape_v x y kchararray
  | KIntegerArray x, KIntegerArray y -> reshape_v x y kintegerarray
  | KIntegerArray x, KSymbolArray y -> reshape_v x y ksymbolarray
  | KIntegerArray x, KFloatArray y -> reshape_v x y kfloatarray
  | KIntegerArray x, KChar y -> reshape_v x [|y|] kchararray
  | KIntegerArray x, KInteger y -> reshape_v x [|y|] kintegerarray
  | KIntegerArray x, KSymbol y -> reshape_v x [|y|] ksymbolarray
  | KIntegerArray x, KFloat y -> reshape_v x [|y|] kfloatarray
  | KInteger 0, _ -> KList [||]
  | KList x, _ -> vpound (kintegerarray (try amap x kinteger_prj with _ -> raise KError_type)) y
  | _ -> raise KError_type
let vpound_m x = KInteger (klen x) (* length *)
let vlodash x y = match x,y with (* drop *)
  | KInteger x, KList y -> KList (adrop x y)
  | KInteger x, KCharArray y -> KCharArray (adrop x y)
  | KInteger x, KIntegerArray y -> KIntegerArray (adrop x y)
  | KInteger x, KSymbolArray y -> KSymbolArray (adrop x y)
  | KInteger x, KFloatArray y -> KFloatArray (adrop x y)
  | KIntegerArray x, KList y -> KList (acut x y klist)
  | KIntegerArray x, KCharArray y -> KList (acut x y kchararray)
  | KIntegerArray x, KIntegerArray y -> KList (acut x y kintegerarray)
  | KIntegerArray x, KSymbolArray y -> KList (acut x y ksymbolarray)
  | KIntegerArray x, KFloatArray y -> KList (acut x y kfloatarray)
  | _ -> raise KError_type
let vlodash_m = num_atomic_m (* floor *)
  ~f_int:kinteger
  ~f_float:(comp3 kinteger int_of_float floor)
let vtilde x y = KInteger (if x=y then 1 else 0) (* match *)
let vtilde_m = atomic_m (function (* not / attribute *)
  | KInteger x -> KInteger (if x=0 then 1 else 0)
  | KFloat x -> KInteger (if x=0.0 then 1 else 0)
  | KSymbol s -> raise Not_implemented_attribute (* attribute *)
  | _ -> raise KError_type)
let vdollar _ _ = raise Not_implemented_format (* format / form *)
let vdollar_m = atomic_m (fun k -> KCharArray (explode (fps (fun f -> pp_k f k)))) (* format *)
let vquestion x y = match x,y with (* find / function inverse *)
  | KNil, _ -> KInteger 1
  | KList x, y -> KInteger (afindi x y)
  | KIntegerArray x, KInteger y -> KInteger (afindi x y)
  | KIntegerArray x, _ -> KInteger (len x)
  | KCharArray x, KChar y -> KInteger (afindi x y)
  | KCharArray x, _ -> KInteger (len x)
  | KSymbolArray x, KSymbol y -> KInteger (afindi x y)
  | KSymbolArray x, _ -> KInteger (len x)
  | KFloatArray x, KFloat y -> KInteger (afindi x y)
  | KFloatArray x, _ -> KInteger (len x)
  | KFunction f, y ->
    let f = match f with
       | FMonadDyadTriadTetrad (f,_,_,_) | FMonadDyadTriad (f,_,_) | FMonadDyad (f,_) | FMonad f ->
        (fun x -> match f (kfloat x) with
          | KFloat x -> x
          | KInteger x -> float_of_int x
          | _ -> raise KError_type)
      | _ -> raise KError_valence in
   float_atomic_m (fun y ->
    KFloat (secant_root ~f:(fun x -> (f x) -. y) ~x0:0.9999 ~x1:0.9998
                        ~tolerance:(config.approx_tolerance *. y)
                        ~max_iter:config.approx_iter)) y
  | _ -> raise KError_type
let vquestion_t f y x = (* function inverse (triadic) *)
  let f = match f with
    | KFunction (FMonadDyadTriadTetrad (f,_,_,_) | FMonadDyadTriad (f,_,_) | FMonadDyad (f, _) | FMonad f) ->
      (fun x -> match f (kfloat x) with
        | KFloat x -> x
        | KInteger x -> float_of_int x
        | _ -> raise KError_type)
    | KFunction _ -> raise KError_valence
    | _ -> raise KError_type in
  float_atomic_d2 (fun x y ->
    KFloat (secant_root ~f:(fun x -> (f x) -. y) ~x0:x ~x1:(0.9999*.x)
                          ~tolerance:(config.approx_tolerance *. y)
                          ~max_iter:config.approx_iter)) x y
let vquestion_m = not_atomic_m (* range *)
  ~f_k:(fun xs -> KList (range_k xs))
  ~f_char:(fun xs -> KCharArray (range_char xs))
  ~f_int:(fun xs -> KIntegerArray (range_int xs))
  ~f_sym:(fun xs -> KSymbolArray (range_sym xs))
  ~f_float:(fun xs -> KFloatArray (range_float xs))
let rec vat x y = match x,y with
  | KList x,         KInteger y               -> aget x y
  | KIntegerArray x, KInteger y               -> KInteger (aget x (y))
  | KFloatArray x,   KInteger y               -> KFloat (aget x (y))
  | KCharArray x,    KInteger y               -> KChar (aget x (y))
  | KSymbolArray x,  KInteger y               -> KSymbol (aget x (y))
  | KList x,         KIntegerArray y          -> kvec (amap y (aget x))
  | KIntegerArray x, KIntegerArray y          -> KIntegerArray (amap y (aget x))
  | KFloatArray x,   KIntegerArray y          -> KFloatArray (amap y (aget x))
  | KCharArray x,    KIntegerArray y          -> KCharArray (amap y (aget x))
  | KSymbolArray x,  KIntegerArray y          -> KSymbolArray (amap y (aget x))
  | _,               KList y                  -> kvec (amap y (vat x))
  | KDictionary d,   KSymbol s                -> dgetv_or_nil d s
  | KDictionary d,   y when (not (is_atom y)) -> atomic_m (vat (KDictionary d)) y
  | KSymbol s,       y                        -> (match kgets_exn s with
                                                   | exception Not_found -> raise KError_domain
                                                   | KFunction f -> kfmonad_prj (KFunction f) y
                                                   | x -> vat x y)
  | KFunction _, y                            -> kfmonad_prj x y
  | _,               KNil                     -> x
  | _                                         -> raise KError_type
let vat_m x = KInteger (if is_atom x then 1 else 0)
let vat_t_aux d i f = match d with (* amend item (monad) *)
  | KList d ->
    let rec loop i = match i with
        | KInteger i -> d.(i) <- f d.(i)
        |_ -> if is_atom i then raise KError_type else kiter_with loop i
      in kiter_with loop i; kvec d
  | KDictionary d ->
    let rec loop i = match i with
      | KSymbol s -> dsetv d s (f (dgetv_or_nil d s))
      |_ -> if is_atom i then raise KError_type else kiter_with loop i
    in kiter_with loop i; KDictionary d
  | _ -> assert false
let vat_t d i f = let f = kfmonad_prj f in match d with
  | KSymbol s -> ksetsv_ret s (vat_t_aux (kcopy_deep_box @@ try kgets_exn s with Not_found -> raise KError_domain) i f)
  | _ -> vat_t_aux (kcopy_deep_box d) i f
let vat_q_aux d i f y = match d with (* amend item (dyad) *)
  | KList d ->
   let rec loop i y = match i with
      | KInteger i -> let k=f d.(i) y in (try d.(i) <- k with _ -> raise KError_index)
      | i when not (is_atom i) -> kiter2_with loop i y
      | _ -> raise KError_type
    in kiter2_with loop i y; kvec d
  | KDictionary d ->
    let rec loop i y = match i with
     | KSymbol s -> dsetv d s (f (dgetv_or_nil d s) y)
     | i when not (is_atom i) -> kiter2_with loop i y
     | _ -> raise KError_type
   in kiter2_with loop i y; KDictionary d
  | _ -> assert false
let vat_q_assign h i f y = ksethv_ret h (vat_q_aux (kcopy_deep_box @@ try kgeth_exn h with Not_found -> raise KError_domain) i f y)
let vat_q d i f y = let f = kfdyad_prj f in match d with
  | KSymbol s -> ksetsv_ret s (vat_q_aux (kcopy_deep_box @@ try kgets_exn s with Not_found -> raise KError_domain) i f y)
  | _ -> vat_q_aux (kcopy_deep_box d) i f y
let vdot_aux d i =
  let n = len i in let rec loop d f r = (* TODO/FIXME:not sufficiently polymorphic (w.r.t. shape); ex: .[1 2 3;0 1] *)
    if f = KNil && r<n then (match d with
      | KDictionary d -> let d'=dmake (H.length d) in
        H.iter (fun k {value;attr} -> dset d' k {value=loop value i.(r) (r+1);attr}) d;KDictionary d'
      | _ -> each_mm (fun d -> loop d i.(r) (r+1)) d)
    else if f = KNil && r=n then d
    else if r=n then vat d f
    else if is_atom f then loop (vat d f) i.(r) (r+1)
    else each_mm (fun f -> loop d f r) f
  in loop d i.(0) 1
let rec vdot x y = match x,y with (* apply / index / of *)
  | KFunction(FNary (n,f)),KList x     -> let m=len x in if m=n then f x
                                          else if m<n then partial_app_nary_prefix f n m x else raise KError_valence
  | KFunction f,    KList [|x|]        -> (fmonad_prj f) x
  | KFunction f,    KList [|x;y|]      -> (fdyad_prj f) x y
  | KFunction f,    KList [|x;y;z|]    -> (ftriad_prj f) x y z
  | KFunction f,    KList [|x;y;z;u|]  -> (ftetrad_prj f) x y z u
  | KFunction f,    KIntegerArray y    -> vdot x (klist(amap y kinteger))
  | KFunction f,    KCharArray y       -> vdot x (klist(amap y kchar))
  | KFunction f,    KFloatArray y      -> vdot x (klist(amap y kfloat))
  | KFunction f,    KSymbolArray y     -> vdot x (klist(amap y ksymbol))
  | KFunction f,    _                  -> (kfmonad_prj x) y
  | KSymbol s,      _                  -> (try vdot (kgets_exn s) y with Not_found -> KNil)
  | _,(KChar _|KFloat _|KCharArray _|KFloatArray _|KDictionary _) -> raise KError_type
  | _,(KNil|KIntegerArray[||]|KSymbolArray[||]|KList[||]) -> x
  | KIntegerArray x,KIntegerArray y    -> KIntegerArray (Array.map (aget x) y)
  | KCharArray x,   KIntegerArray y    -> KCharArray (Array.map (aget x) y)
  | KFloatArray x,  KIntegerArray y    -> KFloatArray (Array.map (aget x) y)
  | KSymbolArray x, KIntegerArray y    -> KSymbolArray (Array.map (aget x) y)
  | _,              KIntegerArray y    -> afoldl y ~init:x ~f:(fun x i -> vdot x (KInteger i))
  | _,              KInteger _         -> vat x y
  | _,              KSymbolArray y     -> afoldl y ~init:x ~f:(fun x i -> vdot x (KSymbol i))
  | KDictionary d,  KSymbol s          -> dgetv_or_nil d s
  | _,              KList [|i|]        -> vat x i
  | d,              KList i            -> vdot_aux d i
  | _                                  -> raise KError_type
let vdot_m = function (* make/unmake dictionary *)
  | KDictionary d -> KList (dvalues d)
  | KList xs -> KDictionary (dmakel xs)
  | KSymbol s -> (try kgets_exn s with Not_found -> KNil)
  | _ -> raise KError_type
let rec vdot_t_aux d i f = (* PERF; FIXME: assuming f is pure *)
  let i = match i with
  | KList x -> x | KIntegerArray i -> amap i kinteger | KSymbolArray i -> amap i ksymbol
  | KCharArray _ | KFloatArray _ | KDictionary _ ->  raise KError_type
  | (KSymbol _ | KInteger _ | KNil ) -> [|i|]
  | _ -> raise KError_rank in
  let n = len i in let rec loop d h t = (* invariant: d is either a list or a dict, and mutating it is the right thing to do *)
    if h = KNil && t < n then (match d with
      | KDictionary d -> H.iter (fun k {value;attr} -> loop value i.(t) (t+1)) d
      | KList d -> let m = len d in for j = 0 to m-1 do loop d.(j) i.(t) (t+1); done
      | _ -> assert false)
    else if h = KNil && t = n then (match d with
      | KDictionary d -> H.iter (fun k {value;attr} -> let value = f value in dset d k {value;attr}) d
      | KList d -> let m = len d in for j = 0 to m-1 do d.(j) <- f d.(j); done
      | _ -> assert false)
    else if t=n then ignore(vat_t_aux d h f)
    else if is_atom h then (match d,h with
      | KList d, KInteger j -> loop d.(j) i.(t) (t+1)
      | KDictionary d, KSymbol s -> let ds = dgetv_or_nil d s in dsetv d s ds; loop ds i.(t) (t+1)
      | _ -> raise KError_type)
    else if is_atom h then (match d,h with
      | KList d, KInteger j -> loop d.(j) i.(t) (t+1)
      | KDictionary d, KSymbol s -> loop (dgetv_or_nil d s) i.(t) (t+1))
      else kiter_with (fun i -> loop d i t) h in
  loop d i.(0) 1; kvec_deep d
let vdot_t_assign h i f = ksethv_ret h (vdot_t_aux (kcopy_deep_box @@ try kgeth_exn h with Not_found -> raise KError_domain) i f)
let vdot_t d i f = let f = kfmonad_prj f in match d with (* amend (triad) *)
  | KSymbol s -> ksetsv_ret s (vdot_t_aux (kcopy_deep_box @@ try kgets_exn s with Not_found -> raise KError_domain) i f)
  | _ -> vdot_t_aux (kcopy_deep_box d) i f
let rec vdot_q_aux d i f y = (* PERF; UGLY *)
  let i = match i with
  | KList x -> x | KIntegerArray i -> amap i kinteger | KSymbolArray i -> amap i ksymbol
  | KCharArray _ | KFloatArray _ | KDictionary _ ->  raise KError_type
  | (KSymbol _ | KInteger _ | KNil ) -> [|i|]
  | _ -> raise KError_rank in
  let n = len i in let rec loop d h t y =
    if h = KNil && t < n then (match d with
        | KDictionary d -> kaiter_with (fun y k -> let {value;attr} = dget_exn d k in loop value i.(t) (t+1) y) y (dkeys d)
        | KList d -> kaiter_with (fun y d -> loop d i.(t) (t+1) y) y d
        | _ -> assert false)
    else if h = KNil && t = n then (match d with
        | KDictionary d -> kaiter_with (fun y k -> let {value;attr} = dget_exn d k in dset d k {value=f value y;attr}) y (dkeys d)
        | KList d -> kaiteri_with (fun y dj j -> d.(j) <- f dj y) y d
        | _ -> assert false)
    else if t=n then ignore(vat_q_aux d h f y)
    else if is_atom h then (match d,h with
    | KList d, KInteger j -> loop d.(j) i.(t) (t+1) y
    | KDictionary d, KSymbol s -> loop (dgetv_or_nil d s) i.(t) (t+1) y
    | _ -> raise KError_type)
    else (kiter2_with (fun i y -> loop d i t y) h y)
  in loop d i.(0) 1 y; kvec_deep d
let vdot_q_assign h i f y = ksethv_ret h (vdot_q_aux (kcopy_deep_box @@ try kgeth_exn h with Not_found -> raise KError_domain) i f y)
let vdot_q d i f y = let f = kfdyad_prj f in match d with (* amend (tetrad) *)
  | KSymbol s -> ksetsv_ret s (vdot_q_aux (kcopy_deep_box @@ try kgets_exn s with Not_found -> raise KError_domain) i f y)
  | _ -> vdot_q_aux (kcopy_deep_box d) i f y

(* i/o verbs =============================================================== *)
let unmarshal_symbol x = let x,h = parse_symbol x in s x (match h with HRel _ -> None | _ -> Some h)
let rec marshal_dict d =
  Array.map(fun (KList[|KSymbol s;v;a|])->sname s,marshal_symbols v,match a with KNil -> a|KDictionary d->KSDictionary (marshal_dict d))(dvalues d)
and marshal_symbols k = kmap_rec (function
  | KSymbol x -> KSSymbol (sname x)
  | KSymbolArray x -> KSSymbolArray (amap x sname)
  | KDictionary x -> KSDictionary (marshal_dict x)
  | x -> x) k
let rec unmarshal_dict d =
  dmakel(Array.map(fun (k,v,a)->KList[|KSymbol (unmarshal_symbol k);unmarshal_symbols v;match a with KSDictionary d->KDictionary (unmarshal_dict d)|_->KNil|])d)
and unmarshal_symbols k = kmap_rec (function
  | KSSymbol x -> KSymbol(unmarshal_symbol x)
  | KSSymbolArray x -> KSymbolArray(Array.map unmarshal_symbol x)
  | KSDictionary x -> KDictionary(unmarshal_dict x)
  | x -> x) k
let with_file_in fn f =
  try let ch = open_in fn in try let k = f ch in close_in ch;k with e -> (close_in ch;raise e)
  with Sys_error _ -> raise KError_domain | e -> raise e
let load_file_text_lines f ch = let acc = ref [] in
  try (while true do acc := (f (input_line ch))::!acc; done; raise Exit)
  with End_of_file -> array_of_list_rev !acc
let write_file_text_lines f ls =
  let ch = open_out f and n = len ls in
  for i=0 to n-1 do let lsi = ls.(i) in output_bytes ch (String.init (len lsi) (Array.get lsi));output_char ch '\n'; done; close_out ch
let string_value = function
  KSymbol s -> sname s | KChar c -> String.make 1 c | KCharArray c -> String.init (len c) (fun i -> c.(i)) | _ -> raise KError_type
let trim_quoted s = let n = String.length s in if n>0&&s.[0]='"'&&s.[n-1]='"' then String.sub s 1 (n-2) else s
let parse_field = function
  |'I' -> comp4 some kinteger int_of_string String.trim
  |'F' -> comp4 some kfloat float_of_string String.trim
  |'C' -> comp4 some kchararray explode (comp trim_quoted String.trim)
  |'S' -> comp4 some ksymbol (flip s None) (comp trim_quoted String.trim)
  |' ' -> const None
  | _ -> raise KError_domain
let parse_fixed_width_fields (t:char array) (w:int array) (m:int) (l:string) =
  let i = ref 0 and a = Array.make m KNil and t = Array.map parse_field t in
  let ln = String.length l in
  for j = 0 to m-1 do
    if !i+w.(j)>=ln then raise KError_length
    else (match t.(j) (String.sub l !i w.(j)) with None -> () | Some x -> a.(j) <- x);i:=!i+w.(j);
  done; a
let parse_delimited_fields (t:char array) (s:char) (m:int) (l:string) =
  let i = ref 0 and a = Array.make m KNil and t = Array.map parse_field t in
  let n = len t and ln = String.length l in
  (try for j = 0 to n-1 do
    let k = if j=n-1 then ln
            else let k = ref !i in while !k<ln && l.[!k]!=s do incr k; done; !k in
    if k > ln then raise Exit;
    (match t.(j) (String.sub l !i (k - !i)) with None -> () | Some x -> a.(j) <- x | exception KError_domain -> ());
    i := k+1;
  done with Exit -> ()); a
let vzero_colon_m x = KList (with_file_in (string_value x) (load_file_text_lines (comp kchararray explode)))
let vzero_colon_aux_fw t w ch =
  let m = afoldl ~init:0 ~f:(fun n c -> if c=' ' then n else n+1) t in
  if m <> len w then raise KError_length;
  let rows = load_file_text_lines (parse_fixed_width_fields t w m) ch in
  let m = len t and n = len rows in (Array.init m (fun i -> kvec (Array.init n (fun j -> rows.(j).(i)))))
let vzero_colon_aux_d t s ch =
  let m = afoldl ~init:0 ~f:(fun n c -> if c=' ' then n else n+1) t in
  let rows = load_file_text_lines (parse_delimited_fields t s m) ch in
  let n = len rows in (Array.init m (fun i -> kvec (Array.init n (fun j -> rows.(j).(i)))))
let vzero_colon x y = match x,y with (* PERF: load column-wise, not row-wise + transpose *)
  | KSymbol s0r', (KCharArray _|KChar _) when s0r'=s0r -> Format.printf "%s" (string_value y); KNil
  | KSymbol s0r', KList y when s0r'=s0r -> (aiter y (comp (Format.printf "%s") string_value)); KNil
  | (KChar _ | KCharArray _ | KSymbol _), _ -> (* load text file as line list *)
    write_file_text_lines (string_value x) (match y with
      | KList x -> amap x (function KCharArray c -> c | KChar c -> [|c|] | _ -> raise KError_type)
      | KChar c -> [|[|c|]|] | KCharArray c -> [|c|] | _ -> raise KError_type);
    KNil
  | KList [|KCharArray t;KIntegerArray w|], (KChar _ | KCharArray _ | KSymbol _) ->
    klist @@ with_file_in (string_value y) (vzero_colon_aux_fw t w) (* load text file, fixed-width fields.*)
  | KList [|KCharArray t;KChar s|], (KChar _|KCharArray _|KSymbol _) ->
    klist @@ with_file_in (string_value y) (vzero_colon_aux_d t s)(* load text file, delimited fields *)
  | KList [|KCharArray t;KCharArray [|s|]|], (KChar _|KCharArray _|KSymbol _) -> (* load text file, delimited fields, header*)
    klist @@ with_file_in (string_value y) (fun ch ->
      let m = afoldl ~init:0 ~f:(fun n c -> if c=' ' then n else n+1) t in
      let header = parse_delimited_fields (amap t (function ' '->' '|_->'S')) s m (input_line ch)
      and cols = vzero_colon_aux_d t s ch in [|kvec header;KList cols|])
  | KList [|s;w|], KList [|f;b;n|] -> raise Not_implemented_io (* TODO: offset+length args *)
  | _ -> raise KError_type
let vone_colon_m x = raise Not_implemented_io
let vone_colon x y =
  let f = ensure_suffix ".L" (string_value x) in
  let ch = try open_out_bin f with Sys_error _-> raise KError_domain in
  Marshal.to_channel ch (marshal_symbols y) [Marshal.Closures]; close_out ch; KNil
let vtwo_colon_m x =
  let f = ensure_suffix ".L" (string_value x) in
  let ch = try open_in_bin f with Sys_error _-> raise KError_domain in
  let k:k = try Marshal.from_channel ch with _-> raise KError_nonce in close_in ch; unmarshal_symbols k
let vtwo_colon x y = match y with
  | KList [|KCharArray _;KInteger _|] -> raise Not_implemented_dynlink
  | _ -> vone_colon x y
let vfour_colon_m x = KInteger (match x with
  | KList _ -> 0
  | KInteger _ -> 1    | KIntegerArray _ -> -1
  | KFloat _ -> 2      | KFloatArray _ -> -2
  | KChar _ -> 3       | KCharArray _ -> -3
  | KSymbol _ -> 4     | KSymbolArray _ -> -4
  | KSSymbol _ -> 9    | KSSymbolArray _ -> -9
  | KDictionary _ -> 5 | KNil -> 6
  | KFunction _ -> 7   | KSDictionary _ -> 10)

(* system functions ======================================================== *)
let _pretty x = KCharArray (explode (fps (fun f -> pp_k f x)))
[@@inline always] let _ain x y = if afindi y x < len y then 1 else 0
let _in x y = match x,y with
  | x, KList y -> KInteger (_ain x y)
  | KInteger x, KIntegerArray y -> KInteger (_ain x y)
  | _, KIntegerArray _ -> KInteger 0
  | KFloat x, KFloatArray y -> KInteger (_ain x y)
  | _, KFloatArray _ -> KInteger 0
  | KChar x, KCharArray y -> KInteger (_ain x y)
  | _, KCharArray _ -> KInteger 0
  | KSymbol x, KSymbolArray y -> KInteger (_ain x y)
  | _, KSymbolArray _ -> KInteger 0
  | x,y -> vtilde x y
let _lin x y = match x with
  | KList _|KIntegerArray _|KCharArray _|KSymbolArray _|KFloatArray _ -> KIntegerArray (kmap1 (fun x -> kinteger_prj @@ _in x y) x)
  | _ -> raise KError_domain
let _exp = num_atomic_m ~f_int:(comp kfloat (comp exp float_of_int)) ~f_float:(comp kfloat exp)
let _log = num_atomic_m ~f_int:(comp kfloat (comp log float_of_int)) ~f_float:(comp kfloat log)
let _cos = num_atomic_m ~f_int:(comp kfloat (comp cos float_of_int)) ~f_float:(comp kfloat cos)
let _cosh = num_atomic_m ~f_int:(comp kfloat (comp cosh float_of_int)) ~f_float:(comp kfloat cosh)
let _sin = num_atomic_m ~f_int:(comp kfloat (comp sin float_of_int)) ~f_float:(comp kfloat sin)
let _sinh = num_atomic_m ~f_int:(comp kfloat (comp sinh float_of_int)) ~f_float:(comp kfloat sinh)
let _tan = num_atomic_m ~f_int:(comp kfloat (comp tan float_of_int)) ~f_float:(comp kfloat tan)
let _tanh = num_atomic_m ~f_int:(comp kfloat (comp tanh float_of_int)) ~f_float:(comp kfloat tanh)
let _sqr = num_atomic_m ~f_int:(comp kfloat (comp (fun x->x*.x) float_of_int)) ~f_float:(comp kfloat (fun x->x*.x))
let _sqrt = num_atomic_m ~f_int:(comp kfloat (comp sqrt float_of_int)) ~f_float:(comp kfloat sqrt)
let _ci = atomic_m (function (KChar c) -> KInteger(Char.code c)|_->raise KError_type)
let _ic = atomic_m (function (KInteger i) -> if 0<=i&&i<=255 then KChar(Char.chr i) else raise KError_domain |_->raise KError_type)
let _dot x y = over_dm vplus (vstar x y)
let _mul x y = each_left_dd _dot x y

(* eval ==================================================================== *)
let eval_verb = function
  | VPlus -> FMonadDyad(vplus_m, vplus)
  | VMinus -> FMonadDyad(vminus_m, vminus)
  | VStar -> FMonadDyad(vstar_m, vstar)
  | VExclaim -> FMonadDyad(vexclaim_m, vexclaim)
  | VPercent -> FMonadDyad(vpercent_m, vpercent)
  | VPipe -> FMonadDyad(vpipe_m, vpipe)
  | VAmpersand -> FMonadDyad(vampersand_m, vampersand)
  | VCircumflex -> FMonadDyad(vcircumflex_m, vcircumflex)
  | VLangle -> FMonadDyad(vlangle_m, vlangle)
  | VRangle -> FMonadDyad(vrangle_m, vrangle)
  | VEquals -> FMonadDyad(vequals_m, vequals)
  | VPound -> FMonadDyad(vpound_m, vpound)
  | VLodash -> FMonadDyad(vlodash_m, vlodash)
  | VTilde -> FMonadDyad(vtilde_m, vtilde)
  | VDollar -> FMonadDyad(vdollar_m, vdollar)
  | VQuestion -> FMonadDyadTriad(vquestion_m, vquestion, vquestion_t)
  | VAt -> FMonadDyadTriadTetrad(vat_m, vat, vat_t, vat_q)
  | VDot -> FMonadDyadTriadTetrad(vdot_m, vdot, vdot_t, vdot_q)
  | VComma -> FMonadDyad(vcomma_m, vcomma)
  | VZeroColon -> FMonadDyad (vzero_colon_m,vzero_colon)
  | VOneColon -> FMonadDyad (vone_colon_m,vone_colon)
  | VTwoColon -> FMonadDyad (vtwo_colon_m,vtwo_colon)
  | VThreeColon -> FMonadDyad ((fun _ -> raise Not_implemented_io),(fun _ _ -> raise Not_implemented_io))
  | VFourColon -> FMonadDyad (vfour_colon_m,(fun _ _ -> raise Not_implemented_io))
  | VFiveColon -> FMonadDyad ((fun _ -> raise Not_implemented_io),(fun _ _ -> raise Not_implemented_io))
let eval_verb_m = function
  | VPlus->FMonad vplus_m|VMinus->FMonad vminus_m|VStar->FMonad vstar_m|VExclaim->FMonad vexclaim_m|VPercent->FMonad vpercent_m|VPipe->FMonad vpipe_m
  | VAmpersand->FMonad vampersand_m|VCircumflex->FMonad vcircumflex_m|VLangle->FMonad vlangle_m|VRangle->FMonad vrangle_m|VEquals->FMonad vequals_m
  | VPound->FMonad vpound_m|VLodash->FMonad vlodash_m|VTilde->FMonad vtilde_m|VDollar->FMonad vdollar_m|VQuestion->FMonad vquestion_m|VAt->FMonad vat_m
  | VDot->FMonad vdot_m|VComma->FMonad vcomma_m|VZeroColon->FMonad vzero_colon_m|VOneColon ->FMonad vone_colon_m|VTwoColon->FMonad vtwo_colon_m
  | VThreeColon -> raise Not_implemented_io
  | VFourColon -> FMonad vfour_colon_m
  | VFiveColon -> raise Not_implemented_io
let eval_adverb av f = match av,f with (* TODO: once we have n-ary adverbs, this will have to be adapted. *)
  | AVForwardslash, FMonad f -> FMonadDyad(over_mm f,over_md f)
  | AVForwardslash, (FDyad f|FMonadDyad(_,f)|FMonadDyadTriad(_,f,_)|FMonadDyadTriadTetrad(_,f,_,_)) -> FMonadDyad(over_dm f,over_dd f)
  | AVForwardslash, _ -> raise KError_valence
  | AVForwardslashColon, FMonad _ -> raise KError_valence
  | AVForwardslashColon, (FDyad f|FMonadDyad(_,f)|FMonadDyadTriad(_,f,_)|FMonadDyadTriadTetrad(_,f,_,_)) -> FDyad(each_right_dd f)
  | AVForwardslashColon, _ -> raise KError_valence
  | AVBackslash, (FMonadDyad (_,f) | FMonadDyadTriad (_,f,_) | FMonadDyadTriadTetrad (_,f,_,_)) -> FMonadDyad(scan_dm f,scan_dd f)
  | AVBackslash, FMonad f -> FMonadDyad(scan_mm f,scan_md f)
  | AVBackslash, _ -> raise KError_valence
  | AVBackslashColon, FMonad f -> raise KError_valence
  | AVBackslashColon, (FDyad f|FMonadDyad(_,f)|FMonadDyadTriad(_,f,_)|FMonadDyadTriadTetrad(_,f,_,_)) -> FDyad(each_left_dd f)
  | AVBackslashColon, _ -> raise KError_valence
  | AVQuote, FMonad f -> FMonad(each_mm f)
  | AVQuote, FDyad f -> FDyad(each_dd f)
  | AVQuote, (FMonadDyad(fm,fd)|FMonadDyadTriad(fm,fd,_)|FMonadDyadTriadTetrad(fm,fd,_,_)) -> FMonadDyad(each_mm fm,each_dd fd)
  | AVQuote, _ -> raise KError_valence
  | AVQuoteColon, FMonad f -> raise KError_valence
  | AVQuoteColon, (FDyad f|FMonadDyad (_,f)|FMonadDyadTriad (_,f,_)|FMonadDyadTriadTetrad (_,f,_,_)) -> FMonad(each_pair_dm f)
  | AVQuoteColon, _ -> raise KError_valence
let eval_app f args = (* UGLY *)
  match f, args with
  | FNilad f,                         Ka0                   -> f ()
  | FNilad _,                         _                     -> raise KError_valence
  | FMonad f,                         Ka1 x                 -> f x
  | FMonad _,                         _                     -> raise KError_valence
  | FMonadDyad (fm,_),                Ka1 x                 -> fm x
  | FMonadDyad (_,fd),                Ka2 (x,y)             -> fd x y
  | FMonadDyad (_,fd),                Kap (2,ks,is,js)      -> partial_app_dyad fd ks is
  | FMonadDyad _,                     _                     -> raise KError_valence
  | FDyad f,                          Ka2 (x,y)             -> f x y
  | FDyad f,                          Ka1 x                 -> KFunction (FMonad (f x))
  | FDyad f,                          Kap (2,ks,is,_)       -> partial_app_dyad f ks is
  | FDyad _,                          _                     -> raise KError_valence
  | FMonadDyadTriad (fm,_,_),         Ka1 x                 -> fm x
  | FMonadDyadTriad (_,fd,_),         Ka2 (x,y)             -> fd x y
  | FMonadDyadTriad (_,_,ft),         Ka3 (x,y,z)           -> ft x y z
  | FMonadDyadTriad (_,fd,_),         Kap (2,ks,is,_)       -> partial_app_dyad fd ks is
  | FMonadDyadTriad (_,_,ft),         Kap (3,ks,is,js)      -> partial_app_triad ft ks is
  | FMonadDyadTriad _,        _                             -> raise KError_valence
  | FMonadDyadTriadTetrad (fm,_,_,_), Ka1 x                 -> fm x
  | FMonadDyadTriadTetrad (_,fd,_,_), Ka2 (x,y)             -> fd x y
  | FMonadDyadTriadTetrad (_,_,ft,_), Ka3 (x,y,z)           -> ft x y z
  | FMonadDyadTriadTetrad (_,_,_,fq), Ka [|x;y;z;u|]        -> fq x y z u
  | FMonadDyadTriadTetrad (_,fd,_,_), Kap (2,ks,is,_)       -> partial_app_dyad fd ks is
  | FMonadDyadTriadTetrad (_,_,ft,_), Kap (3,ks,is,js)      -> partial_app_triad ft ks is
  | FMonadDyadTriadTetrad (_,_,_,fq), Kap (4,ks,is,js)      -> partial_app_tetrad fq ks is
  | FMonadDyadTriadTetrad _,          _                     -> raise KError_valence
  | FTriad f,                         Ka3 (x,y,z)           -> f x y z
  | FTriad f,                         Ka1 x                 -> KFunction (FDyad (f x))
  | FTriad f,                         Ka2 (x,y)             -> KFunction (FMonad (f x y))
  | FTriad f,                         Kap ((2|3),ks,is,js)  -> partial_app_triad f ks is
  | FTriad _,                         _                     -> raise KError_valence
  | FNary (n,fn),                     Ka0                   -> KFunction f
  | FNary (n,fn),                     Ka1 x                 -> partial_app_nary_prefix fn n 1 [|x|]
  | FNary (n,fn),                     Ka2(x,y)              -> partial_app_nary_prefix fn n 2 [|x;y|]
  | FNary (n,fn),                     Ka3(x,y,z)            -> partial_app_nary_prefix fn n 3 [|x;y;z|]
  | FNary (n,fn),                     Ka xs                 -> let m = len xs in if n<m then raise KError_valence else
                                                               if n>m then partial_app_nary_prefix fn n m xs
                                                               else fn xs
  | FNary (n,fn),                     Kap (m,ks,is,js)      -> if m<=n then partial_app_nary fn n ks is js
                                                               else raise KError_valence
let eval_builtin s =
  if s=s_n then KNil
  else if s=s_pretty then KFunction (FMonad _pretty)
  else if s=s_in then KFunction (FDyad _in)
  else if s=s_lin then KFunction (FDyad _lin)
  else if s=s_exp then KFunction (FMonad _exp)
  else if s=s_log then KFunction (FMonad _log)
  else if s=s_cos then KFunction (FMonad _cos)
  else if s=s_cosh then KFunction (FMonad _cosh)
  else if s=s_sin then KFunction (FMonad _sin)
  else if s=s_sinh then KFunction (FMonad _sinh)
  else if s=s_tan then KFunction (FMonad _tan)
  else if s=s_tanh then KFunction (FMonad _tanh)
  else if s=s_sqrt then KFunction (FMonad _sqrt)
  else if s=s_sqr then KFunction (FMonad _sqr)
  else if s=s_ci then KFunction (FMonad _ci)
  else if s=s_ic then KFunction (FMonad _ic)
  else if s=s_dot then KFunction (FDyad _dot)
  else if s=s_mul then KFunction (FDyad _mul)
  else raise Not_implemented_builtins
let local_env () = H.create config.local_env_hash_size
let rec eval = function
  | ENil -> KNil
  | EColon -> KNil
  | ELiteral k -> k
  | ENameSys s -> eval_builtin s
  | EName (HAbs h) -> (try kgetl_abs_exn h with Not_found -> KNil)
  | EName (HRel h) -> (try kgetl_rel_exn h with Not_found -> KNil)
  | EVerb v -> KFunction (eval_verb v)
  | EComp(e,e') -> eval (ELambda ([|sx|],EApp(e,Ea1(EApp(e',Ea1(EName (HRel [sx])))))))
  | EVerbMonadic v -> KFunction (eval_verb_m v)
  | ELambda (args, body) ->
      let d=local_env() in let ds = d::!ktree_env in
      KFunction (match args with (* FIXME/UGLY: duplication *)
      | [||] -> FNilad (fun () -> ktree_in ds @@ fun () -> try eval body with KReturn k -> k)
      | [|x|] -> FMonad (fun _x -> dsetv d x _x; ktree_in ds @@ fun () -> try eval body with KReturn k -> k)
      | [|x;y|] -> FDyad (fun _x _y -> dsetv d x _x;dsetv d y _y; ktree_in ds @@ fun () -> try eval body with KReturn k -> k)
      | [|x;y;z|] -> FTriad (fun _x _y _z -> dsetv d x _x;dsetv d y _y; dsetv d z _z; ktree_in ds @@ fun () -> try eval body with KReturn k -> k)
      | xs -> let n = len xs in FNary(n, fun _xs -> aiter2_ xs _xs n (fun x _x -> dsetv d x _x); ktree_in ds @@ fun () -> try eval body with KReturn k -> k))
  | EApp(EVerb VAt,Ea [|d;i;EColon;y|]) -> (* FIXME/UGLY: hack to make @[d;i;f;:;y] work *)
    eval (EApp(EVerb VAt,Ea [|d;i;ELiteral (KFunction (FDyad (flip const)));y|]))
  | EApp(EVerb VDot,Ea [|d;i;EColon;y|]) -> (* FIXME/UGLY: hack to make .[d;i;f;:;y] work *)
    eval (EApp(EVerb VDot,Ea [|d;i;ELiteral (KFunction (FDyad (flip const)));y|]))
  | EApp (f,args) -> (match eval f with
      | KFunction f -> eval_app f (eval_args args)
      | KNil -> k_of_kargs(eval_args args)
      | (KIntegerArray [||]|KCharArray [||]|KSymbolArray [||]|KFloatArray [||]|KList [||]) as x -> x
      | (KIntegerArray _|KCharArray _|KSymbolArray _|KFloatArray _|KList _|KDictionary _) as d -> vdot d (klist_of_kargs(eval_args args))
      | _ -> raise KError_rank)
  | EAdverb (av,f) -> (match eval f with
      | KFunction f -> KFunction (eval_adverb av f)
      | KNil -> KFunction (eval_adverb av (FMonad id)) (* FIXME: identity-function semantics of nil *)
      | _ -> raise KError_type)
  | EAssign (h,e) -> ksethv_ret h (eval e)
  | EAssignGlobal (h,e) -> let k = eval e in (match !ktree_env with (c::p::t) -> ktree_env:=(p::t);ksethv h k;ktree_env:=c::p::t;k|_->ksethv_ret h k)
  | EAssignIndex (h,[|e|],e') -> vat_q_assign h (eval e) (flip const) (eval e') (* FIXME: return changed items only *)
  | EAssignIndex (h,es,e) -> vdot_q_assign h (KList (amap es (eval))) (flip const) (eval e) (* FIXME: return changed items only *)
  | EAssignIndexMonad (h,es,e) -> vdot_t_assign h (KList (amap es (eval))) (kfmonad_prj (eval e)) (* FIXME: return changed items only *)
  | EAssignIndexDyad (h,es,e,e') -> vdot_q_assign h (KList (amap es (eval))) (kfdyad_prj (eval e)) (eval e') (* FIXME: return changed items only *)
  | EAssignMonad (h,e) -> ksethv_ret h (match eval e with
      | KFunction (FMonadDyadTriadTetrad (f,_,_,_) | FMonadDyadTriad (f,_,_) | FMonadDyad (f,_) | FMonad f) ->  f (kgeth_or_nil h)
      | KFunction (FNilad _) -> raise KError_valence
      | KFunction f -> eval_app f (Ka1 (kgeth_or_nil h))
    | _ -> raise KError_type)
  | EAssignDyad (h,e,e') -> ksethv_ret h (match eval e with
      | KFunction (FMonadDyadTriadTetrad (_,f,_,_) | FMonadDyadTriad (_,f,_) | FMonadDyad (_,f) | FDyad f) ->  f (kgeth_or_nil h) (eval e')
      | KFunction (FNilad _| FMonad _) -> raise KError_valence
      | KFunction f -> eval_app f (Ka2 (kgeth_or_nil h,eval e'))
    | _ -> raise KError_type)
  | EList es -> kvec (Array.of_list (List.map (eval) es))
  | ESeq (e,e') -> ignore(eval e); eval e'
  | EIfMulti (_ifs,_thens,_else) -> let n = len _ifs in (try for i = 0 to n-1 do
      match eval _ifs.(i) with KInteger 0 -> () | KInteger _ -> raise (Return (eval _thens.(i))) | _ -> raise KError_type
    done; eval _else with Return k -> k)
  | EIfSimple (_if,_then,_else) ->
      (match eval _if with KInteger 0 -> eval _else | KInteger _ -> eval _then | _ -> raise KError_type)
  | EReturn e -> let k = eval e in raise (KReturn k)
and eval_args = function
  | Ea0 -> Ka0
  | Ea1 e -> Ka1 (eval e)
  | Ea2 (ENil,ENil) -> Kap (2,[||],[||],[|0;1|])
  | Ea2 (ENil, e) -> Kap (2,[|eval e|],[|1|],[|0|])
  | Ea2 (e,ENil) -> Kap (2,[|eval e|],[|0|],[|1|])
  | Ea2 (e,e') -> Ka2 (eval e, eval e')
  | Ea3 (ENil,ENil,ENil) -> Kap (3,[||],[||],[|1;2;3|])
  | Ea3 (ENil,ENil,e) -> Kap (3,[|eval e|],[|2|],[|0;1|])
  | Ea3 (ENil,e,ENil) -> Kap (3,[|eval e|],[|1|],[|0;2|])
  | Ea3 (e,ENil,ENil) -> Kap (3,[|eval e|],[|0|],[|1;2|])
  | Ea3 (ENil,e,e') -> Kap (3,[|eval e;eval e'|],[|1;2|],[|0|])
  | Ea3 (e,ENil,e') -> Kap (3,[|eval e;eval e'|],[|0;2|],[|1|])
  | Ea3 (e,e',ENil) -> Kap (3,[|eval e;eval e'|],[|0;1|],[|2|])
  | Ea3 (e,e',e'') -> Ka3 (eval e, eval e',eval e'')
  | Ea es -> let n = len es in let rec loop i ks is js =
              if i=n then (let ks = array_of_list_rev ks in if js=[] then Ka ks else Kap(n,ks,array_of_list_rev is,array_of_list_rev js))
              else let e = es.(i) in if es.(i) = ENil then loop (i+1) ks is (i::js)
              else loop (i+1) (eval e::ks) (i::is) js
             in loop 0 [] [] []

let eval_file = ref (fun _ -> raise Exit) (* NB. Forward dependency on parser. *)
let rec eval_command = function (* UGLY,FIXME: workspace save/load *)
  | CEval e -> eval e
  | CExit -> raise KExit
  | CPwd -> Format.printf "%a\n" pp_h (HAbs !ktree_pwdh);KNil
  | CCd h -> let d = (match kgeth_exn h with
      | KDictionary d -> d
      | _ -> raise KError_type
      | exception Not_found -> (let d = dmake config.hash_size in ksethv h (KDictionary d); d))
    in ktree_cd d;ktree_pwd:=d;ktree_set_pwdh h; KNil
  | CLoad f -> !eval_file f; KNil
  | CWsLoad None -> eval_command (CWsLoad (Some config.workspace_name))
  | CWsSave None -> eval_command (CWsSave (Some config.workspace_name))
  | CWsSave (Some f) -> let fa=KCharArray(explode f) in let _ = vone_colon fa (kgeth_exn (HAbs [])) in config.workspace_name<-f; fa
  | CWsLoad (Some f) -> let fa=KCharArray(explode f) in ktree:=kdictionary_prj(vtwo_colon_m fa);
                        let k=kdictionary_prj(kgeth_exn(HAbs[s_k]))
                        in ktree_env:=[k];ktree_pwd:=k;ktree_pwdh:=[s_k];config.workspace_name<-f;fa
  | CWsSize -> raise Not_implemented_builtins
let rec eval_commands = function
  | [] -> KNil
  | [c] -> eval_command c
  | c::cs -> ignore (eval_command c); eval_commands cs
(* parse =================================================================== *)
(* NB. parsing is a bit of a mess again, but can be cleaned up with a moderate
       amount of effort once it makes sense to do so. *)
open Lexer
open Tinyparse
let args3 = [|sx;sy;sz|] and args2 = [|sx;sy|] and args1 = [|sx|] and args0 = [||]
let infer_args e =
  let x = ref false and y = ref false and z = ref false in
  let name = function
    | HRel(n::_) -> if n = sx then x:=true else if n = sy then y:=true else if n = sz then z:=true
    | _ -> () in
  let rec loop e = match e with
  (* | ELambda([||],e) -> loop e *)
  | ELambda _ -> ()
  | EApp(e,ea) -> loop e; (match ea with Ea0->()|Ea1 e->loop e|Ea2(e,e')->loop e;loop e'|Ea3 (e,e',e'') -> loop e;loop e';loop e''|Ea es->aiter es loop)
  | EList es -> List.iter loop es
  | EAssignGlobal(_,e) | EAdverb(_,e) | EReturn e -> loop e
  | EComp(e,e') | ESeq(e,e') -> loop e; loop e'
  | EIfSimple(i,t,e) -> loop i; loop t; loop e
  | EIfMulti(i,t,e) -> Array.iter loop i; Array.iter loop t; loop e
  | EAssign(h,e)| EAssignMonad(h,e) -> name h; loop e
  | EAssignDyad(h,e,e') -> name h;loop e; loop e'
  | EAssignIndex(h,es,e) | EAssignIndexMonad(h,es,e) -> name h; Array.iter loop es; loop e
  | EAssignIndexDyad(h,es,e,e') -> name h; Array.iter loop es; loop e; loop e'
  | EName h -> name h
  | ENameSys _ |EVerb _ |EVerbMonadic _ |ELiteral _ |ENil|EColon -> ()
  in loop e; if !z then args3 else if !y then args2 else if !x then args1 else args0
let verb = function
  |PLUS->VPlus|MINUS->VMinus|STAR->VStar|EXCLAIM->VExclaim|PERCENT->VPercent
  |PIPE->VPipe|AMPERSAND->VAmpersand|CIRCUMFLEX->VCircumflex|LANGLE->VLangle
  |RANGLE->VRangle|EQUALS->VEquals|POUND->VPound|LODASH->VLodash|TILDE->VTilde
  |DOLLAR->VDollar|QUESTION->VQuestion|AT->VAt|DOT->VDot|COMMA->VComma|_->fail()
let adverb = function
  |FORWARDSLASH->AVForwardslash|FORWARDSLASHCOLON->AVForwardslashColon
  |BACKSLASH->AVBackslash|BACKSLASHCOLON->AVBackslashColon|QUOTE->AVQuote
  |QUOTECOLON->AVQuoteColon|_->fail()
let tstring = tm (function STRING s -> s|_->fail())
let psymbol = t BACKTICK |>^ choice [tstring |>> (fun x -> s x None);
                                     phandle |>> function (x,h) -> s x (match h with HRel _ -> None | _ -> Some h)]
let psymbols = seq1 (psymbol |^> skip ws) |>> (function [s] -> KSymbol s | a -> KSymbolArray (Array.of_list a))
let one_many one many = function [x] -> one x | xs -> many xs
let pnums = seq_fold_token ~init:(`I []) ~f:(fun acc x -> match acc, x with
  | `I xs, INT i -> `I(i::xs)
  | `I xs, FLOAT i -> `F(i::(List.map float_of_int xs))
  | `F xs, FLOAT f -> `F(f::xs)
  | `F xs, INT i -> `F((float_of_int i) :: xs)
  | _, WS -> acc | _ -> fail())
  |>> function
    | `I[x] -> KInteger x | `I(x::xs) -> KIntegerArray (array_of_list_rev (x::xs))
    | `F[x] -> KFloat x | `F(x::xs) -> KFloatArray (array_of_list_rev (x::xs))
    |  _ -> fail()
let pchars = tstring |>> (fun s -> match explode s with [|c|] -> KChar c | cs -> KCharArray cs)
let pvector = choice [pnums; psymbols; pchars] |>> eliteral
let padverbs init = seq_fold (tm adverb) ~init ~f:(flip eadverb)
let ioverb = function INT 0->VZeroColon|INT 1->VOneColon|INT 2->VTwoColon|INT 3->VThreeColon|INT 4->VFourColon|INT 5->VFiveColon|_->fail()
let pverb = choice[tm verb >>= (fun v -> choice[t COLON|>^return(EVerbMonadic v);return (EVerb v)]) >>= padverbs; tm ioverb |>> everb |^> t COLON]
let pname = phandle |>> comp ename snd
let psysname = tm (function SYSNAME i -> i |_->fail()) |>> fun h -> s h None
let psysname_dyad = psysname |>> (fun n -> try let _=kfdyad_prj (eval_builtin n)in n with _->fail())
let bracket x = tws LBRACKET |>^ x |^> tws RBRACKET
let paren x = tws LPAREN |>^ x |^> tws RPAREN
let brace x = tws LBRACE |>^ x |^> tws RBRACE
let pargs = function ([]|[ENil]) -> Ea0 |[x] -> Ea1 x |[x;y] -> Ea2 (x,y)|[x;y;z] -> Ea3 (x,y,z)|xs -> Ea (Array.of_list xs)
let formals = bracket (sep (tws SEMI) (tname |^> skip ws |>> flip s None)) |>> Array.of_list
let eif = function [i;t;e] -> EIfSimple(i,t,e) | ([]|[_]|[_;_]) -> fail () | es ->
  let rec loop ifs thens = function
  | [] -> EIfMulti(array_of_list_rev ifs,array_of_list_rev thens,ENil)
  | [e] -> EIfMulti(array_of_list_rev ifs,array_of_list_rev thens,e)
  | i::t::es -> loop (i::ifs) (t::thens) es
  in loop [] [] es
let rec expr s = choice[choice [
  tws LPAREN |>^ tws RPAREN |>> const (EList []);paren expr;
  pipe4 ((phandle |>> snd) |^> skip ws) (eindex |^> skip ws) eassignf expr eassignindexdyad;
  pipe3 ((phandle |>> snd) |^> skip ws) (eindex |^> skip ws) eassignf eassignindexmonad;
  pipe3 ((phandle |>> snd)) (eindex|^>tws COLON ) expr eassignindex;
  pipe3 ((phandle |>> snd) |^> skip ws) eassignf expr eassigndyad;
  pipe2 ((phandle |>> snd) |^> ws) eassignf eassignmonad;
  t COLON |>^ bracket (sep_empty (tws SEMI) (expr|^>skip ws) ENil) |>> eif;
  pipe2 ((phandle |>> snd) |^> skip ws |^> tws COLONCOLON) expr eassignglobal;
  pipe2 ((phandle |>> snd) |^> skip ws |^> tws COLON) expr eassign;
  expr_lambda >>= padverbs;
  pverb |^>^ pverb >>= (fun (e,e') -> seq_fold pverb ~f:ecomp ~init:(ecomp e e'));
  pname; pipe2 (pverb |^> skip ws) expr (fun v e -> EApp(v,Ea1 e));
  tws COLON |>^ expr |>> ereturn;
  psysname |>> enamesys >>= padverbs;pverb>>=padverbs;pvector;expr_list;tws BACKTICK|>>const(ELiteral(KSymbol s0r))] >>= more_expr;tws COLON|>^return EColon;] s
and more_expr left = skip ws |>^ choice [
  bracket (sep_empty (tws SEMI) (expr|^>skip ws) ENil) |>> pargs |>> eapp left >>= more_expr;
  pipe2 (tm adverb) expr (fun av e -> EApp(EAdverb(av,left),Ea1 e));
  (tm adverb|>>flip eadverb left) >>= more_expr;
  pipe2 (pverb|^>skip ws|>>eapp) (expr|>>ea2 left) (@@);
  pverb |>> (fun v -> EApp(v,Ea2(left,ENil)));
  pipe2 (psysname_dyad |>> comp eapp enamesys) (skip ws|>^expr|>>ea2 left) (@@);
  psysname_dyad |>> (fun v -> EApp(ENameSys v,Ea2(left,ENil)));
  pipe2 (pipe2 pname (tm adverb) (flip eadverb) >>= padverbs) (skip ws|>^expr) (fun e e'-> EApp(e,Ea2(left,e'))); (* init f/ xs *)
  pipe2 (pipe2 expr_lambda (tm adverb) (flip eadverb) >>= padverbs) (skip ws|>^expr) (fun f e -> EApp(f,Ea2(left,e)));
  expr |>> ea1 |>> eapp left;
  return left]
and expr_lambda s = (choice[brace (pipe2 formals expr_seq elambda); brace expr_seq |>> (fun e -> elambda (infer_args e) e)]) s
and expr_list s = (paren (sep_empty (tws SEMI) expr ENil) |>> (function []->fail()| [e] -> e | es -> elist es)) s
and expr_seq s = (sep_empty (tws SEMI) expr ENil |>> function [] -> fail() | e::es -> List.fold_left eseq e es) s
and eindex s = (bracket (choice [sep_empty (tws SEMI) expr ENil |^> skip ws |>> Array.of_list; skip ws |>^ return [||]])) s
and eassignf s = (choice [phandle |>> snd |>> ename;(tm verb|>>everb)>>=padverbs;expr] |^> tws COLON) s
let command = choice [t BACKSLASH |>^ choice [t BACKSLASH |>^ return CExit;
                        tm (function NAME "load"->()|_->fail())|>^skip ws|>^ option(choice [tname;tstring]) |>> cwsload;
                        tm (function NAME "save"-> ()|_->fail())|>^skip ws|>^ option(choice [tname;tstring]) |>> cwssave;
                        tm (function NAME "w"->()|_->fail())|>> const CWsSize;
                        tm (function NAME "l"->()|_->fail())|>^ skip ws |>^ choice [tname;tstring] |>> cload;
                        tm (function NAME "d"->()|_->fail())|>^ skip ws |>^ (phandle|>>snd) |>> ccd;
                        tm (function NAME "d"->()|_->fail())|>> const CPwd];
                      choice [skip ws |>^ expr_seq; choice [ws;tws SEMI] |>> const ENil] |>> ceval]
let phrase = command |^> t EOF
let parse_multiline ch  =
  let tokenize_multiline lexbuf acc stack =
    let rec loop acc stack =
      let t = Lexer.read lexbuf in
        let stack = match t, stack with
      | RPAREN,LPAREN::stack | RBRACKET,LBRACKET::stack | RBRACE,LBRACE::stack -> stack
      | (RPAREN|RBRACE|RBRACKET), _ -> raise KError_unmatched
      | LPAREN,_ | LBRACE,_ | LBRACKET,_ -> t::stack
      | _, _ -> stack in
      if t=COMMENTREST || (t=FORWARDSLASH && acc=[]) || t=EOF then (stack,if stack=[] then EOF::acc else SEMI::acc)
      else loop (t::acc) stack
    in loop acc stack in
  let rec loop acc stack =
    let stack, acc = tokenize_multiline(Lexing.from_string(input_line ch)) acc stack in
    if stack=[] then fst (phrase {tokens=array_of_list_rev acc;pos=0})
    else (if ch=stdin then Format.printf ">  "; Format.print_flush (); loop acc stack) in
  loop [] []
let parse_many f ch = try while true do f (parse_multiline ch); done with End_of_file -> ()
let _ = eval_file := (fun f -> let h= !ktree_pwdh and pwd=(!ktree_pwd) and env=(!ktree_env) in let ch = open_in (ensure_suffix ".k" f) in
                      ignore(parse_many eval_command ch);close_in ch;ktree_env:=env;ktree_pwd:=pwd;ktree_pwdh:=h)
(* REPL ==================================================================== *)
let _ = Printexc.record_backtrace true
let banner () = Format.printf "%s\n" (String.concat "\n" ["┌──────────┐"; "│ok console│"; "└──────────┘"]); Format.print_flush ()
let repl () =
  try while true do
    Format.printf "  "; Format.print_flush ();
    try let c = parse_multiline stdin in
        (* Format.printf "              / parsed as: %a\n" pp_c c; Format.print_flush (); *)
        let k = try eval_command c with KReturn k -> k in
        (if k<>KNil then Format.printf "%a\n" pp_k k); Format.print_flush ();
    with | KError_domain -> Format.printf "domain error\n"
         | KError_index -> Format.printf "index error\n"
         | KError_length -> Format.printf "length error\n"
         | KError_limit -> Format.printf "limit error\n"
         | KError_rank -> Format.printf "rank error\n"
         | KError_syntax -> Format.printf "syntax error\n"
         | KError_unmatched -> Format.printf "unmatched error\n"
         | KError_type -> Format.printf "type error\n"
         | KError_valence -> Format.printf "valence error\n"
         | KError_nonce -> Format.printf "unmarshaling error\n"
         | Not_implemented_attribute -> Format.printf "not implemented: attribute\n"
         | Not_implemented_apply -> Format.printf "not implemented: apply\n"
         | Not_implemented_format -> Format.printf "not implemented: format\n"
         | Not_implemented_builtins -> Format.printf "not implemented: builtin\n"
         | Not_implemented_io -> Format.printf "not implemented: I/O\n"
         | Not_implemented_dynlink -> Format.printf "not implemented: FFI\n"
         | Tinyparse.Failed -> Format.printf "parse error\n"
         | KExit | End_of_file -> raise KExit
         | e -> Format.printf "unhandled error (likely bug): %s\n" (Printexc.to_string e)
  done with KExit -> ()
let _ = banner ();if len Sys.argv = 2 then !eval_file Sys.argv.(1); repl ()