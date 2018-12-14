#load "dynlink.cma";;
#load "camlp4/camlp4o.cma"

(** Environnement fonctionnel **)

type oper2 = 
  | Moins
  | Plus
  | Mul
  | Div
  | Ou
  | Et
  | Egal

type oper1 =
  | Non

type expr = 
  | Int of int
  | Op1 of oper1 * expr
  | Op2 of oper2 * expr * expr
  | Bool of bool
  | IfThenElse of expr * expr * expr 
  | LetIn of string * expr * expr
  | FunDecl of (string list) * expr 
  | VarCall of string
  | FunCall of string * (expr list)

(* Un nom de variable est associé à une valeur *)
type mem = Var of string*int | Fun of string * (string list) * expr
type env = mem list
                                                 
(* Retourne la valeur associée à la variable v dans l'environnement l *)
(* Si un même nom est utilisé, c'est la valeur la plus récente qui sera retournée *)
let rec getVar v l =
  match l with
  |[] -> failwith "Identifieur inconnu"
  |Var(id,va)::q -> if (id = v) then va else getVar v q 
  |_::q ->  getVar v q

(* Retourne les noms de paramètre et le corps de la fonction f dans l'environnement l*)
let rec getFun f l =
  match l with
  |[] -> failwith "Identifieur inconnu"
  |Fun(id,p,c)::q -> if (id = f) then (p,c) else getFun f l
  |_::q -> getFun f l


let rec load_params args params oldenv newenv =
  match args,params with
  |[],[] -> newenv@oldenv
  |[],_  -> failwith "Not enough arguments"
  |_ ,[] -> failwith "Too many arguments"
  |(a::qargs),(p::qparams) -> load_params qargs qparams oldenv ( Var(p,(eval a oldenv))::newenv)

and eval exp env =
  match exp with
  | Int n -> n
  | Bool b -> if b then 1 else 0
  | Op2 (Moins, x, y) -> eval x env - eval y env
  | Op2 (Plus, x, y) -> eval x env + eval y env
  | Op2 (Mul, x, y) -> eval x env * eval y env
  | Op2 (Div, x, y) -> eval x env/ eval y env
  | Op2 (Ou, x, y) -> if ((eval x env) == 1) || ((eval y env) == 1) then 1 else 0 
  | Op2 (Et, x, y) -> if ((eval x env) == 1) && ((eval y env) == 1) then 1 else 0 
  | Op1 (Non, x) -> if ((eval x env) == 1) then 0 else 1 
  | Op2 (Egal, x, y) -> if ((eval x env) == (eval y env)) then 1 else 0 
  | IfThenElse (cond,x,y) -> if ((eval cond env)==1) then (eval x env) else (eval y env)         
  | VarCall(v) -> (getVar v env)
  | FunCall(f,pargs) -> let (params,fexpr) = (getFun f env) in
                        let envf = (load_params pargs params env []) in
                        (eval fexpr envf)
  | FunDecl(params,expr) -> failwith "Function declared without name"
  | LetIn(name,vexpr,suite) -> match vexpr with
          | FunDecl(params,expr) -> eval suite (Fun(name,params,expr)::env)
          | _ -> let value = (eval vexpr env) in eval suite (Var(name,value)::env)  
(*Evaluer les paramètres, les ajouter à l'environnement, evaluer l'identifieur v dans le nouvel environnement*)
  
                 
let string_oper2 o =
  match o with
  | Moins -> "-"
  | Plus -> "+"
  | Mul -> "*"
  | Div -> "/"
  | Ou -> " | "
  | Et -> " & "
  | Egal -> " = "

let string_oper1 o =
  match o with
  | Non -> "!"
          
let rec print_expr e =
  match e with
  | Int n -> print_int n
  | Bool b -> print_string (string_of_bool b)
  | Op2 (o, x, y) ->
     (print_char '(';
      print_expr x;
      print_string (string_oper2 o);
      print_expr y;
      print_char ')')
  | Op1 (o,x) ->
     (print_char '(';
      print_string (string_oper1 o);
      print_expr x;
      print_char ')')
  |IfThenElse (c,x,y) ->
     (print_string ("if ");
      print_expr c;
      print_string (" then {");
      print_expr x;
      print_string ("} else {");
      print_expr y;
      print_char '}')
  | LetIn (v,x,y) ->
     (print_string ("let ");
      print_string v;
      print_string (" = ");
      print_expr x;
      print_string (" in ");
      print_expr y)
  | VarCall(v) ->
     (print_string v)
  | FunDecl(param,expr) ->
     (print_string "funTODO")
  | FunCall(_) ->
     (print_string "TODO")
     
      (* FLOTS *)

(* Pour le test *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []

(* ANALYSEUR LEXICAL sur un flot de caractères *)
	      
(* Schéma de Horner *)
let chiffre = parser  [<'  '0'..'9' as x >] -> x

let valchiffre c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< c = chiffre ; s >] -> horner (10 * n + valchiffre c) s
  | [< >] -> n

let lettre = parser  [< ''a'..'z' | 'A'..'Z' as x >] -> x  
let alphanum = parser
  | [< x = lettre >] -> x
  | [< x = chiffre >] -> x

let rec lettres = parser
  | [<  x = alphanum; l = lettres >] -> x::l;
  | [< >] -> []

let rec lettres_to_bytes (l : char list) (i : int) (b : bytes) : string =
  match l with
  | []   -> Bytes.to_string b
  | x::q -> Bytes.set b i x ; lettres_to_bytes q (i+1) b  

let ident = parser
  | [< c = lettre ; l = lettres>] -> 
  let b = Bytes.make ((List.length l)+1) c in
  (lettres_to_bytes l 1 b)

(* Type des lexèmes *)
type token = 
  | Tent of int
  | Tmoins
  | Tplus
  | Tparouvre
  | Tparferme
  | Tmul
  | Tdiv
  | Tbool of bool  
  | Tou
  | Tet
  | Tnon
  | Tsi
  | Tsinon
  | Talors
  | Tegal
  | Tident of string
  | Tsoit
  | Tdans
  | Tfun
  | Tfleche
  | Tparam of string list
(* 
Pour passer d'un flot de caractères à un flot de lexèmes,
on commence par une fonction qui analyse lexicalement les
caractères d'un lexème au début d'un flot de caractères.
La fonction next_token rend un token option, c'est-à-dire :
- soit Some (tk)   où tk est un token
  dans le cas où le début du flot correspond lexème
- soit None

Le type option est prédéfini ainsi dans la bibliothèque standard OCaml :
type 'a option =
  | None           (* indique l'absence de valeur *)
  | Some of 'a     (* indique la présence de valeur *)
*)
            
let id_to_token id =
  match id with
  | "vrai" -> Tbool(true)
  | "faux" -> Tbool(false)
  | "non" -> Tnon
  | "si" -> Tsi
  | "alors" -> Talors
  | "sinon" -> Tsinon
  | "soit" -> Tsoit
  | "dans" -> Tdans
  | "fun" -> Tfun
  | str -> Tident(str) 

let rec next_token = parser
  | [< '  ' '|'\n'; tk = next_token >] -> tk (* élimination des espaces *)
  | [< '  '0'..'9' as c; n = horner (valchiffre c) >] -> Some (Tent (n))
  | [< '  '~';'  '>'>] -> Some (Tfleche)
  | [< '  '-' >] -> Some (Tmoins)
  | [< '  '+' >] -> Some (Tplus)
  | [< '  '(' >] -> Some (Tparouvre)
  | [< '  ')' >] -> Some (Tparferme)
  | [< '  '*' >] -> Some (Tmul)
  | [< '  '/' >] -> Some (Tdiv)
  | [< '  '=' >] -> Some (Tegal)
  | [< '  '&'; '  '&'>] -> Some (Tet)
  | [< '  '|'; '  '|'>] -> Some (Tou)
  | [< s = ident >] -> Some (id_to_token s)
  | [< >] -> None

(* tests *)
let s = Stream.of_string "soit f = fun x ~> x * x dans f 2"
let tk1 = next_token s
let tk2 = next_token s
let tk3 = next_token s
let tk4 = next_token s
let tk5 = next_token s
let tk6 = next_token s
let _ = next_token s

      
(* L'analyseur lexical parcourt récursivement le flot de caractères s
   en produisant un flot de lexèmes *)
let rec tokens s =
  match next_token s with
  | None -> [< >]
  | Some tk -> [< 'tk; tokens s >]

let lex s = tokens s

(* tests *)
let s = Stream.of_string "soit f = fun x -> x*x dans f 2"
let stk = lex s
let ltk = list_of_stream stk  

(*
Alternativement, la primitive Stream.from conduit au même résultat,
on l'utilise comme ci-dessous.
*)

let lex s = Stream.from (fun _ -> next_token s)

(*
A savoir : cette dernière version repose sur une représentation
interne des flots beaucoup plus efficace. Pour plus de détails
sur Stream.from, consulter le manuel OCaml.
Dans un compilateur réaliste devant traiter de gros textes, 
c'est la version à utiliser.
*)

let ltk1 = list_of_stream (lex (Stream.of_string "356 - 10 - 4"))

(* ANALYSEUR SYNTAXIQUE sur un flot de lexèmes *)

(* A noter : le passage d'un argument de type expr pour obtenir le
   bon parenthèsage de l'expression :
   41 - 20 - 1 est compris comme (41 - 20) - 1, non pas 41 - (20 - 1)
*)
let rec p_expr = parser
     | [< 'Tsi ; e1 = p_expr ; 'Talors ; e2 = p_expr ; 'Tsinon ; e3 = p_expr >] -> IfThenElse (e1,e2,e3)
     | [< 'Tsoit ; 'Tident(v) ; 'Tegal ; f = p_fun ; 'Tdans ; e2 = p_expr >] -> LetIn(v,f,e2)
     | [< c = p_conj ; sd = p_s_disj c >] -> sd
and p_fun = parser
     | [< 'Tfun ; p = p_param ; 'Tfleche ; x = p_expr>] -> FunDecl(p,x)
     | [< e = p_expr>] -> e
and p_param = parser
     | [< 'Tident(x) ; l = p_param>] -> x::l
     | [< >] -> []
and p_s_disj c = parser
     | [< 'Tou ; p = p_conj ; sd = p_s_disj (Op2(Ou,c,p))>] -> sd
     | [< >] -> c
and p_conj = parser
     | [< l = p_litt ; c = p_s_conj l>] -> c
and p_s_conj c = parser
     | [< 'Tet ; p = p_litt ; sc = p_s_conj (Op2(Et,c,p)) >] -> sc
     | [< >] -> c           
and p_litt = parser
     | [< 'Tnon ; p = p_litt>] -> Op1(Non,p)
     | [< ec = p_expr_comp; cmp = p_comp ec >] -> cmp
and p_comp e = parser
     |[< 'Tegal ; ec = p_expr_comp>] -> (Op2(Egal,e,ec))
     |[< >] -> e
and p_expr_comp = parser
     | [< t = p_terme; e = p_s_add t >] -> e
and p_s_add a = parser 
     | [< ' Tmoins; t = p_terme; e = p_s_add (Op2(Moins,a,t)) >] -> e
     | [< ' Tplus; t = p_terme; e = p_s_add (Op2(Plus,a,t)) >] -> e
     | [< >] -> a
and p_terme = parser
     | [< f = p_fact; sm = p_s_mul f >] -> sm
and p_s_mul a = parser
     | [< ' Tmul; t = p_fact; e = p_s_mul (Op2(Mul,a,t)) >] -> e
     | [< ' Tdiv; t = p_fact; e = p_s_mul (Op2(Div,a,t)) >] -> e
     | [< >] -> a
and p_s_expr = parser
     | [<x = p_expr ; l = p_s_expr>] -> x::l
     | [< >] -> []
and p_fact = parser
     | [< ' Tent(n)>] -> Int(n)
     | [< ' Tparouvre ; exp = p_expr; ' Tparferme>] -> exp
     | [< ' Tbool(b) >] -> Bool(b)
     | [< ' Tident(v) ; se = p_s_expr>] -> if (se = []) then VarCall(v) else FunCall(v,se)
                         
let ast s = p_expr (lex (Stream.of_string s));;

let e1 = ast "soit f = fun ~> 2 dans f";;
let _ = eval e1 [];;

let _ = print_expr e1;;

