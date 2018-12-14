#load "dynlink.cma";;
#load "camlp4/camlp4o.cma" ;;

(** Environnement fonctionnel **)
(* Un nom de variable est associé à une valeur *)
type env = (string*int) list

(* Retourne la valeur de la variable s dans l'environnement l *)
(* Si un même nom est utilisé, c'est la valeur la plus récente qui sera retournée *)
let rec get s l =
  match l with
  |[] -> failwith "Identifieur inconnu"
  |(id,va)::q -> if (id = s) then va else get s q

type typage =
  | Bool of b
  | Int of int
         
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
  | Var of string
                
let rec eval exp env =
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
  | LetIn(v,x,y) -> let var = (eval x env) in eval y ((v,var)::env)
  | Var(v) -> get v env

let rec eval exp env  =
  match exp with
  | Int(_) -> Int(evalI exp env)
  | Bool(_) -> Bool(evalB exp env)
  | Op2 (Moins, x, y)
  | Op2 (Plus, x, y)
  | Op2 (Mul, x, y)
  | Op2 (Div, x, y) -> Int(evalI exp env)
  | Op2 (_,_,_) -> Bool(evalB exp env)
  | Op1(Non,x) -> Bool(evalB exp env)
  | IfThenElse (cond,x,y) -> if (evalB cond env) then (eval x env) else (eval y env)
  | LetIn(v,x,y) -> let var = (eval x env) in match var with |Int(n) -> eval y ((v,n)::env)
                                                             |Bool(n) -> failwith"Probleme de type"
  | Var(v) -> Int(get v env)
                           
and evalI exp env : int=
  match exp with
  | Int n -> n
  | Op2 (Moins, x, y) -> evalI x env - evalI y env
  | Op2 (Plus, x, y) -> evalI x env + evalI y env
  | Op2 (Mul, x, y) -> evalI x env * evalI y env
  | Op2 (Div, x, y) -> evalI x env/ evalI y env

and evalB exp env : bool =
  match exp with
  | Bool b -> b
  | Op1 (Non, x) -> not(evalB x env)
  | Op2 (Ou, x, y) -> (evalB x env)||(evalB y env) 
  | Op2 (Et, x, y) -> (evalB x env)&&(evalB y env) 
  | Op1 (Non, x) -> not(evalB x env) 
  | Op2 (Egal, x, y) -> (eval x env) == (eval y env)
                 
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
  | Var(v) ->
     (print_string v)

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

let ident c = parser
  | [< l = lettres>] -> 
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
  | str -> Tident(str) 

let rec next_token = parser
  | [< '  ' '|'\n'; tk = next_token >] -> tk (* élimination des espaces *)
  | [< '  '0'..'9' as c; n = horner (valchiffre c) >] -> Some (Tent (n))
  | [< '  '-' >] -> Some (Tmoins)
  | [< '  '+' >] -> Some (Tplus)
  | [< '  '(' >] -> Some (Tparouvre)
  | [< '  ')' >] -> Some (Tparferme)
  | [< '  '*' >] -> Some (Tmul)
  | [< '  '/' >] -> Some (Tdiv)
  | [< '  '&'; '  '&'>] -> Some (Tet)
  | [< '  '|'; '  '|'>] -> Some (Tou)
  | [< '  '='>] -> Some (Tegal)
  | [<  l = lettre; s = (ident l) >] -> Some (id_to_token s)
  | [< >] -> None

(* tests *)
let s = Stream.of_string "45 - - 089"
let tk1 = next_token s
let tk2 = next_token s
let tk3 = next_token s
let tk4 = next_token s
let tk5 = next_token s
let tk6 = next_token s

(* L'analyseur lexical parcourt récursivement le flot de caractères s
   en produisant un flot de lexèmes *)
let rec tokens s =
  match next_token s with
  | None -> [< >]
  | Some tk -> [< 'tk; tokens s >]

let lex s = tokens s

(* tests *)
let s = Stream.of_string "45 - - 089"
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
               | [< 'Tsoit ; 'Tident(v) ; 'Tegal ; e1 = p_expr ; 'Tdans ; e2 = p_expr >] -> LetIn(v,e1,e2)
     | [< c = p_conj ; sd = p_s_disj c >] -> sd                                      
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
and p_fact = parser
     | [< ' Tent(n)>] -> Int(n)
     | [< ' Tparouvre; exp = p_expr; ' Tparferme>] -> exp
     | [< ' Tbool(b) >] -> Bool(b)
     | [< ' Tident(v)>] -> Var(v)
                         
let ast s = p_expr (lex (Stream.of_string s));;

let e1 = ast "soit x = 5 dans x + (soit x = 2 dans x) - x";;


let e1 = ast "x";;


let _ = eval e1 [("x",5)];;
let _ = print_expr e1;;


let e1 = ast "vrai";;
let _ = eval e1 [];;

