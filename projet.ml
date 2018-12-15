(* 
 * projet.ml
 * 
 * -- Projet Programmation Fonctionnelle
 * -- Analyse Syntaxique
 * 
 * @authors Ariane ANCRENAZ
 *          Tanguy SAUTON
 *          Mathieu VINCENT
 *
 * Polytech Grenoble 2018 - INFO4 - PF
 *)

(* #load "dynlink.cma"  *)
(* #load "camlp4/camlp4o.cma"  *)
#use "topfind";;
#camlp4o;;

(*
 * Parties du sujet réalisées:
 * - Partie 1 : Expressions
 * - Partie 2 : Typage (Option 1)
 * - Partie 3 : Extensions fonctionnelles (sauf récursivité)
 *)

(** Définition de l'AST **)

(* Opérateurs binaires *)
type oper2 = 
  | Moins
  | Plus
  | Mul
  | Div
  | Ou
  | Et
  | Egal

(* Opérateurs unaires *)
type oper1 =
  | Non

(* Expressions du langages (Noeud de l'AST) *)
type expr = 
  | Int of int
  (*
    int -> entier
  *)
  | Bool of bool
  (*
    bool -> booléen
  *)
  | Op1 of oper1 * expr
  (*
    oper1 -> Symbole de l'opération unaire
    expr  -> expression à évaluer
   *)
  | Op2 of oper2 * expr * expr
  (*
   oper2 -> Symbole de l'opération binaire
   expr  -> Partie gauche de l'opération
   expr  -> Partie droite de l'opération
  *)
  | IfThenElse of expr * expr * expr 
  (* "Si ... Alors ... Sinon ..."
   expr -> expression à évaluer (booléen)
   expr -> expression du ALORS
   expr -> expression du SINON
  *)
  | LetIn of string * (string list) * expr * expr
  (* Définition de fonction (les variables sont des fonctions sans arguments)
     string      -> nom de fonction
     string list -> paramètres de la fonction: pour une variable, ce champ est []
     expr        -> l'expression de la fonction
     expr        -> expression à évaluer
  *)
  | Call of string * (expr list)
  (* Appel de fonction
     string    -> nom de la fonction à appeler
     expr list -> arguments de la fonction ([] si variable)
  *)

(** Environnement fonctionnel **)

(* L'environnement est constitué de déclarations de fonction
   string      -> nom de la fonction
   string list -> paramètres de la fonction (noms)
   expr        -> expression de la fonction

NB : Les valeurs les plus récentes sont stockées en tête *)
type env = (string * (string list) * expr) list

exception UnknownIdentifier of string
         
(* 
 * get : (string -> env -> string list * expr)
 * Récupération d'une fonction dans un environnement
 * On retourne le nom des paramètres et l'expression de la fonction
 *)
let rec get (name : string) (e : env) =
  match e with
  |[] -> raise (UnknownIdentifier name)
  |(id,params,expr)::q -> if (id = name) then (params,expr) else (get name q)


(** Typage des expressions **)

(* Type à 2 valeurs représentant les entiers et les booléens *)
type typage =
  | TBool of bool
  | TInt of int

(* Exception levée en cas de typage incorrect *)
exception TypeMismatch of string

(* isInt : (typage -> int)
   Vérifie si une valeur (de type typage) 
   est entière et retourne cet entier 
   En cas d'erreur de typage, une exception TypeMismatch est levée
   *)
let isInt (n : typage) = match n with
  |TInt(n) -> n
  |_ -> raise (TypeMismatch "Was expecting integer")

(* isBool : (typage -> bool)
   Vérifie si une valeur (de type typage)
   est booléenne et retourne ce booléen 
   En cas d'erreur de typage, une exception TypeMismatch est levée
   *)
let isBool (n : typage) = match n with
  |TBool(b) -> b
  | _ -> raise (TypeMismatch "Was expecting boolean")

(* egal : (expr -> expr -> bool)
   Compare deux expressions du même type
   et retourne true/false si l'évaluation
   est identique
   En cas d'erreur de typage, une exception TypeMismatch est levée
  *)
let egal e1 e2 =
  match e1, e2 with
  |TInt(n1),TInt(n2) -> (n1 == n2)
  |TBool(b1),TBool(b2) -> (b1 == b2)
  |_ -> raise (TypeMismatch "Different types for comparison")


(** Evalutation des expressions **)

(* Exception pour gérer les erreurs de paramètres *)
exception ArgsMismatch of string

(* eval : (expr -> env -> typage) 
   Evalue un noeud de l'AST
   En cas d'erreur avec les arguments, une exception ArgsMismatch est levée
   En cas d'erreur de typage, une exception TypeMismatch est levée
 *)
let rec eval exp env =
  match exp with
  | Int n -> TInt(n)
  | Bool b -> TBool(b)
  | Op2 (Moins, x, y) -> TInt((isInt (eval x env)) - (isInt (eval y env)))
  | Op2 (Plus, x, y) -> TInt((isInt (eval x env)) + (isInt (eval y env)))
  | Op2 (Mul, x, y) -> TInt((isInt (eval x env)) * (isInt (eval y env)))
  | Op2 (Div, x, y) -> TInt((isInt (eval x env)) / (isInt (eval y env)))
  | Op2 (Ou, x, y) -> TBool((isBool (eval x env)) || (isBool (eval y env))) 
  | Op2 (Et, x, y) -> TBool((isBool (eval x env)) && (isBool (eval y env))) 
  | Op1 (Non, x) -> TBool(not (isBool (eval x env)))
  | Op2 (Egal, x, y) -> TBool(egal (eval x env) (eval y env))   
  | IfThenElse (cond,x,y) -> let a = (eval cond env) in let a2 = (isBool a) in (if a2 then (eval x env) else (eval y env))
  | Call(fname,pargs) -> let (params,fexpr) = (get fname env) in
                        let envf = (load_params pargs params env []) in
                        (eval fexpr envf) 
  | LetIn(name,params,expr,suite) ->  eval suite ((name,params,expr)::env)                                 

(* load_params (string list ->  -> env -> env -> env)
 * Fonction auxiliaire pour le chargement des arguments
 * NB : Pourquoi 2 environnements différents ?
 * Sinon pb avec => (fun y x -> ...)  appelé avec (f x y)
 *)
 and load_params args params oldenv newenv =
 match args,params with
 |[],[] -> newenv@oldenv (* Nombre d'argument correct, on rajoute le nouvel environnement en tête de l'ancien *)
 |[],_  -> raise (ArgsMismatch "Not enough arguments")
 |_ ,[] -> raise (ArgsMismatch "Too many arguments")
 |(a::qargs),(p::qparams) -> 
   let ev = (eval a oldenv) in (* Evaluation des arguments *)
       begin
       match ev with (* Ajout dans le nouvel environnement *)
       | TInt(n) -> load_params qargs qparams oldenv ((p,[],Int(n))::newenv)
       | TBool(b) -> load_params qargs qparams oldenv ((p,[],Bool(b))::newenv)
       end

(** Affichage des expression **)

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

let rec print_strings p =
  match p with
  | [] -> print_string ""
  | x::l -> print_string x ; print_string " " ;print_strings l 

let rec print_exprs l =
  match l with
  |[] -> print_string ""
  |x::l -> print_expr x ; print_string " " ; print_exprs l 
and print_expr e =
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
  | LetIn (v,p,x,y) ->
     (print_string ("let ");
      print_string v;
      print_string (" = ");
      print_string "fun ";
      print_strings p ;
      print_string "-> " ;
      print_expr x ;
      print_string (" in ");
      print_expr y)
  | Call(v,p) ->
      print_string v;
      print_string " ";
      print_exprs p
    
(** FLOTS **)

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

(* Lecture des identifieurs *)
let lettre = parser  [< ''a'..'z' | 'A'..'Z' as x >] -> x  
let alphanum = parser
  | [< x = lettre >] -> x
  | [< x = chiffre >] -> x

let rec alphanums = parser
  | [<  x = alphanum; l = alphanums >] -> x::l;
  | [< >] -> []

(* Transtypage char list -> string *)
let rec lettres_to_bytes (l : char list) (i : int) (b : bytes) : string =
  match l with
  | []   -> Bytes.to_string b
  | x::q -> Bytes.set b i x ; lettres_to_bytes q (i+1) b  

(* Un identifieur commence toujours par une lettre suivie de caractères alphanumériques *)
let ident = parser
  | [< c = lettre ; l = alphanums>] -> 
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

(* Passage des identifieurs aux tokens *)
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
  | [< '  '~';'  '>'>] -> Some (Tfleche) (* Flèche implémentée avec un ~>*)
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

(* Tests *)
(*
let s = Stream.of_string "soit f = fun x ~> x * x dans f 2"
let _ = next_token s
*)

(*
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

(*
A savoir : cette dernière version repose sur une représentation
interne des flots beaucoup plus efficace. Pour plus de détails
sur Stream.from, consulter le manuel OCaml.
Dans un compilateur réaliste devant traiter de gros textes, 
c'est la version à utiliser.
*)
*)

let lex s = Stream.from (fun _ -> next_token s)

(*
 let _ = list_of_stream (lex (Stream.of_string "356 - 10 - 4"))
*)


(** ANALYSEUR SYNTAXIQUE sur un flot de lexèmes **)

(* Grammaire:
  E = expression
  C = conjonction
  SC = suite de conjonctions
  SD = suite de disjonctions
  L = littéral
  EC = expression comparable
  CMP = comparaison
  T = terme
  SA = suite d’additions
  F = facteur
  SM = suite de multiplications
  FUN = fonction
  PARAMS = suite de paramètres (ident)
  SE = suite d'expressions

  E ::= ’si’ E ’alors’ E ’sinon’ E | 'soit' ident '=' FUN 'dans' E | C SD
  FUN ::= 'fun' PARAMS '~>' E | E
  PARAMS ::= ident PARAMS | ϵ 
  SD ::= ’||’ C SD | ϵ
  C ::= L SC
  SC ::= ’&&’ L SC | ϵ
  L ::= ’non’ L | EC CMP
  CMP ::= ’=’ EC | ϵ
  EC ::= T SA
  SA ::= ’+’ T SA | ’-’ T SA | ϵ
  T ::= F SM
  SM ::= ’*’ F SM | ’/’ F SM | ϵ
  SE ::= E SE | ϵ
  F ::= entier | ’vrai’ | ’faux’ | ’(’ E ’)’ | ident SE
*)
let rec p_expr = parser
     | [< 'Tsi ; e1 = p_expr ; 'Talors ; e2 = p_expr ; 'Tsinon ; e3 = p_expr >] -> IfThenElse (e1,e2,e3)
     | [< 'Tsoit ; 'Tident(v) ; 'Tegal ; (p,x) = p_fun ; 'Tdans ; e1 = p_expr >] -> LetIn(v,p,x,e1)
     | [< c = p_conj ; sd = p_s_disj c >] -> sd
and p_fun = parser
     | [< 'Tfun ; p = p_param []; 'Tfleche ; x = p_expr>] -> (p,x)
     | [< e = p_expr>] -> ([],e)
and p_param c = parser
     | [< 'Tident(x) ; l = p_param (x::c)>] -> l
     | [< >] -> c
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
and p_s_expr c = parser
     | [<x = p_expr ; l = p_s_expr (x::c)>] -> l
     | [< >] -> c
and p_fact = parser
     | [< ' Tent(n)>] -> Int(n)
     | [< ' Tparouvre ; exp = p_expr; ' Tparferme>] -> exp
     | [< ' Tbool(b) >] -> Bool(b)
     | [< ' Tident(v) ; se = p_s_expr []>] -> Call(v,se)

(* Constructeur d'AST *)
let ast s = p_expr (lex (Stream.of_string s))


(** Tests **)

let e1 = ast "soit f = fun x y ~> x * y dans (f 3 4) + 3"
let _ = eval e1 []

let _ = print_expr e1


let test1 = ast "soit x = 5 dans x + (soit x = 2 dans x) - x"
let _ = eval test1 []

let test2 = ast "soit x = 5 dans (soit y = 2 dans x + y)"
let _ = eval test2 []

let test3 = ast "si vrai alors 2 sinon 3"
let _ = print_expr test3
let _ = eval test3 []

let test4 = ast "soit x = 5 dans si faux alors si vrai || faux alors vrai sinon faux sinon x"
let _ = print_expr test4
let _ = eval test4 []
          
let test5 = ast "soit x = 5 dans x + (si vrai && faux || vrai alors 3 sinon 2)"
let _ = print_expr test5
let _ = eval test5 []

let test6 = ast "soit x = 4 dans x + (si vrai alors soit x = 4 dans x sinon (si faux alors soit x = 2 dans x sinon soit x = 3 dans x))"
let _ = print_expr test6
let _ = eval test6 []
      
let test7 = ast "soit var = 42 dans var + (soit vra1 = 2 dans vra1)";;
let _ = print_expr test7
let _ = eval test7 []

let test8 = ast "soit var1 = 4 dans var1 + (si non vrai alors soit var2 = 1 dans var2 sinon soit var3 = 2 dans var3)"
let _ = print_expr test8
let _ = eval test8 []

let test9 = ast "non non non non vrai"
let _ = print_expr test9
let _ = eval test9 []
      
let test10 = ast "soit x = 10 dans x * (si non non vrai && non faux alors soit y = 5 dans y sinon (si vrai && non non faux alors soit z = 8 dans z sinon soit w = 4 dans w))"
let _ = print_expr test10
let _ = eval test10 []

let x = 5 in x + (if true && false || true then 3 else 2)
let x = 4 in x + (if true then let x = 4 in x else (if false then let x = 2 in x else let x = 3 in x))
let x = 10 in x*(if (not (not true)) && not false then let y = 5 in y else (if true && (not (not false)) then let z = 8 in z else let w = 4 in w))

(* Tests d'exceptions *)
(* Exceptions de typage *)
let e = ast "si 2 alors vrai sinon faux"
let _ = eval e []

let e = ast "si (2 = vrai) alors 1 sinon 2"
let _ = eval e []

(* Exceptions d'identifieurs*)
let e = ast "let x = 2 in x"
let _ = eval e []
      
(* Exceptions d'arguments*)
let e = ast "soit f = fun a b c ~> a+b*c dans f 1 2"
let _ = eval e []

let e = ast "soit f = fun a ~> a dans f 1 2"
let _ = eval e []

      
(* Les variables sont des fonctions *)
let var1 = eval (ast "soit f = 2 dans f") []
let var1fun = eval (ast "soit f = fun ~> 2 dans f") []
let _ = assert(var1 = var1fun)
