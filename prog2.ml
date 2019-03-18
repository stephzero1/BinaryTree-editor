type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp |
	ETree of tree | ApplyOver of exp * exp | Update of (ide list) * exp * exp |
	Select of (ide list) * exp * exp
and tree = Empty |
	Node of ide * exp * tree * tree;;

	(*ambiente polimorfo*)
	type 't env = ide -> 't;;
	let emptyenv (v : 't) = function x -> v;;
	let applyenv (r : 't env) (i : ide) = r i;;
	let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

	(*tipi esprimibili*)
	type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | Tree of node
	and node = Empty | Nodes of ide * evT * node * node
	and evFun = ide * exp * evT env;;


	(*rts*)
	(*type checking*)
	let typecheck (s : string) (v : evT) : bool = match s with
		"int" -> (match v with
			Int(_) -> true |
			_ -> false) |
		"bool" -> (match v with
			Bool(_) -> true |
			_ -> false) |
		_ -> failwith("not a valid type");;

	(*funzioni primitive*)
	let prod x y = if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n*u))
		else failwith("Type error");;

	let sum x y = if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n+u))
		else failwith("Type error");;

	let diff x y = if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n-u))
		else failwith("Type error");;

	let eq x y = if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Bool(n=u))
		else failwith("Type error");;

	let minus x = if (typecheck "int" x)
		then (match x with
		   	Int(n) -> Int(-n))
		else failwith("Type error");;

	let iszero x = if (typecheck "int" x)
		then (match x with
			Int(n) -> Bool(n=0))
		else failwith("Type error");;

	let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
		then (match (x,y) with
			(Bool(b),Bool(e)) -> (Bool(b||e)))
		else failwith("Type error");;

	let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
		then (match (x,y) with
			(Bool(b),Bool(e)) -> Bool(b&&e))
		else failwith("Type error");;

	let non x = if (typecheck "bool" x)
		then (match x with
			Bool(true) -> Bool(false) |
			Bool(false) -> Bool(true))
		else failwith("Type error");;

	(*interprete*)
	let rec eval (e : exp) (r : evT env) : evT = match e with
		Eint n -> Int n |
		Ebool b -> Bool b |
		IsZero a -> iszero (eval a r) |
		Den i -> applyenv r i |
		Eq(a, b) -> eq (eval a r) (eval b r) |
		Prod(a, b) -> prod (eval a r) (eval b r) |
		Sum(a, b) -> sum (eval a r) (eval b r) |
		Diff(a, b) -> diff (eval a r) (eval b r) |
		Minus a -> minus (eval a r) |
		And(a, b) -> et (eval a r) (eval b r) |
		Or(a, b) -> vel (eval a r) (eval b r) |
		Not a -> non (eval a r) |
		Ifthenelse(a, b, c) ->
			let g = (eval a r) in
				if (typecheck "bool" g)
					then (if g = Bool(true) then (eval b r) else (eval c r))
					else failwith ("nonboolean guard") |
		Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
		Fun(i, a) -> FunVal(i, a, r) |
		FunCall(f, eArg) ->
			let fClosure = (eval f r) in
				(match fClosure with
					FunVal(arg, fBody, fDecEnv) ->
						eval fBody (bind fDecEnv arg (eval eArg r)) |
					RecFunVal(g, (arg, fBody, fDecEnv)) ->
						let aVal = (eval eArg r) in
							let rEnv = (bind fDecEnv g fClosure) in
								let aEnv = (bind rEnv arg aVal) in
									eval fBody aEnv |
					_ -> failwith("non functional value")) |
	        Letrec(f, funDef, letBody) ->
	        		(match funDef with
	            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
	                         			                eval letBody r1 |
	            		_ -> failwith("non functional def")) |

		(*2° PRPGETTO PRII*)

		ETree(body) -> let rec evbod bod = match bod with
			Node(i,arg,lx,rx) -> Nodes (i, eval arg r,  evbod lx, evbod rx)
			|Empty -> Empty
		in Tree(evbod body) |

		ApplyOver(exf, ext) -> let evtree = (match ext with
			ETree(body) -> body
			|_ -> failwith("non Tree"))
		in let rec evbod bod = match bod with
			Node(i,arg,lx,rx) -> Nodes (i, eval (FunCall(exf, arg)) r,  evbod lx, evbod rx)
			|Empty -> Empty
		in Tree(evbod evtree) |

		Update(idl,exf,ext) -> let evtree = (match ext with
			ETree(body) -> body
			|_ -> failwith("non Tree"))
		in let rec evup tr path = match tr,path with
			Node(i,arg,lx,rx),x::xs -> if i=x then Nodes (i, eval (FunCall(exf, arg)) r,  evup lx xs, evup rx xs)
									   else  Nodes (i, eval arg r,  evup lx [], evup rx [])
			|Node(i,arg,lx,rx),[] -> Nodes (i, eval arg r,  evup lx [], evup rx [])
			|Empty,_->Empty
		in Tree(evup evtree idl) |

		Select(idl,exf,ext) -> let evtree = (match ext with
			ETree(body)-> body
			|_ -> failwith("non Tree"))
		in let rec evsel tr path= match tr,path with
			Node(i,arg,lx,rx),x::[] -> if i=x then
			 								if (eval (FunCall(exf, arg)) r)=Bool(true) then ETree(Node(i,arg,lx,rx))
											else ETree(Empty)
										else ETree(Empty)
			|Node(i,arg,lx,rx),x::xs -> if i=x then let ok = evsel lx xs in if ok = ETree(Empty) then evsel rx xs else ok
									   else ETree(Empty)
			|_,[]-> ETree(Empty)
			|Empty,_ -> ETree(Empty)
		in eval (evsel evtree idl) r;;

(*

(* =============================  TESTS  ================= *)

	(*Definizione ambiente*)
	let env0 = emptyenv Unbound;;

	(*Definizione albero - t1 vuoto | t2 pieno*)
	let t1 = ETree(Empty);;
	let t2 = ETree(Node("a", Eint 2, Node("b", Eint 3, Empty, Empty), Node("c", Eint 4, Empty, Empty)))

	eval t1 env0;; eval t2 env0;;

	(*Uso di ApplyOver*)
	let e0 = ApplyOver(Fun("y", Sum(Den "y", Eint 1), t1);;
	let e1 = ApplyOver(Fun("y", Sum(Den "y", Eint 1)), ETree(Node("a", Eint 3, Node("b", Eint 4, Empty, Empty), Empty)));;

	eval e0 env0;; eval e1 env0;;

	(*Uso di Update*)
	let e0 = Update(["a";"c"],Fun("y", Sum(Den "y", Eint 1)),t1);;
	let e1 = Update(["a";"c"],Fun("y", Sum(Den "y", Eint 1)),ETree(Node("a", Eint 3, Node("b", Eint 4, Empty, Empty), Empty)));;

	eval e0 env0;; eval e1 env0;;

	(*Uso di Select*)
	let e0 = Select(["a";"b"],Fun("y",IsZero(Den "y")),ETree(Node("a", Eint 3, Node("b", Eint 4, Empty, Empty), Empty)));;
	let e1 = Select(["a"],Fun("y",IsZero(Den "y")),ETree(Node("a", Eint 0, Node("b", Eint 0, Node("d", Eint 0, Empty, Empty),  Node("c", Eint 0, Empty, Empty)), Node("b", Eint 0, Empty, Empty))));;

	eval e0 env0;; eval e1 env0;;

*)
