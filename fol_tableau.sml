Control.Print.printLength := 10000; (* set printing parameters so that *)
Control.Print.printDepth := 10000; (* we’ll see all details *)
Control.Print.stringDepth := 10000; (* and strings *)


structure TABLEAU =
struct

open FOL





fun lookup(x, l) = 
	case l of 
		[] => NONE
	  | (x'::l') => if x = x' 
			 then SOME x 
			 else lookup(x, l')


fun find(x, l) = 
	case lookup(x, l) of
		NONE => false
	  | SOME _ => true



fun remove_redundant(l1, nil) = l1 | remove_redundant(l1, l2) =
	let
		val hd::tl = l2
	in
		if find(hd, l1) then remove_redundant(l1, tl) else remove_redundant(hd::l1, tl)
	end


(*finds if particular atom is present, and returns its set of terms, as well as atom*)

fun find_atom_in_list(a, nil) = NONE | find_atom_in_list(a, l) =
	let
		val hd::tl = l
	in
		case (a, hd) of
		(ATOM(x, y), ATOM(p, q)) => if x = p then SOME (q, hd) else find_atom_in_list(a, tl)
		| (NOT(ATOM(x, y)), NOT(ATOM(p, q))) => if x = p then SOME (q, hd) else find_atom_in_list(a, tl)
		| (_, _) => find_atom_in_list(a, tl)
	end


fun remove(nil, x) = [] | remove(l, x) =
	let
		val hd::tl = l
	in
		if (hd = x) then tl else hd::remove(tl, x)
	end


fun find_atom(nil) = (FF, false) | find_atom(l) =
	let
		val hd::tl = l
	in
		case hd of
		ATOM(a, b) => (hd, true)
		| NOT(ATOM(a, b)) => (hd, true)
		| _ => find_atom(tl)
	end



fun find_prop_formula(nil) = (FF, false) | find_prop_formula(l) =
	let
		val hd::tl = l
	in
		case hd of
		NOT(NOT(a)) => (hd, true)
		| AND(a, b) => (hd, true)
		| NOT(OR(a, b)) => (hd, true)
		| NOT(COND(a, b)) => (hd, true)
		| NOT(AND(a, b)) => (hd, true)
		| OR(a, b) => (hd, true)
		| COND(a, b) => (hd, true)
		| BIC(a, b) => (hd, true)
		| NOT(BIC(a, b)) => (hd, true)
		| ITE(a, b, c) => (hd, true)
		| NOT(ITE(a, b, c)) => (hd, true)
		| _ => find_prop_formula(tl)
	end


fun find_exists_formula(nil) = (FF, false) | find_exists_formula(l) =
	let
		val hd::tl = l
	in
		case hd of
		EX(a, b) => (hd, true)
		| NOT(ALL(a, b)) => (hd, true)
		| _ => find_exists_formula(tl)
	end




fun subs_term(t, y, s) =
	case t of
		VAR(a) => if t = y then s else t
		| FUN(a, b) => FUN(a, subs_term_list(b, y, s))
		| CONST(a) => t


and

subs_term_list(nil, _, _) = [] | subs_term_list(l, y, s) =
	let
		val hd::tl = l
		val a = subs_term(hd, y, s)
	in
	 	a::subs_term_list(tl, y, s)
	end


fun substitute(x, y, s) =
	case x of
		ATOM(a, b) => ATOM(a, subs_term_list(b, y, s))
		| NOT(a) => NOT(substitute(a, y, s))
		| AND(a, b) => AND(substitute(a, y, s), substitute(b, y, s))
		| OR(a, b) => OR(substitute(a, y, s), substitute(b, y, s))
		| COND(a, b) => COND(substitute(a, y, s), substitute(b, y, s))
		| BIC(a, b) => BIC(substitute(a, y, s), substitute(b, y, s))
		| ITE(a, b, c) => ITE(substitute(a, y, s), substitute(b, y, s), substitute(c, y, s))
		| ALL(a, b) => if a = y then x else ALL(a, substitute(b, y, s))
		| EX(a, b) => if a = y then x else EX(a, substitute(b, y, s))
		| FF => FF



fun free_var_term(t) =
	case t of
		VAR(a) => [t]
		| FUN(a, b) => free_variable(b)
		| CONST(a) => []



and free_variable(nil) = [] | free_variable(l) =
	let
		val hd::tl = l
	in
		remove_redundant(free_var_term(hd), free_variable(tl))
	end


fun compose_mgu(nil, b, a) = [] | compose_mgu(l, b, a) =
	let
		val hd::tl = l
		val (x, y) = hd
	in
		(subs_term(x, b, a), y)::compose_mgu(tl, b, a)
	end



fun unify_terms(t1, t2) =
	case (t1, t2) of
		(VAR(a), VAR(b)) => if a = b then SOME [] else SOME [(t2, t1)]
		| (VAR(a), CONST(b)) => SOME [(t2, t1)]
		| (CONST(b), VAR(a)) => SOME [(t1, t2)]
		| (CONST(a), CONST(b)) => if a = b then SOME [] else NONE
		| (FUN(a, b), FUN(c, d)) => if a = c then unify_term_list(b, d, []) else NONE
		| (VAR(a), FUN(c, d)) => if find(VAR(a), free_variable(d)) then NONE else SOME [(t2, t1)]
		| (FUN(c, d), VAR(a)) => if find(VAR(a), free_variable(d)) then NONE else SOME [(t1, t2)]
		| (CONST(a), _) => NONE
		| (_, CONST(a)) => NONE


and 


unify_term_list(nil, nil, s) = SOME s | unify_term_list(nil, _, s) = SOME s | unify_term_list(_, nil, s) = SOME s | unify_term_list(l1, l2, s) =
	let
		val x1::y1 = l1
		val x2::y2 = l2
		val t = unify_terms(x1, x2)
		fun helper(nil, f, y1, y2) = (y1, y2, f) | helper(n, f, y1, y2) =
			let
				val hd::tl = n
				val (a, b) = hd
			in
				helper(tl, hd::compose_mgu(f, b, a), subs_term_list(y1, b, a), subs_term_list(y2, b, a))
			end
	in
		case t of
			SOME x => unify_term_list(helper(x, s, y1, y2))
			| NONE => NONE
	end



fun subs_mgu(nil, nil) = [] | subs_mgu(nil, _) = [] | subs_mgu(l, nil) = l | subs_mgu(l, m) =
	let
		val x2::y2 = m
		val (a, b) = x2
		val x = subs_term_list(l, b, a)
	in
		subs_mgu(x, y2)
	end


fun atom_mgu(a, m) =
	case a of
	ATOM(x, y) => ATOM(x, subs_mgu(y, m))
	| NOT(ATOM(x, y)) => NOT(ATOM(x, subs_mgu(y, m)))







(*add code for finding atoms in the list on preference, checking for their negation in atom list, and moving them to the atom list
IDEA: Maybe return tree in form of list of list, i.e., if el broken, then return [el]::[tableau(whatever)]::[tableau(whatever)], will need to make FF::l as [FF]
IDEA: To generate constants for EX and NOT ALL, add extra parameter k to tableau, and generate strings of the form 'dgjgejge' everytime increasing k by 1
TO-DO: Add appropriate x to every tableau call
TO-DO: Substitute mgu for both the broken formula, and the unifying atom -- Done
TO-DO: Check if argument is well formed -- exception handling
TO-DO: Add breaking rules in tableau for ITE*)




fun envAdd (var, e, env) =
    (var,e)::env

fun envLookup (var, env) =
    case List.find(fn (x, _) => x = var) env of
				       SOME (x, v)   => v
				    |   NONE => ~1







fun free_var_formula(f) =
	case f of
		FF => []
		| ATOM(a, b) => free_variable(b)
		| NOT(a) => free_var_formula(a)
		| AND(a, b) => remove_redundant(free_var_formula(a), free_var_formula(b))
		| OR(a, b) => remove_redundant(free_var_formula(a), free_var_formula(b))
		| COND(a, b) => remove_redundant(free_var_formula(a), free_var_formula(b))
		| BIC(a, b) => remove_redundant(free_var_formula(a), free_var_formula(b))
		| ITE(a, b, c) => remove_redundant(remove_redundant(free_var_formula(a), free_var_formula(b)), free_var_formula(c))
		| ALL(a, b) => remove(free_var_formula(b), a)
		| EX(a, b) => remove(free_var_formula(b), a)



fun well_formed_term(t, env) =
	case t of
		VAR(x) => (true, env)
		| FUN(a, b) =>
			let
				val arity = envLookup(a, env)
				val n = List.length(b)
				val (x, y) = well_formed_term_list(b, env)
			in
			 	if arity <> ~1 then if n = arity then (x, y) else raise NotWFT else (true, envAdd(a, n, env))
			end
		| CONST(a) => (false, env)



and 


well_formed_term_list(nil, env) = (true, env) | well_formed_term_list(l, env) =
	let
		val hd::tl = l
		val (x, y) = well_formed_term(hd, env)
	in
		if x then well_formed_term_list(tl, y) else (false, env)
	end


fun closed_formula(f) =
	let
		val a = free_var_formula(f)
		val b = List.length(a)
	in
		if b = 0 then true else false
	end



fun term_list_to_string(nil) = "" | term_list_to_string(l) =
	let
		val n = List.length(l)
		val hd::tl = l
	in
		if n = 1 then term_to_string(hd) ^ term_list_to_string(tl) else term_to_string(hd) ^ ", " ^ term_list_to_string(tl)
	end


and

term_to_string(t) =
	case t of
		VAR(x) => "VAR(" ^ x ^ ")"
		| FUN(x, y) => "FUN(" ^ x ^ ", [" ^ term_list_to_string(y) ^ "])"
		| CONST(x) => "CONST(" ^ x ^ ")"


fun for_to_st(f) =
	case f of
		FF => "FF"
		| ATOM(a, b) => "ATOM(" ^ a ^ ", [" ^ term_list_to_string(b) ^ "])"
		| NOT(a) => "NOT(" ^ for_to_st(a) ^ ")"
		| AND(a, b) => "AND(" ^ for_to_st(a) ^ ", " ^ for_to_st(b) ^ ")"
		| OR(a, b) => "OR(" ^ for_to_st(a) ^ ", " ^ for_to_st(b) ^ ")"
		| COND(a, b) => "COND(" ^ for_to_st(a) ^ ", " ^ for_to_st(b) ^ ")"
		| BIC(a, b) => "BIC(" ^ for_to_st(a) ^ ", " ^ for_to_st(b) ^ ")"
		| ITE(a, b, c) => "ITE(" ^ for_to_st(a) ^ ", " ^ for_to_st(b) ^ ", " ^ for_to_st(c) ^ ")"
		| ALL(a, b) => "ALL(" ^ term_to_string(a) ^ ", " ^ for_to_st(b) ^ ")"
		| EX(a, b) => "EX(" ^ term_to_string(a) ^ ", " ^ for_to_st(b) ^ ")"


fun well_formed(c, env1, env2) =
	case c of
		FF => (false, env1, env2)
		| ATOM(a, b) =>
			let
				val arity = envLookup(a, env1)
				val n = List.length(b)
				val (x, y) = well_formed_term_list(b, env2)
			in
			 	if arity <> ~1 then if n = arity then (x, env1, y) else raise NotWFP else (true, envAdd(a, n, env1), y)
			end
		| NOT(a) => well_formed(a, env1, env2)
		| AND(a, b) => 
			let
				val (x, y, z) = well_formed(a, env1, env2)
				val (u, v, w) = well_formed(b, y, z)
			in
				if x andalso u then (true, v, w) else (false, env1, env2)
			end
		| OR(a, b) =>
			let
				val (x, y, z) = well_formed(a, env1, env2)
				val (u, v, w) = well_formed(b, y, z)
			in
				if x andalso u then (true, v, w) else (false, env1, env2)
			end
		| COND(a, b) =>
			let
				val (x, y, z) = well_formed(a, env1, env2)
				val (u, v, w) = well_formed(b, y, z)
			in
				if x andalso u then (true, v, w) else (false, env1, env2)
			end
		| BIC(a, b) =>
			let
				val (x, y, z) = well_formed(a, env1, env2)
				val (u, v, w) = well_formed(b, y, z)
			in
				if x andalso u then (true, v, w) else (false, env1, env2)
			end
		| ITE(a, b, c) =>
			let
				val (x, y, z) = well_formed(a, env1, env2)
				val (u, v, w) = well_formed(b, y, z)
				val (p, q, r) = well_formed(c, v, w)
			in
				if (x andalso u) andalso p then (true, q, r) else (false, env1, env2)
			end
		| ALL(a, b) => (case a of
						VAR(x) => well_formed(b, env1, env2)
						| _ => raise NotVAR)
		| EX(a, b) => (case a of
						VAR(x) => well_formed(b, env1, env2)
						| _ => raise NotVAR)




fun well_formed_list(nil, env1, env2) = true | well_formed_list(l, env1, env2) =
	let
		val hd::tl = l
		val (x, y, z) = well_formed(hd, env1, env2)
	in
		if closed_formula(hd) then if x then well_formed_list(tl, y, z) else false else raise NotClosed
	end



fun atoms_unifying(alpha, y, p, q, hd, tl, atoms, x, flag, b) =
	if flag then case unify_term_list(y, p, []) of
				SOME ulist => (print("Unify: " ^ for_to_st(hd) ^ ", " ^ for_to_st(q) ^ "\n"); UNTREE(hd, tableau((ATOM(alpha, subs_mgu(y, ulist))::tl)@[hd], atom_mgu(q, ulist)::remove(atoms, q), x)))
				| NONE => UNTREE(hd, tableau((b::tl)@[hd], atoms, x))
	else case unify_term_list(y, p, []) of
		SOME ulist => (print("Unify: " ^ for_to_st(hd) ^ ", " ^ for_to_st(q) ^ "\n"); UNTREE(hd, tableau((NOT(ATOM(alpha, subs_mgu(y, ulist)))::tl)@[hd], atom_mgu(q, ulist)::remove(atoms, q), x)))
		| NONE => UNTREE(hd, tableau((b::tl)@[hd], atoms, x))


and


tableau(l, atoms, x) =
	let
		val (c, d) = find_atom(l)
		val (el, f) = find_prop_formula(l)
		val (g, h) = find_exists_formula(l)
		val hd::tl = l
	in
		if d then case c of
		ATOM(a, b) => if find(NOT(ATOM(a, b)), atoms) then (print("Closing Path: " ^ for_to_st(c) ^ ", " ^ for_to_st(NOT(ATOM(a, b))) ^ "\n"); UNTREE(c, EMPTY(FF))) else if find(NOT(ATOM(a, b)), l) then (print("Closing Path: " ^ for_to_st(c) ^ ", " ^ for_to_st(NOT(ATOM(a, b))) ^ "\n"); UNTREE(c, EMPTY(FF))) else if closed_formula(c) then UNTREE(c, tableau(remove(l, c), c::atoms, x)) else (case find_atom_in_list(NOT(c), atoms) of
					SOME (p, q) => (case unify_term_list(b, p, []) of
									SOME ulist => (print("Unify: " ^ for_to_st(c) ^ ", " ^ for_to_st(q) ^ "\n"); UNTREE(c, tableau(ATOM(a, subs_mgu(b, ulist))::remove(l, c), atom_mgu(q, ulist)::remove(atoms, q), x)))
									| NONE => tableau(remove(l, c), atoms, x))
					| NONE => tableau(remove(l, c), atoms, x))

		| NOT(ATOM(a, b)) => if find((ATOM(a, b)), atoms) then (print("Closing Path: " ^ for_to_st(c) ^ ", " ^ for_to_st((ATOM(a, b))) ^ "\n"); UNTREE(c, EMPTY(FF))) else if find((ATOM(a, b)), l) then (print("Closing Path: " ^ for_to_st(c) ^ ", " ^ for_to_st((ATOM(a, b))) ^ "\n"); UNTREE(c, EMPTY(FF))) else if closed_formula(c) then UNTREE(c, tableau(remove(l, c), c::atoms, x)) else (case find_atom_in_list(ATOM(a, b), atoms) of
					SOME (p, q) => (case unify_term_list(b, p, []) of
									SOME ulist => (print("Unify: " ^ for_to_st(c) ^ ", " ^ for_to_st(q) ^ "\n"); UNTREE(c, tableau(NOT(ATOM(a, subs_mgu(b, ulist)))::remove(l, c), atom_mgu(q, ulist)::remove(atoms, q), x)))
									| NONE => tableau(remove(l, c), atoms, x))
					| NONE => tableau((remove(l,c), atoms, x)))
		else
		if f then case el of
		NOT(NOT(a)) => if find(NOT(a), l) then UNTREE(el, EMPTY(FF)) else if find(a, l) then UNTREE(el, tableau(l, atoms, x)) else UNTREE(el, tableau(a::remove(l, el), atoms, x))
		| AND(a, b) => if (find(a, l) andalso find(b, l)) then UNTREE(el, tableau(l, atoms, x)) else if find(a, l) then UNTREE(el, tableau(b::remove(l, el), atoms, x)) else UNTREE(el, tableau(a::b::remove(l, el), atoms, x))
		| NOT(OR(a, b)) => if find(OR(a, b), l) then UNTREE(el, EMPTY(FF)) else if (find(NOT(a), l) andalso find(NOT(b), l)) then UNTREE(el, tableau(remove(l, el), atoms, x)) else if find(NOT(a), l) then UNTREE(el, tableau(NOT(b)::remove(l, el), atoms, x)) else UNTREE(el, tableau(NOT(a)::NOT(b)::remove(l, el), atoms, x))
		| NOT(COND(a, b)) => if find(COND(a, b), l) then UNTREE(el, EMPTY(FF)) else if (find(a, l) andalso find(NOT(b), l)) then UNTREE(el, tableau(remove(l, el), atoms, x)) else if find(a, l) then UNTREE(el, tableau(NOT(b)::remove(l, el), atoms, x)) else UNTREE(el, tableau(a::NOT(b)::remove(l, el), atoms, x))
		| NOT(AND(a, b)) => if find(AND(a, b), l) then UNTREE(el, EMPTY(FF)) else if (find(NOT(a), l) andalso find(NOT(b), l)) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(remove(l, el), atoms, x)) else if find(NOT(a), l) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(NOT(b)::remove(l, el), atoms, x)) else BINTREE(el, tableau(NOT(a)::remove(l, el), atoms, x), tableau(NOT(b)::remove(l, el), atoms, x))
		| OR(a, b) => if (find(a, l) andalso find(b, l)) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(remove(l, el), atoms, x)) else if find(a, l) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(b::remove(l, el), atoms, x)) else BINTREE(el, tableau(a::remove(l, el), atoms, x), tableau(b::remove(l, el), atoms, x))
		| COND(a, b) => if (find(NOT(a), l) andalso find(b, l)) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(remove(l, el), atoms, x)) else if find(NOT(a), l) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(b::remove(l, el), atoms, x)) else BINTREE(el, tableau(NOT(a)::remove(l, el), atoms, x), tableau(b::remove(l, el), atoms, x))
		| BIC(a, b) => if (find(AND(a, b), l) andalso find(AND(NOT(a), NOT(b)), l)) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(remove(l, el), atoms, x)) else if find(AND(a, b), l) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(AND(NOT(a), NOT(b))::remove(l, el), atoms, x)) else BINTREE(el, tableau(AND(a, b)::remove(l, el), atoms, x), tableau(AND(NOT(a), NOT(b))::remove(l, el), atoms, x))
		| NOT(BIC(a, b)) => if find(BIC(a, b), l) then UNTREE(el, EMPTY(FF)) else if (find(AND(a, NOT(b)), l) andalso find(AND(NOT(a), b), l)) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(remove(l, el), atoms, x)) else if find(AND(a, NOT(b)), l) then BINTREE(el, tableau(remove(l, el), atoms, x), tableau(AND(NOT(a), b)::remove(l, el), atoms, x)) else BINTREE(el, tableau(AND(a, NOT(b))::remove(l, el), atoms, x), tableau(AND(NOT(a), b)::remove(l, el), atoms, x))
		| ITE(a, b, c) => UNTREE(el, tableau(AND(COND(a, b), COND(NOT(a), b))::remove(l, el), atoms, x))
		| NOT(ITE(a, b, c)) => UNTREE(el, tableau(NOT(AND(COND(a, b), COND(NOT(a), b)))::remove(l, el), atoms, x))
		else
		if h then case g of
		EX(a, b) => if find(NOT(EX(a, b)), l) then UNTREE(g, EMPTY(FF)) else UNTREE(g, tableau(substitute(b, a, CONST(x^"a"))::remove(l, g), atoms, x^"a"))
		| NOT(ALL(a, b)) => if find(ALL(a, b), l) then UNTREE(g, EMPTY(FF)) else UNTREE(g, tableau(NOT(substitute(b, a, CONST(x^"a")))::remove(l, g), atoms, x^"a"))
		else case hd of
		ALL(a, b) =>
			(case b of
				ATOM(alpha, y) => (case find_atom_in_list(NOT(b), atoms) of
					SOME (p, q) => atoms_unifying(alpha, y, p, q, hd, tl, atoms, x, true, b)
					| NONE => UNTREE(hd, tableau((substitute(b, a, CONST("a"))::b::tl)@[hd], atoms, x)))
				| NOT(ATOM(alpha, y)) => (case find_atom_in_list(ATOM(alpha, y), atoms) of
					SOME (p, q) => atoms_unifying(alpha, y, p, q, hd, tl, atoms, x, false, b)
					| NONE => UNTREE(hd, tableau((substitute(b, a, CONST("a"))::b::tl)@[hd], atoms, x)))
				| _ => UNTREE(hd, tableau((substitute(b, a, CONST("a"))::b::tl)@[hd], atoms, x)))
		| NOT(EX(a, b)) =>
			(case b of
				ATOM(alpha, y) => (case find_atom_in_list(b, atoms) of
					SOME (p, q) => atoms_unifying(alpha, y, p, q, hd, tl, atoms, x, false, NOT(b))
					| NONE => UNTREE(hd, tableau((substitute(NOT(b), a, CONST("a"))::NOT(b)::tl)@[hd], atoms, x)))
				| NOT(ATOM(alpha, y)) => (case find_atom_in_list(b, atoms) of
					SOME (p, q) => atoms_unifying(alpha, y, p, q, hd, tl, atoms, x, true, NOT(b))
					| NONE => UNTREE(hd, tableau((substitute(NOT(b), a, CONST("a"))::NOT(b)::tl)@[hd], atoms, x)))
				| _ => UNTREE(hd, tableau((substitute(NOT(b), a, CONST("a"))::NOT(b)::tl)@[hd], atoms, x)))
		| _ => EMPTY(FF)
	end




fun maketableau(arg) =
	case arg of
		HENCE(h, c) =>
	let
		val s = NOT(c) :: h
	in
		well_formed_list(c::h, [], []);
		tableau(s, [], "")
	end



fun output(t) =
	case t of
		EMPTY(x) => "EMPTY[" ^ for_to_st(x) ^ "]\n"
		| UNTREE(x, y) => "UNTREE[" ^ for_to_st(x) ^ ",\n\t" ^ output(y) ^ "]"
		| BINTREE(x, y, z) => "BINTREE[" ^ for_to_st(x) ^ ",\n\t" ^ output(y) ^ ",\n\t" ^ output(z) ^ "]"


fun output_tableau(arg) =
	let
		val t = maketableau(arg)
		val outstream = TextIO.openOut "output.txt"
		val s = output(t)
	in
		TextIO.output(outstream, s);
		TextIO.closeOut outstream
	end



end;