structure TABLEAU  =
struct
open AST


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


fun findassignment(nil) = nil | findassignment(hd::tl) = 
	case hd of
	ATOM(a) => (a, true) :: findassignment(tl)
	| NOT(ATOM(a)) => (a, false) :: findassignment(tl)


fun branching(l1, l2) =
	let
		val (a1, b1) = l1
		val (a2, b2) = l2
	in
		case a1 of
		true => (true, b1)
		| false => (a2, b2)
	end



fun proptableauimpl(pl:Prop list, x) =
	let
		val el::tl = pl
	in
		if find(NOT(el), tl) then (false, []) else
		case el of
		NOT(NOT(a)) => if find(NOT(a), tl) then (false, []) else if find(a, tl) then proptableauimpl(tl, x) else proptableauimpl(a::tl, x)
		| AND(a, b) => if (find(a, tl) andalso find(b, tl)) then proptableauimpl(tl, x) else if find(a, tl) then proptableauimpl(b::tl, x) else proptableauimpl(a::b::tl, x)
		| NOT(OR(a, b)) => if find(OR(a, b), tl) then (false, []) else if (find(NOT(a), tl) andalso find(NOT(b), tl)) then proptableauimpl(tl, x) else if find(NOT(a), tl) then proptableauimpl(NOT(b)::tl, x) else proptableauimpl(NOT(a)::NOT(b)::tl, x)
		| NOT(COND(a, b)) => if find(COND(a, b), tl) then (false, []) else if (find(a, tl) andalso find(NOT(b), tl)) then proptableauimpl(tl, x) else if find(a, tl) then proptableauimpl(NOT(b)::tl, x) else proptableauimpl(a::NOT(b)::tl, x)
		| NOT(AND(a, b)) => if find(AND(a, b), tl) then (false, []) else if (find(NOT(a), tl) andalso find(NOT(b), tl)) then branching(proptableauimpl(tl, x), proptableauimpl(tl, x)) else if find(NOT(a), tl) then branching(proptableauimpl(tl, x), proptableauimpl(NOT(b)::tl, x)) else branching(proptableauimpl(NOT(a)::tl, x), proptableauimpl(NOT(b)::tl, x))
		| OR(a, b) => if (find(a, tl) andalso find(b, tl)) then branching(proptableauimpl(tl, x), proptableauimpl(tl, x)) else if find(a, tl) then branching(proptableauimpl(tl, x), proptableauimpl(b::tl, x)) else branching(proptableauimpl(a::tl, x), proptableauimpl(b::tl, x))
		| COND(a, b) => if (find(NOT(a), tl) andalso find(b, tl)) then branching(proptableauimpl(tl, x), proptableauimpl(tl, x)) else if find(NOT(a), tl) then branching(proptableauimpl(tl, x), proptableauimpl(b::tl, x)) else branching(proptableauimpl(NOT(a)::tl, x), proptableauimpl(b::tl, x))
		| BIC(a, b) => if (find(AND(a, b), tl) andalso find(AND(NOT(a), NOT(b)), tl)) then branching(proptableauimpl(tl, x), proptableauimpl(tl, x)) else if find(AND(a, b), tl) then branching(proptableauimpl(tl, x), proptableauimpl(AND(NOT(a), NOT(b))::tl, x)) else branching(proptableauimpl(AND(a, b)::tl, x), proptableauimpl(AND(NOT(a), NOT(b))::tl, x))
		| NOT(BIC(a, b)) => if find(BIC(a, b), tl) then (false, []) else if (find(AND(a, NOT(b)), tl) andalso find(AND(NOT(a), b), tl)) then branching(proptableauimpl(tl, x), proptableauimpl(tl, x)) else if find(AND(a, NOT(b)), tl) then branching(proptableauimpl(tl, x), proptableauimpl(AND(NOT(a), b)::tl, x)) else branching(proptableauimpl(AND(a, NOT(b))::tl, x), proptableauimpl(AND(NOT(a), b)::tl, x))
		| ATOM(a) => if find(NOT(ATOM(a)), tl) then (false, []) else if find(ATOM(a), tl) then proptableauimpl(tl, x) else if (el = x) then (true, findassignment(pl)) else if (x = ATOM("")) then proptableauimpl(tl@[el], el) else proptableauimpl(tl@[el], x)
		| NOT(ATOM(a)) => if find(ATOM(a), tl) then (false, []) else if find(NOT(ATOM(a)), tl) then proptableauimpl(tl, x) else if (el = x) then (true, findassignment(pl)) else if (x = ATOM("")) then proptableauimpl(tl@[el], el) else proptableauimpl(tl@[el], x)
	end


fun proptableau(arg:Argument) =
	case
	arg of HENCE(hypotheses, conclusion) =>
		let
			val gamma = hypotheses@[NOT(conclusion)]
			val (a, b) = proptableauimpl(gamma, ATOM(""))
		in
			if (a) then ("Invalid", b) else ("Valid", [])
		end


end