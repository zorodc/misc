#include <variant>
#include <string>
#include <memory>
#include <cctype>
#include <tuple>
#include <ostream>
#include <functional>
#include <type_traits>
#include <unordered_map>
#include <iomanip>  /* std::boolalpha      */
#include <iostream> /* std::cout, std::cin */
/*
 * A small lisp interpreter implemented in C++, using the standard library.
 *
 * This was mostly an experiment, to see what could be done w/ std::variant
 *  and std::shared_ptr, which provide most of what's necessary
 *  for a lisp runtime: primitive garbage collection and runtime tagging.
 *
 * These components get you quite far, though not quite there.
 * They do get you the respective elements, a type system and memory management,
 *  without having to implement these things yourself.
 * The former is easier to implement oneself than the latter in C++;
 * Therefore, whilst implementing lisp in Java might be easier, as one can
 *  leverage the garbage collector, std::shared_ptr offers some substitute.
 *
 * Additionally, one finds that compiler errors w/ std::variant are atrocious.
 *
 * There's still a lot to add, before this can be used for anything:
 * TODO: Quoting.
 * TODO: dot-cons-notation in input and output.
 * TODO: Clean up some of the code a bit, wherever possible.
 * TODO: Make the exception handling a bit more robust.
 * TODO: Provide error messages whenever an exception is met.
 */

/*
 * Basic types and operations.
 */
namespace lisp {
	struct Cel; /* forward-decl of cons-cell */
	struct FNS; /* forward-decl of fn-struct */

	using  LFn = std::shared_ptr< FNS >;
	using  Ptr = std::shared_ptr< Cel >;
	using  Int =   long long;
	using  Str = std::string;
	using  Sym = std::tuple<std::string>;
	using  Val = std::variant<bool, Int, Sym, Str, Ptr, LFn>;

	using Namespace = std::unordered_map<std::string, Val>;
	struct Cel { Val Car, Cdr; Cel(Val ca, Val cd) : Car{ca}, Cdr{cd} {} };
	struct FNS { std::function<Val(Ptr, Namespace&, Ptr)> evl; Ptr body; };

	namespace exceptions {
		struct unexpected { char           which; };
		struct badinteger { std::string_view bad; };
		struct early_eofs { std::string_view bad; }; /* Early EOF.      */
		struct nullp_args {                       }; /* An arg was Nil. */
		struct wrong_type {                       }; /* Wrong type arg. */
		struct wrong_form {                       }; /* Syntax error.   */
	}

	namespace check {
		template <class T>
		inline void TAG(Val v) { if (!std::holds_alternative<T>(v))
		                             throw exceptions::wrong_type{}; }
		inline void NUL(Ptr p) { if (!p) throw exceptions::nullp_args{}; }
	}

	Ptr Lexr (const Str& sexp); /* Retuns conscell AST from a string's s-expr */
	Val Eval (const Ptr& sast, Namespace& n); /* Returns an AST's evaluation. */
	Val Eval (const Val& sast, Namespace& n);

	static const Ptr Nil = Ptr{nullptr};
	inline Val& Car (Ptr Obj)      { check::NUL(Obj);  return Obj->Car; }
	inline Val& Cdr (Ptr Obj)      { check::NUL(Obj);  return Obj->Cdr; }
	inline auto Cons(Val f, Val s) { return std::make_shared<Cel>(f,s); }
	inline Sym  Symbolize(std::string&& str) { return {std::move(str)}; }

	inline auto Call(const LFn& f, Namespace& n, Ptr a) {
		return f->evl(a, n, f->body);
	}

	inline Ptr  Eval_List(Ptr args, Namespace& n) {
		if (!args) return lisp::Nil;
		return Cons(Eval(Car(args), n), Eval_List(std::get<Ptr>(Cdr(args)), n));
	}

}

namespace func {
	inline auto Fst(lisp::Val c){return     lisp::Car(std::get<lisp::Ptr>(c)); }
	inline auto Snd(lisp::Val c){return Fst(lisp::Cdr(std::get<lisp::Ptr>(c)));}
	inline auto Nth(lisp::Val c, unsigned N) {
		while (N--) c = lisp::Cdr(std::get<lisp::Ptr>(c));
		return Fst (c);
	}
}

/*
 * METAPROGRAMMING
 */

namespace meta {
	/* A type to allow template parameter T of _pack::operator() to be deduced. */
	template <unsigned N> struct proxy { enum { value = N }; };

	/* Instantiate template R with a parameter pack of N different T args. */
	template <typename T, template <typename...> class R, typename... Ts>
	struct pack {
		template <unsigned N> auto operator()(proxy<N> = {}) {
			if constexpr (N) return pack<T,R,Ts...,T>{}(proxy<N-1>{});
			else             return        R<Ts...  >();
		}
	};

	template <typename... Ts>
	struct unwrapper {
		template <typename FN> auto untyped(FN fn, lisp::Ptr args) {
			unsigned i = sizeof...(Ts);
			return fn( Ts{func::Nth(args, --i)}... );
		}

		template <typename FN> auto checked(FN fn, lisp::Ptr args) {
			unsigned i = sizeof...(Ts);
			return fn( std::get<Ts>(func::Nth(args, --i))... );
		}
	};


	template <typename T, typename... Ts>
	struct last_of_pack { using type = typename last_of_pack<Ts...>::type; };
	template <typename Last> struct last_of_pack<Last>{ using type = Last; };

	/*
	 * Call a function w/ some lisp::Val arguments contained in a lisp list.
	 */
	template <unsigned Arity, typename FN>
	auto Untyped_Dispatch(FN fn, lisp::Ptr args) {
		return pack<lisp::Val, unwrapper>{}(proxy<Arity>{}).untyped(fn, args);
	}

	/*
	 * Call a function w/ some typed arguments contained in a lisp list.
	 */
	template <unsigned Arity, typename... Ts>
	auto Checked_Dispatch(auto fn, lisp::Ptr args) {
		using last_type  = typename last_of_pack<Ts...>::type;
		const auto Addnl = Arity - sizeof...(Ts);
		return pack<last_type, unwrapper, Ts...>{}(proxy<Addnl>{}).checked(fn, args);
	}
}

/*
 * Helpers for defining functions, using the metaprograming stuff.
 */

namespace def {

	/* Used for defining functions which control their evaluation order. */
	inline lisp::LFn Builtin(
		 std::function<lisp::Val(lisp::Ptr, lisp::Namespace&, lisp::Ptr)> fn,
		 lisp::Ptr body = lisp::Nil) {
		using namespace lisp;
		return std::make_shared<FNS>(FNS{fn, std::move(body)});
	}

	/* TODO: Some kind of variadic form? (Defined w/ a foldl or something...) */
	// TODO: N optional ret from Eval_List + check arity here.
	template <unsigned Arity, typename FN>
	lisp::LFn Untyped(FN fn) {
		return Builtin([=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
		    auto ev = Eval_List(args, n);
		    try { return lisp::Val{meta::Untyped_Dispatch<Arity>(fn, ev)}; }
		    catch (...) { throw lisp::exceptions::wrong_type{}; }
		});
	}

	template <unsigned Arity, typename... Ts>
	lisp:: LFn Checked(auto fn) {
		return Builtin([=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
			auto ev = Eval_List(args, n);
			try { return lisp::Val{meta::Checked_Dispatch<Arity, Ts...>(fn, ev)}; }
			catch (...) { throw lisp::exceptions::wrong_type{}; }
		});
	}
}

static std::ostream& operator<<(std::ostream& o, const lisp::Val& v)
{
	o << std::boolalpha;
	std::visit([&](auto&& arg) {
		using T = std::decay_t<decltype(arg)>;
		     if constexpr (std::is_same_v<T, lisp::Str>) o << '"' << arg << '"';
		else if constexpr (std::is_same_v<T, lisp::Sym>) o << std::get<0> (arg);
		else if constexpr (std::is_same_v<T, lisp::Ptr>) {
			o << '(';
			for (auto p = &arg; p && *p;
			          p = std::get_if<lisp::Ptr>(&lisp::Cdr(*p))) {
				if (p != &arg) o << ' ';
				o << lisp::Car(*p);
			}
			o << ')';
		} else o << arg; }, v);
	return o;
}

/*
 * Functions for use in the language itself, and a hash table to hold them.
 */

namespace func {
	inline auto Last(lisp::Val lv) {
		auto l = std::get<lisp::Ptr>(lv);

		while (lisp::Cdr(l) != lisp::Val{lisp::Nil})
			l = std::get<lisp::Ptr>(lisp::Cdr(l));
		return lisp::Car(l);
	}

	inline auto Zip(lisp::Ptr a, lisp::Ptr b) {
		if (a == lisp::Nil && b == lisp::Nil) return lisp::Nil;
		else return lisp::Cons(lisp::Cons(Fst(a), lisp::Cons(Fst(b), lisp::Nil)),
		 Zip(std::get<lisp::Ptr>(lisp::Cdr(a)),
		     std::get<lisp::Ptr>(lisp::Cdr(b))));
	}

	lisp::Namespace Lang = {
		{{"true" },  true               },
		{{"false"}, false               },
		{{"nil"  }, lisp::Val{lisp::Nil}},

		{{"car" }, def::Checked<1, lisp::Ptr>([](lisp::Ptr c) { return lisp::Car(c); })},
		{{"cdr" }, def::Checked<1, lisp::Ptr>([](lisp::Ptr c) { return lisp::Cdr(c); })},
		{{"cons"}, def::Untyped<2>([](lisp::Val x, lisp::Val y) {
					return lisp::Val{lisp::Cons(x, y)}; })},

		{{"-"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x-y; })},
		{{"*"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x*y; })},
		{{"/"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x/y; })},
		{{"%"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x%y; })},
		{{"="}, def::Untyped<2> ([](lisp::Val x, lisp::Val y) { return x==y; })},

		{{"+"}, def::Builtin([](lisp::Ptr arg, lisp::Namespace& n, lisp::Ptr _) {
			lisp::Int acc = 0;

			try {
				for (auto ev = Eval_List(arg, n); ev != lisp::Nil;
				          ev = std::get<lisp::Ptr>(lisp::Cdr(ev)))
					acc += std::get<lisp::Int>(lisp::Car(ev));
			} catch (...) { return lisp::Val{lisp::Nil}; }
			return lisp::Val{acc};
		})},

		{{"if"}, def::Builtin([](lisp::Ptr arg, lisp::Namespace& n, lisp::Ptr _) {
			auto testp = lisp::Car(arg);
			try {
				auto ifp = std::get   <lisp::Ptr>( lisp::Cdr(arg));
				auto elp = std::get_if<lisp::Ptr>(&lisp::Cdr(ifp));
				auto res = std::get<bool>(lisp::Eval(testp, n));
				if (!res && elp) return lisp::Eval(lisp::Car(*elp), n);
				else             return lisp::Eval(lisp::Car( ifp), n);
			} catch (...) { throw lisp::exceptions::wrong_type{}; }
		})},

		{{"let"}, def::Builtin([](lisp::Ptr lexpr, lisp::Namespace& n, lisp::Ptr _) {
			auto union_shadow = [&](lisp::Ptr pairs) -> lisp::Namespace {
				auto newns = n;
				try {
					for (auto it = pairs; it != lisp::Nil;
					          it = std::get<lisp::Ptr>(lisp::Cdr(it))) {
						auto elm = lisp::Car(it);
						auto metav = Fst(elm), sexpr = Snd(elm);
						auto bound = lisp::Eval(sexpr, newns);
						newns[std::get<0>(std::get<lisp::Sym>(metav))] = bound;
					}
				} catch (...) { throw lisp::exceptions::wrong_form{}; }

				return newns;
			};

			try {
				auto n = union_shadow(std::get<lisp::Ptr>(lisp::Car(lexpr)));
				return Last(lisp::Eval_List(
					            std::get<lisp::Ptr>(lisp::Cdr(lexpr)), n));
			} catch (...) { throw lisp::exceptions::wrong_form{}; }
		})},

		{{"defun"}, def::Builtin([](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
			auto body = lisp::Cdr(args);

			try {
				auto alst =             std::get<lisp::Ptr>(lisp::Car(args));
				auto name = std::get<0>(std::get<lisp::Sym>(lisp::Car(alst)));
				auto mvar =             std::get<lisp::Ptr>(lisp::Cdr(alst));
				return n[name] = def::Builtin(
				    [=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr body) {
						auto binds = func::Zip(mvar, args);
						return lisp::Eval(lisp::Cons(lisp::Sym{"let"},
						                  lisp::Cons(binds, body)), n);
					}, std::get<lisp::Ptr>(body));

			} catch (...) { throw lisp::exceptions::wrong_form{}; }
		})}
	};
}

/*
 * Lexing/parsing implementation.
 */

using size = unsigned long;
lisp::Ptr lisp::Lexr (const lisp::Str& sexp)
{
	auto expect = [&](size i, char req) {
		if (sexp[i] != req) throw lisp::exceptions::unexpected{sexp[i]}; };

	auto intlit = [&](size i, size& next) {
		auto s = sexp.substr(i);
		next   = i;
		Val retval;
		try { retval = std::stoll(s, &i); } catch (...) {
			throw lisp::exceptions::badinteger{s.substr(i)}; }
		next += i;
		return retval;
	};

	auto strlit = [&](size i, size& next) {
		expect(i++, '\"'); /* Sanity check. */
		for (size c = i; c < sexp.length(); ++c)
			switch (sexp[c]) {
			case '\\': ++c;  break;
			case  '"':
				next = c + 1;
				return sexp.substr(i, c-i);
			}
		throw lisp::exceptions::early_eofs{{sexp.c_str() + i, sexp.length()}};
	};

	auto isidch = [ ](char c) { return isgraph(c) && c != '(' && c != ')'; };
	auto symbol = [&](size i, size& next) {
		if (!isidch(sexp[i])) expect(i, '\0');
		size c = i;

		while (isidch(sexp[c])) c++;

		next = c;
		return lisp::Symbolize(sexp.substr(i, c-i));
	};

//	auto oquote = [&](size i, size& next) {
//
//	};

	auto skipws = [&](size i, size& next) {
		while (sexp[i] ==  ' ' ||
		       sexp[i] == '\t' ||
		       sexp[i] == '\n') ++i;
		next = i;
	};

	std::function<lisp::Val(size i, size& next)> expr; /* "forward-decl" */
	auto conses = [&](size i, size& next) {
		expect(i++, '('); /* Sanity check. */

		lisp::Val  list = lisp::Nil;
		lisp::Val* last = &list;
		for (size c = i; c < sexp.length(); skipws(c, c))
			if   (sexp[c] == ')') { next = c+1; return std::get<Ptr>(list); }
			else {
				*last = Val{lisp::Cons(expr(c, c), lisp::Nil)};
				 last = &Cdr(std::get<Ptr>(*last));
			}
		throw lisp::exceptions::early_eofs{{sexp.c_str() + i, sexp.length()}};
	};

	expr = [&](size i, size& next) -> lisp::Val { skipws(i, i);
		switch (sexp[i]) {
		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7': case '8':
		case '9': return intlit(i, next);
		case '(': return conses(i, next);
		case'\"': return strlit(i, next);
//		case'\'': return oquote(i, next);
		default : return symbol(i, next);

		/* Prevent inputs from being interpreted in odd ways. */
		case ')': throw lisp::exceptions::unexpected{sexp[i]};
		}
	};

	size _; return lisp::Cons(expr(0, _), lisp::Nil);
}

lisp::Val lisp::Eval (const lisp::Val& ast, lisp::Namespace& n) {
	if (std::holds_alternative<Sym>(ast)) {
		auto   it = n.find(std::get<0>(std::get<Sym>(ast)));
		return it != std::end(n) ? it->second : lisp::Nil; /* TODO: Change. */
	}

	return std::holds_alternative<Ptr>(ast) ? Eval(std::get<Ptr>(ast), n) : ast;
}

lisp::Val lisp::Eval (const lisp::Ptr& ast, lisp::Namespace& n) {
	Val fn = std::visit([&](auto&& e) {
		using T = std::decay_t<decltype(e)>;
		if (std::is_same_v<T, Ptr> || std::is_same_v<T, Sym>) return Eval(e, n);
		else                                                  return Val{ Nil };
	}, lisp::Car(ast));

	try {
		auto v = std::get<LFn>(fn);
		return lisp::Call(v, n, std::get<Ptr>(lisp::Cdr(ast)));
	} catch (...) { throw lisp::exceptions::wrong_type{}; }
}

int main() {
	for (;;) {
		std::string expr{}; getline(std::cin, expr);
		if (!std::cin || expr == "exit") break;

		lisp::Val parsetree = lisp::Nil;
		try { parsetree = lisp::Car(lisp::Lexr(expr)); } catch (...)
		    { std::cerr << "Lexer error!\n"; continue; }

		std::cout << lisp::Eval(parsetree, func::Lang) << '\n';
	}
}
